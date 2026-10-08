-- Prove2me | solution 1 for MartinetReg.ConvexMin.remark1
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T13:21:15.589009+00:00
-- url     : https://prove2.me/submissions/8b76f2d0-5075-4366-b359-802815d107cf

import Definitions.Def_MartinetReg_ConvexMin_Setting
set_option autoImplicit false
section
set_option autoImplicit false
namespace MartinetCodex
open MartinetReg.ConvexMin

theorem uniform_convex_strict_on_set {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : H → ℝ) (C : Set H) (hC : Convex ℝ C) (φ : ℝ → ℝ)
    (hφ : ∀ r : ℝ, 0 < r → 0 < φ r) (hf : UniformConvexOn Set.univ φ f) :
    StrictConvexOn ℝ C f := by
  refine ⟨hC,?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hd : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hp : 0 < a*b*φ ‖x-y‖ := mul_pos (mul_pos ha hb) (hφ _ hd)
  exact (hf.2 (Set.mem_univ x) (Set.mem_univ y) ha.le hb.le hab).trans_lt (sub_lt_self _ hp)

theorem uniform_convex_fixed_distance_gap {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : H → ℝ) (C : Set H) (hC : Convex ℝ C) (hconv : ConvexOn ℝ Set.univ f)
    (φ : ℝ → ℝ) (hf : UniformConvexOn Set.univ φ f)
    (z y : H) (hz : z ∈ solSet f C) (hy : y ∈ C)
    (ε : ℝ) (hε : 0 < ε) (hd : ε ≤ ‖y-z‖) : φ ε ≤ 2*(f y-f z) := by
  have hdpos : 0 < ‖y-z‖ := hε.trans_le hd
  let t := ε/‖y-z‖
  have ht : 0 < t := div_pos hε hdpos
  have ht1 : t ≤ 1 := (div_le_iff₀ hdpos).mpr (by simpa using hd)
  let w := (1-t) • z+t • y
  have hw : w ∈ C := hC hz.1 hy (by linarith) ht.le (by ring)
  have he : w-z=t • (y-z) := by dsimp [w]; rw [sub_smul,one_smul,smul_sub]; abel
  have hnorm : ‖w-z‖=ε := by
    rw [he,norm_smul,Real.norm_of_nonneg ht.le]
    dsimp [t]
    field_simp
  have hcv := hconv.2 (Set.mem_univ z) (Set.mem_univ y) (by linarith : 0 ≤ 1-t) ht.le
    (by ring : 1-t+t=1)
  have hp : 0 ≤ (1-t)*(f y-f z) := mul_nonneg (by linarith) (sub_nonneg.mpr (hz.2 y hy))
  have hwy : f w ≤ f y := by simp only [smul_eq_mul] at hcv; dsimp [w] at *; nlinarith
  have hmid : (1/2 : ℝ) • z+(1/2 : ℝ) • w ∈ C := hC hz.1 hw (by norm_num) (by norm_num) (by norm_num)
  have hmin := hz.2 _ hmid
  have hu := hf.2 (Set.mem_univ z) (Set.mem_univ w) (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)+1/2=1)
  rw [norm_sub_rev z w,hnorm] at hu
  simp only [smul_eq_mul] at hu
  nlinarith
end MartinetCodex

end

section
set_option autoImplicit false
namespace MartinetCodex
open MartinetReg.ConvexMin

theorem proxSeq_mem {H : Type*} [NormedAddCommGroup H] (f : H → ℝ) (C : Set H)
    (x : ℕ → H) (hx : IsProxSeq f C x) (n : ℕ) : x n ∈ C := by
  cases n with
  | zero => exact hx.1
  | succ n => exact (hx.2 n).1

theorem proxSeq_descent {H : Type*} [NormedAddCommGroup H] (f : H → ℝ) (C : Set H)
    (x : ℕ → H) (hx : IsProxSeq f C x) (n : ℕ) :
    f (x (n+1))+‖x (n+1)-x n‖^2 ≤ f (x n) := by
  have h := (hx.2 n).2 (x n) (proxSeq_mem f C x hx n)
  simpa only [sub_self,norm_zero,zero_pow (by decide : 2≠0),add_zero] using h

theorem proxSeq_value_antitone {H : Type*} [NormedAddCommGroup H] (f : H → ℝ) (C : Set H)
    (x : ℕ → H) (hx : IsProxSeq f C x) : Antitone (fun n => f (x n)) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := proxSeq_descent f C x hx n
  nlinarith [sq_nonneg ‖x (n+1)-x n‖]
end MartinetCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace MartinetCodex
open MartinetReg.ConvexMin

/-- Squared-norm interpolation follows the algebraic pattern in miao's accepted unique-step proof. -/
theorem norm_affine_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u v : H) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    ‖a • u+b • v‖^2 = a*‖u‖^2+b*‖v‖^2-a*b*‖u-v‖^2 := by
  rw [norm_add_sq_real,norm_sub_sq_real,norm_smul,norm_smul,
    real_inner_smul_left,inner_smul_right,Real.norm_of_nonneg ha,Real.norm_of_nonneg hb]
  obtain rfl := eq_sub_of_add_eq hab
  ring

theorem le_of_small_penalties (A B D : ℝ)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → A ≤ B+t*D) : A ≤ B := by
  have hn (n : ℕ) : A ≤ B+(1/(n+1 : ℝ))*D := by
    apply h
    · positivity
    · apply (div_le_iff₀ (by positivity : 0 < (n+1 : ℝ))).mpr
      linarith [Nat.cast_nonneg (α := ℝ) n]
  have ht : Tendsto (fun n : ℕ => B+(1/(n+1 : ℝ))*D) atTop (𝓝 B) := by
    have hsmall : Tendsto (fun n : ℕ => 1/(n+1 : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hB : Tendsto (fun _ : ℕ => B) atTop (𝓝 B) := tendsto_const_nhds
    have hD : Tendsto (fun _ : ℕ => D) atTop (𝓝 D) := tendsto_const_nhds
    simpa using hB.add (hsmall.mul hD)
  exact (isClosed_Ici : IsClosed (Set.Ici A)).mem_of_tendsto ht (Eventually.of_forall hn)

theorem proxStep_three_point {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (C : Set H) (hC : Convex ℝ C) (hf : ConvexOn ℝ Set.univ f)
    (xn y z : H) (hy : IsProxStep f C xn y) (hz : z ∈ C) :
    f y+‖y-xn‖^2+‖y-z‖^2 ≤ f z+‖z-xn‖^2 := by
  apply le_of_small_penalties _ _ (‖y-z‖^2)
  intro t ht ht1
  have hm : (1-t) • y+t • z ∈ C := hC hy.1 hz (by linarith) ht.le (by ring)
  have hp := hy.2 _ hm
  have hc := hf.2 (Set.mem_univ y) (Set.mem_univ z) (by linarith : 0 ≤ 1-t) ht.le (by ring : 1-t+t=1)
  have he : (1-t) • y+t • z-xn = (1-t) • (y-xn)+t • (z-xn) := by
    rw [smul_sub,smul_sub,← add_sub_add_comm,← add_smul]
    have hcoeff : (1-t)+t=1 := by ring
    rw [hcoeff,one_smul]
  have hd : (y-xn)-(z-xn)=y-z := by abel
  rw [he,norm_affine_sq _ _ (1-t) t (by linarith) ht.le (by ring),hd] at hp
  simp only [smul_eq_mul] at hc
  have hi : t*(f y+‖y-xn‖^2+‖y-z‖^2-(f z+‖z-xn‖^2+t*‖y-z‖^2)) ≤ 0 := by nlinarith
  by_contra hn
  have hp : 0 < t*(f y+‖y-xn‖^2+‖y-z‖^2-(f z+‖z-xn‖^2+t*‖y-z‖^2)) :=
    mul_pos ht (sub_pos.mpr (lt_of_not_ge hn))
  linarith
end MartinetCodex

end

section
set_option autoImplicit false
open MartinetReg.ConvexMin
open Set Topology

private theorem weak_closed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {S : Set H} (hS : Convex ℝ S) (hc : IsClosed S) :
    IsClosed (toWeakSpace ℝ H '' S) := by
  have he := hS.toWeakSpace_closure ℝ
  rw [hc.closure_eq] at he
  exact closure_eq_iff_isClosed.mp he.symm

private theorem weak_compact {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {S : Set H} (hS : Convex ℝ S) (hc : IsClosed S)
    (hb : Bornology.IsBounded S) : IsCompact (toWeakSpace ℝ H '' S) := by
  have hsur : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ H) := by
    intro L
    let e := InnerProductSpace.toDual ℝ H
    let f : StrongDual ℝ H := L.comp e.toContinuousLinearEquiv.toContinuousLinearMap
    refine ⟨e.symm f, ?_⟩
    ext g
    have hg : e (e.symm g) = g := e.apply_symm_apply g
    change g (e.symm f) = L g
    rw [← hg]
    change inner ℝ (e.symm g) (e.symm f) = L (e (e.symm g))
    rw [real_inner_comm]
    change e (e.symm f) (e.symm g) = L (e (e.symm g))
    rw [e.apply_symm_apply]
    rfl
  have hsurw : Function.Surjective (NormedSpace.inclusionInDoubleDualWeak ℝ H) := by
    intro L
    obtain ⟨x, hx⟩ := hsur (StrongDual.toWeakDual.symm L)
    refine ⟨toWeakSpace ℝ H x, ?_⟩
    apply StrongDual.toWeakDual.symm.injective
    exact hx
  have hn := NormedSpace.isCompact_closure_of_isBounded ℝ H (toWeakSpace ℝ H '' S)
    (by rw [Set.preimage_image_eq _ (toWeakSpace ℝ H).injective]; exact hb)
    (by rw [Set.range_eq_univ.mpr hsurw]; exact Set.subset_univ _)
  rwa [(weak_closed hS hc).closure_eq] at hn

private theorem convex_min_exists {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (C : Set H) (hS : Standing f C) :
    ∃ xs ∈ C, ∀ x ∈ C, f xs ≤ f x := by
  let e := toWeakSpace ℝ H
  have hf : LowerSemicontinuous (fun x : WeakSpace ℝ H => f (e.symm x)) := by
    apply lowerSemicontinuous_iff_isClosed_preimage.mpr
    intro a
    have he : (fun x : WeakSpace ℝ H => f (e.symm x)) ⁻¹' Iic a =
        e '' {x : H | f x ≤ a} := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_image, mem_setOf_eq]
      constructor
      · intro hx; exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
      · rintro ⟨y, hy, rfl⟩; simpa using hy
    rw [he]
    exact weak_closed (by simpa using hS.fconvex.convex_le a) (hS.flsc.isClosed_preimage a)
  obtain ⟨x0, hx0⟩ := hS.nonempty
  let K := {x : H | x ∈ C ∧ f x ≤ f x0}
  have hsubconv : Convex ℝ {x : H | f x ≤ f x0} := by
    simpa using hS.fconvex.convex_le (f x0)
  have hKconv : Convex ℝ K := hS.convex.inter hsubconv
  have hKclosed : IsClosed K := hS.closed.inter (hS.flsc.isClosed_preimage (f x0))
  have hKcomp := weak_compact hKconv hKclosed (hS.sublevel_bounded (f x0))
  obtain ⟨y, hy, hmy⟩ := LowerSemicontinuousOn.exists_isMinOn
    (Set.Nonempty.image e (show K.Nonempty from ⟨x0, hx0, le_rfl⟩)) hKcomp
    (hf.lowerSemicontinuousOn _)
  obtain ⟨xs, hxs, rfl⟩ := hy
  refine ⟨xs, hxs.1, ?_⟩
  intro x hx
  by_cases hfx : f x ≤ f x0
  · have hh := hmy (Set.mem_image_of_mem e (show x ∈ K from ⟨hx, hfx⟩))
    simpa using hh
  · exact hxs.2.trans (le_of_not_ge hfx)

theorem MartinetCodex.exists_minimizer_miao {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (C : Set H) (hS : Standing f C) :
    (solSet f C).Nonempty := by
  exact convex_min_exists f C hS


end

section
set_option autoImplicit false
open Filter Topology
namespace MartinetCodex
open MartinetReg.ConvexMin

theorem prox_gap_sum_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (C : Set H) (hC : Convex ℝ C) (hf : ConvexOn ℝ Set.univ f)
    (x : ℕ → H) (hx : IsProxSeq f C x) (z : H) (hz : z ∈ C) (N : ℕ) :
    (∑ i ∈ Finset.range N, (f (x (i+1))-f z))+‖x N-z‖^2 ≤ ‖x 0-z‖^2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hp := proxStep_three_point f C hC hf (x N) (x (N+1)) z (hx.2 N) hz
    rw [norm_sub_rev z (x N)] at hp
    nlinarith [sq_nonneg ‖x (N+1)-x N‖]

theorem prox_objective_gap_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (C : Set H) (hC : Convex ℝ C) (hf : ConvexOn ℝ Set.univ f)
    (x : ℕ → H) (hx : IsProxSeq f C x) (z : H) (hz : z ∈ C) (N : ℕ) (hN : 0 < N) :
    f (x N)-f z ≤ ‖x 0-z‖^2/(N : ℝ) := by
  have hsum := prox_gap_sum_bound f C hC hf x hx z hz N
  have hmono := proxSeq_value_antitone f C x hx
  have hlower : (N : ℝ)*(f (x N)-f z) ≤ ∑ i ∈ Finset.range N, (f (x (i+1))-f z) := by
    calc
      _ = ∑ i ∈ Finset.range N, (f (x N)-f z) := by simp <;> ring
      _ ≤ _ := Finset.sum_le_sum (fun i hi => sub_le_sub_right
        (hmono (by have := Finset.mem_range.mp hi; omega)) (f z))
  apply (le_div_iff₀ (by exact_mod_cast hN : 0 < (N : ℝ))).mpr
  nlinarith [sq_nonneg ‖x N-z‖]

theorem prox_value_tendsto_minimum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (C : Set H) (hC : Convex ℝ C) (hf : ConvexOn ℝ Set.univ f)
    (x : ℕ → H) (hx : IsProxSeq f C x) (z : H) (hz : z ∈ solSet f C) :
    Tendsto (fun N => f (x N)) atTop (𝓝 (f z)) := by
  have hh : Tendsto (fun N : ℕ => f z+‖x 0-z‖^2/(N : ℝ)) atTop (𝓝 (f z)) := by
    have hconst : Tendsto (fun _ : ℕ => f z) atTop (𝓝 (f z)) := tendsto_const_nhds
    simpa using hconst.add (tendsto_const_div_atTop_nhds_zero_nat (‖x 0-z‖^2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hh
  · exact Eventually.of_forall (fun N => hz.2 (x N) (proxSeq_mem f C x hx N))
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hb := prox_objective_gap_bound f C hC hf x hx z hz.1 N (by omega)
    linarith

theorem prox_exists_minimum_value_limit {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (C : Set H) (hS : Standing f C)
    (x : ℕ → H) (hx : IsProxSeq f C x) :
    ∃ m : ℝ, IsGLB (f '' C) m ∧ Tendsto (fun n => f (x n)) atTop (𝓝 m) := by
  obtain ⟨z,hz⟩ := exists_minimizer_miao f C hS
  have hleast : IsLeast (f '' C) (f z) := by
    refine ⟨⟨z,hz.1,rfl⟩,?_⟩
    rintro r ⟨y,hy,rfl⟩
    exact hz.2 y hy
  exact ⟨f z,hleast.isGLB,prox_value_tendsto_minimum f C hS.convex hS.fconvex x hx z hz⟩
end MartinetCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace MartinetCodex
open MartinetReg.ConvexMin

theorem uniform_convex_minimizer_unique {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : H → ℝ) (C : Set H) (hC : Convex ℝ C) (φ : ℝ → ℝ)
    (hφ : ∀ r : ℝ, 0 < r → 0 < φ r) (hf : UniformConvexOn Set.univ φ f)
    (z : H) (hz : z ∈ solSet f C) : solSet f C = {z} := by
  have hstrict := uniform_convex_strict_on_set f C hC φ hφ hf
  ext y
  constructor
  · intro hy
    exact Set.mem_singleton_iff.mpr (hstrict.eq_of_isMinOn hy.2 hz.2 hy.1 hz.1)
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    simpa [hy] using hz

theorem uniform_convex_value_limit_implies_strong {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : H → ℝ) (C : Set H) (hC : Convex ℝ C) (hconv : ConvexOn ℝ Set.univ f)
    (φ : ℝ → ℝ) (hφ : ∀ r : ℝ, 0 < r → 0 < φ r) (hf : UniformConvexOn Set.univ φ f)
    (x : ℕ → H) (hx : ∀ n, x n ∈ C) (z : H) (hz : z ∈ solSet f C)
    (hlim : Tendsto (fun n => f (x n)) atTop (𝓝 (f z))) : Tendsto x atTop (𝓝 z) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hp : 0 < φ ε := hφ ε hε
  have hevent : ∀ᶠ n in atTop, f (x n) < f z+φ ε/2 := hlim.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hevent
  refine ⟨N,?_⟩
  intro n hn
  rw [dist_eq_norm]
  by_contra hnot
  have hd : ε ≤ ‖x n-z‖ := le_of_not_gt hnot
  have hg := uniform_convex_fixed_distance_gap f C hC hconv φ hf z (x n) hz (hx n) ε hε hd
  have hb := hN n hn
  linarith

theorem prox_uniform_convex_strong_limit {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (C : Set H) (hS : Standing f C)
    (φ : ℝ → ℝ) (hφ : ∀ r : ℝ, 0 < r → 0 < φ r) (hf : UniformConvexOn Set.univ φ f)
    (x : ℕ → H) (hx : IsProxSeq f C x) :
    ∃ z : H, solSet f C = {z} ∧ Tendsto x atTop (𝓝 z) := by
  obtain ⟨z,hz⟩ := exists_minimizer_miao f C hS
  have hlim := prox_value_tendsto_minimum f C hS.convex hS.fconvex x hx z hz
  exact ⟨z,uniform_convex_minimizer_unique f C hS.convex φ hφ hf z hz,
    uniform_convex_value_limit_implies_strong f C hS.convex hS.fconvex φ hφ hf x
      (proxSeq_mem f C x hx) z hz hlim⟩
end MartinetCodex

end

set_option autoImplicit false
open Filter Topology MartinetReg.ConvexMin
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (C : Set H) (hS : Standing f C)
    (φ : ℝ → ℝ) (hφ : ∀ t : ℝ, 0 < t → 0 < φ t) (hunif : UniformConvexOn Set.univ φ f)
    (x : ℕ → H) (hx : IsProxSeq f C x) :
    ∃ xs : H, solSet f C = {xs} ∧ Tendsto x atTop (𝓝 xs) := by
  exact MartinetCodex.prox_uniform_convex_strong_limit f C hS φ hφ hunif x hx


#print axioms solution
