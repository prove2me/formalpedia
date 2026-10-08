-- Prove2me | solution 1 for MartinetReg.VI.eq9
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T13:54:18.603288+00:00
-- url     : https://prove2.me/submissions/b5fd0004-4362-41f3-ab88-cc1cd858c00b

import Definitions.Def_MartinetReg_VI_Setting
set_option autoImplicit false
section
set_option autoImplicit false
open Filter Topology
namespace MartinetVICodex
open MartinetReg.VI
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem minty_forward (T : H → StrongDual ℝ H) (C : Set H)
    (hmono : MonotoneOnSet T C) {z : H} (hz : z ∈ solSet T C) :
    z ∈ C ∧ ∀ y ∈ C, 0 ≤ T y (y-z) := by
  refine ⟨hz.1, fun y hy => ?_⟩
  have hm := hmono y hy z hz.1
  have hs := hz.2 y hy
  change 0 ≤ T y (y-z)-T z (y-z) at hm
  linarith

theorem minty_reverse (T : H → StrongDual ℝ H) (C : Set H)
    (hC : Convex ℝ C) (hhemi : HemicontinuousOn T C) {z : H}
    (hz : z ∈ C ∧ ∀ y ∈ C, 0 ≤ T y (y-z)) : z ∈ solSet T C := by
  refine ⟨hz.1, fun y hy => ?_⟩
  let a : ℕ → ℝ := fun n => 1/(n+1 : ℝ)
  have ha (n : ℕ) : 0 < a n ∧ a n ≤ 1 := by
    dsimp [a]; constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : 0 < (n+1 : ℝ))).mpr
      linarith [Nat.cast_nonneg (α := ℝ) n]
  have hn (n : ℕ) : 0 ≤ T ((1-a n) • z+a n • y) (y-z) := by
    have hc : (1-a n) • z+a n • y ∈ C :=
      hC hz.1 hy (by linarith [(ha n).2]) (ha n).1.le (by ring)
    have hp := hz.2 _ hc
    have he : (1-a n) • z+a n • y-z = a n • (y-z) := by
      rw [smul_sub,sub_smul,one_smul]; abel
    rw [he,map_smul] at hp
    simp only [smul_eq_mul] at hp
    exact nonneg_of_mul_nonneg_right hp (ha n).1
  have hat : Tendsto a atTop (𝓝[Set.Icc (0 : ℝ) 1] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall ?_⟩
    intro n; exact ⟨(ha n).1.le,(ha n).2⟩
  have ht := (hhemi z hz.1 y hy (y-z) 0 (by simp)).tendsto.comp hat
  have ht' : Tendsto (fun n => T ((1-a n) • z+a n • y) (y-z)) atTop
      (𝓝 (T z (y-z))) := by simpa only [Function.comp_def, sub_zero, zero_smul, one_smul, add_zero] using ht
  exact (isClosed_Ici : IsClosed (Set.Ici (0 : ℝ))).mem_of_tendsto ht'
    (Eventually.of_forall hn)

theorem minty (T : H → StrongDual ℝ H) (C : Set H) (hS : Standing T C) :
    solSet T C = {z | z ∈ C ∧ ∀ y ∈ C, 0 ≤ T y (y-z)} := by
  ext z; exact ⟨minty_forward T C hS.mono, minty_reverse T C hS.convex hS.hemi⟩
end MartinetVICodex

end

section
set_option autoImplicit false
open Filter Topology
namespace MartinetVICodex
open MartinetReg.VI
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem iterates_mem (T : H → StrongDual ℝ H) (C : Set H) (x : ℕ → H)
    (hx : IsRegSeq T C x) (n : ℕ) : x n ∈ C := by
  cases n with
  | zero => exact hx.1
  | succ n => exact (hx.2 n).1

theorem step_energy (T : H → StrongDual ℝ H) (C : Set H)
    (hmono : MonotoneOnSet T C) {xn y z : H}
    (hy : IsRegStep T C xn y) (hz : z ∈ solSet T C) :
    ‖y-z‖^2 ≤ ‖xn-z‖^2-‖y-xn‖^2 := by
  have hm := (minty_forward T C hmono hz).2 y hy.1
  have hs := hy.2 z hz.1
  have hT : T y (z-y) = -T y (y-z) := by rw [← neg_sub y z,map_neg]
  have hi : inner ℝ (y-xn) (z-y) = -inner ℝ (y-xn) (y-z) := by
    rw [← neg_sub y z,inner_neg_right]
  rw [hT,hi] at hs
  have hinner : inner ℝ (y-xn) (y-z) ≤ 0 := by linarith
  have he : xn-z = (y-z)-(y-xn) := by abel
  have hn := norm_sub_sq_real (y-z) (y-xn)
  rw [← he] at hn
  have hc : inner ℝ (y-z) (y-xn) = inner ℝ (y-xn) (y-z) := real_inner_comm _ _
  rw [hc] at hn
  nlinarith

theorem eq7 (T : H → StrongDual ℝ H) (C : Set H) (hS : Standing T C)
    (x : ℕ → H) (hx : IsRegSeq T C x) (z : H) (hz : z ∈ solSet T C) (n : ℕ) :
    ‖x (n+1)-z‖^2 ≤ ‖x n-z‖^2-‖x (n+1)-x n‖^2 :=
  step_energy T C hS.mono (hx.2 n) hz
end MartinetVICodex

end

section
set_option autoImplicit false
open Filter Topology Finset
namespace MartinetVICodex

/-- A finite bilinear minimax criterion, applied below to original monotone operators.
The Sion interface follows the repository's Hart-Schmeidler minimax pattern. -/
theorem finite_minimax_criterion {I : Type*} [Fintype I] [Nonempty I]
    (A : I → I → ℝ)
    (hA : ∀ p ∈ stdSimplex ℝ I, 0 ≤ ∑ i, ∑ j, p i*p j*A i j) :
    ∃ q ∈ stdSimplex ℝ I, ∀ p ∈ stdSimplex ℝ I,
      0 ≤ ∑ i, ∑ j, p i*q j*A i j := by
  classical
  let f : (I → ℝ) → (I → ℝ) → ℝ := fun p q => ∑ i, ∑ j, p i*q j*A i j
  have hc1 (q : I → ℝ) : Continuous (fun p => f p q) := by dsimp [f]; fun_prop
  have hc2 (p : I → ℝ) : Continuous (fun q => f p q) := by dsimp [f]; fun_prop
  have hl1 (q p p' : I → ℝ) (a b : ℝ) :
      f (a • p+b • p') q = a*f p q+b*f p' q := by
    simp only [f,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_sum,← sum_add_distrib]
    apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; ring
  have hl2 (p q q' : I → ℝ) (a b : ℝ) :
      f p (a • q+b • q') = a*f p q+b*f p q' := by
    simp only [f,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_sum,← sum_add_distrib]
    apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; ring
  have hconv (q : I → ℝ) : ConvexOn ℝ (stdSimplex ℝ I) (fun p => f p q) := by
    refine ⟨convex_stdSimplex ℝ I, ?_⟩
    intro p _ p' _ a b _ _ _
    change f (a • p+b • p') q ≤ a*f p q+b*f p' q
    rw [hl1]
  have hconc (p : I → ℝ) : ConcaveOn ℝ (stdSimplex ℝ I) (fun q => f p q) := by
    refine ⟨convex_stdSimplex ℝ I, ?_⟩
    intro q _ q' _ a b _ _ _
    change a*f p q+b*f p q' ≤ f p (a • q+b • q')
    rw [hl2]
  have hne : (stdSimplex ℝ I).Nonempty :=
    ⟨Pi.single (Classical.arbitrary I) 1,single_mem_stdSimplex ℝ _⟩
  obtain ⟨p,hp,q,hq,hs⟩ := Sion.exists_isSaddlePointOn (X := stdSimplex ℝ I)
    (Y := stdSimplex ℝ I) (f := f) hne (convex_stdSimplex ℝ I)
    (isCompact_stdSimplex ℝ I)
    (fun q _ => (hc1 q).lowerSemicontinuous.lowerSemicontinuousOn _)
    (fun q _ => (hconv q).quasiconvexOn)
    (convex_stdSimplex ℝ I) hne (isCompact_stdSimplex ℝ I)
    (fun p _ => (hc2 p).upperSemicontinuous.upperSemicontinuousOn _)
    (fun p _ => (hconc p).quasiconcaveOn)
  exact ⟨q,hq,fun p' hp' => (hA p hp).trans (hs p' hp' p hp)⟩

/-- Pairwise nonnegative symmetric sums supply the finite minimax premise. -/
theorem matrix_simplex_nonneg {I : Type*} [Fintype I] (A : I → I → ℝ)
    (hA : ∀ i j, 0 ≤ A i j+A j i) (p : I → ℝ) (hp : p ∈ stdSimplex ℝ I) :
    0 ≤ ∑ i, ∑ j, p i*p j*A i j := by
  classical
  have ht : (∑ i, ∑ j, p i*p j*A j i) = ∑ i, ∑ j, p i*p j*A i j := by
    rw [sum_comm]; apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro j _; ring
  have hn : 0 ≤ ∑ i, ∑ j, p i*p j*(A i j+A j i) :=
    sum_nonneg fun i _ => sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hp.1 i) (hp.1 j)) (hA i j)
  have he : (∑ i, ∑ j, p i*p j*(A i j+A j i)) =
      (∑ i, ∑ j, p i*p j*A i j)+(∑ i, ∑ j, p i*p j*A j i) := by
    simp only [mul_add,sum_add_distrib]
  rw [he,ht] at hn; linarith
end MartinetVICodex

end

section
set_option autoImplicit false
open Finset Filter Topology
namespace MartinetVICodex
open MartinetReg.VI
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Every finite family of Minty inequalities is feasible, using monotonicity only. -/
theorem finite_minty_feasible {I : Type*} [Fintype I] [Nonempty I]
    (T : H → StrongDual ℝ H) (C : Set H) (hC : Convex ℝ C)
    (hmono : MonotoneOnSet T C) (y : I → H) (hy : ∀ i, y i ∈ C) :
    ∃ u ∈ C, ∀ i, 0 ≤ T (y i) (y i-u) := by
  classical
  let A : I → I → ℝ := fun i j => T (y i) (y i-y j)
  have hA (i j : I) : 0 ≤ A i j+A j i := by
    have hm := hmono (y i) (hy i) (y j) (hy j)
    change 0 ≤ T (y i) (y i-y j)-T (y j) (y i-y j) at hm
    have he : T (y j) (y j-y i) = -T (y j) (y i-y j) := by
      rw [← neg_sub (y i) (y j),map_neg]
    dsimp [A]; rw [he]; linarith
  obtain ⟨q,hq,hqs⟩ := finite_minimax_criterion A
    (fun p hp => matrix_simplex_nonneg A hA p hp)
  let u := ∑ j, q j • y j
  have hu : u ∈ C := hC.sum_mem (fun i _ => hq.1 i) hq.2 (fun i _ => hy i)
  refine ⟨u,hu,fun i => ?_⟩
  have hi : 0 ≤ ∑ j, q j*A i j := by
    simpa [Pi.single_apply] using hqs (Pi.single i 1) (single_mem_stdSimplex ℝ i)
  have he : T (y i) (y i-u) = ∑ j, q j*A i j := by
    simp only [u,A,map_sub,map_sum,map_smul,smul_eq_mul,mul_sub,sum_sub_distrib,
      ← sum_mul,hq.2,one_mul]
  rw [he]; exact hi
end MartinetVICodex

end

section
set_option autoImplicit false
open Set Topology
namespace MartinetVICodex
theorem weak_closed_miao {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {S : Set H} (hS : Convex ℝ S) (hc : IsClosed S) :
    IsClosed (toWeakSpace ℝ H '' S) := by
  have he := hS.toWeakSpace_closure ℝ
  rw [hc.closure_eq] at he
  exact closure_eq_iff_isClosed.mp he.symm

theorem weak_compact_miao {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
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
  rwa [(weak_closed_miao hS hc).closure_eq] at hn

end MartinetVICodex

end

section
set_option autoImplicit false
open Set Filter Topology
namespace MartinetVICodex
open MartinetReg.VI
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Original infinite-dimensional existence, via finite Minty feasibility and weak compactness. -/
theorem exists_solution (T : H → StrongDual ℝ H) (C : Set H) (hS : Standing T C)
    (hne : C.Nonempty) : (solSet T C).Nonempty := by
  classical
  let e := toWeakSpace ℝ H
  let K : C → Set (WeakSpace ℝ H) := fun y => {w | 0 ≤ T y.val (y.val-e.symm w)}
  have hK (y : C) : IsClosed (K y) := by
    have heval : Continuous (fun w : WeakSpace ℝ H => T y.val (e.symm w)) :=
      WeakBilin.eval_continuous (topDualPairing ℝ H).flip (T y.val)
    simpa only [K,map_sub] using
      (isClosed_le continuous_const (continuous_const.sub heval) :
        IsClosed {w : WeakSpace ℝ H | (0 : ℝ) ≤ T y.val y.val-T y.val (e.symm w)})
  have hfinite (s : Finset C) : (e '' C ∩ ⋂ y ∈ s, K y).Nonempty := by
    by_cases hs : s.Nonempty
    · let : Nonempty ↑s := ⟨⟨hs.choose,hs.choose_spec⟩⟩
      obtain ⟨u,hu,hus⟩ := finite_minty_feasible T C hS.convex hS.mono
        (fun i : s => i.val.val) (fun i => i.val.property)
      refine ⟨e u,⟨u,hu,rfl⟩, ?_⟩
      simp only [mem_iInter]
      intro y hy
      simpa only [K,mem_ofPred_eq,LinearEquiv.symm_apply_apply] using hus ⟨y,hy⟩
    · obtain ⟨u,hu⟩ := hne
      have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      simp only [hs0,Finset.notMem_empty,iInter_of_empty,iInter_univ,
        inter_univ]
      exact ⟨e u,⟨u,hu,rfl⟩⟩
  have hc := weak_compact_miao hS.convex hS.closed hS.bounded
  obtain ⟨w,hwC,hwK⟩ := hc.inter_iInter_nonempty K hK hfinite
  obtain ⟨u,hu,rfl⟩ := hwC
  refine ⟨u,minty_reverse T C hS.convex hS.hemi ⟨hu, ?_⟩⟩
  intro y hy
  simpa only [K,e,mem_ofPred_eq,LinearEquiv.symm_apply_apply] using mem_iInter.mp hwK ⟨y,hy⟩
end MartinetVICodex

end

section
set_option autoImplicit false
open Filter Topology Finset
namespace MartinetVICodex
open MartinetReg.VI
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem step_square_sum_bound (T : H → StrongDual ℝ H) (C : Set H) (hS : Standing T C)
    (x : ℕ → H) (hx : IsRegSeq T C x) (z : H) (hz : z ∈ solSet T C) (N : ℕ) :
    (∑ n ∈ range N, ‖x (n+1)-x n‖^2)+‖x N-z‖^2 ≤ ‖x 0-z‖^2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have h := eq7 T C hS x hx z hz N
    nlinarith

theorem lemma1 (T : H → StrongDual ℝ H) (C : Set H) (hS : Standing T C)
    (x : ℕ → H) (hx : IsRegSeq T C x) :
    Tendsto (fun n => ‖x (n+1)-x n‖) atTop (𝓝 0) := by
  obtain ⟨z,hz⟩ := exists_solution T C hS ⟨x 0,hx.1⟩
  have hsum : Summable (fun n => ‖x (n+1)-x n‖^2) := by
    apply summable_of_sum_range_le (fun n => sq_nonneg _) (c := ‖x 0-z‖^2)
    intro N
    have h := step_square_sum_bound T C hS x hx z hz N
    nlinarith [sq_nonneg ‖x N-z‖]
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hsum.tendsto_atTop_zero
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using ht
end MartinetVICodex

end

section
set_option autoImplicit false
open Filter Topology
namespace MartinetVICodex
open MartinetReg.VI
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem eq8 (T : H → StrongDual ℝ H) (C : Set H) (hS : Standing T C)
    (x : ℕ → H) (hx : IsRegSeq T C x) :
    ∀ y ∈ C, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      -ε ≤ T (x (n+1)) (y-x (n+1)) := by
  intro y hy ε hε
  obtain ⟨R,hR,hbound⟩ := hS.bounded.exists_pos_norm_le
  have ht : Tendsto (fun n => ‖x (n+1)-x n‖*(2*R)) atTop (𝓝 0) := by
    simpa using (lemma1 T C hS x hx).mul_const (2*R)
  have hev : ∀ᶠ n in atTop, ‖x (n+1)-x n‖*(2*R) < ε :=
    (tendsto_order.mp ht).2 ε hε
  filter_upwards [hev] with n hn
  have hd : ‖y-x (n+1)‖ ≤ 2*R := by
    have := norm_sub_le y (x (n+1))
    have h1 := hbound y hy
    have h2 := hbound _ (iterates_mem T C x hx (n+1))
    linarith
  have hi := real_inner_le_norm (x (n+1)-x n) (y-x (n+1))
  have hp := mul_le_mul_of_nonneg_left hd (norm_nonneg (x (n+1)-x n))
  have hs := (hx.2 n).2 y hy
  linarith

theorem eq9 (T : H → StrongDual ℝ H) (C : Set H) (hS : Standing T C)
    (x : ℕ → H) (hx : IsRegSeq T C x) :
    ∀ y ∈ C, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, -ε ≤ T y (y-x n) := by
  intro y hy ε hε
  have hev : ∀ᶠ n in atTop, -ε ≤ T y (y-x (n+1)) := by
    filter_upwards [eq8 T C hS x hx y hy ε hε] with n hn
    have hm := hS.mono y hy (x (n+1)) (iterates_mem T C x hx (n+1))
    change 0 ≤ T y (y-x (n+1))-T (x (n+1)) (y-x (n+1)) at hm
    linarith
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  filter_upwards [eventually_ge_atTop (N+1)] with n hn
  have hp := hN (n-1) (by omega)
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hp
end MartinetVICodex

end

set_option autoImplicit false
open MartinetReg.VI Filter Topology
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → StrongDual ℝ H) (C : Set H) (hS : Standing T C)
    (x : ℕ → H) (hx : IsRegSeq T C x) :
    ∀ y ∈ C, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, -ε ≤ T y (y - x n) := by
  exact MartinetVICodex.eq9 T C hS x hx



#print axioms solution
