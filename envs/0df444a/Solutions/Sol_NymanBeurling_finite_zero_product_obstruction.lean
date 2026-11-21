-- Prove2me | solution 1 for NymanBeurling.finite_zero_product_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:23:23.785163+00:00
-- url     : https://prove2.me/submissions/4380accc-7325-4083-bb64-8934c1619739

import Mathlib

open Complex Function Set Filter Topology MeasureTheory
open scoped ComplexConjugate
noncomputable section
private abbrev HP := {z : ℂ // 1/2 < z.re}
private def gd (z w : HP) : ℂ := z.val + conj w.val - 1
private theorem gd_re (z w : HP) : 0 < (gd z w).re := by
  simp [gd]; linarith [z.property,w.property]
private theorem gd_ne (z w : HP) : gd z w ≠ 0 := fun h => by simpa [h] using gd_re z w
private theorem gd_conj (z w : HP) : conj (gd z w)=gd w z := by simp [gd,add_comm]
private def bf (v z : HP) : ℂ := (z.val-v.val)/gd z v

private theorem cross_factor (z w v : HP) :
    (gd z w)⁻¹ - gd v v / (gd z v*gd v w) = bf v z*conj (bf v w)/gd z w := by
  simp only [bf,map_div₀,map_sub,gd_conj]
  field_simp [gd_ne]
  dsimp [gd]
  ring

private theorem strip_gram (z w v : HP) (b : HP→ℂ) (hv : b v ≠ 0) :
    b z*conj (b w)/gd z w - (b z*conj (b v)/gd z v) * (b v*conj (b w)/gd v w) /
      (b v*conj (b v)/gd v v) =
    (b z*bf v z)*conj (b w*bf v w)/gd z w := by
  have hconj : conj (b v) ≠ 0 := by simpa using hv
  calc _ = b z * conj (b w) * ((gd z w)⁻¹ - gd v v / (gd z v*gd v w)) := by
         field_simp [gd_ne,hv,hconj]
       _ = _ := by rw [cross_factor,map_mul]; ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
private def remv (p x : E) : E := x-(inner ℂ p x / inner ℂ p p) • p
private theorem remv_gram {p : E} (hp : p≠0) (x y : E) :
    inner ℂ (remv p x) (remv p y) = inner ℂ x y - inner ℂ x p*inner ℂ p y / inner ℂ p p := by
  have h₀ : inner ℂ p p ≠ 0 := inner_self_ne_zero.mpr hp
  simp only [remv,inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,map_div₀,inner_conj_symm]
  field_simp [h₀];ring

private theorem norm_of_gram (K : HP→E) (b : HP→ℂ)
    (hg : ∀ z w, inner ℂ (K z) (K w)=b z*conj (b w)/gd z w) (o : HP) :
    ‖K o‖^2 = ‖b o‖^2/(2*o.val.re-1) := by
  rw [←inner_self_eq_norm_sq (𝕜 := ℂ),hg,Complex.mul_conj,gd,Complex.add_conj,←Complex.ofReal_one,
    ←Complex.ofReal_sub,←Complex.ofReal_div,Complex.normSq_eq_norm_sq]
  rfl

private theorem gram_bound (T : Finset HP) (o : HP) (K : HP→E) (b : HP→ℂ) (x : E)
    (hg : ∀ z w, inner ℂ (K z) (K w)=b z*conj (b w)/gd z w)
    (hb : ∀ z ∈ T, b z ≠ 0)
    (hx : ∀ z ∈ T, inner ℂ (K z) x=inner ℂ (K z) (K o)) :
    ‖K o‖^2-‖x‖^2 ≤ ‖b o‖^2/(2*o.val.re-1)* ∏ z ∈ T, ‖bf z o‖^2 := by
  classical
  induction T using Finset.induction_on generalizing K b x with
  | empty => simp [norm_of_gram K b hg o]
  | @insert v T hv ih =>
    have hbv := hb v (Finset.mem_insert_self v T)
    have hnv : K v ≠ 0 := by
      intro h
      have hh := hg v v
      rw [h,inner_zero_left] at hh
      exact (div_ne_zero (mul_ne_zero hbv (by simpa using hbv)) (gd_ne v v)) hh.symm
    let K' := fun z => remv (K v) (K z)
    let b' := fun z => b z * bf v z
    let x' := remv (K v) x
    have hg' (z w : HP) : inner ℂ (K' z) (K' w) = b' z*conj (b' w)/gd z w := by
      simp only [K',remv_gram hnv,hg,b']; exact strip_gram _ _ _ _ hbv
    have hb' (z : HP) (hz : z ∈ T) : b' z ≠ 0 := by
      have hn : z.val ≠ v.val := fun h => hv (Subtype.ext h ▸ hz)
      exact mul_ne_zero (hb z (Finset.mem_insert_of_mem hz)) (div_ne_zero (sub_ne_zero.mpr hn) (gd_ne _ _))
    have hxv := hx v (Finset.mem_insert_self v T)
    have hxc : inner ℂ x (K v) = inner ℂ (K o) (K v) := by
      simpa only [inner_conj_symm] using congrArg conj hxv
    have hx' (z : HP) (hz : z ∈ T) : inner ℂ (K' z) x' = inner ℂ (K' z) (K' o) := by
      simp only [K',x',remv_gram hnv,hxv,hx z (Finset.mem_insert_of_mem hz)]
    have hdiff : ‖K' o‖^2-‖x'‖^2 = ‖K o‖^2-‖x‖^2 := by
      simp only [←inner_self_eq_norm_sq (𝕜 := ℂ),K',x',remv_gram hnv,hxv,hxc,map_sub]
      ring
    have h := ih K' b' x' hg' hb' hx'
    rw [hdiff] at h
    rw [Finset.prod_insert hv]
    convert h using 1
    rw [show b' o=b o*bf v o from rfl,norm_mul,mul_pow]
    ring
private def edge (n : ℕ) := Real.log (n+1:ℝ)
private def tile (n : ℕ) := Ico (edge n) (edge (n+1))
private theorem edge_mono : Monotone edge := by
  intro n m h
  apply Real.log_le_log (by positivity)
  exact_mod_cast (by omega : n+1 ≤ m+1)
private theorem tile_union : ⋃ n, tile n = Ici 0 := by
  have hlim : Tendsto edge atTop atTop := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hn : ¬BddAbove (Set.range edge) := not_bddAbove_iff.mpr fun x => by
    obtain ⟨n,hn⟩ := (hlim.eventually_gt_atTop x).exists
    exact ⟨_,⟨n,rfl⟩,hn⟩
  have h := iUnion_Ico_map_succ_eq_Ici (f := edge) (fun n => edge_mono (bot_le : ⊥≤n)) hn
  simpa [tile,edge,Nat.succ_eq_add_one] using h
private theorem tile_disj : Pairwise (Function.onFun Disjoint tile) := by
  intro i j h
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne h with h|h
  · exact (not_lt_of_ge (le_trans (edge_mono (Nat.succ_le_of_lt h)) hy.1)) hx.2
  · exact (not_lt_of_ge (le_trans (edge_mono (Nat.succ_le_of_lt h)) hx.1)) hy.2

private def step (a : ℕ → ℂ) (x : ℝ) := if 0≤x then
  (Real.exp (-(1/2:ℝ)*x):ℂ) * a (⌊Real.exp x⌋₊-1) else 0
private theorem step_meas (a : ℕ → ℂ) : Measurable (step a) := by
  have ha : Measurable a := measurable_of_countable a
  unfold step
  exact Measurable.ite measurableSet_Ici (by fun_prop) measurable_const

private theorem step_bound (a : ℕ → ℂ) (B : ℝ) (hb : ∀ n, ‖a n‖ ≤ B) (x : ℝ) :
    ‖step a x‖ ≤ (Ici 0).indicator (fun x : ℝ => B*Real.exp (-(1/2:ℝ)*x)) x := by
  by_cases hx : 0≤x
  · simp only [step,if_pos hx,indicator_of_mem (show x∈Ici 0 from hx),norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (hb _) (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  · simp [step,hx,indicator_of_notMem (show x∉Ici 0 from hx)]
private theorem step_int (a : ℕ → ℂ) (B : ℝ) (hb : ∀ n, ‖a n‖ ≤ B) : Integrable (step a) := by
  have hh : IntegrableOn (fun x : ℝ => B*Real.exp (-(1/2:ℝ)*x)) (Ici 0) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi ((integrableOn_exp_mul_Ioi (by norm_num : -(1/2:ℝ)<0) 0).const_mul B)
  exact (hh.integrable_indicator measurableSet_Ici).mono' (step_meas _).aestronglyMeasurable (.of_forall (step_bound a B hb))

private theorem step_L2 (a : ℕ → ℂ) (B : ℝ) (hb : ∀ n, ‖a n‖ ≤ B) : MemLp (step a) 2 := by
  apply (memLp_two_iff_integrable_sq_norm (step_meas _).aestronglyMeasurable).mpr
  have hh : IntegrableOn (fun x : ℝ => B^2*Real.exp ((-1:ℝ)*x)) (Ici 0) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi ((integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0).const_mul _)
  apply (hh.integrable_indicator measurableSet_Ici).mono' ((step_meas a).norm.pow_const 2).aestronglyMeasurable (.of_forall fun x => ?_)
  by_cases hx : 0≤x
  · have hm := pow_le_pow_left₀ (norm_nonneg _) (step_bound a B hb x) 2
    rw [indicator_of_mem (show x∈Ici 0 from hx),mul_pow,←Real.exp_nat_mul] at hm
    simpa [indicator_of_mem (show x∈Ici 0 from hx),Real.norm_eq_abs,abs_of_nonneg,mul_assoc] using hm
  · simp [step,hx,indicator_of_notMem (show x∉Ici 0 from hx)]

private theorem on_tile (a : ℕ → ℂ) (n : ℕ) {x : ℝ} (h : x ∈ tile n) :
    step a x = (Real.exp (-(1/2:ℝ)*x):ℂ)*a n := by
  have hx : 0≤x := le_trans (by exact Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]) : 0≤edge n) h.1
  have hl : (n+1:ℝ) ≤ Real.exp x := (Real.log_le_iff_le_exp (by positivity)).mp h.1
  have hr : Real.exp x < ((n+1:ℕ)+1:ℝ) := (Real.lt_log_iff_exp_lt (by positivity)).mp h.2
  have hf : ⌊Real.exp x⌋₊ = n+1 := (Nat.floor_eq_iff (Real.exp_pos _).le).mpr ⟨by exact_mod_cast hl,hr⟩
  simp [step,hx,hf]

private theorem tile_int {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (g : ℝ → G)
    (hg : Integrable g) (hsupp : ∀ x < 0, g x = 0) :
    HasSum (fun n => ∫ x in tile n, g x) (∫ x, g x) := by
  have hh := hasSum_integral_iUnion (μ := volume) (s := tile) (fun _ => measurableSet_Ico) tile_disj hg.integrableOn
  convert hh using 1
  rw [tile_union]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ici (0:ℝ)) (f := g) (fun x hx => hsupp x (lt_of_not_ge hx))).symm

private theorem wexp_end (s : ℂ) (n : ℕ) :
    Complex.exp (-s * (edge n : ℂ)) = ((n+1:ℕ):ℂ)^(-s) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Nat.succ_ne_zero n))]
  dsimp [edge]; rw [Complex.ofReal_log (by positivity)]
  push_cast; congr 1; ring

private theorem step_energy_tile (a : ℕ→ℂ) (n : ℕ) :
    (∫ u in tile n, ‖step a u‖^2) = ‖a n‖^2/((n+1:ℝ)*(n+2:ℝ)) := by
  have he : (∫ u in tile n, ‖step a u‖^2) = (∫ u in tile n, Real.exp (-u) * ‖a n‖^2) := by
    apply setIntegral_congr_fun measurableSet_Ico
    intro u hu
    change ‖step a u‖^2 = _
    rw [on_tile a n hu,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le,mul_pow,
      ←Real.exp_nat_mul]
    congr 2; push_cast; ring
  have hi (n : ℕ) : Real.exp (-edge n) = (n+1:ℝ)⁻¹ := by
    rw [Real.exp_neg,edge,Real.exp_log (by positivity)]
  rw [he,integral_mul_const,tile,integral_Ico_eq_integral_Ioc,←intervalIntegral.integral_of_le (edge_mono (Nat.le_succ n))]
  have hh : (∫ u in edge n..edge (n+1), Real.exp (-u)) = Real.exp (-edge n) - Real.exp (-edge (n+1)) := by
    simpa [integral_exp] using (intervalIntegral.integral_comp_neg (f := Real.exp) (a := edge n) (b := edge (n+1)))
  rw [hh,hi,hi]
  push_cast; field_simp; ring

private def pval (s : ℂ) (m : ℕ) : ℂ := (m : ℂ) ^ (-s)
private def jump (s : ℂ) (n : ℕ) : ℂ := pval s (n+1) - pval s (n+2)
private def remainder (k m : ℕ) : ℂ := ((m % k : ℕ) : ℂ) / k

private theorem jump_estimate {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖jump s n‖ ≤ ‖s‖ * (n+1 : ℝ)^(-s.re-1) := by
  let a := (n+1 : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hs' : -s ≠ 0 := neg_ne_zero.mpr (by intro h; simp [h] at hs)
  have hd (x : ℝ) (hx : x ∈ Icc a (a+1)) :=
    (hasDerivAt_ofReal_cpow_const (lt_of_lt_of_le ha hx.1).ne' hs').hasDerivWithinAt (s := Icc a (a+1))
  have hb (x : ℝ) (hx : x ∈ Ico a (a+1)) :
      ‖(-s) * (x:ℂ)^(-s-1)‖ ≤ ‖s‖ * a^(-s.re-1) := by
    rw [norm_mul,norm_neg,Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le ha hx.1)]
    simp only [sub_re,neg_re,one_re]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha hx.1 (by linarith)) (norm_nonneg _)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb (a+1) (show a+1 ∈ Icc a (a+1) by constructor <;> linarith)
  rw [norm_sub_rev] at h
  norm_num [jump,pval,a,Nat.cast_add,add_assoc] at h ⊢
  exact h

private theorem sum_rpow (a : ℝ) (ha : a < -1) :
    Summable (fun n : ℕ => (n+1 : ℝ)^a) := by
  simpa using (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr ha)

private theorem remainder_bound {k : ℕ} (hk : 0 < k) (m : ℕ) : ‖remainder k m‖ ≤ 1 := by
  have h := Nat.mod_lt m hk
  simp only [remainder,norm_div,Complex.norm_natCast]
  exact (div_le_one (by positivity)).mpr (by exact_mod_cast h.le)

private theorem bounded_jump_summable {g : ℕ → ℂ} {B : ℝ} (hg : ∀ n, ‖g n‖ ≤ B)
    {s : ℂ} (hs : 0 < s.re) : Summable (fun n => g n * jump s n) := by
  apply Summable.of_norm_bounded ((sum_rpow _ (by linarith : -s.re-1 < -1)).mul_left (B*‖s‖))
  intro n
  rw [norm_mul,mul_assoc]
  exact mul_le_mul (hg n) (jump_estimate hs n) (norm_nonneg _) ((norm_nonneg _).trans (hg n))

private theorem jump_series_analytic {g : ℕ → ℂ} {B : ℝ} (hg : ∀ n, ‖g n‖ ≤ B) :
    AnalyticOnNhd ℂ (fun s => ∑' n, g n * jump s n) {s : ℂ | 0 < s.re} := by
  intro s hs
  change 0 < s.re at hs
  let U := {w : ℂ | s.re / 2 < w.re ∧ ‖w‖ < ‖s‖ + 1}
  have hopen : IsOpen U := (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_norm continuous_const)
  have hsU : s ∈ U := ⟨by linarith,by linarith⟩
  have hdb (n : ℕ) : DifferentiableOn ℂ (fun w => g n * jump w n) U := by
    unfold jump pval
    simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    apply DifferentiableOn.const_mul
    apply DifferentiableOn.sub
    · exact differentiableOn_id.neg.const_cpow (Or.inl (by exact_mod_cast (by omega : n+1 ≠ 0)))
    · exact differentiableOn_id.neg.const_cpow (Or.inl (by exact_mod_cast (by omega : n+2 ≠ 0)))
  apply (Complex.differentiableOn_tsum_of_summable_norm (F := fun n w => g n * jump w n)
    ((sum_rpow _ (by linarith : -(s.re / 2)-1 < -1)).mul_left (B*(‖s‖+1))) hdb hopen _).analyticOnNhd hopen s hsU
  intro n w hw
  have hw' : s.re/2 < w.re ∧ ‖w‖ < ‖s‖+1 := hw
  rw [norm_mul,mul_assoc]
  apply mul_le_mul (hg n) _ (norm_nonneg _) ((norm_nonneg _).trans (hg n))
  apply (jump_estimate (by linarith : 0 < w.re) n).trans
  exact mul_le_mul hw'.2.le (Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith))
    (by positivity) (by positivity)

private theorem remainder_step {k : ℕ} (hk : 0 < k) (m : ℕ) :
    remainder k (m+1) - remainder k m = (k : ℂ)⁻¹ - (if k ∣ m+1 then 1 else 0) := by
  have hk' : (k:ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hr (j : ℕ) : remainder k j = (j:ℂ)/k - ((j/k:ℕ):ℂ) := by
    have h : ((j % k : ℕ):ℂ) + (k:ℂ) * ((j/k:ℕ):ℂ) = (j:ℂ) := by exact_mod_cast Nat.mod_add_div j k
    unfold remainder
    field_simp
    linear_combination h
  rw [hr,hr,Nat.succ_div]
  split_ifs <;> push_cast <;> ring

private theorem pval_hasSum {s : ℂ} (hs : 1 < s.re) : HasSum (pval s) (riemannZeta s) := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  apply ((Complex.summable_one_div_nat_cpow.mpr hs).hasSum).congr_fun
  intro n
  simp [pval,Complex.cpow_neg,one_div]

private theorem multiple_hasSum {k : ℕ} (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun m : ℕ => if k ∣ m then pval s m else 0) (pval s k * riemannZeta s) := by
  have hi : Injective (fun n : ℕ => k*n) := fun _ _ h => Nat.eq_of_mul_eq_mul_left hk h
  apply (hi.hasSum_iff (fun x hx => by
    have h : ¬ k ∣ x := fun ⟨y,hy⟩ => hx ⟨y,hy.symm⟩
    simp [h])).mp
  apply ((pval_hasSum hs).mul_left (pval s k)).congr_fun
  intro n
  simp only [Function.comp_apply,dvd_mul_right,if_true,pval,Nat.cast_mul]
  exact (Complex.mul_cpow_ofReal_nonneg (a := k) (b := n) (by positivity) (by positivity) (-s))

private theorem remainder_dirichlet {k : ℕ} (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => (remainder k (n+1) - remainder k n) * pval s (n+1))
      (((k:ℂ)⁻¹ - pval s k) * riemannZeta s) := by
  let f (m : ℕ) := (k:ℂ)⁻¹ * pval s m - (if k ∣ m then pval s m else 0)
  have hs' : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  have h : HasSum f (((k:ℂ)⁻¹ - pval s k) * riemannZeta s) := by
    rw [sub_mul]
    exact ((pval_hasSum hs).mul_left (k:ℂ)⁻¹).sub (multiple_hasSum hk hs)
  have h0 : f 0 = 0 := by simp [f,pval,Complex.zero_cpow (neg_ne_zero.mpr hs')]
  have h' : HasSum (fun n => f (n+1)) (((k:ℂ)⁻¹ - pval s k) * riemannZeta s) := by
    simpa [h0] using (hasSum_nat_add_iff' 1).mpr h
  apply h'.congr_fun
  intro n
  rw [remainder_step hk, sub_mul]
  dsimp [f]; split_ifs <;> simp

private theorem initial_transform {k : ℕ} (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, remainder k (n+1) * jump s n) = ((k:ℂ)⁻¹ - pval s k) * riemannZeta s := by
  have hq := (summable_nat_add_iff 1).mpr (pval_hasSum hs).summable
  have hb (d : ℕ) : Summable (fun n : ℕ => remainder k (n+d) * pval s (n+1)) := by
    apply Summable.of_norm_bounded hq.norm
    intro n
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_right (remainder_bound hk (n+d)) (norm_nonneg (pval s (n+1)))
  have h0 : Summable (fun n : ℕ => remainder k n * pval s (n+1)) := by simpa using hb 0
  have h1 := hb 1
  have hshift := h0.tsum_eq_zero_add
  simp only [remainder, Nat.zero_mod,Nat.cast_zero,zero_div,zero_mul,zero_add] at hshift
  rw [← (remainder_dirichlet hk hs).tsum_eq]
  simp only [jump,mul_sub,sub_mul]
  rw [h1.tsum_sub ((summable_nat_add_iff 1).mpr h0), h1.tsum_sub h0]
  exact congrArg _ hshift.symm

-- Remove the pole of zeta at one before applying uniqueness on the connected half-plane.
private theorem remainder_transform {k : ℕ} (hk : 0 < k) {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    (∑' n : ℕ, remainder k (n+1) * jump s n) = ((k:ℂ)⁻¹ - pval s k) * riemannZeta s := by
  let U := {z : ℂ | 0 < z.re}
  let G (z : ℂ) := ∑' n, remainder k (n+1) * jump z n
  let C (z : ℂ) := (k:ℂ)⁻¹ - pval z k
  have hG : AnalyticOnNhd ℂ G U := jump_series_analytic (fun n => remainder_bound hk (n+1))
  have hC : Differentiable ℂ C := by
    intro z
    exact (differentiableAt_const _).sub (differentiableAt_id.neg.const_cpow (Or.inl (by exact_mod_cast hk.ne')))
  have ha : AnalyticOnNhd ℂ (fun z => (z-1) * G z) U := (analyticOnNhd_id.sub analyticOnNhd_const).mul hG
  have hb : AnalyticOnNhd ℂ (fun z => C z * riemannZeta₁ z) U :=
    (hC.mul differentiable_riemannZeta₁).differentiableOn.analyticOnNhd (isOpen_lt continuous_const continuous_re)
  have he (z : ℂ) (hz : 1 < z.re) : (z-1) * G z = C z * riemannZeta₁ z := by
    have hz' : z ≠ 1 := by intro h; simp [h] at hz
    dsimp [G,C]
    rw [initial_transform hk hz,riemannZeta_eq_inv_sub_mul hz']
    field_simp
  have htwo : (2:ℂ) ∈ U := by change 0 < (2:ℂ).re; norm_num
  have h := ha.eqOn_of_preconnected_of_eventuallyEq hb (convex_halfSpace_re_gt 0).isPreconnected htwo
    (eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds (show (1:ℝ) < (2:ℂ).re by norm_num)) he)
    (show s ∈ U from hs)
  change G s = C s * riemannZeta s
  rw [riemannZeta_eq_inv_sub_mul h1]
  have hne := sub_ne_zero.mpr h1
  field_simp
  linear_combination h

private theorem pval_zero {s : ℂ} (hs : 0 < s.re) : Tendsto (fun n => pval s (n+1)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := (tendsto_rpow_neg_atTop hs).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h' := h.comp (tendsto_add_atTop_nat 1)
  apply h'.congr
  intro n
  simp only [Function.comp_apply,pval]
  exact (Complex.norm_cpow_eq_rpow_re_of_pos (x := (n+1:ℕ)) (by positivity) (-s)).symm

private theorem jump_one {s : ℂ} (hs : 0 < s.re) : HasSum (jump s) 1 := by
  have hsum : Summable (jump s) := by simpa using (bounded_jump_summable (g := fun _ => 1) (B := 1) (by simp) hs)
  apply hsum.hasSum_iff_tendsto_nat.mpr
  have htel (N : ℕ) : ∑ n ∈ Finset.range N, jump s n = 1 - pval s (N+1) := by
    induction N with
    | zero => simp [pval]
    | succ N ih => rw [Finset.sum_range_succ,ih]; dsimp [jump]; ring
  simp_rw [htel]
  simpa using (tendsto_const_nhds (x := (1:ℂ))).sub (pval_zero hs)

private def wt (n : ℕ) : ℝ := (n+1 : ℝ)*(n+2 : ℝ)

private theorem weight_pos (n : ℕ) : 0 < wt n := by unfold wt; positivity


private theorem residual_hasSum {s : ℂ} (hs : 1/2 < s.re) (h1 : s ≠ 1) (hz : riemannZeta s = 0)
    (S : Finset ℕ) (c : ℕ → ℂ) :
    HasSum (fun n => (1 - ∑ k ∈ S, c k * remainder (k+2) (n+1)) * jump s n) 1 := by
  have hkernel (k : ℕ) : HasSum (fun n => remainder (k+2) (n+1) * jump s n) 0 := by
    have h := bounded_jump_summable (fun n => remainder_bound (by omega : 0 < k+2) (n+1)) (by linarith : 0 < s.re)
    simpa [remainder_transform (by omega : 0 < k+2) (by linarith : 0 < s.re) h1,hz] using h.hasSum
  have hlin := hasSum_sum (s := S) (fun k _ => (hkernel k).mul_left (c k))
  have h := (jump_one (by linarith : 0 < s.re)).sub hlin
  simpa [sub_mul,Finset.sum_mul,mul_assoc] using h

private def qrem (k m : ℕ) : ℚ := (m % k : ℕ) / (k:ℚ)
private def resid (c : ℕ →₀ ℚ) (n : ℕ) : ℚ :=
  1 - ∑ k ∈ c.support, c k * qrem (k+2) (n+1)
private def qweight (n : ℕ) : ℚ := (n+1:ℚ)*(n+2:ℚ)
private def part (c : ℕ →₀ ℚ) (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range N, (resid c n)^2 / qweight n
private def major (c : ℕ →₀ ℚ) : ℚ := 1 + ∑ k ∈ c.support, |c k|
private def certificate (c : ℕ →₀ ℚ) (H : ℕ) : ℚ := part c H + (major c)^2/(H+1)

private theorem resid_bound (c : ℕ →₀ ℚ) (n : ℕ) : |resid c n| ≤ major c := by
  unfold resid major
  refine (abs_sub _ _).trans ?_
  simp only [abs_one,add_le_add_iff_left]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  rw [abs_mul]
  have hb : 0 ≤ qrem (k+2) (n+1) := by unfold qrem; positivity
  have h1 : qrem (k+2) (n+1) ≤ 1 := (div_le_one (by positivity)).mpr (by exact_mod_cast (Nat.mod_lt (n+1) (by omega : 0 < k+2)).le)
  rw [abs_of_nonneg hb]
  exact mul_le_of_le_one_right (abs_nonneg _) h1

private theorem part_le_certificate (c : ℕ →₀ ℚ) (N H : ℕ) : part c N ≤ certificate c H := by
  have hpos (n : ℕ) : 0 < qweight n := by dsimp [qweight]; positivity
  have hm : Monotone (part c) := monotone_nat_of_le_succ fun n => by
    simp only [part, Finset.sum_range_succ,le_add_iff_nonneg_right]
    exact div_nonneg (sq_nonneg _) (hpos n).le
  by_cases h : N ≤ H
  · exact (hm h).trans (le_add_of_nonneg_right (by positivity))
  have hstep (n : ℕ) : certificate c (n+1) ≤ certificate c n := by
    unfold certificate part
    rw [Finset.sum_range_succ,add_assoc]
    rw [add_le_add_iff_left]
    have hR : (resid c n)^2 ≤ (major c)^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (resid_bound c n) 2
    calc
      _ ≤ (major c)^2 / qweight n + (major c)^2/((n+1 : ℕ)+1 : ℚ) :=
        add_le_add (div_le_div_of_nonneg_right hR (hpos n).le) le_rfl
      _ = _ := by unfold qweight; push_cast; field_simp; ring
  have hc := (antitone_nat_of_succ_le hstep) (Nat.le_of_lt (Nat.lt_of_not_ge h))
  exact (le_add_of_nonneg_right (show 0 ≤ (major c)^2/(N+1) by positivity)).trans hc

private theorem embed_resid (c : ℕ →₀ ℚ) (n : ℕ) :
    ‖1 - ∑ k ∈ c.support, (c k : ℂ) * remainder (k+2) (n+1)‖^2 / wt n =
      (((resid c n)^2 / qweight n : ℚ) : ℝ) := by
  have he : (resid c n : ℂ) = 1 - ∑ k ∈ c.support, (c k : ℂ) * remainder (k+2) (n+1) := by
    simp [resid, qrem, remainder]
  rw [←he]
  simp [wt,qweight,Complex.norm_ratCast,sq_abs]

private abbrev posμ := volume.restrict (Ioi (0:ℝ))
private abbrev Hil := Lp ℂ 2 posμ
private def wave (z : HP) (u : ℝ) := Complex.exp ((1/2-conj z.val)*(u:ℂ))

private theorem wave_L2 (z : HP) : MemLp (wave z) 2 posμ := by
  apply (memLp_two_iff_integrable_sq_norm (by unfold wave; fun_prop)).mpr
  have hh : 1-2*z.val.re<0 := by linarith [z.property]
  have he (u : ℝ) : ‖wave z u‖^2=Real.exp ((1-2*z.val.re)*u) := by
    simp only [wave,Complex.norm_exp,←Real.exp_nat_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    congr 1
    norm_num [Complex.sub_re]
    ring
  change IntegrableOn (fun u:ℝ => ‖wave z u‖^2) (Ioi 0)
  simpa only [he] using integrableOn_exp_mul_Ioi hh 0

private def kernel (z : HP) : Hil := (wave_L2 z).toLp (wave z)

private theorem vec_inner {p q : ℝ→ℂ} (hp : MemLp p 2 posμ) (hq : MemLp q 2 posμ) :
    inner ℂ (hp.toLp p) (hq.toLp q) = ∫ u in Ioi (0:ℝ), conj (p u)*q u := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hp.coeFn_toLp,hq.coeFn_toLp] with u hu hv
  simp only [hu,hv,RCLike.inner_apply]; ring

private theorem vec_norm {p : ℝ→ℂ} (hp : MemLp p 2 posμ) :
    ‖hp.toLp p‖^2 = ∫ u in Ioi (0:ℝ), ‖p u‖^2 := by
  have hi : inner ℂ (hp.toLp p) (hp.toLp p) = ((∫ u in Ioi (0:ℝ), ‖p u‖^2 : ℝ):ℂ) := by
    rw [vec_inner,←integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    simp [mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  rw [←inner_self_eq_norm_sq (𝕜 := ℂ),hi]
  rfl

private theorem conj_wave (z : HP) (u : ℝ) :
    conj (wave z u)=Complex.exp ((1/2-z.val)*(u:ℂ)) := by
  simp only [wave,←Complex.exp_conj,map_mul,map_sub,map_div₀,map_one,Complex.conj_ofNat,Complex.conj_conj,Complex.conj_ofReal]

private theorem ker_gram (z w : HP) : inner ℂ (kernel z) (kernel w) =
    (1:ℂ)*conj (1:ℂ)/gd z w := by
  rw [kernel,kernel,vec_inner]
  have he (u : ℝ) : conj (wave z u)*wave w u=Complex.exp (-gd z w*(u:ℂ)) := by
    rw [conj_wave,wave,←Complex.exp_add];congr 1;unfold gd;ring
  simp only [he]
  rw [integral_exp_mul_complex_Ioi (by simpa using gd_re z w)]
  simp

private theorem step_pos_integral {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : ℝ→G) (h : ∀ u < 0, g u=0) : (∫ u in Ioi (0:ℝ),g u)=∫ u,g u := by
  rw [←integral_Ici_eq_integral_Ioi]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => h u (lt_of_not_ge hu)

private theorem half_int {s : ℂ} (hs : s≠0) (n : ℕ) :
    (∫ u in tile n, Complex.exp (-s*(u:ℂ))) = jump s n/s := by
  rw [tile,integral_Ico_eq_integral_Ioc,←intervalIntegral.integral_of_le (edge_mono (Nat.le_succ n)),
    integral_exp_mul_complex (neg_ne_zero.mpr hs),wexp_end,wexp_end]
  unfold jump pval
  ring

private theorem step_eval (a : ℕ → ℂ) (B : ℝ) (hb : ∀ n, ‖a n‖ ≤ B) (z : HP) :
    inner ℂ (kernel z) (((step_L2 a B hb).restrict (Ioi 0)).toLp (step a)) =
      (∑' n, a n * jump z.val n)/z.val := by
  have hz : z.val≠0 := by intro h; have hh:=z.property; simp [h] at hh; norm_num at hh
  let f (u : ℝ) := Complex.exp ((1/2-z.val)*(u:ℂ))*step a u
  have hf : Integrable f := by
    have hm : Measurable f := (by fun_prop : Measurable (fun u : ℝ => Complex.exp ((1/2-z.val)*(u:ℂ)))).mul (step_meas a)
    apply (step_int a B hb).mono hm.aestronglyMeasurable
    filter_upwards with u
    by_cases hu : 0 ≤ u
    · dsimp only [f]
      rw [norm_mul]
      apply mul_le_of_le_one_left (norm_nonneg _) (by
        rw [Complex.norm_exp,Real.exp_le_one_iff,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
        apply mul_nonpos_of_nonpos_of_nonneg _ hu
        norm_num
        linarith [z.property])
    · simp [f,step,hu]
  have hsupp (u : ℝ) (hu : u<0) : f u=0 := by simp [f,step,not_le_of_gt hu]
  have hs := tile_int f hf hsupp
  have ht (n : ℕ) : (∫ u in tile n, f u)=a n*jump z.val n/z.val := by
    rw [mul_div_assoc,←half_int hz,←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ico
    intro u hu
    change Complex.exp ((1/2-z.val)*(u:ℂ))*step a u=a n*Complex.exp (-z.val*(u:ℂ))
    rw [on_tile a n hu,Complex.ofReal_exp,←mul_assoc,←Complex.exp_add,mul_comm (a n)]
    congr 2; push_cast;ring
  rw [kernel,vec_inner]
  simp only [conj_wave]
  change (∫ u in Ioi (0:ℝ),f u)=_
  rw [step_pos_integral f hsupp,←hs.tsum_eq,←tsum_div_const]
  exact tsum_congr ht
private def errSeq (c : ℕ →₀ ℚ) (n : ℕ) : ℂ :=
    1-∑ k ∈ c.support,(c k:ℂ)*remainder (k+2) (n+1)
private theorem residual_bdd (c : ℕ →₀ ℚ) (n : ℕ) : ‖errSeq c n‖ ≤ (major c:ℝ) := by
  have he : errSeq c n = (resid c n:ℂ) := by simp [errSeq,resid,qrem,remainder]
  rw [he,Complex.norm_ratCast]
  exact_mod_cast resid_bound c n

private def errvec (c : ℕ →₀ ℚ) : Hil :=
  ((step_L2 _ _ (residual_bdd c)).restrict (Ioi 0)).toLp (step (errSeq c))

private theorem err_cost (c : ℕ →₀ ℚ) (H : ℕ) : ‖errvec c‖^2 ≤ (certificate c H : ℝ) := by
  let a := errSeq c
  have hi := (memLp_two_iff_integrable_sq_norm (step_meas a).aestronglyMeasurable).mp
    (step_L2 a _ (residual_bdd c))
  have hs := tile_int (fun u => ‖step a u‖^2) hi (fun u hu => by simp [step,not_le_of_gt hu])
  simp only [step_energy_tile] at hs
  rw [errvec,vec_norm,step_pos_integral _ (fun u hu => by simp [step,not_le_of_gt hu])]
  apply le_of_tendsto hs.tendsto_sum_nat
  filter_upwards with N
  change ∑ n ∈ Finset.range N, ‖1-∑ k ∈ c.support,(c k:ℂ)*remainder (k+2) (n+1)‖^2 / wt n ≤ _
  simp_rw [embed_resid]
  exact_mod_cast part_le_certificate c N H

private def basePoint : HP := ⟨1,by norm_num⟩

private theorem base_factor (z : HP) : ‖bf z basePoint‖ = ‖1-1/z.val‖ := by
  have hz : z.val≠0 := by intro h; have hh:=z.property; simp [h] at hh; norm_num at hh
  have hd : gd basePoint z = conj z.val := by unfold gd basePoint; simp
  simp only [bf,hd,norm_div,Complex.norm_conj]
  change ‖1-z.val‖/‖z.val‖=_
  rw [norm_sub_rev]
  rw [show (1:ℂ)-1/z.val = (z.val-1)/z.val by field_simp,norm_div]

theorem solution (S : Finset {z : ℂ // (1/2:ℝ)<z.re})
    (hS : ∀ z ∈ S, z.val≠1 ∧ riemannZeta z.val=0) (c : ℕ →₀ ℚ) (H : ℕ) :
    1 - ∏ z ∈ S, ‖1-1/z.val‖^2 ≤
      (((∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
      (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) : ℚ) : ℝ) := by
  classical
  have hx (z : HP) (hz : z ∈ S) : inner ℂ (kernel z) (errvec c)=inner ℂ (kernel z) (kernel basePoint) := by
    rw [errvec,step_eval _ _ (residual_bdd c) z,ker_gram]
    have hh := residual_hasSum z.property (hS z hz).1 (hS z hz).2 c.support (fun k => (c k:ℂ))
    rw [show (∑' n,errSeq c n*jump z.val n)=1 from hh.tsum_eq]
    simp [gd,basePoint]
  have h := gram_bound S basePoint kernel (fun _=>1) (errvec c) ker_gram (by simp) hx
  have ho := norm_of_gram kernel (fun _=>1) ker_gram basePoint
  have hr : (‖(1:ℂ)‖^2/(2*basePoint.val.re-1):ℝ)=1 := by norm_num [basePoint]
  rw [hr] at ho
  rw [ho] at h
  simp only [base_factor] at h
  rw [hr,one_mul] at h
  have hc := err_cost c H
  have res : 1 - ∏ z ∈ S, ‖1-1/z.val‖^2 ≤ (certificate c H:ℝ) := by linarith
  simpa only [certificate,part,resid,qrem,qweight,major,mul_div_assoc] using res
