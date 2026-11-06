-- Prove2me | solution 2 for LostSalesExpGap.ConstOrder.best_constant_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T08:06:59.727327+00:00
-- url     : https://prove2.me/submissions/52fc25f6-b39d-4427-9dc3-17ae88a0edd2

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder
import Theorems.Thm_LostSalesExpGap_ConstOrder_kingman_series

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LSExpGapEq3

open CappedBaseStock LostSalesExpGap.ConstOrder Filter Topology

/-- Pipeline contents under the constant order `ρ`. -/
lemma run_slot (c : Parameters) (ρ : ℝ≥0) (ω : Sample) (t : ℕ) (i : Fin c.L) :
    (run c (constOrderPolicy ρ) ω t).2 i = if c.L ≤ t + i then ρ else 0 := by
  induction t generalizing i with
  | zero =>
    simp only [run, initialState, zero_add]
    rw [if_neg (by have := i.2; omega)]
  | succ t ih =>
    simp only [run, step]
    split_ifs with h1 h2 h2
    · rw [ih]; rw [if_pos (by simp only [Fin.val_mk]; omega)]
    · rw [ih]; rw [if_neg (by simp only [Fin.val_mk]; omega)]
    · simp [order, constOrderPolicy]
    · exfalso; have := i.2; omega

lemma arrival_run (c : Parameters) (ρ : ℝ≥0) (ω : Sample) (t : ℕ) :
    arrival c (run c (constOrderPolicy ρ) ω t) = if c.L ≤ t then ρ else 0 := by
  unfold arrival
  rw [run_slot]
  simp

lemma inv_run_le (c : Parameters) (ρ : ℝ≥0) (ω : Sample) (t : ℕ) (ht : t ≤ c.L) :
    (run c (constOrderPolicy ρ) ω t).1 = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show (step c (run c _ ω t) (order (constOrderPolicy ρ) t ω) (ω.1 t)).1 = 0
    simp only [step]
    rw [ih (by omega), arrival_run, if_neg (by omega)]
    simp

/-- Forward recursion for the running maximum of partial sums. -/
lemma finiteInventory_succ (d : DemandPath) (r : ℝ) (k : ℕ) :
    finiteInventory d r (k + 1) =
      max 0 ((r - d 0) + finiteInventory (fun i => d (i + 1)) r k) := by
  unfold finiteInventory
  apply le_antisymm
  · apply Finset.sup'_le
    intro j hj
    rcases j with _ | j
    · simp
    · rw [Finset.sum_range_succ']
      refine le_trans ?_ (le_max_right _ _)
      rw [add_comm]
      have := Finset.le_sup' (fun j => ∑ i ∈ Finset.range j, (r - (d (i + 1) : ℝ)))
        (Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega) : j ∈ Finset.range (k + 1))
      linarith
  · apply max_le
    · exact le_trans (by simp) (Finset.le_sup' (fun k => ∑ i ∈ Finset.range k, (r - (d i : ℝ)))
        (Finset.mem_range.mpr (Nat.succ_pos _)))
    · have : (Finset.range (k + 1)).sup' (by simp)
          (fun j => ∑ i ∈ Finset.range j, (r - (d (i + 1) : ℝ))) ≤
          (Finset.range (k + 1 + 1)).sup' (by simp)
            (fun k => ∑ i ∈ Finset.range k, (r - (d i : ℝ))) - (r - d 0) := by
        apply Finset.sup'_le
        intro j hj
        have := Finset.le_sup' (fun k => ∑ i ∈ Finset.range k, (r - (d i : ℝ)))
          (Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega : j + 1 < k + 1 + 1))
        rw [Finset.sum_range_succ'] at this
        linarith
      linarith

/-- Lindley: the inventory `k` periods after the first arrival. -/
lemma inv_run_Lk (c : Parameters) (r : ℝ) (hr : 0 ≤ r) (ω : Sample) (k : ℕ) :
    ((run c (constOrderPolicy r.toNNReal) ω (c.L + k)).1 : ℝ) =
      finiteInventory (fun i => ω.1 (c.L + k - 1 - i)) r k := by
  induction k with
  | zero =>
    rw [add_zero, inv_run_le c _ ω c.L le_rfl]
    simp [finiteInventory]
  | succ k ih =>
    rw [finiteInventory_succ]
    have e1 : (fun i => (fun i => ω.1 (c.L + (k + 1) - 1 - i)) (i + 1)) =
        (fun i => ω.1 (c.L + k - 1 - i)) := by
      funext i
      show ω.1 _ = ω.1 _
      rw [show c.L + (k + 1) - 1 - (i + 1) = c.L + k - 1 - i by omega]
    rw [e1, show c.L + (k + 1) - 1 - 0 = c.L + k by omega, ← ih, ← add_assoc]
    show ((step c (run c _ ω (c.L + k)) (order (constOrderPolicy r.toNNReal) (c.L + k) ω)
      (ω.1 (c.L + k))).1 : ℝ) = _
    simp only [step]
    rw [arrival_run, if_pos (by omega), NNReal.coe_sub_def]
    push_cast
    rw [Real.coe_toNNReal _ hr, max_comm]
    congr 1; ring

/-- The reversal permutation of the first `n` coordinates. -/
def revFun (n : ℕ) (k : ℕ) : ℕ := if k < n then n - 1 - k else k

lemma revFun_invol (n : ℕ) : Function.Involutive (revFun n) := by
  intro k
  unfold revFun
  by_cases hk : k < n
  · have : n - 1 - k < n := by omega
    simp only [hk, if_true, this]
    omega
  · simp [hk]

def revPerm (n : ℕ) : Equiv.Perm ℕ := (revFun_invol n).toPerm

lemma map_rev (P : DemandLaw) (n : ℕ) :
    (demandPathLaw P).map (fun d : DemandPath => fun k => d (revPerm n k)) = demandPathLaw P := by
  have h := Measure.infinitePi_map_piCongrLeft (X := fun _ : ℕ => ℝ≥0)
    (μ := fun _ : ℕ => P.law) (revPerm n)
  have hfun : (⇑(MeasurableEquiv.piCongrLeft (fun _ : ℕ => ℝ≥0) (revPerm n))) =
      (fun d : DemandPath => fun k => d (revPerm n k)) := by
    funext d k
    simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, cast_eq]
    rfl
  rw [hfun] at h
  simpa [demandPathLaw] using h

lemma finiteInventory_congr (d d' : DemandPath) (r : ℝ) (k : ℕ) (h : ∀ i < k, d i = d' i) :
    finiteInventory d r k = finiteInventory d' r k := by
  unfold finiteInventory
  refine Finset.sup'_congr _ rfl (fun j hj => Finset.sum_congr rfl fun i hi => ?_)
  rw [h i (by have := Finset.mem_range.mp hj; have := Finset.mem_range.mp hi; omega)]

lemma measurable_finiteInventory (x : ℝ) (m : ℕ) :
    Measurable (fun d : DemandPath => finiteInventory d x m) := by
  unfold finiteInventory
  apply Finset.measurable_range_sup''
  intro k _
  fun_prop

lemma finiteInventory_nonneg (d : DemandPath) (x : ℝ) (m : ℕ) : 0 ≤ finiteInventory d x m := by
  unfold finiteInventory
  exact le_trans (by simp) (Finset.le_sup' (fun k => ∑ i ∈ Finset.range k, (x - (d i : ℝ)))
    (Finset.mem_range.mpr (Nat.succ_pos m)))

lemma finiteInventory_le (d : DemandPath) (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    finiteInventory d x m ≤ m * x := by
  unfold finiteInventory
  apply Finset.sup'_le
  intro k hk
  have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  calc ∑ i ∈ Finset.range k, (x - (d i : ℝ)) ≤ ∑ i ∈ Finset.range k, x :=
        Finset.sum_le_sum fun i _ => by have := NNReal.coe_nonneg (d i); linarith
    _ = k * x := by simp
    _ ≤ m * x := mul_le_mul_of_nonneg_right (by exact_mod_cast hk') hx

lemma integrable_finiteInventory (μ : Measure DemandPath) [IsFiniteMeasure μ] (x : ℝ) (hx : 0 ≤ x)
    (m : ℕ) (f : DemandPath → DemandPath) (hf : Measurable f) :
    Integrable (fun d => finiteInventory (f d) x m) μ := by
  refine Integrable.of_bound (C := m * x)
    ((measurable_finiteInventory x m).comp hf).aestronglyMeasurable (ae_of_all _ fun d => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (finiteInventory_nonneg _ x m)]
  exact finiteInventory_le _ x hx m

/-- `J_k`: the inventory `k` periods after the first arrival, as a function of the path. -/
noncomputable def J (L : ℕ) (r : ℝ) (k : ℕ) (d : DemandPath) : ℝ :=
  finiteInventory (fun i => d (L + k - 1 - i)) r k

lemma measurable_J (L : ℕ) (r : ℝ) (k : ℕ) : Measurable (J L r k) := by
  unfold J
  exact (measurable_finiteInventory r k).comp
    (measurable_pi_lambda _ fun i => measurable_pi_apply _)

lemma integral_J (P : DemandLaw) (L : ℕ) (r : ℝ) (hr : 0 ≤ r) (k : ℕ) :
    ∫ d, J L r k d ∂demandPathLaw P = EIL P r k := by
  have hJ : ∀ d : DemandPath,
      J L r k d = finiteInventory (fun i => d (revPerm (L + k) i)) r k := by
    intro d
    unfold J
    apply finiteInventory_congr
    intro i hi
    show d (L + k - 1 - i) = d (revFun (L + k) i)
    unfold revFun; rw [if_pos (by omega)]
  have hφ : Measurable (fun d : DemandPath => fun k' => d (revPerm (L + k) k')) :=
    measurable_pi_lambda _ fun k' => measurable_pi_apply _
  simp_rw [hJ]
  unfold EIL
  conv_rhs => rw [← map_rev P (L + k)]
  rw [integral_map hφ.aemeasurable (measurable_finiteInventory r k).aestronglyMeasurable]

lemma walk_eq (r : ℝ≥0) (d : DemandPath) (k : ℕ) :
    LostSalesConstantOrder.LargeLeadTime.walk r d k = ∑ i ∈ Finset.range k, ((r : ℝ) - d i) := by
  unfold LostSalesConstantOrder.LargeLeadTime.walk
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]
    push_cast
    linarith

lemma supWalk_eq (r : ℝ) (hr : 0 ≤ r) (d : DemandPath) :
    LostSalesConstantOrder.LargeLeadTime.supWalk r.toNNReal d =
      ⨆ m : ℕ, ENNReal.ofReal (finiteInventory d r m) := by
  unfold LostSalesConstantOrder.LargeLeadTime.supWalk
  apply le_antisymm
  · refine iSup_le fun k => le_iSup_of_le k (ENNReal.ofReal_le_ofReal ?_)
    rw [walk_eq, Real.coe_toNNReal _ hr]
    unfold finiteInventory
    exact Finset.le_sup' (fun k => ∑ i ∈ Finset.range k, (r - (d i : ℝ)))
      (Finset.mem_range.mpr (Nat.lt_succ_self k))
  · refine iSup_le fun m => ?_
    obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup' (Finset.nonempty_range_add_one (n := m))
      (fun k => ∑ i ∈ Finset.range k, (r - (d i : ℝ)))
    refine le_iSup_of_le k (le_of_eq ?_)
    unfold finiteInventory
    rw [hkeq, walk_eq, Real.coe_toNNReal _ hr]

lemma EIinf_eq_iSup (P : DemandLaw) (r : ℝ) (hr : 0 ≤ r) :
    EIinf P r = ⨆ m : ℕ, ENNReal.ofReal (EIL P r m) := by
  unfold EIinf
  simp_rw [supWalk_eq r hr]
  rw [lintegral_iSup (f := fun m d => ENNReal.ofReal (finiteInventory d r m))
    (fun m => ENNReal.measurable_ofReal.comp (measurable_finiteInventory r m))]
  · congr 1; funext m
    unfold EIL
    have hint : Integrable (fun d => finiteInventory d r m) (demandPathLaw P) :=
      integrable_finiteInventory (demandPathLaw P) r hr m id measurable_id
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun d => finiteInventory_nonneg d r m)]
  · intro m n hmn d
    apply ENNReal.ofReal_le_ofReal
    unfold finiteInventory
    exact Finset.sup'_mono _ (Finset.range_mono (by omega)) _

lemma EIL_mono (P : DemandLaw) (r : ℝ) (hr : 0 ≤ r) {m n : ℕ} (hmn : m ≤ n) :
    EIL P r m ≤ EIL P r n := by
  unfold EIL
  apply integral_mono (integrable_finiteInventory _ r hr m id measurable_id)
    (integrable_finiteInventory _ r hr n id measurable_id)
  intro d
  unfold finiteInventory
  exact Finset.sup'_mono _ (Finset.range_mono (by omega)) _

lemma J_succ (L : ℕ) (r : ℝ) (k : ℕ) (d : DemandPath) :
    J L r (k + 1) d = max 0 ((r - d (L + k)) + J L r k d) := by
  unfold J
  rw [finiteInventory_succ]
  have e1 : (fun i => (fun i => d (L + (k + 1) - 1 - i)) (i + 1)) =
      (fun i => d (L + k - 1 - i)) := by
    funext i
    show d _ = d _
    rw [show L + (k + 1) - 1 - (i + 1) = L + k - 1 - i by omega]
  rw [e1, show L + (k + 1) - 1 - 0 = L + k by omega]

lemma J_zero (L : ℕ) (r : ℝ) (d : DemandPath) : J L r 0 d = 0 := by
  simp [J, finiteInventory]

lemma J_nonneg (L : ℕ) (r : ℝ) (k : ℕ) (d : DemandPath) : 0 ≤ J L r k d :=
  finiteInventory_nonneg _ r k

lemma inv_run_J (c : Parameters) (r : ℝ) (hr : 0 ≤ r) (ω : Sample) (k : ℕ) :
    ((run c (constOrderPolicy r.toNNReal) ω (c.L + k)).1 : ℝ) = J c.L r k ω.1 :=
  inv_run_Lk c r hr ω k

lemma coe_eq_ofReal (a : ℝ≥0) : (a : ℝ≥0∞) = ENNReal.ofReal (a : ℝ) :=
  (ENNReal.ofReal_coe_nnreal).symm

lemma cost_lt (c : Parameters) (r : ℝ) (ω : Sample) (t : ℕ) (ht : t < c.L) :
    periodCost c (run c (constOrderPolicy r.toNNReal) ω t) (ω.1 t) =
      ENNReal.ofReal (c.p * (ω.1 t : ℝ)) := by
  unfold periodCost lostSales
  rw [inv_run_le c _ ω t ht.le, arrival_run, if_neg (by omega)]
  simp only [add_zero, zero_tsub, ENNReal.coe_zero, mul_zero, zero_add, tsub_zero]
  rw [coe_eq_ofReal, ← ENNReal.ofReal_mul c.penalty_pos.le]

lemma cost_ge (c : Parameters) (r : ℝ) (hr : 0 ≤ r) (ω : Sample) (k : ℕ) :
    periodCost c (run c (constOrderPolicy r.toNNReal) ω (c.L + k)) (ω.1 (c.L + k)) =
      ENNReal.ofReal (c.h * J c.L r (k + 1) ω.1 +
        c.p * (J c.L r (k + 1) ω.1 - J c.L r k ω.1 - r + ω.1 (c.L + k))) := by
  have hh := c.holding_pos; have hp := c.penalty_pos
  unfold periodCost lostSales
  rw [arrival_run, if_pos (by omega)]
  set s := run c (constOrderPolicy r.toNNReal) ω (c.L + k)
  set d := ω.1 (c.L + k)
  have hs : (s.1 : ℝ) = J c.L r k ω.1 := inv_run_J c r hr ω k
  have hJ := J_succ c.L r k ω.1
  have hA : ((s.1 + r.toNNReal - d : ℝ≥0) : ℝ) = J c.L r (k + 1) ω.1 := by
    rw [NNReal.coe_sub_def, hJ]
    push_cast
    rw [Real.coe_toNNReal _ hr, hs, max_comm]
    congr 1; ring
  have hB : ((d - (s.1 + r.toNNReal) : ℝ≥0) : ℝ) =
      J c.L r (k + 1) ω.1 - J c.L r k ω.1 - r + d := by
    rw [NNReal.coe_sub_def, hJ]
    push_cast
    rw [Real.coe_toNNReal _ hr, hs]
    rcases le_total 0 ((r - d) + J c.L r k ω.1) with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]; ring
    · rw [max_eq_left h, max_eq_left (by linarith)]; ring
  rw [coe_eq_ofReal, coe_eq_ofReal, hA, hB, ← ENNReal.ofReal_mul hh.le,
    ← ENNReal.ofReal_mul hp.le, ← ENNReal.ofReal_add (mul_nonneg hh.le (J_nonneg _ _ _ _))]
  have : 0 ≤ J c.L r (k + 1) ω.1 - J c.L r k ω.1 - r + d := by
    rw [hJ]; have := le_max_right 0 ((r - d) + J c.L r k ω.1); linarith
  exact mul_nonneg hp.le this

lemma lintegral_sample (P : DemandLaw) (f : DemandPath → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ ω, f ω.1 ∂sampleLaw P = ∫⁻ x, f x ∂demandPathLaw P := by
  rw [sampleLaw, lintegral_prod (fun z : DemandPath × ℝ => f z.1)
    (hf.comp measurable_fst).aemeasurable]
  simp

lemma integrable_coord (P : DemandLaw) (i : ℕ) :
    Integrable (fun d : DemandPath => (d i : ℝ)) (demandPathLaw P) := by
  have hmap : (demandPathLaw P).map (fun d : DemandPath => d i) = P.law := by
    rw [demandPathLaw]; exact Measure.infinitePi_map_eval _ i
  have := P.finiteMean
  rw [← hmap] at this
  exact this.comp_measurable (measurable_pi_apply i)

lemma integral_coord (P : DemandLaw) (i : ℕ) :
    ∫ d : DemandPath, (d i : ℝ) ∂demandPathLaw P = mean P := by
  have hmap : (demandPathLaw P).map (fun d : DemandPath => d i) = P.law := by
    rw [demandPathLaw]; exact Measure.infinitePi_map_eval _ i
  unfold mean
  rw [← hmap, integral_map (measurable_pi_apply i).aemeasurable
    (Measurable.aestronglyMeasurable (by fun_prop))]

lemma EC_lt (P : DemandLaw) (c : Parameters) (r : ℝ) (t : ℕ) (ht : t < c.L) :
    ∫⁻ ω, periodCost c (run c (constOrderPolicy r.toNNReal) ω t) (ω.1 t) ∂sampleLaw P =
      ENNReal.ofReal (c.p * mean P) := by
  simp_rw [cost_lt c r _ t ht]
  rw [lintegral_sample P (fun x => ENNReal.ofReal (c.p * (x t : ℝ))) (by fun_prop)]
  rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_coord P t).const_mul c.p)
    (ae_of_all _ fun x => mul_nonneg c.penalty_pos.le (NNReal.coe_nonneg _)),
    integral_const_mul, integral_coord]

lemma EC_ge (P : DemandLaw) (c : Parameters) (r : ℝ) (hr : 0 ≤ r) (k : ℕ) :
    ∫⁻ ω, periodCost c (run c (constOrderPolicy r.toNNReal) ω (c.L + k)) (ω.1 (c.L + k))
        ∂sampleLaw P =
      ENNReal.ofReal (c.h * EIL P r (k + 1) +
        c.p * (EIL P r (k + 1) - EIL P r k - r + mean P)) := by
  have hh := c.holding_pos; have hp := c.penalty_pos
  simp_rw [cost_ge c r hr _ k]
  set G : DemandPath → ℝ := fun x => c.h * J c.L r (k + 1) x +
    c.p * (J c.L r (k + 1) x - J c.L r k x - r + x (c.L + k)) with hG
  have hGm : Measurable G := by
    simp only [hG]
    have := measurable_J c.L r (k + 1); have := measurable_J c.L r k
    fun_prop
  rw [lintegral_sample P (fun x => ENNReal.ofReal (G x)) (ENNReal.measurable_ofReal.comp hGm)]
  have hJi : ∀ m, Integrable (J c.L r m) (demandPathLaw P) := fun m =>
    integrable_finiteInventory _ r hr m _ (measurable_pi_lambda _ fun i => measurable_pi_apply _)
  have hGi : Integrable G (demandPathLaw P) :=
    ((hJi (k + 1)).const_mul _).add
      (((((hJi (k + 1)).sub (hJi k)).sub (integrable_const r)).add
        (integrable_coord P (c.L + k))).const_mul _)
  have hG0 : ∀ x, 0 ≤ G x := by
    intro x
    simp only [hG]
    have hJ := J_succ c.L r k x
    have : 0 ≤ J c.L r (k + 1) x - J c.L r k x - r + x (c.L + k) := by
      rw [hJ]; have := le_max_right 0 ((r - x (c.L + k)) + J c.L r k x); linarith
    have := J_nonneg c.L r (k + 1) x
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hGi (ae_of_all _ hG0)]
  congr 1
  simp only [hG]
  have i1 : Integrable (fun x => J c.L r (k + 1) x - J c.L r k x) (demandPathLaw P) :=
    (hJi (k + 1)).sub (hJi k)
  have i2 : Integrable (fun x => J c.L r (k + 1) x - J c.L r k x - r) (demandPathLaw P) :=
    i1.sub (integrable_const r)
  have i3 : Integrable (fun x : DemandPath => J c.L r (k + 1) x - J c.L r k x - r +
      (x (c.L + k) : ℝ)) (demandPathLaw P) := i2.add (integrable_coord P (c.L + k))
  rw [integral_add (f := fun x => c.h * J c.L r (k + 1) x)
    (g := fun x => c.p * (J c.L r (k + 1) x - J c.L r k x - r + x (c.L + k)))
    ((hJi (k + 1)).const_mul _) (i3.const_mul _), integral_const_mul, integral_const_mul,
    integral_add (f := fun x => J c.L r (k + 1) x - J c.L r k x - r)
      (g := fun x : DemandPath => (x (c.L + k) : ℝ)) i2 (integrable_coord P _),
    integral_sub (f := fun x => J c.L r (k + 1) x - J c.L r k x) (g := fun _ => r) i1
      (integrable_const r),
    integral_sub (f := fun x => J c.L r (k + 1) x) (g := fun x => J c.L r k x) (hJi (k + 1))
      (hJi k), integral_J P c.L r hr, integral_J P c.L r hr, integral_coord]
  simp

end LSExpGapEq3

namespace LSExpGapEq3
open CappedBaseStock LostSalesExpGap.ConstOrder Filter Topology

lemma incr_nonneg (P : DemandLaw) (L : ℕ) (r : ℝ) (hr : 0 ≤ r) (k : ℕ) :
    0 ≤ EIL P r (k + 1) - EIL P r k - r + mean P := by
  have hJi : ∀ m, Integrable (J L r m) (demandPathLaw P) := fun m =>
    integrable_finiteInventory _ r hr m _ (measurable_pi_lambda _ fun i => measurable_pi_apply _)
  have i1 : Integrable (fun x => J L r (k + 1) x - J L r k x) (demandPathLaw P) :=
    (hJi (k + 1)).sub (hJi k)
  have i2 : Integrable (fun x => J L r (k + 1) x - J L r k x - r) (demandPathLaw P) :=
    i1.sub (integrable_const r)
  have h0 : 0 ≤ ∫ x, (J L r (k + 1) x - J L r k x - r + (x (L + k) : ℝ)) ∂demandPathLaw P := by
    apply integral_nonneg
    intro x
    have hJ := J_succ L r k x
    simp only [Pi.zero_apply]
    rw [hJ]; have := le_max_right 0 ((r - x (L + k)) + J L r k x); linarith
  rw [integral_add (f := fun x => J L r (k + 1) x - J L r k x - r)
      (g := fun x : DemandPath => (x (L + k) : ℝ)) i2 (integrable_coord P _),
    integral_sub (f := fun x => J L r (k + 1) x - J L r k x) (g := fun _ => r) i1
      (integrable_const r),
    integral_sub (f := fun x => J L r (k + 1) x) (g := fun x => J L r k x) (hJi (k + 1))
      (hJi k), integral_J P L r hr, integral_J P L r hr, integral_coord] at h0
  simpa using h0

end LSExpGapEq3

open LostSalesExpGap.ConstOrder LSExpGapEq3 CappedBaseStock Filter Topology in
lemma LSExpGapEq3.eq3_gen (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters) (r : ℝ)
    (hr₀ : 0 ≤ r) (hr : r ≤ CappedBaseStock.mean P) :
    constCost P c r =
      ENNReal.ofReal c.h * EIinf P r + ENNReal.ofReal (c.p * (CappedBaseStock.mean P - r)) := by
  have hh := c.holding_pos
  have hp := c.penalty_pos
  set m := mean P with hm
  have hmpos : 0 < m := P.positiveMean
  set e : ℕ → ℝ := fun k => EIL P r k with he
  have he0 : e 0 = 0 := by
    simp only [he, EIL, finiteInventory]; simp
  have heN : ∀ k, 0 ≤ e k := fun k =>
    integral_nonneg fun d => finiteInventory_nonneg d r k
  have hemono : ∀ {a b : ℕ}, a ≤ b → e a ≤ e b := fun hab => EIL_mono P r hr₀ hab
  -- real expected costs
  let cc : ℕ → ℝ := fun t => if t < c.L then c.p * m else
    c.h * e (t - c.L + 1) + c.p * (e (t - c.L + 1) - e (t - c.L) - r + m)
  have hcc0 : ∀ t, 0 ≤ cc t := by
    intro t
    simp only [cc]
    split_ifs
    · positivity
    · have := incr_nonneg P c.L r hr₀ (t - c.L)
      have := heN (t - c.L + 1)
      positivity
  have hEC : ∀ t, ∫⁻ ω, periodCost c (run c (constOrderPolicy r.toNNReal) ω t) (ω.1 t)
      ∂sampleLaw P = ENNReal.ofReal (cc t) := by
    intro t
    by_cases ht : t < c.L
    · rw [EC_lt P c r t ht]; simp only [cc, if_pos ht]; rfl
    · obtain ⟨k, rfl⟩ : ∃ k, t = c.L + k := ⟨t - c.L, by omega⟩
      rw [EC_ge P c r hr₀ k]
      simp only [cc, if_neg ht, Nat.add_sub_cancel_left]; rfl
  -- closed form of partial sums
  have hS : ∀ n, ∑ t ∈ Finset.range (c.L + n), cc t =
      c.L * (c.p * m) + c.h * ∑ k ∈ Finset.range n, e (k + 1) + c.p * e n +
        n * (c.p * (m - r)) := by
    intro n
    induction n with
    | zero =>
      rw [add_zero, Finset.sum_congr rfl (fun t ht => if_pos (Finset.mem_range.mp ht))]
      simp [he0]
    | succ n ih =>
      rw [← add_assoc, Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp only [cc, if_neg (show ¬ c.L + n < c.L by omega), Nat.add_sub_cancel_left]
      push_cast; ring
  -- the Cesàro averages
  have havg : ∀ T : ℕ, (∑ t ∈ Finset.range (T + 1), ENNReal.ofReal (cc t)) / ((T : ℝ≥0∞) + 1) =
      ENNReal.ofReal ((∑ t ∈ Finset.range (T + 1), cc t) / ((T : ℝ) + 1)) := by
    intro T
    rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ => hcc0 t),
      ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    rw [ENNReal.ofReal_add (by positivity) zero_le_one]; simp
  unfold constCost policyCost averageCost
  simp_rw [hEC, havg]
  have hEI := EIinf_eq_iSup P r hr₀
  apply le_antisymm
  · -- upper bound
    by_cases htop : EIinf P r = ⊤
    · rw [htop, ENNReal.mul_top (by simp [hh]), top_add]; exact le_top
    set E := (EIinf P r).toReal with hE
    have heE : ∀ k, e k ≤ E := by
      intro k
      have h1 : ENNReal.ofReal (e k) ≤ EIinf P r := by rw [hEI]; exact le_iSup_of_le k le_rfl
      have := ENNReal.toReal_mono htop h1
      rwa [ENNReal.toReal_ofReal (heN k)] at this
    have hE0 : 0 ≤ E := ENNReal.toReal_nonneg
    let u : ℕ → ℝ := fun T => (c.L * (c.p * m) + c.p * E) * (1 / ((T : ℝ) + 1)) +
      (c.h * E + c.p * (m - r))
    have hu : Tendsto u atTop (𝓝 (c.h * E + c.p * (m - r))) := by
      have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (c.L * (c.p * m) + c.p * E)).add_const (c.h * E + c.p * (m - r))
      rw [mul_zero, zero_add] at this
      exact this
    have hle : ∀ᶠ T : ℕ in atTop, (∑ t ∈ Finset.range (T + 1), cc t) / ((T : ℝ) + 1) ≤ u T := by
      filter_upwards [eventually_ge_atTop c.L] with T hT
      obtain ⟨n, hn⟩ : ∃ n, T + 1 = c.L + n := ⟨T + 1 - c.L, by omega⟩
      rw [hn, hS n]
      have hT1 : (0 : ℝ) < (T : ℝ) + 1 := by positivity
      have hnT : (n : ℝ) ≤ (T : ℝ) + 1 := by
        have : n ≤ T + 1 := by omega
        exact_mod_cast this
      have hsum : ∑ k ∈ Finset.range n, e (k + 1) ≤ n * E := by
        calc ∑ k ∈ Finset.range n, e (k + 1) ≤ ∑ _k ∈ Finset.range n, E :=
              Finset.sum_le_sum fun k _ => heE (k + 1)
          _ = n * E := by simp
      rw [div_le_iff₀ hT1]
      simp only [u]
      rw [show ((c.L * (c.p * m) + c.p * E) * (1 / ((T : ℝ) + 1)) + (c.h * E + c.p * (m - r))) *
        ((T : ℝ) + 1) = (c.L * (c.p * m) + c.p * E) + (c.h * E + c.p * (m - r)) * ((T : ℝ) + 1)
        by field_simp]
      have h1 : c.h * ∑ k ∈ Finset.range n, e (k + 1) ≤ c.h * E * ((T : ℝ) + 1) := by
        calc c.h * ∑ k ∈ Finset.range n, e (k + 1) ≤ c.h * (n * E) :=
              mul_le_mul_of_nonneg_left hsum hh.le
          _ ≤ c.h * E * ((T : ℝ) + 1) := by
              have := mul_le_mul_of_nonneg_left hnT (mul_nonneg hh.le hE0)
              linarith
      have h2 : c.p * e n ≤ c.p * E := mul_le_mul_of_nonneg_left (heE n) hp.le
      have h3 : (n : ℝ) * (c.p * (m - r)) ≤ c.p * (m - r) * ((T : ℝ) + 1) := by
        have : 0 ≤ c.p * (m - r) := by nlinarith
        nlinarith
      nlinarith
    calc limsup (fun T : ℕ => ENNReal.ofReal ((∑ t ∈ Finset.range (T + 1), cc t) / ((T : ℝ) + 1)))
          atTop ≤ limsup (fun T => ENNReal.ofReal (u T)) atTop :=
          limsup_le_limsup (hle.mono fun T hT => ENNReal.ofReal_le_ofReal hT)
      _ = ENNReal.ofReal (c.h * E + c.p * (m - r)) :=
          ((ENNReal.tendsto_ofReal hu).limsup_eq)
      _ = ENNReal.ofReal c.h * EIinf P r + ENNReal.ofReal (c.p * (m - r)) := by
          rw [ENNReal.ofReal_add (by positivity) (by nlinarith), ENNReal.ofReal_mul hh.le, hE,
            ENNReal.ofReal_toReal htop]
  · -- lower bound
    rw [hEI, ENNReal.mul_iSup, ENNReal.iSup_add]
    refine iSup_le fun K => ?_
    let l : ℕ → ℝ := fun T => c.h * e K * (1 - (c.L + K) * (1 / ((T : ℝ) + 1))) +
      c.p * (m - r) * (1 - c.L * (1 / ((T : ℝ) + 1)))
    have hl : Tendsto l atTop (𝓝 (c.h * e K + c.p * (m - r))) := by
      have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h1 := ((h0.const_mul ((c.L : ℝ) + K)).const_sub 1).const_mul (c.h * e K)
      have h2 := ((h0.const_mul (c.L : ℝ)).const_sub 1).const_mul (c.p * (m - r))
      have h3 := h1.add h2
      simp only [mul_zero, sub_zero, mul_one] at h3
      exact h3
    have hge : ∀ᶠ T : ℕ in atTop, l T ≤ (∑ t ∈ Finset.range (T + 1), cc t) / ((T : ℝ) + 1) := by
      filter_upwards [eventually_ge_atTop (c.L + K)] with T hT
      obtain ⟨n, hn⟩ : ∃ n, T + 1 = c.L + n := ⟨T + 1 - c.L, by omega⟩
      have hKn : K ≤ n := by omega
      rw [hn, hS n]
      have hT1 : (0 : ℝ) < (T : ℝ) + 1 := by positivity
      have hTn : (T : ℝ) + 1 = c.L + n := by exact_mod_cast hn
      have hsum : (n - K : ℝ) * e K ≤ ∑ k ∈ Finset.range n, e (k + 1) := by
        rw [← Finset.sum_range_add_sum_Ico _ hKn]
        have h1 : 0 ≤ ∑ k ∈ Finset.range K, e (k + 1) := Finset.sum_nonneg fun k _ => heN _
        have h2 : ∑ _k ∈ Finset.Ico K n, e K ≤ ∑ k ∈ Finset.Ico K n, e (k + 1) :=
          Finset.sum_le_sum fun k hk => hemono (by have := (Finset.mem_Ico.mp hk).1; omega)
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hKn] at h2
        linarith
      rw [le_div_iff₀ hT1]
      simp only [l]
      rw [show (c.h * e K * (1 - (c.L + K) * (1 / ((T : ℝ) + 1))) +
          c.p * (m - r) * (1 - c.L * (1 / ((T : ℝ) + 1)))) * ((T : ℝ) + 1) =
          c.h * e K * ((T : ℝ) + 1 - (c.L + K)) + c.p * (m - r) * ((T : ℝ) + 1 - c.L) by
        field_simp]
      rw [hTn]
      have h1 : c.h * e K * (c.L + n - (c.L + K)) ≤ c.h * ∑ k ∈ Finset.range n, e (k + 1) := by
        rw [show (c.L : ℝ) + n - (c.L + K) = n - K by ring, mul_assoc, mul_comm (e K)]
        exact mul_le_mul_of_nonneg_left hsum hh.le
      have h2 : 0 ≤ c.L * (c.p * m) := by positivity
      have h3 : 0 ≤ c.p * e n := mul_nonneg hp.le (heN n)
      nlinarith
    calc ENNReal.ofReal c.h * ENNReal.ofReal (e K) + ENNReal.ofReal (c.p * (m - r))
        = ENNReal.ofReal (c.h * e K + c.p * (m - r)) := by
          rw [ENNReal.ofReal_add (mul_nonneg hh.le (heN K)) (by nlinarith),
            ENNReal.ofReal_mul hh.le]
      _ = limsup (fun T => ENNReal.ofReal (l T)) atTop := ((ENNReal.tendsto_ofReal hl).limsup_eq).symm
      _ ≤ _ := limsup_le_limsup (hge.mono fun T hT => ENNReal.ofReal_le_ofReal hT)

namespace LSExpGapBCE

open CappedBaseStock LostSalesExpGap.ConstOrder LSExpGapEq3 Filter Topology

lemma finiteInventory_le_abs (d : DemandPath) (x : ℝ) (m : ℕ) :
    finiteInventory d x m ≤ m * |x| := by
  unfold finiteInventory
  apply Finset.sup'_le
  intro k hk
  have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  calc ∑ i ∈ Finset.range k, (x - (d i : ℝ)) ≤ ∑ i ∈ Finset.range k, |x| :=
        Finset.sum_le_sum fun i _ => by
          have := NNReal.coe_nonneg (d i); have := le_abs_self x; linarith
    _ = k * |x| := by simp
    _ ≤ m * |x| := by
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast hk') (abs_nonneg x)

lemma finiteInventory_lip (d : DemandPath) (x y : ℝ) (m : ℕ) :
    finiteInventory d x m ≤ finiteInventory d y m + m * |x - y| := by
  unfold finiteInventory
  apply Finset.sup'_le
  intro k hk
  have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h1 : ∑ i ∈ Finset.range k, (x - (d i : ℝ)) =
      ∑ i ∈ Finset.range k, (y - (d i : ℝ)) + k * (x - y) := by
    rw [show (k : ℝ) * (x - y) = ∑ _i ∈ Finset.range k, (x - y) by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul], ← Finset.sum_add_distrib]
    congr 1; funext i; ring
  rw [h1]
  have h2 : (k : ℝ) * (x - y) ≤ m * |x - y| := by
    calc (k : ℝ) * (x - y) ≤ k * |x - y| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (Nat.cast_nonneg k)
      _ ≤ m * |x - y| := mul_le_mul_of_nonneg_right (by exact_mod_cast hk') (abs_nonneg _)
  have h3 : ∑ i ∈ Finset.range k, (y - (d i : ℝ)) ≤ (Finset.range (m + 1)).sup' (by simp)
      (fun k => ∑ i ∈ Finset.range k, (y - (d i : ℝ))) :=
    Finset.le_sup' (fun k => ∑ i ∈ Finset.range k, (y - (d i : ℝ))) hk
  linarith

lemma integrable_fI (P : DemandLaw) (x : ℝ) (m : ℕ) :
    Integrable (fun d => finiteInventory d x m) (demandPathLaw P) := by
  refine Integrable.of_bound (C := m * |x|)
    (measurable_finiteInventory x m).aestronglyMeasurable (ae_of_all _ fun d => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (finiteInventory_nonneg d x m)]
  exact finiteInventory_le_abs d x m

lemma EIL_lip (P : DemandLaw) (m : ℕ) (x y : ℝ) :
    EIL P x m ≤ EIL P y m + m * |x - y| := by
  unfold EIL
  have := integral_mono (integrable_fI P x m)
    ((integrable_fI P y m).add (integrable_const ((m : ℝ) * |x - y|)))
    (fun d => finiteInventory_lip d x y m)
  simp only [Pi.add_apply] at this
  rw [integral_add (integrable_fI P y m) (integrable_const _), integral_const] at this
  simpa using this

lemma continuous_EIL (P : DemandLaw) (m : ℕ) : Continuous (fun x => EIL P x m) := by
  apply LipschitzWith.continuous (K := ⟨m, Nat.cast_nonneg m⟩)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, Real.dist_eq]
  show |EIL P x m - EIL P y m| ≤ (m : ℝ) * |x - y|
  rw [abs_le]
  have h1 := EIL_lip P m x y
  have h2 := EIL_lip P m y x
  rw [abs_sub_comm y x] at h2
  constructor <;> linarith

lemma EIL_zero_level (P : DemandLaw) (m : ℕ) : EIL P 0 m = 0 := by
  unfold EIL
  have : ∀ d : DemandPath, finiteInventory d 0 m = 0 := by
    intro d
    apply le_antisymm _ (finiteInventory_nonneg d 0 m)
    unfold finiteInventory
    apply Finset.sup'_le
    intro k _
    exact Finset.sum_nonpos fun i _ => by have := NNReal.coe_nonneg (d i); linarith
  simp [this]

/-- `E[(m - D)^+] > 0` for a non-degenerate law with mean `m`. -/
lemma c0_pos (P : DemandLaw) (hP : LostSalesConstantOrder.LargeLeadTime.NonDeterministic P) :
    0 < ∫ x : ℝ≥0, max (mean P - (x : ℝ)) 0 ∂P.law := by
  set m := mean P
  have hd : Integrable (fun x : ℝ≥0 => (x : ℝ)) P.law := P.finiteMean
  have hint : Integrable (fun x : ℝ≥0 => max (m - (x : ℝ)) 0) P.law :=
    ((integrable_const m).sub hd).pos_part
  rcases (integral_nonneg (f := fun x : ℝ≥0 => max (m - (x : ℝ)) 0) (μ := P.law)
    (fun x => le_max_right _ _)).lt_or_eq with h | h
  · exact h
  exfalso
  have hz := (integral_eq_zero_iff_of_nonneg (f := fun x : ℝ≥0 => max (m - (x : ℝ)) 0)
    (fun x => le_max_right _ _) hint).mp h.symm
  have hge : ∀ᵐ x : ℝ≥0 ∂P.law, m ≤ (x : ℝ) := by
    filter_upwards [hz] with x hx
    simp only [Pi.zero_apply, max_eq_right_iff, tsub_nonpos] at hx
    exact hx
  have hint2 : Integrable (fun x : ℝ≥0 => (x : ℝ) - m) P.law := hd.sub (integrable_const m)
  have h0 : ∫ x : ℝ≥0, ((x : ℝ) - m) ∂P.law = 0 := by
    rw [integral_sub hd (integrable_const m)]; simp [m, mean]
  have hz2 := (integral_eq_zero_iff_of_nonneg_ae (f := fun x : ℝ≥0 => (x : ℝ) - m)
    (by filter_upwards [hge] with x hx; simp only [Pi.zero_apply]; linarith) hint2).mp h0
  have hm0 : 0 ≤ m := P.positiveMean.le
  set a : ℝ≥0 := ⟨m, hm0⟩
  have hae : ∀ᵐ x ∂P.law, x = a := by
    filter_upwards [hz2] with x hx
    simp only [Pi.zero_apply, sub_eq_zero] at hx
    exact NNReal.eq hx
  apply hP a
  ext s hs
  rw [Measure.dirac_apply' a hs]
  have hcongr : (s : Set ℝ≥0) =ᵐ[P.law] {_x | a ∈ s} := by
    filter_upwards [hae] with d hd'
    rw [hd']; rfl
  rw [measure_congr hcongr]
  by_cases has : a ∈ s
  · simp [has]
  · simp [has]

/-- `E[((n+1)m - S_{n+1})^+] ≥ E[(m - D)^+]`, by independence and Jensen. -/
lemma fn_ge_c0 (P : DemandLaw) (n : ℕ) :
    ∫ x : ℝ≥0, max (mean P - (x : ℝ)) 0 ∂P.law ≤
      ∫ d, max (((n : ℝ) + 1) * mean P - ∑ i ∈ Finset.range (n + 1), (d i : ℝ)) 0
        ∂demandPathLaw P := by
  set m := mean P
  set μ := demandPathLaw P with hμ
  let S : Finset ℕ := {0}
  let T : Finset ℕ := Finset.Ico 1 (n + 1)
  let Y : DemandPath → ℝ := fun d => m - d 0
  let Z : DemandPath → ℝ := fun d => ∑ i ∈ T, (m - d i)
  have hYm : Measurable Y := by fun_prop
  have hZm : Measurable Z := by fun_prop
  have hYi : Integrable Y μ := (integrable_const m).sub (integrable_coord P 0)
  have hZi : Integrable Z μ :=
    integrable_finset_sum _ fun i _ => (integrable_const m).sub (integrable_coord P i)
  have hEZ : ∫ d, Z d ∂μ = 0 := by
    simp only [Z]
    rw [integral_finset_sum (f := fun i (d : DemandPath) => m - (d i : ℝ)) _
      fun i _ => (integrable_const m).sub (integrable_coord P i)]
    apply Finset.sum_eq_zero
    intro i _
    rw [integral_sub (integrable_const m) (integrable_coord P i), integral_coord]
    simp [m]
  -- independence of Y and Z
  have hind : IndepFun Y Z μ := by
    have hi := iIndepFun_infinitePi (P := fun _ : ℕ => P.law)
      (X := fun _ (x : ℝ≥0) => x) (fun _ => measurable_id)
    have h2 := hi.indepFun_finset S T (by simp [S, T]) (fun i => measurable_pi_apply i)
    let φ1 : (S → ℝ≥0) → ℝ := fun v => m - v ⟨0, Finset.mem_singleton_self 0⟩
    let φ2 : (T → ℝ≥0) → ℝ := fun v => ∑ i : T, (m - v i)
    have h3 := h2.comp (φ := φ1) (ψ := φ2) (by fun_prop) (by fun_prop)
    have e2 : φ2 ∘ (fun d (i : T) => d i) = Z := by
      funext d
      simp only [Function.comp, φ2, Z]
      exact Finset.sum_coe_sort T (fun i => m - (d i : ℝ))
    rw [e2] at h3
    exact h3
  -- the split `(n+1)m - S_{n+1} = Y + Z`
  have hsplit : ∀ d : DemandPath,
      ((n : ℝ) + 1) * m - ∑ i ∈ Finset.range (n + 1), (d i : ℝ) = Y d + Z d := by
    intro d
    simp only [Y, Z, T]
    rw [Finset.sum_range_eq_add_Ico _ (Nat.succ_pos n), Finset.sum_sub_distrib,
      Finset.sum_const, Nat.card_Ico]
    simp only [nsmul_eq_mul, add_tsub_cancel_right]
    ring
  simp_rw [hsplit]
  -- Jensen on the product
  set νY := μ.map Y
  set νZ := μ.map Z
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hYm.aemeasurable hZm.aemeasurable).mp hind
  have hpair : Measurable (fun d => (Y d, Z d)) := hYm.prodMk hZm
  have hYi' : Integrable (fun y : ℝ => y) νY :=
    (integrable_map_measure aestronglyMeasurable_id hYm.aemeasurable).mpr hYi
  have hZi' : Integrable (fun z : ℝ => z) νZ :=
    (integrable_map_measure aestronglyMeasurable_id hZm.aemeasurable).mpr hZi
  have : IsProbabilityMeasure νY := Measure.isProbabilityMeasure_map hYm.aemeasurable
  have : IsProbabilityMeasure νZ := Measure.isProbabilityMeasure_map hZm.aemeasurable
  have hF : Integrable (fun p : ℝ × ℝ => max (p.1 + p.2) 0) (νY.prod νZ) := by
    refine Integrable.mono' ((hYi'.abs.comp_fst νZ).add (hZi'.abs.comp_snd νY))
      (Measurable.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    simp only [Pi.add_apply]
    exact max_le (by have := le_abs_self p.1; have := le_abs_self p.2; linarith)
      (by positivity)
  have hEZ' : ∫ z, z ∂νZ = 0 := by
    rw [integral_map (f := fun z : ℝ => z) hZm.aemeasurable
      measurable_id'.aestronglyMeasurable]; exact hEZ
  have e1 : ∫ d, max (Y d + Z d) 0 ∂μ = ∫ p, max (p.1 + p.2) 0 ∂(νY.prod νZ) := by
    rw [← hmap, integral_map hpair.aemeasurable (Measurable.aestronglyMeasurable (by fun_prop))]
  have e2 : ∫ x : ℝ≥0, max (m - (x : ℝ)) 0 ∂P.law = ∫ y, max y 0 ∂νY := by
    rw [integral_map hYm.aemeasurable (Measurable.aestronglyMeasurable (by fun_prop))]
    have hmap0 : μ.map (fun d : DemandPath => d 0) = P.law := by
      rw [hμ, demandPathLaw]; exact Measure.infinitePi_map_eval _ 0
    rw [← hmap0, integral_map (measurable_pi_apply 0).aemeasurable
      (Measurable.aestronglyMeasurable (by fun_prop))]
  rw [e1, e2, integral_prod _ hF]
  refine integral_mono hYi'.pos_part hF.integral_prod_left (fun y => ?_)
  have hint : Integrable (fun z : ℝ => max (y + z) 0) νZ :=
    ((integrable_const y).add hZi').pos_part
  apply max_le
  · calc y = ∫ z, (y + z) ∂νZ := by
          rw [integral_add (integrable_const y) hZi', hEZ']; simp
      _ ≤ ∫ z, max (y + z) 0 ∂νZ :=
          integral_mono ((integrable_const y).add hZi') hint (fun z => le_max_left _ _)
  · exact integral_nonneg fun z => le_max_right _ _

end LSExpGapBCE

open LostSalesExpGap.ConstOrder LSExpGapEq3 LSExpGapBCE CappedBaseStock Filter Topology in
theorem solution (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters)
    (hP : LostSalesConstantOrder.LargeLeadTime.NonDeterministic P) :
    (argminConst P c).Nonempty ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ argminConst P c, r ≤ CappedBaseStock.mean P - δ) ∧
      rInf P c ∈ argminConst P c ∧
      rInf P c < CappedBaseStock.mean P := by
  obtain ⟨hK1, -⟩ := kingman_series P
  have hh := c.holding_pos
  have hp := c.penalty_pos
  set m := mean P with hmdef
  have hm : 0 < m := P.positiveMean
  have hEILnn : ∀ r K, 0 ≤ EIL P r K := fun r K =>
    integral_nonneg fun d => finiteInventory_nonneg d r K
  -- the lower semicontinuous representative of `C(π_r)`
  let g : ℝ → ℝ≥0∞ := fun r => ⨆ K : ℕ, ENNReal.ofReal (c.h * EIL P r K + c.p * (m - r))
  have hFg : ∀ r, 0 ≤ r → r ≤ m → constCost P c r = g r := by
    intro r h0 h1
    rw [eq3_gen P c r h0 h1, EIinf_eq_iSup P r h0, ENNReal.mul_iSup, ENNReal.iSup_add]
    congr 1; funext K
    rw [← ENNReal.ofReal_mul hh.le,
      ← ENNReal.ofReal_add (mul_nonneg hh.le (hEILnn r K)) (by nlinarith)]
  have hglsc : LowerSemicontinuous g := by
    apply lowerSemicontinuous_iSup
    intro K
    apply Continuous.lowerSemicontinuous
    exact ENNReal.continuous_ofReal.comp ((continuous_const.mul (continuous_EIL P K)).add
      (continuous_const.mul (continuous_const.sub continuous_id)))
  -- divergence at `r = E[D]`
  set c0 := ∫ x : ℝ≥0, max (m - (x : ℝ)) 0 ∂P.law with hc0def
  have hc0 : 0 < c0 := c0_pos P hP
  obtain ⟨K, hK⟩ : ∃ K : ℕ, c.p * m / c.h + 1 ≤
      ∑ n ∈ Finset.range K, c0 * (1 / ((n : ℝ) + 1)) := by
    have h2 := Filter.Tendsto.const_mul_atTop hc0 Real.tendsto_sum_range_one_div_nat_succ_atTop
    obtain ⟨K, hK⟩ := (h2.eventually_ge_atTop (c.p * m / c.h + 1)).exists
    exact ⟨K, by rw [← Finset.mul_sum]; exact hK⟩
  have hKpos : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h
      simp only [Finset.range_zero, Finset.sum_empty] at hK
      have : 0 ≤ c.p * m / c.h := by positivity
      linarith
    · exact h
  have heKm : c.p * m / c.h + 1 ≤ EIL P m K := by
    rw [hK1 m hm.le le_rfl K hKpos]
    refine hK.trans (Finset.sum_le_sum fun n _ => ?_)
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (fn_ge_c0 P n) (by positivity)
  set δ := min (1 / (2 * (K : ℝ))) (m / 2) with hδdef
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hKpos
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδm : δ < m := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hF0 : constCost P c 0 = ENNReal.ofReal (c.p * m) := by
    rw [hFg 0 le_rfl hm.le]
    simp only [g, EIL_zero_level, mul_zero, zero_add, sub_zero, ciSup_const]
  have hbig : ∀ r, m - δ < r → r ≤ m → constCost P c 0 < constCost P c r := by
    intro r h1 h2
    have hr0 : 0 ≤ r := by linarith
    have hlip := EIL_lip P K m r
    have hmr : |m - r| < 1 / (2 * (K : ℝ)) := by
      rw [abs_of_nonneg (by linarith)]
      have : m - r < δ := by linarith
      exact lt_of_lt_of_le this (min_le_left _ _)
    have hKmr : (K : ℝ) * |m - r| ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_left hmr.le (show (0 : ℝ) ≤ K by positivity)
      rw [show (K : ℝ) * (1 / (2 * K)) = 1 / 2 by field_simp] at this
      exact this
    have heKr : c.p * m / c.h + 1 / 2 ≤ EIL P r K := by linarith
    have h3 : c.h * (c.p * m / c.h + 1 / 2) ≤ c.h * EIL P r K :=
      mul_le_mul_of_nonneg_left heKr hh.le
    rw [mul_add, mul_div_cancel₀ _ hh.ne'] at h3
    have h4 : 0 ≤ c.p * (m - r) := mul_nonneg hp.le (by linarith)
    have h5 : 0 < c.h * (1 / 2) := by positivity
    have h6 : 0 ≤ c.p * m := by positivity
    rw [hF0, hFg r hr0 h2]
    refine lt_of_lt_of_le ?_ (le_iSup (fun K => ENNReal.ofReal (c.h * EIL P r K + c.p * (m - r))) K)
    rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)]
    linarith
  -- existence of a minimiser on `[0, E[D] - δ]`
  obtain ⟨a, ha, hamin⟩ := (hglsc.lowerSemicontinuousOn (Set.Icc 0 (m - δ))).exists_isMinOn
    (Set.nonempty_Icc.mpr (by linarith)) isCompact_Icc
  have haArg : a ∈ argminConst P c := by
    refine ⟨⟨ha.1, by linarith [ha.2]⟩, fun r' hr' => ?_⟩
    rw [hFg a ha.1 (by linarith [ha.2])]
    by_cases hr'δ : r' ≤ m - δ
    · rw [hFg r' hr'.1 hr'.2]; exact hamin ⟨hr'.1, hr'δ⟩
    · push_neg at hr'δ
      have h0 : g a ≤ g 0 := hamin ⟨le_rfl, by linarith⟩
      rw [← hFg 0 le_rfl hm.le] at h0
      exact h0.trans (hbig r' hr'δ hr'.2).le
  have hbound : ∀ r ∈ argminConst P c, r ≤ m - δ := by
    intro r hr
    by_contra hcon
    push_neg at hcon
    have := hr.2 0 ⟨le_rfl, hm.le⟩
    exact absurd this (not_le.mpr (hbig r hcon hr.1.2))
  have hset : argminConst P c = Set.Icc 0 (m - δ) ∩ (g ⁻¹' Set.Iic (g a)) := by
    ext r
    constructor
    · intro hr
      refine ⟨⟨hr.1.1, hbound r hr⟩, ?_⟩
      have := hr.2 a haArg.1
      rw [hFg r hr.1.1 hr.1.2, hFg a haArg.1.1 haArg.1.2] at this
      exact this
    · rintro ⟨hr1, hr2⟩
      refine ⟨⟨hr1.1, by linarith [hr1.2]⟩, fun r' hr' => ?_⟩
      rw [hFg r hr1.1 (by linarith [hr1.2])]
      have := haArg.2 r' hr'
      rw [hFg a haArg.1.1 haArg.1.2] at this
      exact le_trans hr2 this
  have hclosed : IsClosed (argminConst P c) := by
    rw [hset]; exact isClosed_Icc.inter (hglsc.isClosed_preimage (g a))
  have hmem : rInf P c ∈ argminConst P c :=
    hclosed.csInf_mem ⟨a, haArg⟩ ⟨0, fun y hy => hy.1.1⟩
  refine ⟨⟨a, haArg⟩, ⟨δ, hδ, hbound⟩, hmem, ?_⟩
  have := hbound _ hmem
  linarith
