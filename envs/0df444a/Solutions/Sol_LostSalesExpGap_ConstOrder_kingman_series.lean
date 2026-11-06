-- Prove2me | solution 1 for LostSalesExpGap.ConstOrder.kingman_series
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T08:06:59.074978+00:00
-- url     : https://prove2.me/submissions/5834dedc-c7cb-46ef-906d-6fb395a66440

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder

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

namespace LSExpGapKing

open CappedBaseStock LostSalesExpGap.ConstOrder LSExpGapEq3 Filter Topology

lemma map_perm (P : DemandLaw) (σ : Equiv.Perm ℕ) :
    (demandPathLaw P).map (fun d : DemandPath => fun k => d (σ k)) = demandPathLaw P := by
  have h := Measure.infinitePi_map_piCongrLeft (X := fun _ : ℕ => ℝ≥0)
    (μ := fun _ : ℕ => P.law) σ.symm
  have hfun : (⇑(MeasurableEquiv.piCongrLeft (fun _ : ℕ => ℝ≥0) σ.symm)) =
      (fun d : DemandPath => fun k => d (σ k)) := by
    funext d k
    simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, cast_eq,
      Equiv.symm_symm]
  rw [hfun] at h
  simpa [demandPathLaw] using h

lemma integral_perm (P : DemandLaw) (σ : Equiv.Perm ℕ) (F : DemandPath → ℝ) (hF : Measurable F) :
    ∫ d, F (fun k => d (σ k)) ∂demandPathLaw P = ∫ d, F d ∂demandPathLaw P := by
  have hφ : Measurable (fun d : DemandPath => fun k => d (σ k)) :=
    measurable_pi_lambda _ fun k => measurable_pi_apply _
  rw [← integral_map hφ.aemeasurable hF.aestronglyMeasurable, map_perm]

/-- The partial sum `S_{n+1} = (n+1) r - Σ_{i ≤ n} D_i`. -/
noncomputable def Ssum (r : ℝ) (n : ℕ) (d : DemandPath) : ℝ :=
  ((n : ℝ) + 1) * r - ∑ i ∈ Finset.range (n + 1), (d i : ℝ)

lemma Ssum_perm (r : ℝ) (n : ℕ) (σ : Equiv.Perm ℕ) (hσ : {a | σ a ≠ a} ⊆ ↑(Finset.range (n + 1)))
    (d : DemandPath) : Ssum r n (fun k => d (σ k)) = Ssum r n d := by
  unfold Ssum
  congr 1
  exact Equiv.Perm.sum_comp σ (Finset.range (n + 1)) (fun i => (d i : ℝ)) hσ

lemma measurable_Ssum (r : ℝ) (n : ℕ) : Measurable (Ssum r n) := by
  unfold Ssum; fun_prop

lemma integrable_coord' (P : DemandLaw) (i : ℕ) :
    Integrable (fun d : DemandPath => (d i : ℝ)) (demandPathLaw P) := by
  have hmap : (demandPathLaw P).map (fun d : DemandPath => d i) = P.law := by
    rw [demandPathLaw]; exact Measure.infinitePi_map_eval _ i
  have := P.finiteMean
  rw [← hmap] at this
  exact this.comp_measurable (measurable_pi_apply i)

lemma finiteInventory_abs_le (d : DemandPath) (x : ℝ) (m : ℕ) :
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

lemma integrable_M (P : DemandLaw) (x : ℝ) (m : ℕ) (f : DemandPath → DemandPath)
    (hf : Measurable f) : Integrable (fun d => finiteInventory (f d) x m) (demandPathLaw P) := by
  refine Integrable.of_bound (C := m * |x|)
    ((measurable_finiteInventory x m).comp hf).aestronglyMeasurable (ae_of_all _ fun d => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (finiteInventory_nonneg _ x m)]
  exact finiteInventory_abs_le _ x m

lemma finiteInventory_succ_max (d : DemandPath) (r : ℝ) (n : ℕ) :
    finiteInventory d r (n + 1) = max (finiteInventory d r n) (Ssum r n d) := by
  have hS : Ssum r n d = ∑ i ∈ Finset.range (n + 1), (r - (d i : ℝ)) := by
    unfold Ssum; rw [Finset.sum_sub_distrib]; simp
  rw [hS]
  unfold finiteInventory
  apply le_antisymm
  · apply Finset.sup'_le
    intro j hj
    rcases Nat.lt_or_ge j (n + 1) with h | h
    · exact le_trans (Finset.le_sup' (fun k => ∑ i ∈ Finset.range k, (r - (d i : ℝ)))
        (Finset.mem_range.mpr h)) (le_max_left _ _)
    · have : j = n + 1 := by have := Finset.mem_range.mp hj; omega
      subst this; exact le_max_right _ _
  · apply max_le
    · apply Finset.sup'_le
      intro j hj
      exact Finset.le_sup' (fun k => ∑ i ∈ Finset.range k, (r - (d i : ℝ)))
        (Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega))
    · exact Finset.le_sup' (fun k => ∑ i ∈ Finset.range k, (r - (d i : ℝ)))
        (Finset.mem_range.mpr (by omega))

/-- Pointwise decomposition of `M_{n+1}`. -/
lemma M_succ_split (d : DemandPath) (r : ℝ) (n : ℕ) :
    finiteInventory d r (n + 1) =
      {d | 0 < Ssum r n d}.indicator (fun d => r - (d 0 : ℝ)) d +
      {d | 0 < Ssum r n d}.indicator (fun d => finiteInventory (fun i => d (i + 1)) r n) d +
      {d | 0 < Ssum r n d}ᶜ.indicator (fun d => finiteInventory d r n) d := by
  by_cases hS : 0 < Ssum r n d
  · have h1 : d ∈ {d | 0 < Ssum r n d} := hS
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem h1,
      Set.indicator_of_notMem (by simpa using h1), add_zero, finiteInventory_succ]
    have hle : Ssum r n d ≤ (r - d 0) + finiteInventory (fun i => d (i + 1)) r n := by
      have h2 : ∑ i ∈ Finset.range n, (r - (d (i + 1) : ℝ)) ≤
          finiteInventory (fun i => d (i + 1)) r n := by
        unfold finiteInventory
        exact Finset.le_sup' (fun k => ∑ i ∈ Finset.range k, (r - (d (i + 1) : ℝ)))
          (Finset.mem_range.mpr (Nat.lt_succ_self n))
      have h3 : Ssum r n d = (r - d 0) + ∑ i ∈ Finset.range n, (r - (d (i + 1) : ℝ)) := by
        unfold Ssum
        rw [Finset.sum_range_succ', Finset.sum_sub_distrib]
        simp; ring
      linarith
    rw [max_eq_right (by linarith)]
  · have h1 : d ∉ {d | 0 < Ssum r n d} := hS
    rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h1,
      Set.indicator_of_mem (by simpa using h1), zero_add, zero_add, finiteInventory_succ_max]
    push_neg at hS
    exact max_eq_left (le_trans hS (finiteInventory_nonneg d r n))

/-- The cyclic permutation `i ↦ i+1` on `[0, n)`, `n ↦ 0`. -/
def cycFun (n : ℕ) (i : ℕ) : ℕ := if i < n then i + 1 else if i = n then 0 else i
def cycInv (n : ℕ) (i : ℕ) : ℕ := if i = 0 then n else if i ≤ n then i - 1 else i

def cycPerm (n : ℕ) : Equiv.Perm ℕ where
  toFun := cycFun n
  invFun := cycInv n
  left_inv := by
    intro i; unfold cycFun cycInv
    by_cases h1 : i < n
    · simp only [h1, if_true]; rw [if_neg (by omega), if_pos (by omega)]; omega
    · by_cases h2 : i = n
      · subst h2; simp
      · simp only [h1, h2, if_false]; rw [if_neg (by omega), if_neg (by omega)]
  right_inv := by
    intro i; unfold cycFun cycInv
    by_cases h1 : i = 0
    · subst h1; simp
    · by_cases h2 : i ≤ n
      · simp only [h1, h2, if_false, if_true]; rw [if_pos (by omega)]; omega
      · simp only [h1, h2, if_false]; rw [if_neg (by omega), if_neg (by omega)]

lemma cycPerm_support (n : ℕ) : {a | cycPerm n a ≠ a} ⊆ ↑(Finset.range (n + 1)) := by
  intro a ha
  simp only [Set.mem_setOf_eq] at ha
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  apply ha
  show cycFun n a = a
  unfold cycFun; rw [if_neg (by omega), if_neg (by omega)]

lemma swap_support (n i : ℕ) (hi : i < n + 1) :
    {a | Equiv.swap 0 i a ≠ a} ⊆ ↑(Finset.range (n + 1)) := by
  intro a ha
  simp only [Set.mem_setOf_eq] at ha
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  apply ha
  rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]

/-- Spitzer/Kingman increment: `E[M_{n+1}] = E[M_n] + E[S_{n+1}^+]/(n+1)`. -/
lemma EIL_succ (P : DemandLaw) (r : ℝ) (n : ℕ) :
    EIL P r (n + 1) = EIL P r n +
      (1 / ((n : ℝ) + 1)) * ∫ d, max (Ssum r n d) 0 ∂demandPathLaw P := by
  set μ := demandPathLaw P with hμ
  set A : Set DemandPath := {d | 0 < Ssum r n d} with hA
  have hAm : MeasurableSet A := measurableSet_lt measurable_const (measurable_Ssum r n)
  have hshift : Measurable (fun d : DemandPath => fun i => d (i + 1)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have iX : ∀ i, Integrable (fun d : DemandPath => r - (d i : ℝ)) μ :=
    fun i => (integrable_const r).sub (integrable_coord' P i)
  have iM : Integrable (fun d => finiteInventory d r n) μ := integrable_M P r n id measurable_id
  have iMs : Integrable (fun d => finiteInventory (fun i => d (i + 1)) r n) μ :=
    integrable_M P r n _ hshift
  have i1 := (iX 0).indicator hAm
  have i2 := iMs.indicator hAm
  have i3 := iM.indicator hAm.compl
  have hsplit : EIL P r (n + 1) =
      ∫ d, (A.indicator (fun d => r - (d 0 : ℝ)) d +
        A.indicator (fun d => finiteInventory (fun i => d (i + 1)) r n) d +
        Aᶜ.indicator (fun d => finiteInventory d r n) d) ∂μ := by
    unfold EIL
    congr 1; funext d
    exact M_succ_split d r n
  rw [integral_add (f := fun d => A.indicator (fun d => r - (d 0 : ℝ)) d +
        A.indicator (fun d => finiteInventory (fun i => d (i + 1)) r n) d)
      (g := fun d => Aᶜ.indicator (fun d => finiteInventory d r n) d) (i1.add i2) i3,
    integral_add (f := fun d => A.indicator (fun d => r - (d 0 : ℝ)) d)
      (g := fun d => A.indicator (fun d => finiteInventory (fun i => d (i + 1)) r n) d) i1 i2]
    at hsplit
  -- cyclic exchangeability
  have hB : ∫ d, A.indicator (fun d => finiteInventory (fun i => d (i + 1)) r n) d ∂μ =
      ∫ d, A.indicator (fun d => finiteInventory d r n) d ∂μ := by
    have hG : Measurable (fun d => A.indicator (fun d => finiteInventory d r n) d) :=
      (measurable_finiteInventory r n).indicator hAm
    rw [← integral_perm P (cycPerm n) _ hG]
    congr 1; funext d
    have hS : Ssum r n (fun k => d (cycPerm n k)) = Ssum r n d :=
      Ssum_perm r n (cycPerm n) (cycPerm_support n) d
    have hM : finiteInventory (fun k => d (cycPerm n k)) r n =
        finiteInventory (fun i => d (i + 1)) r n := by
      apply finiteInventory_congr
      intro i hi
      show d (cycFun n i) = d (i + 1)
      unfold cycFun; rw [if_pos hi]
    simp only [Set.indicator, hA, Set.mem_setOf_eq, hS, hM]
  -- transposition exchangeability
  have hX : ∀ i < n + 1, ∫ d, A.indicator (fun d => r - (d i : ℝ)) d ∂μ =
      ∫ d, A.indicator (fun d => r - (d 0 : ℝ)) d ∂μ := by
    intro i hi
    have hG : Measurable (fun d => A.indicator (fun d : DemandPath => r - (d 0 : ℝ)) d) :=
      (by fun_prop : Measurable (fun d : DemandPath => r - (d 0 : ℝ))).indicator hAm
    rw [← integral_perm P (Equiv.swap 0 i) _ hG]
    congr 1; funext d
    have hS : Ssum r n (fun k => d (Equiv.swap 0 i k)) = Ssum r n d :=
      Ssum_perm r n (Equiv.swap 0 i) (swap_support n i hi) d
    simp only [Set.indicator, hA, Set.mem_setOf_eq, hS, Equiv.swap_apply_left]
  have hsumX : ∑ i ∈ Finset.range (n + 1), ∫ d, A.indicator (fun d => r - (d i : ℝ)) d ∂μ =
      ∫ d, max (Ssum r n d) 0 ∂μ := by
    rw [← integral_finset_sum _ (fun i _ => (iX i).indicator hAm)]
    congr 1; funext d
    have hS : Ssum r n d = ∑ i ∈ Finset.range (n + 1), (r - (d i : ℝ)) := by
      unfold Ssum; rw [Finset.sum_sub_distrib]; simp
    by_cases h : 0 < Ssum r n d
    · have hd : d ∈ A := h
      simp only [Set.indicator_of_mem hd]
      rw [max_eq_left h.le, hS]
    · have hd : d ∉ A := h
      simp only [Set.indicator_of_notMem hd, Finset.sum_const_zero]
      rw [max_eq_right (not_lt.mp h)]
  have hA0 : ∫ d, A.indicator (fun d => r - (d 0 : ℝ)) d ∂μ =
      (1 / ((n : ℝ) + 1)) * ∫ d, max (Ssum r n d) 0 ∂μ := by
    rw [← hsumX, Finset.sum_congr rfl (fun i hi => hX i (Finset.mem_range.mp hi)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
    push_cast; ring
  have hMsplit : EIL P r n = ∫ d, A.indicator (fun d => finiteInventory d r n) d ∂μ +
      ∫ d, Aᶜ.indicator (fun d => finiteInventory d r n) d ∂μ := by
    unfold EIL
    rw [← integral_add (iM.indicator hAm) i3]
    congr 1; funext d
    exact (Set.indicator_self_add_compl_apply A (fun d => finiteInventory d r n) d).symm
  rw [hsplit, hB, hA0, hMsplit]
  ring

lemma EIL_zero (P : DemandLaw) (r : ℝ) : EIL P r 0 = 0 := by
  simp [EIL, finiteInventory]

lemma kingman_finite (P : DemandLaw) (r : ℝ) (m : ℕ) :
    EIL P r m = ∑ n ∈ Finset.range m, (1 / ((n : ℝ) + 1)) *
      ∫ d, max (((n : ℝ) + 1) * r - ∑ i ∈ Finset.range (n + 1), (d i : ℝ)) 0
        ∂demandPathLaw P := by
  induction m with
  | zero => simp [EIL_zero]
  | succ m ih =>
    rw [EIL_succ, ih, Finset.sum_range_succ]
    rfl

end LSExpGapKing

open LostSalesExpGap.ConstOrder LSExpGapEq3 LSExpGapKing CappedBaseStock in
theorem solution (P : CappedBaseStock.DemandLaw) :
    (∀ r : ℝ, 0 ≤ r → r ≤ CappedBaseStock.mean P → ∀ m : ℕ, 1 ≤ m →
      EIL P r m = ∑ n ∈ Finset.range m, (1 / ((n : ℝ) + 1)) *
        ∫ d, max (((n : ℝ) + 1) * r - ∑ i ∈ Finset.range (n + 1), (d i : ℝ)) 0
          ∂CappedBaseStock.demandPathLaw P) ∧
    (∀ r : ℝ, 0 ≤ r → r < CappedBaseStock.mean P →
      EIinf P r = ∑' n : ℕ, ENNReal.ofReal (1 / ((n : ℝ) + 1)) *
        ∫⁻ d, ENNReal.ofReal (((n : ℝ) + 1) * r - ∑ i ∈ Finset.range (n + 1), (d i : ℝ))
          ∂CappedBaseStock.demandPathLaw P) := by
  refine ⟨fun r _ _ m _ => kingman_finite P r m, fun r hr0 _ => ?_⟩
  rw [EIinf_eq_iSup P r hr0, ENNReal.tsum_eq_iSup_nat]
  congr 1; funext m
  rw [kingman_finite P r m, ENNReal.ofReal_sum_of_nonneg (s := Finset.range m)
    (f := fun n : ℕ => (1 / ((n : ℝ) + 1)) *
      ∫ d, max (((n : ℝ) + 1) * r - ∑ i ∈ Finset.range (n + 1), (d i : ℝ)) 0 ∂demandPathLaw P)
    (fun n _ => mul_nonneg (by positivity) (integral_nonneg fun _ => le_max_right _ _))]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hint : Integrable (fun d : DemandPath =>
      max (((n : ℝ) + 1) * r - ∑ i ∈ Finset.range (n + 1), (d i : ℝ)) 0) (demandPathLaw P) :=
    (((integrable_const _).sub (integrable_finset_sum _ fun i _ => integrable_coord' P i))).pos_part
  rw [ENNReal.ofReal_mul (by positivity), ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun _ => le_max_right _ _)]
  congr 2; funext d
  rcases le_total 0 (((n : ℝ) + 1) * r - ∑ i ∈ Finset.range (n + 1), (d i : ℝ)) with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
