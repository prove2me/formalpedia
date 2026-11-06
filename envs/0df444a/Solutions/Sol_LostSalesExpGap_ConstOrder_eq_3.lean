-- Prove2me | solution 1 for LostSalesExpGap.ConstOrder.eq_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T07:47:19.631951+00:00
-- url     : https://prove2.me/submissions/f8ad21bb-ba01-435c-83a5-1a28f101fec9

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
theorem solution (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters) (r : ℝ)
    (hr₀ : 0 ≤ r) (hr : r < CappedBaseStock.mean P) :
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
