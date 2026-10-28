-- Prove2me | solution 1 for OAI.PiExponent.FiniteMinorComparison.logWeightedCollisionRatio_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T06:58:26.268188+00:00
-- url     : https://prove2.me/submissions/fb6e7157-a0ab-43fc-b167-1498568bb3ac

import Definitions.Def_PiExponent_FiniteMinorComparison
import Mathlib

section

open MeasureTheory Set

namespace PiSimplex

noncomputable section

/-- the simplex `{x ≥ 0, ∑ x ≤ c}` -/
def S (n : ℕ) (c : ℝ) : Set (Fin n → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ c}

lemma S_closed (n : ℕ) (c : ℝ) : IsClosed (S n c) := by
  unfold S
  refine IsClosed.inter ?_ ?_
  · have := isClosed_iInter fun i : Fin n =>
      isClosed_le (continuous_const (y := (0 : ℝ))) (continuous_apply (A := fun _ : Fin n => ℝ) i)
    rw [Set.iInter_setOf] at this
    exact this
  · exact isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const

lemma S_meas (n : ℕ) (c : ℝ) : MeasurableSet (S n c) := (S_closed n c).measurableSet

lemma S_neg (n : ℕ) {c : ℝ} (hc : c < 0) : S n c = ∅ := by
  ext x
  simp only [S, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_le]
  intro h
  exact lt_of_lt_of_le hc (Finset.sum_nonneg fun i _ => h i)

lemma slice (n : ℕ) (c t : ℝ) :
    {y : Fin n → ℝ | (Fin.cons t y : Fin (n + 1) → ℝ) ∈ S (n + 1) c} =
      if 0 ≤ t then S n (c - t) else ∅ := by
  ext y
  simp only [S, mem_setOf_eq, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.sum_univ_succ]
  split_ifs with h
  · simp only [h, true_and, mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  · simp [h]

/-- the value of the volume -/
def F (n : ℕ) (c : ℝ) : ENNReal := if 0 ≤ c then ENNReal.ofReal (c ^ n / n.factorial) else 0

lemma integral_pow_sub (n : ℕ) (c : ℝ) :
    ∫ t in (0 : ℝ)..c, (c - t) ^ n / n.factorial = c ^ (n + 1) / (n + 1).factorial := by
  rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_left (fun t => t ^ n)]
  simp only [sub_self, sub_zero, integral_pow]
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

lemma vol_succ (n : ℕ) (c : ℝ) :
    volume (S (n + 1) c) = ∫⁻ t, (if 0 ≤ t then volume (S n (c - t)) else 0) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  rw [← h.measure_preimage_equiv (S (n + 1) c)]
  rw [show (volume : Measure (Fin (n + 1) → ℝ)) = Measure.pi (fun _ => volume) from rfl] at h
  rw [Measure.volume_eq_prod, Measure.prod_apply]
  · congr 1
    ext t
    have : Prod.mk t ⁻¹' ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm ⁻¹'
        S (n + 1) c) = {y : Fin n → ℝ | (Fin.cons t y : Fin (n + 1) → ℝ) ∈ S (n + 1) c} := by
      ext y
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply]; rfl
    rw [this, slice]
    split_ifs <;> simp
  · exact (MeasurableEquiv.measurable _) (S_meas _ _)

theorem vol_S (n : ℕ) (c : ℝ) : volume (S n c) = F n c := by
  induction n generalizing c with
  | zero =>
    unfold F
    split_ifs with hc
    · have : S 0 c = univ := by
        ext x; simp [S, hc]
      rw [this, volume_pi, Measure.pi_univ]; simp
    · rw [S_neg 0 (lt_of_not_ge hc)]; simp
  | succ n ih =>
    rw [vol_succ]
    simp_rw [ih]
    unfold F
    split_ifs with hc
    · have : (fun t : ℝ => if 0 ≤ t then (if 0 ≤ c - t then ENNReal.ofReal ((c - t) ^ n / n.factorial)
          else 0) else 0) = (Icc 0 c).indicator (fun t => ENNReal.ofReal ((c - t) ^ n / n.factorial)) := by
        ext t
        simp only [indicator, mem_Icc, sub_nonneg]
        split_ifs <;> first | rfl | (exfalso; tauto)
      rw [this, lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal,
        integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hc, integral_pow_sub]
      · exact (Continuous.integrableOn_Icc (by fun_prop))
      · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun t ht => ?_)
        have : 0 ≤ c - t := by linarith [ht.2]
        positivity
    · have : (fun t : ℝ => if 0 ≤ t then (if 0 ≤ c - t then ENNReal.ofReal ((c - t) ^ n / n.factorial)
          else 0) else 0) = fun _ => 0 := by
        ext t
        split_ifs with h1 h2 <;> first | rfl | (exfalso; linarith)
      rw [this]; simp

theorem vol_S_of_nonneg (n : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    volume (S n c) = ENNReal.ofReal (c ^ n / n.factorial) := by
  rw [vol_S, F, if_pos hc]

end

end PiSimplex

end

section

open MeasureTheory Set PiSimplex

namespace PiL2

lemma diag_apply {m : ℕ} (w : Fin m → ℝ) (x : Fin m → ℝ) :
    (Matrix.diagonal w).toLin' x = fun i => w i * x i := by
  ext i; simp [Matrix.mulVec_diagonal]

lemma vol_diag {m : ℕ} (w : Fin m → ℝ) (s : Set (Fin m → ℝ)) :
    volume ((fun x : Fin m → ℝ => fun i => w i * x i) '' s) =
      ENNReal.ofReal |∏ i, w i| * volume s := by
  have := Measure.addHaar_image_linearMap (volume : Measure (Fin m → ℝ)) (Matrix.diagonal w).toLin' s
  have hf : ⇑(Matrix.diagonal w).toLin' = fun x i => w i * x i := funext (diag_apply w)
  rw [LinearMap.det_toLin', Matrix.det_diagonal, hf] at this
  exact this

theorem diag_toReal {m : Nat} (w : Fin m → Real) (hw : ∀ i, w i ≠ 0) (s : Set (Fin m → Real)) (hs : MeasurableSet s) :
    (MeasureTheory.volume ((fun x : Fin m → Real => fun i => w i * x i) '' s)).toReal =
      |(∏ i : Fin m, w i)| * (MeasureTheory.volume s).toReal := by
  rw [vol_diag, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]

lemma weighted_image {m : ℕ} (w : Fin m → ℝ) (hw : ∀ i, 0 < w i) (H : ℝ) :
    (fun x : Fin m → ℝ => fun i => w i * x i) '' {x | (∀ i, 0 ≤ x i) ∧ ∑ i, w i * x i ≤ H} = S m H := by
  ext y
  simp only [mem_image, mem_setOf_eq, S]
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨fun i => mul_nonneg (hw i).le (h1 i), h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => y i / w i, ⟨fun i => div_nonneg (h1 i) (hw i).le, ?_⟩, ?_⟩
    · convert h2 using 2 with i; field_simp [(hw i).ne']
    · ext i; field_simp [(hw i).ne']

theorem weighted_div {m : Nat} (w : Fin m → Real) (H : Real) (hw : ∀ i, 0 < w i) (hH : 0 < H) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, w i * x i ≤ H}).toReal =
      (MeasureTheory.volume {y : Fin m → Real | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ H}).toReal / ∏ i : Fin m, w i := by
  have hp : 0 < ∏ i, w i := Finset.prod_pos fun i _ => hw i
  have := vol_diag w {x | (∀ i, 0 ≤ x i) ∧ ∑ i, w i * x i ≤ H}
  rw [weighted_image w hw] at this
  change _ = (volume (S m H)).toReal / _
  rw [this, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos hp]
  field_simp

theorem weighted_formula {m : Nat} (w : Fin m → Real) (B : Real) (hw : ∀ i, 0 < w i) (hB : 0 < B) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ B + ∑ i : Fin m, w i}).toReal =
      (B + ∑ i : Fin m, w i) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i := by
  have h0 : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ => (hw i).le
  rw [weighted_div w _ hw (by linarith)]
  change (volume (S m _)).toReal / _ = _
  rw [vol_S_of_nonneg _ (by linarith), ENNReal.toReal_ofReal (by positivity)]

end PiL2

end

section

open MeasureTheory Set

namespace PiL20

noncomputable def rws {m : ℕ} (w : Fin m → ℝ) (R : ℝ) : Finset (Fin m → ℕ) := by
  classical
  exact (Fintype.piFinset (fun i => Finset.range (⌊R / w i⌋₊ + 1))).filter
    (fun a => ∑ i, w i * (a i : ℝ) ≤ R)

noncomputable def srws {m : ℕ} (w : Fin m → ℝ) (R : ℝ) : Finset (Fin m → ℕ) := by
  classical
  exact (rws w R).filter (fun a => ∑ i, w i * (a i : ℝ) < R)

lemma mem_rws {m : ℕ} {w : Fin m → ℝ} {R : ℝ} {a : Fin m → ℕ} :
    a ∈ rws w R ↔ (∀ i, a i < ⌊R / w i⌋₊ + 1) ∧ ∑ i, w i * (a i : ℝ) ≤ R := by
  classical
  simp [rws, Fintype.mem_piFinset]

lemma mem_rws' {m : ℕ} {w : Fin m → ℝ} (hw : ∀ i, 0 < w i) {R : ℝ} {a : Fin m → ℕ} :
    a ∈ rws w R ↔ ∑ i, w i * (a i : ℝ) ≤ R := by
  rw [mem_rws]
  refine ⟨fun h => h.2, fun h => ⟨fun i => ?_, h⟩⟩
  apply Nat.lt_succ_of_le
  apply Nat.le_floor
  rw [le_div_iff₀ (hw i), mul_comm]
  have := Finset.single_le_sum (f := fun j => w j * (a j : ℝ))
    (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)
  linarith

lemma mem_srws {m : ℕ} {w : Fin m → ℝ} (hw : ∀ i, 0 < w i) {R : ℝ} {a : Fin m → ℕ} :
    a ∈ srws w R ↔ ∑ i, w i * (a i : ℝ) < R := by
  classical
  simp only [srws, Finset.mem_filter, mem_rws' hw]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

def box {m : ℕ} (n : Fin m → ℕ) : Set (Fin m → ℝ) := {x | ∀ i, (n i : ℝ) ≤ x i ∧ x i < (n i : ℝ) + 1}

lemma box_eq {m : ℕ} (n : Fin m → ℕ) : box n = Set.pi univ fun i => Ico (n i : ℝ) (n i + 1) := by
  ext x; simp [box]

lemma vol_box {m : ℕ} (n : Fin m → ℕ) : volume (box n) = 1 := by
  rw [box_eq, Real.volume_pi_Ico]; simp

lemma box_meas {m : ℕ} (n : Fin m → ℕ) : MeasurableSet (box n) := by
  rw [box_eq]; exact MeasurableSet.univ_pi fun i => measurableSet_Ico

lemma union_eq {m : ℕ} (S : Finset (Fin m → ℕ)) : volume (⋃ n ∈ S, box n) = S.card := by
  rw [measure_biUnion_finset]
  · simp [vol_box]
  · intro a _ b _ hab
    rw [Function.onFun, Set.disjoint_left]
    intro x hxa hxb
    apply hab
    funext i
    obtain ⟨h1, h2⟩ := hxa i
    obtain ⟨h3, h4⟩ := hxb i
    have e1 : (a i : ℝ) < b i + 1 := lt_of_le_of_lt h1 h4
    have e2 : (b i : ℝ) < a i + 1 := lt_of_le_of_lt h3 h2
    have e1' : a i < b i + 1 := by exact_mod_cast e1
    have e2' : b i < a i + 1 := by exact_mod_cast e2
    omega
  · intro a _; exact box_meas a

lemma region_lt_top {m : ℕ} (w : Fin m → ℝ) (hw : ∀ i, 0 < w i) (C : ℝ) :
    volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ C} < ⊤ := by
  refine lt_of_le_of_lt (measure_mono (t := Set.pi univ fun i => Icc (0:ℝ) (|C| / w i)) ?_) ?_
  · rintro x ⟨hx0, hxs⟩ i _
    refine ⟨hx0 i, ?_⟩
    have := Finset.single_le_sum (f := fun j => w j * x j) (fun j _ => mul_nonneg (hw j).le (hx0 j))
      (Finset.mem_univ i)
    rw [le_div_iff₀ (hw i), mul_comm]
    linarith [le_abs_self C]
  · rw [volume_pi_pi]; simp [Real.volume_Icc, ENNReal.prod_lt_top]

theorem card_upper {m : Nat} (w : Fin m → Real) (B : Real) (hw : ∀ i, 0 < w i) (hB : 0 < B) :
    ((rws w B).card : Real) ≤ (B + ∑ i : Fin m, w i) ^ m / ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i := by
  rw [← PiL2.weighted_formula w B hw hB]
  have h1 := union_eq (rws w B)
  have h2 : (⋃ n ∈ rws w B, box n) ⊆
      {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ B + ∑ i : Fin m, w i} := by
    intro x hx
    simp only [mem_iUnion, exists_prop] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    have hs := (mem_rws.1 ha).2
    refine ⟨fun i => le_trans (Nat.cast_nonneg _) (hxa i).1, ?_⟩
    calc ∑ i, w i * x i ≤ ∑ i, (w i * (a i : ℝ) + w i) := Finset.sum_le_sum fun i _ => by
            nlinarith [(hxa i).2, hw i]
      _ = ∑ i, w i * (a i : ℝ) + ∑ i, w i := Finset.sum_add_distrib
      _ ≤ _ := by linarith
  have := ENNReal.toReal_mono (region_lt_top w hw _).ne (measure_mono h2)
  rw [h1] at this
  simpa using this

theorem card_lower {m : Nat} (w : Fin m → Real) (B R : Real) (hw : ∀ i, 0 < w i) (hB : 0 < B)
    (hR : B + ∑ i : Fin m, w i < R) :
    (B + ∑ i : Fin m, w i) ^ m / ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i ≤
      ((srws w R).card : Real) := by
  rw [← PiL2.weighted_formula w B hw hB]
  have h0 : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ => (hw i).le
  have hsub : {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ B + ∑ i : Fin m, w i} ⊆
      ⋃ n ∈ srws w R, box n := by
    rintro x ⟨hx0, hxs⟩
    simp only [mem_iUnion, exists_prop]
    refine ⟨fun i => ⌊x i⌋₊, (mem_srws hw).2 ?_, fun i => ⟨Nat.floor_le (hx0 i), Nat.lt_floor_add_one _⟩⟩
    calc ∑ i, w i * (⌊x i⌋₊ : ℝ) ≤ ∑ i, w i * x i :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (Nat.floor_le (hx0 i)) (hw i).le
      _ < R := by linarith
  have hfin : volume (⋃ n ∈ srws w R, box n) ≠ ⊤ := by
    rw [union_eq]; simp
  have := ENNReal.toReal_mono hfin (measure_mono hsub)
  rw [union_eq] at this
  simpa using this

end PiL20
end

section

open Filter Topology
open scoped BigOperators

namespace S35Col

theorem rws_eq {m : ℕ} (w : Fin m → ℝ) (R : ℝ) : PiL20.rws w R = OAI.PiExponent.realWeightedSimplex w R := rfl
theorem srws_eq {m : ℕ} (w : Fin m → ℝ) (R : ℝ) : PiL20.srws w R = OAI.PiExponent.strictWeightedSimplex w R := rfl

theorem squeeze_aux {m : ℕ} (w : Fin m → ℝ) (hw : ∀ i, 0 < w i) (f : ℝ → ℝ)
    (hlo : ∀ᶠ H in atTop, ((PiL20.srws w H).card : ℝ) ≤ f H)
    (hhi : ∀ᶠ H in atTop, f H ≤ ((PiL20.rws w H).card : ℝ)) :
    Tendsto (fun H => f H / H ^ m) atTop (𝓝 (1 / ((m.factorial : ℝ) * ∏ i, w i))) := by
  set c : ℝ := 1 / ((m.factorial : ℝ) * ∏ i, w i) with hc
  set s : ℝ := ∑ i, w i with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => (hw i).le
  have hP : 0 < ∏ i, w i := Finset.prod_pos fun i _ => hw i
  have hlim : ∀ a : ℝ, Tendsto (fun H : ℝ => (1 + a * H⁻¹) ^ m * c) atTop (𝓝 c) := by
    intro a
    have := ((tendsto_inv_atTop_zero.const_mul a).const_add 1).pow m |>.mul_const c
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim (-1)) (hlim s) ?_ ?_
  · filter_upwards [hlo, eventually_gt_atTop (s + 1)] with H hH hHs
    have hH0 : 0 < H := by linarith
    have h1 := PiL20.card_lower w (H - s - 1) H hw (by linarith) (by linarith)
    have e : (1 + -1 * H⁻¹) ^ m * c = (H - s - 1 + s) ^ m / (m.factorial : ℝ) / (∏ i, w i) / H ^ m := by
      have e1 : 1 + -1 * H⁻¹ = (H - s - 1 + s) / H := by field_simp; ring
      rw [e1, div_pow, hc]; field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (h1.trans hH) (by positivity)
  · filter_upwards [hhi, eventually_gt_atTop (0:ℝ)] with H hH hH0
    have h1 := PiL20.card_upper w H hw hH0
    have e : (1 + s * H⁻¹) ^ m * c = (H + s) ^ m / (m.factorial : ℝ) / (∏ i, w i) / H ^ m := by
      have e1 : 1 + s * H⁻¹ = (H + s) / H := by field_simp
      rw [e1, div_pow, hc]; field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (hH.trans h1) (by positivity)

theorem rws_tendsto {m : ℕ} (w : Fin m → ℝ) (hw : ∀ i, 0 < w i) :
    Tendsto (fun H => ((PiL20.rws w H).card : ℝ) / H ^ m) atTop
      (𝓝 (1 / ((m.factorial : ℝ) * ∏ i, w i))) := by
  apply squeeze_aux w hw
  · refine Eventually.of_forall fun H => ?_
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  · exact Eventually.of_forall fun H => le_rfl

theorem srws_tendsto {m : ℕ} (w : Fin m → ℝ) (hw : ∀ i, 0 < w i) :
    Tendsto (fun H => ((PiL20.srws w H).card : ℝ) / H ^ m) atTop
      (𝓝 (1 / ((m.factorial : ℝ) * ∏ i, w i))) := by
  apply squeeze_aux w hw
  · exact Eventually.of_forall fun H => le_rfl
  · refine Eventually.of_forall fun H => ?_
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

theorem main
    (m K : ℕ) (v0 theta : ℚ) (A eta : ℝ) (q : Fin m → ℕ)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hA : 0 < A)
    (hq : ∀ i, 2 ≤ q i) :
    Tendsto
      (OAI.PiExponent.FiniteMinorComparison.collisionRate
        K (v0 : ℝ) (theta : ℝ) A eta q) atTop
      (𝓝 (OAI.PiExponent.FiniteMinorComparison.collisionLimit
        m K (v0 : ℝ) (theta : ℝ) A eta)) := by
  set lw := OAI.PiExponent.MatrixArithmetic.logWeights q with hlw_def
  have hlw : ∀ i, 0 < lw i := by
    intro i
    simp only [hlw_def, OAI.PiExponent.MatrixArithmetic.logWeights]
    have : 0 < Real.log (q i) := Real.log_pos (by exact_mod_cast (by have := hq i; omega : 1 < q i))
    exact_mod_cast Nat.ceil_pos.mpr this
  have hv0' : (0:ℝ) < v0 := by exact_mod_cast hv0
  have hth' : (0:ℝ) < theta := by exact_mod_cast htheta
  set u := OAI.PiExponent.InterpolationMatrix.rowWeights (v0 : ℝ) (theta : ℝ) lw with hu_def
  have hu : ∀ i, 0 < u i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [hu_def, OAI.PiExponent.InterpolationMatrix.rowWeights] using hv0'
    · simp only [hu_def, OAI.PiExponent.InterpolationMatrix.rowWeights, Fin.cases_succ]
      exact div_pos (hlw j) hth'
  have h1 := srws_tendsto u hu
  have h2 := (rws_tendsto lw hlw).comp (tendsto_id.const_mul_atTop hA)
  have hP : 0 < ∏ i, lw i := Finset.prod_pos fun i _ => hlw i
  have hPu : ∏ i, u i = (v0 : ℝ) * (∏ i, lw i) / (theta : ℝ) ^ m := by
    rw [Fin.prod_univ_succ]
    simp only [hu_def, OAI.PiExponent.InterpolationMatrix.rowWeights, Fin.cases_zero, Fin.cases_succ]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  have hc2 : (1 / ((m.factorial : ℝ) * ∏ i, lw i)) * A ^ m ≠ 0 := by positivity
  have hlim := ((h1.const_mul ((Real.log 2 / 4) * eta ^ 2 * K)).div (h2.mul_const (A ^ m)) hc2)
  have heq : (Real.log 2 / 4) * eta ^ 2 * K * (1 / (((m + 1).factorial : ℝ) * ∏ i, u i)) /
      ((1 / ((m.factorial : ℝ) * ∏ i, lw i)) * A ^ m) =
      OAI.PiExponent.FiniteMinorComparison.collisionLimit m K (v0 : ℝ) (theta : ℝ) A eta := by
    rw [hPu, OAI.PiExponent.FiniteMinorComparison.collisionLimit, Nat.factorial_succ]
    push_cast
    field_simp
  rw [heq] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with H hH
  simp only [Pi.div_apply, Function.comp_apply, id, OAI.PiExponent.FiniteMinorComparison.collisionRate]
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, ← srws_eq, ← rws_eq]
  push_cast
  have hAH : 0 < A * H := mul_pos hA hH
  set X := ((PiL20.rws lw (A * H)).card : ℝ)
  set Y := ((PiL20.srws u H).card : ℝ)
  rw [mul_pow]
  field_simp
  ring

end S35Col

end

namespace S35Col2
open Filter Topology
open scoped BigOperators
theorem main2
    (m K : ℕ) (v0 theta A : ℝ) (q : Fin m → ℕ)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hA : 0 < A)
    (hq : ∀ i, 2 ≤ q i) :
    Tendsto
      (fun H : ℝ =>
        (Fintype.card
          (OAI.PiExponent.InterpolationMatrix.Row K v0 theta
            (OAI.PiExponent.MatrixArithmetic.logWeights q) H) : ℝ) /
          (H * (Fintype.card
            (OAI.PiExponent.realWeightedSimplex
              (OAI.PiExponent.MatrixArithmetic.logWeights q) (A * H)) : ℝ)))
      atTop
      (𝓝 ((K : ℝ) * theta ^ m / (((m : ℝ) + 1) * v0 * A ^ m))) := by
  set lw := OAI.PiExponent.MatrixArithmetic.logWeights q with hlw_def
  have hlw : ∀ i, 0 < lw i := by
    intro i
    simp only [hlw_def, OAI.PiExponent.MatrixArithmetic.logWeights]
    have : 0 < Real.log (q i) := Real.log_pos (by exact_mod_cast (by have := hq i; omega : 1 < q i))
    exact_mod_cast Nat.ceil_pos.mpr this
  set u := OAI.PiExponent.InterpolationMatrix.rowWeights v0 theta lw with hu_def
  have hu : ∀ i, 0 < u i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [hu_def, OAI.PiExponent.InterpolationMatrix.rowWeights] using hv0
    · simp only [hu_def, OAI.PiExponent.InterpolationMatrix.rowWeights, Fin.cases_succ]
      exact div_pos (hlw j) htheta
  have h1 := S35Col.srws_tendsto u hu
  have h2 := (S35Col.rws_tendsto lw hlw).comp (tendsto_id.const_mul_atTop hA)
  have hP : 0 < ∏ i, lw i := Finset.prod_pos fun i _ => hlw i
  have hPu : ∏ i, u i = v0 * (∏ i, lw i) / theta ^ m := by
    rw [Fin.prod_univ_succ]
    simp only [hu_def, OAI.PiExponent.InterpolationMatrix.rowWeights, Fin.cases_zero, Fin.cases_succ]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  have hc2 : (1 / ((m.factorial : ℝ) * ∏ i, lw i)) * A ^ m ≠ 0 := by positivity
  have hlim := ((h1.const_mul (K : ℝ)).div (h2.mul_const (A ^ m)) hc2)
  have heq : (K : ℝ) * (1 / (((m + 1).factorial : ℝ) * ∏ i, u i)) /
      ((1 / ((m.factorial : ℝ) * ∏ i, lw i)) * A ^ m) =
      (K : ℝ) * theta ^ m / (((m : ℝ) + 1) * v0 * A ^ m) := by
    rw [hPu, Nat.factorial_succ]
    push_cast
    field_simp
  rw [heq] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with H hH
  simp only [Pi.div_apply, Function.comp_apply, id]
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, Fintype.card_coe, ← S35Col.srws_eq,
    ← S35Col.rws_eq]
  push_cast
  have hAH : 0 < A * H := mul_pos hA hH
  set X := ((PiL20.rws lw (A * H)).card : ℝ)
  set Y := ((PiL20.srws u H).card : ℝ)
  rw [mul_pow]
  field_simp
  ring
end S35Col2

open Filter Topology
open scoped BigOperators
theorem solution
    (m K : ℕ) (v0 theta A : ℝ) (q : Fin m → ℕ)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hA : 0 < A)
    (hq : ∀ i, 2 ≤ q i) :
    Tendsto
      (fun H : ℝ =>
        (Fintype.card
          (OAI.PiExponent.InterpolationMatrix.Row K v0 theta
            (OAI.PiExponent.MatrixArithmetic.logWeights q) H) : ℝ) /
          (H * (Fintype.card
            (OAI.PiExponent.realWeightedSimplex
              (OAI.PiExponent.MatrixArithmetic.logWeights q) (A * H)) : ℝ)))
      atTop
      (𝓝 ((K : ℝ) * theta ^ m / (((m : ℝ) + 1) * v0 * A ^ m))) :=
  S35Col2.main2 m K v0 theta A q hv0 htheta hA hq
