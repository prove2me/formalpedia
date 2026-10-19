-- Prove2me | solution 1 for MDPFinance.OptimalStopping.theorem_10_1_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T21:54:27.126734+00:00
-- url     : https://prove2.me/submissions/95d0c553-cf7d-481b-9475-29d16e1b9d8a

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_StoppingProblem


open MeasureTheory Filter Topology Set
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace OSAux
open MDPFinance.OptimalStopping

variable {E : Type*} [MeasurableSpace E] {N : ℕ}

/-- prepend a point to a path -/
def cons (x : E) (w : ℕ → E) : ℕ → E := fun i => match i with
  | 0 => x
  | k + 1 => w k

@[simp] lemma cons_zero (x : E) (w : ℕ → E) : cons x w 0 = x := rfl
@[simp] lemma cons_succ (x : E) (w : ℕ → E) (k : ℕ) : cons x w (k + 1) = w k := rfl

lemma cons_meas (x : E) : Measurable (cons x) := by
  refine measurable_pi_lambda _ (fun i => ?_)
  cases i with
  | zero => exact measurable_const
  | succ k => exact measurable_pi_apply k

def box (m : ℕ) (B : ℕ → Set E) : Set (ℕ → E) := {w | ∀ i ≤ m, w i ∈ B i}

def boxes (E : Type*) [MeasurableSpace E] : Set (Set (ℕ → E)) :=
  {S | ∃ m B, (∀ i, MeasurableSet (B i)) ∧ S = box m B}

lemma box_meas (m : ℕ) (B : ℕ → Set E) (hB : ∀ i, MeasurableSet (B i)) :
    MeasurableSet (box m B) := by
  have : box m B = ⋂ i ∈ Finset.range (m + 1), (fun w : ℕ → E => w i) ⁻¹' B i := by
    ext w; simp [box, Nat.lt_succ_iff]
  rw [this]
  exact Finset.measurableSet_biInter _ (fun i _ => (measurable_pi_apply i) (hB i))

lemma boxes_pi : IsPiSystem (boxes E) := by
  rintro _ ⟨m1, B1, hB1, rfl⟩ _ ⟨m2, B2, hB2, rfl⟩ _
  refine ⟨max m1 m2, fun i => (if i ≤ m1 then B1 i else univ) ∩ (if i ≤ m2 then B2 i else univ),
    fun i => ?_, ?_⟩
  · refine MeasurableSet.inter ?_ ?_
    · split_ifs; exacts [hB1 i, MeasurableSet.univ]
    · split_ifs; exacts [hB2 i, MeasurableSet.univ]
  · ext w
    simp only [box, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      constructor
      · split_ifs with h; exacts [h1 i h, mem_univ _]
      · split_ifs with h; exacts [h2 i h, mem_univ _]
    · intro h
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · have := (h i (le_max_of_le_left hi)).1; rwa [if_pos hi] at this
      · have := (h i (le_max_of_le_right hi)).2; rwa [if_pos hi] at this

lemma boxes_gen : (MeasurableSpace.pi : MeasurableSpace (ℕ → E)) =
    MeasurableSpace.generateFrom (boxes E) := by
  apply le_antisymm
  · refine iSup_le (fun i => ?_)
    rw [MeasurableSpace.comap_le_iff_le_map]
    intro A hA
    apply MeasurableSpace.measurableSet_generateFrom
    refine ⟨i, fun j => if j = i then A else univ, fun j => ?_, ?_⟩
    · show MeasurableSet (if j = i then A else univ)
      split_ifs; exacts [hA, MeasurableSet.univ]
    · ext w
      simp only [mem_preimage, box, mem_setOf_eq]
      constructor
      · intro h j _
        split_ifs with hj
        · subst hj; exact h
        · exact mem_univ _
      · intro h
        have := h i le_rfl
        rwa [if_pos rfl] at this
  · refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨m, B, hB, rfl⟩
    exact box_meas m B hB

lemma cyl_meas (P : StoppingProblem E N) (m : ℕ) : ∀ (t : ℕ) (B : ℕ → Set E),
    (∀ i, MeasurableSet (B i)) → Measurable (P.cyl t m B) := by
  induction m with
  | zero => intro t B _; exact measurable_const
  | succ m ih =>
    intro t B hB
    have hf := ih (t + 1) (fun i => B (i + 1)) (fun i => hB (i + 1))
    have : P.cyl t (m + 1) B = fun x =>
        ∫⁻ y, (B 0).indicator (P.cyl (t + 1) m (fun i => B (i + 1))) y ∂(P.QX t x) := by
      funext x
      rw [StoppingProblem.cyl, lintegral_indicator (hB 0)]
    rw [this]
    exact (Measure.measurable_lintegral (hf.indicator (hB 0))).comp (P.QX_meas t)

variable {P : StoppingProblem E N} {Pr : ℕ → E → Measure (ℕ → E)}

lemma pr_box (hPr : P.IsPathLaw Pr) (n : ℕ) (x : E) (m : ℕ) (B : ℕ → Set E)
    (hB : ∀ i, MeasurableSet (B i)) :
    Pr n x (box m B) = (B 0).indicator (fun y => P.cyl n m (fun i => B (i + 1)) y) x :=
  hPr.2 n x m B hB

lemma pr_meas (hPr : P.IsPathLaw Pr) (n : ℕ) : Measurable (Pr n) := by
  haveI := hPr.1
  refine Measure.measurable_of_measurable_coe _ (fun S hS => ?_)
  induction S, hS using MeasurableSpace.induction_on_inter boxes_gen boxes_pi with
  | empty => simp
  | basic t ht =>
    obtain ⟨m, B, hB, rfl⟩ := ht
    have : (fun y => Pr n y (box m B)) =
        (B 0).indicator (fun y => P.cyl n m (fun i => B (i + 1)) y) := by
      funext y; exact pr_box hPr n y m B hB
    rw [this]
    exact (cyl_meas P m n _ (fun i => hB (i + 1))).indicator (hB 0)
  | compl t htm ih =>
    have : (fun y => Pr n y tᶜ) = fun y => 1 - Pr n y t := by
      funext y; rw [measure_compl htm (measure_ne_top _ _), measure_univ]
    rw [this]; exact measurable_const.sub ih
  | iUnion f hd hfm ih =>
    have : (fun y => Pr n y (⋃ i, f i)) = fun y => ∑' i, Pr n y (f i) := by
      funext y; exact measure_iUnion hd hfm
    rw [this]; exact Measurable.ennreal_tsum ih

open scoped Classical in
lemma cons_box_zero (x : E) (B : ℕ → Set E) :
    cons x ⁻¹' box 0 B = if x ∈ B 0 then univ else ∅ := by
  ext w; split_ifs with h <;> simp [box, h]

open scoped Classical in
lemma cons_box_succ (x : E) (m : ℕ) (B : ℕ → Set E) :
    cons x ⁻¹' box (m + 1) B = if x ∈ B 0 then box m (fun i => B (i + 1)) else ∅ := by
  ext w
  split_ifs with h
  · simp only [mem_preimage, box, mem_setOf_eq]
    constructor
    · intro hw i hi; exact hw (i + 1) (by omega)
    · intro hw i hi
      cases i with
      | zero => exact h
      | succ k => exact hw k (by omega)
  · simp only [mem_preimage, box, mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall]
    exact ⟨0, by omega, h⟩

/-- Markov property: `Pr n x` is `x` followed by a path drawn from `∫ Q_n(x,dy) Pr (n+1) y`. -/
lemma markov (hPr : P.IsPathLaw Pr) (n : ℕ) (x : E) :
    Pr n x = (P.QX n x).bind (fun y => (Pr (n + 1) y).map (cons x)) := by
  haveI := hPr.1
  haveI := P.QX_prob n x
  have hκ : Measurable (fun y => (Pr (n + 1) y).map (cons x)) :=
    (Measure.measurable_map _ (cons_meas x)).comp (pr_meas hPr (n + 1))
  have hbind : ∀ S, MeasurableSet S →
      (P.QX n x).bind (fun y => (Pr (n + 1) y).map (cons x)) S
        = ∫⁻ y, Pr (n + 1) y (cons x ⁻¹' S) ∂(P.QX n x) := by
    intro S hS
    rw [Measure.bind_apply hS hκ.aemeasurable]
    congr 1; funext y; rw [Measure.map_apply (cons_meas x) hS]
  refine ext_of_generate_finite (boxes E) boxes_gen boxes_pi ?_ ?_
  · rintro _ ⟨m, B, hB, rfl⟩
    rw [hbind _ (box_meas m B hB), pr_box hPr n x m B hB]
    cases m with
    | zero =>
      rw [cons_box_zero]
      split_ifs with h
      · simp [h, StoppingProblem.cyl]
      · simp [h]
    | succ m =>
      rw [cons_box_succ]
      split_ifs with h
      · rw [indicator_of_mem h, StoppingProblem.cyl]
        simp_rw [pr_box hPr (n + 1) _ m _ (fun i => hB (i + 1))]
        rw [lintegral_indicator (hB 1)]
      · simp [h]
  · rw [hbind _ MeasurableSet.univ]
    simp

lemma markov_lintegral (hPr : P.IsPathLaw Pr) (n : ℕ) (x : E) {F : (ℕ → E) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ w, F w ∂(Pr n x) = ∫⁻ y, ∫⁻ w, F (cons x w) ∂(Pr (n + 1) y) ∂(P.QX n x) := by
  have hκ : Measurable (fun y => (Pr (n + 1) y).map (cons x)) :=
    (Measure.measurable_map _ (cons_meas x)).comp (pr_meas hPr (n + 1))
  conv_lhs => rw [markov hPr n x]
  rw [Measure.lintegral_bind hκ.aemeasurable hF.aemeasurable]
  congr 1; funext y
  rw [lintegral_map hF (cons_meas x)]

end OSAux

open MeasureTheory Filter Topology Set
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace OSAux
open MDPFinance.OptimalStopping

lemma pp (r : ℝ) : ((r : EReal) ⊔ 0).toENNReal = ENNReal.ofReal r := by
  rcases le_total r 0 with h | h
  · have : (r : EReal) ⊔ 0 = 0 := sup_of_le_right (by exact_mod_cast h)
    rw [this, ENNReal.ofReal_of_nonpos h]; simp
  · have : (r : EReal) ⊔ 0 = r := sup_of_le_left (by exact_mod_cast h)
    rw [this, EReal.toENNReal_of_ne_top (EReal.coe_ne_top r), EReal.toReal_coe]

lemma pn (r : ℝ) : ((-(r : EReal)) ⊔ 0).toENNReal = ENNReal.ofReal (-r) := by
  rw [← EReal.coe_neg, pp]

lemma ereal_real {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) :
    erealIntegral μ (fun w => (f w : EReal)) =
      ((∫⁻ w, ENNReal.ofReal (f w) ∂μ : ℝ≥0∞) : EReal) +
        -((∫⁻ w, ENNReal.ofReal (-f w) ∂μ : ℝ≥0∞) : EReal) := by
  unfold erealIntegral
  simp_rw [pp, pn]

lemma ereal_mono {α : Type*} [MeasurableSpace α] (μ : Measure α) {v w : α → EReal}
    (h : ∀ a, v a ≤ w a) : erealIntegral μ v ≤ erealIntegral μ w := by
  unfold erealIntegral
  refine add_le_add ?_ ?_
  · exact_mod_cast lintegral_mono (fun a => EReal.toENNReal_le_toENNReal (sup_le_sup_right (h a) 0))
  · rw [EReal.neg_le_neg_iff]
    exact_mod_cast lintegral_mono (fun a => EReal.toENNReal_le_toENNReal
      (sup_le_sup_right (EReal.neg_le_neg_iff.2 (h a)) 0))

lemma ennreal_ereal_sub (A B : ℝ≥0∞) (hA : A ≠ ⊤) (hB : B ≠ ⊤) :
    (A : EReal) + -(B : EReal) = ((A.toReal - B.toReal : ℝ) : EReal) := by
  rw [← EReal.coe_ennreal_toReal hA, ← EReal.coe_ennreal_toReal hB]
  norm_cast

lemma ereal_const {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (c : ℝ) : erealIntegral μ (fun _ => (c : EReal)) = c := by
  rw [ereal_real μ (fun _ => c)]
  simp only [lintegral_const, measure_univ, mul_one]
  rw [ennreal_ereal_sub _ _ ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
  congr 1
  rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
  rcases le_total c 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

lemma ereal_shift {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (c : ℝ) (f : α → ℝ) (hf : Measurable f) :
    erealIntegral μ (fun w => ((c + f w : ℝ) : EReal)) = (c : EReal) + erealIntegral μ (fun w => (f w : EReal)) := by
  rw [ereal_real, ereal_real]
  set A := ∫⁻ w, ENNReal.ofReal (f w) ∂μ
  set B := ∫⁻ w, ENNReal.ofReal (-f w) ∂μ
  set A' := ∫⁻ w, ENNReal.ofReal (c + f w) ∂μ
  set B' := ∫⁻ w, ENNReal.ofReal (-(c + f w)) ∂μ
  have h1 : A' ≤ ENNReal.ofReal c + A := by
    calc A' ≤ ∫⁻ w, (ENNReal.ofReal c + ENNReal.ofReal (f w)) ∂μ :=
          lintegral_mono (fun w => ENNReal.ofReal_add_le)
      _ = ENNReal.ofReal c + A := by
          rw [lintegral_add_left measurable_const]; simp only [lintegral_const, measure_univ, mul_one]; rfl
  have h2 : A ≤ A' + ENNReal.ofReal (-c) := by
    calc A ≤ ∫⁻ w, (ENNReal.ofReal (c + f w) + ENNReal.ofReal (-c)) ∂μ :=
          lintegral_mono (fun w => by
            have := ENNReal.ofReal_add_le (p := c + f w) (q := -c)
            rwa [show c + f w + -c = f w by ring] at this)
      _ = A' + ENNReal.ofReal (-c) := by
          rw [lintegral_add_right _ measurable_const]; simp only [lintegral_const, measure_univ, mul_one]; rfl
  have h3 : B' ≤ ENNReal.ofReal (-c) + B := by
    calc B' ≤ ∫⁻ w, (ENNReal.ofReal (-c) + ENNReal.ofReal (-f w)) ∂μ :=
          lintegral_mono (fun w => by
            have := ENNReal.ofReal_add_le (p := -c) (q := -f w)
            rwa [show -c + -f w = -(c + f w) by ring] at this)
      _ = ENNReal.ofReal (-c) + B := by
          rw [lintegral_add_left measurable_const]; simp only [lintegral_const, measure_univ, mul_one]; rfl
  have h4 : B ≤ B' + ENNReal.ofReal c := by
    calc B ≤ ∫⁻ w, (ENNReal.ofReal (-(c + f w)) + ENNReal.ofReal c) ∂μ :=
          lintegral_mono (fun w => by
            have := ENNReal.ofReal_add_le (p := -(c + f w)) (q := c)
            rwa [show -(c + f w) + c = -f w by ring] at this)
      _ = B' + ENNReal.ofReal c := by
          rw [lintegral_add_right _ measurable_const]; simp only [lintegral_const, measure_univ, mul_one]; rfl
  by_cases hA : A = ⊤
  · have hA' : A' = ⊤ := by
      by_contra h
      have : A' + ENNReal.ofReal (-c) ≠ ⊤ := ENNReal.add_ne_top.2 ⟨h, ENNReal.ofReal_ne_top⟩
      exact this (top_le_iff.1 (hA ▸ h2))
    by_cases hB : B = ⊤
    · have hB' : B' = ⊤ := by
        by_contra h
        have : B' + ENNReal.ofReal c ≠ ⊤ := ENNReal.add_ne_top.2 ⟨h, ENNReal.ofReal_ne_top⟩
        exact this (top_le_iff.1 (hB ▸ h4))
      rw [hA, hA', hB, hB']; simp
    · have hB' : B' ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hB⟩) h3
      rw [hA, hA', ← EReal.coe_ennreal_toReal hB, ← EReal.coe_ennreal_toReal hB']
      simp only [EReal.coe_ennreal_top]
      rw [← EReal.coe_neg, ← EReal.coe_neg, EReal.top_add_coe, EReal.top_add_coe,
        EReal.coe_add_top]
  · have hA' : A' ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hA⟩) h1
    by_cases hB : B = ⊤
    · have hB' : B' = ⊤ := by
        by_contra h
        have : B' + ENNReal.ofReal c ≠ ⊤ := ENNReal.add_ne_top.2 ⟨h, ENNReal.ofReal_ne_top⟩
        exact this (top_le_iff.1 (hB ▸ h4))
      rw [hB, hB', ← EReal.coe_ennreal_toReal hA, ← EReal.coe_ennreal_toReal hA']
      simp only [EReal.coe_ennreal_top, EReal.neg_top, EReal.add_bot]
    · have hB' : B' ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hB⟩) h3
      rw [ennreal_ereal_sub _ _ hA' hB', ennreal_ereal_sub _ _ hA hB]
      norm_cast
      -- integrability
      have hfi : Integrable f μ := by
        refine ⟨hf.aestronglyMeasurable, ?_⟩
        unfold HasFiniteIntegral
        calc ∫⁻ w, ‖f w‖ₑ ∂μ ≤ ∫⁻ w, (ENNReal.ofReal (f w) + ENNReal.ofReal (-f w)) ∂μ := by
              refine lintegral_mono (fun w => ?_)
              rw [Real.enorm_eq_ofReal_abs]
              rcases le_total (f w) 0 with h | h
              · rw [abs_of_nonpos h]; exact le_add_self
              · rw [abs_of_nonneg h]; exact le_self_add
          _ = A + B := lintegral_add_left (hf.ennreal_ofReal) _
          _ < ⊤ := ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hA, lt_top_iff_ne_top.2 hB⟩
      have hcfi : Integrable (fun w => c + f w) μ := (integrable_const c).add hfi
      have e1 := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi
      have e2 := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hcfi
      rw [integral_add (integrable_const c) hfi, integral_const] at e2
      simp only [probReal_univ, smul_eq_mul, one_mul] at e2
      linarith

lemma pt_pos (a b : ℝ≥0∞) (ha : a ≠ ⊤) :
    (((a : EReal) - (b : EReal)) ⊔ 0).toENNReal = a - b := by
  by_cases hb : b = ⊤
  · subst hb
    rw [EReal.coe_ennreal_top, ← EReal.coe_ennreal_toReal ha, EReal.sub_top]
    simp
  · rw [← EReal.coe_ennreal_toReal ha, ← EReal.coe_ennreal_toReal hb, ← EReal.coe_sub, pp,
      ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ha,
      ENNReal.ofReal_toReal hb]

lemma pt_neg (a b : ℝ≥0∞) (ha : a ≠ ⊤) :
    ((-((a : EReal) - (b : EReal))) ⊔ 0).toENNReal = b - a := by
  by_cases hb : b = ⊤
  · subst hb
    rw [EReal.coe_ennreal_top, ← EReal.coe_ennreal_toReal ha, EReal.sub_top]
    simp [ENNReal.top_sub ha]
  · rw [← EReal.coe_ennreal_toReal ha, ← EReal.coe_ennreal_toReal hb, ← EReal.coe_sub, pn,
      neg_sub, ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ha,
      ENNReal.ofReal_toReal hb]

lemma ereal_sub_int {α : Type*} [MeasurableSpace α] (μ : Measure α) {a b : α → ℝ≥0∞}
    (ha : Measurable a) (hb : Measurable b) (hfin : ∫⁻ y, a y ∂μ ≠ ⊤) :
    erealIntegral μ (fun y => (a y : EReal) - (b y : EReal)) =
      ((∫⁻ y, a y ∂μ : ℝ≥0∞) : EReal) - ((∫⁻ y, b y ∂μ : ℝ≥0∞) : EReal) := by
  have hae : ∀ᵐ y ∂μ, a y ≠ ⊤ := ae_lt_top' ha.aemeasurable hfin |>.mono (fun y h => h.ne)
  unfold erealIntegral
  have e1 : ∫⁻ y, (((a y : EReal) - (b y : EReal)) ⊔ 0).toENNReal ∂μ = ∫⁻ y, (a y - b y) ∂μ :=
    lintegral_congr_ae (hae.mono (fun y h => pt_pos _ _ h))
  have e2 : ∫⁻ y, ((-((a y : EReal) - (b y : EReal))) ⊔ 0).toENNReal ∂μ = ∫⁻ y, (b y - a y) ∂μ :=
    lintegral_congr_ae (hae.mono (fun y h => pt_neg _ _ h))
  rw [e1, e2]
  set X := ∫⁻ y, (a y - b y) ∂μ
  set Y := ∫⁻ y, (b y - a y) ∂μ
  set Ai := ∫⁻ y, a y ∂μ
  set Bi := ∫⁻ y, b y ∂μ
  have key : X + Bi = Y + Ai := by
    show ∫⁻ y, (a y - b y) ∂μ + ∫⁻ y, b y ∂μ = ∫⁻ y, (b y - a y) ∂μ + ∫⁻ y, a y ∂μ
    rw [← lintegral_add_left (f := fun y => a y - b y) (ha.sub hb) b,
      ← lintegral_add_left (f := fun y => b y - a y) (hb.sub ha) a]
    congr 1; funext y; rw [tsub_add_eq_max, tsub_add_eq_max, max_comm]
  have hX : X ≤ Ai := lintegral_mono (fun y => tsub_le_self)
  have hXf : X ≠ ⊤ := ne_top_of_le_ne_top hfin hX
  rw [sub_eq_add_neg]
  by_cases hB : Bi = ⊤
  · have hY : Y = ⊤ := by
      by_contra h
      have : Y + Ai ≠ ⊤ := ENNReal.add_ne_top.2 ⟨h, hfin⟩
      rw [← key, hB] at this; simp at this
    rw [hY, hB]
    simp only [EReal.coe_ennreal_top, EReal.neg_top, EReal.add_bot]
  · have hY : Y ≠ ⊤ := by
      intro h
      have : X + Bi ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hXf, hB⟩
      rw [key, h] at this; simp at this
    rw [ennreal_ereal_sub _ _ hXf hY, ennreal_ereal_sub _ _ hfin hB]
    congr 1
    have := congrArg ENNReal.toReal key
    rw [ENNReal.toReal_add hXf hB, ENNReal.toReal_add hY hfin] at this
    linarith

variable {E : Type*} [MeasurableSpace E] {N : ℕ}
variable {P : StoppingProblem E N} {Pr : ℕ → E → Measure (ℕ → E)}

/-- Markov property for extended-real expectations of real rewards with integrable positive
part. -/
lemma ereal_markov (hPr : P.IsPathLaw Pr) (n : ℕ) (x : E) {F : (ℕ → E) → ℝ}
    (hF : Measurable F) (hfin : ∫⁻ w, ENNReal.ofReal (F w) ∂(Pr n x) ≠ ⊤) :
    erealIntegral (Pr n x) (fun w => (F w : EReal)) =
      erealIntegral (P.QX n x)
        (fun y => erealIntegral (Pr (n + 1) y) (fun w => (F (cons x w) : EReal))) := by
  have hFc : Measurable (fun w => F (cons x w)) := hF.comp (cons_meas x)
  have ha : Measurable (fun y => ∫⁻ w, ENNReal.ofReal (F (cons x w)) ∂(Pr (n + 1) y)) :=
    (Measure.measurable_lintegral hFc.ennreal_ofReal).comp (pr_meas hPr (n + 1))
  have hb : Measurable (fun y => ∫⁻ w, ENNReal.ofReal (-F (cons x w)) ∂(Pr (n + 1) y)) :=
    (Measure.measurable_lintegral hFc.neg.ennreal_ofReal).comp (pr_meas hPr (n + 1))
  have hin : ∀ y, erealIntegral (Pr (n + 1) y) (fun w => (F (cons x w) : EReal)) =
      ((∫⁻ w, ENNReal.ofReal (F (cons x w)) ∂(Pr (n + 1) y) : ℝ≥0∞) : EReal) -
        ((∫⁻ w, ENNReal.ofReal (-F (cons x w)) ∂(Pr (n + 1) y) : ℝ≥0∞) : EReal) := by
    intro y; rw [ereal_real, sub_eq_add_neg]
  simp_rw [hin]
  have m1 := markov_lintegral hPr n x hF.ennreal_ofReal
  have m2 := markov_lintegral hPr n x (F := fun w => ENNReal.ofReal (-F w)) hF.neg.ennreal_ofReal
  rw [ereal_sub_int _ ha hb (by rw [← m1]; exact hfin), ereal_real, ← m1, ← m2, sub_eq_add_neg]

end OSAux

open MeasureTheory Filter Topology Set
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace OSAux
open MDPFinance.OptimalStopping

variable {E : Type*} [MeasurableSpace E]

def proj (n : ℕ) (w : ℕ → E) : Fin (n + 1) → E := fun i => w i

lemma proj_meas (n : ℕ) : Measurable (proj (E := E) n) :=
  measurable_pi_lambda _ (fun i => measurable_pi_apply _)

lemma stop_set {τ : (ℕ → E) → ℕ∞} (hτ : IsStopTime τ) (k : ℕ) :
    ∃ T : Set (Fin (k + 1) → E), MeasurableSet T ∧ {w | τ w ≤ (k : ℕ∞)} = proj k ⁻¹' T := by
  obtain ⟨T, hT, he⟩ := (MeasurableSpace.measurableSet_comap).1 (hτ k)
  exact ⟨T, hT, he.symm⟩

lemma stop_meas {τ : (ℕ → E) → ℕ∞} (hτ : IsStopTime τ) (k : ℕ) :
    MeasurableSet {w | τ w ≤ (k : ℕ∞)} := by
  obtain ⟨T, hT, he⟩ := stop_set hτ k
  rw [he]; exact proj_meas k hT

lemma tau_meas {τ : (ℕ → E) → ℕ∞} (hτ : IsStopTime τ) : Measurable τ := by
  refine measurable_to_countable' (fun e => ?_)
  induction e using ENat.recTopCoe with
  | top =>
    have : τ ⁻¹' {⊤} = (⋃ n : ℕ, {w | τ w ≤ (n : ℕ∞)})ᶜ := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion,
        Set.mem_setOf_eq, not_exists, not_le]
      constructor
      · intro h n; rw [h]; exact ENat.coe_lt_top n
      · intro h
        by_contra hne
        obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hne
        exact absurd (h n) (by rw [← hn]; exact lt_irrefl _)
    rw [this]
    exact (MeasurableSet.iUnion (fun n => stop_meas hτ n)).compl
  | coe n =>
    cases n with
    | zero =>
      have : τ ⁻¹' {((0 : ℕ) : ℕ∞)} = {w | τ w ≤ ((0 : ℕ) : ℕ∞)} := by
        ext w; simp
      rw [this]; exact stop_meas hτ 0
    | succ n =>
      have : τ ⁻¹' {((n + 1 : ℕ) : ℕ∞)} =
          {w | τ w ≤ ((n + 1 : ℕ) : ℕ∞)} \ {w | τ w ≤ (n : ℕ∞)} := by
        ext w
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_diff, Set.mem_setOf_eq, not_le]
        constructor
        · intro h; rw [h]; exact ⟨le_rfl, by exact_mod_cast Nat.lt_succ_self n⟩
        · rintro ⟨h1, h2⟩
          induction h : τ w using ENat.recTopCoe with
          | top => rw [h] at h1; exact absurd h1 (by simp)
          | coe m =>
            rw [h] at h1 h2
            have h1' : m ≤ n + 1 := by exact_mod_cast h1
            have h2' : n < m := by exact_mod_cast h2
            have : m = n + 1 := by omega
            rw [this]
      rw [this]; exact (stop_meas hτ _).diff (stop_meas hτ _)

variable {N : ℕ}

noncomputable def G (P : StoppingProblem E N) (n : ℕ) (p : (ℕ → E) × ℕ∞) : ℝ :=
  match p.2 with
  | (m : ℕ) => (∑ k ∈ Finset.range m, P.c (n + k) (p.1 k)) + P.g (n + m) (p.1 m)
  | ⊤ => 0

lemma reward_eq (P : StoppingProblem E N) (n : ℕ) (τ : (ℕ → E) → ℕ∞) (w : ℕ → E) :
    P.rewardFrom n τ w = G P n (w, τ w) := by
  unfold StoppingProblem.rewardFrom G
  rcases τ w with _ | m <;> rfl

lemma reward_coe (P : StoppingProblem E N) (n : ℕ) (τ : (ℕ → E) → ℕ∞) (w : ℕ → E) (m : ℕ)
    (h : τ w = (m : ℕ∞)) :
    P.rewardFrom n τ w = (∑ k ∈ Finset.range m, P.c (n + k) (w k)) + P.g (n + m) (w m) := by
  rw [reward_eq, h]; rfl

lemma reward_meas (P : StoppingProblem E N) (n : ℕ) {τ : (ℕ → E) → ℕ∞} (hτ : IsStopTime τ) :
    Measurable (fun w => P.rewardFrom n τ w) := by
  have hG : Measurable (G P n) := by
    refine measurable_from_prod_countable_left (fun e => ?_)
    induction e using ENat.recTopCoe with
    | top => exact measurable_const
    | coe m =>
      show Measurable (fun w : ℕ → E =>
        (∑ k ∈ Finset.range m, P.c (n + k) (w k)) + P.g (n + m) (w m))
      refine Measurable.add (Finset.measurable_sum _ (fun k _ => ?_)) ?_
      · exact (P.c_meas _).comp (measurable_pi_apply k)
      · exact (P.g_meas _).comp (measurable_pi_apply m)
  have : (fun w => P.rewardFrom n τ w) = G P n ∘ (fun w => (w, τ w)) := by
    funext w; exact reward_eq P n τ w
  rw [this]
  exact hG.comp (measurable_id.prodMk (tau_meas hτ))

/-! ## decomposition under `cons` -/

lemma proj_cons_zero (x : E) (w : ℕ → E) : proj 0 (cons x w) = fun _ => x := by
  funext i; fin_cases i; rfl

lemma zero_dich {τ : (ℕ → E) → ℕ∞} (hτ : IsStopTime τ) (x : E) :
    (∀ w, τ (cons x w) = 0) ∨ (∀ w, τ (cons x w) ≠ 0) := by
  obtain ⟨T, _, he⟩ := stop_set hτ 0
  have key : ∀ w, (τ (cons x w) = 0 ↔ (fun _ => x : Fin 1 → E) ∈ T) := by
    intro w
    have : cons x w ∈ {w | τ w ≤ ((0 : ℕ) : ℕ∞)} ↔ cons x w ∈ proj 0 ⁻¹' T := by rw [he]
    simp only [mem_setOf_eq, mem_preimage, proj_cons_zero, Nat.cast_zero, nonpos_iff_eq_zero]
      at this
    exact this
  by_cases h : (fun _ => x : Fin 1 → E) ∈ T
  · left; intro w; exact (key w).2 h
  · right; intro w hw; exact h ((key w).1 hw)

noncomputable def tl (τ : (ℕ → E) → ℕ∞) (x : E) (w : ℕ → E) : ℕ∞ := τ (cons x w) - 1

lemma finCons_meas (x : E) (k : ℕ) :
    Measurable (fun f : Fin (k + 1) → E => (Fin.cons x f : Fin (k + 2) → E)) := by
  refine measurable_pi_lambda _ (fun i => ?_)
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]; exact measurable_const
  · simp only [Fin.cons_succ]; exact measurable_pi_apply j

lemma proj_cons (x : E) (w : ℕ → E) (k : ℕ) :
    proj (k + 1) (cons x w) = (Fin.cons x (proj k w) : Fin (k + 2) → E) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [Fin.cons_succ, proj, Fin.val_succ]; rfl

lemma tl_stop {τ : (ℕ → E) → ℕ∞} (hτ : IsStopTime τ) (x : E) : IsStopTime (tl τ x) := by
  intro k
  obtain ⟨T, hT, he⟩ := stop_set hτ (k + 1)
  have : {w | tl τ x w ≤ (k : ℕ∞)} = proj k ⁻¹' ((fun f => (Fin.cons x f : Fin (k + 2) → E)) ⁻¹' T) := by
    ext w
    simp only [mem_setOf_eq, tl, mem_preimage]
    rw [tsub_le_iff_right, ← proj_cons]
    have : cons x w ∈ {w | τ w ≤ ((k + 1 : ℕ) : ℕ∞)} ↔ cons x w ∈ proj (k + 1) ⁻¹' T := by rw [he]
    simpa using this
  rw [this]
  exact MeasurableSpace.measurableSet_comap.2 ⟨_, (finCons_meas x k) hT, rfl⟩

lemma tl_add (τ : (ℕ → E) → ℕ∞) (x : E) (w : ℕ → E) (h : τ (cons x w) ≠ 0) :
    τ (cons x w) = tl τ x w + 1 := by
  unfold tl
  rw [tsub_add_cancel_of_le]
  exact ENat.one_le_iff_ne_zero.2 h

lemma tl_le (τ : (ℕ → E) → ℕ∞) (x : E) (M : ℕ) (h : ∀ w, τ w ≤ ((M + 1 : ℕ) : ℕ∞)) (w : ℕ → E) :
    tl τ x w ≤ (M : ℕ∞) := by
  unfold tl
  rw [tsub_le_iff_right]; exact_mod_cast h (cons x w)

lemma rew_zero (P : StoppingProblem E N) (n : ℕ) (τ : (ℕ → E) → ℕ∞) (x : E) (w : ℕ → E)
    (h : τ (cons x w) = 0) : P.rewardFrom n τ (cons x w) = P.g n x := by
  rw [reward_coe P n τ _ 0 (by simpa using h)]; simp

lemma rew_succ (P : StoppingProblem E N) (n : ℕ) (τ : (ℕ → E) → ℕ∞) (x : E) (w : ℕ → E)
    (σ : (ℕ → E) → ℕ∞) (m : ℕ) (hσ : σ w = (m : ℕ∞)) (h : τ (cons x w) = σ w + 1) :
    P.rewardFrom n τ (cons x w) = P.c n x + P.rewardFrom (n + 1) σ w := by
  rw [reward_coe P (n + 1) σ w m hσ, reward_coe P n τ _ (m + 1) (by rw [h, hσ]; norm_cast)]
  rw [Finset.sum_range_succ']
  simp only [cons_succ, cons_zero, add_zero]
  rw [show n + (m + 1) = n + 1 + m by ring]
  have hs : ∑ k ∈ Finset.range m, P.c (n + (k + 1)) (w k) =
      ∑ k ∈ Finset.range m, P.c (n + 1 + k) (w k) :=
    Finset.sum_congr rfl (fun k _ => by rw [show n + (k + 1) = n + 1 + k by ring])
  rw [hs]; ring

/-! ## capped hitting times -/

lemma hitC_le_iff (S : ℕ → Set E) (M : ℕ) (w : ℕ → E) (k : ℕ) :
    hitTimeCapped S M w ≤ (k : ℕ∞) ↔ (∃ j ≤ k, w j ∈ S j) ∨ M ≤ k := by
  unfold hitTimeCapped
  rw [min_le_iff]
  have : sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | w k ∈ S k}) ≤ (k : ℕ∞) ↔ ∃ j ≤ k, w j ∈ S j := by
    constructor
    · intro h
      by_contra hne
      push Not at hne
      have : ((k + 1 : ℕ) : ℕ∞) ≤ sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | w k ∈ S k}) := by
        refine le_sInf ?_
        rintro _ ⟨j, hj, rfl⟩
        have : k < j := by
          by_contra hkn; push Not at hkn; exact hne j hkn hj
        show ((k + 1 : ℕ) : ℕ∞) ≤ (j : ℕ∞)
        exact_mod_cast this
      have := this.trans h
      have : k + 1 ≤ k := by exact_mod_cast this
      omega
    · rintro ⟨j, hj, hS⟩
      exact (sInf_le (show (j : ℕ∞) ∈ (fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | w k ∈ S k} from
        ⟨j, hS, rfl⟩)).trans (by exact_mod_cast hj)
  rw [this]; norm_cast

lemma hitC_le (S : ℕ → Set E) (M : ℕ) (w : ℕ → E) : hitTimeCapped S M w ≤ (M : ℕ∞) :=
  (hitC_le_iff S M w M).2 (Or.inr le_rfl)

lemma hitC_stop (S : ℕ → Set E) (hS : ∀ n, MeasurableSet (S n)) (M : ℕ) :
    IsStopTime (hitTimeCapped S M) := by
  intro k
  by_cases hMk : M ≤ k
  · have : {w : ℕ → E | hitTimeCapped S M w ≤ (k : ℕ∞)} = univ := by
      ext w; simp [hitC_le_iff, hMk]
    rw [this]; exact MeasurableSet.univ
  · have : {w : ℕ → E | hitTimeCapped S M w ≤ (k : ℕ∞)}
        = (fun w : ℕ → E => fun i : Fin (k + 1) => w i) ⁻¹' (⋃ i : Fin (k + 1), {f | f i ∈ S i}) := by
      ext w
      simp only [Set.mem_setOf_eq, hitC_le_iff, hMk, or_false, Set.mem_preimage, Set.mem_iUnion]
      constructor
      · rintro ⟨j, hj, h⟩; exact ⟨⟨j, by omega⟩, h⟩
      · rintro ⟨i, h⟩; exact ⟨i, by omega, h⟩
    rw [this]
    refine MeasurableSet.preimage ?_ (comap_measurable _)
    exact MeasurableSet.iUnion (fun i => (measurable_pi_apply i) (hS i))

lemma enat_eq_of_le_iff {a b : ℕ∞} (h : ∀ k : ℕ, a ≤ k ↔ b ≤ k) : a = b := by
  induction a using ENat.recTopCoe with
  | top =>
    induction b using ENat.recTopCoe with
    | top => rfl
    | coe m => exact absurd ((h m).2 le_rfl) (by simp)
  | coe n =>
    induction b using ENat.recTopCoe with
    | top => exact absurd ((h n).1 le_rfl) (by simp)
    | coe m =>
      have h1 := (h n).1 le_rfl
      have h2 := (h m).2 le_rfl
      have : m ≤ n := by exact_mod_cast h1
      have : n ≤ m := by exact_mod_cast h2
      congr 1; omega

lemma hitC_cons_mem (S : ℕ → Set E) (M : ℕ) (x : E) (w : ℕ → E) (hx : x ∈ S 0) :
    hitTimeCapped S M (cons x w) = 0 := by
  have := (hitC_le_iff S M (cons x w) 0).2 (Or.inl ⟨0, le_rfl, hx⟩)
  simpa using this

lemma hitC_cons_not (S : ℕ → Set E) (M : ℕ) (x : E) (w : ℕ → E) (hx : x ∉ S 0) :
    hitTimeCapped S (M + 1) (cons x w) = hitTimeCapped (fun k => S (k + 1)) M w + 1 := by
  apply enat_eq_of_le_iff
  intro k
  rw [hitC_le_iff]
  cases k with
  | zero =>
    simp only [nonpos_iff_eq_zero, exists_eq_left, cons_zero, hx, false_or]
    constructor
    · intro h; omega
    · intro h
      have : (1 : ℕ∞) ≤ 0 := le_trans le_add_self (by exact_mod_cast h)
      simp at this
  | succ k =>
    rw [show ((k + 1 : ℕ) : ℕ∞) = (k : ℕ∞) + 1 by norm_cast,
      ENat.add_le_add_iff_right ENat.one_ne_top, hitC_le_iff]
    constructor
    · rintro (⟨j, hj, hjS⟩ | h)
      · cases j with
        | zero => exact absurd hjS hx
        | succ j => exact Or.inl ⟨j, by omega, hjS⟩
      · exact Or.inr (by omega)
    · rintro (⟨j, hj, hjS⟩ | h)
      · exact Or.inl ⟨j + 1, by omega, hjS⟩
      · exact Or.inr (by omega)

end OSAux

open MeasureTheory Filter Topology Set
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace OSAux
open MDPFinance.OptimalStopping

variable {E : Type*} [MeasurableSpace E] {N : ℕ}

noncomputable def J (P : StoppingProblem E N) (n : ℕ) : E → EReal :=
  if N ≤ n then fun x => (P.g n x : EReal) else P.T n (J P (n + 1))
termination_by N - n

lemma J_ge (P : StoppingProblem E N) (n : ℕ) (h : N ≤ n) : J P n = fun x => (P.g n x : EReal) := by
  rw [J, if_pos h]

lemma J_lt (P : StoppingProblem E N) (n : ℕ) (h : n < N) : J P n = P.T n (J P (n + 1)) := by
  rw [J, if_neg (by omega)]

lemma meas_toENNReal : Measurable EReal.toENNReal :=
  (show Monotone EReal.toENNReal from fun _ _ h => EReal.toENNReal_le_toENNReal h).measurable

lemma ereal_int_meas (P : StoppingProblem E N) (n : ℕ) {v : E → EReal} (hv : Measurable v) :
    Measurable (fun x => erealIntegral (P.QX n x) v) := by
  unfold erealIntegral
  have h1 : Measurable (fun x => ∫⁻ a, (v a ⊔ 0).toENNReal ∂(P.QX n x)) :=
    (Measure.measurable_lintegral (meas_toENNReal.comp (hv.sup measurable_const))).comp (P.QX_meas n)
  have h2 : Measurable (fun x => ∫⁻ a, ((-v a) ⊔ 0).toENNReal ∂(P.QX n x)) :=
    (Measure.measurable_lintegral (meas_toENNReal.comp
      (((continuous_neg (G := EReal)).measurable.comp hv).sup measurable_const))).comp (P.QX_meas n)
  exact (measurable_coe_ennreal_ereal.comp h1).add
    ((continuous_neg (G := EReal)).measurable.comp (measurable_coe_ennreal_ereal.comp h2))

lemma T_meas (P : StoppingProblem E N) (n : ℕ) {v : E → EReal} (hv : Measurable v) :
    Measurable (P.T n v) := by
  unfold StoppingProblem.T
  refine Measurable.max ?_ ?_
  · exact measurable_coe_real_ereal.comp (P.g_meas n)
  · exact (measurable_coe_real_ereal.comp (P.c_meas n)).add (ereal_int_meas P n hv)

lemma J_meas (P : StoppingProblem E N) : ∀ d n, N - n = d → Measurable (J P n) := by
  intro d
  induction d with
  | zero =>
    intro n hn
    rw [J_ge P n (by omega)]
    exact measurable_coe_real_ereal.comp (P.g_meas n)
  | succ d ih =>
    intro n hn
    rw [J_lt P n (by omega)]
    exact T_meas P n (ih (n + 1) (by omega))

def Sset (P : StoppingProblem E N) (n : ℕ) : Set E := {x | J P n x = (P.g n x : EReal)}

lemma Sset_meas (P : StoppingProblem E N) (n : ℕ) : MeasurableSet (Sset P n) :=
  measurableSet_eq_fun (J_meas P _ n rfl) (measurable_coe_real_ereal.comp (P.g_meas n))

noncomputable def hstar (P : StoppingProblem E N) (n : ℕ) : (ℕ → E) → ℕ∞ :=
  hitTimeCapped (fun k => Sset P (n + k)) (N - n)

lemma hstar_stop (P : StoppingProblem E N) (n : ℕ) : IsStopTime (hstar P n) :=
  hitC_stop _ (fun k => Sset_meas P (n + k)) _

variable {P : StoppingProblem E N} {Pr : ℕ → E → Measure (ℕ → E)}

/-- EReward when the stopping time vanishes on all paths starting at `x`. -/
lemma erew_zero (hPr : P.IsPathLaw Pr) (n : ℕ) (x : E) {τ : (ℕ → E) → ℕ∞} (hτ : IsStopTime τ)
    (h0 : ∀ w, τ (cons x w) = 0) : P.EReward Pr n τ x = (P.g n x : EReal) := by
  haveI := P.QX_prob n x
  have hR := reward_meas P n hτ
  have hc : ∀ w, P.rewardFrom n τ (cons x w) = P.g n x := fun w => rew_zero P n τ x w (h0 w)
  have hfin : ∫⁻ w, ENNReal.ofReal (P.rewardFrom n τ w) ∂(Pr n x) ≠ ⊤ := by
    rw [markov_lintegral hPr n x hR.ennreal_ofReal]
    simp_rw [hc]
    have : ∀ y, ∫⁻ w, ENNReal.ofReal (P.g n x) ∂(Pr (n + 1) y) = ENNReal.ofReal (P.g n x) := by
      intro y; haveI := hPr.1 (n + 1) y; simp
    simp_rw [this]; simp
  unfold StoppingProblem.EReward
  rw [ereal_markov hPr n x hR hfin]
  simp_rw [hc]
  have : ∀ y, erealIntegral (Pr (n + 1) y) (fun _ => (P.g n x : EReal)) = (P.g n x : EReal) := by
    intro y; haveI := hPr.1 (n + 1) y; exact ereal_const _ _
  simp_rw [this]
  exact ereal_const _ _

lemma erew_le_pos (n : ℕ) (τ : (ℕ → E) → ℕ∞) (x : E) :
    P.EReward Pr n τ x ≤ ((∫⁻ w, ENNReal.ofReal (P.rewardFrom n τ w) ∂(Pr n x) : ℝ≥0∞) : EReal) := by
  unfold StoppingProblem.EReward
  rw [ereal_real]
  calc _ ≤ ((∫⁻ w, ENNReal.ofReal (P.rewardFrom n τ w) ∂(Pr n x) : ℝ≥0∞) : EReal) + 0 :=
        add_le_add le_rfl (by have := EReal.coe_ennreal_nonneg (∫⁻ w, ENNReal.ofReal (-P.rewardFrom n τ w) ∂(Pr n x)); exact EReal.neg_le_neg_iff.2 this |>.trans (by simp))
    _ = _ := add_zero _

lemma bn_fin (hBN : P.AssumptionBN Pr) (n : ℕ) (hn : n ≤ N) (x : E) {τ : (ℕ → E) → ℕ∞}
    (hτ : IsStopTime τ) (hb : ∀ w, τ w ≤ ((N - n : ℕ) : ℕ∞)) :
    ∫⁻ w, ENNReal.ofReal (P.rewardFrom n τ w) ∂(Pr n x) ≠ ⊤ := by
  obtain ⟨C, hC, hle⟩ := hBN n hn x
  refine ne_top_of_le_ne_top hC.ne (le_trans (lintegral_mono (fun w => ?_)) (hle τ hτ hb))
  apply ENNReal.ofReal_le_ofReal
  have hfin : τ w ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) (hb w)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hfin
  rw [reward_coe P n τ w m hm.symm, ← hm, ENat.toNat_natCast]
  gcongr with k _
  · exact le_max_left _ _
  · exact le_max_left _ _

end OSAux

open MeasureTheory Filter Topology Set
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace OSAux
open MDPFinance.OptimalStopping

variable {E : Type*} [MeasurableSpace E] {N : ℕ}
variable {P : StoppingProblem E N} {Pr : ℕ → E → Measure (ℕ → E)}

lemma J_ge_g (P : StoppingProblem E N) (n : ℕ) (x : E) : (P.g n x : EReal) ≤ J P n x := by
  by_cases h : N ≤ n
  · rw [J_ge P n h]
  · rw [J_lt P n (by omega)]; exact le_max_left _ _

lemma fin_of (n : ℕ) (x : E) {τ : (ℕ → E) → ℕ∞} (hb : ∀ w, τ w ≤ ((N - n : ℕ) : ℕ∞))
    (w : ℕ → E) : ∃ m : ℕ, τ w = m :=
  ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top _) (hb w)) |>.imp
    (fun _ h => h.symm)

theorem main_ind (hPr : P.IsPathLaw Pr) (hBN : P.AssumptionBN Pr) : ∀ d n, N - n = d →
    (∀ x τ, IsStopTime τ → (∀ w, τ w ≤ ((N - n : ℕ) : ℕ∞)) → P.EReward Pr n τ x ≤ J P n x) ∧
    (∀ x, P.EReward Pr n (hstar P n) x = J P n x) := by
  intro d
  induction d with
  | zero =>
    intro n hn
    have hz : ∀ τ : (ℕ → E) → ℕ∞, (∀ w, τ w ≤ ((N - n : ℕ) : ℕ∞)) → ∀ w, τ w = 0 := by
      intro τ hb w; have := hb w; rw [hn] at this; simpa using this
    refine ⟨fun x τ hτ hb => ?_, fun x => ?_⟩
    · rw [erew_zero hPr n x hτ (fun w => hz τ hb _), J_ge P n (by omega)]
    · rw [erew_zero hPr n x (hstar_stop P n) (fun w => hz _ (hitC_le _ _) _), J_ge P n (by omega)]
  | succ d ih =>
    intro n hn
    have hnN : n < N := by omega
    obtain ⟨ih1, ih2⟩ := ih (n + 1) (by omega)
    have hNn : N - n = (N - (n + 1)) + 1 := by omega
    -- finiteness of J (n+1)
    have hJtop : ∀ y, J P (n + 1) y ≠ ⊤ := by
      intro y hy
      have h1 := ih2 y
      have h2 := erew_le_pos (P := P) (Pr := Pr) (n + 1) (hstar P (n + 1)) y
      have h3 := bn_fin hBN (n + 1) (by omega) y (hstar_stop P (n + 1)) (fun w => hitC_le _ _ _)
      rw [h1, hy] at h2
      exact h3 (by simpa using h2)
    have hJbot : ∀ y, J P (n + 1) y ≠ ⊥ := fun y => ne_bot_of_le_ne_bot (EReal.coe_ne_bot _)
      (J_ge_g P (n + 1) y)
    set j : E → ℝ := fun y => (J P (n + 1) y).toReal with hj
    have hJj : ∀ y, J P (n + 1) y = (j y : EReal) := fun y => (EReal.coe_toReal (hJtop y) (hJbot y)).symm
    have hjm : Measurable j := measurable_ereal_toReal.comp (J_meas P _ (n + 1) rfl)
    have hJn : ∀ x, J P n x = max (P.g n x : EReal)
        ((P.c n x : EReal) + erealIntegral (P.QX n x) (J P (n + 1))) := by
      intro x; rw [J_lt P n hnN]; rfl
    have hshift : ∀ x, erealIntegral (P.QX n x) (fun y => ((P.c n x + j y : ℝ) : EReal)) =
        (P.c n x : EReal) + erealIntegral (P.QX n x) (J P (n + 1)) := by
      intro x
      haveI := P.QX_prob n x
      rw [ereal_shift _ _ _ hjm]
      congr 2; funext y; exact (hJj y).symm
    -- general one-step formula
    have step : ∀ x (τ σ : (ℕ → E) → ℕ∞), IsStopTime τ → (∀ w, τ w ≤ ((N - n : ℕ) : ℕ∞)) →
        IsStopTime σ → (∀ w, σ w ≤ ((N - (n + 1) : ℕ) : ℕ∞)) →
        (∀ w, τ (cons x w) = σ w + 1) →
        P.EReward Pr n τ x = erealIntegral (P.QX n x)
          (fun y => (P.c n x : EReal) + P.EReward Pr (n + 1) σ y) := by
      intro x τ σ hτ hb hσ hσb hrel
      unfold StoppingProblem.EReward
      rw [ereal_markov hPr n x (reward_meas P n hτ) (bn_fin hBN n hnN.le x hτ hb)]
      congr 1; funext y
      haveI := hPr.1 (n + 1) y
      have : (fun w => (P.rewardFrom n τ (cons x w) : EReal)) =
          fun w => ((P.c n x + P.rewardFrom (n + 1) σ w : ℝ) : EReal) := by
        funext w
        obtain ⟨m, hm⟩ := fin_of (n + 1) x hσb w
        rw [rew_succ P n τ x w σ m hm (hrel w)]
      rw [this, ereal_shift _ _ _ (reward_meas P (n + 1) hσ)]
    refine ⟨fun x τ hτ hb => ?_, fun x => ?_⟩
    · rcases zero_dich hτ x with h0 | h1
      · rw [erew_zero hPr n x hτ h0]; exact J_ge_g P n x
      · have hσ := tl_stop hτ x
        have hσb : ∀ w, tl τ x w ≤ ((N - (n + 1) : ℕ) : ℕ∞) :=
          tl_le τ x _ (fun w => by rw [← hNn]; exact hb w)
        rw [step x τ (tl τ x) hτ hb hσ hσb (fun w => tl_add τ x w (h1 w)), hJn x]
        refine le_trans ?_ (le_max_right _ _)
        rw [← hshift x]
        refine ereal_mono _ (fun y => ?_)
        rw [EReal.coe_add, ← hJj y]
        exact add_le_add le_rfl (ih1 y _ hσ hσb)
    · by_cases hx : x ∈ Sset P n
      · rw [erew_zero hPr n x (hstar_stop P n) (fun w => hitC_cons_mem _ _ x w (by simpa using hx))]
        exact hx.symm
      · have hrel : ∀ w, hstar P n (cons x w) = hstar P (n + 1) w + 1 := by
          intro w
          unfold hstar
          rw [hNn, hitC_cons_not _ _ x w (by simpa using hx)]
          congr 2
          funext k; congr 1; ring
        rw [step x _ _ (hstar_stop P n) (fun w => hitC_le _ _ _) (hstar_stop P (n + 1))
          (fun w => hitC_le _ _ _) hrel]
        have : (fun y => (P.c n x : EReal) + P.EReward Pr (n + 1) (hstar P (n + 1)) y) =
            fun y => ((P.c n x + j y : ℝ) : EReal) := by
          funext y; rw [ih2 y, hJj y, EReal.coe_add]
        rw [this, hshift x, hJn x]
        have hne : J P n x ≠ (P.g n x : EReal) := hx
        rw [hJn x] at hne
        rcases max_choice (P.g n x : EReal) ((P.c n x : EReal) + erealIntegral (P.QX n x) (J P (n + 1))) with h | h
        · exact absurd h hne
        · exact h.symm

end OSAux

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace OSAux
open MDPFinance.OptimalStopping

theorem final {E : Type*} [MeasurableSpace E] {N : ℕ} (P : StoppingProblem E N)
    (Pr : ℕ → E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hBN : P.AssumptionBN Pr) :
    ((∀ x, P.Vn Pr N x = (P.g N x : EReal)) ∧
      ∀ n : ℕ, n < N → ∀ x, P.Vn Pr n x = P.T n (P.Vn Pr (n + 1)) x) ∧
    (IsStopTime (hitTimeCapped (fun n => {x | P.Vn Pr n x = (P.g n x : EReal)}) N) ∧
      (∀ w : ℕ → E, hitTimeCapped (fun n => {x | P.Vn Pr n x = (P.g n x : EReal)}) N w ≤ (N : ℕ∞)) ∧
      ∀ x : E, P.EReward Pr 0 (hitTimeCapped (fun n => {x | P.Vn Pr n x = (P.g n x : EReal)}) N) x
        = P.Vn Pr 0 x) := by
  have hV : ∀ n, P.Vn Pr n = J P n := by
    intro n; funext x
    obtain ⟨h1, h2⟩ := main_ind hPr hBN (N - n) n rfl
    apply le_antisymm
    · exact iSup₂_le (fun τ h => h1 x τ h.1 h.2)
    · exact (h2 x).symm.le.trans
        (le_iSup₂_of_le (f := fun τ (_ : IsStopTime τ ∧ ∀ w, τ w ≤ ((N - n : ℕ) : ℕ∞)) =>
          P.EReward Pr n τ x) (hstar P n) ⟨hstar_stop P n, fun w => hitC_le _ _ _⟩ le_rfl)
  have hS : (fun n => {x | P.Vn Pr n x = (P.g n x : EReal)}) = fun n => Sset P n := by
    funext n; ext x; simp only [hV]; rfl
  rw [hS]
  refine ⟨⟨fun x => ?_, fun n hn x => ?_⟩, hitC_stop _ (Sset_meas P) N, fun w => hitC_le _ _ _,
    fun x => ?_⟩
  · rw [hV, J_ge P N le_rfl]
  · rw [hV, hV, J_lt P n hn]
  · have : hitTimeCapped (fun n => Sset P n) N = hstar P 0 := by
      unfold hstar; simp
    rw [this, hV, (main_ind hPr hBN (N - 0) 0 rfl).2 x]

end OSAux

open MeasureTheory MDPFinance.OptimalStopping

theorem solution {E : Type*} [MeasurableSpace E] {N : ℕ} (P : StoppingProblem E N)
    (Pr : ℕ → E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hBN : P.AssumptionBN Pr) :
    ((∀ x, P.Vn Pr N x = (P.g N x : EReal)) ∧
      ∀ n : ℕ, n < N → ∀ x, P.Vn Pr n x = P.T n (P.Vn Pr (n + 1)) x) ∧
    (IsStopTime (hitTimeCapped (fun n => {x | P.Vn Pr n x = (P.g n x : EReal)}) N) ∧
      (∀ w : ℕ → E, hitTimeCapped (fun n => {x | P.Vn Pr n x = (P.g n x : EReal)}) N w ≤ (N : ℕ∞)) ∧
      ∀ x : E, P.EReward Pr 0 (hitTimeCapped (fun n => {x | P.Vn Pr n x = (P.g n x : EReal)}) N) x
        = P.Vn Pr 0 x) :=
  OSAux.final P Pr hPr hBN
