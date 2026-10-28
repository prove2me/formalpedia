-- Prove2me | solution 1 for OAI.PlanarFPP.exponential_source_connector_test
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:47:39.942301+00:00
-- url     : https://prove2.me/submissions/66ffec10-82ba-467f-9539-19a8e5026a96

import Mathlib
import Definitions.Def_PlanarFirstPassage
import Definitions.Def_OAISPf002

section
-- module Solutions.OAIS_PlanarFPP.Compat
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.rateOneProbability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_Paths
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

theorem pathCost_append (τ : Edge → ℝ) (p : Vertex) (ds es : List Step) :
    pathCost τ p (ds ++ es) =
      pathCost τ p ds + pathCost τ (p + displacement ds) es := by
  induction ds generalizing p with
  | nil => simp [pathCost]
  | cons d ds ih => simp [pathCost, ih, add_assoc]

theorem pathCost_nonneg {τ : Edge → ℝ} (hτ : ∀ e, 0 ≤ τ e)
    (p : Vertex) (ds : List Step) : 0 ≤ pathCost τ p ds := by
  induction ds generalizing p with
  | nil => exact le_refl 0
  | cons d ds ih => exact add_nonneg (hτ _) (ih _)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_PassageTime
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

theorem displacement_horizontal (n : ℤ) : displacement (horizontal n) = (n, 0) := by
  by_cases hn : 0 ≤ n
  · simp [horizontal, hn, displacement, Step.delta,
      Int.toNat_of_nonneg hn]
  · have hn' : 0 ≤ -n := by omega
    simp [horizontal, hn, displacement, Step.delta,
      Int.toNat_of_nonneg hn']

theorem displacement_vertical (n : ℤ) : displacement (vertical n) = (0, n) := by
  by_cases hn : 0 ≤ n
  · simp [vertical, hn, displacement, Step.delta,
      Int.toNat_of_nonneg hn]
  · have hn' : 0 ≤ -n := by omega
    simp [vertical, hn, displacement, Step.delta,
      Int.toNat_of_nonneg hn']

theorem exists_path (p q : Vertex) : ∃ ds, p + displacement ds = q := by
  refine ⟨horizontal (q.1 - p.1) ++ vertical (q.2 - p.2), ?_⟩
  rw [displacement_append, displacement_horizontal, displacement_vertical]
  ext <;> simp

theorem path_costs_nonempty (τ : Edge → ℝ) (p q : Vertex) :
    {t | ∃ ds : List Step, p + displacement ds = q ∧ pathCost τ p ds = t}.Nonempty := by
  obtain ⟨ds, hds⟩ := exists_path p q
  exact ⟨pathCost τ p ds, ds, hds, rfl⟩

theorem path_costs_bddBelow (τ : Edge → ℝ) (hτ : ∀ e, 0 ≤ τ e) (p q : Vertex) :
    BddBelow {t | ∃ ds : List Step, p + displacement ds = q ∧ pathCost τ p ds = t} := by
  refine ⟨0, ?_⟩
  rintro t ⟨ds, _, rfl⟩
  exact pathCost_nonneg hτ p ds

theorem passageTime_le_cost (τ : Edge → ℝ) (hτ : ∀ e, 0 ≤ τ e)
    (p q : Vertex) (ds : List Step) (hend : p + displacement ds = q) :
    passageTime τ p q ≤ pathCost τ p ds :=
  csInf_le (path_costs_bddBelow τ hτ p q) ⟨ds, hend, rfl⟩

theorem exists_near_optimal_path (τ : Edge → ℝ) (p q : Vertex)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ds : List Step, p + displacement ds = q ∧
      pathCost τ p ds < passageTime τ p q + ε := by
  obtain ⟨t, ⟨ds, hend, hcost⟩, ht⟩ :=
    exists_lt_of_csInf_lt (path_costs_nonempty τ p q)
      (show sInf {t | ∃ ds : List Step, p + displacement ds = q ∧ pathCost τ p ds = t}
        < passageTime τ p q + ε by change passageTime τ p q < _; linarith)
  exact ⟨ds, hend, by simpa [hcost] using ht⟩

theorem passageTime_triangle (τ : Edge → ℝ) (hτ : ∀ e, 0 ≤ τ e) (p q r : Vertex) :
    passageTime τ p r ≤ passageTime τ p q + passageTime τ q r := by
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨ds, hd, hdc⟩ := exists_near_optimal_path τ p q (ε / 2) (by linarith)
  obtain ⟨es, he, hec⟩ := exists_near_optimal_path τ q r (ε / 2) (by linarith)
  have hfinish : p + displacement (ds ++ es) = r := by
    rw [displacement_append, ← add_assoc, hd, he]
  have hc := passageTime_le_cost τ hτ p r (ds ++ es) hfinish
  rw [pathCost_append, hd] at hc
  linarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ProbabilityFoundations
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set Filter

theorem rateOne_ae_positive : ∀ᵐ x ∂expMeasure 1, 0 < x := by
  have hc : (expMeasure 1 (Iic 0)).toReal = 0 := by
    rw [← measureReal_def, ← cdf_eq_real]
    simp [cdf_expMeasure_eq (r := 1) (by norm_num)]
  have hz : expMeasure 1 (Iic 0) = 0 :=
    (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.zero_ne_top).mp
      (by simpa using hc)
  simpa only [ae_iff, not_lt, Iic] using hz

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem ExponentialEnvironment.ae_positive (h : ExponentialEnvironment P τ) :
    ∀ᵐ ω ∂P, ∀ e, 0 < τ e ω := by
  rw [ae_all_iff]
  intro e
  have hp : ∀ᵐ x ∂Measure.map (τ e) P, 0 < x := by
    rw [h.marginal e]
    exact rateOne_ae_positive
  exact (ae_map_iff (h.measurable e).aemeasurable measurableSet_Ioi).mp hp

theorem measurable_pathCost (hτ : ∀ e, Measurable (τ e))
    (p : Vertex) (ds : List Step) :
    Measurable (fun ω => pathCost (fun e => τ e ω) p ds) := by
  induction ds generalizing p with
  | nil => exact measurable_const
  | cons d ds ih => exact (hτ _).add (ih _)

theorem measurable_passageTime (hτ : ∀ e, Measurable (τ e)) (p q : Vertex) :
    Measurable (fun ω => passageTime (fun e => τ e ω) p q) := by
  have hm := Measurable.sInf (Set.to_countable {ds : List Step |
    p + displacement ds = q}) (fun ds _ => measurable_pathCost hτ p ds)
  convert hm using 1
  funext ω
  unfold passageTime
  congr 1

theorem measurableSet_bounded_path_event (hτ : ∀ e, Measurable (τ e))
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    MeasurableSet {ω | ∃ p ds, family p ds ∧
      pathCost (fun e => τ e ω) p ds ≤ bound p ds} := by
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro p
  apply MeasurableSet.iUnion
  intro ds
  by_cases hf : family p ds
  · simpa only [hf, true_and] using
      measurableSet_le (measurable_pathCost hτ p ds) measurable_const
  · simp [hf]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_Translation
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set

theorem shiftEdge_injective (a : Vertex) : Function.Injective (shiftEdge a) := by
  intro e f h
  simpa [shiftEdge, Prod.ext_iff] using h

theorem step_edge_translate (a p : Vertex) (d : Step) :
    d.edge (a+p) = shiftEdge a (d.edge p) := by
  cases d <;> simp [Step.edge, shiftEdge, add_assoc]

theorem pathCost_translate (w : Edge → ℝ) (a p : Vertex) (ds : List Step) :
    pathCost (fun e => w (shiftEdge a e)) p ds = pathCost w (a+p) ds := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp [pathCost, step_edge_translate, ih, add_assoc]

theorem passageTime_translate (w : Edge → ℝ) (a p q : Vertex) :
    passageTime (fun e => w (shiftEdge a e)) p q = passageTime w (a+p) (a+q) := by
  unfold passageTime
  congr 1
  ext t
  simp only [mem_ofPred_eq, pathCost_translate, add_assoc, add_left_cancel_iff]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem ExponentialEnvironment.translate (h : ExponentialEnvironment P τ) (a : Vertex) :
    ExponentialEnvironment P (fun e => τ (shiftEdge a e)) where
  probability := h.probability
  measurable := fun _ => h.measurable _
  independent := h.independent.precomp (shiftEdge_injective a)
  marginal := fun _ => h.marginal _

theorem ExponentialEnvironment.jointLaw (h : ExponentialEnvironment P τ) :
    Measure.map (fun ω e => τ e ω) P = exponentialProductLaw := by
  rw [h.independent.map_fun_eq_infinitePi_map h.measurable]
  simp only [h.marginal, exponentialProductLaw]

theorem translated_event_probability (h : ExponentialEnvironment P τ) (a : Vertex)
    (A : Set (Edge → ℝ)) (hA : MeasurableSet A) :
    P {ω | (fun e => τ (shiftEdge a e) ω) ∈ A} =
      P {ω | (fun e => τ e ω) ∈ A} := by
  have h1 := (h.translate a).jointLaw
  have h2 := h.jointLaw
  have he := congrArg (fun Q : Measure (Edge → ℝ) => Q A) (h1.trans h2.symm)
  rw [Measure.map_apply (Measurable.of_eval (fun e => h.measurable _)) hA,
    Measure.map_apply (Measurable.of_eval h.measurable) hA] at he
  exact he

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_PositiveMoment
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

lemma positive_weighted_density (x : ℝ) :
    exponentialPDF 1 x * ENNReal.ofReal (exp (x / 2)) =
      ENNReal.ofReal (2 : ℝ) * exponentialPDF (1 / 2) x := by
  by_cases hx : 0 ≤ x
  · rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hx]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    simp only [one_mul]
    calc
      exp (-x) * exp (x / 2) = exp (-(1 / 2 * x)) := by
        rw [← exp_add]
        congr 1
        ring
      _ = 2 * (1 / 2 * exp (-(1 / 2 * x))) := by ring
  · rw [exponentialPDF_of_neg (lt_of_not_ge hx),
      exponentialPDF_of_neg (lt_of_not_ge hx)]
    simp

theorem exponential_moment_half :
    (∫⁻ x, ENNReal.ofReal (exp (x / 2)) ∂expMeasure 1) = 2 := by
  change (∫⁻ x, ENNReal.ofReal (exp (x / 2)) ∂volume.withDensity (exponentialPDF 1)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume (by
    unfold exponentialPDF; fun_prop) (by fun_prop)]
  simp only [Pi.mul_apply, positive_weighted_density]
  rw [lintegral_const_mul _ (by unfold exponentialPDF; fun_prop),
    lintegral_exponentialPDF_eq_one (by norm_num : (0 : ℝ) < 1 / 2), mul_one]
  norm_num

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem edge_set_positive_moment (h : ExponentialEnvironment P τ) (s : Finset Edge) :
    (∫⁻ ω : Ω, ∏ e ∈ s, ENNReal.ofReal (exp (τ e ω / 2)) ∂P) =
      2 ^ s.card := by
  have hind : iIndepFun (fun e (ω : Ω) => ENNReal.ofReal (exp (τ e ω / 2))) P :=
    h.independent.comp (fun _ (x : ℝ) => ENNReal.ofReal (exp (x / 2)))
      (by intro i; fun_prop)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun s _ hind (fun i => ((h.measurable i).div_const 2).exp.ennreal_ofReal)]
  have he : ∀ e : Edge, (∫⁻ ω : Ω, ENNReal.ofReal (exp (τ e ω / 2))
      ∂P) = 2 := by
    intro e
    rw [← lintegral_map (by fun_prop : Measurable (fun x : ℝ =>
      ENNReal.ofReal (exp (x / 2)))) (h.measurable e), h.marginal]
    exact exponential_moment_half
  simp only [he, prod_const]

omit [MeasurableSpace Ω] in
lemma positive_exp_sum (τ : Edge → Ω → ℝ) (s : Finset Edge) (ω : Ω) :
    ENNReal.ofReal (exp ((∑ e ∈ s, τ e ω) / 2)) =
      ∏ e ∈ s, ENNReal.ofReal (exp (τ e ω / 2)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s he ih =>
    rw [sum_insert he, prod_insert he, add_div, exp_add,
      ENNReal.ofReal_mul (exp_pos _).le, ih]

theorem costly_edge_set_probability (h : ExponentialEnvironment P τ) (s : Finset Edge) (t : ℝ) :
    P {ω : Ω | t ≤ ∑ e ∈ s, τ e ω} ≤
      2 ^ s.card / ENNReal.ofReal (exp (t / 2)) := by
  have hm := meas_ge_le_lintegral_div (μ := P)
    (f := fun ω : Ω => ENNReal.ofReal (exp ((∑ e ∈ s, τ e ω) / 2)))
    (((s.measurable_sum (fun i _ => h.measurable i)).div_const 2).exp.ennreal_ofReal.aemeasurable) (ε := ENNReal.ofReal (exp (t / 2)))
    (by positivity) ENNReal.ofReal_ne_top
  have hs : {ω : Ω | ENNReal.ofReal (exp (t / 2)) ≤
      ENNReal.ofReal (exp ((∑ e ∈ s, τ e ω) / 2))} =
      {ω : Ω | t ≤ ∑ e ∈ s, τ e ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, ENNReal.ofReal_le_ofReal_iff (exp_pos _).le,
      exp_le_exp]
    constructor <;> intro h <;> linarith
  rw [hs] at hm
  simp_rw [positive_exp_sum] at hm
  rw [edge_set_positive_moment h] at hm
  exact hm

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_Reversal
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

theorem pathCost_reverse (τ : Edge → ℝ) (p : Vertex) (ds : List Step) :
    pathCost τ (p + displacement ds) (reverseSteps ds) = pathCost τ p ds := by
  induction ds generalizing p with
  | nil => simp [pathCost]
  | cons d ds ih =>
    rw [reverseSteps_cons, displacement_cons, pathCost_append]
    have ha : p + (d.delta + displacement ds) = (p + d.delta) + displacement ds :=
      (add_assoc _ _ _).symm
    rw [ha, ih, displacement_reverseSteps]
    have hb : p + d.delta + displacement ds + -displacement ds = p + d.delta := by
      simp [add_assoc]
    rw [hb]
    simp [pathCost, Step.edge_reverse, add_comm]

theorem passageTime_symm (τ : Edge → ℝ) (hτ : ∀ e, 0 ≤ τ e) (p q : Vertex) :
    passageTime τ p q = passageTime τ q p := by
  have hle : ∀ p q, passageTime τ p q ≤ passageTime τ q p := by
    intro p q
    apply le_csInf (path_costs_nonempty τ q p)
    rintro t ⟨ds, hend, rfl⟩
    have hfinish : p + displacement (reverseSteps ds) = q := by
      rw [displacement_reverseSteps, ← hend]
      simp [add_assoc]
    have hc := passageTime_le_cost τ hτ p q (reverseSteps ds) hfinish
    rw [← hend, pathCost_reverse] at hc
    simpa only [hend] using hc
  exact le_antisymm (hle p q) (hle q p)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_CoordinateTails
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

theorem straightEdge_injective (p : Vertex) (d : Step) :
    Function.Injective (straightEdge p d) := by
  intro i j h
  cases d <;> simp [straightEdge, Step.edge, Step.delta, Prod.ext_iff] at h <;> omega

theorem pathCost_replicate (w : Edge → ℝ) (p : Vertex) (d : Step) (n : ℕ) :
    pathCost w p (List.replicate n d) =
      ∑ i ∈ range n, w (straightEdge p d i) := by
  induction n generalizing p with
  | zero => simp [pathCost]
  | succ n ih =>
    rw [List.replicate_succ, pathCost, ih, sum_range_succ']
    simp [straightEdge, Nat.cast_add, add_smul, add_assoc, add_comm]

theorem pathCost_replicate_edgeSet (w : Edge → ℝ) (p : Vertex) (d : Step) (n : ℕ) :
    pathCost w p (List.replicate n d) =
      ∑ e ∈ (range n).image (straightEdge p d), w e := by
  rw [sum_image (fun i _ j _ hij => straightEdge_injective p d hij)]
  exact pathCost_replicate w p d n

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem costly_straight_probability (h : ExponentialEnvironment P τ)
    (p : Vertex) (d : Step) (n : ℕ) (t : ℝ) :
    P {ω | t ≤ pathCost (fun e => τ e ω) p (List.replicate n d)} ≤
      2 ^ n / ENNReal.ofReal (Real.exp (t / 2)) := by
  simp only [pathCost_replicate_edgeSet]
  have ht := costly_edge_set_probability h ((range n).image (straightEdge p d)) t
  simpa only [card_image_of_injective _ (straightEdge_injective p d), card_range] using ht

theorem costly_straight_probability_real (h : ExponentialEnvironment P τ)
    (p : Vertex) (d : Step) (n : ℕ) (t : ℝ) :
    P.real {ω | t ≤ pathCost (fun e => τ e ω) p (List.replicate n d)} ≤
      (2 : ℝ) ^ n * Real.exp (-t / 2) := by
  have hr := ENNReal.toReal_mono (show (2 : ℝ≥0∞)^n /
      ENNReal.ofReal (Real.exp (t/2)) ≠ ⊤ from
      ENNReal.div_ne_top (by simp) (by positivity))
    (costly_straight_probability h p d n t)
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_ofNat] at hr
  change P.real _ ≤ _ at hr
  rw [show -t / 2 = -(t / 2) by ring, Real.exp_neg]
  simpa only [div_eq_mul_inv] using hr

theorem costly_straight_excess_probability_real (h : ExponentialEnvironment P τ)
    (p : Vertex) (d : Step) (n : ℕ) (t : ℝ) :
    P.real {ω | 4 * (n : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (List.replicate n d)} ≤ Real.exp (-t / 2) := by
  refine (costly_straight_probability_real h p d n (4 * n + t)).trans ?_
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  have hp : (2 : ℝ)^n ≤ Real.exp (2 * (n : ℝ)) := by
    rw [mul_comm (2 : ℝ), Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) htwo n
  calc
    (2 : ℝ)^n * Real.exp (-(4 * n + t) / 2) ≤
        Real.exp (2 * (n : ℝ)) * Real.exp (-(4 * n + t) / 2) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = Real.exp (-t / 2) := by rw [← Real.exp_add]; congr 1; ring

theorem coordinatePath_endpoint (p q : Vertex) : p + displacement (coordinatePath p q) = q := by
  simp [coordinatePath, displacement_horizontal, displacement_vertical, Prod.ext_iff]

theorem costly_horizontal_excess_probability_real (h : ExponentialEnvironment P τ)
    (p : Vertex) (a : ℤ) (t : ℝ) :
    P.real {ω | 4 * (a.natAbs : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (horizontal a)} ≤ Real.exp (-t / 2) := by
  by_cases ha : 0 ≤ a
  · have he : a.toNat = a.natAbs := by omega
    simpa only [horizontal, ite_eq_left ha, he] using
      costly_straight_excess_probability_real h p Step.east a.toNat t
  · have he : (-a).toNat = a.natAbs := by omega
    simpa only [horizontal, ite_eq_right ha, he] using
      costly_straight_excess_probability_real h p Step.west (-a).toNat t

theorem costly_vertical_excess_probability_real (h : ExponentialEnvironment P τ)
    (p : Vertex) (a : ℤ) (t : ℝ) :
    P.real {ω | 4 * (a.natAbs : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (vertical a)} ≤ Real.exp (-t / 2) := by
  by_cases ha : 0 ≤ a
  · have he : a.toNat = a.natAbs := by omega
    simpa only [vertical, ite_eq_left ha, he] using
      costly_straight_excess_probability_real h p Step.north a.toNat t
  · have he : (-a).toNat = a.natAbs := by omega
    simpa only [vertical, ite_eq_right ha, he] using
      costly_straight_excess_probability_real h p Step.south (-a).toNat t

theorem costly_coordinatePath_probability_real (h : ExponentialEnvironment P τ)
    (p q : Vertex) (t : ℝ) :
    P.real {ω | 4 * (latticeDistance p q : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (coordinatePath p q)} ≤ 2 * Real.exp (-t / 4) := by
  let _ := h.probability
  let A := {ω | 4 * ((q.1-p.1).natAbs : ℝ) + t/2 ≤
    pathCost (fun e => τ e ω) p (horizontal (q.1-p.1))}
  let B := {ω | 4 * ((q.2-p.2).natAbs : ℝ) + t/2 ≤
    pathCost (fun e => τ e ω) (p + displacement (horizontal (q.1-p.1)))
      (vertical (q.2-p.2))}
  have hs : {ω | 4 * (latticeDistance p q : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (coordinatePath p q)} ⊆ A ∪ B := by
    intro ω hω
    change _ ∨ _
    by_contra hn
    push Not at hn
    simp only [Set.mem_ofPred_eq, coordinatePath, pathCost_append, latticeDistance, Nat.cast_add] at hω
    simp only [A, B, Set.mem_ofPred_eq, not_le] at hn
    linarith
  refine (measureReal_mono hs).trans ((measureReal_union_le A B).trans ?_)
  have ha := costly_horizontal_excess_probability_real h p (q.1-p.1) (t/2)
  have hb := costly_vertical_excess_probability_real h
    (p + displacement (horizontal (q.1-p.1))) (q.2-p.2) (t/2)
  change P.real A + P.real B ≤ _
  change P.real A ≤ _ at ha
  change P.real B ≤ _ at hb
  have he : -(t / 2) / 2 = -t / 4 := by ring
  rw [he] at ha hb
  linarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SpatialModulus
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Finset Filter Set
open scoped ENNReal Topology

theorem latticeBox_card (n : ℕ) : (latticeBox n).card = (2*n+1)^2 := by
  have hi : (Finset.Icc (-(n : ℤ)) n).card = 2*n+1 := by
    rw [Int.card_Icc]
    omega
  simp [latticeBox, hi, pow_two]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem badConnections_probability (h : ExponentialEnvironment P τ) (ε : ℝ) (n : ℕ) :
    P.real (badConnections τ ε n) ≤
      (2*(n : ℝ)+1)^4 * (2 * Real.exp (-ε * n / 4)) := by
  let _ := h.probability
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  calc
    _ ≤ ∑ _pq ∈ (latticeBox n) ×ˢ (latticeBox n),
        2 * Real.exp (-(ε * n) / 4) :=
      sum_le_sum (fun pq _ => costly_coordinatePath_probability_real h pq.1 pq.2 (ε*n))
    _ = _ := by simp [latticeBox_card]; ring

theorem summable_box_connection_bound {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n : ℕ => (2*(n : ℝ)+1)^4 * (2 * Real.exp (-ε*n/4))) := by
  have hs (k : ℕ) := Real.summable_pow_mul_exp_neg_nat_mul k
    (show 0 < ε/4 by linarith)
  have ht := (((((hs 4).mul_left 32).add ((hs 3).mul_left 64)).add
    ((hs 2).mul_left 48)).add ((hs 1).mul_left 16)).add ((hs 0).mul_left 2)
  apply ht.congr
  intro n
  simp only [pow_one, pow_zero]
  have he : -(ε/4)*(n : ℝ) = -ε*n/4 := by ring
  rw [he]
  ring

theorem ae_eventually_coordinate_connections (h : ExponentialEnvironment P τ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      pathCost (fun e => τ e ω) p (coordinatePath p q) <
        4 * (latticeDistance p q : ℝ) + ε * n := by
  let _ := h.probability
  have hs : Summable (fun n => P.real (badConnections τ ε n)) :=
    (summable_box_connection_bound hε).of_nonneg_of_le
      (fun _ => measureReal_nonneg) (badConnections_probability h ε)
  have ht : (∑' n, P (badConnections τ ε n)) ≠ ⊤ := by
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      hs.tsum_ofReal_ne_top
  filter_upwards [ae_eventually_notMem ht] with ω hω
  filter_upwards [hω] with n hn
  intro p hp q hq
  by_contra hc
  apply hn
  exact mem_iUnion₂.mpr ⟨(p,q), mem_product.mpr ⟨hp,hq⟩, le_of_not_gt hc⟩

theorem ae_eventually_passageTime_connections (h : ExponentialEnvironment P τ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime (fun e => τ e ω) p q <
        4 * (latticeDistance p q : ℝ) + ε * n := by
  filter_upwards [h.ae_positive, ae_eventually_coordinate_connections h hε] with ω hp hc
  filter_upwards [hc] with n hn
  intro p hp' q hq'
  exact (passageTime_le_cost _ (fun e => (hp e).le) p q
    (coordinatePath p q) (coordinatePath_endpoint p q)).trans_lt (hn p hp' q hq')

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_LatticeGeometry
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory Filter Set
open scoped Topology

theorem plane_coordinate_le_norm (v : Plane) (i : Fin 2) : |v i| ≤ ‖v‖ :=
  PiLp.norm_apply_le v i

theorem plane_norm_le_coordinates (v : Plane) : ‖v‖ ≤ |v 0| + |v 1| := by
  let x : Plane := PiLp.single 2 0 (v 0)
  let y : Plane := PiLp.single 2 1 (v 1)
  have hv : v = x+y := by
    ext i
    fin_cases i <;> simp [x,y]
  have hx : ‖x‖ = |v 0| := by simp [x]
  have hy : ‖y‖ = |v 1| := by simp [y]
  calc
    ‖v‖ = ‖x+y‖ := congrArg norm hv
    _ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
    _ = _ := by rw [hx,hy]

theorem latticeDistance_le_norm (p q : Vertex) :
    (latticeDistance p q : ℝ) ≤ 2 * ‖latticeEmbed q - latticeEmbed p‖ := by
  have h0 := plane_coordinate_le_norm (latticeEmbed q - latticeEmbed p) 0
  have h1 := plane_coordinate_le_norm (latticeEmbed q - latticeEmbed p) 1
  have hc (a : ℤ) : (a.natAbs : ℝ) = |(a : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  simp only [latticeDistance, Nat.cast_add, hc, Int.cast_sub]
  simpa only [latticeEmbed, PiLp.sub_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, two_mul] using add_le_add h0 h1

theorem latticeFloor_error (v : Plane) : ‖latticeEmbed (latticeFloor v) - v‖ ≤ 2 := by
  have hi (i : Fin 2) : |(latticeEmbed (latticeFloor v) - v) i| ≤ 1 := by
    have hle := Int.floor_le (v i)
    have hlt := Int.lt_floor_add_one (v i)
    have he : (latticeEmbed (latticeFloor v) - v) i = (⌊v i⌋ : ℝ) - v i := by
      fin_cases i <;> rfl
    rw [he, abs_of_nonpos (by linarith)]
    linarith
  exact (plane_norm_le_coordinates _).trans (by linarith [hi 0, hi 1])

theorem latticeFloor_mem_box {v : Plane} {n : ℕ} (hv : ‖v‖ ≤ 2) (hn : 1 ≤ n) :
    latticeFloor ((n : ℝ) • v) ∈ latticeBox (3*n) := by
  have hi (i : Fin 2) : -(3*(n : ℤ)) ≤ ⌊(n : ℝ)*v i⌋ ∧
      ⌊(n : ℝ)*v i⌋ ≤ 3*(n : ℤ) := by
    have ha := (plane_coordinate_le_norm v i).trans hv
    have hb := abs_le.mp ha
    have hl := Int.floor_le ((n : ℝ)*v i)
    have hu := Int.lt_floor_add_one ((n : ℝ)*v i)
    constructor
    · have : -(3*(n : ℝ)) ≤ (⌊(n : ℝ)*v i⌋ : ℝ) := by
        have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      exact_mod_cast this
    · have : (⌊(n : ℝ)*v i⌋ : ℝ) ≤ 3*(n : ℝ) := by nlinarith
      exact_mod_cast this
  simpa only [latticeBox, Finset.mem_product, Finset.mem_Icc, latticeFloor,
    PiLp.smul_apply, smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] using And.intro (hi 0) (hi 1)

theorem latticeDistance_floor_le (v w : Plane) (n : ℕ) :
    (latticeDistance (latticeFloor ((n : ℝ) • v))
      (latticeFloor ((n : ℝ) • w)) : ℝ) ≤ 2 * (n : ℝ) * ‖w-v‖ + 8 := by
  have hd := latticeDistance_le_norm (latticeFloor ((n : ℝ) • v))
    (latticeFloor ((n : ℝ) • w))
  have he : latticeEmbed (latticeFloor ((n : ℝ) • w)) -
      latticeEmbed (latticeFloor ((n : ℝ) • v)) =
      (latticeEmbed (latticeFloor ((n : ℝ) • w)) - (n : ℝ) • w) +
      (n : ℝ) • (w-v) -
      (latticeEmbed (latticeFloor ((n : ℝ) • v)) - (n : ℝ) • v) := by
    rw [smul_sub]; abel
  have hb : ‖latticeEmbed (latticeFloor ((n : ℝ) • w)) -
      latticeEmbed (latticeFloor ((n : ℝ) • v))‖ ≤
      ‖latticeEmbed (latticeFloor ((n : ℝ) • w)) - (n : ℝ) • w‖ +
      ‖(n : ℝ) • (w-v)‖ +
      ‖latticeEmbed (latticeFloor ((n : ℝ) • v)) - (n : ℝ) • v‖ := by
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  rw [norm_smul, Real.norm_natCast] at hb
  nlinarith [latticeFloor_error ((n : ℝ) • v), latticeFloor_error ((n : ℝ) • w)]

theorem timeConstantNorm_lipschitz_bound (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    ∃ B : ℝ, 0 < B ∧ ∀ v w, |μ v - μ w| ≤ B * ‖v-w‖ := by
  let e0 : Plane := PiLp.single 2 0 1
  let e1 : Plane := PiLp.single 2 1 1
  let B := μ e0 + μ e1 + 1
  have hB : 0 < B := by dsimp [B]; linarith [hμ.nonneg e0, hμ.nonneg e1]
  have hu (v : Plane) : μ v ≤ B * ‖v‖ := by
    have he : v = v 0 • e0 + v 1 • e1 := by
      ext i; fin_cases i <;> simp [e0, e1]
    have ht := hμ.triangle (v 0 • e0) (v 1 • e1)
    rw [← he, hμ.homogeneous, hμ.homogeneous] at ht
    have h0 := mul_le_mul_of_nonneg_right (plane_coordinate_le_norm v 0) (hμ.nonneg e0)
    have h1 := mul_le_mul_of_nonneg_right (plane_coordinate_le_norm v 1) (hμ.nonneg e1)
    dsimp [B]
    nlinarith [norm_nonneg v]
  refine ⟨B, hB, ?_⟩
  intro v w
  apply abs_le.mpr
  have h1 := hμ.triangle (v-w) w
  have h2 := hμ.triangle (w-v) v
  simp only [sub_add_cancel] at h1 h2
  have hu1 := hu (v-w)
  have hu2 := hu (w-v)
  rw [norm_sub_rev] at hu2
  constructor <;> linarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_FiniteNet
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Filter Set Metric
open scoped Topology

theorem uniform_on_unit_ball_of_dense_limits
    (F : ℕ → Plane → ℝ) (μ : Plane → ℝ) (u : ℕ → Plane) (hu : DenseRange u)
    (B : ℝ) (hB : 0 < B) (hμ : ∀ v w, |μ v-μ w| ≤ B * ‖v-w‖)
    (hpoint : ∀ i, Tendsto (fun n => F n (u i)) atTop (𝓝 (μ (u i))))
    (hmod : ∀ ε > 0, ∀ᶠ n in atTop, ∀ v w, ‖v‖ ≤ 2 → ‖w‖ ≤ 2 →
      |F n v-F n w| ≤ 8 * ‖v-w‖ + ε) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ v, ‖v‖ ≤ 1 → |F n v-μ v| < ε := by
  intro ε hε
  let δ := min (1/2 : ℝ) (ε / (4*(8+B)))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by linarith))
  have hδ1 : δ ≤ 1/2 := min_le_left _ _
  have hδe : (8+B)*δ ≤ ε/4 := by
    have ht := min_le_right (1/2 : ℝ) (ε/(4*(8+B)))
    dsimp [δ]
    have hmul := (le_div_iff₀ (by linarith : 0 < 4*(8+B))).mp ht
    nlinarith
  have hcover : closedBall (0 : Plane) 1 ⊆ ⋃ i, ball (u i) δ := by
    intro v _
    obtain ⟨i, hi⟩ := hu.exists_dist_lt v hδ
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨s, hs⟩ := (isCompact_closedBall (0 : Plane) 1).elim_finite_subcover
    (fun i => ball (u i) δ) (fun _ => isOpen_ball) hcover
  have hp : ∀ᶠ n in atTop, ∀ i ∈ s, |F n (u i)-μ (u i)| < ε/2 := by
    rw [eventually_all_finset]
    intro i _
    simpa only [Real.dist_eq] using
      (Metric.tendsto_nhds.mp (hpoint i) (ε/2) (by linarith))
  filter_upwards [hp, hmod (ε/4) (by linarith)] with n hn hm
  intro v hv
  obtain ⟨i, hi, hvi⟩ := mem_iUnion₂.mp (hs (by simpa using hv))
  have hd : ‖v-u i‖ < δ := hvi
  have hui : ‖u i‖ ≤ 2 := by
    have ht := norm_sub_le (u i) v
    have ht' := norm_add_le (u i-v) v
    rw [sub_add_cancel] at ht'
    rw [norm_sub_rev] at ht'
    linarith
  have hm' := hm v (u i) (by linarith) hui
  have hμ' := hμ (u i) v
  rw [norm_sub_rev] at hμ'
  have hp' := hn i hi
  have htri : |F n v-μ v| ≤ |F n v-F n (u i)| +
      |F n (u i)-μ (u i)| + |μ (u i)-μ v| := by
    calc
      _ = |(F n v-F n (u i)) + (F n (u i)-μ (u i)) + (μ (u i)-μ v)| := by
        congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  have hh := mul_lt_mul_of_pos_left hd (show 0 < 8+B by linarith)
  linarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_UniformShape
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

theorem passageTime_origin_difference_le (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p q : Vertex) : |passageTime w 0 p-passageTime w 0 q| ≤ passageTime w p q := by
  have h1 := passageTime_triangle w hw 0 q p
  have h2 := passageTime_triangle w hw 0 p q
  rw [passageTime_symm w hw q p] at h1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem rescaledPassage_modulus (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (hc : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime w p q < 4 * (latticeDistance p q : ℝ) + (1 / (k+1 : ℝ)) * n) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ v u, ‖v‖ ≤ 2 → ‖u‖ ≤ 2 →
      |rescaledPassage w n v-rescaledPassage w n u| ≤ 8 * ‖v-u‖ + ε := by
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < ε/6 by linarith)
  have hthree : Tendsto (fun n : ℕ => 3*n) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have hlarge : ∀ᶠ n : ℕ in atTop, 64/ε < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (64/ε))
  filter_upwards [hthree.eventually (hc k), eventually_ge_atTop 1, hlarge] with n hn hn1 hnlarge
  intro v u hv hu
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hscale : 64 < (n : ℝ)*ε := (div_lt_iff₀ hε).mp hnlarge
  have hconn := hn (latticeFloor ((n : ℝ) • v)) (latticeFloor_mem_box hv hn1)
    (latticeFloor ((n : ℝ) • u)) (latticeFloor_mem_box hu hn1)
  have hd := latticeDistance_floor_le v u n
  rw [norm_sub_rev] at hd
  have hdiff := passageTime_origin_difference_le w hw (latticeFloor ((n : ℝ) • v))
    (latticeFloor ((n : ℝ) • u))
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hconn
  unfold rescaledPassage
  rw [← sub_div, abs_div, abs_of_pos hnpos]
  apply (div_le_iff₀ hnpos).mpr
  have hk' := mul_lt_mul_of_pos_right hk hnpos
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem ae_rescaledPassage_modulus (h : ExponentialEnvironment P τ) :
    ∀ᵐ ω ∂P, ∀ ε > 0, ∀ᶠ n in atTop, ∀ v u, ‖v‖ ≤ 2 → ‖u‖ ≤ 2 →
      |rescaledPassage (fun e => τ e ω) n v-rescaledPassage (fun e => τ e ω) n u| ≤
        8 * ‖v-u‖ + ε := by
  have hc : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime (fun e => τ e ω) p q <
        4 * (latticeDistance p q : ℝ) + (1 / (k+1 : ℝ)) * n := by
    rw [ae_all_iff]
    intro k
    exact ae_eventually_passageTime_connections h (by positivity)
  filter_upwards [h.ae_positive, hc] with ω hp hm
  exact rescaledPassage_modulus _ (fun e => (hp e).le) hm

theorem ae_uniform_rescaledPassage (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ) :
    ∀ᵐ ω ∂P, ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ v, ‖v‖ ≤ 1 →
      |rescaledPassage (fun e => τ e ω) n v-μ v| < ε := by
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq Plane
  obtain ⟨B, hB, hBlip⟩ := timeConstantNorm_lipschitz_bound μ hμ
  have hp : ∀ᵐ ω ∂P, ∀ i : ℕ,
      Tendsto (fun n : ℕ => rescaledPassage (fun e => τ e ω) n (u i))
        atTop (𝓝 (μ (u i))) := by
    rw [ae_all_iff]
    intro i
    filter_upwards [ht (u i)] with ω hω
    exact hω.comp tendsto_natCast_atTop_atTop
  filter_upwards [hp, ae_rescaledPassage_modulus h] with ω hp hm
  exact uniform_on_unit_ball_of_dense_limits _ μ u hu B hB hBlip hp hm

theorem rescaledPassage_lattice_error (w : Edge → ℝ) (μ : Plane → ℝ)
    (hμ : TimeConstantNorm μ) (n : ℕ) (hn : 0 < (n : ℝ)) (z : Vertex) :
    |rescaledPassage w n ((1/(n : ℝ)) • latticeEmbed z) -
      μ ((1/(n : ℝ)) • latticeEmbed z)| =
      |passageTime w 0 z-μ (latticeEmbed z)|/(n : ℝ) := by
  have he : (n : ℝ) • ((1/(n : ℝ)) • latticeEmbed z) = latticeEmbed z := by
    rw [smul_smul, mul_one_div_cancel hn.ne', one_smul]
  rw [rescaledPassage, he, latticeFloor_embed, hμ.homogeneous,
    abs_of_pos (one_div_pos.mpr hn)]
  rw [show (1/(n : ℝ))*μ (latticeEmbed z) = μ (latticeEmbed z)/(n : ℝ) by ring,
    ← sub_div, abs_div, abs_of_pos hn]

theorem uniform_rescaled_ball_bound (w : Edge → ℝ) (μ : Plane → ℝ)
    (hμ : TimeConstantNorm μ)
    (hu : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ v, ‖v‖ ≤ 1 →
      |rescaledPassage w n v-μ v| < ε)
    (C : ℕ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ z : Vertex, ‖latticeEmbed z‖ ≤ (C : ℝ)*n →
      |passageTime w 0 z-μ (latticeEmbed z)| ≤ ε*n := by
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  have hmul : Tendsto (fun n : ℕ => C*n) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    exact hn.trans (Nat.le_mul_of_pos_left n hC)
  filter_upwards [hmul.eventually (hu (ε/C) (div_pos hε hCpos)),
    eventually_ge_atTop 1] with n hn hn1
  intro z hz
  have hnpos : (0 : ℝ) < C*n := mul_pos hCpos (by exact_mod_cast (show 0 < n by omega))
  have hcn : (0 : ℝ) < (C*n : ℕ) := by simpa using hnpos
  have hv : ‖(1/((C*n : ℕ) : ℝ)) • latticeEmbed z‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hcn)]
    have hz' : ‖latticeEmbed z‖ ≤ ((C*n : ℕ) : ℝ) := by simpa using hz
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_one, mul_comm] using (div_le_one hcn).mpr hz'
  have he := hn _ hv
  rw [rescaledPassage_lattice_error w μ hμ (C*n) hcn z] at he
  have ht := (div_lt_iff₀ hcn).mp he
  have hid : ε/(C : ℝ)*((C*n : ℕ) : ℝ) = ε*n := by
    push_cast
    field_simp
  rw [hid] at ht
  exact ht.le

theorem uniformShape_of_uniform_rescaled (w : Edge → ℝ) (μ : Plane → ℝ)
    (hμ : TimeConstantNorm μ)
    (hu : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ v, ‖v‖ ≤ 1 →
      |rescaledPassage w n v-μ v| < ε) : UniformShape w μ := by
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hu (ε/2) (by linarith))
  refine ⟨max 1 (N : ℝ), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro z hz
  let r := ‖latticeEmbed z‖
  let n : ℕ := ⌈r⌉₊
  have hr : 1 ≤ r := (le_max_left _ _).trans hz
  have hnr : r ≤ (n : ℝ) := Nat.le_ceil r
  have hnupper : (n : ℝ) < r+1 := Nat.ceil_lt_add_one (by dsimp [r]; positivity)
  have hnN : N ≤ n := by
    exact_mod_cast ((le_max_right 1 (N : ℝ)).trans hz).trans hnr
  have hnpos : (0 : ℝ) < n := by linarith
  let v : Plane := (1/(n : ℝ)) • latticeEmbed z
  have hnv : (n : ℝ) • v = latticeEmbed z := by
    dsimp [v]
    rw [smul_smul, mul_one_div_cancel hnpos.ne', one_smul]
  have hv : ‖v‖ ≤ 1 := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hnpos)]
    simpa only [r, one_div, div_eq_mul_inv, one_mul, mul_comm] using (div_le_one hnpos).mpr hnr
  have ht := hN n hnN v hv
  have hm : μ (latticeEmbed z) = (n : ℝ) * μ v := by
    rw [← hnv, hμ.homogeneous, abs_of_pos hnpos]
  have hmdiv : μ v = μ (latticeEmbed z)/(n : ℝ) := by
    rw [hm, mul_div_cancel_left₀ _ hnpos.ne']
  simp only [rescaledPassage, hnv, latticeFloor_embed] at ht
  rw [hmdiv, ← sub_div, abs_div, abs_of_pos hnpos] at ht
  have hb := (div_lt_iff₀ hnpos).mp ht
  have hnr2 : (n : ℝ) ≤ 2*r := by linarith
  have he := mul_le_mul_of_nonneg_left hnr2 (show 0 ≤ ε/2 by linarith)
  change |passageTime w 0 z-μ (latticeEmbed z)| ≤ ε*r
  linarith

theorem exponential_uniform_shape (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ) :
    ∀ᵐ ω ∂P, UniformShape (fun e => τ e ω) μ := by
  filter_upwards [ae_uniform_rescaledPassage h μ hμ ht] with ω hω
  exact uniformShape_of_uniform_rescaled _ μ hμ hω

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_Localization
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory Filter Set
open scoped Topology

theorem timeConstantNorm_continuous (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    Continuous μ := by
  obtain ⟨B, hB, hb⟩ := timeConstantNorm_lipschitz_bound μ hμ
  apply Metric.continuous_iff.mpr
  intro v ε hε
  refine ⟨ε/B, div_pos hε hB, ?_⟩
  intro w hw
  have hd : ‖w-v‖ < ε/B := hw
  have he := (lt_div_iff₀ hB).mp hd
  have hl := hb w v
  change |μ w-μ v| < ε
  nlinarith

theorem timeConstantNorm_lower_bound (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    ∃ α : ℝ, 0 < α ∧ ∀ v, α * ‖v‖ ≤ μ v := by
  have hs : (Metric.sphere (0 : Plane) 1).Nonempty := by
    refine ⟨PiLp.single 2 0 1, ?_⟩
    simp
  obtain ⟨v, hv, hmin⟩ := (isCompact_sphere (0 : Plane) 1).exists_isMinOn hs
    (timeConstantNorm_continuous μ hμ).continuousOn
  have hvnorm : ‖v‖ = 1 := by simpa using hv
  have hvne : v ≠ 0 := by intro he; simp [he] at hvnorm
  have hpos : 0 < μ v := lt_of_le_of_ne (hμ.nonneg v) (by
    intro he; exact hvne ((hμ.zero_iff v).mp he.symm))
  refine ⟨μ v,hpos,?_⟩
  intro w
  by_cases hw : w = 0
  · simp [hw, (hμ.zero_iff 0).mpr rfl]
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hunit : (1/‖w‖) • w ∈ Metric.sphere (0 : Plane) 1 := by
    simp [norm_smul, hn.ne']
  have hle : μ v ≤ μ ((1/‖w‖) • w) := hmin hunit
  rw [hμ.homogeneous, abs_of_pos (one_div_pos.mpr hn)] at hle
  have ht := mul_le_mul_of_nonneg_right hle hn.le
  simpa only [one_div, mul_assoc, mul_comm, mul_left_comm,
    inv_mul_cancel₀ hn.ne', mul_inv_cancel₀ hn.ne', one_mul, mul_one] using ht

theorem pathCost_take_le (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p : Vertex) (ds : List Step) (i : ℕ) :
    pathCost w p (ds.take i) ≤ pathCost w p ds := by
  have he := pathCost_append w p (ds.take i) (ds.drop i)
  rw [List.take_append_drop] at he
  have hn := pathCost_nonneg hw (p+displacement (ds.take i)) (ds.drop i)
  linarith

theorem path_confined_of_escape (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p : Vertex) (ds : List Step) (R a : ℝ)
    (hescape : ∀ z, R ≤ ‖latticeEmbed (z-p)‖ → a ≤ passageTime w p z)
    (hcost : pathCost w p ds < a) :
    PathIn p ds {z | ‖latticeEmbed (z-p)‖ < R} := by
  intro i _
  change ‖latticeEmbed (p+displacement (ds.take i)-p)‖ < R
  by_contra hn
  have he := hescape (p+displacement (ds.take i)) (le_of_not_gt hn)
  have hp := passageTime_le_cost w hw p (p+displacement (ds.take i)) (ds.take i) rfl
  have ht := pathCost_take_le w hw p ds i
  linarith

theorem exists_confined_near_optimal (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p q : Vertex) (R a ε : ℝ) (hε : 0 < ε)
    (hescape : ∀ z, R ≤ ‖latticeEmbed (z-p)‖ → a ≤ passageTime w p z)
    (hshort : passageTime w p q + ε ≤ a) :
    ∃ ds, p+displacement ds=q ∧ pathCost w p ds < passageTime w p q+ε ∧
      PathIn p ds {z | ‖latticeEmbed (z-p)‖ < R} := by
  obtain ⟨ds,hend,hcost⟩ := exists_near_optimal_path w p q ε hε
  exact ⟨ds,hend,hcost,path_confined_of_escape w hw p ds R a hescape (hcost.trans_le hshort)⟩

theorem UniformShape.eventually_escape (w : Edge → ℝ) (μ : Plane → ℝ)
    (hu : UniformShape w μ) (α δ : ℝ) (hα : 0 < α) (hδ : 0 < δ)
    (hlower : ∀ v, α*‖v‖ ≤ μ v) :
    ∀ᶠ s : ℝ in atTop, ∀ z : Vertex, δ*s/3 ≤ ‖latticeEmbed z‖ →
      α*δ*s/6 ≤ passageTime w 0 z := by
  obtain ⟨R,hR,hr⟩ := hu (α/2) (by linarith)
  filter_upwards [eventually_ge_atTop (3*R/δ)] with s hs
  intro z hz
  have hRz : R ≤ ‖latticeEmbed z‖ := by
    have ht := (div_le_iff₀ hδ).mp hs
    nlinarith
  have he := (abs_le.mp (hr z hRz)).1
  have hl := hlower (latticeEmbed z)
  have ht := mul_le_mul_of_nonneg_left hz hα.le
  nlinarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ShapeProbability
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

theorem measureReal_tendsto_zero_of_ae_eventually_notMem
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n))
    (he : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ω ∉ A n) :
    Tendsto (fun n => P.real (A n)) atTop (𝓝 0) := by
  classical
  let F : ℕ → Ω → ℝ := fun n => (A n).indicator (fun _ => 1)
  have hm (n) : Measurable (F n) := measurable_const.indicator (hA n)
  have ht : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 0) := by
    filter_upwards [he] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω] with n hn
    simp [F, hn]
  have hi := tendstoInMeasure_of_tendsto_ae (fun n => (hm n).aestronglyMeasurable) ht
  have hp := (tendstoInMeasure_iff_measureReal_norm.mp hi) (1/2) (by norm_num)
  have heq (n : ℕ) : {ω | (1/2 : ℝ) ≤ ‖F n ω-0‖} = A n := by
    ext ω
    by_cases hω : ω ∈ A n <;> norm_num [F, hω]
  simpa only [heq] using hp

theorem measurableSet_goodOrigin (μ : Plane → ℝ) (α : ℝ) (C : ℕ) (η δ : ℝ) (n : ℕ) :
    MeasurableSet {w | GoodOrigin μ α C η δ n w} := by
  unfold GoodOrigin
  simp only [ofPred_and, ofPred_forall]
  refine MeasurableSet.inter (MeasurableSet.iInter fun e => ?_) ?_
  · exact measurableSet_le measurable_const (measurable_pi_apply e)
  refine MeasurableSet.inter (MeasurableSet.iInter fun z => ?_)
    (MeasurableSet.iInter fun z => ?_)
  · apply MeasurableSet.iInter
    intro _
    exact measurableSet_le (continuous_abs.measurable.comp ((measurable_passageTime measurable_pi_apply 0 z).sub_const _))
      measurable_const
  · apply MeasurableSet.iInter
    intro _
    exact measurableSet_le measurable_const (measurable_passageTime measurable_pi_apply 0 z)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem ae_eventually_goodOrigin (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (α : ℝ) (hα : 0 < α) (hlower : ∀ v, α*‖v‖ ≤ μ v)
    (C : ℕ) (hC : 0 < C) (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, GoodOrigin μ α C η δ n (fun e => τ e ω) := by
  filter_upwards [h.ae_positive, ae_uniform_rescaledPassage h μ hμ ht,
    exponential_uniform_shape h μ hμ ht] with ω hp hu hs
  have hb := uniform_rescaled_ball_bound _ μ hμ hu C hC η hη
  have he' : ∀ᶠ n : ℕ in atTop, ∀ z : Vertex, δ*n/3 ≤ ‖latticeEmbed z‖ →
      α*δ*n/6 ≤ passageTime (fun e => τ e ω) 0 z :=
    tendsto_natCast_atTop_atTop.eventually (hs.eventually_escape _ μ α δ hα hδ hlower)
  filter_upwards [hb,he'] with n hn he
  exact ⟨fun e => (hp e).le, hn, he⟩

theorem goodOrigin_failure_tendsto_zero (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (α : ℝ) (hα : 0 < α) (hlower : ∀ v, α*‖v‖ ≤ μ v)
    (C : ℕ) (hC : 0 < C) (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ) :
    Tendsto (fun n => P.real {ω | ¬GoodOrigin μ α C η δ n (fun e => τ e ω)})
      atTop (𝓝 0) := by
  let _ := h.probability
  apply measureReal_tendsto_zero_of_ae_eventually_notMem
  · intro n
    exact ((measurableSet_goodOrigin μ α C η δ n).preimage
      (Measurable.of_eval h.measurable)).compl
  · simpa only [mem_ofPred_eq, not_not] using
      ae_eventually_goodOrigin h μ hμ ht α hα hlower C hC η δ hη hδ

theorem translated_goodOrigin_failure_probability (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (α : ℝ) (C : ℕ) (η δ : ℝ) (n : ℕ) (p : Vertex) :
    P {ω | ¬GoodOrigin μ α C η δ n (fun e => τ (shiftEdge p e) ω)} =
      P {ω | ¬GoodOrigin μ α C η δ n (fun e => τ e ω)} :=
  translated_event_probability h p _ (measurableSet_goodOrigin μ α C η δ n).compl

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_PathConcatenation
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset

theorem pathIn_append (p : Vertex) (ds es : List Step) (S : Set Vertex)
    (hd : PathIn p ds S) (he : PathIn (p+displacement ds) es S) :
    PathIn p (ds++es) S := by
  intro i hi
  by_cases hid : i ≤ ds.length
  · simpa only [List.take_append, Nat.sub_eq_zero_of_le hid, List.take_zero,
      List.append_nil] using hd i hid
  · have hle : ds.length ≤ i := by omega
    have hie : i-ds.length ≤ es.length := by simp only [List.length_append] at hi; omega
    have hh := he (i-ds.length) hie
    simpa only [List.take_append, List.take_of_length_le hle, displacement_append,
      add_assoc] using hh

theorem exists_path_chain (w : Edge → ℝ) (p : ℕ → Vertex) (S : Set Vertex)
    (a : ℕ → ℝ) (n : ℕ) (hp : p 0 ∈ S)
    (h : ∀ i < n, ∃ ds, p i+displacement ds=p (i+1) ∧
      pathCost w (p i) ds ≤ a i ∧ PathIn (p i) ds S) :
    ∃ ds, p 0+displacement ds=p n ∧
      pathCost w (p 0) ds ≤ ∑ i ∈ range n, a i ∧ PathIn (p 0) ds S := by
  induction n with
  | zero =>
    refine ⟨[],by simp,by simp [pathCost],?_⟩
    intro i hi
    simpa using hp
  | succ n ih =>
    obtain ⟨ds,hd,hcostd,hind⟩ := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    obtain ⟨es,he,hcoste,hine⟩ := h n (Nat.lt_succ_self n)
    refine ⟨ds++es,?_,?_,?_⟩
    · rw [displacement_append, ← add_assoc, hd]
      exact he
    · rw [pathCost_append, hd, sum_range_succ]
      exact add_le_add hcostd hcoste
    · apply pathIn_append _ _ _ _ hind
      simpa only [hd] using hine

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_Waypoints
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

theorem waypoint_end (p q : Vertex) (B : ℕ) (hB : 0 < B) : waypoint p q B B=q := by
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  simp [waypoint,segmentPoint,hb]

theorem waypoint_error (p q : Vertex) (B j : ℕ) :
    ‖latticeEmbed (waypoint p q B j)-segmentPoint p q ((j : ℝ)/B)‖ ≤ 2 :=
  latticeFloor_error _

theorem waypoint_displacement_error (p q : Vertex) (B j : ℕ) :
    ‖latticeEmbed (waypoint p q B (j+1)-waypoint p q B j) -
      (1/(B : ℝ)) • latticeEmbed (q-p)‖ ≤ 4 := by
  have he : latticeEmbed (waypoint p q B (j+1)-waypoint p q B j) -
      (1/(B : ℝ)) • latticeEmbed (q-p) =
      (latticeEmbed (waypoint p q B (j+1))-segmentPoint p q (((j+1 : ℕ) : ℝ)/B)) -
      (latticeEmbed (waypoint p q B j)-segmentPoint p q ((j : ℝ)/B)) := by
    rw [latticeEmbed_sub,latticeEmbed_sub]
    unfold segmentPoint
    ext i
    simp [PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
    ring
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith [waypoint_error p q B (j+1),waypoint_error p q B j])

theorem waypoint_displacement_norm (p q : Vertex) (B j : ℕ) (hB : 0 < B) :
    ‖latticeEmbed (waypoint p q B (j+1)-waypoint p q B j)‖ ≤
      ‖latticeEmbed (q-p)‖/(B : ℝ)+4 := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have ht := norm_sub_le (latticeEmbed (waypoint p q B (j+1)-waypoint p q B j))
    ((1/(B : ℝ)) • latticeEmbed (q-p))
  have hn := norm_add_le
    (latticeEmbed (waypoint p q B (j+1)-waypoint p q B j)-(1/(B : ℝ)) • latticeEmbed (q-p))
    ((1/(B : ℝ)) • latticeEmbed (q-p))
  rw [sub_add_cancel,norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hb)] at hn
  have he := waypoint_displacement_error p q B j
  have hid : (1/(B : ℝ))*‖latticeEmbed (q-p)‖=‖latticeEmbed (q-p)‖/(B : ℝ) := by ring
  rw [hid] at hn
  linarith

theorem waypoint_cost_bound (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (β : ℝ) (hβ : 0 ≤ β) (hlip : ∀ v w, |μ v-μ w| ≤ β*‖v-w‖)
    (p q : Vertex) (B j : ℕ) (hB : 0 < B) :
    μ (latticeEmbed (waypoint p q B (j+1)-waypoint p q B j)) ≤
      μ (latticeEmbed (q-p))/(B : ℝ)+4*β := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have ht := (le_abs_self _).trans (hlip
    (latticeEmbed (waypoint p q B (j+1)-waypoint p q B j))
    ((1/(B : ℝ)) • latticeEmbed (q-p)))
  have he := mul_le_mul_of_nonneg_left (waypoint_displacement_error p q B j) hβ
  rw [hμ.homogeneous,abs_of_pos (one_div_pos.mpr hb)] at ht
  have hid : (1/(B : ℝ))*μ (latticeEmbed (q-p))=μ (latticeEmbed (q-p))/(B : ℝ) := by ring
  rw [hid] at ht
  linarith

theorem waypoint_ball_in_tube (p q : Vertex) (B j : ℕ) (hB : 0 < B) (hj : j ≤ B)
    (R : ℝ) (z : Vertex) (hz : ‖latticeEmbed (z-waypoint p q B j)‖ ≤ R) :
    z ∈ SegmentTube p q (R+2) := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  refine ⟨(j : ℝ)/B,div_nonneg (Nat.cast_nonneg _) hb.le,?_,?_⟩
  · exact (div_le_one hb).mpr (by exact_mod_cast hj)
  have he := waypoint_error p q B j
  have ht := norm_add_le (latticeEmbed z-latticeEmbed (waypoint p q B j))
    (latticeEmbed (waypoint p q B j)-segmentPoint p q ((j : ℝ)/B))
  rw [sub_add_sub_cancel] at ht
  rw [latticeEmbed_sub] at hz
  linarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_LocalTravel
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped Topology

theorem localTravel_of_waypoint_tests (w : Edge → ℝ) (μ : Plane → ℝ)
    (hμ : TimeConstantNorm μ) (β : ℝ) (hβ : 0 ≤ β)
    (hlip : ∀ v u, |μ v-μ u| ≤ β*‖v-u‖)
    (p q : Vertex) (B C n : ℕ) (hB : 0 < B) (α D η δ κ : ℝ)
    (hdist : ‖latticeEmbed (q-p)‖ ≤ D*n)
    (hshortdist : D*n/(B : ℝ)+4 ≤ (C : ℝ)*n)
    (hshortcost : β*(D*n)/(B : ℝ)+4*β+κ*n+1 ≤ α*δ*n/6)
    (htotal : (B : ℝ)*(4*β+κ*n+1) ≤ η*n)
    (htube : δ*n/3+2 ≤ δ*n)
    (hgood : ∀ j < B, GoodOrigin μ α C κ δ n
      (fun e => w (shiftEdge (waypoint p q B j) e))) :
    LocalTravel μ η δ n p q w := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hw : ∀ e, 0 ≤ w e := by
    intro e
    have ht := (hgood 0 hB).1 (e.1-p,e.2)
    simpa [waypoint_zero,shiftEdge] using ht
  have hμzero : μ 0=0 := (hμ.zero_iff 0).mpr rfl
  have hwhole : μ (latticeEmbed (q-p)) ≤ β*(D*n) := by
    have ht := (le_abs_self _).trans (hlip (latticeEmbed (q-p)) 0)
    simp only [hμzero,sub_zero] at ht
    exact ht.trans (mul_le_mul_of_nonneg_left hdist hβ)
  let a := μ (latticeEmbed (q-p))/(B : ℝ)+4*β+κ*n+1
  have hpiece (j : ℕ) (hj : j < B) : ∃ ds,
      waypoint p q B j+displacement ds=waypoint p q B (j+1) ∧
      pathCost w (waypoint p q B j) ds ≤ a ∧
      PathIn (waypoint p q B j) ds (SegmentTube p q (δ*n)) := by
    let x := waypoint p q B j
    let y := waypoint p q B (j+1)
    have hg := hgood j hj
    have hlength : ‖latticeEmbed (y-x)‖ ≤ (C : ℝ)*n := by
      have ht := waypoint_displacement_norm p q B j hB
      exact (ht.trans (add_le_add ((div_le_div_iff_of_pos_right hb).mpr hdist) le_rfl)).trans hshortdist
    have herror := (abs_le.mp (hg.2.1 (y-x) hlength)).2
    have hpassage : passageTime w x y ≤ μ (latticeEmbed (y-x))+κ*n := by
      have hxy : waypoint p q B j+(y-x)=y := by dsimp [x]; abel
      simp only [passageTime_translate,add_zero,hxy] at herror
      linarith
    have hstepμ := waypoint_cost_bound μ hμ β hβ hlip p q B j hB
    have hshort : passageTime w x y+1 ≤ α*δ*n/6 := by
      have hd := (div_le_div_iff_of_pos_right hb).mpr hwhole
      change μ (latticeEmbed (y-x)) ≤ _ at hstepμ
      linarith
    have hescape (z : Vertex) (hz : δ*n/3 ≤ ‖latticeEmbed (z-x)‖) :
        α*δ*n/6 ≤ passageTime w x z := by
      have hxz : waypoint p q B j+(z-x)=z := by dsimp [x]; abel
      simpa only [passageTime_translate,add_zero,hxz] using hg.2.2 (z-x) hz
    obtain ⟨ds,hend,hcost,hlocal⟩ := exists_confined_near_optimal w hw x y
      (δ*n/3) (α*δ*n/6) 1 (by norm_num) hescape hshort
    refine ⟨ds,hend,?_,?_⟩
    · change pathCost w x ds ≤ a
      dsimp [a]
      change μ (latticeEmbed (y-x)) ≤ _ at hstepμ
      linarith
    · intro i hi
      obtain ⟨t,ht0,ht1,hbound⟩ := waypoint_ball_in_tube p q B j hB hj.le
        (δ*n/3) (x+displacement (ds.take i)) (hlocal i hi).le
      exact ⟨t,ht0,ht1,hbound.trans htube⟩
  have hp : waypoint p q B 0 ∈ SegmentTube p q (δ*n) := by
    refine ⟨0,by norm_num,by norm_num,?_⟩
    have hn : 0 ≤ δ*n := by linarith
    simpa [segmentPoint] using hn
  obtain ⟨ds,hend,hcost,hlocal⟩ := exists_path_chain w (waypoint p q B)
    (SegmentTube p q (δ*n)) (fun _ => a) B hp hpiece
  refine ⟨ds,by simpa [waypoint_end p q B hB] using hend,?_,by simpa using hlocal⟩
  have hid : (B : ℝ)*a=μ (latticeEmbed (q-p))+(B : ℝ)*(4*β+κ*n+1) := by
    dsimp [a]
    field_simp; ring
  simp only [sum_const,card_range,nsmul_eq_mul] at hcost
  rw [hid] at hcost
  simpa only [waypoint_zero] using hcost.trans (add_le_add le_rfl htotal)

theorem localTravel_parameters (α β D η δ : ℝ)
    (hα : 0 < α) (hβ : 0 ≤ β) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ B C : ℕ, ∃ κ : ℝ, 0 < B ∧ 0 < C ∧ 0 < κ ∧
      ∀ᶠ n : ℕ in atTop,
        D*n/(B : ℝ)+4 ≤ (C : ℝ)*n ∧
        β*(D*n)/(B : ℝ)+4*β+κ*n+1 ≤ α*δ*n/6 ∧
        (B : ℝ)*(4*β+κ*n+1) ≤ η*n ∧ δ*n/3+2 ≤ δ*n := by
  have had : 0 < α*δ := mul_pos hα hδ
  obtain ⟨B,hB⟩ := exists_nat_gt (max 1 (24*β*D/(α*δ)))
  have hb1 : (1 : ℝ) < B := (le_max_left _ _).trans_lt hB
  have hbpos : (0 : ℝ) < B := by linarith
  have hb : 0 < B := by exact_mod_cast hbpos
  have hbchoose := (div_lt_iff₀ had).mp ((le_max_right _ _).trans_lt hB)
  have hbase : β*D/(B : ℝ) ≤ α*δ/24 :=
    (div_le_iff₀ hbpos).mpr (by nlinarith)
  obtain ⟨C,hC⟩ := exists_nat_gt (D+4)
  have hc : 0 < C := by
    have : (0 : ℝ) < C := by linarith
    exact_mod_cast this
  let κ := min (η/(4*(B : ℝ))) (α*δ/24)
  have hk : 0 < κ := lt_min (div_pos hη (by linarith)) (div_pos had (by norm_num))
  have hkcost : κ ≤ α*δ/24 := min_le_right _ _
  have hktotal : (B : ℝ)*κ ≤ η/4 := by
    have ht := (le_div_iff₀ (by linarith : 0 < 4*(B : ℝ))).mp (min_le_left _ _ : κ ≤ η/(4*(B : ℝ)))
    nlinarith
  refine ⟨B,C,κ,hb,hc,hk,?_⟩
  have hlim := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  filter_upwards [eventually_ge_atTop 1,
    hlim.eventually (eventually_ge_atTop (12*(4*β+1)/(α*δ))),
    hlim.eventually (eventually_ge_atTop (2*(B : ℝ)*(4*β+1)/η)),
    hlim.eventually (eventually_ge_atTop (3/δ))] with n hn hn1 hn2 hn3
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1' := (div_le_iff₀ had).mp hn1
  have hn2' := (div_le_iff₀ hη).mp hn2
  have hn3' := (div_le_iff₀ hδ).mp hn3
  have hbase' := mul_le_mul_of_nonneg_right hbase hn0
  have hkcost' := mul_le_mul_of_nonneg_right hkcost hn0
  have hktotal' := mul_le_mul_of_nonneg_right hktotal hn0
  have hdiv : D*(n : ℝ)/(B : ℝ) ≤ D*n := by
    apply (div_le_iff₀ hbpos).mpr
    have ht := mul_le_mul_of_nonneg_left hb1.le (mul_nonneg hD.le hn0)
    simpa using ht
  have hc' := mul_le_mul_of_nonneg_right hC.le hn0
  have hid : β*(D*n)/(B : ℝ) = (β*D/(B : ℝ))*n := by ring
  rw [hid]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem localTravel_failure_bound (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (β : ℝ) (hβ : 0 ≤ β)
    (hlip : ∀ v u, |μ v-μ u| ≤ β*‖v-u‖)
    (p q : Vertex) (B C n : ℕ) (hB : 0 < B) (α D η δ κ : ℝ)
    (hdist : ‖latticeEmbed (q-p)‖ ≤ D*n)
    (hshortdist : D*n/(B : ℝ)+4 ≤ (C : ℝ)*n)
    (hshortcost : β*(D*n)/(B : ℝ)+4*β+κ*n+1 ≤ α*δ*n/6)
    (htotal : (B : ℝ)*(4*β+κ*n+1) ≤ η*n)
    (htube : δ*n/3+2 ≤ δ*n) :
    P.real {ω | ¬LocalTravel μ η δ n p q (fun e => τ e ω)} ≤
      (B : ℝ)*P.real {ω | ¬GoodOrigin μ α C κ δ n (fun e => τ e ω)} := by
  let _ := h.probability
  let A (j : ℕ) := {ω | ¬GoodOrigin μ α C κ δ n
    (fun e => τ (shiftEdge (waypoint p q B j) e) ω)}
  have hsub : {ω | ¬LocalTravel μ η δ n p q (fun e => τ e ω)} ⊆ ⋃ j ∈ range B, A j := by
    intro ω hω
    by_contra hn
    have hg (j : ℕ) (hj : j < B) : GoodOrigin μ α C κ δ n
        (fun e => τ (shiftEdge (waypoint p q B j) e) ω) := by
      by_contra hbad
      exact hn (mem_iUnion₂.mpr ⟨j,mem_range.mpr hj,hbad⟩)
    exact hω (localTravel_of_waypoint_tests _ μ hμ β hβ hlip p q B C n hB
      α D η δ κ hdist hshortdist hshortcost htotal htube hg)
  refine (measureReal_mono hsub (measure_ne_top P _)).trans ((measureReal_biUnion_finset_le _ _).trans ?_)
  have he (j : ℕ) : P.real (A j) = P.real {ω | ¬GoodOrigin μ α C κ δ n (fun e => τ e ω)} :=
    congrArg ENNReal.toReal (translated_goodOrigin_failure_probability h μ α C κ δ n (waypoint p q B j))
  simp only [he,sum_const,card_range,nsmul_eq_mul,le_refl]

theorem exponential_local_travel_nat (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ p q : Vertex, ‖latticeEmbed (q-p)‖ ≤ D*n →
      P.real {ω | ¬LocalTravel μ η δ n p q (fun e => τ e ω)} < ε := by
  obtain ⟨β,hβ,hlip⟩ := timeConstantNorm_lipschitz_bound μ hμ
  obtain ⟨α,hα,hlower⟩ := timeConstantNorm_lower_bound μ hμ
  obtain ⟨B,C,κ,hB,hC,hκ,hparams⟩ := localTravel_parameters α β D η δ hα hβ.le hD hη hδ
  have hprob := goodOrigin_failure_tendsto_zero h μ hμ ht α hα hlower C hC κ δ hκ hδ
  have hprob' : Tendsto (fun n => (B : ℝ)*P.real {ω | ¬GoodOrigin μ α C κ δ n (fun e => τ e ω)})
      atTop (𝓝 0) := by simpa using hprob.const_mul (B : ℝ)
  intro ε hε
  filter_upwards [hparams,hprob'.eventually (gt_mem_nhds hε)] with n hn hp
  intro p q hpq
  exact (localTravel_failure_bound h μ hμ β hβ.le hlip p q B C n hB
    α D η δ κ hpq hn.1 hn.2.1 hn.2.2.1 hn.2.2.2).trans_lt hp

theorem localTravel_mono (μ : Plane → ℝ) (w : Edge → ℝ) (p q : Vertex)
    {η δ s η' δ' s' : ℝ} (hη : η*s ≤ η'*s') (hδ : δ*s ≤ δ'*s')
    (h : LocalTravel μ η δ s p q w) : LocalTravel μ η' δ' s' p q w := by
  obtain ⟨ds,hend,hcost,htube⟩ := h
  refine ⟨ds,hend,hcost.trans (add_le_add le_rfl hη),?_⟩
  intro i hi
  obtain ⟨t,ht0,ht1,hbound⟩ := htube i hi
  exact ⟨t,ht0,ht1,hbound.trans hδ⟩

theorem measurableSet_localTravel (μ : Plane → ℝ) (η δ s : ℝ) (p q : Vertex) :
    MeasurableSet {w | LocalTravel μ η δ s p q w} := by
  have hm := measurableSet_bounded_path_event (τ := fun e (w : Edge → ℝ) => w e)
    measurable_pi_apply
    (fun x ds => x=p ∧ x+displacement ds=q ∧ PathIn x ds (SegmentTube p q (δ*s)))
    (fun _ _ => μ (latticeEmbed (q-p))+η*s)
  convert hm using 1
  ext w
  constructor
  · rintro ⟨ds,hend,hcost,htube⟩
    exact ⟨p,ds,⟨rfl,hend,htube⟩,hcost⟩
  · rintro ⟨x,ds,⟨rfl,hend,htube⟩,hcost⟩
    exact ⟨ds,hend,hcost,htube⟩

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_AttachmentGeometry
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

theorem step_embed_norm_le (d : Step) : ‖latticeEmbed d.delta‖ ≤ 1 := by
  have h := plane_norm_le_coordinates (latticeEmbed d.delta)
  cases d <;> simpa [Step.delta, latticeEmbed] using h

theorem displacement_norm_le_length (ds : List Step) :
    ‖latticeEmbed (displacement ds)‖ ≤ (ds.length : ℝ) := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    rw [displacement_cons, latticeEmbed_add]
    have ht := norm_add_le (latticeEmbed d.delta) (latticeEmbed (displacement ds))
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith [step_embed_norm_le d]

theorem coordinatePath_length (p q : Vertex) :
    (coordinatePath p q).length = latticeDistance p q := by
  have hh (a : ℤ) : (horizontal a).length = a.natAbs := by
    unfold horizontal
    split_ifs <;> simp only [List.length_replicate] <;> omega
  have hv (a : ℤ) : (vertical a).length = a.natAbs := by
    unfold vertical
    split_ifs <;> simp only [List.length_replicate] <;> omega
  simp [coordinatePath, latticeDistance, hh, hv]

theorem coordinatePath_prefix_bound (p q : Vertex) (i : ℕ) :
    ‖latticeEmbed (p+displacement ((coordinatePath p q).take i)-p)‖ ≤
      (latticeDistance p q : ℝ) := by
  simp only [add_sub_cancel_left]
  exact (displacement_norm_le_length _).trans (by
    exact_mod_cast (show ((coordinatePath p q).take i).length ≤ latticeDistance p q by
      rw [List.length_take, coordinatePath_length]; exact min_le_right _ _))

theorem segmentPoint_perturbation (p q p' q' : Vertex) (r t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hp : ‖latticeEmbed (p'-p)‖ ≤ r) (hq : ‖latticeEmbed (q'-q)‖ ≤ r) :
    ‖segmentPoint p' q' t-segmentPoint p q t‖ ≤ r := by
  have he : segmentPoint p' q' t-segmentPoint p q t =
      (1-t) • latticeEmbed (p'-p)+t • latticeEmbed (q'-q) := by
    simp only [segmentPoint,latticeEmbed_sub]
    ext i
    simp [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
    ring
  rw [he]
  have hn := norm_add_le ((1-t) • latticeEmbed (p'-p)) (t • latticeEmbed (q'-q))
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ 1-t),abs_of_nonneg ht0] at hn
  have h1 := mul_le_mul_of_nonneg_left hp (show 0 ≤ 1-t by linarith)
  have h2 := mul_le_mul_of_nonneg_left hq ht0
  nlinarith

theorem segmentTube_perturbation (p q p' q' : Vertex) (r R : ℝ)
    (hp : ‖latticeEmbed (p'-p)‖ ≤ r) (hq : ‖latticeEmbed (q'-q)‖ ≤ r) :
    SegmentTube p' q' R ⊆ SegmentTube p q (R+r) := by
  rintro z ⟨t,ht0,ht1,ht⟩
  refine ⟨t,ht0,ht1,?_⟩
  have hb := segmentPoint_perturbation p q p' q' r t ht0 ht1 hp hq
  have hn := norm_add_le (latticeEmbed z-segmentPoint p' q' t)
    (segmentPoint p' q' t-segmentPoint p q t)
  rw [sub_add_sub_cancel] at hn
  linarith

theorem localTravel_attach (μ : Plane → ℝ) (w : Edge → ℝ)
    (β : ℝ) (hβ : 0 ≤ β) (hlip : ∀ v u, |μ v-μ u| ≤ β*‖v-u‖)
    (p q p' q' : Vertex) (r a η δ s : ℝ)
    (hp : ‖latticeEmbed (p'-p)‖ ≤ r) (hq : ‖latticeEmbed (q'-q)‖ ≤ r)
    (hleft : pathCost w p (coordinatePath p p') ≤ a)
    (hright : pathCost w q' (coordinatePath q' q) ≤ a)
    (hmid : LocalTravel μ η δ s p' q' w) :
    ∃ ds, p+displacement ds=q ∧
        pathCost w p ds ≤ μ (latticeEmbed (q-p))+η*s+2*a+2*β*r ∧
        PathIn p ds (SegmentTube p q (max (3*r) (δ*s+r))) := by
  obtain ⟨ds,hd,hcost,hin⟩ := hmid
  let l := coordinatePath p p'
  let v := coordinatePath q' q
  have hl : p+displacement l=p' := coordinatePath_endpoint p p'
  have hv : q'+displacement v=q := coordinatePath_endpoint q' q
  have hμdiff : μ (latticeEmbed (q'-p')) ≤ μ (latticeEmbed (q-p))+2*β*r := by
    have he : latticeEmbed (q'-p')-latticeEmbed (q-p) =
        latticeEmbed (q'-q)-latticeEmbed (p'-p) := by
      simp only [latticeEmbed_sub]; abel
    have hn : ‖latticeEmbed (q'-p')-latticeEmbed (q-p)‖ ≤ 2*r := by
      rw [he]
      exact (norm_sub_le _ _).trans (by linarith)
    have ht := (le_abs_self _).trans (hlip (latticeEmbed (q'-p')) (latticeEmbed (q-p)))
    have hb := mul_le_mul_of_nonneg_left hn hβ
    linarith
  have hll : PathIn p l (SegmentTube p q (max (3*r) (δ*s+r))) := by
    intro i _
    refine ⟨0,by norm_num,by norm_num,?_⟩
    have hb := coordinatePath_prefix_bound p p' i
    have hdist := latticeDistance_le_norm p p'
    rw [← latticeEmbed_sub] at hdist
    have hr : 0 ≤ r := (norm_nonneg _).trans hp
    simp only [segmentPoint,zero_smul,add_zero]
    rw [← latticeEmbed_sub]
    exact hb.trans ((hdist.trans (by linarith)).trans (le_max_left _ _))
  have hrr : PathIn q' v (SegmentTube p q (max (3*r) (δ*s+r))) := by
    intro i _
    refine ⟨1,by norm_num,by norm_num,?_⟩
    have hb := coordinatePath_prefix_bound q' q i
    have hdist := latticeDistance_le_norm q' q
    rw [norm_sub_rev,← latticeEmbed_sub] at hdist
    have hn := norm_add_le
      (latticeEmbed (q'+displacement (v.take i))-latticeEmbed q')
      (latticeEmbed q'-latticeEmbed q)
    rw [sub_add_sub_cancel,← latticeEmbed_sub,← latticeEmbed_sub,← latticeEmbed_sub] at hn
    simp only [segmentPoint,one_smul,add_sub_cancel]
    rw [← latticeEmbed_sub]
    exact (hn.trans (by dsimp [v] at *; linarith)).trans (le_max_left _ _)
  have hmm : PathIn p' ds (SegmentTube p q (max (3*r) (δ*s+r))) := by
    intro i hi
    obtain ⟨t,ht0,ht1,ht⟩ := segmentTube_perturbation p q p' q' r (δ*s) hp hq (hin i hi)
    exact ⟨t,ht0,ht1,ht.trans (le_max_right _ _)⟩
  refine ⟨l++ds++v,?_,?_,?_⟩
  · rw [displacement_append,displacement_append,← add_assoc,← add_assoc,hl,hd,hv]
  · rw [pathCost_append,pathCost_append,displacement_append,← add_assoc,hl,hd]
    dsimp [l,v]
    linarith
  · apply pathIn_append _ _ _ _ (pathIn_append _ _ _ _ hll (by simpa [hl] using hmm))
    simpa only [displacement_append,← add_assoc,hl,hd] using hrr

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointNet
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter Metric
open scoped Topology

theorem finite_ball_net (D γ : ℝ) (hγ : 0 < γ) :
    ∃ S : Finset {v : Plane // ‖v‖ ≤ D},
      ∀ v : Plane, ‖v‖ ≤ D → ∃ u ∈ S, ‖v-u.val‖ < γ := by
  classical
  have hc : closedBall (0 : Plane) D ⊆
      ⋃ u : {v : Plane // ‖v‖ ≤ D}, ball u.val γ := by
    intro v hv
    have hv' : ‖v‖ ≤ D := by simpa using hv
    exact mem_iUnion.mpr ⟨⟨v,hv'⟩,by simpa using hγ⟩
  obtain ⟨S,hS⟩ := (isCompact_closedBall (0 : Plane) D).elim_finite_subcover
    (fun u : {v : Plane // ‖v‖ ≤ D} => ball u.val γ) (fun _ => isOpen_ball) hc
  refine ⟨S,?_⟩
  intro v hv
  obtain ⟨u,hu,hvu⟩ := mem_iUnion₂.mp (hS (by simpa using hv))
  exact ⟨u,hu,hvu⟩

theorem lattice_mem_box_of_norm_endpt (p : Vertex) (n : ℕ)
    (hp : ‖latticeEmbed p‖ ≤ (n : ℝ)) : p ∈ latticeBox n := by
  have h0 := (plane_coordinate_le_norm (latticeEmbed p) 0).trans hp
  have h1 := (plane_coordinate_le_norm (latticeEmbed p) 1).trans hp
  simp only [latticeEmbed,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h0 h1
  have hh0 : -(n : ℤ) ≤ p.1 ∧ p.1 ≤ n := by exact_mod_cast abs_le.mp h0
  have hh1 : -(n : ℤ) ≤ p.2 ∧ p.2 ≤ n := by exact_mod_cast abs_le.mp h1
  simpa only [latticeBox,Finset.mem_product,Finset.mem_Icc] using And.intro hh0 hh1

theorem scaled_net_norm (D : ℝ) (u : {v : Plane // ‖v‖ ≤ D}) (n : ℕ) :
    ‖latticeEmbed (latticeFloor ((n : ℝ) • u.val))‖ ≤ D*n+2 := by
  have ht := norm_add_le
    (latticeEmbed (latticeFloor ((n : ℝ) • u.val))-(n : ℝ) • u.val)
    ((n : ℝ) • u.val)
  rw [sub_add_cancel,norm_smul,Real.norm_natCast] at ht
  have hu := mul_le_mul_of_nonneg_left u.property (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  linarith [latticeFloor_error ((n : ℝ) • u.val)]

theorem scaled_net_approximates (D γ : ℝ)
    (S : Finset {v : Plane // ‖v‖ ≤ D})
    (hS : ∀ v : Plane, ‖v‖ ≤ D → ∃ u ∈ S, ‖v-u.val‖ < γ)
    (n : ℕ) (hn : 0 < n) (p : Vertex) (hp : ‖latticeEmbed p‖ ≤ D*n) :
    ∃ u ∈ S, ‖latticeEmbed (latticeFloor ((n : ℝ) • u.val)-p)‖ ≤ γ*n+2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let v := (1/(n : ℝ)) • latticeEmbed p
  have hv : ‖v‖ ≤ D := by
    dsimp [v]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hn')]
    rw [one_div_mul_eq_div]
    exact (div_le_iff₀ hn').mpr (by nlinarith)
  obtain ⟨u,hu,hvu⟩ := hS v hv
  refine ⟨u,hu,?_⟩
  have he : (n : ℝ) • v = latticeEmbed p := by
    dsimp [v]; rw [smul_smul]; simp [hn'.ne']
  have hd : ‖(n : ℝ) • u.val-latticeEmbed p‖ ≤ γ*n := by
    rw [← he,← smul_sub,norm_smul,Real.norm_natCast,norm_sub_rev]
    nlinarith
  have ht := norm_add_le
    (latticeEmbed (latticeFloor ((n : ℝ) • u.val))-(n : ℝ) • u.val)
    ((n : ℝ) • u.val-latticeEmbed p)
  rw [sub_add_sub_cancel,← latticeEmbed_sub] at ht
  linarith [latticeFloor_error ((n : ℝ) • u.val)]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BallTravel
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter Finset MeasureTheory ProbabilityTheory
open scoped Topology

theorem ballTravel_of_net (μ : Plane → ℝ) (w : Edge → ℝ)
    (D γ β η δ κ : ℝ) (hβ : 0 ≤ β)
    (hlip : ∀ v u, |μ v-μ u| ≤ β*‖v-u‖)
    (S : Finset {v : Plane // ‖v‖ ≤ D})
    (hS : ∀ v : Plane, ‖v‖ ≤ D → ∃ u ∈ S, ‖v-u.val‖ < γ)
    (C n : ℕ) (hn : 0 < n) (hbox : D*n+2 ≤ (C*n : ℕ))
    (hcost : η/4*n+2*(8*(γ*n+2)+κ*(C*n : ℕ))+2*β*(γ*n+2) ≤ η*n)
    (htube : max (3*(γ*n+2)) (δ/2*n+(γ*n+2)) ≤ δ*n)
    (hc : ∀ p ∈ latticeBox (C*n), ∀ q ∈ latticeBox (C*n),
      pathCost w p (coordinatePath p q) < 4*(latticeDistance p q : ℝ)+κ*(C*n : ℕ))
    (hm : ∀ u ∈ S, ∀ v ∈ S, LocalTravel μ (η/4) (δ/2) n
      (latticeFloor ((n : ℝ) • u.val)) (latticeFloor ((n : ℝ) • v.val)) w) :
    BallTravel μ D η δ n w := by
  intro p q hp hq
  obtain ⟨u,hu,hpu⟩ := scaled_net_approximates D γ S hS n hn p hp
  obtain ⟨v,hv,hqv⟩ := scaled_net_approximates D γ S hS n hn q hq
  let p' := latticeFloor ((n : ℝ) • u.val)
  let q' := latticeFloor ((n : ℝ) • v.val)
  have hpbox : p ∈ latticeBox (C*n) := lattice_mem_box_of_norm_endpt p (C*n) (hp.trans (by linarith))
  have hqbox : q ∈ latticeBox (C*n) := lattice_mem_box_of_norm_endpt q (C*n) (hq.trans (by linarith))
  have hp'box : p' ∈ latticeBox (C*n) := lattice_mem_box_of_norm_endpt p' (C*n)
    ((scaled_net_norm D u n).trans hbox)
  have hq'box : q' ∈ latticeBox (C*n) := lattice_mem_box_of_norm_endpt q' (C*n)
    ((scaled_net_norm D v n).trans hbox)
  have hleft : pathCost w p (coordinatePath p p') ≤ 8*(γ*n+2)+κ*(C*n : ℕ) := by
    have hd := latticeDistance_le_norm p p'
    rw [← latticeEmbed_sub] at hd
    have hh := hc p hpbox p' hp'box
    dsimp [p'] at *
    linarith
  have hright : pathCost w q' (coordinatePath q' q) ≤ 8*(γ*n+2)+κ*(C*n : ℕ) := by
    have hd := latticeDistance_le_norm q' q
    rw [norm_sub_rev,← latticeEmbed_sub] at hd
    have hh := hc q' hq'box q hqbox
    dsimp [q'] at *
    linarith
  obtain ⟨ds,hend,hc',ht'⟩ := localTravel_attach μ w β hβ hlip p q p' q'
    (γ*n+2) (8*(γ*n+2)+κ*(C*n : ℕ)) (η/4) (δ/2) n hpu hqv hleft hright (hm u hu v hv)
  refine ⟨ds,hend,hc'.trans (by linarith),?_⟩
  intro i hi
  obtain ⟨t,ht0,ht1,hbound⟩ := ht' i hi
  exact ⟨t,ht0,ht1,hbound.trans htube⟩

theorem ballTravel_parameters (D β η δ : ℝ)
    (hD : 0 < D) (hβ : 0 ≤ β) (hη : 0 < η) (hδ : 0 < δ) :
    ∃ γ κ : ℝ, ∃ C : ℕ, 0 < γ ∧ 0 < κ ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        0 < n ∧ D*n+2 ≤ (C*n : ℕ) ∧
        η/4*n+2*(8*(γ*n+2)+κ*(C*n : ℕ))+2*β*(γ*n+2) ≤ η*n ∧
        max (3*(γ*n+2)) (δ/2*n+(γ*n+2)) ≤ δ*n := by
  obtain ⟨C,hC⟩ := exists_nat_gt (D+2)
  have hc : (0 : ℝ) < C := by linarith
  have hc' : 0 < C := by exact_mod_cast hc
  let γ := min (η/(8*(16+2*β))) (δ/12)
  let κ := η/(16*(C : ℝ))
  have hγ : 0 < γ := lt_min (div_pos hη (by positivity)) (by positivity)
  have hκ : 0 < κ := div_pos hη (by positivity)
  have hgη : (16+2*β)*γ ≤ η/8 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 8*(16+2*β))).mp (min_le_left _ _ : γ ≤ _)
    nlinarith
  have hgδ : γ ≤ δ/12 := min_le_right _ _
  have hk : κ*(C : ℝ)=η/16 := by dsimp [κ]; field_simp
  refine ⟨γ,κ,C,hγ,hκ,hc',?_⟩
  have hlim := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  filter_upwards [eventually_ge_atTop 1,
    hlim.eventually (eventually_ge_atTop (4*(32+4*β)/η)),
    hlim.eventually (eventually_ge_atTop (24/δ))] with n hn hnη hnδ
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hhη := (div_le_iff₀ hη).mp hnη
  have hhδ := (div_le_iff₀ hδ).mp hnδ
  have hge := mul_le_mul_of_nonneg_right hgη hn0
  have hgd := mul_le_mul_of_nonneg_right hgδ hn0
  have hcb := mul_le_mul_of_nonneg_right hC.le hn0
  simp only [Nat.cast_mul]
  refine ⟨by omega,by nlinarith,?_,?_⟩
  · have he : κ*((C : ℝ)*n)=(η/16)*n := by rw [← mul_assoc,hk]
    rw [he]
    nlinarith
  · apply max_le <;> nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem badConnections_tendsto_zero (h : ExponentialEnvironment P τ)
    (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun n => P.real (badConnections τ κ n)) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) (badConnections_probability h κ)
  exact (summable_box_connection_bound hκ).tendsto_atTop_zero

theorem exponential_ball_travel_nat (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => P.real {ω | ¬BallTravel μ D η δ n (fun e => τ e ω)})
      atTop (𝓝 0) := by
  classical
  let _ := h.probability
  obtain ⟨β,hβ,hlip⟩ := timeConstantNorm_lipschitz_bound μ hμ
  obtain ⟨γ,κ,C,hγ,hκ,hC,hparams⟩ := ballTravel_parameters D β η δ hD hβ.le hη hδ
  obtain ⟨S,hS⟩ := finite_ball_net D γ hγ
  let A (n : ℕ) := ⋃ uv ∈ S ×ˢ S, {ω | ¬LocalTravel μ (η/4) (δ/2) n
    (latticeFloor ((n : ℝ) • uv.1.val)) (latticeFloor ((n : ℝ) • uv.2.val)) (fun e => τ e ω)}
  have hA : Tendsto (fun n => P.real (A n)) atTop (𝓝 0) := by
    apply (tendsto_order.2 ⟨?_,?_⟩)
    · intro a ha
      exact Eventually.of_forall (fun _ => ha.trans_le measureReal_nonneg)
    · intro ε hε
      have hden : 0 < ((S ×ˢ S).card : ℝ)+1 := by positivity
      filter_upwards [eventually_ge_atTop 1,
        exponential_local_travel_nat h μ hμ ht (2*D+4) (η/4) (δ/2)
          (by linarith) (by linarith) (by linarith)
          (ε/(((S ×ˢ S).card : ℝ)+1)) (div_pos hε hden)] with n hn hh
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hbound : P.real (A n) ≤ ((S ×ˢ S).card : ℝ)*(ε/(((S ×ˢ S).card : ℝ)+1)) := by
        refine (measureReal_biUnion_finset_le _ _).trans ?_
        calc
          _ ≤ ∑ _uv ∈ S ×ˢ S, ε/(((S ×ˢ S).card : ℝ)+1) := by
            apply sum_le_sum
            intro uv huv
            apply (hh _ _ ?_).le
            rw [latticeEmbed_sub]
            exact (norm_sub_le _ _).trans (by
              have h1 := scaled_net_norm D uv.1 n
              have h2 := scaled_net_norm D uv.2 n
              nlinarith)
          _ = _ := by simp
      apply hbound.trans_lt
      have he := (div_pos hε hden)
      have hid : ((((S ×ˢ S).card : ℝ)+1))*(ε/(((S ×ˢ S).card : ℝ)+1))=ε := by field_simp
      nlinarith
  have hCn : Tendsto (fun n : ℕ => C*n) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    exact hn.trans (Nat.le_mul_of_pos_left n hC)
  have hB := (badConnections_tendsto_zero h κ hκ).comp hCn
  have hbound : ∀ᶠ n : ℕ in atTop,
      P.real {ω | ¬BallTravel μ D η δ n (fun e => τ e ω)} ≤
        P.real (badConnections τ κ (C*n))+P.real (A n) := by
    filter_upwards [hparams] with n hn
    have hsub : {ω | ¬BallTravel μ D η δ n (fun e => τ e ω)} ⊆
        badConnections τ κ (C*n) ∪ A n := by
      intro ω hω
      by_contra hb
      have hc : ω ∉ badConnections τ κ (C*n) := fun hc => hb (Or.inl hc)
      have hm : ω ∉ A n := fun hm => hb (Or.inr hm)
      apply hω
      apply ballTravel_of_net μ _ D γ β η δ κ hβ.le hlip S hS C n
        hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
      · intro p hp q hq
        by_contra hh
        exact hc (mem_iUnion₂.mpr ⟨(p,q),mem_product.mpr ⟨hp,hq⟩,le_of_not_gt hh⟩)
      · intro u hu v hv
        by_contra hh
        exact hm (mem_iUnion₂.mpr ⟨(u,v),mem_product.mpr ⟨hu,hv⟩,hh⟩)
    exact (measureReal_mono hsub).trans (measureReal_union_le _ _)
  exact squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) hbound
    (by simpa using hB.add hA)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_IntervalTravel
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

theorem segmentTube_translate_iff (a p q z : Vertex) (R : ℝ) :
    a+z ∈ SegmentTube (a+p) (a+q) R ↔ z ∈ SegmentTube p q R := by
  simp only [SegmentTube,mem_ofPred_eq,segmentPoint,latticeEmbed_add,
    add_sub_add_left_eq_sub]
  have he (t : ℝ) : latticeEmbed a+latticeEmbed z-
      (latticeEmbed a+latticeEmbed p+t • (latticeEmbed q-latticeEmbed p)) =
      latticeEmbed z-(latticeEmbed p+t • (latticeEmbed q-latticeEmbed p)) := by abel
  simp only [he]

theorem localTravel_translate_iff (μ : Plane → ℝ) (w : Edge → ℝ)
    (a p q : Vertex) (η δ s : ℝ) :
    LocalTravel μ η δ s p q (fun e => w (shiftEdge a e)) ↔
      LocalTravel μ η δ s (a+p) (a+q) w := by
  constructor
  · rintro ⟨ds,hd,hc,hin⟩
    refine ⟨ds,by rw [add_assoc,hd],?_,?_⟩
    · simpa only [pathCost_translate,add_sub_add_left_eq_sub] using hc
    · intro i hi
      rw [add_assoc,segmentTube_translate_iff]
      exact hin i hi
  · rintro ⟨ds,hd,hc,hin⟩
    refine ⟨ds,by simpa only [add_assoc,add_left_cancel_iff] using hd,?_,?_⟩
    · simpa only [pathCost_translate,add_sub_add_left_eq_sub] using hc
    · intro i hi
      have ht := hin i hi
      rw [add_assoc,segmentTube_translate_iff] at ht
      exact ht

theorem measurableSet_ballTravel (μ : Plane → ℝ) (D η δ s : ℝ) :
    MeasurableSet {w | BallTravel μ D η δ s w} := by
  simp only [BallTravel,ofPred_forall]
  exact MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun q =>
    MeasurableSet.iInter (fun _ => MeasurableSet.iInter (fun _ =>
      measurableSet_localTravel μ η δ s p q))))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem exponential_ball_travel (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ ε > 0, ∀ᶠ s : ℝ in atTop, ∀ a : Vertex,
      P.real {ω | ¬BallTravel μ D η δ s (fun e => τ (shiftEdge a e) ω)} < ε := by
  let _ := h.probability
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    ((exponential_ball_travel_nat h μ hμ ht D (η/2) (δ/2) hD (by linarith) (by linarith)).eventually
      (gt_mem_nhds hε))
  filter_upwards [eventually_ge_atTop (max 1 (N : ℝ))] with s hs
  intro a
  have he := translated_event_probability h a
    {w | ¬BallTravel μ D η δ s w} (measurableSet_ballTravel μ D η δ s).compl
  rw [show P.real {ω | ¬BallTravel μ D η δ s (fun e => τ (shiftEdge a e) ω)} =
      P.real {ω | ¬BallTravel μ D η δ s (fun e => τ e ω)} from congrArg ENNReal.toReal he]
  let n : ℕ := ⌈s⌉₊
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hs
  have hsn : s ≤ (n : ℝ) := Nat.le_ceil s
  have hnN : N ≤ n := by exact_mod_cast ((le_max_right _ _).trans hs).trans hsn
  have hnupper : (n : ℝ) ≤ 2*s := by
    have hh : (n : ℝ) < s+1 := Nat.ceil_lt_add_one (by linarith)
    linarith
  have hη' : (η/2)*(n : ℝ) ≤ η*s := by nlinarith
  have hδ' : (δ/2)*(n : ℝ) ≤ δ*s := by nlinarith
  refine (measureReal_mono (show {ω | ¬BallTravel μ D η δ s (fun e => τ e ω)} ⊆
      {ω | ¬BallTravel μ D (η/2) (δ/2) n (fun e => τ e ω)} from ?_)).trans_lt (hN n hnN)
  intro ω hb hg
  apply hb
  intro p q hp hq
  apply localTravel_mono μ _ p q hη' hδ'
  apply hg p q <;> nlinarith

theorem exponential_set_travel (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ ε > 0, ∀ᶠ s : ℝ in atTop, ∀ I J : Set Vertex,
      (∀ p ∈ I ∪ J, ∀ q ∈ I ∪ J, ‖latticeEmbed (q-p)‖ ≤ D*s) →
      P.real {ω | ¬∀ p ∈ I, ∀ q ∈ J,
        LocalTravel μ η δ s p q (fun e => τ e ω)} < ε := by
  let _ := h.probability
  intro ε hε
  filter_upwards [exponential_ball_travel h μ hμ ht D η δ hD hη hδ ε hε] with s hs
  intro I J hdiam
  by_cases hI : I.Nonempty
  · obtain ⟨a,ha⟩ := hI
    refine (measureReal_mono (show {ω | ¬∀ p ∈ I, ∀ q ∈ J, LocalTravel μ η δ s p q (fun e => τ e ω)} ⊆
        {ω | ¬BallTravel μ D η δ s (fun e => τ (shiftEdge a e) ω)} from ?_)).trans_lt (hs a)
    intro ω hb hg
    apply hb
    intro p hp q hq
    have hgood := hg (p-a) (q-a) (hdiam a (Or.inl ha) p (Or.inl hp))
      (hdiam a (Or.inl ha) q (Or.inr hq))
    have hh := (localTravel_translate_iff μ (fun e => τ e ω) a (p-a) (q-a) η δ s).mp hgood
    simpa only [add_sub_cancel] using hh
  · have he : I=∅ := Set.not_nonempty_iff_eq_empty.mp hI
    simpa [he] using hε

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ConnectorEvents
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set MeasureTheory Filter
open scoped Topology

theorem mem_allPairsRegionEvent (V : Finset Vertex) (I J : Set Vertex)
    (bound : Vertex → Vertex → ℝ) (w : Edge → ℝ) :
    w ∈ allPairsRegionEvent V I J bound ↔
      ∀ p ∈ I, ∀ q ∈ J, ∃ ds, p+displacement ds=q ∧
        PathIn p ds (V : Set Vertex) ∧ pathCost w p ds ≤ bound p q := by
  simp [allPairsRegionEvent,boundedLocalizedEvent]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem exponential_allPairsRegionEvent (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ ε > 0, ∀ᶠ s : ℝ in atTop, ∀ (V : Finset Vertex) (I J : Set Vertex)
      (bound : Vertex → Vertex → ℝ),
      (∀ p ∈ I ∪ J, ∀ q ∈ I ∪ J, ‖latticeEmbed (q-p)‖ ≤ D*s) →
      (∀ p ∈ I, ∀ q ∈ J, μ (latticeEmbed (q-p))+η*s ≤ bound p q) →
      (∀ p ∈ I, ∀ q ∈ J, SegmentTube p q (δ*s) ⊆ (V : Set Vertex)) →
      P.real {ω | (fun e => τ e ω) ∉ allPairsRegionEvent V I J bound} < ε := by
  let _ := h.probability
  intro ε hε
  filter_upwards [exponential_set_travel h μ hμ ht D η δ hD hη hδ ε hε] with s hs
  intro V I J bound hdiam hcost hregion
  refine (measureReal_mono (show {ω | (fun e => τ e ω) ∉ allPairsRegionEvent V I J bound} ⊆
    {ω | ¬∀ p ∈ I, ∀ q ∈ J, LocalTravel μ η δ s p q (fun e => τ e ω)} from ?_)).trans_lt
      (hs I J hdiam)
  intro ω hbad htravel
  apply hbad
  rw [mem_allPairsRegionEvent]
  intro p hp q hq
  obtain ⟨ds,hd,hc,hin⟩ := htravel p hp q hq
  refine ⟨ds,hd,?_,hc.trans (hcost p hp q hq)⟩
  intro i hi
  exact hregion p hp q hq (hin i hi)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ExtremeSlopes
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

theorem extreme_slopes_ordered (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ) :
    leftSlope φ ≤ rightSlope φ :=
  hφ.leftDeriv_le_rightDeriv_of_mem_interior (by simp)

theorem subgradient_of_between_slopes (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ)
    (a : ℝ) (hleft : leftSlope φ ≤ a) (hright : a ≤ rightSlope φ) :
    ∀ t, φ 0 + a * t ≤ φ t := by
  intro t
  rcases lt_trichotomy 0 t with ht | rfl | ht
  · have hbound := hφ.rightDeriv_le_slope_of_mem_interior (by simp) (by simp) ht
    have ha : a ≤ (φ t - φ 0) / t := by
      exact le_trans hright (by simpa [rightSlope, slope_def_field] using hbound)
    have := (le_div_iff₀ ht).mp ha
    linarith
  · simp
  · have hbound := hφ.slope_le_leftDeriv_of_mem_interior (by simp) (by simp) ht
    have ha : (φ 0 - φ t) / (0 - t) ≤ a := by
      exact le_trans (by simpa [leftSlope, slope_def_field] using hbound) hleft
    have := (div_le_iff₀ (show 0 < 0 - t by linarith)).mp ha
    linarith

theorem extreme_subgradients (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ) :
    (∀ t, φ 0 + leftSlope φ * t ≤ φ t) ∧
    (∀ t, φ 0 + rightSlope φ * t ≤ φ t) := by
  have horder := extreme_slopes_ordered φ hφ
  exact ⟨subgradient_of_between_slopes φ hφ _ le_rfl horder,
    subgradient_of_between_slopes φ hφ _ horder le_rfl⟩

theorem extreme_slopes_contact (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ) :
    HasDerivWithinAt φ (leftSlope φ) (Iio 0) 0 ∧
    HasDerivWithinAt φ (rightSlope φ) (Ioi 0) 0 := by
  exact ⟨hφ.hasDerivWithinAt_leftDeriv_of_mem_interior (by simp),
    hφ.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)⟩

theorem convex_transverse_profile {E : Type*} [AddCommGroup E] [Module ℝ E]
    (μ : E → ℝ) (u e : E)
    (hadd : ∀ z w, μ (z + w) ≤ μ z + μ w)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z) :
    ConvexOn ℝ univ (fun t : ℝ => μ (u + t • e)) := by
  refine ⟨convex_univ, ?_⟩
  intro v _ w _ a b ha hb hab
  simp only [smul_eq_mul]
  have heq : u + (a * v + b * w) • e = a • (u + v • e) + b • (u + w • e) := by
    rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm,
      ← add_smul, hab, one_smul, ← add_smul]
  rw [heq]
  exact (hadd _ _).trans_eq (by rw [hhom a ha, hhom b hb])

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_PlaneGeometry
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

theorem plane_reconstruction (b : ℝ) (z : Plane) :
    z = xCoord z • direction b + rCoord b z • transverseUnit := by
  ext i
  fin_cases i <;> simp [direction, transverseUnit, PiLp.add_apply, PiLp.smul_apply]
  ring

theorem norm_positive_homogeneous (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z := by
  intro t ht z
  rw [hμ.homogeneous, abs_of_nonneg ht]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SupportContactEstimate
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter
open scoped Topology

theorem derivative_remainder_radius (φ : ℝ → ℝ) (a : ℝ) (S : Set ℝ)
    (ha : HasDerivWithinAt φ a S 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ S, |t| ≤ r → |φ t-φ 0-a*t| ≤ ε*|t| := by
  have hh := ha.isLittleO.bound hε
  simp only [sub_zero,smul_eq_mul,Real.norm_eq_abs] at hh
  obtain ⟨r,hr,hh⟩ := Metric.mem_nhdsWithin_iff.mp hh
  refine ⟨r/2,by linarith,?_⟩
  intro t ht htr
  have hball : t ∈ Metric.ball 0 r := by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero]
    linarith
  simpa only [mem_ofPred_eq,mul_comm t a] using hh ⟨hball,ht⟩

theorem norm_extreme_support_contact (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (b : ℝ) (plus : Bool) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ contactSide plus, |t| ≤ r →
      0 ≤ μ (direction b+t • transverseUnit)-μ (direction b)-extremeSlope μ b plus*t ∧
      μ (direction b+t • transverseUnit)-μ (direction b)-extremeSlope μ b plus*t ≤ ε*|t| := by
  let φ := fun t : ℝ => μ (direction b+t • transverseUnit)
  have hφ := convex_transverse_profile μ (direction b) transverseUnit
    hμ.triangle (norm_positive_homogeneous μ hμ)
  have hc := extreme_slopes_contact φ hφ
  have hs := extreme_subgradients φ hφ
  have hd : HasDerivWithinAt φ (extremeSlope μ b plus) (contactSide plus) 0 := by
    cases plus <;> simp only [extremeSlope,contactSide,Bool.false_eq_true,ite_false,ite_true]
    · exact hc.1
    · exact hc.2
  obtain ⟨r,hr,hh⟩ := derivative_remainder_radius φ (extremeSlope μ b plus)
    (contactSide plus) hd ε hε
  refine ⟨r,hr,?_⟩
  intro t ht htr
  have he := (le_abs_self _).trans (hh t ht htr)
  have hl : φ 0+extremeSlope μ b plus*t ≤ φ t := by
    cases plus
    · exact hs.1 t
    · exact hs.2 t
  simp only [φ,zero_smul,add_zero] at he hl
  exact ⟨by linarith,he⟩

theorem connector_support_gap (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (b : ℝ) (plus : Bool) (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C) :
    ∃ D0 : ℝ, 1 ≤ D0 ∧ ∀ s : ℝ, 0 < s → ∀ z : Plane,
      D0*s ≤ xCoord z → rCoord b z ∈ contactSide plus → |rCoord b z| ≤ 3*C*s →
      μ z-(μ (direction b)*xCoord z+extremeSlope μ b plus*rCoord b z) ≤ ε*s/4 := by
  obtain ⟨r,hr,hcontact⟩ := norm_extreme_support_contact μ hμ b plus
    (ε/(12*C)) (by positivity)
  let D0 := max 1 (3*C/r)
  have hD : 1 ≤ D0 := le_max_left _ _
  have hCr : 3*C ≤ D0*r := (div_le_iff₀ hr).mp (le_max_right _ _)
  refine ⟨D0,hD,?_⟩
  intro s hs z hz hside htrans
  have hx : 0 < xCoord z := by nlinarith
  have hratio : rCoord b z / xCoord z ∈ contactSide plus := by
    cases plus <;> simp only [contactSide,Bool.false_eq_true,ite_false,ite_true,
      mem_Iio,mem_Ioi] at hside ⊢
    · exact div_neg_of_neg_of_pos hside hx
    · exact div_pos hside hx
  have hsmall : |rCoord b z/xCoord z| ≤ r := by
    rw [abs_div,abs_of_pos hx]
    apply (div_le_iff₀ hx).mpr
    have h1 := mul_le_mul_of_nonneg_right hCr hs.le
    have h2 := mul_le_mul_of_nonneg_left hz hr.le
    nlinarith
  have hg := (hcontact _ hratio hsmall).2
  have hrepr : z = xCoord z • (direction b+(rCoord b z/xCoord z) • transverseUnit) := by
    rw [smul_add,smul_smul]
    have he : xCoord z*(rCoord b z/xCoord z)=rCoord b z := by field_simp
    rw [he]
    exact plane_reconstruction b z
  have hnorm : μ z = xCoord z*μ (direction b+(rCoord b z/xCoord z) • transverseUnit) := by
    conv_lhs => rw [hrepr]
    rw [hμ.homogeneous,abs_of_pos hx]
  calc
    _ = xCoord z*(μ (direction b+(rCoord b z/xCoord z) • transverseUnit)-
        μ (direction b)-extremeSlope μ b plus*(rCoord b z/xCoord z)) := by
      rw [hnorm]
      field_simp
      ring
    _ ≤ xCoord z*(ε/(12*C)*|rCoord b z/xCoord z|) :=
      mul_le_mul_of_nonneg_left hg hx.le
    _ = ε/(12*C)*|rCoord b z| := by
      rw [abs_div,abs_of_pos hx]
      field_simp
    _ ≤ ε/(12*C)*(3*C*s) := mul_le_mul_of_nonneg_left htrans (by positivity)
    _ = ε*s/4 := by field_simp; ring

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ConnectorGeometry
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

theorem connector_transverse_displacement (b : ℝ) (X d : ℤ) (Y S σ a : ℝ)
    (hS : 0 ≤ S) (hσ : |σ|=1) (ha : 1 ≤ a ∧ a ≤ 2)
    (p q : Vertex) (hp : p ∈ connectorWindow b X Y S)
    (hq : q ∈ connectorWindow b (X+d) (Y+σ*a*S) S) :
    S/2 ≤ σ*(transverse b q-transverse b p) ∧
      σ*(transverse b q-transverse b p) ≤ 5*S/2 := by
  have hsq : σ*σ=1 := by nlinarith [sq_abs σ]
  have hep := hp.2
  have heq := hq.2
  have hp' : |σ*(transverse b p-Y)| ≤ S/4 := by simpa [abs_mul,hσ] using hep
  have hq' : |σ*(transverse b q-(Y+σ*a*S))| ≤ S/4 := by simpa [abs_mul,hσ] using heq
  have he : σ*(transverse b q-transverse b p) =
      σ*(transverse b q-(Y+σ*a*S))-σ*(transverse b p-Y)+a*S := by
    calc
      _ = σ*(transverse b q-(Y+σ*a*S))-σ*(transverse b p-Y)+(σ*σ)*(a*S) := by ring
      _ = _ := by rw [hsq]; ring
  rw [he]
  obtain ⟨hp₀,hp₁⟩ := abs_le.mp hp'
  obtain ⟨hq₀,hq₁⟩ := abs_le.mp hq'
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right ha.1 hS,
    mul_le_mul_of_nonneg_right ha.2 hS]

theorem connector_window_bounds (b : ℝ) (X d : ℤ) (Y S σ a : ℝ)
    (hd : 0 ≤ d) (hS : 0 ≤ S) (hσ : |σ|=1) (ha : 1 ≤ a ∧ a ≤ 2)
    (p : Vertex) (hp : p ∈ connectorWindow b X Y S ∪
      connectorWindow b (X+d) (Y+σ*a*S) S) :
    (X : ℝ) ≤ p.1 ∧ (p.1 : ℝ) ≤ (X : ℝ)+d ∧
      |transverse b p-Y| ≤ 9*S/4 := by
  have hd' : (0 : ℝ) ≤ d := by exact_mod_cast hd
  rcases hp with hp | hp
  · refine ⟨by simp [hp.1],?_,?_⟩
    · simp only [hp.1]; linarith
    · linarith [hp.2]
  · refine ⟨?_,by simp [hp.1],?_⟩
    · simp only [hp.1,Int.cast_add]; linarith
    · have hh := abs_add_le (transverse b p-(Y+σ*a*S)) (σ*a*S)
      have he : transverse b p-(Y+σ*a*S)+σ*a*S=transverse b p-Y := by ring
      rw [he,abs_mul,abs_mul,hσ,one_mul,abs_of_nonneg (by linarith : 0 ≤ a),abs_of_nonneg hS] at hh
      nlinarith [hp.2,mul_le_mul_of_nonneg_right ha.2 hS]

theorem transverse_plane_lipschitz (b : ℝ) (hb : |b| ≤ 1) (z : Plane) :
    |rCoord b z| ≤ 2*‖z‖ := by
  have hh := abs_sub_le (z 1) 0 (b*z 0)
  simp only [sub_zero,zero_sub,abs_neg,abs_mul] at hh
  have hc₀ := plane_coordinate_le_norm z 0
  have hc₁ := plane_coordinate_le_norm z 1
  have hm := mul_le_mul_of_nonneg_right hb (abs_nonneg (z 0))
  change |z 1-b*z 0| ≤ _
  nlinarith

theorem plane_norm_le_shear (b : ℝ) (hb : |b| ≤ 1) (z : Plane) :
    ‖z‖ ≤ 2*|xCoord z|+|rCoord b z| := by
  have hh := abs_add_le (rCoord b z) (b*z 0)
  have he : rCoord b z+b*z 0=z 1 := by simp [rCoord_apply]
  rw [he,abs_mul] at hh
  have hm := mul_le_mul_of_nonneg_right hb (abs_nonneg (z 0))
  have hn := plane_norm_le_coordinates z
  change ‖z‖ ≤ 2*|z 0|+|rCoord b z|
  linarith

theorem connector_union_diameter (b : ℝ) (hb : |b| ≤ 1)
    (X d : ℤ) (Y S σ a : ℝ) (hd : 0 ≤ d) (hS : 0 ≤ S)
    (hσ : |σ|=1) (ha : 1 ≤ a ∧ a ≤ 2)
    (p q : Vertex)
    (hp : p ∈ connectorWindow b X Y S ∪ connectorWindow b (X+d) (Y+σ*a*S) S)
    (hq : q ∈ connectorWindow b X Y S ∪ connectorWindow b (X+d) (Y+σ*a*S) S) :
    ‖latticeEmbed (q-p)‖ ≤ 2*(d : ℝ)+9*S/2 := by
  obtain ⟨hp₀,hp₁,hp₂⟩ := connector_window_bounds b X d Y S σ a hd hS hσ ha p hp
  obtain ⟨hq₀,hq₁,hq₂⟩ := connector_window_bounds b X d Y S σ a hd hS hσ ha q hq
  have hx : |xCoord (latticeEmbed (q-p))| ≤ (d : ℝ) := by
    change |((q-p).1 : ℝ)| ≤ _
    simp only [Prod.fst_sub,Int.cast_sub]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hr : |rCoord b (latticeEmbed (q-p))| ≤ 9*S/2 := by
    have hh := abs_sub_le (transverse b q-Y) 0 (transverse b p-Y)
    simp only [sub_zero,zero_sub,abs_neg] at hh
    have he : rCoord b (latticeEmbed (q-p))=(transverse b q-Y)-(transverse b p-Y) := by
      simp [rCoord_apply,latticeEmbed,transverse]; ring
    rw [he]
    linarith
  exact (plane_norm_le_shear b hb _).trans (by linarith)

theorem connector_tube_containment (b : ℝ) (hb : |b| ≤ 1)
    (X d : ℤ) (Y S s σ a : ℝ) (hd : 0 ≤ d) (hs : 0 ≤ s) (hS : s ≤ S)
    (hσ : |σ|=1) (ha : 1 ≤ a ∧ a ≤ 2)
    (p q : Vertex) (hp : p ∈ connectorWindow b X Y S)
    (hq : q ∈ connectorWindow b (X+d) (Y+σ*a*S) S) :
    SegmentTube p q (s/2) ⊆ (connectorVertices b X d Y S s : Set Vertex) := by
  have hS0 : 0 ≤ S := hs.trans hS
  obtain ⟨hp₀,hp₁,hp₂⟩ := connector_window_bounds b X d Y S σ a hd hS0 hσ ha p (Or.inl hp)
  obtain ⟨hq₀,hq₁,hq₂⟩ := connector_window_bounds b X d Y S σ a hd hS0 hσ ha q (Or.inr hq)
  intro z hz
  obtain ⟨t,ht₀,ht₁,ht⟩ := hz
  have hsegx : xCoord (segmentPoint p q t)=(1-t)*(p.1 : ℝ)+t*(q.1 : ℝ) := by
    simp [segmentPoint,latticeEmbed,xCoord_apply,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply]
    ring
  have hsegr : rCoord b (segmentPoint p q t)-Y=
      (1-t)*(transverse b p-Y)+t*(transverse b q-Y) := by
    simp [segmentPoint,latticeEmbed,rCoord_apply,transverse,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply]
    ring
  have hseg₀ : (X : ℝ) ≤ xCoord (segmentPoint p q t) := by
    rw [hsegx]
    nlinarith [mul_le_mul_of_nonneg_left hp₀ (by linarith : 0 ≤ 1-t),
      mul_le_mul_of_nonneg_left hq₀ ht₀]
  have hseg₁ : xCoord (segmentPoint p q t) ≤ (X : ℝ)+d := by
    rw [hsegx]
    nlinarith [mul_le_mul_of_nonneg_left hp₁ (by linarith : 0 ≤ 1-t),
      mul_le_mul_of_nonneg_left hq₁ ht₀]
  have hseg₂ : |rCoord b (segmentPoint p q t)-Y| ≤ 9*S/4 := by
    rw [hsegr]
    have hh := abs_add_le ((1-t)*(transverse b p-Y)) (t*(transverse b q-Y))
    rw [abs_mul,abs_mul,abs_of_nonneg ht₀,abs_of_nonneg (by linarith : 0 ≤ 1-t)] at hh
    nlinarith [mul_le_mul_of_nonneg_left hp₂ (by linarith : 0 ≤ 1-t),
      mul_le_mul_of_nonneg_left hq₂ ht₀]
  have hx := (plane_coordinate_le_norm (latticeEmbed z-segmentPoint p q t) 0).trans ht
  have hr := (transverse_plane_lipschitz b hb (latticeEmbed z-segmentPoint p q t)).trans
    (mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 2))
  have hx' : |(z.1 : ℝ)-xCoord (segmentPoint p q t)| ≤ s/2 := by
    simpa [latticeEmbed,PiLp.sub_apply] using hx
  have hr' : |transverse b z-rCoord b (segmentPoint p q t)| ≤ s := by
    have he : 2*(s/2)=s := by ring
    simpa [map_sub,rCoord_apply,latticeEmbed,transverse,he] using hr
  change z ∈ connectorVertices b X d Y S s
  rw [mem_connectorVertices]
  refine ⟨?_,?_,?_⟩
  · linarith [(abs_le.mp hx').1]
  · linarith [(abs_le.mp hx').2]
  · have hh := abs_add_le (transverse b z-rCoord b (segmentPoint p q t))
      (rCoord b (segmentPoint p q t)-Y)
    rw [sub_add_sub_cancel] at hh
    linarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ConnectorProbability
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology

theorem contactSide_of_sign (plus : Bool) (r : ℝ) (hr : 0 < contactSign plus*r) :
    r ∈ contactSide plus := by
  cases plus <;> simpa [contactSign,contactSide] using hr

theorem trialWindow_scale_bounds (M : ℕ) (hM : 0 < M) (R s : ℝ)
    (hR : 0 ≤ R) (hs : 1 ≤ s) :
    s ≤ trialWindow M R s ∧ trialWindow M R s ≤ (200*M*(R+1))*s := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hc := Nat.le_ceil s
  have hc' := Nat.ceil_lt_add_one (by linarith : 0 ≤ s)
  have hbase : s ≤ (R+1)*(⌈s⌉₊ : ℝ) := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hM' (by positivity : 0 ≤ (R+1)*(⌈s⌉₊ : ℝ))
  have hupper := mul_le_mul_of_nonneg_left (show (⌈s⌉₊ : ℝ) ≤ 2*s by linarith)
    (show 0 ≤ 100*(M : ℝ)*(R+1) by positivity)
  unfold trialWindow trialSpacing
  constructor <;> nlinarith

theorem exponential_source_connector_test_oai {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {τ : Edge → Ω → ℝ} (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b : ℝ) (hb : |b| ≤ 1) (plus : Bool) (M : ℕ) (hM : 0 < M)
    (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ D0 : ℝ, 1 ≤ D0 ∧ ∀ κ > 0, ∀ᶠ s : ℝ in atTop,
      ∀ X : ℤ, ∀ Y a : ℝ, 1 ≤ a → a ≤ 2 →
      P.real {ω | (fun e => τ e ω) ∉ allPairsRegionEvent
        (connectorVertices b X ⌈D0*s⌉ Y (trialWindow M R s) s)
        (connectorWindow b X Y (trialWindow M R s))
        (connectorWindow b (X+⌈D0*s⌉)
          (Y+contactSign plus*a*trialWindow M R s) (trialWindow M R s))
        (sourceSupportCost μ b plus ε s)} < κ := by
  let C : ℝ := 200*M*(R+1)
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨D0,hD0,hgap⟩ := connector_support_gap μ hμ b plus ε C hε hC
  let D := 2*(D0+1)+9*C/2
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨D0,hD0,?_⟩
  intro κ hκ
  filter_upwards [exponential_allPairsRegionEvent h μ hμ ht D (ε/4) (1/2)
    hD (by positivity) (by norm_num) κ hκ,eventually_ge_atTop (1 : ℝ)] with s hs hs1
  intro X Y a ha₀ ha₁
  let S := trialWindow M R s
  let d : ℤ := ⌈D0*s⌉
  have hs0 : 0 < s := by linarith
  have hSb := trialWindow_scale_bounds M hM R s hR hs1
  have hS : s ≤ S := hSb.1
  have hSC : S ≤ C*s := hSb.2
  have hS0 : 0 < S := hs0.trans_le hS
  have hdlo : D0*s ≤ (d : ℝ) := Int.le_ceil _
  have hdhi : (d : ℝ) ≤ (D0+1)*s := by
    have hh : (d : ℝ) < D0*s+1 := Int.ceil_lt_add_one _
    nlinarith
  have hd0 : 0 ≤ d := by
    have : (0 : ℝ) ≤ d := by nlinarith
    exact_mod_cast this
  apply hs
  · intro p hp q hq
    exact (connector_union_diameter b hb X d Y S (contactSign plus) a hd0 hS0.le
      (abs_contactSign plus) ⟨ha₀,ha₁⟩ p q hp hq).trans (by dsimp [D]; nlinarith)
  · intro p hp q hq
    have hx : xCoord (latticeEmbed (q-p))=(d : ℝ) := by
      change ((q-p).1 : ℝ)=_
      rw [Prod.fst_sub,hp.1,hq.1]
      congr 1
      omega
    have hr : rCoord b (latticeEmbed (q-p))=transverse b q-transverse b p := by
      simp [rCoord_apply,latticeEmbed,transverse]; ring
    have htrans := connector_transverse_displacement b X d Y S (contactSign plus) a
      hS0.le (abs_contactSign plus) ⟨ha₀,ha₁⟩ p q hp hq
    have hpos : 0 < contactSign plus*rCoord b (latticeEmbed (q-p)) := by
      rw [hr]; linarith [htrans.1]
    have habs : |rCoord b (latticeEmbed (q-p))| ≤ 3*C*s := by
      have he : |rCoord b (latticeEmbed (q-p))| =
          contactSign plus*rCoord b (latticeEmbed (q-p)) := by
        calc
          _ = |contactSign plus*rCoord b (latticeEmbed (q-p))| := by simp [abs_mul]
          _ = _ := abs_of_pos hpos
      rw [he,hr]
      nlinarith [htrans.2]
    have hg := hgap s hs0 (latticeEmbed (q-p)) (by rw [hx]; exact hdlo)
      (contactSide_of_sign plus _ hpos) habs
    unfold sourceSupportCost
    linarith
  · intro p hp q hq
    simpa only [one_div,mul_comm (2⁻¹ : ℝ) s,← div_eq_mul_inv] using
      connector_tube_containment b hb X d Y S s (contactSign plus) a hd0 hs0.le hS
        (abs_contactSign plus) ⟨ha₀,ha₁⟩ p q hp hq

end PlanarFPP

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PlanarFPP.exponential_source_connector_test_oai.{u_1} := @OAI.PlanarFPP.exponential_source_connector_test_oai.{u_1}
