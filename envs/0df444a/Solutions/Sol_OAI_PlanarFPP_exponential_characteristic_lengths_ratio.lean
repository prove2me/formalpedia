-- Prove2me | solution 1 for OAI.PlanarFPP.exponential_characteristic_lengths_ratio
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:45:08.110988+00:00
-- url     : https://prove2.me/submissions/563fe019-998e-4f25-a640-94b2c5f16a18

import Mathlib
import Definitions.Def_PlanarFirstPassage
import Definitions.Def_OAISPf002
import Theorems.Thm_OAI_PlanarFPP_exponential_characteristic_lengths_exist

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

theorem measurableSet_strict_path_event (hτ : ∀ e, Measurable (τ e))
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    MeasurableSet {ω | ∃ p ds, family p ds ∧
      pathCost (fun e => τ e ω) p ds < bound p ds} := by
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro p
  apply MeasurableSet.iUnion
  intro ds
  by_cases hf : family p ds
  · simpa only [hf, true_and] using
      measurableSet_lt (measurable_pathCost hτ p ds) measurable_const
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

theorem exponential_local_travel (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (D η δ : ℝ) (hD : 0 < D) (hη : 0 < η) (hδ : 0 < δ) :
    ∀ ε > 0, ∀ᶠ s : ℝ in atTop, ∀ p q : Vertex, ‖latticeEmbed (q-p)‖ ≤ D*s →
      P.real {ω | ¬LocalTravel μ η δ s p q (fun e => τ e ω)} < ε := by
  let _ := h.probability
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (exponential_local_travel_nat h μ hμ ht D (η/2) (δ/2) hD (by linarith) (by linarith) ε hε)
  filter_upwards [eventually_ge_atTop (max 1 (N : ℝ))] with s hs
  intro p q hpq
  let n : ℕ := ⌈s⌉₊
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hs
  have hsn : s ≤ (n : ℝ) := Nat.le_ceil s
  have hnN : N ≤ n := by exact_mod_cast ((le_max_right _ _).trans hs).trans hsn
  have hnupper : (n : ℝ) ≤ 2*s := by
    have ht : (n : ℝ) < s+1 := Nat.ceil_lt_add_one (by linarith)
    linarith
  have hdist : ‖latticeEmbed (q-p)‖ ≤ D*n :=
    hpq.trans (mul_le_mul_of_nonneg_left hsn hD.le)
  have hη' : (η/2)*(n : ℝ) ≤ η*s := by
    have := mul_le_mul_of_nonneg_left hnupper hη.le
    linarith
  have hδ' : (δ/2)*(n : ℝ) ≤ δ*s := by
    have := mul_le_mul_of_nonneg_left hnupper hδ.le
    linarith
  refine (measureReal_mono (show {ω | ¬LocalTravel μ η δ s p q (fun e => τ e ω)} ⊆
      {ω | ¬LocalTravel μ (η/2) (δ/2) n p q (fun e => τ e ω)} from ?_)).trans_lt (hN n hnN p q hdist)
  intro ω hbad hgood
  exact hbad (localTravel_mono μ _ p q hη' hδ' hgood)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_LocalizedEvents
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

theorem measurableSet_strictLocalizedEvent (V : Finset Vertex)
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    MeasurableSet (strictLocalizedEvent V family bound) := by
  simpa only [strictLocalizedEvent,and_assoc] using
    measurableSet_strict_path_event (τ := fun e (w : Edge → ℝ) => w e) measurable_pi_apply
      (fun p ds => family p ds ∧ PathIn p ds (V : Set Vertex)) bound

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

theorem transverse_plane_lipschitz (b : ℝ) (hb : |b| ≤ 1) (z : Plane) :
    |rCoord b z| ≤ 2*‖z‖ := by
  have hh := abs_sub_le (z 1) 0 (b*z 0)
  simp only [sub_zero,zero_sub,abs_neg,abs_mul] at hh
  have hc₀ := plane_coordinate_le_norm z 0
  have hc₁ := plane_coordinate_le_norm z 1
  have hm := mul_le_mul_of_nonneg_right hb (abs_nonneg (z 0))
  change |z 1-b*z 0| ≤ _
  nlinarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_CrossingTilt
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem measurableSet_crossingEvent (b m K s : ℝ) (n : ℤ) (t : Vertex) :
    MeasurableSet (crossingEvent b m K s n t) := measurableSet_strictLocalizedEvent _ _ _

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ShortCrossingGeometry
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

theorem sourceEndpoint_transverse (b : ℝ) (n : ℤ) :
    |transverse b (sourceEndpoint b n)| ≤ 1 := by
  have hl := Int.floor_le (b*n)
  have hu := Int.lt_floor_add_one (b*n)
  simp only [sourceEndpoint,transverse]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem sourceEndpoint_distance (b : ℝ) (n : ℤ) (hb : |b| ≤ 1) (hn : 1 ≤ n) :
    ‖latticeEmbed (sourceEndpoint b n)‖ ≤ 3*(n : ℝ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr := sourceEndpoint_transverse b n
  have ht := abs_add_le (transverse b (sourceEndpoint b n)) (b*(n : ℝ))
  have he : transverse b (sourceEndpoint b n)+b*(n : ℝ)=(⌊b*n⌋ : ℝ) := by
    simp [transverse,sourceEndpoint]
  rw [he,abs_mul,abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)] at ht
  have hm := mul_le_mul_of_nonneg_right hb (by linarith : (0 : ℝ) ≤ n)
  have hh := plane_norm_le_coordinates (latticeEmbed (sourceEndpoint b n))
  change ‖latticeEmbed (sourceEndpoint b n)‖ ≤ |(n : ℝ)|+|(⌊b*n⌋ : ℝ)| at hh
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)] at hh
  linarith

theorem sourceEndpoint_norm_cost (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (b : ℝ) (n : ℤ) (hn : 0 ≤ n) :
    μ (latticeEmbed (sourceEndpoint b n)) ≤ μ (direction b)*(n : ℝ)+μ transverseUnit := by
  let r := transverse b (sourceEndpoint b n)
  have he : latticeEmbed (sourceEndpoint b n)=(n : ℝ) • direction b+r • transverseUnit := by
    ext i
    fin_cases i <;> simp [r,sourceEndpoint,transverse,latticeEmbed,direction,transverseUnit,
      PiLp.add_apply,PiLp.smul_apply]
    ring
  rw [he]
  have hh := hμ.triangle ((n : ℝ) • direction b) (r • transverseUnit)
  rw [hμ.homogeneous,hμ.homogeneous,abs_of_nonneg (by exact_mod_cast hn : (0 : ℝ) ≤ n)] at hh
  have hr := mul_le_mul_of_nonneg_right (sourceEndpoint_transverse b n) (hμ.nonneg transverseUnit)
  dsimp [r] at hh
  linarith

theorem sourceEndpoint_tube_containment (b C δ s : ℝ) (n : ℤ)
    (hb : |b| ≤ 1) (hs : 1 ≤ s) (hn : 1 ≤ n) (hns : (n : ℝ) ≤ C*s)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1/4) (hδC : δ*C ≤ 1/2) :
    SegmentTube 0 (sourceEndpoint b n) (δ*n) ⊆ rareFastRegion b 1 8 s n 0 := by
  rintro z ⟨t,ht0,ht1,hd⟩
  let u := latticeEmbed z-segmentPoint 0 (sourceEndpoint b n) t
  have hnorm : ‖u‖ ≤ δ*n := hd
  have hx : u 0=(z.1 : ℝ)-t*n := by
    simp [u,segmentPoint,sourceEndpoint,latticeEmbed,PiLp.sub_apply,PiLp.smul_apply]
  have hr : rCoord b u=transverse b z-t*transverse b (sourceEndpoint b n) := by
    simp [u,segmentPoint,sourceEndpoint,latticeEmbed,transverse,rCoord_apply,PiLp.sub_apply,PiLp.smul_apply]
    ring
  have hxbound := (plane_coordinate_le_norm u 0).trans hnorm
  rw [hx] at hxbound
  have hx' := abs_le.mp hxbound
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hδn : δ*(n : ℝ) ≤ n/4 := by nlinarith
  have htn : t*(n : ℝ) ≤ n := by nlinarith
  have htn0 : 0 ≤ t*(n : ℝ) := by positivity
  have hrbound := transverse_plane_lipschitz b hb u
  rw [hr] at hrbound
  have hseg : |t*transverse b (sourceEndpoint b n)| ≤ 1 := by
    rw [abs_mul,abs_of_nonneg ht0]
    nlinarith [sourceEndpoint_transverse b n]
  have hsum := abs_add_le (transverse b z-t*transverse b (sourceEndpoint b n))
    (t*transverse b (sourceEndpoint b n))
  rw [sub_add_cancel] at hsum
  have hscale := mul_le_mul_of_nonneg_left hns hδ
  have hscale' := mul_le_mul_of_nonneg_right hδC (by linarith : 0 ≤ s)
  refine ⟨?_,?_,?_⟩
  · simp only [sub_zero,neg_one_mul]
    linarith
  · norm_num only [sub_zero,one_add_one_eq_two]
    linarith
  · simp only [sub_zero]
    nlinarith

theorem horizontal_in_crossingRegion (b s : ℝ) (n : ℤ) (hb : |b| ≤ 1)
    (hn : 0 ≤ n) (hns : (n : ℝ) ≤ 8*s) :
    PathIn 0 (horizontal n) (rareFastRegion b 1 8 s n 0) := by
  intro i _
  have he : displacement ((horizontal n).take i)=(((min i n.toNat : ℕ) : ℤ),0) := by
    simp [horizontal,hn,displacement,Step.delta]
  have hm : (min i n.toNat : ℤ) ≤ n := by
    have := min_le_right i n.toNat
    exact_mod_cast (show (min i n.toNat : ℤ) ≤ n by omega)
  have hm0 : (0 : ℤ) ≤ min i n.toNat := by positivity
  have hm' : ((min i n.toNat : ℕ) : ℝ) ≤ n := by exact_mod_cast hm
  have hm0' : (0 : ℝ) ≤ min i n.toNat := by positivity
  rw [he]
  simp only [zero_add,rareFastRegion,mem_ofPred_eq,sub_zero,transverse,Int.cast_natCast,
    Int.cast_zero,zero_sub,abs_neg,abs_mul,abs_of_nonneg hm0',neg_one_mul,one_add_one_eq_two]
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_right hb hm0'
  exact ⟨by linarith,by linarith,by linarith⟩

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ShortCrossingProbability
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem exponential_bounded_crossing_failure (h : ExponentialEnvironment P τ)
    (b m K s N : ℝ) (n : ℤ) (hb : |b| ≤ 1) (hm : 0 ≤ m)
    (hn : 0 ≤ n) (hnN : (n : ℝ) ≤ N) (hns : (n : ℝ) ≤ 8*s) :
    P.real {ω | (fun e => τ e ω) ∉ crossingEvent b m K s n 0} ≤
      Real.exp (-(K*s-4*N)/2) := by
  let _ := h.probability
  have hsub : {ω | (fun e => τ e ω) ∉ crossingEvent b m K s n 0} ⊆
      {ω | 4*(n.natAbs : ℝ)+(K*s-4*N) ≤ pathCost (fun e => τ e ω) 0 (horizontal n)} := by
    intro ω hbad
    have hc : m*n+K*s ≤ pathCost (fun e => τ e ω) 0 (horizontal n) := by
      by_contra hh
      apply hbad
      refine ⟨0,horizontal n,⟨rfl,?_⟩,?_,lt_of_not_ge hh⟩
      · simp [displacement_horizontal]
      · intro i hi
        exact (mem_rareFastVertices ..).mpr (horizontal_in_crossingRegion b s n hb hn hns i hi)
    have ha : (n.natAbs : ℝ)=(n : ℝ) := by
      have hi : (n.natAbs : ℤ)=n := by omega
      exact (by simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) hi)
    have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
    change 4*(n.natAbs : ℝ)+(K*s-4*N) ≤ pathCost (fun e => τ e ω) 0 (horizontal n)
    rw [ha]
    nlinarith
  exact (measureReal_mono hsub).trans (costly_horizontal_excess_probability_real h 0 n (K*s-4*N))

theorem exponential_short_crossing_failure (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b K C : ℝ) (hb : |b| ≤ 1) (hK : 0 < K) (hC : 0 < C) :
    ∀ κ > 0, ∀ᶠ s : ℝ in atTop, ∀ n : ℤ, 1 ≤ n → (n : ℝ) ≤ C*s →
      P.real {ω | (fun e => τ e ω) ∉ crossingEvent b (μ (direction b)) K s n 0} < κ := by
  let _ := h.probability
  let η := K/(4*C)
  let δ := min (1/4) (1/(2*C))
  have hη : 0 < η := by dsimp [η]; positivity
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1/4 := min_le_left _ _
  have hδC : δ*C ≤ 1/2 := by
    have hh := min_le_right (1/4 : ℝ) (1/(2*C))
    have he : δ ≤ (1/2)/C := by
      have heq : (1 : ℝ)/(2*C)=(1/2)/C := by ring
      rw [← heq]
      exact hh
    exact (le_div_iff₀ hC).mp he
  intro κ hκ
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (exponential_local_travel h μ hμ ht 3 η δ (by norm_num) hη hδ κ hκ)
  have htail : ∀ᶠ s : ℝ in atTop, Real.exp (-(K*s-4*N)/2) < κ := by
    filter_upwards [eventually_ge_atTop ((4*N-2*Real.log κ+2)/K)] with s hs
    have hh := (div_le_iff₀ hK).mp hs
    rw [← Real.exp_log hκ]
    apply Real.exp_lt_exp.mpr
    linarith
  filter_upwards [eventually_ge_atTop (1 : ℝ),eventually_ge_atTop N,
    eventually_ge_atTop ((4*μ transverseUnit+1)/K),htail] with s hs hsN hsμ htail
  intro n hn hns
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases hnN : N ≤ (n : ℝ)
  · have hlt := hN n hnN 0 (sourceEndpoint b n) (by
      simpa only [sub_zero] using sourceEndpoint_distance b n hb hn)
    have hsub : {ω | (fun e => τ e ω) ∉ crossingEvent b (μ (direction b)) K s n 0} ⊆
        {ω | ¬LocalTravel μ η δ n 0 (sourceEndpoint b n) (fun e => τ e ω)} := by
      intro ω hbad hgood
      obtain ⟨ds,hd,hcost,hin⟩ := hgood
      apply hbad
      refine ⟨0,ds,⟨rfl,?_⟩,?_,?_⟩
      · simpa [sourceEndpoint] using congrArg Prod.fst hd
      · intro i hi
        exact (mem_rareFastVertices ..).mpr
          (sourceEndpoint_tube_containment b C δ s n hb hs hn hns hδ.le hδ1 hδC (hin i hi))
      · have hμbound := sourceEndpoint_norm_cost μ hμ b n (by omega)
        have hηn : η*(n : ℝ) ≤ K*s/4 := by
          dsimp [η]
          calc
            _ ≤ K/(4*C)*(C*s) := mul_le_mul_of_nonneg_left hns hη.le
            _ = _ := by field_simp
        have hh := (div_le_iff₀ hK).mp hsμ
        simp only [sub_zero] at hcost
        change pathCost (fun e => τ e ω) 0 ds < μ (direction b)*n+K*s
        linarith [hμ.nonneg transverseUnit]
    exact (measureReal_mono hsub).trans_lt hlt
  · exact (exponential_bounded_crossing_failure h b (μ (direction b)) K s N n hb (hμ.nonneg _)
      (by omega) (le_of_not_ge hnN) (by linarith)).trans_lt htail

theorem exponential_short_crossing_probability (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b K C : ℝ) (hb : |b| ≤ 1) (hK : 0 < K) (hC : 0 < C) :
    ∀ q < 1, ∀ᶠ s : ℝ in atTop, ∀ n : ℤ, 1 ≤ n → (n : ℝ) ≤ C*s →
      q < P.real {ω | (fun e => τ e ω) ∈ crossingEvent b (μ (direction b)) K s n 0} := by
  let _ := h.probability
  intro q hq
  filter_upwards [exponential_short_crossing_failure h μ hμ ht b K C hb hK hC (1-q) (by linarith)] with s hs
  intro n hn hns
  have hh := hs n hn hns
  have hc := measureReal_compl (μ := P) ((measurableSet_crossingEvent b (μ (direction b)) K s n 0).preimage
    (Measurable.of_eval h.measurable))
  change P.real {ω | (fun e => τ e ω) ∉ crossingEvent b (μ (direction b)) K s n 0} = _ at hc
  rw [hc] at hh
  simpa [Set.preimage] using hh

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_CharacteristicLengths
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (τ : Edge → Ω → ℝ)

variable {P τ}

theorem characteristicLength_pos (μ : Plane → ℝ) (b q : ℝ) (k : ℕ) :
    0 < characteristicLength P τ μ b q k := by unfold characteristicLength; positivity

theorem exponential_characteristic_lengths_ratio_oai (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b q : ℝ) (hb : |b| ≤ 1) (hq : 0 < q) (hq1 : q < 1) :
    Tendsto (fun k : ℕ => (characteristicLength P τ μ b q k : ℝ)/(2 : ℝ)^k) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  let C := max 1 B
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hK : 0 < sourceCrossingK μ b := by unfold sourceCrossingK; positivity
  have hs := exponential_short_crossing_probability h μ hμ ht b (sourceCrossingK μ b) C hb hK hC q hq1
  have h2 := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ)<2)
  filter_upwards [h2.eventually hs,exponential_characteristic_lengths_exist h μ hμ ht b q hb hq] with k hk he
  have hL : 1 ≤ characteristicLength P τ μ b q k := characteristicLength_pos μ b q k
  have hgt : C*(2 : ℝ)^k < (characteristicLength P τ μ b q k : ℝ) := by
    by_contra hn
    exact (not_lt_of_ge he.2) (hk _ hL (le_of_not_gt hn))
  have hr : C < (characteristicLength P τ μ b q k : ℝ)/(2 : ℝ)^k :=
    (lt_div_iff₀ (by positivity)).mpr hgt
  exact (le_max_right _ _).trans hr.le

end PlanarFPP

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PlanarFPP.exponential_characteristic_lengths_ratio_oai.{u_1} := @OAI.PlanarFPP.exponential_characteristic_lengths_ratio_oai.{u_1}
