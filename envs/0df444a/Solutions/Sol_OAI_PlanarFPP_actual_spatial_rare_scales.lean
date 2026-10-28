-- Prove2me | solution 1 for OAI.PlanarFPP.actual_spatial_rare_scales
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:42:33.665985+00:00
-- url     : https://prove2.me/submissions/62fb9dae-e338-4c2b-a007-e6a097be6dcc

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFirstPassage
import Definitions.Def_OAISPf002
import Theorems.Thm_OAI_PlanarFPP_actualSourceTimeConstant_lattice_limits
import Theorems.Thm_OAI_PlanarFPP_actual_grid_trial_probabilities
import Theorems.Thm_OAI_PlanarFPP_exponential_arbitraryEndpoint_tendsto_of_grids
import Theorems.Thm_OAI_PlanarFPP_exponential_characteristic_lengths_exist
import Theorems.Thm_OAI_PlanarFPP_exponential_characteristic_lengths_ratio

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
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
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

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_RealScaleConnections
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory Filter Set
open scoped Topology

lemma lattice_mem_box_of_norm (p : Vertex) (n : ℕ) (hp : ‖latticeEmbed p‖ ≤ n) :
    p ∈ latticeBox n := by
  have hi (i : Fin 2) := (plane_coordinate_le_norm (latticeEmbed p) i).trans hp
  have h₁ : |p.1| ≤ (n : ℤ) := by exact_mod_cast (show |(p.1 : ℝ)| ≤ n from hi 0)
  have h₂ : |p.2| ≤ (n : ℤ) := by exact_mod_cast (show |(p.2 : ℝ)| ≤ n from hi 1)
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (abs_le.mp h₁),Finset.mem_Icc.mpr (abs_le.mp h₂)⟩

theorem real_scale_connections (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (hc : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime w p q < 4*(latticeDistance p q : ℝ)+(1/(k+1 : ℝ))*n)
    (C : ℝ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ p q : Vertex,
      ‖latticeEmbed p‖ ≤ C*t → ‖latticeEmbed q‖ ≤ C*t →
      |passageTime w 0 p/t-passageTime w 0 q/t| ≤
        4*(latticeDistance p q : ℝ)/t+ε := by
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt (div_pos hε (show 0 < C+1 by linarith))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hc k)
  filter_upwards [eventually_ge_atTop (max 1 ((N : ℝ)/C))] with t ht
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := by linarith
  let n : ℕ := ⌈C*t⌉₊
  have htn : C*t ≤ (n : ℝ) := Nat.le_ceil _
  have hnu : (n : ℝ) ≤ (C+1)*t := by
    have he := Nat.ceil_lt_add_one (show 0 ≤ C*t by positivity)
    dsimp [n]
    nlinarith
  have hnN : N ≤ n := by
    have hh := (div_le_iff₀ hC).mp ((le_max_right _ _).trans ht)
    have hh' : (N : ℝ) ≤ (n : ℝ) := by nlinarith
    exact_mod_cast hh'
  intro p q hp hq
  have hp' := lattice_mem_box_of_norm p n (hp.trans htn)
  have hq' := lattice_mem_box_of_norm q n (hq.trans htn)
  have hdiff := passageTime_origin_difference_le w hw p q
  have hconn := hN n hnN p hp' q hq'
  have he : (1/(k+1 : ℝ))*(n : ℝ) ≤ ε*t := by
    have ha := mul_le_mul_of_nonneg_left hnu (show 0 ≤ 1/(k+1 : ℝ) by positivity)
    have hb := (lt_div_iff₀ (show 0 < C+1 by linarith)).mp hk
    nlinarith
  rw [← sub_div,abs_div,abs_of_pos ht0]
  apply (div_le_iff₀ ht0).mpr
  rw [add_mul,div_mul_cancel₀ _ ht0.ne']
  linarith

lemma floor_real_ratio_tendsto (M : ℝ) (hM : 0 < M) :
    Tendsto (fun t : ℝ => (⌊t/M⌋₊ : ℝ)/t) atTop (𝓝 (1/M)) := by
  simpa [div_eq_mul_inv,mul_comm] using
    (tendsto_nat_floor_mul_div_atTop (inv_nonneg.mpr hM.le))

lemma scaledLatticePoint_norm (t : ℝ) (ht : 0 < t) (p : Vertex) :
    ‖scaledLatticePoint t p‖ = ‖latticeEmbed p‖/t := by
  rw [scaledLatticePoint,norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr ht)]
  ring

lemma scaledLatticePoint_sub_norm (t : ℝ) (ht : 0 < t) (p q : Vertex) :
    ‖scaledLatticePoint t p-scaledLatticePoint t q‖ = ‖latticeEmbed p-latticeEmbed q‖/t := by
  rw [scaledLatticePoint,scaledLatticePoint,← smul_sub,norm_smul,Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr ht)]
  ring

lemma scaled_floor_error (t : ℝ) (ht : 0 < t) (v : Plane) :
    ‖scaledLatticePoint t (latticeFloor (t • v))-v‖ ≤ 2/t := by
  have he : scaledLatticePoint t (latticeFloor (t • v))-v =
      (1/t) • (latticeEmbed (latticeFloor (t • v))-t • v) := by
    rw [smul_sub,smul_smul,one_div_mul_cancel ht.ne',one_smul]
    rfl
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr ht)]
  simpa only [one_div,div_eq_mul_inv,one_mul,mul_one,mul_comm] using
    mul_le_mul_of_nonneg_left (latticeFloor_error (t • v)) (le_of_lt (one_div_pos.mpr ht))

lemma scaled_floor_tendsto (v : Plane) :
    Tendsto (fun t : ℝ => scaledLatticePoint t (latticeFloor (t • v))) atTop (𝓝 v) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_gt_atTop (max 0 (2/ε))] with t ht
  have ht0 : 0 < t := (le_max_left _ _).trans_lt ht
  rw [dist_eq_norm]
  exact (scaled_floor_error t ht0 v).trans_lt ((div_lt_iff₀ ht0).mpr
    (by have hh := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt ht); nlinarith))

lemma latticeEmbed_nsmul (n : ℕ) (z : Vertex) :
    latticeEmbed (n • z) = (n : ℝ) • latticeEmbed z := by
  ext i
  fin_cases i <;> simp [latticeEmbed,nsmul_eq_mul]

lemma scaled_lattice_ray_tendsto (z : Vertex) (M : ℝ) (hM : 0 < M) :
    Tendsto (fun t : ℝ => scaledLatticePoint t (⌊t/M⌋₊ • z)) atTop
      (𝓝 ((1/M) • latticeEmbed z)) := by
  have h := (floor_real_ratio_tendsto M hM).smul_const (latticeEmbed z)
  simpa only [scaledLatticePoint,latticeEmbed_nsmul,smul_smul,one_div,div_eq_mul_inv,one_mul,mul_one,mul_comm] using h

theorem real_scale_connections_normalized (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (hc : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime w p q < 4*(latticeDistance p q : ℝ)+(1/(k+1 : ℝ))*n)
    (C : ℝ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ p q : Vertex,
      ‖scaledLatticePoint t p‖ ≤ C → ‖scaledLatticePoint t q‖ ≤ C →
      |passageTime w 0 p/t-passageTime w 0 q/t| ≤
        8*‖scaledLatticePoint t p-scaledLatticePoint t q‖+ε := by
  filter_upwards [real_scale_connections w hw hc C hC ε hε,
    eventually_gt_atTop (0 : ℝ)] with t ht ht0
  intro p q hp hq
  rw [scaledLatticePoint_norm t ht0] at hp hq
  have he := ht p q ((div_le_iff₀ ht0).mp hp) ((div_le_iff₀ ht0).mp hq)
  have hd := latticeDistance_le_norm p q
  rw [norm_sub_rev] at hd
  rw [scaledLatticePoint_sub_norm t ht0]
  apply he.trans
  have hh := (div_le_div_of_nonneg_right hd ht0.le)
  simp only [mul_div_assoc] at hh ⊢
  linarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_LatticeLimitExtension
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory Filter Set
open scoped Topology

lemma passageTime_real_lattice_ray_tendsto (w : Edge → ℝ) (μ : Plane → ℝ)
    (hμ : TimeConstantNorm μ)
    (hray : ∀ z : Vertex, Tendsto (fun n : ℕ => passageTime w 0 (n • z)/n)
      atTop (𝓝 (μ (latticeEmbed z)))) (z : Vertex) (M : ℝ) (hM : 0 < M) :
    Tendsto (fun t : ℝ => passageTime w 0 (⌊t/M⌋₊ • z)/t) atTop
      (𝓝 (μ ((1/M) • latticeEmbed z))) := by
  have hn : Tendsto (fun t : ℝ => ⌊t/M⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_id.atTop_div_const hM)
  have hh := ((hray z).comp hn).mul (floor_real_ratio_tendsto M hM)
  have he : (fun t : ℝ => passageTime w 0 (⌊t/M⌋₊ • z)/t) =ᶠ[atTop]
      (fun t : ℝ => (passageTime w 0 (⌊t/M⌋₊ • z)/(⌊t/M⌋₊ : ℝ))*((⌊t/M⌋₊ : ℝ)/t)) := by
    filter_upwards [hn.eventually (eventually_ge_atTop 1)] with t ht
    have hn0 : (⌊t/M⌋₊ : ℝ) ≠ 0 := by exact_mod_cast (show ⌊t/M⌋₊ ≠ 0 by omega)
    field_simp
  rw [hμ.homogeneous,abs_of_pos (one_div_pos.mpr hM),mul_comm]
  exact hh.congr' he.symm

theorem real_direction_limits_of_lattice_limits (w : Edge → ℝ)
    (hw : ∀ e, 0 ≤ w e) (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hray : ∀ z : Vertex, Tendsto (fun n : ℕ => passageTime w 0 (n • z)/n)
      atTop (𝓝 (μ (latticeEmbed z))))
    (hc : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime w p q < 4*(latticeDistance p q : ℝ)+(1/(k+1 : ℝ))*n) :
    ∀ v : Plane, Tendsto (fun t : ℝ => passageTime w 0 (latticeFloor (t • v))/t)
      atTop (𝓝 (μ v)) := by
  obtain ⟨B,hB,hLip⟩ := timeConstantNorm_lipschitz_bound μ hμ
  intro v
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := min (1/2 : ℝ) (ε/(8*(B+8)))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by linarith))
  have hδ1 : δ ≤ 1/2 := min_le_left _ _
  have hδe : (B+8)*δ ≤ ε/8 := by
    have hh := (le_div_iff₀ (show 0 < 8*(B+8) by linarith)).mp (min_le_right (1/2 : ℝ) (ε/(8*(B+8))))
    dsimp [δ]
    nlinarith
  obtain ⟨M,hM⟩ := exists_nat_gt (max 1 (2/δ))
  have hM0 : (0 : ℝ) < M := (lt_of_lt_of_le (by norm_num) (le_max_left _ _)).trans hM
  let z := latticeFloor ((M : ℝ) • v)
  let u := (1/(M : ℝ)) • latticeEmbed z
  have huv : ‖u-v‖ < δ := by
    apply (scaled_floor_error M hM0 v).trans_lt
    apply (div_lt_iff₀ hM0).mpr
    have hh := (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hM)
    nlinarith
  have hμuv := hLip u v
  let C := ‖v‖+2
  have hC : 0 < C := by dsimp [C]; positivity
  have huC : ‖u‖ < C := by
    have hh := norm_add_le (u-v) v
    rw [sub_add_cancel] at hh
    dsimp [C]
    linarith
  have hp := scaled_floor_tendsto v
  have hq := scaled_lattice_ray_tendsto z M hM0
  have hpC : ∀ᶠ t : ℝ in atTop, ‖scaledLatticePoint t (latticeFloor (t • v))‖ ≤ C :=
    (hp.norm.eventually (gt_mem_nhds (show ‖v‖ < C by dsimp [C]; linarith))).mono (fun _ h => h.le)
  have hqC : ∀ᶠ t : ℝ in atTop, ‖scaledLatticePoint t (⌊t/(M : ℝ)⌋₊ • z)‖ ≤ C :=
    (hq.norm.eventually (gt_mem_nhds huC)).mono (fun _ h => h.le)
  have hpq : ∀ᶠ t : ℝ in atTop,
      ‖scaledLatticePoint t (latticeFloor (t • v))-
        scaledLatticePoint t (⌊t/(M : ℝ)⌋₊ • z)‖ < 2*δ := by
    have hh : ‖v-u‖ < 2*δ := by rw [norm_sub_rev]; linarith
    exact (hp.sub hq).norm.eventually (gt_mem_nhds hh)
  have hcost : ∀ᶠ t : ℝ in atTop,
      |passageTime w 0 (⌊t/(M : ℝ)⌋₊ • z)/t-μ u| < ε/4 := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp
      (passageTime_real_lattice_ray_tendsto w μ hμ hray z M hM0) (ε/4) (by linarith)
  filter_upwards [hpC,hqC,hpq,hcost,
    real_scale_connections_normalized w hw hc C hC (ε/4) (by linarith)] with t hpC hqC hpq hcost ht
  have he := ht _ _ hpC hqC
  have htri : |passageTime w 0 (latticeFloor (t • v))/t-μ v| ≤
      |passageTime w 0 (latticeFloor (t • v))/t-passageTime w 0 (⌊t/(M : ℝ)⌋₊ • z)/t|+
      |passageTime w 0 (⌊t/(M : ℝ)⌋₊ • z)/t-μ u|+|μ u-μ v| := by
    calc
      _ = |(passageTime w 0 (latticeFloor (t • v))/t-passageTime w 0 (⌊t/(M : ℝ)⌋₊ • z)/t)+
        (passageTime w 0 (⌊t/(M : ℝ)⌋₊ • z)/t-μ u)+(μ u-μ v)| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  rw [Real.dist_eq]
  have hmul := mul_lt_mul_of_pos_left huv hB
  nlinarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_FiniteProduct
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset

@[fun_prop] lemma measurable_extendLocalCoordinates (x : Vertex) (R : ℕ) :
    Measurable (extendLocalCoordinates x R) := by
  classical
  apply Measurable.of_eval
  intro e
  by_cases he : e ∈ localEdges x R
  · simpa [extendLocalCoordinates, he] using (measurable_pi_apply (⟨e,he⟩ : ↥(localEdges x R)))
  · simp [extendLocalCoordinates, he]

@[fun_prop] lemma measurable_finitePassageTime (x y : Vertex) (R : ℕ) :
    Measurable (finitePassageTime x y R) :=
  (measurable_localPassageTime x y R).comp (measurable_extendLocalCoordinates x R)

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ActualTimeConstant
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

theorem actualSourceTimeConstant_norm : TimeConstantNorm actualSourceTimeConstant where
  nonneg v := apply_nonneg _ _
  zero_iff v := by
    constructor
    · intro hv
      have he := CompanionFPP.actualTimeNorm.definite (v 0,v 1) hv
      ext i
      fin_cases i
      · exact congrArg Prod.fst he
      · exact congrArg Prod.snd he
    · rintro rfl
      exact map_zero _
  triangle v w := CompanionFPP.timeSeminorm.add_le' (v 0,v 1) (w 0,w 1)
  homogeneous a v := by
    change CompanionFPP.timeSeminorm (a • (v 0,v 1)) = _
    rw [map_smul_eq_mul,Real.norm_eq_abs]
    rfl

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem actualSourceTimeConstant_all_real_limits (h : ExponentialEnvironment P τ) :
    ∀ᵐ ω ∂P, ∀ v : Plane,
      Tendsto (fun t : ℝ => passageTime (fun e => τ e ω) 0 (latticeFloor (t • v))/t)
        atTop (𝓝 (actualSourceTimeConstant v)) := by
  have hc : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime (fun e => τ e ω) p q <
        4*(latticeDistance p q : ℝ)+(1/(k+1 : ℝ))*n := by
    rw [ae_all_iff]
    intro k
    exact ae_eventually_passageTime_connections h (by positivity)
  filter_upwards [h.ae_positive,actualSourceTimeConstant_lattice_limits h,hc] with ω hp hr hc
  exact real_direction_limits_of_lattice_limits _ (fun e => (hp e).le)
    actualSourceTimeConstant actualSourceTimeConstant_norm hr hc

theorem actualSourceTimeConstant_isTimeConstant (h : ExponentialEnvironment P τ) :
    IsTimeConstant P τ actualSourceTimeConstant := by
  intro v
  filter_upwards [actualSourceTimeConstant_all_real_limits h] with ω hω
  exact hω v

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_RecordScales
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Filter
open scoped Topology

theorem exists_strict_record_after (a : ℕ → ℝ) (hpos : ∀ k, 0 < a k)
    (hlim : Tendsto a atTop (𝓝 0)) (N : ℕ) :
    ∃ k, N < k ∧ ∀ i < k, a k < a i := by
  classical
  obtain ⟨i, hi, hmin⟩ := (Finset.range (N + 1)).exists_min_image a (by simp)
  have hex : ∃ k, a k < a i := (hlim.eventually (gt_mem_nhds (hpos i))).exists
  refine ⟨Nat.find hex, ?_, ?_⟩
  · by_contra h
    have hk : Nat.find hex ∈ Finset.range (N + 1) := by
      simp only [Finset.mem_range]
      omega
    exact (not_lt_of_ge (hmin _ hk)) (Nat.find_spec hex)
  · intro j hj
    have hj' : a i ≤ a j := le_of_not_gt (Nat.find_min hex hj)
    exact lt_of_lt_of_le (Nat.find_spec hex) hj'

theorem normalized_lengths_tendsto (L : ℕ → ℝ)
    (hpos : ∀ k, 0 < L k) (hbound : ∀ k, L k ≤ (2 : ℝ) ^ (3 * k)) :
    Tendsto (fun k => L k * (1 / 16 : ℝ) ^ k) atTop (𝓝 0) := by
  have hupper : ∀ k, L k * (1 / 16 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ k := by
    intro k
    calc
      L k * (1 / 16 : ℝ) ^ k ≤ (2 : ℝ) ^ (3 * k) * (1 / 16 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right (hbound k) (by positivity)
      _ = (1 / 2 : ℝ) ^ k := by
        rw [pow_mul, ← mul_pow]
        norm_num
  exact squeeze_zero (fun k => mul_nonneg (hpos k).le (by positivity)) hupper
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

theorem record_scales (L : ℕ → ℝ) (hpos : ∀ k, 0 < L k)
    (hbound : ∀ k, L k ≤ (2 : ℝ) ^ (3 * k)) :
    ∀ N, ∃ k, N < k ∧ ∀ i ≤ k, L k ≤ (16 : ℝ) ^ (k - i) * L i := by
  intro N
  obtain ⟨k, hk, hrec⟩ := exists_strict_record_after
    (fun k => L k * (1 / 16 : ℝ) ^ k) (fun k => mul_pos (hpos k) (by positivity))
    (normalized_lengths_tendsto L hpos hbound) N
  refine ⟨k, hk, ?_⟩
  intro i hi
  have hcmp : L k * (1 / 16 : ℝ) ^ k ≤ L i * (1 / 16 : ℝ) ^ i := by
    rcases eq_or_lt_of_le hi with rfl | hi
    · exact le_refl _
    · exact le_of_lt (hrec i hi)
  have hp : (0 : ℝ) < 16 ^ k := by positivity
  have hmult := mul_le_mul_of_nonneg_right hcmp (le_of_lt hp)
  have hki : k = i + (k - i) := by omega
  have heq : (1 / 16 : ℝ) ^ i * 16 ^ k = 16 ^ (k - i) := by
    conv_lhs => rw [hki, pow_add]
    rw [← mul_assoc, ← mul_pow]
    norm_num
  have hone : (1 / 16 : ℝ) ^ k * 16 ^ k = 1 := by
    rw [← mul_pow]; norm_num
  calc
    L k = (L k * (1 / 16 : ℝ) ^ k) * 16 ^ k := by rw [mul_assoc, hone, mul_one]
    _ ≤ (L i * (1 / 16 : ℝ) ^ i) * 16 ^ k := hmult
    _ = 16 ^ (k - i) * L i := by rw [mul_assoc, heq, mul_comm]

theorem record_scales_from (L : ℕ → ℝ) (k₀ : ℕ)
    (hpos : ∀ k, k₀ ≤ k → 0 < L k)
    (hbound : ∀ k, k₀ ≤ k → L k ≤ (2 : ℝ) ^ (3 * k)) :
    ∀ N, ∃ k, N < k ∧ k₀ ≤ k ∧
      ∀ j, j ≤ k - k₀ → (1 / 16 : ℝ) ^ j * L k ≤ L (k - j) := by
  classical
  intro N
  let L' : ℕ → ℝ := fun k => if k₀ ≤ k then L k else 1
  have hp : ∀ k, 0 < L' k := by
    intro k
    dsimp [L']
    split_ifs with h
    · exact hpos k h
    · norm_num
  have hb : ∀ k, L' k ≤ (2 : ℝ) ^ (3 * k) := by
    intro k
    dsimp [L']
    split_ifs with h
    · exact hbound k h
    · exact one_le_pow₀ (by norm_num)
  obtain ⟨k, hk, hrec⟩ := record_scales L' hp hb (max N k₀)
  have hk₀ : k₀ ≤ k := by omega
  refine ⟨k, by omega, hk₀, ?_⟩
  intro j hj
  have hjk : j ≤ k := by omega
  have hk' : k₀ ≤ k - j := by omega
  have hcomp := hrec (k - j) (Nat.sub_le _ _)
  have hsub : k - (k - j) = j := by omega
  simp only [L', ite_eq_left hk₀, ite_eq_left hk', hsub] at hcomp
  have hm := mul_le_mul_of_nonneg_left hcomp (show 0 ≤ (1 / 16 : ℝ) ^ j by positivity)
  have hcancel : (1 / 16 : ℝ) ^ j * 16 ^ j = 1 := by
    rw [← mul_pow]; norm_num
  simpa only [← mul_assoc, hcancel, one_mul] using hm

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_FiniteEdgeEvents
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set Finset

theorem measurable_extendEdgeWeights (S : Finset Edge) : Measurable (extendEdgeWeights S) := by
  apply Measurable.of_eval
  intro e
  by_cases he : e ∈ S
  · simpa only [extendEdgeWeights,dite_eq_left he] using (measurable_pi_apply (⟨e,he⟩ : S))
  · simp only [extendEdgeWeights,dite_eq_right he]
    exact measurable_const

theorem DependsOnEdges.restriction_iff {A : Set (Edge → ℝ)} {S : Finset Edge}
    (hA : DependsOnEdges A S) (w : Edge → ℝ) :
    extendEdgeWeights S (fun e : S => w e) ∈ A ↔ w ∈ A := by
  apply hA
  intro e he
  simp [extendEdgeWeights,he]

theorem DependsOnEdges.compl {A : Set (Edge → ℝ)} {S : Finset Edge}
    (hA : DependsOnEdges A S) : DependsOnEdges Aᶜ S := by
  intro w w' hh
  exact not_congr (hA w w' hh)

theorem dependsOnEdges_biInter {ι : Type*} (t : Finset ι)
    (A : ι → Set (Edge → ℝ)) (S : ι → Finset Edge)
    (hA : ∀ i ∈ t, DependsOnEdges (A i) (S i)) :
    DependsOnEdges (⋂ i ∈ t, A i) (t.biUnion S) := by
  classical
  intro w w' hh
  simp only [mem_iInter]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  exact hA i hi w w' (fun e he => hh e (mem_biUnion.mpr ⟨i,hi,he⟩))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem disjoint_edge_events_independent (h : ExponentialEnvironment P τ)
    (A B : Set (Edge → ℝ)) (S T : Finset Edge)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAS : DependsOnEdges A S) (hBT : DependsOnEdges B T) (hST : Disjoint S T) :
    IndepSet {ω | (fun e => τ e ω) ∈ A} {ω | (fun e => τ e ω) ∈ B} P := by
  let _ := h.probability
  have hf := h.independent.indepFun_finset S T hST h.measurable
  have hs : Measurable (fun ω (e : S) => τ e ω) := Measurable.of_eval (fun e => h.measurable e)
  have ht : Measurable (fun ω (e : T) => τ e ω) := Measurable.of_eval (fun e => h.measurable e)
  have hi := (indepFun_iff_indepSet_preimage hs ht).mp hf
    ((extendEdgeWeights S) ⁻¹' A) ((extendEdgeWeights T) ⁻¹' B)
    (hA.preimage (measurable_extendEdgeWeights S)) (hB.preimage (measurable_extendEdgeWeights T))
  have heA : (fun ω (e : S) => τ e ω) ⁻¹' ((extendEdgeWeights S) ⁻¹' A) =
      {ω | (fun e => τ e ω) ∈ A} := by
    ext ω
    simpa only [Set.mem_preimage,mem_ofPred_eq] using hAS.restriction_iff (fun e => τ e ω)
  have heB : (fun ω (e : T) => τ e ω) ⁻¹' ((extendEdgeWeights T) ⁻¹' B) =
      {ω | (fun e => τ e ω) ∈ B} := by
    ext ω
    simpa only [Set.mem_preimage,mem_ofPred_eq] using hBT.restriction_iff (fun e => τ e ω)
  simpa only [heA,heB] using hi

theorem disjoint_edge_events_inter_probability (h : ExponentialEnvironment P τ)
    {ι : Type*} (t : Finset ι) (A : ι → Set (Edge → ℝ)) (S : ι → Finset Edge)
    (hA : ∀ i ∈ t, MeasurableSet (A i))
    (hAS : ∀ i ∈ t, DependsOnEdges (A i) (S i))
    (hdis : Set.Pairwise (↑t : Set ι) (fun i j => Disjoint (S i) (S j))) :
    P {ω | ∀ i ∈ t, (fun e => τ e ω) ∈ A i} =
      ∏ i ∈ t, P {ω | (fun e => τ e ω) ∈ A i} := by
  classical
  let _ := h.probability
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    have hAt : ∀ i ∈ t, MeasurableSet (A i) := fun i hi => hA i (mem_insert_of_mem hi)
    have hSt : ∀ i ∈ t, DependsOnEdges (A i) (S i) := fun i hi => hAS i (mem_insert_of_mem hi)
    have hd : Set.Pairwise (↑t : Set ι) (fun i j => Disjoint (S i) (S j)) := by
      intro i hi j hj hij
      exact hdis (mem_insert_of_mem hi) (mem_insert_of_mem hj) hij
    have hdunion : Disjoint (S a) (t.biUnion S) := by
      rw [Finset.disjoint_biUnion_right]
      intro i hi
      exact hdis (mem_insert_self _ _) (mem_insert_of_mem hi) (by intro he; exact ha (he ▸ hi))
    have hm : MeasurableSet (⋂ i ∈ t, A i) := MeasurableSet.biInter (t.countable_toSet) hAt
    have hi := disjoint_edge_events_independent h (A a) (⋂ i ∈ t, A i) (S a) (t.biUnion S)
      (hA a (mem_insert_self _ _)) hm (hAS a (mem_insert_self _ _))
      (dependsOnEdges_biInter t A S hSt) hdunion
    have hprob := hi.measure_inter_eq_mul
    have he : {ω | ∀ i ∈ insert a t, (fun e => τ e ω) ∈ A i} =
        {ω | (fun e => τ e ω) ∈ A a} ∩ {ω | (fun e => τ e ω) ∈ ⋂ i ∈ t, A i} := by
      ext ω; simp
    rw [he,hprob,Finset.prod_insert ha]
    congr 1
    simpa only [mem_iInter] using ih hAt hSt hd

theorem disjoint_trials_failure_bound (h : ExponentialEnvironment P τ)
    {ι : Type*} (t : Finset ι) (A : ι → Set (Edge → ℝ)) (S : ι → Finset Edge)
    (hA : ∀ i ∈ t, MeasurableSet (A i)) (hAS : ∀ i ∈ t, DependsOnEdges (A i) (S i))
    (hdis : Set.Pairwise (↑t : Set ι) (fun i j => Disjoint (S i) (S j)))
    (p : ℝ)
    (hprob : ∀ i ∈ t, p ≤ P.real {ω | (fun e => τ e ω) ∈ A i}) :
    P.real {ω | ∀ i ∈ t, (fun e => τ e ω) ∉ A i} ≤ (1-p)^t.card := by
  classical
  let _ := h.probability
  have he := disjoint_edge_events_inter_probability h t (fun i => (A i)ᶜ) S
    (fun i hi => (hA i hi).compl) (fun i hi => (hAS i hi).compl) hdis
  have her := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_prod] at her
  change P.real _ = ∏ i ∈ t, P.real {ω | (fun e => τ e ω) ∉ A i} at her
  simp only [mem_compl_iff] at her
  rw [her]
  calc
    _ ≤ ∏ _i ∈ t, (1-p) := by
      apply Finset.prod_le_prod
      · intro i _; exact measureReal_nonneg
      · intro i hi
        have hm := (hA i hi).preimage (Measurable.of_eval h.measurable)
        have hc := measureReal_compl (μ := P) hm
        simp only [Set.preimage] at hc
        change P.real ({ω | (fun e => τ e ω) ∈ A i}ᶜ) ≤ _
        rw [hc]
        simpa using sub_le_sub_left (hprob i hi) 1
    _ = _ := by simp

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

theorem mem_internalEdges (e : Edge) (V : Finset Vertex) :
    e ∈ internalEdges V ↔ e.1 ∈ V ∧ edgeEnd e ∈ V := by
  simp [internalEdges]

theorem step_mem_internalEdges (V : Finset Vertex) (p : Vertex) (d : Step)
    (hp : p ∈ V) (hq : p+d.delta ∈ V) : d.edge p ∈ internalEdges V := by
  rw [mem_internalEdges]
  cases d <;> simp_all [Step.edge,Step.delta,edgeEnd,add_assoc]
  all_goals change p+0 ∈ V; simpa using hp

theorem internalEdges_disjoint {V W : Finset Vertex} (h : Disjoint V W) :
    Disjoint (internalEdges V) (internalEdges W) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact Finset.disjoint_left.mp h (mem_internalEdges e V |>.mp he).1
    (mem_internalEdges e W |>.mp hf).1

theorem pathIn_cons_iff (p : Vertex) (d : Step) (ds : List Step) (S : Set Vertex) :
    PathIn p (d::ds) S ↔ p ∈ S ∧ PathIn (p+d.delta) ds S := by
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by simp),?_⟩
    intro i hi
    have hh := h (i+1) (by simpa using hi)
    simpa only [List.take_succ_cons,displacement_cons,add_assoc] using hh
  · rintro ⟨hp,ht⟩ i hi
    cases i with
    | zero => simpa using hp
    | succ i =>
      have hh := ht i (by simpa using hi)
      simpa only [List.take_succ_cons,displacement_cons,add_assoc] using hh

theorem pathEdges_subset_internalEdges (V : Finset Vertex) (p : Vertex) (ds : List Step)
    (h : PathIn p ds (V : Set Vertex)) : pathEdges p ds ⊆ internalEdges V := by
  induction ds generalizing p with
  | nil => simp [pathEdges]
  | cons d ds ih =>
    obtain ⟨hp,ht⟩ := (pathIn_cons_iff p d ds _).mp h
    have hq : p+d.delta ∈ V := by simpa using ht 0 (by omega)
    intro e he
    rcases Finset.mem_insert.mp he with he | he
    · rw [he]
      exact step_mem_internalEdges V p d hp hq
    · exact ih (p+d.delta) ht he

theorem pathCost_eq_of_agree (w w' : Edge → ℝ) (p : Vertex) (ds : List Step)
    (h : ∀ e ∈ pathEdges p ds, w e=w' e) : pathCost w p ds=pathCost w' p ds := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih =>
    simp only [pathCost]
    rw [h (d.edge p) (by simp [pathEdges])]
    rw [ih (p+d.delta) (fun e he => h e (by simp [pathEdges,he]))]

theorem measurableSet_strictLocalizedEvent (V : Finset Vertex)
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    MeasurableSet (strictLocalizedEvent V family bound) := by
  simpa only [strictLocalizedEvent,and_assoc] using
    measurableSet_strict_path_event (τ := fun e (w : Edge → ℝ) => w e) measurable_pi_apply
      (fun p ds => family p ds ∧ PathIn p ds (V : Set Vertex)) bound

theorem strictLocalizedEvent_depends (V : Finset Vertex)
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    DependsOnEdges (strictLocalizedEvent V family bound) (internalEdges V) := by
  intro w w' hh
  have hc (p ds) (hin : PathIn p ds (V : Set Vertex)) : pathCost w p ds=pathCost w' p ds :=
    pathCost_eq_of_agree w w' p ds (fun e he => hh e (pathEdges_subset_internalEdges V p ds hin he))
  constructor
  · rintro ⟨p,ds,hf,hin,hcost⟩
    exact ⟨p,ds,hf,hin,by rwa [← hc p ds hin]⟩
  · rintro ⟨p,ds,hf,hin,hcost⟩
    exact ⟨p,ds,hf,hin,by rwa [hc p ds hin]⟩

theorem strip_vertices_disjoint (V W : Finset Vertex) (b y z R : ℝ)
    (hV : ∀ v ∈ V, |transverse b v-y| ≤ R)
    (hW : ∀ v ∈ W, |transverse b v-z| ≤ R)
    (hsep : 2*R < |y-z|) : Disjoint V W := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  have ht := abs_add_le (y-transverse b v) (transverse b v-z)
  rw [sub_add_sub_cancel,abs_sub_comm y (transverse b v)] at ht
  have h1 := hV v hv
  have h2 := hW v hw
  linarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_RareFastEvents
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

theorem mem_rareFastEvent (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) (w : Edge → ℝ) :
    w ∈ rareFastEvent b m a A R ε s n t ↔
      ∃ p ds, p.1=t.1 ∧ (p+displacement ds).1=t.1+n ∧
        PathIn p ds (rareFastRegion b A R s n t) ∧ defect w b m a p ds < -ε*s := by
  simp only [rareFastEvent,strictLocalizedEvent,mem_ofPred_eq,defect]
  have hV : (rareFastVertices b A R s n t : Set Vertex)=rareFastRegion b A R s n t := by
    ext p; simp
  rw [hV]
  constructor
  · rintro ⟨p,ds,⟨hp,hq⟩,hin,hc⟩
    exact ⟨p,ds,hp,hq,hin,by linarith⟩
  · rintro ⟨p,ds,hp,hq,hin,hc⟩
    exact ⟨p,ds,⟨hp,hq⟩,hin,by linarith⟩

theorem measurableSet_rareFastEvent (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) :
    MeasurableSet (rareFastEvent b m a A R ε s n t) :=
  measurableSet_strictLocalizedEvent _ _ _

theorem rareFastEvent_translate (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) (w : Edge → ℝ) :
    (fun e => w (shiftEdge t e)) ∈ rareFastEvent b m a A R ε s n 0 ↔
      w ∈ rareFastEvent b m a A R ε s n t := by
  rw [mem_rareFastEvent,mem_rareFastEvent]
  have hc (p ds) : defect (fun e => w (shiftEdge t e)) b m a p ds =
      defect w b m a (t+p) ds := by simp only [defect,pathCost_translate]
  constructor
  · rintro ⟨p,ds,hp,hq,hin,hcost⟩
    refine ⟨t+p,ds,by simpa using hp,by simpa [add_assoc] using hq,?_,?_⟩
    · intro i hi
      have he : t+p+displacement (ds.take i)-t=p+displacement (ds.take i) := by abel
      change _ ∈ rareFastRegion b A R s n t
      simpa only [rareFastRegion,mem_ofPred_eq,he,sub_zero] using hin i hi
    · rwa [← hc]
  · rintro ⟨p,ds,hp,hq,hin,hcost⟩
    refine ⟨p-t,ds,by simpa using sub_eq_zero.mpr hp,?_,?_,?_⟩
    · simp only [Prod.fst_add,Prod.fst_sub,Prod.fst_zero] at *
      omega
    · intro i hi
      have he : p-t+displacement (ds.take i)=(p+displacement (ds.take i))-t := by abel
      rw [he]
      simpa [rareFastRegion] using hin i hi
    · rw [hc,add_sub_cancel]
      exact hcost

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem rareFastEvent_probability_translate (h : ExponentialEnvironment P τ)
    (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) :
    P {ω | (fun e => τ e ω) ∈ rareFastEvent b m a A R ε s n t} =
      P {ω | (fun e => τ e ω) ∈ rareFastEvent b m a A R ε s n 0} := by
  have he : {ω | (fun e => τ (shiftEdge t e) ω) ∈ rareFastEvent b m a A R ε s n 0} =
      {ω | (fun e => τ e ω) ∈ rareFastEvent b m a A R ε s n t} := by
    ext ω
    exact rareFastEvent_translate b m a A R ε s n t (fun e => τ e ω)
  rw [← he]
  exact translated_event_probability h t _ (measurableSet_rareFastEvent ..)

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

theorem crossingEvent_depends (b m K s : ℝ) (n : ℤ) (t : Vertex) :
    DependsOnEdges (crossingEvent b m K s n t) (internalEdges (rareFastVertices b 1 8 s n t)) :=
  strictLocalizedEvent_depends _ _ _

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

theorem exponential_characteristic_record_scales (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b q : ℝ) (hb : |b| ≤ 1) (hq : 0 < q) :
    ∃ k0 : ℕ, ∀ N, ∃ k, N < k ∧ k0 ≤ k ∧
      ∀ j, j ≤ k-k0 → (1/16 : ℝ)^j*(characteristicLength P τ μ b q k : ℝ) ≤
        (characteristicLength P τ μ b q (k-j) : ℝ) := by
  obtain ⟨k0,hk0⟩ := eventually_atTop.mp (exponential_characteristic_lengths_exist h μ hμ ht b q hb hq)
  refine ⟨k0,record_scales_from (fun k => (characteristicLength P τ μ b q k : ℝ)) k0 (fun k _ => by exact_mod_cast characteristicLength_pos μ b q k) ?_⟩
  intro k hk
  have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (hk0 k hk).1
  have he : characteristicLength P τ μ b q k ≤ (2 : ℤ)^(3*k) := hh
  exact_mod_cast he

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridMeshes
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Filter Set MeasureTheory
open scoped Topology

lemma gridMesh_pos (m j : ℕ) : 0 < gridMesh m j := by unfold gridMesh; positivity
lemma gridWidth_pos (k j : ℕ) : 0 < gridWidth k j := by unfold gridWidth; positivity

lemma gridMesh_count_ratio (m j : ℕ) :
    (2 : ℝ)^m / (gridMesh m j : ℝ) ≤ (2 : ℝ)^(4*j+1) := by
  have hg : (0 : ℝ) < (gridMesh m j : ℝ) := by exact_mod_cast gridMesh_pos m j
  rw [div_le_iff₀ hg]
  simp only [gridMesh,Int.cast_pow,Int.cast_ofNat,← pow_add]
  apply pow_le_pow_right₀ (by norm_num)
  unfold gridMeshExponent
  omega

lemma gridWidth_ratio (k j : ℕ) (hj : j ≤ k) :
    (2 : ℝ)^k / (gridWidth k j : ℝ) = (2 : ℝ)^j := by
  have he : k=j+(k-j) := by omega
  simp only [gridWidth,Int.cast_pow,Int.cast_ofNat]
  rw [show (2 : ℝ)^k=(2 : ℝ)^j*(2 : ℝ)^(k-j) by rw [← pow_add,← he]]
  rw [mul_div_cancel_right₀ _ (by positivity)]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridCounting
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset Set

lemma gridIndexRange_card (x : ℝ) : (gridIndexRange x).card=2*⌈x⌉₊+1 := by
  rw [gridIndexRange,Int.card_Icc]
  omega

lemma gridIndexConstant_pos (A R : ℝ) (hA : 0 < A) (hR : 0 < R) :
    0 < gridIndexConstant A R := by unfold gridIndexConstant; positivity

lemma gridTestIndices_card (A R L s l w : ℝ) (hA : 0 < A) (hR : 0 < R)
    (hl : 0 < l) (hw : 0 < w) (hLl : 1 ≤ L/l) (hsw : 1 ≤ s/w) :
    ((gridTestIndices A R L s l w).card : ℝ) ≤
      (2*(A+4)+3)*(2*R+5)*(L/l)*(s/w) := by
  have hL : 0 ≤ L := by have hh := (le_div_iff₀ hl).mp hLl; linarith
  have hs : 0 ≤ s := by have hh := (le_div_iff₀ hw).mp hsw; linarith
  have hc₁ := Nat.ceil_lt_add_one (show 0 ≤ (A+4)*L/l by positivity)
  have hc₂ := Nat.ceil_lt_add_one (show 0 ≤ R*s/w+1 by positivity)
  have hc₁' : 2*(⌈(A+4)*L/l⌉₊ : ℝ)+1 ≤ (2*(A+4)+3)*(L/l) := by
    simp only [mul_div_assoc] at hc₁ ⊢
    nlinarith
  have hc₂' : 2*(⌈R*s/w+1⌉₊ : ℝ)+1 ≤ (2*R+5)*(s/w) := by
    simp only [mul_div_assoc] at hc₂ ⊢
    nlinarith
  rw [gridTestIndices,Finset.card_product,gridIndexRange_card,gridIndexRange_card]
  push_cast
  have hh := mul_le_mul hc₁' hc₂' (by positivity) (by positivity)
  nlinarith

lemma gridTestIndices_level_card (A R : ℝ) (hA : 0 < A) (hR : 0 < R)
    (k m j : ℕ) (hj : j ≤ k) :
    ((gridTestIndices A R ((2 : ℝ)^m) ((2 : ℝ)^k)
      (gridMesh m j) (gridWidth k j)).card : ℝ) ≤ gridIndexConstant A R*(2 : ℝ)^(5*j) := by
  have hl : (0 : ℝ) < gridMesh m j := by exact_mod_cast gridMesh_pos m j
  have hw : (0 : ℝ) < gridWidth k j := by exact_mod_cast gridWidth_pos k j
  have hLl : 1 ≤ (2 : ℝ)^m/(gridMesh m j : ℝ) := by
    apply (le_div_iff₀ hl).mpr
    simp only [one_mul,gridMesh,Int.cast_pow,Int.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have hsw : 1 ≤ (2 : ℝ)^k/(gridWidth k j : ℝ) := by
    rw [gridWidth_ratio k j hj]
    exact one_le_pow₀ (by norm_num)
  apply (gridTestIndices_card A R _ _ _ _ hA hR hl hw hLl hsw).trans
  rw [gridWidth_ratio k j hj]
  calc
    _ ≤ (2*(A+4)+3)*(2*R+5)*(2 : ℝ)^(4*j+1)*(2 : ℝ)^j := by
      gcongr
      exact gridMesh_count_ratio m j
    _ = _ := by
      rw [mul_assoc ((2*(A+4)+3)*(2*R+5)),← pow_add,
        show 4*j+1+j=5*j+1 by omega,pow_succ]
      unfold gridIndexConstant
      ring

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridTrials
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

lemma crossingEvent_eq_rareFastEvent (b m K s : ℝ) (n : ℤ) (t : Vertex) :
    crossingEvent b m K s n t = rareFastEvent b m 0 1 8 (-K) s n t := by
  ext w
  constructor <;> rintro ⟨p,ds,hcols,hin,hcost⟩
  all_goals
    have hd : (displacement ds).1=n := by
      have hh := hcols.2
      simp only [Prod.fst_add,hcols.1] at hh
      omega
    refine ⟨p,ds,hcols,hin,?_⟩
    simpa only [support,zero_mul,add_zero,hd,neg_mul,sub_neg_eq_add] using hcost

lemma gridTrialTranslate_center (b : ℝ) (X h w : ℤ) (t : ℕ) :
    transverse b (gridTrialTranslate b X h w t) =
      (⌊b*X⌋ : ℝ)-b*X+((h : ℝ)+30*(t+1))*w := by
  simp [gridTrialTranslate,transverse]
  ring

lemma gridTrialTranslate_separation (b : ℝ) (X h w : ℤ) (hw : 1 ≤ w)
    {t u : ℕ} (htu : t ≠ u) :
    2*(8*(w : ℝ)) < |transverse b (gridTrialTranslate b X h w t)-
      transverse b (gridTrialTranslate b X h w u)| := by
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hsep : 1 ≤ |(t : ℝ)-u| := by
    have hn : (1 : ℤ) ≤ |(t : ℤ)-u| := by
      rw [abs_eq_max_neg]
      omega
    exact_mod_cast hn
  rw [gridTrialTranslate_center,gridTrialTranslate_center,
    show ((⌊b*X⌋ : ℝ)-b*X+((h : ℝ)+30*(t+1))*w)-
      ((⌊b*X⌋ : ℝ)-b*X+((h : ℝ)+30*(u+1))*w) =
      30*(w : ℝ)*((t : ℝ)-u) by ring,abs_mul,abs_of_nonneg (by positivity)]
  nlinarith

lemma gridTrials_disjoint (b : ℝ) (X h w l : ℤ) (hw : 1 ≤ w) (j : ℕ) :
    Pairwise (fun t u : Fin (j^2) => Disjoint
      (rareFastVertices b 1 8 w l (gridTrialTranslate b X h w t))
      (rareFastVertices b 1 8 w l (gridTrialTranslate b X h w u))) := by
  intro t u htu
  apply strip_vertices_disjoint _ _ b
    (transverse b (gridTrialTranslate b X h w t))
    (transverse b (gridTrialTranslate b X h w u)) (8*w)
  · intro p hp
    have hh := ((mem_rareFastVertices ..).mp hp).2.2
    convert hh using 1
    simp [transverse]
    congr 1
    ring
  · intro p hp
    have hh := ((mem_rareFastVertices ..).mp hp).2.2
    convert hh using 1
    simp [transverse]
    congr 1
    ring
  · exact gridTrialTranslate_separation b X h w hw (fun he => htu (Fin.ext he))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

lemma crossingEvent_probability_translate (h : ExponentialEnvironment P τ)
    (b m K s : ℝ) (n : ℤ) (t : Vertex) :
    P {ω | (fun e => τ e ω) ∈ crossingEvent b m K s n t} =
      P {ω | (fun e => τ e ω) ∈ crossingEvent b m K s n 0} := by
  simp only [crossingEvent_eq_rareFastEvent]
  exact rareFastEvent_probability_translate h b m 0 1 8 (-K) s n t

theorem gridTrials_failure_bound (henv : ExponentialEnvironment P τ)
    (b m K q₀ : ℝ) (X h w l : ℤ) (hw : 1 ≤ w) (j : ℕ)
    (hq : q₀ ≤ P.real {ω | (fun e => τ e ω) ∈ crossingEvent b m K w l 0}) :
    P.real {ω | ∀ t : Fin (j^2), (fun e => τ e ω) ∉
      crossingEvent b m K w l (gridTrialTranslate b X h w t)} ≤ (1-q₀)^(j^2) := by
  have hh := disjoint_trials_failure_bound henv (Finset.univ : Finset (Fin (j^2)))
    (fun t => crossingEvent b m K w l (gridTrialTranslate b X h w t))
    (fun t => internalEdges (rareFastVertices b 1 8 w l (gridTrialTranslate b X h w t)))
    (fun _ _ => measurableSet_crossingEvent ..)
    (fun t _ => crossingEvent_depends b m K w l (gridTrialTranslate b X h w t))
    (fun _ _ _ _ htu => internalEdges_disjoint (gridTrials_disjoint b X h w l hw j htu))
    q₀ (fun t _ => ?_)
  · simpa using hh
  · unfold Measure.real
    rw [crossingEvent_probability_translate henv]
    exact hq

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_VerticalIntervals
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

lemma verticalIntervalEdges_card (X lo hi : ℤ) :
    (verticalIntervalEdges X lo hi).card=(hi-lo).toNat := by
  rw [verticalIntervalEdges,Finset.card_image_of_injective]
  · exact Int.card_Ico lo hi
  · intro a b hab
    exact congrArg (fun e : Edge => e.1.2) hab

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

lemma costly_edge_set_probability_real (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (a : ℝ) :
    P.real {ω | a ≤ ∑ e ∈ S, τ e ω} ≤ (2 : ℝ)^S.card*Real.exp (-a/2) := by
  have he := ENNReal.toReal_mono
    (show (2 : ℝ≥0∞)^S.card/ENNReal.ofReal (Real.exp (a/2)) ≠ ⊤ from
      ENNReal.div_ne_top (by simp) (by positivity)) (costly_edge_set_probability h S a)
  simp only [ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (Real.exp_pos _).le] at he
  change P.real _ ≤ _ at he
  rw [show -a/2=-(a/2) by ring,Real.exp_neg]
  simpa only [div_eq_mul_inv] using he

theorem grid_vertical_cost_tail (henv : ExponentialEnvironment P τ)
    (X lo hi : ℤ) (a : ℝ)
    (hcard : ((verticalIntervalEdges X lo hi).card : ℝ) ≤ 50*a) :
    P.real {ω | 100*a < ∑ e ∈ verticalIntervalEdges X lo hi,τ e ω} ≤
      Real.exp (-(50*(1-Real.log 2))*a) := by
  let _ := henv.probability
  apply (measureReal_mono (show {ω | 100*a < ∑ e ∈ verticalIntervalEdges X lo hi,τ e ω} ⊆
    {ω | 100*a ≤ ∑ e ∈ verticalIntervalEdges X lo hi,τ e ω} from by
      intro ω hω
      change 100*a ≤ _
      exact le_of_lt hω)).trans
  apply (costly_edge_set_probability_real henv _ (100*a)).trans
  rw [show (2 : ℝ)^(verticalIntervalEdges X lo hi).card =
      Real.exp ((verticalIntervalEdges X lo hi).card*Real.log 2) by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 2)],← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hcard (show 0 ≤ Real.log 2 by positivity)
  nlinarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridConnectionGeometry
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

lemma transverseIntervalEdges_card_le (b : ℝ) (X : ℤ) (lo hi A : ℝ)
    (hA : 0 ≤ A) (hwidth : hi-lo ≤ A) :
    ((transverseIntervalEdges b X lo hi).card : ℝ) ≤ A := by
  rw [transverseIntervalEdges,verticalIntervalEdges_card]
  by_cases hle : ⌈lo+b*X⌉ ≤ ⌊hi+b*X⌋
  · have he : ((⌊hi+b*X⌋-⌈lo+b*X⌉).toNat : ℝ) = (⌊hi+b*X⌋ : ℝ)-(⌈lo+b*X⌉ : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ ⌊hi+b*X⌋-⌈lo+b*X⌉ by omega)
    rw [he]
    have hl := Int.le_ceil (lo+b*X)
    have hh := Int.floor_le (hi+b*X)
    linarith
  · rw [Int.toNat_eq_zero.mpr (by omega)]
    simpa using hA

lemma grid_interval_card (b : ℝ) (X h w : ℤ) (j : ℕ) (hj : 1 ≤ j) (hw : 1 ≤ w) :
    ((transverseIntervalEdges b X (gridIntervalLower h w) (gridIntervalUpper j h w)).card : ℝ) ≤
      50*(j : ℝ)^2*w := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hj2 : (1 : ℝ) ≤ (j : ℝ)^2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hj2 (show 0 ≤ (w : ℝ) by linarith)
  apply transverseIntervalEdges_card_le _ _ _ _ _ (by positivity)
  unfold gridIntervalLower gridIntervalUpper
  nlinarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridProbability
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

lemma gridVerticalExponent_pos : 0 < gridVerticalExponent := by
  have hlog : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    norm_num at h
    exact h
  unfold gridVerticalExponent
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem gridBinGood_failure_bound (henv : ExponentialEnvironment P τ)
    (b m K q₀ : ℝ) (X h w l : ℤ) (j : ℕ) (hj : 1 ≤ j) (hw : 1 ≤ w)
    (hq : q₀ ≤ P.real {ω | (fun e => τ e ω) ∈ crossingEvent b m K w l 0}) :
    P.real {ω | (fun e => τ e ω) ∉ gridBinGood b m K X h w l j} ≤
      (1-q₀)^(j^2)+2*Real.exp (-gridVerticalExponent*(j : ℝ)^2*w) := by
  let _ := henv.probability
  let F := {ω | ∀ t : Fin (j^2), (fun e => τ e ω) ∉ crossingEvent b m K w l (gridTrialTranslate b X h w t)}
  let V₁ := {ω | 100*(j : ℝ)^2*w < ∑ e ∈ transverseIntervalEdges b X
    (gridIntervalLower h w) (gridIntervalUpper j h w),τ e ω}
  let V₂ := {ω | 100*(j : ℝ)^2*w < ∑ e ∈ transverseIntervalEdges b (X+l)
    (gridIntervalLower h w) (gridIntervalUpper j h w),τ e ω}
  have hsub : {ω | (fun e => τ e ω) ∉ gridBinGood b m K X h w l j} ⊆ F ∪ V₁ ∪ V₂ := by
    intro ω hω
    simp only [gridBinGood,Set.mem_ofPred_eq,not_and_or,not_exists,not_le] at hω
    rcases hω with hf | hv | hv
    · exact Or.inl (Or.inl hf)
    · exact Or.inl (Or.inr hv)
    · exact Or.inr hv
  have hf := gridTrials_failure_bound henv b m K q₀ X h w l hw j hq
  have hv₁ := grid_vertical_cost_tail henv X ⌈gridIntervalLower h w+b*X⌉
    ⌊gridIntervalUpper j h w+b*X⌋ ((j : ℝ)^2*w) (by
      simpa only [transverseIntervalEdges,mul_assoc] using grid_interval_card b X h w j hj hw)
  have hv₂ := grid_vertical_cost_tail henv (X+l) ⌈gridIntervalLower h w+b*(X+l)⌉
    ⌊gridIntervalUpper j h w+b*(X+l)⌋ ((j : ℝ)^2*w) (by
      simpa only [transverseIntervalEdges,mul_assoc,Int.cast_add] using grid_interval_card b (X+l) h w j hj hw)
  have hv₁' : P.real V₁ ≤ Real.exp (-gridVerticalExponent*(j : ℝ)^2*w) := by
    simpa only [V₁,transverseIntervalEdges,gridVerticalExponent,mul_assoc] using hv₁
  have hv₂' : P.real V₂ ≤ Real.exp (-gridVerticalExponent*(j : ℝ)^2*w) := by
    simpa only [V₂,transverseIntervalEdges,gridVerticalExponent,mul_assoc,Int.cast_add] using hv₂
  have hh := (measureReal_mono (μ := P) hsub).trans
    ((measureReal_union_le (μ := P) (F ∪ V₁) V₂).trans
      (add_le_add (measureReal_union_le (μ := P) F V₁) le_rfl))
  change P.real F ≤ _ at hf
  linarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridTail
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Filter Finset Set
open scoped Topology

lemma summable_grid_gaussian (a : ℝ) (ha : 0 < a) :
    Summable (fun j : ℕ => (2 : ℝ)^(5*j)*Real.exp (-a*(j : ℝ)^2)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((5*Real.log 2+1)/a)
  apply (summable_nat_add_iff N).mp
  have hs : Summable (fun n : ℕ => Real.exp (-1)^n) :=
    summable_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]; exact Real.exp_lt_one_iff.mpr (by norm_num))
  apply hs.of_nonneg_of_le (fun _ => by positivity)
  intro n
  have hNa : 5*Real.log 2+1 < (N : ℝ)*a := (div_lt_iff₀ ha).mp hN
  have hja : 5*Real.log 2+1 ≤ a*((n+N : ℕ) : ℝ) := by push_cast; nlinarith
  have hmul := mul_le_mul_of_nonneg_right hja (show 0 ≤ ((n+N : ℕ) : ℝ) by positivity)
  rw [show (2 : ℝ)^(5*(n+N))=Real.exp ((5*(n+N : ℕ) : ℕ)*Real.log 2) by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ)<2)],← Real.exp_add,← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  push_cast at hmul ⊢
  nlinarith

lemma gridFailureSeries_nonneg (q : ℝ) (j : ℕ) : 0 ≤ gridFailureSeries q j := by
  unfold gridFailureSeries
  positivity

lemma summable_gridFailureSeries (q : ℝ) (hq : 0 < q) : Summable (gridFailureSeries q) := by
  have h := (summable_grid_gaussian q hq).add
    ((summable_grid_gaussian gridVerticalExponent gridVerticalExponent_pos).mul_left 2)
  apply h.congr
  intro j
  unfold gridFailureSeries
  ring

lemma grid_level_failure_le_series (q : ℝ) (_hq : 0 ≤ q) (hq1 : q ≤ 1)
    (j : ℕ) (w : ℝ) (hw : 1 ≤ w) :
    (2 : ℝ)^(5*j)*((1-q)^(j^2)+2*Real.exp (-gridVerticalExponent*(j : ℝ)^2*w)) ≤
      gridFailureSeries q j := by
  have hb : 1-q ≤ Real.exp (-q) := by have hh := Real.add_one_le_exp (-q); linarith
  have hp := pow_le_pow_left₀ (show 0 ≤ 1-q by linarith) hb (j^2)
  have hp' : (1-q)^(j^2) ≤ Real.exp (-q*(j : ℝ)^2) := by
    rw [← Real.exp_nat_mul] at hp
    simpa only [Nat.cast_pow,mul_comm] using hp
  have he : Real.exp (-gridVerticalExponent*(j : ℝ)^2*w) ≤
      Real.exp (-gridVerticalExponent*(j : ℝ)^2) := by
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul_of_nonneg_left hw
      (mul_nonneg gridVerticalExponent_pos.le (sq_nonneg (j : ℝ)))
    nlinarith
  unfold gridFailureSeries
  gcongr

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridConnections
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem gridConnectionsEvent_failure_bound (henv : ExponentialEnvironment P τ)
    (b m₀ K A R q₀ : ℝ) (hA : 0 < A) (hR : 0 < R) (hq : 0 < q₀) (hq1 : q₀ ≤ 1)
    (k m J : ℕ) (hJ : 1 ≤ J) (hlast : gridLastLevel m ≤ k)
    (htrial : ∀ j, J ≤ j → j ≤ gridLastLevel m →
      q₀ ≤ P.real {ω | (fun e => τ e ω) ∈ crossingEvent b m₀ K (gridWidth k j) (gridMesh m j) 0}) :
    P.real {ω | (fun e => τ e ω) ∉ gridConnectionsEvent b m₀ K A R k m J} ≤
      gridFailureTail (gridIndexConstant A R) q₀ J := by
  let _ := henv.probability
  let N := gridLastLevel m+1-J
  let S (n : ℕ) := gridTestIndices A R ((2 : ℝ)^m) ((2 : ℝ)^k) (gridMesh m (n+J)) (gridWidth k (n+J))
  let Bad (n : ℕ) (ih : ℤ×ℤ) : Set Ω := {ω | (fun e => τ e ω) ∉ gridBinGood b m₀ K
    (gridMesh m (n+J)*ih.1) ih.2 (gridWidth k (n+J)) (gridMesh m (n+J)) (n+J)}
  let AllBad : Set Ω := ⋃ n ∈ Finset.range N, ⋃ ih ∈ S n, Bad n ih
  have hsub : ∀ᵐ ω ∂P, (fun e => τ e ω) ∉ gridConnectionsEvent b m₀ K A R k m J → ω ∈ AllBad := by
    filter_upwards [henv.ae_positive] with ω hω hb
    have ht : ¬(fun e => τ e ω) ∈ gridTestsEvent b m₀ K A R k m J := by
      intro ht
      exact hb ⟨fun e => (hω e).le,ht⟩
    simp only [gridTestsEvent,Set.mem_ofPred_eq,not_forall] at ht
    obtain ⟨n,hn,ih,hih,hbad⟩ := ht
    exact mem_iUnion₂.mpr ⟨n,hn,mem_iUnion₂.mpr ⟨ih,hih,hbad⟩⟩
  have hprob : P.real {ω | (fun e => τ e ω) ∉ gridConnectionsEvent b m₀ K A R k m J} ≤ P.real AllBad :=
    ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)
  have hC : 0 ≤ gridIndexConstant A R := (gridIndexConstant_pos A R hA hR).le
  have hlevel (n : ℕ) (hn : n ∈ Finset.range N) :
      P.real (⋃ ih ∈ S n, Bad n ih) ≤ gridIndexConstant A R*gridFailureSeries q₀ (n+J) := by
    have hn' : n+J ≤ gridLastLevel m := by have hh := Finset.mem_range.mp hn; dsimp [N] at hh; omega
    have hjk : n+J ≤ k := hn'.trans hlast
    let d := (1-q₀)^((n+J)^2)+2*Real.exp (-gridVerticalExponent*((n+J : ℕ) : ℝ)^2*(gridWidth k (n+J)))
    have hd : 0 ≤ d := by dsimp [d]; positivity
    have hb (ih : ℤ×ℤ) : P.real (Bad n ih) ≤ d :=
      gridBinGood_failure_bound henv b m₀ K q₀ _ _ _ _ (n+J) (by omega)
        (gridWidth_pos k (n+J)) (htrial (n+J) (by omega) hn')
    calc
      _ ≤ ∑ ih ∈ S n,P.real (Bad n ih) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _ih ∈ S n,d := Finset.sum_le_sum (fun ih _ => hb ih)
      _ = ((S n).card : ℝ)*d := by simp
      _ ≤ (gridIndexConstant A R*(2 : ℝ)^(5*(n+J)))*d :=
        mul_le_mul_of_nonneg_right (gridTestIndices_level_card A R hA hR k m (n+J) hjk) hd
      _ ≤ gridIndexConstant A R*gridFailureSeries q₀ (n+J) := by
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ hC
        exact grid_level_failure_le_series q₀ hq.le hq1 (n+J)
          (gridWidth k (n+J)) (by exact_mod_cast gridWidth_pos k (n+J))
  calc
    _ ≤ P.real AllBad := hprob
    _ ≤ ∑ n ∈ Finset.range N,P.real (⋃ ih ∈ S n, Bad n ih) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ n ∈ Finset.range N,gridIndexConstant A R*gridFailureSeries q₀ (n+J) :=
      Finset.sum_le_sum hlevel
    _ = gridIndexConstant A R*(∑ n ∈ Finset.range N,gridFailureSeries q₀ (n+J)) := by rw [Finset.mul_sum]
    _ ≤ gridIndexConstant A R*(∑' n : ℕ,gridFailureSeries q₀ (n+J)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact (summable_gridFailureSeries q₀ hq).comp_injective (fun _ _ h => Nat.add_right_cancel h)
        |>.sum_le_tsum (Finset.range N) (fun _ _ => gridFailureSeries_nonneg q₀ _)
    _ = _ := rfl

theorem exponential_simultaneous_grid_scales (henv : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b q₀ : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) :
    ∃ k₀ : ℕ, ∀ N : ℕ, ∃ k : ℕ, N < k ∧ k₀ ≤ k ∧
      (∀ j, j ≤ k-k₀ → (1/16 : ℝ)^j*(characteristicLength P τ μ b q₀ k : ℝ) ≤
        (characteristicLength P τ μ b q₀ (k-j) : ℝ)) ∧
      ∀ A R : ℝ, 0 < A → 0 < R → ∀ J : ℕ, 1 ≤ J →
        P.real {ω | (fun e => τ e ω) ∉ gridConnectionsEvent b (μ (direction b))
          (sourceCrossingK μ b) A R k (characteristicExponent P τ μ b q₀ k) J} ≤
          gridFailureTail (gridIndexConstant A R) q₀ J := by
  obtain ⟨k₀,hrec⟩ := exponential_characteristic_record_scales henv μ hμ ht b q₀ hb hq
  have he := (exponential_characteristic_lengths_exist henv μ hμ ht b q₀ hb hq).and
    (actual_grid_trial_probabilities henv μ hμ ht b q₀ hb hq hq1)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp he
  refine ⟨k₀,?_⟩
  intro N
  obtain ⟨k,hk,hkk₀,hkr⟩ := hrec (max N (max N₀ (4*k₀+4)))
  have hkN : N < k := (le_max_left _ _).trans_lt hk
  have hkN₀ : N₀ ≤ k := by omega
  have hklarge : 4*k₀+4 ≤ k := by omega
  obtain ⟨hex,hp⟩ := hN₀ k hkN₀
  have hlast : gridLastLevel (characteristicExponent P τ μ b q₀ k) ≤ k-k₀ := by
    unfold gridLastLevel
    omega
  refine ⟨k,hkN,hkk₀,hkr,?_⟩
  intro A R hA hR J hJ
  apply gridConnectionsEvent_failure_bound henv b (μ (direction b)) (sourceCrossingK μ b)
    A R q₀ hA hR hq hq1.le k (characteristicExponent P τ μ b q₀ k) J hJ
    (hlast.trans (Nat.sub_le _ _))
  intro j _ hj
  exact (hp j hj (hkr j (hj.trans hlast))).le

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointEvents
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

lemma measurableSet_arbitraryEndpointEvent (b m₀ a A R ε : ℝ) (k m : ℕ) :
    MeasurableSet (arbitraryEndpointEvent b m₀ a A R ε k m) :=
  measurableSet_strictLocalizedEvent _ _ _

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointRecords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem exponential_arbitraryEndpoint_record_scales (henv : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b q₀ : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) :
    ∃ k₀ : ℕ, ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧
      (∀ n, n < k n ∧ k₀ ≤ k n ∧
        ∀ j, j ≤ k n-k₀ → (1/16 : ℝ)^j*(characteristicLength P τ μ b q₀ (k n) : ℝ) ≤
          (characteristicLength P τ μ b q₀ (k n-j) : ℝ)) ∧
      ∀ A R ε : ℝ, 0 < A → 0 < R → 0 < ε → ∀ plus : Bool,
        Tendsto (fun n => P.real {ω | (fun e => τ e ω) ∈ arbitraryEndpointEvent b (μ (direction b))
          (extremeSlope μ b plus) A R ε (k n) (characteristicExponent P τ μ b q₀ (k n))}) atTop (𝓝 0) := by
  obtain ⟨k₀,hscales⟩ := exponential_simultaneous_grid_scales henv μ hμ ht b q₀ hb hq hq1
  choose k hk hk₀ hrec hgrid using hscales
  have hkt : Tendsto k atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hn.trans (hk n).le
  refine ⟨k₀,k,hkt,fun n => ⟨hk n,hk₀ n,hrec n⟩,?_⟩
  intro A R ε hA hR hε plus
  have hratio : Tendsto (fun n => (2 : ℝ)^(characteristicExponent P τ μ b q₀ (k n))/(2 : ℝ)^(k n)) atTop atTop := by
    convert (exponential_characteristic_lengths_ratio henv μ hμ ht b q₀ hb hq hq1).comp hkt using 1
    ext n
    simp [characteristicLength]
  have hm : ∀ᶠ n : ℕ in atTop, characteristicExponent P τ μ b q₀ (k n) ≤ 3*k n := by
    filter_upwards [hkt.eventually (exponential_characteristic_lengths_exist henv μ hμ ht b q₀ hb hq)] with n hn
    exact hn.1
  exact exponential_arbitraryEndpoint_tendsto_of_grids henv μ hμ ht b (sourceCrossingK μ b) A R ε q₀
    hb (by unfold sourceCrossingK; positivity) hA hR hε hq plus k
    (fun n => characteristicExponent P τ μ b q₀ (k n)) hkt hratio hm
    (fun J hJ => Eventually.of_forall (fun n => hgrid n A R hA hR J hJ))

theorem actual_arbitraryEndpoint_record_scales (henv : ExponentialEnvironment P τ)
    (b q₀ : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) :
    ∃ k₀ : ℕ, ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧
      (∀ n, n < k n ∧ k₀ ≤ k n ∧
        ∀ j, j ≤ k n-k₀ → (1/16 : ℝ)^j*(characteristicLength P τ actualSourceTimeConstant b q₀ (k n) : ℝ) ≤
          (characteristicLength P τ actualSourceTimeConstant b q₀ (k n-j) : ℝ)) ∧
      ∀ A R ε : ℝ, 0 < A → 0 < R → 0 < ε → ∀ plus : Bool,
        Tendsto (fun n => P.real {ω | (fun e => τ e ω) ∈ arbitraryEndpointEvent b (actualSourceTimeConstant (direction b))
          (extremeSlope actualSourceTimeConstant b plus) A R ε (k n)
          (characteristicExponent P τ actualSourceTimeConstant b q₀ (k n))}) atTop (𝓝 0) :=
  exponential_arbitraryEndpoint_record_scales henv actualSourceTimeConstant actualSourceTimeConstant_norm
    (actualSourceTimeConstant_isTimeConstant henv) b q₀ hb hq hq1

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

lemma eitherEndpointEvent_probability_translate (henv : ExponentialEnvironment P τ)
    (b m₀ am ap A R ε : ℝ) (k m : ℕ) (t : Vertex) :
    P {ω | (fun e => τ e ω) ∈ eitherEndpointEvent b m₀ am ap A R ε k m t} =
      P {ω | (fun e => τ e ω) ∈
        arbitraryEndpointEvent b m₀ am A R ε k m ∪ arbitraryEndpointEvent b m₀ ap A R ε k m} := by
  exact translated_event_probability henv t _
    ((measurableSet_arbitraryEndpointEvent ..).union (measurableSet_arbitraryEndpointEvent ..))

theorem actual_arbitrary_endpoints (henv : ExponentialEnvironment P τ)
    (b q₀ : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) :
    ∃ k₀ : ℕ, ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧
      (∀ n, n < k n ∧ k₀ ≤ k n ∧
        ∀ j, j ≤ k n-k₀ → (1/16 : ℝ)^j*(characteristicLength P τ actualSourceTimeConstant b q₀ (k n) : ℝ) ≤
          (characteristicLength P τ actualSourceTimeConstant b q₀ (k n-j) : ℝ)) ∧
      ∀ A R ε : ℝ, 0 < A → 0 < R → 0 < ε → ∀ t : ℕ → Vertex,
        Tendsto (fun n => P.real {ω | (fun e => τ e ω) ∈ eitherEndpointEvent b
          (actualSourceTimeConstant (direction b)) (extremeSlope actualSourceTimeConstant b false)
          (extremeSlope actualSourceTimeConstant b true) A R ε (k n)
          (characteristicExponent P τ actualSourceTimeConstant b q₀ (k n)) (t n)}) atTop (𝓝 0) := by
  let _ := henv.probability
  obtain ⟨k₀,k,hkt,hrec,hl⟩ := actual_arbitraryEndpoint_record_scales henv b q₀ hb hq hq1
  refine ⟨k₀,k,hkt,hrec,?_⟩
  intro A R ε hA hR hε t
  have hsum := (hl A R ε hA hR hε false).add (hl A R ε hA hR hε true)
  simp only [add_zero] at hsum
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hsum
  intro n
  unfold Measure.real
  rw [eitherEndpointEvent_probability_translate henv]
  exact measureReal_union_le _ _

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SpatialRareEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem actual_spatial_rare_scales_oai (henv : ExponentialEnvironment P τ)
    (b q₀ η : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) (hη : 0 < η)
    (N : ℕ) (S D : ℝ) :
    ∃ k : ℕ, N < k ∧ S ≤ (2 : ℝ)^k ∧
      D*(2 : ℝ)^k ≤ (characteristicLength P τ actualSourceTimeConstant b q₀ k : ℝ) ∧
      ∀ ih : ℤ×ℤ, P.real {ω | (fun e => τ e ω) ∈ spatialRareEvent b
        (actualSourceTimeConstant (direction b)) (extremeSlope actualSourceTimeConstant b false)
        (extremeSlope actualSourceTimeConstant b true) (sourceCrossingK actualSourceTimeConstant b) η k
        (characteristicExponent P τ actualSourceTimeConstant b q₀ k) ih} ≤ 2*q₀ := by
  let _ := henv.probability
  let μ := actualSourceTimeConstant
  have hμ := actualSourceTimeConstant_norm
  have ht := actualSourceTimeConstant_isTimeConstant henv
  obtain ⟨k₀,k,hkt,_hrec,hend⟩ := actual_arbitrary_endpoints henv b q₀ hb hq hq1
  have he := hend 4 4 η (by norm_num) (by norm_num) hη (fun _ => 0)
  have hs := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hkt
  have hr := (exponential_characteristic_lengths_ratio henv μ hμ ht b q₀ hb hq hq1).comp hkt
  have hc := hkt.eventually (exponential_characteristic_lengths_exist henv μ hμ ht b q₀ hb hq)
  obtain ⟨n,hn,hns,hnr,hnc,hne⟩ := ((hkt.eventually (eventually_gt_atTop N)).and
    ((hs.eventually (eventually_ge_atTop S)).and
    ((hr.eventually (eventually_ge_atTop D)).and (hc.and (he.eventually (gt_mem_nhds hq)))))).exists
  refine ⟨k n,hn,hns,(le_div_iff₀ (by positivity : (0 : ℝ) < 2^(k n))).mp hnr,?_⟩
  intro ih
  let m := characteristicExponent P τ μ b q₀ (k n)
  let v := spatialTranslate b (k n) m ih
  let v' := spatialTranslate b (k n) m (ih+(1,0))
  have hp : P.real {ω | (fun e => τ e ω) ∈ eitherEndpointEvent b (μ (direction b))
      (extremeSlope μ b false) (extremeSlope μ b true) 4 4 η (k n) m v} ≤ q₀ := by
    have heq : P.real {ω | (fun e => τ e ω) ∈ eitherEndpointEvent b (μ (direction b))
        (extremeSlope μ b false) (extremeSlope μ b true) 4 4 η (k n) m v} =
      P.real {ω | (fun e => τ e ω) ∈ eitherEndpointEvent b (μ (direction b))
        (extremeSlope μ b false) (extremeSlope μ b true) 4 4 η (k n) m 0} := by
      unfold Measure.real
      rw [eitherEndpointEvent_probability_translate henv,eitherEndpointEvent_probability_translate henv]
    rw [heq]
    exact hne.le
  have hcross : P.real {ω | (fun e => τ e ω) ∈ crossingEvent b (μ (direction b))
      (sourceCrossingK μ b) ((2 : ℝ)^(k n)) ((2 : ℤ)^m) v'} ≤ q₀ := by
    unfold Measure.real
    rw [crossingEvent_probability_translate henv]
    exact hnc.2
  have hu := measureReal_union_le (μ := P)
    {ω | (fun e => τ e ω) ∈ eitherEndpointEvent b (μ (direction b))
      (extremeSlope μ b false) (extremeSlope μ b true) 4 4 η (k n) m v}
    {ω | (fun e => τ e ω) ∈ crossingEvent b (μ (direction b))
      (sourceCrossingK μ b) ((2 : ℝ)^(k n)) ((2 : ℤ)^m) v'}
  change _ ≤ 2*q₀
  exact hu.trans (by linarith)

end PlanarFPP

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PlanarFPP.actual_spatial_rare_scales_oai.{u_1} := @OAI.PlanarFPP.actual_spatial_rare_scales_oai.{u_1}
