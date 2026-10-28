-- Prove2me | solution 1 for OAI.PlanarFPP.actual_differentiable_horizontal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:42:10.230046+00:00
-- url     : https://prove2.me/submissions/9cf9e90a-e119-46c2-9d74-d5a3c25de706

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFirstPassage
import Definitions.Def_OAISPf002
import Theorems.Thm_OAI_PlanarFPP_actualSourceTimeConstant_lattice_limits
import Theorems.Thm_OAI_PlanarFPP_actual_spatial_rare_scales
import Theorems.Thm_OAI_PlanarFPP_ae_eventually_spatial_long_paths

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
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
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

theorem step_edge_translate (a p : Vertex) (d : Step) :
    d.edge (a+p) = shiftEdge a (d.edge p) := by
  cases d <;> simp [Step.edge, shiftEdge, add_assoc]

theorem pathCost_translate (w : Edge → ℝ) (a p : Vertex) (ds : List Step) :
    pathCost (fun e => w (shiftEdge a e)) p ds = pathCost w (a+p) ds := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp [pathCost, step_edge_translate, ih, add_assoc]

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
-- module Solutions.OAIS_PlanarFPP.FirstPassage_LocalizedEvents
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

theorem pathCost_eq_of_agree (w w' : Edge → ℝ) (p : Vertex) (ds : List Step)
    (h : ∀ e ∈ pathEdges p ds, w e=w' e) : pathCost w p ds=pathCost w' p ds := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih =>
    simp only [pathCost]
    rw [h (d.edge p) (by simp [pathEdges])]
    rw [ih (p+d.delta) (fun e he => h e (by simp [pathEdges,he]))]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BKFamilies
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset
variable {α : Type*} [DecidableEq α]

lemma mem_disjointOccurrenceFamily (s : Finset α) (A B : Finset (Finset α)) (x : Finset α) :
    x ∈ disjointOccurrenceFamily s A B ↔
      x ⊆ s ∧ ∃ a ∈ A, ∃ b ∈ B, a ⊆ x ∧ b ⊆ x ∧ Disjoint a b := by
  classical
  simp [disjointOccurrenceFamily]

lemma disjointOccurrenceFamily_mono (s : Finset α) {A A' B B' : Finset (Finset α)}
    (hA : A ⊆ A') (hB : B ⊆ B') :
    disjointOccurrenceFamily s A B ⊆ disjointOccurrenceFamily s A' B' := by
  intro x hx
  obtain ⟨hs,a,ha,b,hb,hax,hbx,hab⟩ := (mem_disjointOccurrenceFamily ..).mp hx
  exact (mem_disjointOccurrenceFamily ..).mpr ⟨hs,a,hA ha,b,hB hb,hax,hbx,hab⟩

lemma UpwardFamily.nonMember {s : Finset α} {A : Finset (Finset α)} {e : α}
    (he : e ∉ s) (hA : UpwardFamily (insert e s) A) :
    UpwardFamily s (A.nonMemberSubfamily e) := by
  constructor
  · intro x hx
    obtain ⟨hx,he'⟩ := mem_nonMemberSubfamily.mp hx
    exact (subset_insert_iff_of_notMem he').mp (hA.1 x hx)
  · intro x hx y hxy hys
    obtain ⟨hx,hex⟩ := mem_nonMemberSubfamily.mp hx
    exact mem_nonMemberSubfamily.mpr ⟨hA.2 x hx y hxy (hys.trans (subset_insert _ _)),
      fun hey => he (hys hey)⟩

lemma UpwardFamily.member {s : Finset α} {A : Finset (Finset α)} {e : α}
    (he : e ∉ s) (hA : UpwardFamily (insert e s) A) :
    UpwardFamily s (A.memberSubfamily e) := by
  constructor
  · intro x hx
    obtain ⟨hx,hex⟩ := mem_memberSubfamily.mp hx
    exact (subset_insert_iff_of_notMem hex).mp ((subset_insert _ _).trans (hA.1 _ hx))
  · intro x hx y hxy hys
    obtain ⟨hx,hex⟩ := mem_memberSubfamily.mp hx
    exact mem_memberSubfamily.mpr ⟨hA.2 _ hx _ (insert_subset_insert _ hxy)
      (insert_subset_insert _ hys),fun hey => he (hys hey)⟩

lemma UpwardFamily.slice_subset {s : Finset α} {A : Finset (Finset α)} {e : α}
    (hA : UpwardFamily (insert e s) A) : A.nonMemberSubfamily e ⊆ A.memberSubfamily e := by
  intro x hx
  obtain ⟨hx,hex⟩ := mem_nonMemberSubfamily.mp hx
  exact mem_memberSubfamily.mpr ⟨hA.2 x hx _ (subset_insert _ _)
    (by intro y hy; rcases mem_insert.mp hy with rfl | hy; exact mem_insert_self _ _; exact hA.1 x hx hy),hex⟩

lemma disjointOccurrence_nonMember (s : Finset α) (A B : Finset (Finset α)) (e : α) (he : e ∉ s) :
    (disjointOccurrenceFamily (insert e s) A B).nonMemberSubfamily e =
      disjointOccurrenceFamily s (A.nonMemberSubfamily e) (B.nonMemberSubfamily e) := by
  ext x
  simp only [mem_nonMemberSubfamily,mem_disjointOccurrenceFamily]
  constructor
  · rintro ⟨⟨hxs,a,ha,b,hb,hax,hbx,hab⟩,hex⟩
    exact ⟨(subset_insert_iff_of_notMem hex).mp hxs,a,⟨ha,fun he => hex (hax he)⟩,
      b,⟨hb,fun he => hex (hbx he)⟩,hax,hbx,hab⟩
  · rintro ⟨hxs,a,⟨ha,hea⟩,b,⟨hb,heb⟩,hax,hbx,hab⟩
    refine ⟨⟨hxs.trans (subset_insert _ _),a,ha,b,hb,hax,hbx,hab⟩,?_⟩
    exact fun hex => he (hxs hex)

lemma erase_subset_of_subset_insert {e : α} {a x : Finset α} (ha : a ⊆ insert e x) :
    a.erase e ⊆ x := by
  intro v hv
  obtain ⟨hne,hva⟩ := mem_erase.mp hv
  exact (mem_insert.mp (ha hva)).resolve_left hne

lemma disjointOccurrence_member (s : Finset α) (A B : Finset (Finset α)) (e : α)
    (he : e ∉ s) (hA : UpwardFamily (insert e s) A) (hB : UpwardFamily (insert e s) B) :
    (disjointOccurrenceFamily (insert e s) A B).memberSubfamily e =
      disjointOccurrenceFamily s (A.memberSubfamily e) (B.nonMemberSubfamily e) ∪
      disjointOccurrenceFamily s (A.nonMemberSubfamily e) (B.memberSubfamily e) := by
  ext x
  simp only [mem_memberSubfamily,mem_union,mem_disjointOccurrenceFamily]
  constructor
  · rintro ⟨⟨hxs,a,ha,b,hb,hax,hbx,hab⟩,hex⟩
    have hxs' : x ⊆ s := (subset_insert_iff_of_notMem hex).mp ((subset_insert _ _).trans hxs)
    by_cases hea : e ∈ a
    · have heb : e ∉ b := fun hb' => Finset.disjoint_left.mp hab hea hb'
      left
      refine ⟨hxs',a.erase e,?_,b,mem_nonMemberSubfamily.mpr ⟨hb,heb⟩,erase_subset_of_subset_insert hax,?_,?_⟩
      · exact ⟨by simpa [insert_erase hea] using ha,notMem_erase _ _⟩
      · exact (subset_insert_iff_of_notMem heb).mp hbx
      · exact hab.mono_left (erase_subset _ _)
    · right
      refine ⟨hxs',a,mem_nonMemberSubfamily.mpr ⟨ha,hea⟩,b.erase e,?_,
        (subset_insert_iff_of_notMem hea).mp hax,erase_subset_of_subset_insert hbx,?_⟩
      · refine ⟨hB.2 b hb _ (by intro v hv; by_cases heq : v=e; exact mem_insert.mpr (Or.inl heq); exact mem_insert.mpr (Or.inr (mem_erase.mpr ⟨heq,hv⟩))) ?_,notMem_erase _ _⟩
        intro v hv
        rcases mem_insert.mp hv with rfl | hv
        · exact mem_insert_self _ _
        · exact hB.1 b hb (mem_of_mem_erase hv)
      · exact hab.mono_right (erase_subset _ _)
  · intro hx
    rcases hx with ⟨hxs,a,⟨ha,hea⟩,b,hb,hax,hbx,hab⟩ | ⟨hxs,a,ha,b,⟨hb,heb⟩,hax,hbx,hab⟩
    · obtain ⟨hb,heb⟩ := mem_nonMemberSubfamily.mp hb
      refine ⟨⟨insert_subset_insert _ hxs,insert e a,ha,b,hb,
        insert_subset_insert _ hax,hbx.trans (subset_insert _ _),?_⟩,fun h => he (hxs h)⟩
      exact Finset.disjoint_insert_left.mpr ⟨heb,hab⟩
    · obtain ⟨ha,hea⟩ := mem_nonMemberSubfamily.mp ha
      refine ⟨⟨insert_subset_insert _ hxs,a,ha,insert e b,hb,
        hax.trans (subset_insert _ _),insert_subset_insert _ hbx,?_⟩,fun h => he (hxs h)⟩
      exact Finset.disjoint_insert_right.mpr ⟨hea,hab⟩

theorem finite_fair_BK (s : Finset α) (A B : Finset (Finset α))
    (hA : UpwardFamily s A) (hB : UpwardFamily s B) :
    2^s.card*(disjointOccurrenceFamily s A B).card ≤ A.card*B.card := by
  classical
  induction s using Finset.induction_on generalizing A B with
  | empty =>
    have hAs := hA.1
    have hBs := hB.1
    simp_rw [subset_empty,← subset_singleton_iff',subset_singleton_iff] at hAs hBs
    rcases hAs with rfl | rfl <;> rcases hBs with rfl | rfl <;>
      simp [disjointOccurrenceFamily]
  | @insert e s he ih =>
    let D₀ := disjointOccurrenceFamily s (A.nonMemberSubfamily e) (B.nonMemberSubfamily e)
    let D₁ := disjointOccurrenceFamily s (A.memberSubfamily e) (B.nonMemberSubfamily e)
    let D₂ := disjointOccurrenceFamily s (A.nonMemberSubfamily e) (B.memberSubfamily e)
    have h₀₁ : D₀ ⊆ D₁ := disjointOccurrenceFamily_mono s hA.slice_subset (Subset.rfl)
    have h₀₂ : D₀ ⊆ D₂ := disjointOccurrenceFamily_mono s (Subset.rfl) hB.slice_subset
    have hcount : (disjointOccurrenceFamily (insert e s) A B).card ≤ D₁.card+D₂.card := by
      rw [← card_memberSubfamily_add_card_nonMemberSubfamily e,
        disjointOccurrence_member s A B e he hA hB,disjointOccurrence_nonMember s A B e he]
      have hh := Finset.card_le_card (subset_inter h₀₁ h₀₂)
      have hu := Finset.card_union_add_card_inter D₁ D₂
      change (D₁ ∪ D₂).card+D₀.card ≤ D₁.card+D₂.card
      omega
    have h₁ := ih _ _ (hA.member he) (hB.nonMember he)
    have h₂ := ih _ _ (hA.nonMember he) (hB.member he)
    have hca := Finset.card_le_card hA.slice_subset
    have hcb := Finset.card_le_card hB.slice_subset
    have hcross := mul_add_mul_le_mul_add_mul hca hcb
    have ha := card_memberSubfamily_add_card_nonMemberSubfamily e A
    have hb := card_memberSubfamily_add_card_nonMemberSubfamily e B
    have hmul := Nat.mul_le_mul_left (2^s.card) hcount
    rw [Finset.card_insert_of_notMem he,pow_succ]
    dsimp [D₁,D₂] at hmul
    nlinarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BKRepeated
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset
variable {α : Type*} [DecidableEq α]

lemma upward_disjointOccurrence (s : Finset α) (A B : Finset (Finset α)) :
    UpwardFamily s (disjointOccurrenceFamily s A B) := by
  constructor
  · intro x hx
    exact ((mem_disjointOccurrenceFamily ..).mp hx).1
  · intro x hx y hxy hys
    obtain ⟨_,a,ha,b,hb,hax,hbx,hab⟩ := (mem_disjointOccurrenceFamily ..).mp hx
    exact (mem_disjointOccurrenceFamily ..).mpr ⟨hys,a,ha,b,hb,hax.trans hxy,hbx.trans hxy,hab⟩

omit [DecidableEq α] in
lemma fairFamilyMass_nonneg (s : Finset α) (A : Finset (Finset α)) :
    0 ≤ fairFamilyMass s A := by unfold fairFamilyMass; positivity

omit [DecidableEq α] in
lemma fairFamilyMass_mono (s : Finset α) {A B : Finset (Finset α)} (h : A ⊆ B) :
    fairFamilyMass s A ≤ fairFamilyMass s B := by
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_le_card h) (by positivity)

omit [DecidableEq α] in
lemma fairFamilyMass_powerset (s : Finset α) : fairFamilyMass s s.powerset = 1 := by
  simp [fairFamilyMass,Finset.card_powerset]

lemma finite_fair_BK_mass (s : Finset α) (A B : Finset (Finset α))
    (hA : UpwardFamily s A) (hB : UpwardFamily s B) :
    fairFamilyMass s (disjointOccurrenceFamily s A B) ≤ fairFamilyMass s A * fairFamilyMass s B := by
  have h := finite_fair_BK s A B hA hB
  have hr : (2:ℝ)^s.card * (disjointOccurrenceFamily s A B).card ≤ (A.card:ℝ)*B.card := by
    exact_mod_cast h
  unfold fairFamilyMass
  rw [div_mul_div_comm,div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos (by norm_num : (0:ℝ)<2) s.card]

lemma upward_iteratedDisjointOccurrence (s : Finset α) (As : List (Finset (Finset α))) :
    UpwardFamily s (iteratedDisjointOccurrence s As) := by
  cases As with
  | nil =>
    constructor
    · intro x hx; exact mem_powerset.mp hx
    · intro x hx y hxy hys; exact mem_powerset.mpr hys
  | cons A As => exact upward_disjointOccurrence s A _

theorem finite_fair_BK_repeated (s : Finset α) (As : List (Finset (Finset α)))
    (hAs : ∀ A ∈ As, UpwardFamily s A) :
    fairFamilyMass s (iteratedDisjointOccurrence s As) ≤ (As.map (fairFamilyMass s)).prod := by
  induction As with
  | nil => simp [iteratedDisjointOccurrence,fairFamilyMass_powerset]
  | cons A As ih =>
    have hA := hAs A (List.mem_cons_self ..)
    have htail : ∀ B ∈ As, UpwardFamily s B := fun B hB => hAs B (List.mem_cons_of_mem _ hB)
    exact (finite_fair_BK_mass s A _ hA (upward_iteratedDisjointOccurrence s As)).trans
      (by simpa using mul_le_mul_of_nonneg_left (ih htail) (fairFamilyMass_nonneg s A))

lemma mem_foldr_union (ws : List (Finset α)) (a : α) :
    a ∈ ws.foldr (· ∪ ·) ∅ ↔ ∃ v ∈ ws, a ∈ v := by
  induction ws with
  | nil => simp
  | cons v vs ih => simp [ih]

theorem certificates_mem_iterated (s : Finset α) (As : List (Finset (Finset α)))
    (ws : List (Finset α)) (x : Finset α) (hxs : x ⊆ s)
    (hmem : List.Forall₂ (fun w A => w ∈ A) ws As)
    (hdis : ws.Pairwise Disjoint) (hsub : ∀ w ∈ ws, w ⊆ x) :
    x ∈ iteratedDisjointOccurrence s As := by
  induction hmem generalizing x with
  | nil => exact mem_powerset.mpr hxs
  | @cons w A ws As hw hmem ih =>
    have hd := List.pairwise_cons.mp hdis
    let u : Finset α := ws.foldr (· ∪ ·) ∅
    have hu : ∀ a, a ∈ u ↔ ∃ v ∈ ws, a ∈ v := mem_foldr_union ws
    have hux : u ⊆ x := by
      intro a ha
      obtain ⟨v,hv,hav⟩ := (hu a).mp ha
      exact hsub v (List.mem_cons_of_mem _ hv) hav
    have htail : ∀ v ∈ ws, v ⊆ u := by
      intro v hv a ha
      exact (hu a).mpr ⟨v,hv,ha⟩
    have hwu : Disjoint w u := by
      apply Finset.disjoint_left.mpr
      intro a haw hau
      obtain ⟨v,hv,hav⟩ := (hu a).mp hau
      exact Finset.disjoint_left.mp (hd.1 v hv) haw hav
    exact (mem_disjointOccurrenceFamily ..).mpr ⟨hxs,w,hw,u,
      ih u (hux.trans hxs) hd.2 htail,hsub w (List.mem_cons_self ..),hux,hwu⟩

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BKForcing
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset
variable {α : Type*} [DecidableEq α]

lemma ForcesBits.positive_certificate {s : Finset α} {A : Finset (Finset α)}
    {x c : Finset α} (hxs : x ⊆ s) (h : ForcesBits s A x c) : x ∩ c ∈ A := by
  apply h (x ∩ c) ((inter_subset_left).trans hxs)
  intro e he
  simp [he]

theorem forcing_certificates_mem (s : Finset α) (As : List (Finset (Finset α)))
    (cs : List (Finset α)) (x : Finset α) (hxs : x ⊆ s)
    (hforce : List.Forall₂ (fun c A => ForcesBits s A x c) cs As)
    (hdis : cs.Pairwise Disjoint) : x ∈ iteratedDisjointOccurrence s As := by
  apply certificates_mem_iterated s As (cs.map (fun c => x ∩ c)) x hxs
  · clear hdis
    induction hforce with
    | nil => exact List.Forall₂.nil
    | cons h ht ih => exact List.Forall₂.cons (h.positive_certificate hxs) ih
  · rw [List.pairwise_map]
    exact hdis.imp (fun hab => hab.mono (inter_subset_right) (inter_subset_right))
  · intro w hw
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hw
    exact inter_subset_left

theorem finite_fair_BK_forcing (s : Finset α) (As : List (Finset (Finset α)))
    (D : Finset (Finset α)) (hAs : ∀ A ∈ As, UpwardFamily s A)
    (hD : ∀ x ∈ D, x ⊆ s ∧ ∃ cs : List (Finset α),
      List.Forall₂ (fun c A => ForcesBits s A x c) cs As ∧ cs.Pairwise Disjoint) :
    fairFamilyMass s D ≤ (As.map (fairFamilyMass s)).prod := by
  apply (fairFamilyMass_mono s ?_).trans (finite_fair_BK_repeated s As hAs)
  intro x hx
  obtain ⟨hxs,cs,hforce,hdis⟩ := hD x hx
  exact forcing_certificates_mem s As cs x hxs hforce hdis

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BKDyadicPaths
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset

lemma dyadicSurvival_mono (t : ℕ) {x y : Finset (Edge × Fin t)} (hxy : x ⊆ y) (e : Edge) :
    dyadicSurvival t x e ≤ dyadicSurvival t y e := by
  apply Finset.sum_le_sum
  intro h _
  by_cases hx : (e,h) ∈ x
  · simp [hx,hxy hx]
  · simp only [hx,↓reduceIte]
    split_ifs <;> positivity

lemma dyadicSurvival_eq (t : ℕ) (x y : Finset (Edge × Fin t)) (e : Edge)
    (h : ∀ a : Fin t, (e,a) ∈ x ↔ (e,a) ∈ y) :
    dyadicSurvival t x e = dyadicSurvival t y e := by
  apply Finset.sum_congr rfl
  intro a _
  simp only [h a]

lemma pathCost_le_of_edges {w v : Edge → ℝ} (p : Vertex) (ds : List Step)
    (h : ∀ e ∈ pathEdges p ds, w e ≤ v e) : pathCost w p ds ≤ pathCost v p ds := by
  induction ds generalizing p with
  | nil => exact le_rfl
  | cons d ds ih =>
    exact add_le_add (h _ (by simp [pathEdges]))
      (ih _ (fun e he => h e (by simp [pathEdges,he])))

lemma DyadicPathGood.mono {t : ℕ} {x y : Finset (Edge × Fin t)} {p : StrictPathWitness}
    (h : DyadicPathGood t x p) (hxy : x ⊆ y) : DyadicPathGood t y p := by
  constructor
  · intro e he
    exact (h.1 e he).trans_le (dyadicSurvival_mono t hxy e)
  · apply lt_of_le_of_lt (pathCost_le_of_edges p.start p.steps ?_) h.2
    intro e he
    exact neg_le_neg (Real.log_le_log (h.1 e he) (dyadicSurvival_mono t hxy e))

lemma DyadicPathGood.of_agree {t : ℕ} {x y : Finset (Edge × Fin t)} {p : StrictPathWitness}
    (h : DyadicPathGood t x p)
    (hxy : ∀ a ∈ p.bits t, a ∈ y ↔ a ∈ x) : DyadicPathGood t y p := by
  have heq : ∀ e ∈ p.edges, dyadicSurvival t y e = dyadicSurvival t x e := by
    intro e he
    apply dyadicSurvival_eq
    intro a
    exact hxy (e,a) (by simp [StrictPathWitness.bits,he])
  constructor
  · intro e he; rw [heq e he]; exact h.1 e he
  · have hc := pathCost_eq_of_agree
      (fun e => -Real.log (dyadicSurvival t y e))
      (fun e => -Real.log (dyadicSurvival t x e)) p.start p.steps
      (fun e he => congrArg (fun a => -Real.log a) (heq e he))
    rw [hc]; exact h.2

lemma mem_dyadicPathFamily (S : Finset Edge) (t : ℕ) (F : Set StrictPathWitness)
    (x : Finset (Edge × Fin t)) :
    x ∈ dyadicPathFamily S t F ↔ x ⊆ S ×ˢ univ ∧
      ∃ p ∈ F, p.edges ⊆ S ∧ DyadicPathGood t x p := by
  classical
  simp [dyadicPathFamily]

lemma upward_dyadicPathFamily (S : Finset Edge) (t : ℕ) (F : Set StrictPathWitness) :
    UpwardFamily (S ×ˢ univ) (dyadicPathFamily S t F) := by
  constructor
  · intro x hx; exact ((mem_dyadicPathFamily ..).mp hx).1
  · intro x hx y hxy hys
    obtain ⟨_,p,hp,he,hgood⟩ := (mem_dyadicPathFamily ..).mp hx
    exact (mem_dyadicPathFamily ..).mpr ⟨hys,p,hp,he,hgood.mono hxy⟩

lemma dyadic_path_forces (S : Finset Edge) (t : ℕ) (F : Set StrictPathWitness)
    (x : Finset (Edge × Fin t)) (p : StrictPathWitness)
    (hp : p ∈ F) (he : p.edges ⊆ S) (hgood : DyadicPathGood t x p) :
    ForcesBits (S ×ˢ univ) (dyadicPathFamily S t F) x (p.bits t) := by
  intro y hys hxy
  exact (mem_dyadicPathFamily ..).mpr ⟨hys,p,hp,he,hgood.of_agree hxy⟩

lemma StrictPathWitness.disjoint_bits {p q : StrictPathWitness} (t : ℕ)
    (h : Disjoint p.edges q.edges) : Disjoint (p.bits t) (q.bits t) := by
  apply Finset.disjoint_left.mpr
  intro a hp hq
  exact Finset.disjoint_left.mp h (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hq).1

theorem dyadic_strict_path_BK (S : Finset Edge) (t : ℕ) (Fs : List (Set StrictPathWitness)) :
    fairFamilyMass (S ×ˢ univ) (dyadicDisjointPathFamily S t Fs) ≤
      (Fs.map (fun F => fairFamilyMass (S ×ˢ univ) (dyadicPathFamily S t F))).prod := by
  apply (finite_fair_BK_forcing (S ×ˢ univ) (Fs.map (dyadicPathFamily S t))
    (dyadicDisjointPathFamily S t Fs) ?_ ?_).trans_eq
      (by simp only [List.map_map,Function.comp_def])
  · intro A hA
    obtain ⟨F,_,rfl⟩ := List.mem_map.mp hA
    exact upward_dyadicPathFamily S t F
  · intro x hx
    simp only [dyadicDisjointPathFamily,mem_filter,mem_powerset] at hx
    obtain ⟨hxs,ps,hps,hd⟩ := hx
    refine ⟨hxs,ps.map (fun p => p.bits t),?_,?_⟩
    · clear hd
      induction hps with
      | nil => exact List.Forall₂.nil
      | cons h ht ih =>
        exact List.Forall₂.cons (dyadic_path_forces S t _ x _ h.1 h.2.1 h.2.2) ih
    · rw [List.pairwise_map]
      exact hd.imp (fun h => StrictPathWitness.disjoint_bits t h)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BKBinaryRanks
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset

lemma dyadicPositions_subset (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) :
    dyadicPositions t x e ⊆ range t := by
  intro a ha
  obtain ⟨h,_,rfl⟩ := mem_image.mp ha
  rw [mem_range]
  have := h.isLt
  omega

lemma mem_dyadicPositions (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) (h : Fin t) :
    t-(h.val+1) ∈ dyadicPositions t x e ↔ (e,h) ∈ x := by
  constructor
  · intro hm
    obtain ⟨a,ha,he⟩ := mem_image.mp hm
    have heq : a=h := by apply Fin.ext; have := a.isLt; have := h.isLt; omega
    subst a
    exact (mem_filter.mp ha).2
  · intro hm
    exact mem_image.mpr ⟨h,mem_filter.mpr ⟨mem_univ _,hm⟩,rfl⟩

lemma sum_two_powers_range (t : ℕ) : (∑ a ∈ range t, 2^a)+1=2^t := by
  induction t with
  | zero => simp
  | succ t ih => rw [sum_range_succ,pow_succ]; omega

lemma dyadicRank_lt (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) :
    dyadicRank t x e < 2^t := by
  have h := sum_le_sum_of_subset_of_nonneg (f := fun a : ℕ => 2^a) (dyadicPositions_subset t x e)
    (fun _ _ _ => Nat.zero_le _)
  have hg := sum_two_powers_range t
  unfold dyadicRank
  omega

lemma dyadicRank_eq_iff (t : ℕ) (x y : Finset (Edge × Fin t)) (e : Edge) :
    dyadicRank t x e = dyadicRank t y e ↔ ∀ h : Fin t, (e,h) ∈ x ↔ (e,h) ∈ y := by
  constructor
  · intro he
    have hp : dyadicPositions t x e = dyadicPositions t y e := by
      have hh := congrArg (fun n : ℕ => n.bitIndices.toFinset) he
      simpa [dyadicRank] using hh
    intro h
    rw [← mem_dyadicPositions t x e h,← mem_dyadicPositions t y e h,hp]
  · intro he
    have hp : dyadicPositions t x e = dyadicPositions t y e := by
      unfold dyadicPositions
      congr 1
      ext h
      simp [he h]
    simp [dyadicRank,hp]

lemma dyadicRanks_injective (S : Finset Edge) (t : ℕ) {x y : Finset (Edge × Fin t)}
    (hx : x ⊆ S ×ˢ univ) (hy : y ⊆ S ×ˢ univ)
    (h : ∀ e ∈ S, dyadicRank t x e = dyadicRank t y e) : x=y := by
  ext ⟨e,a⟩
  by_cases he : e ∈ S
  · exact (dyadicRank_eq_iff t x y e).mp (h e he) a
  · have hn : (e,a) ∉ x := fun hm => he (mem_product.mp (hx hm)).1
    have hn' : (e,a) ∉ y := fun hm => he (mem_product.mp (hy hm)).1
    simp [hn,hn']

lemma dyadicRank_sum (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) :
    dyadicRank t x e = ∑ h : Fin t, if (e,h) ∈ x then 2^(t-(h.val+1)) else 0 := by
  unfold dyadicRank dyadicPositions
  rw [sum_image]
  · simp only [sum_filter]
  · intro a _ b _ hab
    change t-(a.val+1)=t-(b.val+1) at hab
    apply Fin.ext
    have := a.isLt
    have := b.isLt
    omega

lemma dyadicSurvival_eq_rank (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) :
    dyadicSurvival t x e = (dyadicRank t x e : ℝ)/(2:ℝ)^t := by
  rw [dyadicRank_sum]
  simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_zero]
  rw [Finset.sum_div]
  unfold dyadicSurvival
  apply sum_congr rfl
  intro h _
  by_cases hm : (e,h) ∈ x
  · simp only [hm,↓reduceIte]
    have hh : t=(t-(h.val+1))+(h.val+1) := by omega
    have hp : (2:ℝ)^t = 2^(t-(h.val+1))*2^(h.val+1) := by rw [← pow_add,← hh]
    rw [hp]
    field_simp
  · simp [hm]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BKQuantization
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Filter
open scoped Topology

lemma roundedSurvival_le (t : ℕ) (r : ℝ) : roundedSurvival t r ≤ Real.exp (-r) := by
  rw [roundedSurvival,div_le_iff₀ (by positivity)]
  simpa only [mul_comm] using Nat.floor_le (show 0 ≤ (2:ℝ)^t*Real.exp (-r) by positivity)

lemma roundedSurvival_tendsto (r : ℝ) :
    Tendsto (fun t => roundedSurvival t r) atTop (𝓝 (Real.exp (-r))) := by
  have h := (tendsto_nat_floor_mul_div_atTop (Real.exp_pos (-r)).le).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))
  simpa [roundedSurvival,Function.comp_def,mul_comm] using h

lemma roundedSurvival_eventually_pos (r : ℝ) :
    ∀ᶠ t in atTop, 0 < roundedSurvival t r :=
  (roundedSurvival_tendsto r).eventually (lt_mem_nhds (Real.exp_pos (-r)))

lemma roundedEdgeCost_ge (t : ℕ) (r : ℝ) (hp : 0 < roundedSurvival t r) :
    r ≤ roundedEdgeCost t r := by
  have h := Real.log_le_log hp (roundedSurvival_le t r)
  rw [Real.log_exp] at h
  unfold roundedEdgeCost
  linarith

lemma roundedEdgeCost_tendsto (r : ℝ) :
    Tendsto (fun t => roundedEdgeCost t r) atTop (𝓝 r) := by
  have h := ((Real.continuousAt_log (Real.exp_ne_zero (-r))).tendsto.comp
    (roundedSurvival_tendsto r)).neg
  simpa [roundedEdgeCost,Real.log_exp] using h

lemma rounded_pathCost_tendsto (w : Edge → ℝ) (p : Vertex) (ds : List Step) :
    Tendsto (fun t => pathCost (fun e => roundedEdgeCost t (w e)) p ds) atTop
      (𝓝 (pathCost w p ds)) := by
  induction ds generalizing p with
  | nil => exact tendsto_const_nhds
  | cons d ds ih => exact (roundedEdgeCost_tendsto (w (d.edge p))).add (ih _)

lemma RoundedPathGood.original {t : ℕ} {w : Edge → ℝ} {p : StrictPathWitness}
    (h : RoundedPathGood t w p) : p.Good w := by
  exact lt_of_le_of_lt (pathCost_le_of_edges p.start p.steps
    (fun e he => roundedEdgeCost_ge t (w e) (h.1 e he))) h.2

lemma StrictPathWitness.Good.eventually_rounded {w : Edge → ℝ} {p : StrictPathWitness}
    (h : p.Good w) : ∀ᶠ t in atTop, RoundedPathGood t w p := by
  have he : ∀ᶠ t in atTop, ∀ e ∈ p.edges, 0 < roundedSurvival t (w e) := by
    rw [Filter.eventually_all_finset]
    intro e _
    exact roundedSurvival_eventually_pos (w e)
  have hc := (rounded_pathCost_tendsto w p.start p.steps).eventually (gt_mem_nhds h)
  exact he.and hc

lemma strict_path_list_eventually_rounded (w : Edge → ℝ) (ps : List StrictPathWitness)
    (h : ∀ p ∈ ps, p.Good w) : ∀ᶠ t in atTop, ∀ p ∈ ps, RoundedPathGood t w p := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hp := (h p (List.mem_cons_self ..)).eventually_rounded
    have ht := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    filter_upwards [hp,ht] with t hp ht q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp
    · exact ht q hq

lemma RoundedDisjointPaths.original {S : Finset Edge} {Fs : List (Set StrictPathWitness)}
    {t : ℕ} {w : Edge → ℝ} (h : RoundedDisjointPaths S Fs t w) : StrictDisjointPaths S Fs w := by
  obtain ⟨ps,hps,hd⟩ := h
  refine ⟨ps,?_,hd⟩
  exact hps.imp (fun _ _ h => ⟨h.1,h.2.1,h.2.2.original⟩)

lemma StrictDisjointPaths.eventually_rounded {S : Finset Edge} {Fs : List (Set StrictPathWitness)}
    {w : Edge → ℝ} (h : StrictDisjointPaths S Fs w) :
    ∀ᶠ t in atTop, RoundedDisjointPaths S Fs t w := by
  obtain ⟨ps,hps,hd⟩ := h
  have hg : ∀ p ∈ ps, p.Good w := by
    clear hd
    induction hps with
    | nil => simp
    | cons hp hps ih =>
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hp.2.2
      · exact ih q hq
  filter_upwards [strict_path_list_eventually_rounded w ps hg] with t ht
  refine ⟨ps,?_,hd⟩
  clear hd hg
  induction hps with
  | nil => exact List.Forall₂.nil
  | @cons p F ps Fs hp hps ih =>
    exact List.Forall₂.cons ⟨hp.1,hp.2.1,ht p (List.mem_cons_self ..)⟩
      (ih (fun q hq => ht q (List.mem_cons_of_mem _ hq)))

theorem strict_disjoint_eventual_rounded_iff (S : Finset Edge) (Fs : List (Set StrictPathWitness))
    (w : Edge → ℝ) :
    StrictDisjointPaths S Fs w ↔ ∀ᶠ t in atTop, RoundedDisjointPaths S Fs t w := by
  constructor
  · exact StrictDisjointPaths.eventually_rounded
  · intro h
    obtain ⟨t,ht⟩ := h.exists
    exact ht.original

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BKExponentialQuantiles
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

lemma ExponentialEnvironment.edge_tail_real (h : ExponentialEnvironment P τ)
    (e : Edge) (r : ℝ) (hr : 0 ≤ r) : P.real {ω | r < τ e ω} = Real.exp (-r) := by
  let _ := h.probability
  have hm : P {ω | τ e ω ≤ r} = expMeasure 1 (Iic r) := by
    rw [← h.marginal e,Measure.map_apply (h.measurable e) measurableSet_Iic]
    rfl
  have hc : P.real {ω | τ e ω ≤ r} = 1-Real.exp (-r) := by
    change (P {ω | τ e ω ≤ r}).toReal = _
    rw [hm,← measureReal_def,← cdf_eq_real,cdf_expMeasure_eq (by norm_num)]
    simp [hr]
  have he : {ω | r < τ e ω} = {ω | τ e ω ≤ r}ᶜ := by ext ω; simp
  rw [he,measureReal_compl (measurableSet_le (h.measurable e) measurable_const),hc]
  simp

theorem ExponentialEnvironment.survival_lt_real (h : ExponentialEnvironment P τ)
    (e : Edge) (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    P.real {ω | Real.exp (-τ e ω) < u} = u := by
  by_cases hz : u=0
  · subst u
    have he : {ω | Real.exp (-τ e ω) < 0} = ∅ := by
      ext ω; simp [not_lt.mpr (Real.exp_pos (-τ e ω)).le]
    rw [he]; simp
  · have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
    have he : {ω | Real.exp (-τ e ω) < u} = {ω | -Real.log u < τ e ω} := by
      ext ω
      rw [mem_ofPred_eq,mem_ofPred_eq,← Real.exp_log hup,Real.exp_lt_exp]
      simp only [Real.log_exp]
      constructor <;> intro hh <;> linarith
    rw [he,h.edge_tail_real e (-Real.log u) (neg_nonneg.mpr (Real.log_nonpos hu hu1))]
    simp [Real.exp_log hup]

theorem ExponentialEnvironment.survival_bin_real (h : ExponentialEnvironment P τ)
    (e : Edge) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    P.real {ω | a ≤ Real.exp (-τ e ω) ∧ Real.exp (-τ e ω) < b} = b-a := by
  let _ := h.probability
  let A : Set Ω := {ω | Real.exp (-τ e ω) < a}
  let B : Set Ω := {ω | Real.exp (-τ e ω) < b}
  have hA : MeasurableSet A := measurableSet_lt (Real.measurable_exp.comp (h.measurable e).neg) measurable_const
  have hAB : A ⊆ B := fun ω hω => lt_of_lt_of_le hω hab
  have he : {ω | a ≤ Real.exp (-τ e ω) ∧ Real.exp (-τ e ω) < b} = B \ A := by
    ext ω
    simp only [mem_ofPred_eq,mem_sdiff,A,B,not_lt]
    tauto
  rw [he,measureReal_sdiff hAB hA]
  exact congrArg₂ (·-·) (h.survival_lt_real e b (ha.trans hab) hb)
    (h.survival_lt_real e a ha (hab.trans hb))

theorem ExponentialEnvironment.survival_rank_real (h : ExponentialEnvironment P τ)
    (e : Edge) (m i : ℕ) (hm : 0 < m) (hi : i < m) :
    P.real {ω | ⌊(m:ℝ)*Real.exp (-τ e ω)⌋₊ = i} = 1/(m:ℝ) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have he : {ω | ⌊(m:ℝ)*Real.exp (-τ e ω)⌋₊ = i} =
      {ω | (i:ℝ)/m ≤ Real.exp (-τ e ω) ∧ Real.exp (-τ e ω) < ((i:ℝ)+1)/m} := by
    ext ω
    rw [mem_ofPred_eq,mem_ofPred_eq,Nat.floor_eq_iff (by positivity)]
    rw [div_le_iff₀ hm',lt_div_iff₀ hm']
    simp only [mul_comm]
  have hu : ((i:ℝ)+1)/m ≤ 1 := by
    rw [div_le_iff₀ hm']
    have hi' : (i:ℝ)+1 ≤ m := by exact_mod_cast (show i+1 ≤ m by omega)
    simpa using hi'
  rw [he,h.survival_bin_real e ((i:ℝ)/m) (((i:ℝ)+1)/m) (by positivity)
    (div_le_div_of_nonneg_right (by linarith) hm'.le) hu]
  ring

theorem ExponentialEnvironment.survival_ranks_joint_real (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (m : ℕ) (hm : 0 < m) (i : Edge → ℕ) (hi : ∀ e ∈ S, i e < m) :
    P.real {ω | ∀ e ∈ S, ⌊(m:ℝ)*Real.exp (-τ e ω)⌋₊ = i e} = (1/(m:ℝ))^S.card := by
  let A : Edge → Set (Edge → ℝ) := fun e => {w | ⌊(m:ℝ)*Real.exp (-w e)⌋₊ = i e}
  have hA : ∀ e ∈ S, MeasurableSet (A e) := by
    intro e _
    apply measurableSet_eq_fun _ measurable_const
    fun_prop
  have hAS : ∀ e ∈ S, DependsOnEdges (A e) {e} := by
    intro e _ w w' hw
    have he := hw e (Finset.mem_singleton_self e)
    simp only [A,mem_ofPred_eq,he]
  have hd : Set.Pairwise (↑S : Set Edge) (fun e f => Disjoint ({e} : Finset Edge) {f}) := by
    intro e _ f _ hef
    simpa using hef
  have hj := disjoint_edge_events_inter_probability h S A (fun e => {e}) hA hAS hd
  have hr := congrArg ENNReal.toReal hj
  simp only [ENNReal.toReal_prod] at hr
  change P.real _ = ∏ e ∈ S, P.real _ at hr
  dsimp [A] at hr
  rw [hr]
  calc
    _ = ∏ _e ∈ S, (1/(m:ℝ)) := by
      apply Finset.prod_congr rfl
      intro e he
      exact h.survival_rank_real e m (i e) hm (hi e he)
    _ = _ := by simp

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BKBitLaw
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

lemma measurableSet_dyadicRankCell (hτ : ∀ e, Measurable (τ e))
    (S : Finset Edge) (t : ℕ) (x : Finset (Edge × Fin t)) :
    MeasurableSet (dyadicRankCell τ S t x) := by
  simp only [dyadicRankCell,ofPred_forall]
  apply MeasurableSet.iInter
  intro e
  apply MeasurableSet.iInter
  intro _
  apply measurableSet_eq_fun _ measurable_const
  fun_prop

omit [MeasurableSpace Ω] in
lemma dyadicRankCell_disjoint (τ : Edge → Ω → ℝ) (S : Finset Edge) (t : ℕ)
    {x y : Finset (Edge × Fin t)} (hx : x ⊆ S ×ˢ Finset.univ) (hy : y ⊆ S ×ˢ Finset.univ) (hxy : x ≠ y) :
    Disjoint (dyadicRankCell τ S t x) (dyadicRankCell τ S t y) := by
  apply Set.disjoint_left.mpr
  intro ω hωx hωy
  apply hxy
  exact dyadicRanks_injective S t hx hy (fun e he => (hωx e he).symm.trans (hωy e he))

lemma ExponentialEnvironment.dyadicRankCell_real (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (t : ℕ) (x : Finset (Edge × Fin t)) :
    P.real (dyadicRankCell τ S t x) = 1/(2:ℝ)^((S ×ˢ (Finset.univ : Finset (Fin t))).card) := by
  have hh := h.survival_ranks_joint_real S (2^t) (by positivity) (dyadicRank t x)
    (fun e _ => dyadicRank_lt t x e)
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hh
  change P.real (dyadicRankCell τ S t x) = _ at hh
  rw [hh,one_div_pow,← pow_mul,card_product,card_univ,Fintype.card_fin]
  rw [Nat.mul_comm]

theorem ExponentialEnvironment.dyadicRankCells_real (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (t : ℕ) (A : Finset (Finset (Edge × Fin t)))
    (hA : A ⊆ (S ×ˢ Finset.univ).powerset) :
    P.real (⋃ x ∈ A, dyadicRankCell τ S t x) = fairFamilyMass (S ×ˢ Finset.univ) A := by
  classical
  let _ := h.probability
  have hd : Set.PairwiseDisjoint (↑A : Set (Finset (Edge × Fin t))) (dyadicRankCell τ S t) := by
    intro x hx y hy hxy
    exact dyadicRankCell_disjoint τ S t (mem_powerset.mp (hA hx)) (mem_powerset.mp (hA hy)) hxy
  have he := measure_biUnion_finset (μ := P) hd (fun x _ => measurableSet_dyadicRankCell h.measurable S t x)
  have hr := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)] at hr
  change P.real (⋃ x ∈ A, dyadicRankCell τ S t x) = ∑ x ∈ A, P.real (dyadicRankCell τ S t x) at hr
  rw [hr]
  simp only [h.dyadicRankCell_real,sum_const,nsmul_eq_mul,fairFamilyMass,div_eq_mul_inv,one_mul]

theorem ExponentialEnvironment.ae_dyadicRankCell (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (t : ℕ) :
    ∀ᵐ ω ∂P, ∃ x ∈ (S ×ˢ (Finset.univ : Finset (Fin t))).powerset, ω ∈ dyadicRankCell τ S t x := by
  let _ := h.probability
  let U : Set Ω := ⋃ x ∈ (S ×ˢ (Finset.univ : Finset (Fin t))).powerset, dyadicRankCell τ S t x
  have hm : MeasurableSet U := MeasurableSet.biUnion (Finset.countable_toSet _)
    (fun x _ => measurableSet_dyadicRankCell h.measurable S t x)
  have hp : P.real U = 1 := by
    rw [h.dyadicRankCells_real S t _ (Finset.Subset.rfl),fairFamilyMass_powerset]
  have hP : P U = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.one_ne_top).mp
    change P.real U = (1 : ℝ≥0∞).toReal
    simpa using hp
  have hz : P (Uᶜ) = 0 := by
    rw [measure_compl hm (measure_ne_top _ _),hP]
    simp
  have hh : ∀ᵐ ω ∂P, ω ∈ U := by
    rw [ae_iff]
    exact hz
  filter_upwards [hh] with ω hω
  obtain ⟨x,hx⟩ := Set.mem_iUnion.mp hω
  obtain ⟨hx,hcell⟩ := Set.mem_iUnion.mp hx
  exact ⟨x,hx,hcell⟩

omit [MeasurableSpace Ω] in
lemma dyadicRankCell_survival {S : Finset Edge} {t : ℕ} {x : Finset (Edge × Fin t)}
    {ω : Ω} (h : ω ∈ dyadicRankCell τ S t x) {e : Edge} (he : e ∈ S) :
    roundedSurvival t (τ e ω) = dyadicSurvival t x e := by
  rw [roundedSurvival,h e he,dyadicSurvival_eq_rank]

omit [MeasurableSpace Ω] in
lemma dyadicRankCell_path_iff {S : Finset Edge} {t : ℕ} {x : Finset (Edge × Fin t)}
    {ω : Ω} (h : ω ∈ dyadicRankCell τ S t x) (p : StrictPathWitness) (hp : p.edges ⊆ S) :
    RoundedPathGood t (fun e => τ e ω) p ↔ DyadicPathGood t x p := by
  have hs : ∀ e ∈ p.edges, roundedSurvival t (τ e ω) = dyadicSurvival t x e :=
    fun e he => dyadicRankCell_survival h (hp he)
  have hc := pathCost_eq_of_agree (fun e => roundedEdgeCost t (τ e ω))
    (fun e => -Real.log (dyadicSurvival t x e)) p.start p.steps
    (fun e he => congrArg (fun a => -Real.log a) (hs e he))
  unfold RoundedPathGood DyadicPathGood
  rw [hc]
  apply and_congr_left
  intro _
  exact forall_congr' (fun e => forall_congr' (fun he => by rw [hs e he]))

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BKLimit
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory Filter Set
open scoped ENNReal

theorem strict_disjoint_measure_le_of_rounded {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (τ : Edge → Ω → ℝ) (S : Finset Edge)
    (Fs : List (Set StrictPathWitness)) (C : ℝ≥0∞)
    (hbound : ∀ t, P {ω | RoundedDisjointPaths S Fs t (fun e => τ e ω)} ≤ C) :
    P {ω | StrictDisjointPaths S Fs (fun e => τ e ω)} ≤ C := by
  let E : ℕ → Set Ω := fun N => ⋂ t ≥ N, {ω | RoundedDisjointPaths S Fs t (fun e => τ e ω)}
  have he : {ω | StrictDisjointPaths S Fs (fun e => τ e ω)} = ⋃ N, E N := by
    ext ω
    simp only [mem_ofPred_eq,mem_iUnion,mem_iInter,E]
    rw [strict_disjoint_eventual_rounded_iff,eventually_atTop]
  have hmono : Monotone E := by
    intro N M hNM ω hω
    simp only [E,mem_iInter] at hω ⊢
    exact fun t ht => hω t (hNM.trans ht)
  have hE : ∀ N, P (E N) ≤ C := by
    intro N
    apply (measure_mono ?_).trans (hbound N)
    intro ω hω
    exact mem_iInter.mp (mem_iInter.mp hω N) le_rfl
  rw [he,hmono.measure_iUnion]
  exact iSup_le hE

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BKContinuous
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal

lemma dyadicPathFamily_subset (S : Finset Edge) (t : ℕ) (F : Set StrictPathWitness) :
    dyadicPathFamily S t F ⊆ (S ×ˢ Finset.univ).powerset := by
  intro x hx
  exact mem_powerset.mpr ((mem_dyadicPathFamily ..).mp hx).1

lemma dyadicDisjointPathFamily_subset (S : Finset Edge) (t : ℕ) (Fs : List (Set StrictPathWitness)) :
    dyadicDisjointPathFamily S t Fs ⊆ (S ×ˢ Finset.univ).powerset := by
  classical
  exact Finset.filter_subset _ _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

omit [MeasurableSpace Ω] in
lemma dyadic_single_cell_original {S : Finset Edge} {t : ℕ} {F : Set StrictPathWitness}
    {x : Finset (Edge × Fin t)} {ω : Ω}
    (hx : x ∈ dyadicPathFamily S t F) (hcell : ω ∈ dyadicRankCell τ S t x) :
    StrictPathEvent S F (fun e => τ e ω) := by
  obtain ⟨_,p,hp,he,hgood⟩ := (mem_dyadicPathFamily ..).mp hx
  exact ⟨p,hp,he,((dyadicRankCell_path_iff hcell p he).mpr hgood).original⟩

lemma ExponentialEnvironment.dyadic_single_mass_le (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (t : ℕ) (F : Set StrictPathWitness) :
    fairFamilyMass (S ×ˢ Finset.univ) (dyadicPathFamily S t F) ≤
      P.real {ω | StrictPathEvent S F (fun e => τ e ω)} := by
  let _ := h.probability
  rw [← h.dyadicRankCells_real S t _ (dyadicPathFamily_subset S t F)]
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  obtain ⟨x,hx⟩ := Set.mem_iUnion.mp hω
  obtain ⟨hx,hcell⟩ := Set.mem_iUnion.mp hx
  exact dyadic_single_cell_original hx hcell

omit [MeasurableSpace Ω] in
lemma rounded_disjoint_cell_mem {S : Finset Edge} {t : ℕ} {Fs : List (Set StrictPathWitness)}
    {x : Finset (Edge × Fin t)} {ω : Ω} (hx : x ⊆ S ×ˢ Finset.univ)
    (hcell : ω ∈ dyadicRankCell τ S t x)
    (hd : RoundedDisjointPaths S Fs t (fun e => τ e ω)) :
    x ∈ dyadicDisjointPathFamily S t Fs := by
  classical
  obtain ⟨ps,hps,hdis⟩ := hd
  apply Finset.mem_filter.mpr
  refine ⟨mem_powerset.mpr hx,ps,?_,hdis⟩
  exact hps.imp (fun p _ hp => ⟨hp.1,hp.2.1,(dyadicRankCell_path_iff hcell p hp.2.1).mp hp.2.2⟩)

lemma ExponentialEnvironment.rounded_disjoint_mass_le (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (t : ℕ) (Fs : List (Set StrictPathWitness)) :
    P.real {ω | RoundedDisjointPaths S Fs t (fun e => τ e ω)} ≤
      fairFamilyMass (S ×ˢ Finset.univ) (dyadicDisjointPathFamily S t Fs) := by
  let _ := h.probability
  rw [← h.dyadicRankCells_real S t _ (dyadicDisjointPathFamily_subset S t Fs)]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [h.ae_dyadicRankCell S t] with ω hω
  intro hd
  obtain ⟨x,hx,hcell⟩ := hω
  exact Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr
    ⟨rounded_disjoint_cell_mem (mem_powerset.mp hx) hcell hd,hcell⟩⟩

lemma strict_path_probabilities_nonneg (P : Measure Ω) (τ : Edge → Ω → ℝ)
    (S : Finset Edge) (Fs : List (Set StrictPathWitness)) :
    0 ≤ (Fs.map (fun F => P.real {ω | StrictPathEvent S F (fun e => τ e ω)})).prod := by
  induction Fs with
  | nil => simp
  | cons F Fs ih => exact mul_nonneg measureReal_nonneg ih

lemma ExponentialEnvironment.dyadic_factors_le (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (t : ℕ) (Fs : List (Set StrictPathWitness)) :
    (Fs.map (fun F => fairFamilyMass (S ×ˢ Finset.univ) (dyadicPathFamily S t F))).prod ≤
      (Fs.map (fun F => P.real {ω | StrictPathEvent S F (fun e => τ e ω)})).prod := by
  induction Fs with
  | nil => simp
  | cons F Fs ih =>
    simp only [List.map_cons,List.prod_cons]
    exact (mul_le_mul_of_nonneg_left ih (fairFamilyMass_nonneg _ _)).trans
      (mul_le_mul_of_nonneg_right (h.dyadic_single_mass_le S t F)
        (strict_path_probabilities_nonneg P τ S Fs))

theorem ExponentialEnvironment.rounded_strict_path_BK (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (t : ℕ) (Fs : List (Set StrictPathWitness)) :
    P.real {ω | RoundedDisjointPaths S Fs t (fun e => τ e ω)} ≤
      (Fs.map (fun F => P.real {ω | StrictPathEvent S F (fun e => τ e ω)})).prod :=
  (h.rounded_disjoint_mass_le S t Fs).trans
    ((dyadic_strict_path_BK S t Fs).trans (h.dyadic_factors_le S t Fs))

theorem exponential_strict_path_BK (h : ExponentialEnvironment P τ)
    (S : Finset Edge) (Fs : List (Set StrictPathWitness)) :
    P.real {ω | StrictDisjointPaths S Fs (fun e => τ e ω)} ≤
      (Fs.map (fun F => P.real {ω | StrictPathEvent S F (fun e => τ e ω)})).prod := by
  let _ := h.probability
  let C : ℝ := (Fs.map (fun F => P.real {ω | StrictPathEvent S F (fun e => τ e ω)})).prod
  have hC : 0 ≤ C := strict_path_probabilities_nonneg P τ S Fs
  have hh := strict_disjoint_measure_le_of_rounded P τ S Fs (ENNReal.ofReal C) (fun t => by
    calc
      P {ω | RoundedDisjointPaths S Fs t (fun e => τ e ω)} =
          ENNReal.ofReal (P.real {ω | RoundedDisjointPaths S Fs t (fun e => τ e ω)}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (h.rounded_strict_path_BK S t Fs))
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq (ENNReal.toReal_ofReal hC)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_CompanionModel
attribute [-instance] _root_.OAI.CompanionFPP.countable_lattice_walk _root_.OAI.CompanionFPP.encodable_lattice_walk _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set

lemma steps_companion_walk (w : Edge → ℝ) (p : Vertex) (ds : List Step) :
    ∃ walk : CompanionFPP.lattice.Walk p (p+displacement ds),
      CompanionFPP.pathCost (companionWeights w) walk = pathCost w p ds := by
  induction ds generalizing p with
  | nil =>
    refine ⟨(SimpleGraph.Walk.nil : CompanionFPP.lattice.Walk p p).copy rfl (by simp),?_⟩
    rw [companion_pathCost_copy]
    rfl
  | cons d ds ih =>
    obtain ⟨walk,hw⟩ := ih (p+d.delta)
    have he : (p+d.delta)+displacement ds = p+displacement (d::ds) := by
      simp [add_assoc]
    refine ⟨(SimpleGraph.Walk.cons (companion_adj_step p d) walk).copy rfl he,?_⟩
    simp only [companion_pathCost_copy, CompanionFPP.pathCost_cons, CompanionFPP.edgeCost, pathCost, hw]
    rw [← companionEdge_step,companionWeights_edge]

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
-- module Solutions.OAIS_PlanarFPP.FirstPassage_LocalDifferentiability
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter
open scoped Topology

theorem profile_hasDerivAt_of_equal_slopes (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ)
    (heq : leftSlope φ = rightSlope φ) : HasDerivAt φ (leftSlope φ) 0 := by
  obtain ⟨hl, hr⟩ := extreme_slopes_contact φ hφ
  rw [← heq] at hr
  apply hasDerivAt_iff_tendsto_slope_left_right.mpr
  exact ⟨(hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hl,
    (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hr⟩

theorem differentiableAt_of_transverse_profile
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : E → ℝ) (x r : E →L[ℝ] ℝ) (u e : E)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z)
    (hxu : x u = 1) (hru : r u = 0)
    (hcoords : ∀ z, z = x z • u + r z • e)
    (hprofile : DifferentiableAt ℝ (fun t : ℝ => μ (u + t • e)) 0) :
    DifferentiableAt ℝ μ u := by
  let φ : ℝ → ℝ := fun t => μ (u + t • e)
  have hinv : DifferentiableAt ℝ (fun z : E => (x z)⁻¹) u :=
    (hasDerivAt_inv (x := x u) (by rw [hxu]; norm_num)).differentiableAt.comp u x.differentiableAt
  have hquot : DifferentiableAt ℝ (fun z : E => r z / x z) u := by
    convert! r.differentiableAt.mul hinv using 1
  have hcomp : DifferentiableAt ℝ (fun z : E => φ (r z / x z)) u := by
    have hφat : DifferentiableAt ℝ φ (r u / x u) := by
      simpa only [hru, hxu, zero_div] using hprofile
    exact DifferentiableAt.comp (f := fun z : E => r z / x z) (g := φ) u hφat hquot
  have hprod : DifferentiableAt ℝ (fun z : E => x z * φ (r z / x z)) u :=
    x.differentiableAt.mul hcomp
  have hpos : ∀ᶠ z in 𝓝 u, 0 < x z :=
    x.continuous.continuousAt (lt_mem_nhds (show 0 < x u by rw [hxu]; norm_num))
  have heq : μ =ᶠ[𝓝 u] (fun z : E => x z * φ (r z / x z)) := by
    filter_upwards [hpos] with z hz
    have hrepr : z = x z • (u + (r z / x z) • e) := by
      rw [smul_add, smul_smul]
      have hc : x z * (r z / x z) = r z := by field_simp [ne_of_gt hz]
      rw [hc]
      exact hcoords z
    change μ z = x z * μ (u + (r z / x z) • e)
    conv_lhs => rw [hrepr]
    exact hhom _ (le_of_lt hz) _
  exact hprod.congr_of_eventuallyEq heq

theorem differentiableAt_of_equal_extreme_slopes
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : E → ℝ) (x r : E →L[ℝ] ℝ) (u e : E)
    (hadd : ∀ z w, μ (z + w) ≤ μ z + μ w)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z)
    (hxu : x u = 1) (hru : r u = 0)
    (hcoords : ∀ z, z = x z • u + r z • e)
    (heq : leftSlope (fun t : ℝ => μ (u + t • e)) =
      rightSlope (fun t : ℝ => μ (u + t • e))) :
    ∃ ℓ : E →L[ℝ] ℝ, HasFDerivAt μ ℓ u := by
  exact differentiableAt_of_transverse_profile μ x r u e hhom hxu hru hcoords
    (profile_hasDerivAt_of_equal_slopes _ (convex_transverse_profile μ u e hadd hhom)
      heq).differentiableAt

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

theorem planar_differentiability_of_no_corner (μ : Plane → ℝ)
    (hμ : TimeConstantNorm μ) (b : ℝ)
    (heq : leftSlope (fun t : ℝ => μ (direction b + t • transverseUnit)) =
      rightSlope (fun t : ℝ => μ (direction b + t • transverseUnit))) :
    ∃ ℓ : Plane →L[ℝ] ℝ, HasFDerivAt μ ℓ (direction b) := by
  exact differentiableAt_of_equal_extreme_slopes μ xCoord (rCoord b) (direction b)
    transverseUnit hμ.triangle (norm_positive_homogeneous μ hμ)
    (xCoord_direction b) (rCoord_direction b) (plane_reconstruction b) heq

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SourceTilt
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

theorem norm_direction_pos (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (b : ℝ) :
    0 < μ (direction b) := by
  have hn : direction b ≠ 0 := by
    intro hh
    have := congrArg xCoord hh
    norm_num [direction] at this
  exact lt_of_le_of_ne (hμ.nonneg _) (Ne.symm ((hμ.zero_iff _).not.mpr hn))

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

lemma mem_arbitraryEndpointEvent (b m₀ a A R ε : ℝ) (k m : ℕ) (w : Edge → ℝ) :
    w ∈ arbitraryEndpointEvent b m₀ a A R ε k m ↔
      ∃ p ds, PathIn p ds (endpointBox b A R k m) ∧ defect w b m₀ a p ds < -ε*(2 : ℝ)^k := by
  have hv : (endpointBoxVertices b A R k m : Set Vertex)=endpointBox b A R k m :=
    (endpointBox_finite b A R k m).coe_toFinset
  simp only [arbitraryEndpointEvent,strictLocalizedEvent,mem_ofPred_eq,true_and,hv,defect]
  constructor <;> rintro ⟨p,ds,hin,hc⟩ <;> exact ⟨p,ds,hin,by linarith⟩

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

lemma mem_translatedArbitraryEndpointEvent (b m₀ a A R ε : ℝ) (k m : ℕ) (t : Vertex) (w : Edge → ℝ) :
    w ∈ translatedArbitraryEndpointEvent b m₀ a A R ε k m t ↔
      ∃ p ds, PathIn p ds {z | z-t ∈ endpointBox b A R k m} ∧ defect w b m₀ a p ds < -ε*(2 : ℝ)^k := by
  change (fun e => w (shiftEdge t e)) ∈ arbitraryEndpointEvent b m₀ a A R ε k m ↔ _
  rw [mem_arbitraryEndpointEvent]
  have hc (p ds) : defect (fun e => w (shiftEdge t e)) b m₀ a p ds=defect w b m₀ a (t+p) ds := by
    simp only [defect,pathCost_translate]
  constructor
  · rintro ⟨p,ds,hin,hcost⟩
    refine ⟨t+p,ds,?_,by rwa [← hc]⟩
    intro i hi
    have he : t+p+displacement (ds.take i)-t=p+displacement (ds.take i) := by abel
    simpa only [mem_ofPred_eq,he] using hin i hi
  · rintro ⟨p,ds,hin,hcost⟩
    refine ⟨p-t,ds,?_,?_⟩
    · intro i hi
      have he : p-t+displacement (ds.take i)=p+displacement (ds.take i)-t := by abel
      simpa only [mem_ofPred_eq,he] using hin i hi
    · rw [hc,add_sub_cancel]
      exact hcost

lemma mem_eitherEndpointEvent (b m₀ am ap A R ε : ℝ) (k m : ℕ) (t : Vertex) (w : Edge → ℝ) :
    w ∈ eitherEndpointEvent b m₀ am ap A R ε k m t ↔
      ∃ p ds, PathIn p ds {z | z-t ∈ endpointBox b A R k m} ∧
        (defect w b m₀ am p ds < -ε*(2 : ℝ)^k ∨ defect w b m₀ ap p ds < -ε*(2 : ℝ)^k) := by
  simp only [eitherEndpointEvent,mem_union,mem_translatedArbitraryEndpointEvent]
  constructor
  · rintro (⟨p,ds,hin,hc⟩ | ⟨p,ds,hin,hc⟩)
    · exact ⟨p,ds,hin,Or.inl hc⟩
    · exact ⟨p,ds,hin,Or.inr hc⟩
  · rintro ⟨p,ds,hin,hc | hc⟩
    · exact Or.inl ⟨p,ds,hin,hc⟩
    · exact Or.inr ⟨p,ds,hin,hc⟩

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SpatialWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

lemma spatialWitness_good_event (b m₀ am ap K η : ℝ) (k m : ℕ) (ih : ℤ×ℤ)
    (p : StrictPathWitness) (hp : p ∈ spatialWitnessFamily b m₀ am ap K η k m ih)
    (w : Edge → ℝ) (hw : p.Good w) : w ∈ spatialRareEvent b m₀ am ap K η k m ih := by
  rcases hp with ⟨hin,hbound | hbound⟩ | ⟨hstart,hend,hin,hbound⟩
  · apply Or.inl
    apply (mem_eitherEndpointEvent ..).mpr
    refine ⟨p.start,p.steps,hin,Or.inl ?_⟩
    change pathCost w p.start p.steps < p.bound at hw
    unfold defect
    rw [hbound] at hw
    linarith
  · apply Or.inl
    apply (mem_eitherEndpointEvent ..).mpr
    refine ⟨p.start,p.steps,hin,Or.inr ?_⟩
    change pathCost w p.start p.steps < p.bound at hw
    unfold defect
    rw [hbound] at hw
    linarith
  · apply Or.inr
    refine ⟨p.start,p.steps,⟨hstart,hend⟩,?_,?_⟩
    · intro i hi
      exact (mem_rareFastVertices ..).mpr (hin i hi)
    · simpa only [StrictPathWitness.Good,Int.cast_pow,Int.cast_ofNat,hbound] using hw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem exponential_spatial_witness_BK (henv : ExponentialEnvironment P τ)
    (b m₀ am ap K η p₀ : ℝ) (hp₀ : 0 ≤ p₀) (k m : ℕ)
    (hrare : ∀ ih : ℤ×ℤ, P.real {ω | (fun e => τ e ω) ∈ spatialRareEvent b m₀ am ap K η k m ih} ≤ p₀)
    (is : List (ℤ×ℤ)) :
    P.real {ω | StrictDisjointPaths (spatialListSupport b k m is)
      (is.map (spatialWitnessFamily b m₀ am ap K η k m)) (fun e => τ e ω)} ≤ p₀^is.length := by
  let _ := henv.probability
  let S := spatialListSupport b k m is
  have hsingle (ih : ℤ×ℤ) : P.real {ω | StrictPathEvent S (spatialWitnessFamily b m₀ am ap K η k m ih)
      (fun e => τ e ω)} ≤ p₀ := by
    apply (measureReal_mono ?_).trans (hrare ih)
    rintro ω ⟨p,hp,_he,hg⟩
    exact spatialWitness_good_event b m₀ am ap K η k m ih p hp _ hg
  apply (exponential_strict_path_BK henv S (is.map (spatialWitnessFamily b m₀ am ap K η k m))).trans
  simp only [List.map_map]
  have hprod (js : List (ℤ×ℤ)) :
      (js.map (fun ih => P.real {ω | StrictPathEvent S (spatialWitnessFamily b m₀ am ap K η k m ih)
        (fun e => τ e ω)})).prod ≤ p₀^js.length := by
    induction js with
    | nil => simp
    | cons i js ih =>
      simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ]
      calc
        _ ≤ p₀*(js.map (fun ih => P.real {ω | StrictPathEvent S (spatialWitnessFamily b m₀ am ap K η k m ih)
          (fun e => τ e ω)})).prod := mul_le_mul_of_nonneg_right (hsingle i) (List.prod_nonneg (by intro a ha; obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha; exact measureReal_nonneg))
        _ ≤ p₀*p₀^js.length := mul_le_mul_of_nonneg_left ih hp₀
        _ = _ := by ring
  exact hprod is

theorem actual_spatial_witness_BK_scales (henv : ExponentialEnvironment P τ)
    (b q₀ η : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) (hη : 0 < η)
    (N : ℕ) (S D : ℝ) :
    ∃ k : ℕ, N < k ∧ S ≤ (2 : ℝ)^k ∧
      D*(2 : ℝ)^k ≤ (characteristicLength P τ actualSourceTimeConstant b q₀ k : ℝ) ∧
      ∀ is : List (ℤ×ℤ), P.real {ω | StrictDisjointPaths
        (spatialListSupport b k (characteristicExponent P τ actualSourceTimeConstant b q₀ k) is)
        (is.map (spatialWitnessFamily b (actualSourceTimeConstant (direction b))
          (extremeSlope actualSourceTimeConstant b false) (extremeSlope actualSourceTimeConstant b true)
          (sourceCrossingK actualSourceTimeConstant b) η k
          (characteristicExponent P τ actualSourceTimeConstant b q₀ k))) (fun e => τ e ω)} ≤
        (2*q₀)^is.length := by
  obtain ⟨k,hk,hs,hd,hrare⟩ := actual_spatial_rare_scales henv b q₀ η hb hq hq1 hη N S D
  refine ⟨k,hk,hs,hd,?_⟩
  intro is
  exact exponential_spatial_witness_BK henv b _ _ _ _ η (2*q₀) (by positivity) k
    (characteristicExponent P τ actualSourceTimeConstant b q₀ k) hrare is

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SpatialFirstExit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

lemma chunkInterior_zero (b : ℝ) (k m : ℕ) : chunkInterior b k m 0 := by
  constructor
  · change (0 : ℤ) < 2*(2 : ℤ)^m
    positivity
  · simp [transverse]

theorem first_full_spatial_chunk (b : ℝ) (k m : ℕ) (ds : List Step) :
    (∀ i ≤ ds.length, chunkInterior b k m (displacement (ds.take i))) ∨
    ∃ pre rest : List Step, ds=pre++rest ∧ pre ≠ [] ∧ FullSpatialChunk b k m pre := by
  classical
  by_cases h : ∃ i : ℕ, i ≤ ds.length ∧ ¬chunkInterior b k m (displacement (ds.take i))
  · let n := Nat.find h
    have hn := Nat.find_spec h
    have hn0 : 0 < n := by
      by_contra hh
      have he : n=0 := by omega
      have hn' : ¬chunkInterior b k m (displacement (ds.take n)) := hn.2
      simp only [he,List.take_zero,displacement_nil] at hn'
      exact hn' (chunkInterior_zero b k m)
    have hlen : (ds.take n).length=n := List.length_take_of_le hn.1
    refine Or.inr ⟨ds.take n,ds.drop n,(List.take_append_drop n ds).symm,?_,?_,?_⟩
    · intro he
      rw [he] at hlen
      simp only [List.length_nil] at hlen
      omega
    · intro i hi
      rw [hlen] at hi
      have hnot := Nat.find_min h hi
      have hip : i ≤ ds.length := by omega
      have hv : chunkInterior b k m (displacement (ds.take i)) := by tauto
      simpa only [List.take_take,Nat.min_eq_left hi.le] using hv
    · exact hn.2
  · exact Or.inl (fun i hi => by by_contra hn; exact h ⟨i,hi,hn⟩)

lemma step_transverse_abs_le (b : ℝ) (hb : |b| ≤ 1) (d : Step) : |transverse b d.delta| ≤ 1 := by
  cases d with
  | east => simpa [Step.delta,transverse] using hb
  | west => simpa [Step.delta,transverse] using hb
  | north => norm_num [Step.delta,transverse]
  | south => norm_num [Step.delta,transverse]

lemma chunk_step_localization (b : ℝ) (hb : |b| ≤ 1) (k m : ℕ) (v : Vertex)
    (hv : chunkInterior b k m v) (d : Step) :
    |(v+d.delta).1| ≤ 2*(2 : ℤ)^m ∧ |transverse b (v+d.delta)| ≤ (2 : ℝ)^k+1 := by
  have hx := abs_lt.mp hv.1
  constructor
  · cases d <;> simp only [Step.delta,Prod.fst_add] <;> apply abs_le.mpr <;> omega
  · rw [transverse_add]
    exact (abs_add_le _ _).trans (by linarith [hv.2,step_transverse_abs_le b hb d])

lemma proper_chunk_endpoint_localization (b : ℝ) (hb : |b| ≤ 1) (k m : ℕ) (ds : List Step)
    (hproper : ∀ i < ds.length, chunkInterior b k m (displacement (ds.take i))) :
    |(displacement ds).1| ≤ 2*(2 : ℤ)^m ∧ |transverse b (displacement ds)| ≤ (2 : ℝ)^k+1 := by
  induction ds using List.reverseRecOn with
  | nil =>
    constructor
    · change (0 : ℤ) ≤ 2*(2 : ℤ)^m
      positivity
    · simpa [transverse] using (show (0 : ℝ) ≤ (2 : ℝ)^k+1 by positivity)
  | append_singleton ds d _ih =>
    have h := hproper ds.length (by simp)
    have ht : (ds++[d]).take ds.length=ds := by simp
    rw [ht] at h
    simpa [displacement_append,displacement] using chunk_step_localization b hb k m (displacement ds) h d

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SpatialChunks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

theorem spatial_chunk_decomposition (b : ℝ) (k m : ℕ) (ds : List Step) :
    ∃ blocks : List (List Step), ∃ rest : List Step,
      ds=blocks.flatten++rest ∧ (∀ q ∈ blocks, FullSpatialChunk b k m q) ∧
      (∀ i ≤ rest.length, chunkInterior b k m (displacement (rest.take i))) := by
  induction hn : ds.length using Nat.strong_induction_on generalizing ds with
  | h n ih =>
    rcases first_full_spatial_chunk b k m ds with hrest | ⟨pre,rest,heq,hpre,hfull⟩
    · exact ⟨[],ds,by simp,by simp,hrest⟩
    · have hlen : rest.length < n := by
        rw [heq,List.length_append] at hn
        have hp := List.length_pos_iff.mpr hpre
        omega
      obtain ⟨bs,tail,hbs,hbf,hbt⟩ := ih rest.length hlen rest rfl
      refine ⟨pre::bs,tail,?_,?_,hbt⟩
      · simp [heq,hbs,List.append_assoc]
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hfull
        · exact hbf q hq

lemma spatial_chunk_displacement_bound (b : ℝ) (hb : |b| ≤ 1) (k m : ℕ)
    (blocks : List (List Step)) (rest : List Step)
    (hfull : ∀ q ∈ blocks, FullSpatialChunk b k m q)
    (hrest : ∀ i ≤ rest.length, chunkInterior b k m (displacement (rest.take i))) :
    |(displacement (blocks.flatten++rest)).1| ≤ 2*(2 : ℤ)^m*((blocks.length : ℤ)+1) := by
  induction blocks with
  | nil =>
    have hh := (hrest rest.length le_rfl).1.le
    simpa using hh
  | cons q qs ih =>
    have hq := proper_chunk_endpoint_localization b hb k m q (hfull q (by simp)).1
    have htail := ih (fun v hv => hfull v (by simp [hv]))
    simp only [List.flatten_cons,List.append_assoc,displacement_append,Prod.fst_add,List.length_cons,Nat.cast_add,Nat.cast_one]
    have ht := abs_add_le (displacement q).1 (displacement (qs.flatten++rest)).1
    simp only [displacement_append,Prod.fst_add] at ht htail
    nlinarith [hq.1]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ActualWitnessScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory Filter

lemma witness_scale_inequalities (b m₀ am ap η s L : ℝ) (hm : 0 < m₀)
    (hη : 0 < η) (hη1 : η ≤ 1) (hs : 2 ≤ s)
    (hS : max |m₀-((am+ap)/2)*b| |(am+ap)/2| / η ≤ s)
    (hD : ((η+2*|(am+ap)/2|+1)/m₀)*s ≤ L) :
    max |m₀-((am+ap)/2)*b| |(am+ap)/2| ≤ η*s ∧
    η*s < 2*m₀*L-|(am+ap)/2| *(s+1) ∧
    3*η*s+2*|(am+ap)/2| *(s+1) < 100*(1+|am|+|ap|)*s := by
  have hstep := (div_le_iff₀ hη).mp hS
  have hD' := mul_le_mul_of_nonneg_left hD hm.le
  have he : m₀*((η+2*|(am+ap)/2|+1)/m₀*s)=(η+2*|(am+ap)/2|+1)*s := by field_simp
  rw [he] at hD'
  have hA : 2*|(am+ap)/2| ≤ |am|+|ap| := by
    rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]
    linarith [abs_add_le am ap]
  have hAs := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ s+1)
  have hηs := mul_le_mul_of_nonneg_right hη1 (by linarith : 0 ≤ s)
  have haS := mul_nonneg (abs_nonneg am) (by linarith : 0 ≤ s-1)
  have hapS := mul_nonneg (abs_nonneg ap) (by linarith : 0 ≤ s-1)
  have hmidS := mul_nonneg (abs_nonneg ((am+ap)/2)) (by linarith : 0 ≤ s-1)
  refine ⟨by nlinarith,?_,?_⟩ <;> nlinarith [abs_nonneg am,abs_nonneg ap,abs_nonneg ((am+ap)/2),mul_pos hη (by linarith : 0<s)]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem actual_witness_scale (henv : ExponentialEnvironment P τ) (b η : ℝ)
    (hb : |b| ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ k m : ℕ, 2 ≤ (2 : ℝ)^k ∧
      max |actualSourceTimeConstant (direction b)-
        ((extremeSlope actualSourceTimeConstant b false+extremeSlope actualSourceTimeConstant b true)/2)*b|
        |(extremeSlope actualSourceTimeConstant b false+extremeSlope actualSourceTimeConstant b true)/2| ≤ η*(2 : ℝ)^k ∧
      η*(2 : ℝ)^k < 2*actualSourceTimeConstant (direction b)*(2 : ℝ)^m-
        |(extremeSlope actualSourceTimeConstant b false+extremeSlope actualSourceTimeConstant b true)/2| *((2 : ℝ)^k+1) ∧
      3*η*(2 : ℝ)^k+2*|(extremeSlope actualSourceTimeConstant b false+extremeSlope actualSourceTimeConstant b true)/2| *((2 : ℝ)^k+1)
        < sourceCrossingK actualSourceTimeConstant b*(2 : ℝ)^k ∧
      ∀ is : List (ℤ×ℤ), P.real {ω | StrictDisjointPaths (spatialListSupport b k m is)
        (is.map (spatialWitnessFamily b (actualSourceTimeConstant (direction b))
          (extremeSlope actualSourceTimeConstant b false) (extremeSlope actualSourceTimeConstant b true)
          (sourceCrossingK actualSourceTimeConstant b) η k m)) (fun e => τ e ω)} ≤
        (((1 : ℝ)/1024)^16)^is.length := by
  let μ := actualSourceTimeConstant
  let am := extremeSlope μ b false
  let ap := extremeSlope μ b true
  let a := (am+ap)/2
  let m₀ := μ (direction b)
  let q₀ : ℝ := ((1/1024)^16)/2
  have hq : 0 < q₀ := by dsimp [q₀]; positivity
  have hq1 : q₀ < 1 := by dsimp [q₀]; norm_num
  let S := max 2 (max |m₀-a*b| |a| / η)
  let D := (η+2*|a|+1)/m₀
  obtain ⟨k,hk,hs,hd,hBK⟩ := actual_spatial_witness_BK_scales henv b q₀ η hb hq hq1 hη 0 S D
  let m := characteristicExponent P τ μ b q₀ k
  have hpow : (characteristicLength P τ μ b q₀ k : ℝ)=(2 : ℝ)^m := by
    simp [characteristicLength,m]
  rw [hpow] at hd
  have hs2 : 2 ≤ (2 : ℝ)^k := (le_max_left _ _).trans hs
  have hsC : max |m₀-a*b| |a| / η ≤ (2 : ℝ)^k := (le_max_right _ _).trans hs
  obtain ⟨hstep,hscale₁,hscale₂⟩ := witness_scale_inequalities b m₀ am ap η ((2 : ℝ)^k) ((2 : ℝ)^m)
    (norm_direction_pos μ actualSourceTimeConstant_norm b) hη hη1 hs2 hsC hd
  refine ⟨k,m,hs2,hstep,hscale₁,hscale₂,?_⟩
  intro is
  have hh := hBK is
  have he : 2*q₀=((1 : ℝ)/1024)^16 := by dsimp [q₀]; ring
  rw [he] at hh
  exact hh

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SimplePathApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

lemma companion_walk_steps_edges (w : Edge → ℝ) {p q : Vertex}
    (walk : CompanionFPP.lattice.Walk p q) :
    ∃ ds : List Step, p+displacement ds=q ∧
      pathCost w p ds=CompanionFPP.pathCost (companionWeights w) walk ∧
      ((trace p ds).map (fun t => (companionEdge (traversalEdge t)).val))=walk.edges := by
  induction walk with
  | nil => exact ⟨[],by simp,rfl,rfl⟩
  | @cons p u q hadj walk ih =>
    obtain ⟨d,rfl⟩ := (companion_adj_iff p u).mp hadj
    obtain ⟨ds,he,hc,hedges⟩ := ih
    refine ⟨d::ds,by simpa [add_assoc] using he,?_,?_⟩
    · simp only [pathCost,CompanionFPP.pathCost_cons,CompanionFPP.edgeCost,hc]
      rw [← companionEdge_step,companionWeights_edge]
    · simp only [trace,List.map_cons,traversalEdge,companionEdge_step,SimpleGraph.Walk.edges_cons]
      simpa only [traversalEdge,companionEdge_step] using congrArg (List.cons s(p,p+d.delta)) hedges

theorem erase_path_loops (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e) (p : Vertex) (ds : List Step) :
    ∃ es : List Step, displacement es=displacement ds ∧
      ((trace p es).map traversalEdge).Nodup ∧ pathCost w p es ≤ pathCost w p ds := by
  obtain ⟨walk,hcost⟩ := steps_companion_walk w p ds
  obtain ⟨es,hend,hc,he⟩ := companion_walk_steps_edges w walk.bypass
  have hn := walk.bypass_isPath.isTrail.edges_nodup
  rw [← he] at hn
  have hn' : (((trace p es).map traversalEdge).map (fun e => (companionEdge e).val)).Nodup := by
    simpa only [List.map_map,Function.comp_def] using hn
  refine ⟨es,add_left_cancel hend,List.Nodup.of_map _ hn',?_⟩
  rw [hc,← hcost]
  exact CompanionFPP.bypass_cost_le (companionWeights w) (fun e => hw _) walk

theorem exists_near_optimal_simple_path (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p q : Vertex) (ε : ℝ) (hε : 0 < ε) :
    ∃ ds : List Step, p+displacement ds=q ∧
      ((trace p ds).map traversalEdge).Nodup ∧
      passageTime w p q ≤ pathCost w p ds ∧ pathCost w p ds < passageTime w p q+ε := by
  obtain ⟨ds,hend,hcost⟩ := exists_near_optimal_path w p q ε hε
  obtain ⟨es,he,hs,hc⟩ := erase_path_loops w hw p ds
  have he' : p+displacement es=q := by rw [he,hend]
  exact ⟨es,he',hs,passageTime_le_cost w hw p q es he',hc.trans_lt hcost⟩

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_NoCornerContradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology

theorem long_paths_contradict_directional_limit (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b m₀ a η : ℝ) (hb : |b| ≤ 1) (hη : 0 < η) (k m : ℕ)
    (hlim : Tendsto (fun n : ℕ => passageTime w 0 ((n : ℤ),⌊b*(n : ℝ)⌋)/(n : ℝ)) atTop (𝓝 m₀))
    (hlong : ∀ᶠ N : ℕ in atTop, ∀ blocks : List (List Step), ∀ rest : List Step,
      blocks.length=N → (∀ q ∈ blocks, FullSpatialChunk b k m q) →
      (∀ i ≤ rest.length, chunkInterior b k m (displacement (rest.take i))) →
      ((trace 0 (blocks.flatten++rest)).map traversalEdge).Nodup →
      N*η*(2 : ℝ)^k/2 ≤ defect w b m₀ a 0 (blocks.flatten++rest)) : False := by
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hlong
  let A := η*(2 : ℝ)^k
  let L := (2 : ℝ)^m
  let δ := A/(8*L)
  have hA : 0 < A := by dsimp [A]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : 8*L*δ=A := by dsimp [δ]; field_simp
  have hup := hlim.eventually (gt_mem_nhds (show m₀ < m₀+δ by linarith))
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hnlarge := hnat.eventually (eventually_gt_atTop (((N₀ : ℝ)+1)*2*L))
  have hnC := hnat.eventually (eventually_gt_atTop ((A/2+|a|+1)/δ))
  have hnpos := hnat.eventually (eventually_gt_atTop (0 : ℝ))
  obtain ⟨n,hnup,hnlarge,hnC,hnpos⟩ := (hup.and (hnlarge.and (hnC.and hnpos))).exists
  obtain ⟨ds,hend,hsimple,_hmin,hcost⟩ := exists_near_optimal_simple_path w hw 0 ((n : ℤ),⌊b*(n : ℝ)⌋) 1 (by norm_num)
  have hdisp : displacement ds=((n : ℤ),⌊b*(n : ℝ)⌋) := by simpa using hend
  obtain ⟨blocks,rest,heq,hfull,hrest⟩ := spatial_chunk_decomposition b k m ds
  have hcut := spatial_chunk_displacement_bound b hb k m blocks rest hfull hrest
  rw [← heq,hdisp] at hcut
  have hcutR : (n : ℝ) ≤ 2*L*((blocks.length : ℝ)+1) := by
    have hh : (n : ℤ) ≤ 2*(2 : ℤ)^m*((blocks.length : ℤ)+1) := by simpa using hcut
    dsimp [L]
    exact_mod_cast hh
  have hN : N₀ ≤ blocks.length := by
    by_contra hh
    have hl : ((blocks.length : ℝ)+1) ≤ N₀ := by exact_mod_cast (show blocks.length+1 ≤ N₀ by omega)
    have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*L by positivity)
    nlinarith
  have hlow := hN₀ blocks.length hN blocks rest rfl hfull hrest (by rw [← heq]; exact hsimple)
  have hloA : (blocks.length : ℝ)*A/2 ≤ defect w b m₀ a 0 ds := by
    rw [← heq] at hlow
    simpa only [A,mul_assoc] using hlow
  have hr : |(⌊b*(n : ℝ)⌋ : ℝ)-b*n| ≤ 1 := by
    apply abs_le.mpr
    have hl := Int.floor_le (b*(n : ℝ))
    have hu := Int.lt_floor_add_one (b*(n : ℝ))
    constructor <;> linarith
  have hab : |a*((⌊b*(n : ℝ)⌋ : ℝ)-b*n)| ≤ |a| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left hr (abs_nonneg a)
  have hsupport : m₀*n-|a| ≤ support b m₀ a (displacement ds) := by
    rw [hdisp]
    simp only [support,transverse,Int.cast_natCast]
    linarith [(abs_le.mp hab).1]
  have hpass : passageTime w 0 ((n : ℤ),⌊b*(n : ℝ)⌋) < (m₀+δ)*n := (div_lt_iff₀ hnpos).mp hnup
  have hupper : defect w b m₀ a 0 ds < δ*n+|a|+1 := by
    unfold defect
    nlinarith
  have hcutδ := mul_le_mul_of_nonneg_left hcutR hδ.le
  have hδN := congrArg (fun x : ℝ => x*((blocks.length : ℝ)+1)) hδeq
  have hC : A/2+|a|+1 < δ*n := by
    have hh := (div_lt_iff₀ hδ).mp hnC
    nlinarith
  nlinarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ActualNoCorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

lemma actual_direction_nat_limit (henv : ExponentialEnvironment P τ) (b : ℝ) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => passageTime (fun e => τ e ω) 0 ((n : ℤ),⌊b*(n : ℝ)⌋)/(n : ℝ))
      atTop (𝓝 (actualSourceTimeConstant (direction b))) := by
  filter_upwards [actualSourceTimeConstant_isTimeConstant henv (direction b)] with ω hω
  have hh := hω.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have he (n : ℕ) : latticeFloor ((n : ℝ) • direction b)=((n : ℤ),⌊b*(n : ℝ)⌋) := by
    simp [latticeFloor,direction,PiLp.smul_apply,mul_comm]
  simpa only [Function.comp_def,he,show (0 : Vertex)=(0,0) from rfl] using hh

theorem actual_no_corner (henv : ExponentialEnvironment P τ) (b : ℝ) (hb : |b| ≤ 1) :
    extremeSlope actualSourceTimeConstant b false=extremeSlope actualSourceTimeConstant b true := by
  let _ := henv.probability
  let μ := actualSourceTimeConstant
  let am := extremeSlope μ b false
  let ap := extremeSlope μ b true
  have horder : am ≤ ap := by
    exact extreme_slopes_ordered _ (convex_transverse_profile μ (direction b) transverseUnit
      actualSourceTimeConstant_norm.triangle (norm_positive_homogeneous μ actualSourceTimeConstant_norm))
  change am=ap
  by_contra hneq
  have hgap0 : 0 < (ap-am)/8 := by have hh := lt_of_le_of_ne horder hneq; linarith
  let η := min 1 ((ap-am)/8)
  have hη : 0 < η := lt_min (by norm_num) hgap0
  have hη1 : η ≤ 1 := min_le_left ..
  have hgap : 4*η ≤ (ap-am)/2 := by have hh := min_le_right (1 : ℝ) ((ap-am)/8); nlinarith
  obtain ⟨k,m,hs,hstep,hscale₁,hscale₂,hBK⟩ := actual_witness_scale henv b η hb hη hη1
  have hlong := ae_eventually_spatial_long_paths henv b (μ (direction b)) am ap (sourceCrossingK μ b) η
    ((1 : ℝ)/1024) hb horder hη (by norm_num) (by norm_num) (by norm_num)
    hgap k m hs hstep hscale₁ hscale₂ hBK
  obtain ⟨ω,hp,hl,hh⟩ := (henv.ae_positive.and ((actual_direction_nat_limit henv b).and hlong)).exists
  exact long_paths_contradict_directional_limit (fun e => τ e ω) (fun e => (hp e).le)
    b (μ (direction b)) ((am+ap)/2) η hb hη k m hl hh

theorem actual_direction_differentiable (henv : ExponentialEnvironment P τ) (b : ℝ) (hb : |b| ≤ 1) :
    DifferentiableAt ℝ actualSourceTimeConstant (direction b) := by
  obtain ⟨ℓ,hℓ⟩ := planar_differentiability_of_no_corner actualSourceTimeConstant actualSourceTimeConstant_norm b
    (actual_no_corner henv b hb)
  exact hℓ.differentiableAt

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GlobalDifferentiability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory

lemma norm_differentiable_smul (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (u : Plane) (t : ℝ) (ht : t ≠ 0) (hu : DifferentiableAt ℝ μ u) :
    DifferentiableAt ℝ μ (t • u) := by
  have hi : DifferentiableAt ℝ μ (t⁻¹ • (t • u)) := by simpa [smul_smul,ht] using hu
  have hc := hi.comp (t • u) (differentiableAt_id.const_smul t⁻¹)
  have hd := hc.const_mul |t|
  have he : (fun z : Plane => |t| *μ (t⁻¹ • z))=μ := by
    funext z
    rw [hμ.homogeneous,abs_inv,← mul_assoc,mul_inv_cancel₀ (abs_ne_zero.mpr ht),one_mul]
  simpa only [Function.comp_def,he] using hd

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

lemma actual_differentiable_horizontal_oai (henv : ExponentialEnvironment P τ)
    (v : Plane) (hv : v ≠ 0) (hdom : |v 1| ≤ |v 0|) :
    DifferentiableAt ℝ actualSourceTimeConstant v := by
  have hx : v 0 ≠ 0 := by
    intro hx
    have hy : v 1=0 := by simpa [hx] using hdom
    apply hv
    ext i
    fin_cases i <;> simp [hx,hy]
  have hb : |v 1/v 0| ≤ 1 := by rw [abs_div]; exact (div_le_one (abs_pos.mpr hx)).mpr hdom
  have he : v 0 • direction (v 1/v 0)=v := by
    ext i
    fin_cases i <;> simp [direction,PiLp.smul_apply]
    field_simp
  rw [← he]
  exact norm_differentiable_smul _ actualSourceTimeConstant_norm _ _ hx
    (actual_direction_differentiable henv _ hb)

end PlanarFPP

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PlanarFPP.actual_differentiable_horizontal_oai.{u_1} := @OAI.PlanarFPP.actual_differentiable_horizontal_oai.{u_1}
