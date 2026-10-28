-- Prove2me | solution 1 for OAI.PlanarFPP.manuscriptMain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:48:02.502371+00:00
-- url     : https://prove2.me/submissions/01d454d9-34f3-473c-8ea5-2df0ca7994e3

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFirstPassage
import Definitions.Def_OAISPf002
import Theorems.Thm_OAI_PlanarFPP_actualSourceTimeConstant_lattice_limits
import Theorems.Thm_OAI_PlanarFPP_actual_differentiable_horizontal

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
-- module Solutions.OAIS_PlanarFPP.FirstPassage_TimeConstantObligation
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory Filter
open scoped Topology

theorem isTimeConstant_unique {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {τ : Edge → Ω → ℝ} (h : ExponentialEnvironment P τ)
    {μ ν : Plane → ℝ} (hμ : IsTimeConstant P τ μ) (hν : IsTimeConstant P τ ν) : μ=ν := by
  let _ := h.probability
  funext v
  obtain ⟨ω,hω⟩ := ((hμ v).and (hν v)).exists
  exact tendsto_nhds_unique hω.1 hω.2

end PlanarFPP

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

theorem actualSourceTimeConstant_unique (h : ExponentialEnvironment P τ)
    {μ : Plane → ℝ} (hμ : IsTimeConstant P τ μ) : μ=actualSourceTimeConstant :=
  isTimeConstant_unique h hμ (actualSourceTimeConstant_isTimeConstant h)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_Localization
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
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

theorem norm_positive_homogeneous (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z := by
  intro t ht z
  rw [hμ.homogeneous, abs_of_nonneg ht]

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
-- module Solutions.OAIS_PlanarFPP.FirstPassage_LatticeSwap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

lemma swapEdge_injective : Function.Injective swapEdge := Function.LeftInverse.injective swapEdge_swap

lemma swapStep_edge (p : Vertex) (d : Step) : (swapStep d).edge p.swap=swapEdge (d.edge p) := by
  cases d <;> rfl

lemma displacement_swap (ds : List Step) : displacement (ds.map swapStep)=(displacement ds).swap := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [ih,Prod.swap_add]

lemma pathCost_swap (w : Edge → ℝ) (p : Vertex) (ds : List Step) :
    pathCost w p.swap (ds.map swapStep)=pathCost (fun e => w (swapEdge e)) p ds := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp [pathCost,swapStep_edge,← Prod.swap_add,ih]

lemma passageTime_swap (w : Edge → ℝ) (p q : Vertex) :
    passageTime w p.swap q.swap=passageTime (fun e => w (swapEdge e)) p q := by
  unfold passageTime
  congr 1
  ext t
  constructor
  · rintro ⟨ds,hend,hc⟩
    refine ⟨ds.map swapStep,?_,?_⟩
    · rw [displacement_swap]
      have hh := congrArg Prod.swap hend
      simpa only [Prod.swap_add,Prod.swap_swap] using hh
    · have hh := pathCost_swap (fun e => w (swapEdge e)) p.swap ds
      simpa only [Prod.swap_swap,swapEdge_swap,hc] using hh
  · rintro ⟨ds,hend,hc⟩
    exact ⟨ds.map swapStep,by rw [displacement_swap,← Prod.swap_add,hend],by rw [pathCost_swap,hc]⟩

lemma latticeFloor_swap (v : Plane) : latticeFloor (swapPlane v)=(latticeFloor v).swap := by
  simp [latticeFloor]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

lemma ExponentialEnvironment.swap (henv : ExponentialEnvironment P τ) :
    ExponentialEnvironment P (fun e => τ (swapEdge e)) where
  probability := henv.probability
  measurable _e := henv.measurable _
  independent := henv.independent.precomp swapEdge_injective
  marginal _e := henv.marginal _

theorem actualSourceTimeConstant_swap (henv : ExponentialEnvironment P τ) (v : Plane) :
    actualSourceTimeConstant (swapPlane v)=actualSourceTimeConstant v := by
  have ht : IsTimeConstant P (fun e => τ (swapEdge e)) (fun z => actualSourceTimeConstant (swapPlane z)) := by
    intro z
    filter_upwards [actualSourceTimeConstant_isTimeConstant henv (swapPlane z)] with ω hω
    have he (t : ℝ) : passageTime (fun e => τ (swapEdge e) ω) 0 (latticeFloor (t • z)) =
        passageTime (fun e => τ e ω) 0 (latticeFloor (t • swapPlane z)) := by
      rw [← passageTime_swap (fun e => τ e ω) (0 : Vertex) (latticeFloor (t • z)),← latticeFloor_swap,map_smul]
      rfl
    simpa only [show ((0,0) : Vertex)=0 from rfl,he] using hω
  have hh := actualSourceTimeConstant_unique henv.swap ht
  exact congrFun hh v

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

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem actual_differentiable_away (henv : ExponentialEnvironment P τ) :
    DifferentiableAwayFromOrigin actualSourceTimeConstant := by
  intro v hv
  have hd : DifferentiableAt ℝ actualSourceTimeConstant v := by
    by_cases hh : |v 1| ≤ |v 0|
    · exact actual_differentiable_horizontal henv v hv hh
    · have hsv : swapPlane v ≠ 0 := by intro h; apply hv; exact swapPlane.injective (by simpa using h)
      have hdom : |swapPlane v 1| ≤ |swapPlane v 0| := by simpa using (le_of_not_ge hh)
      have hs := actual_differentiable_horizontal henv (swapPlane v) hsv hdom
      have hc := hs.comp v swapPlane.toContinuousLinearEquiv.differentiableAt
      have he : (fun z => actualSourceTimeConstant (swapPlane z))=actualSourceTimeConstant :=
        funext (actualSourceTimeConstant_swap henv)
      simpa only [Function.comp_def,he] using hc
  exact ⟨fderiv ℝ actualSourceTimeConstant v,hd.hasFDerivAt⟩

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ConvexC1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter
open scoped Topology

lemma convex_continuous_deriv (φ : ℝ → ℝ) (hc : ConvexOn ℝ univ φ)
    (hd : Differentiable ℝ φ) : Continuous (deriv φ) := by
  let g := fun x => deriv φ x+x
  have hm : Monotone g := fun x y h => add_le_add
    (hc.monotoneOn_deriv (fun x _ => hd x) (mem_univ x) (mem_univ y) h) h
  have hg (x : ℝ) : HasDerivAt (fun t => φ t+t^2/2) (g x) x := by
    have hq : HasDerivAt (fun t : ℝ => t^2/2) x x := by
      simpa using ((hasDerivAt_id x).pow 2).div_const 2
    exact (hd x).hasDerivAt.add hq
  have hsurj : Function.Surjective g := by
    intro y
    let a := min 0 (y-deriv φ 0-1)
    let b := max 0 (y-deriv φ 0+1)
    have ha : a ≤ 0 := min_le_left ..
    have hb : 0 ≤ b := le_max_left ..
    have hda := hc.monotoneOn_deriv (fun x _ => hd x) (mem_univ a) (mem_univ 0) ha
    have hdb := hc.monotoneOn_deriv (fun x _ => hd x) (mem_univ 0) (mem_univ b) hb
    have hay : a ≤ y-deriv φ 0-1 := min_le_right ..
    have hby : y-deriv φ 0+1 ≤ b := le_max_right ..
    have hga : g a < y := by dsimp [g]; linarith
    have hgb : y < g b := by dsimp [g]; linarith
    obtain ⟨x,_hx,hx⟩ := exists_hasDerivWithinAt_eq_of_gt_of_lt (ha.trans hb)
      (fun x _ => (hg x).hasDerivWithinAt) hga hgb
    exact ⟨x,hx⟩
  have hcont := hm.continuous_of_surjective hsurj
  convert hcont.sub continuous_id using 1
  funext x
  dsimp [g]
  ring

lemma convex_contDiff_one (φ : ℝ → ℝ) (hc : ConvexOn ℝ univ φ)
    (hd : Differentiable ℝ φ) : ContDiff ℝ 1 φ :=
  contDiff_one_iff_deriv.mpr ⟨hd,convex_continuous_deriv φ hc hd⟩

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_UniqueSupports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter

lemma norm_derivative_subgradient (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (v : Plane) (ℓ : Plane →L[ℝ] ℝ) (hd : HasFDerivAt μ ℓ v) (w : Plane) :
    μ v+ℓ (w-v) ≤ μ w := by
  have hc := convex_transverse_profile μ v (w-v) hμ.triangle (norm_positive_homogeneous μ hμ)
  have ha : HasDerivAt (fun t : ℝ => v+t • (w-v)) (w-v) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (w-v)).const_add v
  have hd' : HasFDerivAt μ ℓ (v+(0 : ℝ) • (w-v)) := by simpa using hd
  have hp := hd'.comp_hasDerivAt 0 ha
  have hh := hc.le_slope_of_hasDerivAt (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) (by norm_num) hp
  simp only [slope_def_field,sub_zero,div_one,one_smul,zero_smul,add_zero,add_sub_cancel] at hh
  linarith

lemma norm_derivative_support (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (v : Plane) (ℓ : Plane →L[ℝ] ℝ) (hd : HasFDerivAt μ ℓ v) :
    ℓ v=μ v ∧ ∀ w, ℓ w ≤ μ w := by
  have h0 := norm_derivative_subgradient μ hμ v ℓ hd 0
  have h2 := norm_derivative_subgradient μ hμ v ℓ hd ((2 : ℝ) • v)
  have hzero : μ 0=0 := (hμ.zero_iff 0).mpr rfl
  have htwo : μ ((2 : ℝ) • v)=2*μ v := by rw [hμ.homogeneous]; norm_num
  have he : (2 : ℝ) • v-v=v := by module
  simp only [zero_sub,map_neg,hzero] at h0
  rw [htwo,he] at h2
  have hv : ℓ v=μ v := by linarith
  refine ⟨hv,?_⟩
  intro w
  have hh := norm_derivative_subgradient μ hμ v ℓ hd w
  rw [map_sub,hv] at hh
  linarith

lemma norm_support_unique (μ : Plane → ℝ) (v : Plane) (ℓ g : Plane →L[ℝ] ℝ)
    (hd : HasFDerivAt μ ℓ v) (hg : g v=μ v) (hlower : ∀ w, g w ≤ μ w) : g=ℓ := by
  have hmin : IsLocalMin (fun w => μ w-g w) v := by
    apply Filter.Eventually.of_forall
    intro w
    have hv : μ v-g v=0 := by rw [hg]; ring
    change μ v-g v ≤ μ w-g w
    rw [hv]
    exact sub_nonneg.mpr (hlower w)
  have he := hmin.hasFDerivAt_eq_zero (hd.sub g.hasFDerivAt)
  exact (sub_eq_zero.mp he).symm

theorem unique_supports_of_differentiable (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hd : DifferentiableAwayFromOrigin μ) : UniqueNormalizedSupports μ := by
  intro v hv
  have hne : v ≠ 0 := by intro he; have hh := (hμ.zero_iff v).mpr he; linarith
  obtain ⟨ℓ,hℓ⟩ := hd v hne
  obtain ⟨he,hl⟩ := norm_derivative_support μ hμ v ℓ hℓ
  refine ⟨ℓ,⟨by rw [he,hv],hl⟩,?_⟩
  intro g hg
  exact norm_support_unique μ v ℓ g hℓ (by rw [hg.1,hv]) hg.2

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_UnitSphereC1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

lemma actual_profile_contDiff (henv : ExponentialEnvironment P τ) :
    ContDiff ℝ 1 (fun t => actualSourceTimeConstant (direction t)) := by
  let μ := actualSourceTimeConstant
  have he (t : ℝ) : direction 0+t • transverseUnit=direction t := by
    ext i; fin_cases i <;> simp [direction,transverseUnit,PiLp.add_apply,PiLp.smul_apply]
  have hc := convex_transverse_profile μ (direction 0) transverseUnit
    actualSourceTimeConstant_norm.triangle (norm_positive_homogeneous μ actualSourceTimeConstant_norm)
  have hd : Differentiable ℝ (fun t : ℝ => μ (direction 0+t • transverseUnit)) := by
    intro t
    have hne : direction t ≠ 0 := by intro hz; have hh := congrArg xCoord hz; change (1 : ℝ)=0 at hh; norm_num at hh
    obtain ⟨ℓ,hℓ⟩ := actual_differentiable_away henv (direction t) hne
    have hh : DifferentiableAt ℝ μ (direction 0+t • transverseUnit) := by rw [he]; exact hℓ.differentiableAt
    have hm : DifferentiableAt ℝ (fun s : ℝ => direction 0+s • transverseUnit) t :=
      (((hasDerivAt_id t).smul_const transverseUnit).const_add (direction 0)).differentiableAt
    exact DifferentiableAt.comp (g := μ) (f := fun s : ℝ => direction 0+s • transverseUnit) t hh hm
  simpa only [he] using convex_contDiff_one _ hc hd

lemma plane_direction_representation (v : Plane) (hx : v 0 ≠ 0) :
    v 0 • direction (v 1/v 0)=v := by
  ext i
  fin_cases i <;> simp [direction,PiLp.smul_apply]
  field_simp

lemma actual_contDiffAt_horizontal (henv : ExponentialEnvironment P τ) (v : Plane) (hx : v 0 ≠ 0) :
    ContDiffAt ℝ 1 actualSourceTimeConstant v := by
  let y : Plane →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1
  have hxc : ContDiffAt ℝ 1 (fun z : Plane => z 0) v := xCoord.contDiff.contDiffAt
  have hyc : ContDiffAt ℝ 1 (fun z : Plane => z 1) v := y.contDiff.contDiffAt
  have hquot := hyc.div hxc hx
  have hprofile := (actual_profile_contDiff henv).contDiffAt.comp v hquot
  have habs : ContDiffAt ℝ 1 (fun z : Plane => |z 0|) v := by
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · have hn : ∀ᶠ z in 𝓝 v, z 0 < 0 := xCoord.continuous.continuousAt.eventually (gt_mem_nhds hneg)
      apply hxc.neg.congr_of_eventuallyEq
      filter_upwards [hn] with z hz
      exact abs_of_neg hz
    · have hn : ∀ᶠ z in 𝓝 v, 0 < z 0 := xCoord.continuous.continuousAt.eventually (lt_mem_nhds hpos)
      apply hxc.congr_of_eventuallyEq
      filter_upwards [hn] with z hz
      exact abs_of_pos hz
  have hprod := habs.mul hprofile
  have heq : actualSourceTimeConstant =ᶠ[𝓝 v]
      (fun z : Plane => |z 0| * actualSourceTimeConstant (direction (z 1/z 0))) := by
    have hn : ∀ᶠ z in 𝓝 v, z 0 ≠ 0 := xCoord.continuous.continuousAt.eventually (eventually_ne_nhds hx)
    filter_upwards [hn] with z hz
    conv_lhs => rw [← plane_direction_representation z hz]
    exact actualSourceTimeConstant_norm.homogeneous _ _
  exact hprod.congr_of_eventuallyEq heq

theorem actual_contDiffAt_away (henv : ExponentialEnvironment P τ) (v : Plane) (hv : v ≠ 0) :
    ContDiffAt ℝ 1 actualSourceTimeConstant v := by
  by_cases hx : v 0 ≠ 0
  · exact actual_contDiffAt_horizontal henv v hx
  · have hy : v 1 ≠ 0 := by
      intro hy
      apply hv
      ext i
      fin_cases i <;> simp_all
    have hswap : swapPlane v 0 ≠ 0 := by simpa using hy
    have hs := actual_contDiffAt_horizontal henv (swapPlane v) hswap
    have hh := hs.comp v swapPlane.toContinuousLinearEquiv.contDiff.contDiffAt
    have he : (fun z => actualSourceTimeConstant (swapPlane z))=actualSourceTimeConstant :=
      funext (actualSourceTimeConstant_swap henv)
    simpa only [Function.comp_def,he] using hh

theorem actual_C1_unit_sphere (henv : ExponentialEnvironment P τ) : C1UnitSphere actualSourceTimeConstant := by
  let μ := actualSourceTimeConstant
  let U : Set Plane := {0}ᶜ
  have hU : IsOpen U := isClosed_singleton.isOpen_compl
  have hc : ContDiffOn ℝ 1 μ U := by
    intro v hv
    exact (actual_contDiffAt_away henv v hv).contDiffWithinAt
  intro v hv
  have hne : v ≠ 0 := by intro he; have hz := (actualSourceTimeConstant_norm.zero_iff v).mpr he; linarith
  refine ⟨U,hU,hne,fun w => μ w-1,hc.sub contDiffOn_const,?_,?_⟩
  · intro w _
    exact sub_eq_zero.symm
  · intro w hw hzero
    have hw1 : μ w=1 := sub_eq_zero.mp hzero
    obtain ⟨ℓ,hℓ⟩ := actual_differentiable_away henv w hw
    have hEuler := (norm_derivative_support μ actualSourceTimeConstant_norm w ℓ hℓ).1
    refine ⟨ℓ,by simpa using hℓ.sub_const 1,?_⟩
    intro hz
    simp [hz,hw1] at hEuler

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_NormBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology

theorem norm_ball_frontier (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    frontier {v | μ v ≤ 1}={v | μ v=1} := by
  apply Subset.antisymm (frontier_le_subset_eq (timeConstantNorm_continuous μ hμ) continuous_const)
  intro v hv
  change μ v=1 at hv
  rw [frontier_eq_closure_inter_closure]
  refine ⟨subset_closure (show μ v ≤ 1 by exact hv.le),?_⟩
  have ht : Tendsto (fun t : ℝ => t • v) (𝓝[>] (1 : ℝ)) (𝓝 v) := by
    have hh : ContinuousAt (fun t : ℝ => t • v) 1 := continuous_id.smul continuous_const |>.continuousAt
    simpa only [one_smul] using hh.mono_left (show 𝓝[>] (1 : ℝ) ≤ 𝓝 (1 : ℝ) from nhdsWithin_le_nhds)
  apply mem_closure_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 1<t at ht
  change ¬μ (t • v) ≤ 1
  rw [hμ.homogeneous,hv,abs_of_pos (show 0<t by linarith)]
  linarith

lemma ball_support_contact_pos (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (v : Plane) (g : Plane →L[ℝ] ℝ) (hg : g ≠ 0)
    (hs : ∀ z, μ z ≤ 1 → g z ≤ g v) : 0 < g v := by
  obtain ⟨u,hu⟩ : ∃ u : Plane, g u ≠ 0 := by
    by_contra hh
    apply hg
    ext u
    simpa using not_exists.mp hh u
  let w := g u • u
  have hwg : 0 < g w := by
    dsimp [w]
    rw [map_smul,smul_eq_mul]
    exact mul_self_pos.mpr hu
  have hw : w ≠ 0 := by intro hz; rw [hz,map_zero] at hwg; exact lt_irrefl _ hwg
  have hμw : 0 < μ w := lt_of_le_of_ne (hμ.nonneg w) (fun h => hw ((hμ.zero_iff w).mp h.symm))
  have hunit : μ ((μ w)⁻¹ • w)=1 := by
    rw [hμ.homogeneous,abs_of_pos (inv_pos.mpr hμw),inv_mul_cancel₀ hμw.ne']
  have hh := hs ((μ w)⁻¹ • w) hunit.le
  rw [map_smul,smul_eq_mul] at hh
  exact (mul_pos (inv_pos.mpr hμw) hwg).trans_le hh

lemma ball_support_normalized (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (v : Plane) (_hv : μ v=1) (g : Plane →L[ℝ] ℝ) (hg : g ≠ 0)
    (hs : ∀ z, μ z ≤ 1 → g z ≤ g v) :
    ((g v)⁻¹ • g) v=1 ∧ ∀ z, ((g v)⁻¹ • g) z ≤ μ z := by
  have hc := ball_support_contact_pos μ hμ v g hg hs
  constructor
  · simp [inv_mul_cancel₀ hc.ne']
  · intro z
    by_cases hz : z=0
    · subst z
      simp [(hμ.zero_iff 0).mpr rfl]
    · have hμz : 0 < μ z := lt_of_le_of_ne (hμ.nonneg z) (fun h => hz ((hμ.zero_iff z).mp h.symm))
      have hn : μ ((μ z)⁻¹ • z)=1 := by
        rw [hμ.homogeneous,abs_of_pos (inv_pos.mpr hμz),inv_mul_cancel₀ hμz.ne']
      have hh := hs ((μ z)⁻¹ • z) hn.le
      simp only [map_smul,smul_eq_mul] at hh
      have hmul := mul_le_mul_of_nonneg_left hh hμz.le
      rw [← mul_assoc,mul_inv_cancel₀ hμz.ne',one_mul] at hmul
      change (g v)⁻¹*g z ≤ μ z
      exact (inv_mul_le_iff₀ hc).mpr (by nlinarith)

theorem norm_supporting_line_unique (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hd : DifferentiableAwayFromOrigin μ) (v : Plane) (hv : v ∈ frontier {z | μ z ≤ 1}) :
    ∃! L : Set Plane, ∃ g : Plane →L[ℝ] ℝ, g ≠ 0 ∧
      (∀ z, μ z ≤ 1 → g z ≤ g v) ∧ L={z | g z=g v} := by
  have hv1 : μ v=1 := by rw [norm_ball_frontier μ hμ] at hv; exact hv
  obtain ⟨ℓ,hℓ,hunique⟩ := unique_supports_of_differentiable μ hμ hd v hv1
  have hℓne : ℓ ≠ 0 := by intro he; simp [he] at hℓ
  refine ⟨{z | ℓ z=1},⟨ℓ,hℓne,fun z hz => (hℓ.2 z).trans (by rw [hℓ.1]; exact hz),by rw [hℓ.1]⟩,?_⟩
  rintro L ⟨g,hg,hs,rfl⟩
  have hc := ball_support_contact_pos μ hμ v g hg hs
  have he := hunique ((g v)⁻¹ • g) (ball_support_normalized μ hμ v hv1 g hg hs)
  ext z
  rw [← he]
  change g z=g v ↔ (g v)⁻¹*g z=1
  constructor
  · intro hz
    rw [hz,inv_mul_cancel₀ hc.ne']
  · intro hz
    have hh := congrArg (fun x : ℝ => g v*x) hz
    simpa only [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul,mul_one] using hh

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SphereCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology

lemma contDiff_direction : ContDiff ℝ 1 direction := by
  have hh : ContDiff ℝ 1 (fun t : ℝ => direction 0+t • transverseUnit) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have he : (fun t : ℝ => direction 0+t • transverseUnit)=direction := by
    funext t; ext i; fin_cases i <;> simp [direction,transverseUnit,PiLp.add_apply,PiLp.smul_apply]
  rwa [he] at hh

lemma sphereChart_coordinates (μ : Plane → ℝ) (c t : ℝ) :
    sphereChart μ c t 0=c/μ (direction t) ∧ sphereChart μ c t 1=(c/μ (direction t))*t := by
  simp [sphereChart,direction,PiLp.smul_apply]

lemma sphereChart_ratio (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (c : ℝ) (hc : c ≠ 0) (t : ℝ) :
    directionRatio (sphereChart μ c t)=t := by
  obtain ⟨h0,h1⟩ := sphereChart_coordinates μ c t
  unfold directionRatio
  rw [h0,h1]
  have hp := norm_direction_pos μ hμ t
  field_simp

lemma sphereChart_mem (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (c : ℝ) (hc : |c|=1) (t : ℝ) :
    μ (sphereChart μ c t)=1 ∧ 0 < c*sphereChart μ c t 0 := by
  have hp := norm_direction_pos μ hμ t
  have hc0 : c ≠ 0 := by intro he; simp [he] at hc
  constructor
  · rw [sphereChart,hμ.homogeneous,abs_div,hc,abs_of_pos hp]
    field_simp
  · rw [(sphereChart_coordinates μ c t).1]
    have hcs : 0 < c*c := mul_self_pos.mpr hc0
    exact (div_pos hcs hp).trans_eq (by ring)

lemma sphereChart_reconstruct (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (c : ℝ) (hc : |c|=1) (v : Plane) (hv : μ v=1) (hsign : 0 < c*v 0) :
    sphereChart μ c (directionRatio v)=v := by
  have hx : v 0 ≠ 0 := by intro he; rw [he,mul_zero] at hsign; exact lt_irrefl _ hsign
  have hrep := plane_direction_representation v hx
  change v 0 • direction (directionRatio v)=v at hrep
  have hnorm : |v 0| *μ (direction (directionRatio v))=1 := by
    rw [← hμ.homogeneous,hrep,hv]
  have hcx : c*|v 0|=v 0 := by
    rcases eq_or_eq_neg_of_abs_eq hc with hc | hc
    · rw [hc] at hsign ⊢
      simp only [one_mul] at hsign ⊢
      exact abs_of_pos hsign
    · rw [hc] at hsign ⊢
      have hvneg : v 0 < 0 := by linarith
      rw [abs_of_neg hvneg]
      ring
  have he : c/μ (direction (directionRatio v))=v 0 := by
    apply (div_eq_iff (ne_of_gt (norm_direction_pos μ hμ _))).mpr
    rw [← hcx,mul_assoc,hnorm,mul_one]
  rw [sphereChart,he]
  exact hrep

lemma sphereChart_contDiff (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hφ : ContDiff ℝ 1 (fun t => μ (direction t))) (c : ℝ) :
    ContDiff ℝ 1 (sphereChart μ c) :=
  (contDiff_const.div hφ (fun t => ne_of_gt (norm_direction_pos μ hμ t))).smul contDiff_direction

lemma sphereChart_regular (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hφ : ContDiff ℝ 1 (fun t => μ (direction t))) (c : ℝ) (hc : c ≠ 0) (t : ℝ) :
    ∃ d : Plane, HasDerivAt (sphereChart μ c) d t ∧ d ≠ 0 := by
  have hg := ((sphereChart_contDiff μ hμ hφ c).differentiable (by norm_num) t).hasDerivAt
  let y : Plane →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1
  have hx : sphereChart μ c t 0 ≠ 0 := by
    rw [(sphereChart_coordinates μ c t).1]
    exact div_ne_zero hc (ne_of_gt (norm_direction_pos μ hμ t))
  have hyc : ContDiffAt ℝ 1 (fun z : Plane => z 1) (sphereChart μ c t) := y.contDiff.contDiffAt
  have hxc : ContDiffAt ℝ 1 (fun z : Plane => z 0) (sphereChart μ c t) := xCoord.contDiff.contDiffAt
  have hr : DifferentiableAt ℝ directionRatio (sphereChart μ c t) :=
    (hyc.div hxc hx).differentiableAt (by norm_num)
  have hchain := hr.hasFDerivAt.comp_hasDerivAt t hg
  have he : (directionRatio ∘ sphereChart μ c)=id := funext (sphereChart_ratio μ hμ c hc)
  rw [he] at hchain
  have hid := hchain.unique (hasDerivAt_id t)
  refine ⟨_,hg,?_⟩
  intro hz
  rw [hz,map_zero] at hid
  norm_num at hid

lemma sphere_horizontal_chart (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hφ : ContDiff ℝ 1 (fun t => μ (direction t))) (c : ℝ) (hc : |c|=1)
    (v : Plane) (hv : μ v=1) (hsign : 0 < c*v 0) : HasC1CurveChart {z | μ z=1} v := by
  let U : Set Plane := {z | 0 < c*z 0}
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_const.mul xCoord.continuous)
  have hc0 : c ≠ 0 := by intro he; simp [he] at hc
  let y : Plane →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1
  have hθ : ContinuousOn directionRatio U := y.continuous.continuousOn.div xCoord.continuous.continuousOn
    (fun z hz => by intro he; change 0<c*z 0 at hz; rw [he,mul_zero] at hz; exact lt_irrefl _ hz)
  exact ⟨U,hU,hsign,hv,sphereChart μ c,directionRatio,sphereChart_contDiff μ hμ hφ c,hθ,
    sphereChart_mem μ hμ c hc,sphereChart_ratio μ hμ c hc0,
    fun z hz => sphereChart_reconstruct μ hμ c hc z hz.1 hz.2,sphereChart_regular μ hμ hφ c hc0⟩

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BoundaryCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set MeasureTheory

lemma HasC1CurveChart.preimage_isometry (S : Set Plane) (v : Plane)
    (e : Plane ≃ₗᵢ[ℝ] Plane) (h : HasC1CurveChart S (e v)) :
    HasC1CurveChart (e ⁻¹' S) v := by
  obtain ⟨U,hU,hv,hvS,γ,θ,hγ,hθ,hmem,hleft,hright,hreg⟩ := h
  refine ⟨e ⁻¹' U,hU.preimage e.continuous,hv,hvS,e.symm ∘ γ,θ ∘ e,?_,?_,?_,?_,?_,?_⟩
  · exact e.symm.toContinuousLinearEquiv.contDiff.comp hγ
  · exact hθ.comp e.continuous.continuousOn (fun _ hz => hz)
  · intro t
    simpa only [Function.comp_apply,mem_inter_iff,mem_preimage,e.apply_symm_apply] using hmem t
  · intro t
    simpa only [Function.comp_apply,e.apply_symm_apply] using hleft t
  · intro z hz
    change e.symm (γ (θ (e z)))=z
    rw [hright (e z) hz,e.symm_apply_apply]
  · intro t
    obtain ⟨d,hd,hne⟩ := hreg t
    refine ⟨e.symm d,e.symm.toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivAt t hd,?_⟩
    intro hz
    exact hne (e.symm.injective (by simpa using hz))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem actual_sphere_curve_chart (henv : ExponentialEnvironment P τ) (v : Plane)
    (hv : actualSourceTimeConstant v=1) : HasC1CurveChart {z | actualSourceTimeConstant z=1} v := by
  let μ := actualSourceTimeConstant
  have horizontal (z : Plane) (hz : μ z=1) (hx : z 0 ≠ 0) : HasC1CurveChart {w | μ w=1} z := by
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · exact sphere_horizontal_chart μ actualSourceTimeConstant_norm (actual_profile_contDiff henv) (-1)
        (by norm_num) z hz (by linarith)
    · exact sphere_horizontal_chart μ actualSourceTimeConstant_norm (actual_profile_contDiff henv) 1
        (by norm_num) z hz (by simpa using hpos)
  by_cases hx : v 0 ≠ 0
  · exact horizontal v hv hx
  · have hvne : v ≠ 0 := by
      intro he
      have hz := (actualSourceTimeConstant_norm.zero_iff v).mpr he
      linarith
    have hy : v 1 ≠ 0 := by
      intro hy
      apply hvne
      ext i
      fin_cases i <;> simp_all
    have hsv : μ (swapPlane v)=1 := by dsimp [μ]; rw [actualSourceTimeConstant_swap henv,hv]
    have hs := horizontal (swapPlane v) hsv (by simpa using hy)
    have hh := HasC1CurveChart.preimage_isometry {z | μ z=1} v swapPlane hs
    have he : swapPlane ⁻¹' {z | μ z=1}={z | μ z=1} := by
      ext z
      simp only [mem_preimage,mem_ofPred_eq,μ,actualSourceTimeConstant_swap henv]
    rwa [he] at hh

theorem actual_boundary_curve (henv : ExponentialEnvironment P τ) (v : Plane)
    (hv : v ∈ frontier {z | actualSourceTimeConstant z ≤ 1}) :
    HasC1CurveChart (frontier {z | actualSourceTimeConstant z ≤ 1}) v := by
  rw [norm_ball_frontier _ actualSourceTimeConstant_norm] at hv ⊢
  exact actual_sphere_curve_chart henv v hv

theorem manuscriptMain_oai (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (τ : Edge → Ω → ℝ)
    (henv : ExponentialEnvironment P τ) :
    ∃ μ : Plane → ℝ, TimeConstantNorm μ ∧ IsTimeConstant P τ μ ∧
      DifferentiableAwayFromOrigin μ ∧ UniqueNormalizedSupports μ ∧ C1UnitSphere μ ∧
      (∀ v ∈ frontier {z | μ z ≤ 1}, ∃! L : Set Plane,
        ∃ g : Plane →L[ℝ] ℝ, g ≠ 0 ∧ (∀ z, μ z ≤ 1 → g z ≤ g v) ∧ L={z | g z=g v}) ∧
      (∀ v ∈ frontier {z | μ z ≤ 1}, HasC1CurveChart (frontier {z | μ z ≤ 1}) v) := by
  exact ⟨actualSourceTimeConstant,actualSourceTimeConstant_norm,actualSourceTimeConstant_isTimeConstant henv,
    actual_differentiable_away henv,
    unique_supports_of_differentiable _ actualSourceTimeConstant_norm (actual_differentiable_away henv),
    actual_C1_unit_sphere henv,
    norm_supporting_line_unique _ actualSourceTimeConstant_norm (actual_differentiable_away henv),
    actual_boundary_curve henv⟩

end PlanarFPP

end OAI
end

theorem solution : type_of% @OAI.PlanarFPP.manuscriptMain_oai := @OAI.PlanarFPP.manuscriptMain_oai
