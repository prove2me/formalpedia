-- Prove2me | solution 1 for OAI.PlanarFPP.exponential_goodSite_path_probability_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:46:13.929685+00:00
-- url     : https://prove2.me/submissions/f431046b-4392-4a5c-a636-c278278494d5

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

theorem defect_append (τ : Edge → ℝ) (b m a : ℝ) (p : Vertex) (ds es : List Step) :
    defect τ b m a p (ds ++ es) =
      defect τ b m a p ds + defect τ b m a (p + displacement ds) es := by
  simp [defect, pathCost_append]; ring

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
-- module Solutions.OAIS_PlanarFPP.FirstPassage_LocalizedEvents
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

theorem pathIn_endpoint (p : Vertex) (ds : List Step) (S : Set Vertex)
    (h : PathIn p ds S) : p+displacement ds ∈ S := by
  simpa using h ds.length le_rfl

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

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_CrossingTrialGeometry
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset

theorem nearest_integer_error (t : ℝ) : |(⌊t+1/2⌋ : ℝ)-t| ≤ 1/2 := by
  have hlo := Int.floor_le (t+1/2)
  have hhi := Int.lt_floor_add_one (t+1/2)
  apply abs_le.mpr
  constructor <;> linarith

theorem trialTranslate_error (b : ℝ) (X : ℤ) (Y : ℝ)
    (M : ℕ) (R s : ℝ) (j : Fin M) :
    |transverse b (trialTranslate b X Y M R s j)-(Y+trialOffset M R s j)| ≤ 1/2 := by
  have hh := nearest_integer_error (b*X+Y+trialOffset M R s j)
  convert hh using 1
  simp [trialTranslate,transverse]
  congr 1
  ring

theorem trialSpacing_bounds (R s : ℝ) (hR : 0 ≤ R) (hs : 1 ≤ s) :
    1 ≤ trialSpacing R s ∧ R*s ≤ trialSpacing R s := by
  have hc := Nat.le_ceil s
  have hn : (1 : ℝ) ≤ (⌈s⌉₊ : ℝ) := by linarith
  unfold trialSpacing
  constructor
  · nlinarith
  · nlinarith

theorem trialOffset_bound (M : ℕ) (R s : ℝ) (j : Fin M)
    (hR : 0 ≤ R) (hs : 1 ≤ s) :
    |trialOffset M R s j| ≤ 3*M*trialSpacing R s := by
  have hB := (trialSpacing_bounds R s hR hs).1
  have hj : (j.val : ℝ)+1 ≤ M := by exact_mod_cast j.isLt
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  have ha : |2*((j.val : ℝ)+1)-(M : ℝ)-1| ≤ M := by
    apply abs_le.mpr
    constructor <;> linarith
  unfold trialOffset
  rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<3),abs_of_nonneg (show 0 ≤ trialSpacing R s by linarith)]
  nlinarith

theorem trial_strip_in_window (b : ℝ) (X : ℤ) (Y : ℝ)
    (M : ℕ) (R s : ℝ) (j : Fin M) (hR : 0 ≤ R) (hs : 1 ≤ s)
    (p : Vertex) (hp : |transverse b p-transverse b (trialTranslate b X Y M R s j)| ≤ R*s) :
    |transverse b p-Y| ≤ trialWindow M R s/4 := by
  have he := trialTranslate_error b X Y M R s j
  have ho := trialOffset_bound M R s j hR hs
  have hB := trialSpacing_bounds R s hR hs
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast j.pos
  have hh := abs_add_le
    (transverse b (trialTranslate b X Y M R s j)-(Y+trialOffset M R s j))
    (trialOffset M R s j)
  have heq : transverse b (trialTranslate b X Y M R s j)-(Y+trialOffset M R s j)+
      trialOffset M R s j = transverse b (trialTranslate b X Y M R s j)-Y := by ring
  rw [heq] at hh
  have ht := abs_add_le (transverse b p-transverse b (trialTranslate b X Y M R s j))
    (transverse b (trialTranslate b X Y M R s j)-Y)
  rw [sub_add_sub_cancel] at ht
  unfold trialWindow
  nlinarith [mul_le_mul_of_nonneg_right hM (by linarith : 0 ≤ trialSpacing R s)]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_Supports
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem support_le_of_positive_halfspace (μ : E → ℝ) (x f : E →ₗ[ℝ] ℝ) (u : E)
    (hadd : ∀ z w, μ (z + w) ≤ μ z + μ w)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z)
    (hxu : x u = 1) (hfu : f u = μ u)
    (hhalf : ∀ z, 0 < x z → f z ≤ μ z) : ∀ z, f z ≤ μ z := by
  intro z
  let t : ℝ := |x z| + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hz : 0 < x (z + t • u) := by
    simp only [map_add, map_smul, hxu, smul_eq_mul, mul_one]
    dsimp [t]
    linarith [neg_le_abs (x z)]
  have hh := hhalf (z + t • u) hz
  have ha := hadd z (t • u)
  rw [hhom t ht u] at ha
  simp only [map_add, map_smul, smul_eq_mul, hfu] at hh
  linarith

theorem support_from_transverse_subgradient (μ : E → ℝ) (x r : E →ₗ[ℝ] ℝ)
    (u e : E) (a : ℝ)
    (hadd : ∀ z w, μ (z + w) ≤ μ z + μ w)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z)
    (hxu : x u = 1) (hru : r u = 0)
    (hcoords : ∀ z, z = x z • u + r z • e)
    (hsub : ∀ t : ℝ, μ u + a * t ≤ μ (u + t • e)) :
    (∀ z, coordinateSupport x r (μ u) a z ≤ μ z) ∧
      coordinateSupport x r (μ u) a u = μ u := by
  have hcontact : coordinateSupport x r (μ u) a u = μ u := by
    simp [hxu, hru]
  refine ⟨support_le_of_positive_halfspace μ x _ u hadd hhom hxu hcontact ?_, hcontact⟩
  intro z hz
  have hrepr : z = x z • (u + (r z / x z) • e) := by
    rw [smul_add, smul_smul]
    have heq : x z * (r z / x z) = r z := by field_simp [ne_of_gt hz]
    rw [heq]
    exact hcoords z
  have hbound := mul_le_mul_of_nonneg_left (hsub (r z / x z)) (le_of_lt hz)
  have hμ : μ z = x z * μ (u + (r z / x z) • e) := by
    conv_lhs => rw [hrepr]
    exact hhom _ (le_of_lt hz) _
  rw [coordinateSupport_apply, hμ]
  calc
    μ u * x z + a * r z = x z * (μ u + a * (r z / x z)) := by
      field_simp [ne_of_gt hz]
    _ ≤ x z * μ (u + (r z / x z) • e) := hbound

end
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

theorem extreme_supports {E : Type*} [AddCommGroup E] [Module ℝ E]
    (μ : E → ℝ) (x r : E →ₗ[ℝ] ℝ) (u e : E)
    (hadd : ∀ z w, μ (z + w) ≤ μ z + μ w)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z)
    (hxu : x u = 1) (hru : r u = 0)
    (hcoords : ∀ z, z = x z • u + r z • e) :
    let φ := fun t : ℝ => μ (u + t • e)
    (∀ z, coordinateSupport x r (μ u) (leftSlope φ) z ≤ μ z) ∧
    (∀ z, coordinateSupport x r (μ u) (rightSlope φ) z ≤ μ z) ∧
    coordinateSupport x r (μ u) (leftSlope φ) u = μ u ∧
    coordinateSupport x r (μ u) (rightSlope φ) u = μ u := by
  dsimp only
  obtain ⟨hl, hr⟩ := extreme_subgradients _ (convex_transverse_profile μ u e hadd hhom)
  have hls := support_from_transverse_subgradient μ x r u e _ hadd hhom hxu hru hcoords
    (by simpa using hl)
  have hrs := support_from_transverse_subgradient μ x r u e _ hadd hhom hxu hru hcoords
    (by simpa using hr)
  exact ⟨hls.1, hrs.1, hls.2, hrs.2⟩

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

theorem planar_extreme_supports (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (b : ℝ) :
    let φ := fun t : ℝ => μ (direction b + t • transverseUnit)
    (∀ z, coordinateSupport xCoord.toLinearMap (rCoord b).toLinearMap
      (μ (direction b)) (leftSlope φ) z ≤ μ z) ∧
    (∀ z, coordinateSupport xCoord.toLinearMap (rCoord b).toLinearMap
      (μ (direction b)) (rightSlope φ) z ≤ μ z) ∧
    coordinateSupport xCoord.toLinearMap (rCoord b).toLinearMap
      (μ (direction b)) (leftSlope φ) (direction b) = μ (direction b) ∧
    coordinateSupport xCoord.toLinearMap (rCoord b).toLinearMap
      (μ (direction b)) (rightSlope φ) (direction b) = μ (direction b) := by
  exact extreme_supports μ xCoord.toLinearMap (rCoord b).toLinearMap (direction b)
    transverseUnit hμ.triangle (norm_positive_homogeneous μ hμ)
    (xCoord_direction b) (rCoord_direction b) (plane_reconstruction b)

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

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ShapeDeficit
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory Filter Set
open scoped Topology

theorem UniformShape.no_linear_deficit (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (μ f : Plane → ℝ) (hu : UniformShape w μ) (hf : ∀ v, f v ≤ μ v)
    (z : ℕ → Vertex) (ds : ℕ → List Step) (C a B : ℝ) (ha : 0 < a) (hB : 0 < B)
    (hescape : Tendsto (fun n => ‖latticeEmbed (z n)‖) atTop atTop)
    (hbound : ∀ n, ‖latticeEmbed (z n)‖ ≤ B*((n : ℝ)+1))
    (hend : ∀ n, displacement (ds n)=z n)
    (hcost : ∀ n, pathCost w 0 (ds n) ≤ f (latticeEmbed (z n))+C-a*n) : False := by
  obtain ⟨R,hR,hr⟩ := hu (a/(2*B)) (by positivity)
  have hlarge : ∀ᶠ n : ℕ in atTop, 2*C/a+2 < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
  obtain ⟨n,hnR,hn⟩ := ((hescape.eventually (eventually_ge_atTop R)).and hlarge).exists
  have he := hr (z n) hnR
  have hlow := (abs_le.mp he).1
  have hpass := passageTime_le_cost w hw 0 (z n) (ds n) (by simpa using hend n)
  have hprod := mul_le_mul_of_nonneg_left (hbound n) (show 0 ≤ a/(2*B) by positivity)
  have hid : a/(2*B)*(B*((n : ℝ)+1))=a/2*((n : ℝ)+1) := by field_simp
  rw [hid] at hprod
  have hn' := (div_lt_iff₀ ha).mp (show 2*C/a < (n : ℝ)-2 by linarith)
  have hs := hf (latticeEmbed (z n))
  have hc := hcost n
  nlinarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_CrossingChain
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Filter
open scoped Topology

theorem crossingChain_endpoint (initialPath : List Step) (trial connector : ℕ → List Step)
    (a z : ℕ → Vertex) (hp : displacement initialPath = a 0)
    (ht : ∀ n, a n+displacement (trial n)=z n)
    (hc : ∀ n, z n+displacement (connector n)=a (n+1)) (n : ℕ) :
    displacement (crossingChain initialPath trial connector n)=z n := by
  induction n with
  | zero => simpa only [crossingChain,displacement_append,hp] using ht 0
  | succ n ih =>
    simp only [crossingChain,displacement_append,ih,← add_assoc,hc,ht]

theorem crossingChain_defect (w : Edge → ℝ) (b m a e : ℝ)
    (initialPath : List Step) (trial connector : ℕ → List Step) (p z : ℕ → Vertex)
    (hp : displacement initialPath=p 0)
    (ht : ∀ n, p n+displacement (trial n)=z n)
    (hc : ∀ n, z n+displacement (connector n)=p (n+1))
    (htrial : ∀ n, defect w b m a (p n) (trial n) ≤ -e)
    (hconnector : ∀ n, defect w b m a (z n) (connector n) ≤ e/2) (n : ℕ) :
    defect w b m a 0 (crossingChain initialPath trial connector n) ≤
      defect w b m a 0 initialPath-((n : ℝ)+1)*e+(n : ℝ)*e/2 := by
  induction n with
  | zero =>
    simp only [crossingChain,defect_append,zero_add,hp]
    have hh := htrial 0
    norm_num
    linarith
  | succ n ih =>
    rw [crossingChain,defect_append,crossingChain_endpoint initialPath trial connector p z hp ht hc,
      zero_add,defect_append,hc]
    have h1 := htrial (n+1)
    have h2 := hconnector n
    push_cast
    linarith

theorem oriented_path_coordinates (v : ℕ → Vertex) (h0 : v 0=0)
    (hs : ∀ n, v (n+1)=v n+(1,0) ∨ v (n+1)=v n+(0,1)) (n : ℕ) :
    (v n).1+(v n).2=(n : ℤ) ∧ 0 ≤ (v n).1 ∧ 0 ≤ (v n).2 ∧ (v n).2 ≤ n := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rcases hs n with he | he <;> rw [he] <;> simp only [Prod.fst_add,Prod.snd_add] <;>
      push_cast <;> omega

theorem UniformShape.no_crossing_chain (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (μ : Plane → ℝ) (hu : UniformShape w μ) (b m a e B : ℝ) (he : 0 < e) (hB : 0 < B)
    (hf : ∀ v, m*v 0+a*(v 1-b*v 0) ≤ μ v)
    (initialPath : List Step) (trial connector : ℕ → List Step) (p z : ℕ → Vertex)
    (hp : displacement initialPath=p 0)
    (ht : ∀ n, p n+displacement (trial n)=z n)
    (hc : ∀ n, z n+displacement (connector n)=p (n+1))
    (htrial : ∀ n, defect w b m a (p n) (trial n) ≤ -e)
    (hconnector : ∀ n, defect w b m a (z n) (connector n) ≤ e/2)
    (hescape : Tendsto (fun n => ‖latticeEmbed (z n)‖) atTop atTop)
    (hbound : ∀ n, ‖latticeEmbed (z n)‖ ≤ B*((n : ℝ)+1)) : False := by
  apply hu.no_linear_deficit w hw μ (fun v => m*v 0+a*(v 1-b*v 0)) hf z
    (crossingChain initialPath trial connector) (defect w b m a 0 initialPath) (e/2) B
    (by linarith) hB hescape hbound
    (crossingChain_endpoint initialPath trial connector p z hp ht hc)
  intro n
  have hh := crossingChain_defect w b m a e initialPath trial connector p z hp ht hc htrial hconnector n
  rw [defect,crossingChain_endpoint initialPath trial connector p z hp ht hc] at hh
  simp only [support,transverse] at hh
  change pathCost w 0 (crossingChain initialPath trial connector n) ≤
    m*(z n).1+a*((z n).2-b*(z n).1)+defect w b m a 0 initialPath-e/2*n
  linarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_CrossingEndpointBounds
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Filter
open scoped Topology

theorem crossing_endpoints_escape_linear (b σ S : ℝ) (n d : ℤ)
    (hb : |b| ≤ 1) (hσ : |σ|=1) (hS : 0 < S) (hn : 0 < n) (hd : 0 ≤ d)
    (v z : ℕ → Vertex) (hv0 : v 0=0)
    (hstep : ∀ t, v (t+1)=v t+(1,0) ∨ v (t+1)=v t+(0,1))
    (hx : ∀ t, (z t).1=blockX n d (v t)+n)
    (hr : ∀ t, |transverse b (z t)-blockY σ S (v t)| ≤ S/4) :
    Tendsto (fun t => ‖latticeEmbed (z t)‖) atTop atTop ∧
    ∀ t, ‖latticeEmbed (z t)‖ ≤ (2*((n : ℝ)+d)+3*S)*((t : ℝ)+1) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd' : (0 : ℝ) ≤ d := by exact_mod_cast hd
  have hcoords (t : ℕ) := oriented_path_coordinates v hv0 hstep t
  have hxt (t : ℕ) : ((z t).1 : ℝ) = (t : ℝ)*((n : ℝ)+d)+n := by
    rw [hx]
    simp only [blockX,blockLayer,Int.cast_add,Int.cast_mul]
    have hh := congrArg (fun a : ℤ => (a : ℝ)) (hcoords t).1
    push_cast at hh
    rw [hh]
  have hxpos (t : ℕ) : (t : ℝ)+1 ≤ ((z t).1 : ℝ) := by
    rw [hxt]
    nlinarith [Nat.cast_nonneg (α := ℝ) t]
  have hnlow (t : ℕ) : (t : ℝ) ≤ ‖latticeEmbed (z t)‖ := by
    have hh := plane_coordinate_le_norm (latticeEmbed (z t)) 0
    change |((z t).1 : ℝ)| ≤ _ at hh
    have hp : (0 : ℝ) ≤ (z t).1 := by linarith [Nat.cast_nonneg (α := ℝ) t,hxpos t]
    rw [abs_of_nonneg hp] at hh
    linarith [hxpos t]
  refine ⟨tendsto_atTop_mono hnlow tendsto_natCast_atTop_atTop,?_⟩
  intro t
  have hlevel : (0 : ℝ) ≤ blockLevel (v t) ∧ (blockLevel (v t) : ℝ) ≤ 2*t := by
    have hh := hcoords t
    constructor <;> dsimp [blockLevel] <;> exact_mod_cast (by omega : _)
  have hy : |blockY σ S (v t)| ≤ 2*(t : ℝ)*S := by
    unfold blockY
    rw [abs_mul,abs_mul,hσ,one_mul,abs_of_nonneg hlevel.1,abs_of_pos hS]
    exact mul_le_mul_of_nonneg_right hlevel.2 hS.le
  have hrbound : |transverse b (z t)| ≤ 2*(t : ℝ)*S+S/4 := by
    have hh := abs_add_le (transverse b (z t)-blockY σ S (v t)) (blockY σ S (v t))
    rw [sub_add_cancel] at hh
    linarith [hr t]
  have hpos : (0 : ℝ) ≤ (z t).1 := by linarith [hxpos t,Nat.cast_nonneg (α := ℝ) t]
  have hyy : |((z t).2 : ℝ)| ≤ |transverse b (z t)|+((z t).1 : ℝ) := by
    have hh := abs_add_le (transverse b (z t)) (b*((z t).1 : ℝ))
    have he : transverse b (z t)+b*((z t).1 : ℝ)=((z t).2 : ℝ) := by unfold transverse; ring
    rw [he,abs_mul,abs_of_nonneg hpos] at hh
    have hm := mul_le_mul_of_nonneg_right hb hpos
    linarith
  have hnorm := plane_norm_le_coordinates (latticeEmbed (z t))
  change ‖latticeEmbed (z t)‖ ≤ |((z t).1 : ℝ)|+|((z t).2 : ℝ)| at hnorm
  rw [abs_of_nonneg hpos] at hnorm
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  rw [hxt] at hyy hnorm
  nlinarith

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

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GoodSitePaths
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology

theorem goodSite_trial_witness (μ : Plane → ℝ) (b A R ε s : ℝ) (plus : Bool)
    (n d : ℤ) (M : ℕ) (v : Vertex) (w : Edge → ℝ) (hR : 0 ≤ R) (hs : 1 ≤ s)
    (hg : w ∈ goodSiteEvent μ b A R ε s plus n d M v) :
    ∃ p ds,
      p ∈ connectorWindow b (blockX n d v) (blockY (contactSign plus) (trialWindow M R s) v)
        (trialWindow M R s) ∧
      p+displacement ds ∈ connectorWindow b (blockX n d v+n)
        (blockY (contactSign plus) (trialWindow M R s) v) (trialWindow M R s) ∧
      defect w b (μ (direction b)) (extremeSlope μ b plus) p ds < -ε*s := by
  obtain ⟨j,hj⟩ := hg.1
  obtain ⟨p,ds,hp,hq,hin,hcost⟩ := (mem_rareFastEvent ..).mp hj
  have hw (q : Vertex) (hq : q ∈ rareFastRegion b A R s n
      (trialTranslate b (blockX n d v) (blockY (contactSign plus) (trialWindow M R s) v) M R s j)) :
      |transverse b q-blockY (contactSign plus) (trialWindow M R s) v| ≤ trialWindow M R s/4 := by
    apply trial_strip_in_window b (blockX n d v)
      (blockY (contactSign plus) (trialWindow M R s) v) M R s j hR hs q
    convert hq.2.2 using 1
    simp [transverse]
    congr 1
    ring
  refine ⟨p,ds,⟨hp,hw p ?_⟩,⟨hq,hw _ (pathIn_endpoint _ _ _ hin)⟩,hcost⟩
  simpa using hin 0 (by omega)

theorem sourceSupportCost_of_endpoint (μ : Plane → ℝ) (b ε s : ℝ) (plus : Bool)
    (p q : Vertex) (ds : List Step) (hd : p+displacement ds=q) :
    sourceSupportCost μ b plus ε s p q =
      support b (μ (direction b)) (extremeSlope μ b plus) (displacement ds)+ε*s/2 := by
  have he : q-p=displacement ds := by rw [← hd]; abel
  simp [sourceSupportCost,he,support,transverse,latticeEmbed]

theorem goodSite_connector_witness (μ : Plane → ℝ) (b A R ε s : ℝ) (plus : Bool)
    (n d : ℤ) (M : ℕ) (v v' : Vertex) (w : Edge → ℝ)
    (hg : w ∈ goodSiteEvent μ b A R ε s plus n d M v)
    (hstep : v'=v+(1,0) ∨ v'=v+(0,1))
    (p q : Vertex)
    (hp : p ∈ connectorWindow b (blockX n d v+n)
      (blockY (contactSign plus) (trialWindow M R s) v) (trialWindow M R s))
    (hq : q ∈ connectorWindow b (blockX n d v')
      (blockY (contactSign plus) (trialWindow M R s) v') (trialWindow M R s)) :
    ∃ ds, p+displacement ds=q ∧
      defect w b (μ (direction b)) (extremeSlope μ b plus) p ds ≤ ε*s/2 := by
  have htest (a : ℝ) (hc : w ∈ siteConnector μ b R ε s plus n d M v a)
      (hX : blockX n d v'=blockX n d v+n+d)
      (hY : blockY (contactSign plus) (trialWindow M R s) v'=
        blockY (contactSign plus) (trialWindow M R s) v+contactSign plus*a*trialWindow M R s) :
      ∃ ds, p+displacement ds=q ∧
        defect w b (μ (direction b)) (extremeSlope μ b plus) p ds ≤ ε*s/2 := by
    have hq' := hq
    rw [hX,hY] at hq'
    obtain ⟨ds,hd,_,hcost⟩ := (mem_allPairsRegionEvent _ _ _ _ w).mp hc p hp q hq'
    refine ⟨ds,hd,?_⟩
    rw [sourceSupportCost_of_endpoint μ b ε s plus p q ds hd] at hcost
    unfold defect
    linarith
  rcases hstep with rfl | rfl
  · apply htest 1 hg.2.1
    · simp [blockX,blockLayer]; ring
    · simp [blockY,blockLevel]; ring
  · apply htest 2 hg.2.2
    · simp [blockX,blockLayer]; ring
    · simp [blockY,blockLevel]; ring

theorem UniformShape.no_goodSite_path (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (b A R ε s : ℝ) (plus : Bool) (n d : ℤ) (M : ℕ)
    (hb : |b| ≤ 1) (hR : 0 ≤ R) (hε : 0 < ε) (hs : 1 ≤ s)
    (hn : 0 < n) (hd : 0 ≤ d) (hM : 0 < M)
    (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e) (hu : UniformShape w μ) :
    ¬infiniteOrientedPath (fun v => w ∈ goodSiteEvent μ b A R ε s plus n d M v) 0 := by
  rintro ⟨v,hv0,hstep,hgood⟩
  choose p trial hp hz ht using (fun t =>
    goodSite_trial_witness μ b A R ε s plus n d M (v t) w hR hs (hgood t))
  let z := fun t => p t+displacement (trial t)
  choose connector hc hcost using (fun t =>
    goodSite_connector_witness μ b A R ε s plus n d M (v t) (v (t+1)) w
      (hgood t) (hstep t) (z t) (p (t+1)) (hz t) (hp (t+1)))
  obtain ⟨initialPath,hinit⟩ := exists_path 0 (p 0)
  have hS : 0 < trialWindow M R s := by
    have := (trialWindow_scale_bounds M hM R s hR hs).1
    linarith
  obtain ⟨hescape,hbound⟩ := crossing_endpoints_escape_linear b (contactSign plus)
    (trialWindow M R s) n d hb (abs_contactSign plus) hS hn hd v z hv0 hstep
    (fun t => (hz t).1) (fun t => (hz t).2)
  have hf : ∀ u : Plane, μ (direction b)*u 0+extremeSlope μ b plus*(u 1-b*u 0) ≤ μ u := by
    have hh := planar_extreme_supports μ hμ b
    cases plus
    · exact hh.1
    · exact hh.2.1
  apply hu.no_crossing_chain w hw μ b (μ (direction b)) (extremeSlope μ b plus) (ε*s)
    (2*((n : ℝ)+d)+3*trialWindow M R s) (by positivity) (by
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hd' : (0 : ℝ) ≤ d := by exact_mod_cast hd
      positivity) hf initialPath trial connector p z (by simpa using hinit)
    (fun _ => rfl) hc (fun t => by have := (ht t).le; linarith) hcost hescape hbound

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem exponential_goodSite_path_probability_zero_oai (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b A R ε s : ℝ) (plus : Bool) (n d : ℤ) (M : ℕ)
    (hb : |b| ≤ 1) (hR : 0 ≤ R) (hε : 0 < ε) (hs : 1 ≤ s)
    (hn : 0 < n) (hd : 0 ≤ d) (hM : 0 < M) :
    P {ω | infiniteOrientedPath (fun v => (fun e => τ e ω) ∈
      goodSiteEvent μ b A R ε s plus n d M v) 0}=0 := by
  have hh : ∀ᵐ ω ∂P, ¬infiniteOrientedPath (fun v => (fun e => τ e ω) ∈
      goodSiteEvent μ b A R ε s plus n d M v) 0 := by
    filter_upwards [h.ae_positive,exponential_uniform_shape h μ hμ ht] with ω hw hu
    exact hu.no_goodSite_path μ hμ b A R ε s plus n d M hb hR hε hs hn hd hM
      (fun e => τ e ω) (fun e => (hw e).le)
  simpa only [ae_iff,not_not] using hh

end PlanarFPP

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PlanarFPP.exponential_goodSite_path_probability_zero_oai.{u_1} := @OAI.PlanarFPP.exponential_goodSite_path_probability_zero_oai.{u_1}
