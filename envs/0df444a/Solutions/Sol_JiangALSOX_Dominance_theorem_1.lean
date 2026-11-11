-- Prove2me | solution 1 for JiangALSOX.Dominance.theorem_1
-- status  : ACCEPTED   (disprove)
-- author  : @vibe-prover
-- created : 2026-11-10T13:50:44.167457+00:00
-- url     : https://prove2.me/submissions/8f227c66-3877-40a3-9601-84e00b5258a5

import Definitions.Def_JiangALSOX_Dominance_Programs
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace P076Counterexample

open JiangALSOX.Dominance

abbrev Ω := (Set.univ : Set (Fin 1 → ℝ))

def atom0 : Ω := ⟨0, Set.mem_univ _⟩
def atom1 : Ω := ⟨1, Set.mem_univ _⟩

def law : Measure Ω :=
  ENNReal.ofReal (1 / 4 : ℝ) • Measure.dirac atom0 +
    ENNReal.ofReal (3 / 4 : ℝ) • Measure.dirac atom1

def decisionSet : Set (Fin 2 → ℝ) :=
  {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ ∀ q : ℝ, 2 * q ≤ x 0 + q ^ 2 * x 1}

def randomLoss (x : Fin 2 → ℝ) (ω : Ω) : ℝ :=
  if ω.1 0 = 0 then x 1 else -x 1

def slack (v : ℝ) (ω : Ω) : ℝ :=
  if ω.1 0 = 0 then v else 0

def data : Model 2 1 0 where
  Ξ := Set.univ
  P := law
  gi := fun _ => randomLoss
  X := decisionSet
  C := ConvexCone.positive ℝ (Fin 2 → ℝ)
  c := 0
  ε := 1 / 2

lemma law_ae (p : Ω → Prop) : (∀ᵐ ω ∂law, p ω) ↔ p atom0 ∧ p atom1 := by
  have h0 : ENNReal.ofReal (1 / 4 : ℝ) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by norm_num)
  have h1 : ENNReal.ofReal (3 / 4 : ℝ) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by norm_num)
  simp only [law, ae_add_measure_iff, Measure.ae_ennreal_smul_measure_iff h0,
    Measure.ae_ennreal_smul_measure_iff h1, ae_dirac_eq, Filter.eventually_pure]

lemma law_probability : IsProbabilityMeasure law := by
  constructor
  simp only [law, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

lemma measurable_branch : MeasurableSet {ω : Ω | ω.1 0 = 0} := by
  exact measurableSet_eq_fun (measurable_pi_apply 0 |>.comp measurable_subtype_coe)
    measurable_const

lemma measurable_randomLoss (x : Fin 2 → ℝ) : Measurable (randomLoss x) := by
  exact Measurable.ite measurable_branch measurable_const measurable_const

lemma measurable_slack (v : ℝ) : Measurable (slack v) := by
  exact Measurable.ite measurable_branch measurable_const measurable_const

@[simp] lemma randomLoss_atom0 (x : Fin 2 → ℝ) : randomLoss x atom0 = x 1 := by
  simp [randomLoss, atom0]

@[simp] lemma randomLoss_atom1 (x : Fin 2 → ℝ) : randomLoss x atom1 = -x 1 := by
  simp [randomLoss, atom1]

@[simp] lemma slack_atom0 (v : ℝ) : slack v atom0 = v := by
  simp [slack, atom0]

@[simp] lemma slack_atom1 (v : ℝ) : slack v atom1 = 0 := by
  simp [slack, atom1]

@[simp] lemma data_loss (x : Fin 2 → ℝ) (ω : Ω) : loss data x ω = randomLoss x ω := by
  simp [loss, data]

lemma decisionSet_pos {x : Fin 2 → ℝ} (hx : x ∈ decisionSet) : 0 < x 1 := by
  rcases hx with ⟨h0, h1, hq⟩
  apply lt_of_le_of_ne h1
  intro heq
  have h := hq (x 0 + 1)
  rw [← heq] at h
  nlinarith

lemma decisionSet_one : (1 : Fin 2 → ℝ) ∈ decisionSet := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro q
  dsimp
  nlinarith [sq_nonneg (q - 1)]

lemma decisionSet_closed : IsClosed decisionSet := by
  apply IsClosed.inter (isClosed_le continuous_const (continuous_apply 0))
  apply IsClosed.inter (isClosed_le continuous_const (continuous_apply 1))
  have h := isClosed_iInter fun q : ℝ =>
    isClosed_le (continuous_const : Continuous (fun _ : Fin 2 → ℝ => 2 * q))
      ((continuous_apply 0).add
        ((continuous_const : Continuous (fun _ : Fin 2 → ℝ => q ^ 2)).mul (continuous_apply 1)))
  rw [Set.iInter_ofPred] at h
  simpa only [Set.ofPred, Pi.add_apply, Pi.mul_apply] using h

lemma decisionSet_convex : Convex ℝ decisionSet := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hx0, hx1, hxq⟩
  rcases hy with ⟨hy0, hy1, hyq⟩
  simp only [decisionSet, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨by positivity, by positivity, ?_⟩
  intro q
  have h1 := mul_le_mul_of_nonneg_left (hxq q) ha
  have h2 := mul_le_mul_of_nonneg_left (hyq q) hb
  have habq : 2 * q * (a + b) = 2 * q := by rw [hab, mul_one]
  nlinarith [add_le_add h1 h2, habq]

def improve (x : Fin 2 → ℝ) : Fin 2 → ℝ := ![2 * x 0, x 1 / 2]

lemma improve_mem {x : Fin 2 → ℝ} (hx : x ∈ decisionSet) : improve x ∈ decisionSet := by
  rcases hx with ⟨h0, h1, hq⟩
  refine ⟨by dsimp [improve]; positivity, by dsimp [improve]; positivity, ?_⟩
  intro q
  have h := hq (q / 2)
  dsimp [improve]
  nlinarith

lemma assumptions : Assumptions data := by
  refine ⟨law_probability, by norm_num [data], by norm_num [data], ?_, ?_,
    ⟨1, decisionSet_one⟩, decisionSet_closed, decisionSet_convex, ?_, ?_, ?_⟩
  · intro i x
    exact measurable_randomLoss x
  · apply Filter.Eventually.of_forall
    intro ω i
    change ConvexOn ℝ Set.univ (fun x => randomLoss x ω) ∧
      LowerSemicontinuous (fun x => randomLoss x ω)
    by_cases hω : ω.1 0 = 0
    · simp only [randomLoss, if_pos hω]
      refine ⟨⟨convex_univ, ?_⟩, (continuous_apply 1).lowerSemicontinuous⟩
      intro x hx y hy a b ha hb hab
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact le_rfl
    · simp only [randomLoss, if_neg hω]
      refine ⟨⟨convex_univ, ?_⟩, (continuous_apply 1).neg.lowerSemicontinuous⟩
      intro x hx y hy a b ha hb hab
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
  · intro x hx
    change 0 ≤ x
    intro i
    fin_cases i
    · exact hx.1
    · exact hx.2.1
  · exact isClosed_Ici
  · intro x hx hn
    apply le_antisymm
    · simpa using neg_nonneg.mp hn
    · exact hx

lemma positiveExpectation_eq (f : Ω → ℝ) :
    positiveExpectation law f =
      ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (f atom0) +
        ENNReal.ofReal (3 / 4 : ℝ) * ENNReal.ofReal (f atom1) := by
  simp [positiveExpectation, law, lintegral_add_measure, lintegral_smul_measure,
    lintegral_dirac]

lemma expectation_real (f : Ω → ℝ) (h0 : 0 ≤ f atom0) (h1 : 0 ≤ f atom1) :
    (positiveExpectation law f).toEReal =
      (((1 / 4 : ℝ) * f atom0 + (3 / 4 : ℝ) * f atom1 : ℝ) : EReal) := by
  have heq : positiveExpectation law f =
      ENNReal.ofReal ((1 / 4 : ℝ) * f atom0 + (3 / 4 : ℝ) * f atom1) := by
    rw [positiveExpectation_eq, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3 / 4)]
  rw [heq]
  change ((ENNReal.ofReal ((1 / 4 : ℝ) * f atom0 + (3 / 4 : ℝ) * f atom1) : EReal)) = _
  rw [EReal.coe_ennreal_ofReal, max_eq_left]
  positivity

lemma no_hinge_optimal (t : ℝ) (x : Fin 2 → ℝ) (s : Ω → ℝ) :
    ¬ hingeOptimal data t x s := by
  intro h
  rcases h.1 with ⟨hx, ht, hs, hae⟩
  have hp : 0 < x 1 := decisionSet_pos hx
  have ha : (0 ≤ s atom0 ∧ x 1 ≤ s atom0) ∧
      (0 ≤ s atom1 ∧ -x 1 ≤ s atom1) := by
    simpa only [data_loss, randomLoss_atom0, randomLoss_atom1] using
      (law_ae (fun ω => 0 ≤ s ω ∧ loss data x ω ≤ s ω)).mp hae
  have hnew : hingeFeasible data t (improve x) (slack (x 1 / 2)) := by
    refine ⟨improve_mem hx, ?_, measurable_slack _, ?_⟩
    · simpa [data, dotProduct] using ht
    · apply (law_ae _).mpr
      simp only [data_loss, randomLoss_atom0, randomLoss_atom1, slack_atom0, slack_atom1]
      dsimp [improve]
      constructor <;> constructor <;> linarith
  have hmin := h.2 (improve x) (slack (x 1 / 2)) hnew
  change (positiveExpectation law s).toEReal ≤
    (positiveExpectation law (slack (x 1 / 2))).toEReal at hmin
  rw [expectation_real s ha.1.1 ha.2.1,
    expectation_real (slack (x 1 / 2)) (by simp; positivity) (by simp)] at hmin
  simp only [slack_atom0, slack_atom1, mul_zero, add_zero, EReal.coe_le_coe_iff] at hmin
  linarith [ha.1.2, ha.2.1]

lemma alsoBudgets_empty : alsoBudgets data = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro t ht
  rcases ht with ⟨x, s, hs, hz⟩
  exact no_hinge_optimal t x s hs

lemma alsoValue_top : alsoValue data = ⊤ := by
  simp [alsoValue, alsoBudgets_empty]

lemma cvar_objective_nonneg (t : ℝ) (x : Fin 2 → ℝ) (s : Ω → ℝ) (β : ℝ)
    (h : cvarFeasible data t x s β) : 0 ≤ cvarObjective data s β := by
  rcases h with ⟨hx, ht, hβ, hs, hae⟩
  have ha : (β ≤ s atom0 ∧ x 1 ≤ s atom0) ∧
      (β ≤ s atom1 ∧ -x 1 ≤ s atom1) := by
    simpa only [data_loss, randomLoss_atom0, randomLoss_atom1] using
      (law_ae (fun ω => β ≤ s ω ∧ loss data x ω ≤ s ω)).mp hae
  change (0 : EReal) ≤ (((1 / 2 : ℝ) * β : ℝ) : EReal) +
    (positiveExpectation law (fun ω => s ω - β)).toEReal
  rw [expectation_real (fun ω => s ω - β) (sub_nonneg.mpr ha.1.1)
    (sub_nonneg.mpr ha.2.1), ← EReal.coe_add]
  apply EReal.coe_nonneg.mpr
  linarith [ha.1.2, ha.2.2, ha.2.1]

lemma cvar_witness_feasible :
    cvarFeasible data 0 (1 : Fin 2 → ℝ) (randomLoss 1) (-1) := by
  refine ⟨decisionSet_one, by simp [data, dotProduct], by norm_num,
    measurable_randomLoss _, ?_⟩
  apply (law_ae _).mpr
  simp only [data_loss, randomLoss_atom0, randomLoss_atom1, Pi.one_apply]
  norm_num

lemma cvar_witness_objective : cvarObjective data (randomLoss 1) (-1) = 0 := by
  change (((1 / 2 : ℝ) * (-1) : ℝ) : EReal) +
    (positiveExpectation law (fun ω => randomLoss 1 ω - (-1))).toEReal = 0
  rw [expectation_real _ (by simp) (by simp)]
  simp only [randomLoss_atom0, randomLoss_atom1, Pi.one_apply]
  rw [← EReal.coe_add]
  norm_num

lemma zero_cvarBudget : 0 ∈ cvarBudgets data := by
  refine ⟨1, randomLoss 1, -1, ⟨cvar_witness_feasible, ?_⟩, ?_⟩
  · intro y r b hfeas
    rw [cvar_witness_objective]
    exact cvar_objective_nonneg 0 y r b hfeas
  · rw [cvar_witness_objective]

lemma cvarValue_le_zero : cvarValue data ≤ 0 := by
  apply sInf_le
  exact ⟨0, zero_cvarBudget, by simp⟩

theorem root_false : ¬ (∀ {n m I : ℕ} (D : Model n m I), Assumptions D →
    alsoValue D ≤ cvarValue D) := by
  intro h
  have hbad := h data assumptions
  rw [alsoValue_top] at hbad
  have hcontra : (⊤ : EReal) ≤ 0 := hbad.trans cvarValue_le_zero
  simp at hcontra

end P076Counterexample

open JiangALSOX.Dominance

theorem solution : ¬ (∀ {n m I : ℕ} (D : Model n m I), Assumptions D →
    alsoValue D ≤ cvarValue D) := P076Counterexample.root_false

#print axioms solution
