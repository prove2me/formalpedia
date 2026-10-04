-- Prove2me | solution 1 for MDPFinance.StructuredModels.monotone_maximizer_supermodular
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T00:05:09.462024+00:00
-- url     : https://prove2.me/submissions/e2d75f71-0b6f-4cdf-a8a8-a88203cd5750

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_BoundingFunction
import Definitions.Def_MDPFinance_StructuredModels_Model
import Definitions.Def_MDPFinance_StructuredModels_Policy
import Definitions.Def_MDPFinance_StructuredModels_Operators
import Definitions.Def_MDPFinance_StructuredModels_CompletelyMonotone
import Definitions.Def_MDPFinance_StructuredModels_Supermodular

open MeasureTheory ProbabilityTheory

namespace Cex76fc

open MDPFinance.StructuredModels

/-- Two states, two actions, all pairs admissible, zero rewards; the next state is
`x && !a` deterministically. -/
noncomputable def M : MarkovDecisionModel Bool Bool 1 where
  D := fun _ => Set.univ
  hD_meas := fun _ _ => MeasurableSet.univ
  hD_sel := fun _ _ => ⟨fun _ => false, measurable_const, fun _ => Set.mem_univ _⟩
  Q := fun _ => Kernel.deterministic (fun xa : Bool × Bool => xa.1 && !xa.2)
    (measurable_of_countable _)
  hQ_prob := fun _ _ xa =>
    (inferInstance : IsMarkovKernel (Kernel.deterministic (fun xa : Bool × Bool => xa.1 && !xa.2)
      (measurable_of_countable _))).isProbabilityMeasure xa
  r := fun _ _ => 0
  hr_meas := fun _ _ => measurable_const
  g := fun _ => 0
  hg_meas := measurable_const

/-- `v true = 0`, `v false = ⊥`. -/
noncomputable def v : Bool → EReal := fun e => if e then 0 else ⊥

def fstar : Bool → Bool := fun x => !x

theorem integ_dirac (y : Bool) : erealIntegral (Measure.dirac y) v = v y := by
  unfold erealIntegral
  rw [lintegral_dirac, lintegral_dirac]
  cases y <;> simp [v]

theorem hL (xa : Bool × Bool) : L M 0 v xa = v (xa.1 && !xa.2) := by
  unfold L
  simp only [M, Kernel.deterministic_apply, integ_dirac]
  simp

theorem hT_false : T M 0 v false = ⊥ := by
  unfold T
  simp only [MarkovDecisionModel.Dx, hL]
  simp [v]

theorem hT_true : T M 0 v true = 0 := by
  unfold T
  simp only [MarkovDecisionModel.Dx, hL]
  apply le_antisymm
  · refine iSup₂_le fun a _ => ?_
    cases a <;> simp [v]
  · refine le_trans ?_ (le_iSup₂ (f := fun a (_ : a ∈ {a | (true, a) ∈ M.D 0}) =>
      v ((true, a).1 && !(true, a).2)) false (by simp [M]))
    simp [v]

theorem hb : IsUpperBoundingFunction M (fun _ => 0) 0 0 0 where
  hb_meas := measurable_const
  hb_nonneg := fun _ => le_rfl
  hcr := le_rfl
  hcg := le_rfl
  hαb := le_rfl
  hr := fun _ _ _ _ => by simp [M]
  hg := fun _ => by simp [M]
  hQ := fun _ _ _ _ => by simp

theorem hv : v ∈ IBbPlus (fun _ : Bool => (0 : ℝ)) := by
  refine ⟨measurable_of_countable _, ?_, 0, le_rfl, ?_⟩
  · intro x; cases x <;> simp [v]
  · intro x; cases x <;> simp [v]

theorem hCM : CompletelyMonotone (M.D 0) := by
  intro x x' a a' _ _ _ _
  exact ⟨Set.mem_univ _, Set.mem_univ _⟩

theorem hSM : SupermodularOn (M.D 0) (L M 0 v) := by
  rintro ⟨x, a⟩ - ⟨y, b⟩ -
  simp only [hL, Prod.mk_inf_mk, Prod.mk_sup_mk]
  cases x <;> cases a <;> cases y <;> cases b <;> simp [v]

theorem hmax : IsMaximizer M 0 v fstar := by
  refine ⟨⟨measurable_of_countable _, fun _ => Set.mem_univ _⟩, ?_⟩
  funext x
  cases x
  · rw [hT_false]; simp [Tf, hL, fstar, v]
  · rw [hT_true]; simp [Tf, hL, fstar, v]

theorem hlargest : ∀ x : Bool, ∀ a ∈ {a ∈ M.Dx 0 x | L M 0 v (x, a) = T M 0 v x},
    (fstar x ≤ a ∨ a ≤ fstar x) → a ≤ fstar x := by
  intro x a ha _
  cases x
  · simp [fstar]
  · obtain ⟨-, h⟩ := ha
    rw [hL, hT_true] at h
    cases a
    · exact le_rfl
    · simp [v] at h

end Cex76fc

theorem solution : ¬ (∀ {E A : Type} [MeasurableSpace E] [MeasurableSpace A]
    [Lattice E] [Lattice A] {N : ℕ} (M : MDPFinance.StructuredModels.MarkovDecisionModel E A N)
    (b : E → ℝ) (cr cg αb : ℝ)
    (hb : MDPFinance.StructuredModels.IsUpperBoundingFunction M b cr cg αb) (n : ℕ) (hn : n < N)
    (v : E → EReal) (hv : v ∈ MDPFinance.StructuredModels.IBbPlus b)
    (hCM : MDPFinance.StructuredModels.CompletelyMonotone (M.D n))
    (hSM : MDPFinance.StructuredModels.SupermodularOn (M.D n) (MDPFinance.StructuredModels.L M n v))
    (fstar : E → A)
    (hfstar : MDPFinance.StructuredModels.IsMaximizer M n v fstar)
    (hfstar_largest : ∀ x : E, ∀ a ∈ {a ∈ M.Dx n x |
        MDPFinance.StructuredModels.L M n v (x, a) = MDPFinance.StructuredModels.T M n v x},
      (fstar x ≤ a ∨ a ≤ fstar x) → a ≤ fstar x),
    ∀ x x' : E, x ≤ x' → (fstar x ≤ fstar x' ∨ fstar x' ≤ fstar x) → fstar x ≤ fstar x') := by
  intro H
  have h := H Cex76fc.M (fun _ => 0) 0 0 0 Cex76fc.hb 0 Nat.one_pos Cex76fc.v Cex76fc.hv
    Cex76fc.hCM Cex76fc.hSM Cex76fc.fstar Cex76fc.hmax Cex76fc.hlargest false true
    (by decide) (Or.inr (by decide))
  exact absurd h (by decide)
