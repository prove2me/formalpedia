-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52ArrivalMarkSequenceIndepV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:53:41.9168+00:00
-- url     : https://prove2.me/submissions/5a320116-dee9-402a-b090-7c1ccab637bb

import Mathlib
import Theorems.Thm_levy_foundations_iIndepFun_setRestrict_pairwiseDisjoint
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch05_RiskConditionalPassage
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set
open Kyprianou.Ch05
/-- Group independent coordinates into the two disjoint sequence blocks. -/
theorem solution
    {Lambda : Type} [MeasurableSpace Lambda] (Q : Measure Lambda)
    [IsProbabilityMeasure Q] (arrival marks : ℕ → Lambda → ℝ)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : LevyFoundations.IsCompoundPoissonDriver arrival marks 1 F Q) :
    IndepFun (fun w n => arrival n w) (fun w n => marks n w) Q := by
  let blk : Bool → Set (ℕ ⊕ ℕ) := fun b =>
    if b then Set.range Sum.inl else Set.range Sum.inr
  have hall : ∀ i : ℕ ⊕ ℕ, Measurable (Sum.elim arrival marks i) :=
    Sum.rec hd.measurable_interarrival hd.measurable_mark
  have hS : Pairwise (Function.onFun Disjoint blk) := by
    intro i j hij
    cases i <;> cases j <;> simp_all [blk, Function.onFun, Set.disjoint_left]
  have hgroup := levy_foundations_iIndepFun_setRestrict_pairwiseDisjoint hall hd.indep hS
  have hTT := hgroup.indepFun (by decide : true ≠ false)
  have hGτm : Measurable (fun (x : ↥(blk true) → ℝ) (i : ℕ) =>
      x ⟨Sum.inl i, (show Sum.inl i ∈ blk true from ⟨i,rfl⟩)⟩) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hGYm : Measurable (fun (x : ↥(blk false) → ℝ) (i : ℕ) =>
      x ⟨Sum.inr i, (show Sum.inr i ∈ blk false from ⟨i,rfl⟩)⟩) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  exact hTT.comp hGτm hGYm
