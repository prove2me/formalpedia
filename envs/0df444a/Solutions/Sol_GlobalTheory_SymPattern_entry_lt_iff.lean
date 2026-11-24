-- Prove2me | solution 1 for GlobalTheory.SymPattern.entry_lt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:21:46.472112+00:00
-- url     : https://prove2.me/submissions/da082ffb-dfde-44f9-aedc-998d40d549b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
namespace GlobalTheory.SymPattern
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
section Field
variable {F : Type} [Field F] {κ l : ℕ}
end Field
section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem valuation_lt_one_iff_residue_eq_zero (y : 𝒪[k]) :
    valuation k (y : k) < 1 ↔ IsLocalRing.residue 𝒪[k] y = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.symm
end Local
end GlobalTheory.SymPattern
end
end

set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.SymPattern
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.SymPattern
theorem _root_.solution (g₀ : GL ι 𝒪[k]) (a b : ι) :
    valuation k ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₀).val a b - (1 : Matrix ι ι k) a b) < 1 ↔
      (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g₀).val a b = (1 : Matrix ι ι 𝓀[k]) a b := by
  have e1 : (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₀).val a b - (1 : Matrix ι ι k) a b =
      ((g₀.val a b - (1 : Matrix ι ι 𝒪[k]) a b : 𝒪[k]) : k) := by
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab] <;> rfl
  have e2 : (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g₀).val a b -
      (1 : Matrix ι ι 𝓀[k]) a b = IsLocalRing.residue 𝒪[k] (g₀.val a b - (1 : Matrix ι ι 𝒪[k]) a b) := by
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  rw [e1, valuation_lt_one_iff_residue_eq_zero, ← e2, sub_eq_zero]
end GlobalTheory.SymPattern
