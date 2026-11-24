-- Prove2me | solution 1 for GlobalTheory.FlatFactor.KerEngine.sum_single_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:40:10.339432+00:00
-- url     : https://prove2.me/submissions/9bcd3aec-3156-47f6-9981-dc5485d6aa02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatLinearFunctional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearMapKillsPartialEvalIntegralKernelOfLaws
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.FlatFactor GlobalTheory.FlatFactor.KerEngine
open GlobalTheory.FlatFactor
variable {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
namespace GlobalTheory.FlatFactor.KerEngine
theorem _root_.solution (it : Finset (m × m')) (a : m × m' → k) (r : m) (q : m') :
    (∑ e ∈ it, Matrix.single e.1 e.2 (a e)) r q = if (r, q) ∈ it then a (r, q) else 0 := by
  rw [Matrix.sum_apply]
  have : ∀ e : m × m', Matrix.single e.1 e.2 (a e) r q = if (r, q) = e then a e else 0 := by
    rintro ⟨x, y⟩
    simp only [Matrix.single_apply, Prod.mk.injEq]
    split_ifs <;> aesop
  simp_rw [this, Finset.sum_ite_eq]
end GlobalTheory.FlatFactor.KerEngine
