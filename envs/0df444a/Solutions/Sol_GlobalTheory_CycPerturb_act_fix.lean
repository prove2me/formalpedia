-- Prove2me | solution 1 for GlobalTheory.CycPerturb.act_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:15:51.155375+00:00
-- url     : https://prove2.me/submissions/e5bbbca6-06e8-4a26-a448-8db024833e5e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerGeneratorMatrixPerturbation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycPerturb
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.CycPerturb
theorem _root_.solution {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (hact : IsActC act)
    {K : FinExt l} {j : ℕ} {g : GQ l} (hg : g ∈ Gj K j) {y : PadicComplex l}
    (hy : y ∈ inC (Ks K j)) : act g y = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  have := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x hx
  change act g (x : PadicComplex l) = (x : PadicComplex l)
  rw [hact.1, this]
end GlobalTheory.CycPerturb
