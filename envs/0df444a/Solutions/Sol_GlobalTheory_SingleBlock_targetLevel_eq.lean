-- Prove2me | solution 1 for GlobalTheory.SingleBlock.targetLevel_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:09:55.655916+00:00
-- url     : https://prove2.me/submissions/65dd3914-8679-40c6-89f9-feba3d5bb49d

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FromBlocksMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
import Theorems.Thm_GlobalTheory_SingleBlock_targetSet_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate ValuativeRel Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
open GlobalTheory GlobalTheory.SingleBlock
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {r t : ℕ} {ϖ : 𝒪[F]}
namespace GlobalTheory.SingleBlock
theorem _root_.solution (hϖ : Irreducible ϖ) {P : Subgroup (GL (Fin r) F)}
    (hP : P ≤ GLint 𝒪[F] r) :
    targetLevel t 𝒪[F] (ϖ : F) P =
      ((blockPar t (residueImage P)).comap
        (GeneralLinearGroup.map (n := Fin r ⊕ Fin t) (IsLocalRing.residue 𝒪[F]))).map
        (GeneralLinearGroup.map (n := Fin r ⊕ Fin t) (𝒪[F]).subtype) := by
  unfold targetLevel
  rw [targetSet_eq hϖ hP, Subgroup.closure_eq]
end GlobalTheory.SingleBlock
