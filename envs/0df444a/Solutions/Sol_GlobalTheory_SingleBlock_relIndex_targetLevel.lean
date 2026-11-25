-- Prove2me | solution 1 for GlobalTheory.SingleBlock.relIndex_targetLevel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:17:17.968133+00:00
-- url     : https://prove2.me/submissions/1252dbde-f6ad-4cfe-a31f-253ecf49922a

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FromBlocksMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
import Theorems.Thm_GlobalTheory_SingleBlock_map_subtype_injective
import Theorems.Thm_GlobalTheory_SingleBlock_map_residue_surj
import Theorems.Thm_GlobalTheory_SingleBlock_targetLevel_eq

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
    (targetLevel t 𝒪[F] (ϖ : F) P).relIndex (glInt 𝒪[F] (Fin r ⊕ Fin t)) =
      (blockPar t (residueImage P)).index := by
  unfold glInt
  rw [targetLevel_eq hϖ hP, MonoidHom.range_eq_map,
    Subgroup.relIndex_map_map_of_injective _ _ (map_subtype_injective _ _),
    Subgroup.relIndex_top_right, Subgroup.index_comap_of_surjective _ (map_residue_surj _ _)]
end GlobalTheory.SingleBlock
