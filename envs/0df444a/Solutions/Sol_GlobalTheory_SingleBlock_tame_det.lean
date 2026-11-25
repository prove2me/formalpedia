-- Prove2me | solution 1 for GlobalTheory.SingleBlock.tame_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:09:56.529963+00:00
-- url     : https://prove2.me/submissions/08292e21-161f-4083-bbec-f9daf8061dbf

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FromBlocksMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
import Theorems.Thm_GlobalTheory_SingleBlock_le_range_of_le_GLint
import Theorems.Thm_GlobalTheory_SingleBlock_comap_congSub
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate ValuativeRel Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
open GlobalTheory GlobalTheory.SingleBlock
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {r t : ℕ} {ϖ : 𝒪[F]}
namespace GlobalTheory.SingleBlock
theorem _root_.solution (hϖ : Irreducible ϖ) {μ : Fˣ →* ℂˣ} (hμ : IsTame μ) {k : GL (Fin r) F}
    (hk : k ∈ congSub 𝒪[F] (ϖ : F) r) : μ (GeneralLinearGroup.det k) = 1 := by
  obtain ⟨g, rfl⟩ := le_range_of_le_GLint le_rfl hk.1
  have h1 : g ∈ (GeneralLinearGroup.map (n := Fin r) (IsLocalRing.residue 𝒪[F])).ker := by
    rw [← comap_congSub hϖ]; exact hk
  have h2 : (IsLocalRing.residue 𝒪[F]).mapMatrix (g : Matrix (Fin r) (Fin r) 𝒪[F]) = 1 :=
    congrArg Units.val (MonoidHom.mem_ker.1 h1)
  refine hμ _ ((g : Matrix (Fin r) (Fin r) 𝒪[F]).det - 1) ?_ ?_
  · rw [← IsLocalRing.residue_eq_zero_iff, map_sub, RingHom.map_det, h2, det_one, map_one, sub_self]
  · have : ((GeneralLinearGroup.det (GeneralLinearGroup.map (n := Fin r) (𝒪[F]).subtype g) : Fˣ) :
        F) = (𝒪[F]).subtype (g : Matrix (Fin r) (Fin r) 𝒪[F]).det := by
      rw [RingHom.map_det]; rfl
    rw [this]; simp
end GlobalTheory.SingleBlock
