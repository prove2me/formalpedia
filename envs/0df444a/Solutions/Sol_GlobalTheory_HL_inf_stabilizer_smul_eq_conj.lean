-- Prove2me | solution 1 for GlobalTheory.HL.inf_stabilizer_smul_eq_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:41:18.09996+00:00
-- url     : https://prove2.me/submissions/fc279890-e8ee-4ae9-8ade-a8490b47a29f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StabilizerCommensurableInvVolumeSmulComplementStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InfStabilizerSmulEqConj
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
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL
namespace GlobalTheory.HL
theorem _root_.solution {G X : Type*} [Group G] [MulAction G X] (H : Subgroup G)
    {h : G} (hh : h ∈ H) (x : X) :
    H ⊓ MulAction.stabilizer G (h • x) = MulAut.conj h • (H ⊓ MulAction.stabilizer G x) := by
  ext g
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAut.smul_def, MulAut.conj_inv_apply]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨H.mul_mem (H.mul_mem (H.inv_mem hh) h1) hh, ?_⟩
    rw [mul_smul, mul_smul, h2, inv_smul_smul]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := H.mul_mem (H.mul_mem hh h1) (H.inv_mem hh)
      simpa [mul_assoc] using this
    · rw [mul_smul, mul_smul, inv_smul_eq_iff] at h2
      exact h2
end GlobalTheory.HL
