-- Prove2me | solution 1 for GlobalTheory.MassFibre.wt_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:41:13.045093+00:00
-- url     : https://prove2.me/submissions/c741cfe3-39ef-4489-8344-05d16ac67d3d

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitMassEquivariantConstantFibre
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.MassFibre
open MulAction
namespace GlobalTheory.MassFibre
theorem _root_.solution {G : Type} [Group G] (Γ : Subgroup G) {Y : Type} [MulAction G Y] (γ : G)
    (hγ : γ ∈ Γ) (y : Y) : wt Γ (γ • y) = wt Γ y := by
  unfold wt
  congr 2
  have hset : ((Γ ⊓ MulAction.stabilizer G (γ • y) : Subgroup G) : Set G)
      = (fun h => γ * h * γ⁻¹) '' ((Γ ⊓ MulAction.stabilizer G y : Subgroup G) : Set G) := by
    ext x
    simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, MulAction.mem_stabilizer_iff,
      Set.mem_image]
    constructor
    · rintro ⟨hx1, hx2⟩
      refine ⟨γ⁻¹ * x * γ, ⟨?_, ?_⟩, by group⟩
      · exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) hx1) hγ
      · rw [mul_smul, mul_smul, hx2, inv_smul_smul]
    · rintro ⟨h, ⟨hh1, hh2⟩, rfl⟩
      refine ⟨Γ.mul_mem (Γ.mul_mem hγ hh1) (Γ.inv_mem hγ), ?_⟩
      rw [mul_smul, mul_smul, inv_smul_smul, hh2]
  rw [hset, Function.Injective.encard_image]
  intro a b hab
  simpa using hab
end GlobalTheory.MassFibre
