-- Prove2me | solution 1 for GlobalTheory.HL.CongFin.conj_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:50:30.117293+00:00
-- url     : https://prove2.me/submissions/89d7f9ac-cceb-46a8-b00d-ad446c4824cd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPowSmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruenceSubgroupLatticeStabilizer
import Theorems.Thm_GlobalTheory_HL_CongFin_conj_mem
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CongFin
variable {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] {O : Subring E}
namespace GlobalTheory.HL.CongFin
theorem _root_.solution (Λ : Submodule O V) (c : E) {a : V ≃ₗ[E] V}
    (ha : a ∈ MulAction.stabilizer (V ≃ₗ[E] V) Λ) :
    MulAut.conj a • congSub Λ c = congSub Λ c := by
  ext g
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  have e : (MulAut.conj a)⁻¹ • g = a⁻¹ * g * a⁻¹⁻¹ := by simp
  rw [e]
  constructor
  · intro h
    have := conj_mem Λ c ha h
    simpa [mul_assoc] using this
  · exact conj_mem Λ c (inv_mem ha)
end GlobalTheory.HL.CongFin
