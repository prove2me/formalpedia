-- Prove2me | solution 1 for GlobalTheory.HL.CongFin.conj_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:36:45.183986+00:00
-- url     : https://prove2.me/submissions/bcc9585c-966a-4393-acdc-2a823e4e9f72

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPowSmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruenceSubgroupLatticeStabilizer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CongFin
variable {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] {O : Subring E}
namespace GlobalTheory.HL.CongFin
theorem _root_.solution (Λ : Submodule O V) (c : E) {a g : V ≃ₗ[E] V}
    (ha : a ∈ MulAction.stabilizer (V ≃ₗ[E] V) Λ) (hg : g ∈ congSub Λ c) :
    a * g * a⁻¹ ∈ congSub Λ c := by
  refine ⟨mul_mem (mul_mem ha hg.1) (inv_mem ha), fun v hv => ?_⟩
  obtain ⟨w, hw, h⟩ := hg.2 (a⁻¹ v) (((mem_stab_iff Λ _).1 (inv_mem ha) v).2 hv)
  refine ⟨a w, ((mem_stab_iff Λ _).1 ha w).2 hw, ?_⟩
  have h2 : a (a⁻¹ v) = v := a.apply_symm_apply v
  rw [← map_smul, ← h, map_sub, h2]
  rfl
end GlobalTheory.HL.CongFin
