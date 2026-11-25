-- Prove2me | solution 1 for GlobalTheory.HL.relIndex_stabilizer_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:40:32.183224+00:00
-- url     : https://prove2.me/submissions/bc9021b7-9fe9-4ac5-b13b-7a4b3262d181

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormOrbitSumLeOfSymmKernel
import Theorems.Thm_GlobalTheory_HL_ncard_stabilizer_orbit
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
open GlobalTheory GlobalTheory.HL
variable {G X : Type} [Group G] [MulAction G X] (St : Subgroup G)
namespace GlobalTheory.HL
theorem _root_.solution {g : G} (hg : g ∈ St) (y w : X) :
    (St ⊓ MulAction.stabilizer G (g • w)).relIndex (St ⊓ MulAction.stabilizer G (g • y)) =
      (St ⊓ MulAction.stabilizer G w).relIndex (St ⊓ MulAction.stabilizer G y) := by
  rw [← ncard_stabilizer_orbit, ← ncard_stabilizer_orbit,
    ← Set.ncard_image_of_injective {w' | ∃ h ∈ St, h • y = y ∧ h • w = w'} (MulAction.injective g)]
  congr 1
  ext w'
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨h, hh, h1, h2⟩
    refine ⟨_, ⟨g⁻¹ * h * g, St.mul_mem (St.mul_mem (St.inv_mem hg) hh) hg, ?_, rfl⟩, ?_⟩
    · rw [mul_smul, mul_smul, h1, inv_smul_smul]
    · rw [mul_smul, mul_smul, h2, smul_inv_smul]
  · rintro ⟨_, ⟨h, hh, h1, rfl⟩, rfl⟩
    refine ⟨g * h * g⁻¹, St.mul_mem (St.mul_mem hg hh) (St.inv_mem hg), ?_, ?_⟩
    · rw [mul_smul, mul_smul, inv_smul_smul, h1]
    · rw [mul_smul, mul_smul, inv_smul_smul]
end GlobalTheory.HL
