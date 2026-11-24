-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.Vf2.rank_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:28:48.762114+00:00
-- url     : https://prove2.me/submissions/4b35c257-c62b-4766-b73c-5df35be82af6

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_ExistsPowIdem
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_SkewTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Vf2
open Matrix GlobalTheory.WeilM PositivityTheory.ThKG.Loc.Cone.Vf
variable {A K β : Type} [CommRing A] [Field K] [Fintype β] [DecidableEq β]
omit [DecidableEq β]
namespace GlobalTheory.ThK.Dbl.Vf2
theorem _root_.solution {M : Matrix β β K} {y w φ : β → K} (hy : M *ᵥ y = 0) (hw : w ∉ LinearMap.range M.mulVecLin) (hφ : φ ⬝ᵥ y ≠ 0) :
    M.rank < (M + vecMulVec w φ).rank := by
  have e : ∀ x, (M + vecMulVec w φ) *ᵥ x = M *ᵥ x + (φ ⬝ᵥ x) • w := fun x => by
    rw [add_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
  have h1 : w ∈ LinearMap.range (M + vecMulVec w φ).mulVecLin := ⟨(φ ⬝ᵥ y)⁻¹ • y, by
    rw [mulVecLin_apply, mulVec_smul, e, hy, zero_add, smul_smul, inv_mul_cancel₀ hφ, one_smul]⟩
  refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne ?_ fun h => hw (h ▸ h1))
  rintro _ ⟨x, rfl⟩
  rw [mulVecLin_apply, eq_sub_of_add_eq (e x).symm]
  exact sub_mem ⟨x, rfl⟩ (Submodule.smul_mem _ _ h1)
end GlobalTheory.ThK.Dbl.Vf2
