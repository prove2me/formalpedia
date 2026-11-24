-- Prove2me | solution 1 for GlobalTheory.LatOrb.matLat_stdLat_isLatV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:12:00.262764+00:00
-- url     : https://prove2.me/submissions/8ea1d588-2a45-4cf7-bc5c-74edb7f70961

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFullRankLatticeImageStandardLatticeGL
import Theorems.Thm_GlobalTheory_LatOrbIsLat_single_mem_stdLat
import Theorems.Thm_GlobalTheory_LatOrbIsLat_stdLat_fg
import Theorems.Thm_GlobalTheory_LatOrb_mem_matLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
open GlobalTheory.LatOrbIsLat
namespace GlobalTheory.LatOrb
theorem _root_.solution : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (g : GL (Fin n) K),
    IsLatV O (matLat O g.val (stdLat O n)) := by
  intro O K _ _ _ n g
  refine ⟨(stdLat_fg n).map _, ?_⟩
  rw [eq_top_iff]
  intro v _
  set w : Fin n → K := (g⁻¹ : GL (Fin n) K).val *ᵥ v with hw
  have hgw : g.val *ᵥ w = v := by
    rw [hw, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hw' : w = ∑ i, w i • (Pi.single i (1 : K) : Fin n → K) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hv : v = ∑ i, w i • Matrix.mulVecLin g.val (Pi.single i (1 : K)) := by
    simp only [← map_smul, ← map_sum, ← hw']
    rw [Matrix.mulVecLin_apply, hgw]
  rw [hv]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  show _ ∈ matLat O g.val (stdLat O n)
  rw [mem_matLat]
  exact ⟨_, single_mem_stdLat n i, rfl⟩
end GlobalTheory.LatOrb
