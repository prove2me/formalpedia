-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.isHermitian_of_mem_realScalars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:34:41.459821+00:00
-- url     : https://prove2.me/submissions/b743126e-d1ce-4ac0-a27e-f68c76c4291a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
import Theorems.Thm_GlobalTheory_Tw_mulVec_dot_star
import Theorems.Thm_GlobalTheory_Tw_eq_zero_of_dot_star
import Theorems.Thm_GlobalTheory_Tw_PFlag_le_of_summand_le
import Theorems.Thm_GlobalTheory_Tw_PFlag_mem_lieQ_and_star_iff
import Theorems.Thm_GlobalTheory_Tw_PFlag_preserves_of_mem_realScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw
variable {n : ℕ}
open GlobalTheory.Tw.PFlag
variable {F : PFlag n ℂ}
namespace GlobalTheory.Tw.PFlag
theorem _root_.solution {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ F.realScalars) : X.IsHermitian := by
  have h0 := mem_lieQ_and_star_iff.2 (preserves_of_mem_realScalars hX)
  have h1 := (mem_lieQ_and_star_iff (X := Xᴴ)).1 ⟨h0.2, by simpa using h0.1⟩
  have h2 : ⊤ ≤ LinearMap.ker (Matrix.toLin' (Xᴴ - X)) := le_of_summand_le F.top_mem fun V hV _ v hv => by
    obtain ⟨c, hc⟩ := hX V hV
    have hd : (Xᴴ - X) *ᵥ v ∈ F.summand V := by
      rw [sub_mulVec]; exact sub_mem (h1 V hV v hv) (preserves_of_mem_realScalars hX V hV v hv)
    have h3 := hc _ hd
    rw [LinearMap.mem_ker, Matrix.toLin'_apply]
    set d := (Xᴴ - X) *ᵥ v with hdef
    have h4 : d ⬝ᵥ star d = 0 := by
      conv_lhs => enter [1]; rw [hdef]
      rw [sub_mulVec, sub_dotProduct, mulVec_dot_star, conjTranspose_conjTranspose, h3, hc v hv]
      simp
    exact eq_zero_of_dot_star h4
  rw [top_le_iff, LinearMap.ker_eq_top, map_eq_zero_iff _ Matrix.toLin'.injective, sub_eq_zero] at h2
  exact h2
end GlobalTheory.Tw.PFlag
