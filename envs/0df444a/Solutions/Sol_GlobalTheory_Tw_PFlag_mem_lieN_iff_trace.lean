-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.mem_lieN_iff_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:58:05.703317+00:00
-- url     : https://prove2.me/submissions/99516b19-fd86-44c9-a375-ccb4efd7035e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
import Theorems.Thm_GlobalTheory_Tw_PFlag_isNilpotent_of_mem_lieN

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
open GlobalTheory.Tw.PFlag
variable {n : ℕ} {k : Type} [Field k] {F : PFlag n k}
namespace GlobalTheory.Tw.PFlag
theorem _root_.solution {X : Matrix (Fin n) (Fin n) k} : X ∈ F.lieN ↔ ∀ Y ∈ F.lieQ, (X * Y).trace = 0 := by
  refine ⟨fun hX Y hY => (isNilpotent_trace_of_isNilpotent (isNilpotent_of_mem_lieN (lieN_mul_lieQ hX hY))).eq_zero,
    fun h V hV v hv => ?_⟩
  by_contra hn
  obtain ⟨l, hl, hl0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  have hY : ∀ w, LinearMap.toMatrix' (l.smulRight v) *ᵥ w = l w • v := fun w => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl
  have h1 := h (LinearMap.toMatrix' (l.smulRight v)) fun V' hV' w hw => by
    rw [hY]
    rcases F.chain.total hV hV' with h' | h'
    · exact V'.smul_mem _ (h' hv)
    · rcases h'.eq_or_lt with rfl | h''
      · exact V'.smul_mem _ hv
      · have : l w = 0 := by
          have : l w ∈ (F.pred V).map l := ⟨w, F.le_pred hV' h'' hw, rfl⟩
          rwa [hl0, Submodule.mem_bot] at this
        simp [this]
  apply hl
  rw [← h1, ← Matrix.trace_toLin'_eq, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  have : Matrix.toLin' X ∘ₗ l.smulRight v = l.smulRight (X *ᵥ v) := by ext; simp
  rw [this, LinearMap.trace_smulRight]
end GlobalTheory.Tw.PFlag
