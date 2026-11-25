-- Prove2me | solution 1 for GlobalTheory.BasicFlow.dropLevelsBasic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:49:10.940688+00:00
-- url     : https://prove2.me/submissions/238e143e-96e7-403b-89d9-c153407c5bfb

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DropLevelsBasic
import Theorems.Thm_GlobalTheory_BasicFlow_basic
import Theorems.Thm_GlobalTheory_BasicFlow_entry_le
import Theorems.Thm_GlobalTheory_BasicFlow_low_optimum
import Theorems.Thm_GlobalTheory_BasicFlow_truncate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open GlobalTheory GlobalTheory.BasicFlow
namespace GlobalTheory.BasicFlow
theorem _root_.solution : DropLevelsBasic := by
  intro l d _ hl W hW i0
  obtain ⟨x, ⟨hx, hx0⟩, hmax⟩ := low_optimum l d hl W hW i0
  have hm : maxFlow l d W ≤ flowVal d x + (∑ a, W a) / (l : ℝ) ^ i0 := by
    refine csSup_le ⟨_, x, hx, rfl⟩ ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', h1, h2, h3⟩ := truncate l d hl W i0 z hz
    linarith [hmax z' h1 h2]
  let T : (ZMod d × ℕ → ℝ) →ₗ[ℝ] (ZMod d → ℝ) :=
    { toFun := fun v s => (∑ i ∈ oddLevels d, (l : ℝ) ^ i * v (s, i)) +
        (∑ i ∈ oddLevels d, v (s - (i : ZMod d), i))
      map_add' := fun v w => by
        ext s; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring
      map_smul' := fun c v => by
        ext s
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add, Finset.mul_sum,
          mul_left_comm c] }
  let φ : (ZMod d × ℕ → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => ∑ s : ZMod d, ∑ i ∈ oddLevels d, v (s, i)
      map_add' := fun v w => by simp only [Pi.add_apply, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum] }
  obtain ⟨y, h1, h2, h3, h4, h5⟩ := basic ((Finset.univ : Finset (ZMod d)) ×ˢ oddLevels d) T φ
    (fun v hv hv0 hT => by
      ext ⟨a, i⟩
      by_cases hi : i ∈ oddLevels d
      · refine le_antisymm ?_ (hv0 _)
        exact entry_le l d hl 0 (fun a i => v (a, i))
          ⟨fun a i => hv0 _, fun s => (congrFun hT s).le⟩ a i hi
      · exact hv _ (by simp [hi]))
    (fun p => x p.1 p.2) (fun p => hx.1 _ _)
    (fun p hp => hx0 _ _ (Or.inr (by simpa using hp)))
  refine ⟨fun a i => y (a, i), ⟨fun a i => h1 _, fun s => ?_⟩,
    fun a i h => h4 (a, i) (hx0 a i h), ?_, ?_⟩
  · exact (congrFun h2 s).le.trans (hx.2 s)
  · simpa [ZMod.card] using h5
  · have : flowVal d x ≤ flowVal d (fun a i => y (a, i)) := h3
    linarith
end GlobalTheory.BasicFlow
