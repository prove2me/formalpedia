-- Prove2me | solution 1 for GlobalTheory.Cyc.IsActC.continuous_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:24:41.114727+00:00
-- url     : https://prove2.me/submissions/095badf5-218d-4aa1-b847-6aa576cf703f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOrbitPadicComplex
import Theorems.Thm_GlobalTheory_Cyc_eventually_apply_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc
namespace GlobalTheory.Cyc
namespace IsActC
theorem _root_.solution (l : ℕ) [Fact l.Prime]
    (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (h : IsActC act) (y : PadicComplex l) :
    Continuous (fun g => act g y) := by
  obtain ⟨hext, hiso⟩ := h
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨x, hx⟩ : ∃ x : Om l, dist y (x : PadicComplex l) < ε / 2 :=
    UniformSpace.Completion.denseRange_coe.exists_dist_lt y (half_pos hε)
  filter_upwards [eventually_apply_eq x g₀] with g hg
  have h1 : act g y - act g₀ y = act g (y - x) - act g₀ (y - x) := by
    rw [map_sub, map_sub, hext g x, hext g₀ x, hg]
    ring
  rw [dist_eq_norm, h1]
  calc ‖act g (y - x) - act g₀ (y - x)‖ ≤ ‖act g (y - x)‖ + ‖act g₀ (y - x)‖ := norm_sub_le _ _
    _ = 2 * ‖y - x‖ := by rw [hiso, hiso]; ring
    _ < ε := by rw [← dist_eq_norm]; linarith
end IsActC
end GlobalTheory.Cyc
