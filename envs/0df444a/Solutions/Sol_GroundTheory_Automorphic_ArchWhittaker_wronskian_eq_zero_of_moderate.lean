-- Prove2me | solution 1 for GroundTheory.Automorphic.ArchWhittaker.wronskian_eq_zero_of_moderate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:59:27.939542+00:00
-- url     : https://prove2.me/submissions/9402669c-8609-43b3-8b9c-a6aaf18f40d4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_WronskianEqZeroOfModerate
import Theorems.Thm_GroundTheory_Automorphic_ArchWhittaker_tendsto_zero_of_moderate
import Theorems.Thm_GroundTheory_Automorphic_ArchWhittaker_tendsto_deriv_zero
import Theorems.Thm_GroundTheory_Automorphic_ArchWhittaker_wronskian_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ArchWhittaker
open Filter Topology Set
namespace GroundTheory.Automorphic.ArchWhittaker
theorem _root_.solution {q f f' g g' : ℝ → ℂ} {c M Y₀ : ℝ} (hY₀ : 0 < Y₀)
    (hc : 0 < c) (hqre : ∀ y ≥ Y₀, c ^ 2 ≤ (q y).re) (hqM : ∀ y ≥ Y₀, ‖q y‖ ≤ M)
    (hf : ∀ y > 0, HasDerivAt f (f' y) y) (hf' : ∀ y > 0, HasDerivAt f' (q y * f y) y)
    (hg : ∀ y > 0, HasDerivAt g (g' y) y) (hg' : ∀ y > 0, HasDerivAt g' (q y * g y) y)
    (hfgr : ∃ (C : ℝ) (N : ℕ), ∀ y ≥ Y₀, ‖f y‖ ≤ C * y ^ N)
    (hggr : ∃ (C : ℝ) (N : ℕ), ∀ y ≥ Y₀, ‖g y‖ ≤ C * y ^ N) :
    f 1 * g' 1 - f' 1 * g 1 = 0 := by
  have pos : ∀ y ≥ Y₀, y > 0 := fun y hy => lt_of_lt_of_le hY₀ hy
  obtain ⟨Cf, Nf, hCf⟩ := hfgr
  obtain ⟨Cg, Ng, hCg⟩ := hggr
  have hf0 := tendsto_zero_of_moderate hc hqre (fun y hy => hf y (pos y hy))
    (fun y hy => hf' y (pos y hy)) hCf
  have hg0 := tendsto_zero_of_moderate hc hqre (fun y hy => hg y (pos y hy))
    (fun y hy => hg' y (pos y hy)) hCg
  have hf0' := tendsto_deriv_zero hqM (fun y hy => hf y (pos y hy)) (fun y hy => hf' y (pos y hy)) hf0
  have hg0' := tendsto_deriv_zero hqM (fun y hy => hg y (pos y hy)) (fun y hy => hg' y (pos y hy)) hg0
  exact wronskian_eq_zero hf hf' hg hg' hf0 hf0' hg0 hg0' 1 one_pos
end GroundTheory.Automorphic.ArchWhittaker
