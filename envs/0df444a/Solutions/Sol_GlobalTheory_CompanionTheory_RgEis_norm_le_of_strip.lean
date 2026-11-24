-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.norm_le_of_strip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:01:24.604802+00:00
-- url     : https://prove2.me/submissions/0cdc486d-d092-4b40-910f-4fee5d1fe6a1

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WallLawOfSectionLaw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {f : ℂ → X}
    (hf : Differentiable ℂ f) {a b B C : ℝ} (hab : a < b)
    (hB : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ B) (ha : ∀ z : ℂ, z.re = a → ‖f z‖ ≤ C)
    (hb : ∀ z : ℂ, z.re = b → ‖f z‖ ≤ C) {z : ℂ} (h1 : a ≤ z.re) (h2 : z.re ≤ b) : ‖f z‖ ≤ C := by
  refine PhragmenLindelof.vertical_strip hf.diffContOnCl ?_ ha hb h1 h2
  refine ⟨0, div_pos Real.pi_pos (sub_pos.2 hab), 0, ?_⟩
  refine Asymptotics.IsBigO.of_bound B ?_
  filter_upwards [mem_inf_of_right (mem_principal_self _)] with w hw
  have := hB w hw.1.le hw.2.le
  simpa using this
end GlobalTheory.CompanionTheory.RgEis
