-- Prove2me | solution 1 for GlobalTheory.LevelPairing.pairL_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:00:48.166843+00:00
-- url     : https://prove2.me/submissions/54e9ceb9-1127-43ba-a4a2-b1ed24312840

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Theorems.Thm_GlobalTheory_LevelPairing_dvd_right
import Theorems.Thm_GlobalTheory_LevelPairing_dvd_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevelPairing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
namespace GlobalTheory.LevelPairing
theorem _root_.solution {n : ℕ} (x0 x0' x x' : Fin n → Dw.La)
    (h0 : ∀ b, x0 b - x0' b ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La))
    (h1 : ∀ b, x b - x' b ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)) :
    (l.M : ℤ) ∣ pairL (l := l) x0 x - pairL (l := l) x0' x' := by
  unfold pairL
  rw [← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun b _ => ?_
  have : Dw.EF (x0 b) (cSep l • x b) - Dw.EF (x0' b) (cSep l • x' b) =
      Dw.EF (x0 b - x0' b) (cSep l • x b) + Dw.EF (x0' b) (cSep l • (x b - x' b)) := by
    simp [smul_sub]
  rw [this]
  exact dvd_add (dvd_left _ (h0 b)) (dvd_right _ (h1 b))
end GlobalTheory.LevelPairing
