-- Prove2me | solution 1 for GlobalTheory.LevelPairing.Mfr_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:01:23.104648+00:00
-- url     : https://prove2.me/submissions/7bba0953-a4ce-4643-bcb3-b4f76fa212a9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Theorems.Thm_GlobalTheory_LevelPairing_mul_mem_M
import Theorems.Thm_GlobalTheory_LevelPairing_bar_mem_Mb

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
theorem _root_.solution (l : Level H) : Mfr l ≠ ⊤ := by
  intro h
  have h1 : (1 : 𝓞 E) ∈ l.Mb := by simpa using bar_mem_Mb (l := l) (a := 1) (h ▸ Submodule.mem_top)
  have h2 := mul_mem_M h1 (show (1 : 𝓞 E) ∈ Mfr l from h ▸ Submodule.mem_top)
  rw [one_mul, ← Ideal.eq_top_iff_one, Ideal.span_singleton_eq_top] at h2
  have h3 : IsUnit (l.M : ℤ) := by
    have : IsUnit (algebraMap ℤ (𝓞 E) (l.M : ℤ)) := by simpa using h2
    exact (isUnit_map_iff (algebraMap ℤ (𝓞 E)) _).1 this
  have := l.three_le
  rcases Int.isUnit_iff.1 h3 with h | h <;> omega
end GlobalTheory.LevelPairing
