-- Prove2me | solution 1 for GlobalTheory.LevelPairing.finite_LevQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:01:27.478896+00:00
-- url     : https://prove2.me/submissions/e61eb0a4-7a77-4492-b6f4-6533cdd8022d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos

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
theorem _root_.solution : Finite (LevQ Dw l) := by
  haveI := Dw.fin
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hb : l.Mb ≠ ⊥ := by
    intro h
    have : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
    have := this (Ideal.subset_span rfl)
    rw [h, Ideal.mem_bot] at this
    exact hM (by exact_mod_cast this)
  haveI : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot _ hb
  haveI : Module.Finite (𝓞 E ⧸ l.Mb) (LevQ Dw l) := Module.Finite.of_restrictScalars_finite (𝓞 E) _ _
  exact Module.finite_of_finite (𝓞 E ⧸ l.Mb)
end GlobalTheory.LevelPairing
