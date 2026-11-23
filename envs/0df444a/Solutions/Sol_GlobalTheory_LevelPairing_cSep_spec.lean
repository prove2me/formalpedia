-- Prove2me | solution 1 for GlobalTheory.LevelPairing.cSep_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:34.034628+00:00
-- url     : https://prove2.me/submissions/e6c9b74a-0e66-4f2c-a609-c466dfb4688e

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
theorem _root_.solution (l : Level H) : cSep l ∈ Mfr l ∧ cSep l - 1 ∈ l.Mb := by
  have h : ∃ c, c ∈ Mfr l ∧ c - 1 ∈ l.Mb := by
    obtain ⟨m, hm, mb, hmb, hsum⟩ := Submodule.mem_sup.1 (l.coprime ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ l.Mb ⊔ _)
    refine ⟨mb, hmb, ?_⟩
    have : mb - 1 = -m := by rw [← hsum]; ring
    rw [this]; exact neg_mem hm
  unfold cSep
  rw [dif_pos h]
  exact h.choose_spec
end GlobalTheory.LevelPairing
