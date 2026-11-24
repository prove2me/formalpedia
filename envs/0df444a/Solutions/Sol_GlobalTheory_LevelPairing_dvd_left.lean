-- Prove2me | solution 1 for GlobalTheory.LevelPairing.dvd_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:41:33.259879+00:00
-- url     : https://prove2.me/submissions/47be75cc-2a86-4b88-9648-3c226ded1167

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Theorems.Thm_GlobalTheory_LevelPairing_cSep_spec
import Theorems.Thm_GlobalTheory_LevelPairing_dvd_EF_of_mem
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
theorem _root_.solution {x : Dw.La} (y : Dw.La) (hx : x ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)) :
    (l.M : ℤ) ∣ Dw.EF x (cSep l • y) := by
  refine Submodule.smul_induction_on hx (fun a ha z _ => ?_) (fun u v hu hv => ?_)
  · rw [Dw.adj, ← mul_smul]; exact dvd_EF_of_mem _ _ (mul_mem_M (bar_mem_Mb ha) (cSep_spec l).1)
  · rw [map_add, LinearMap.add_apply]; exact dvd_add hu hv
end GlobalTheory.LevelPairing
