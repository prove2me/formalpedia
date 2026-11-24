-- Prove2me | solution 1 for GlobalTheory.LevelPairing.mem_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:41:35.797116+00:00
-- url     : https://prove2.me/submissions/93236fc0-5658-4660-944d-a8ec573688d5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Theorems.Thm_GlobalTheory_LevelPairing_bar_bar
import Theorems.Thm_GlobalTheory_LevelPairing_cSep_spec
import Theorems.Thm_GlobalTheory_LevelPairing_exists_eq_smul_of_dvd

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
theorem _root_.solution {x : Dw.La} (h : ∀ y, (l.M : ℤ) ∣ Dw.EF x (cSep l • y)) :
    x ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La) := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  obtain ⟨z, hz⟩ := exists_eq_smul_of_dvd (H.bar (cSep l) • x) l.M hM (fun y => by
    rw [Dw.adj, bar_bar]; exact h y)
  have h1 : H.bar (cSep l - 1) ∈ Mfr l := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) (cSep_spec l).2
  have hMm : (l.M : 𝓞 E) ∈ Mfr l := by
    have : Ideal.span {(l.M : 𝓞 E)} ≤ Mfr l := l.prod ▸ Ideal.mul_le_right
    exact this (Ideal.subset_span rfl)
  have : x = (l.M : 𝓞 E) • z - H.bar (cSep l - 1) • x := by
    rw [map_sub, map_one, sub_smul, one_smul, hz, ← Int.cast_smul_eq_zsmul (𝓞 E)]; simp
  rw [this]
  exact sub_mem (Submodule.smul_mem_smul hMm trivial) (Submodule.smul_mem_smul h1 trivial)
end GlobalTheory.LevelPairing
