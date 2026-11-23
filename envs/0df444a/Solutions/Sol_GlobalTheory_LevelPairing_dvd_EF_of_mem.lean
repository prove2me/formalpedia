-- Prove2me | solution 1 for GlobalTheory.LevelPairing.dvd_EF_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:01.108802+00:00
-- url     : https://prove2.me/submissions/e3d93c75-2d7a-43a7-9073-63f808a1032a

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
theorem _root_.solution (x y : Dw.La) {a : 𝓞 E} (ha : a ∈ Ideal.span {(l.M : 𝓞 E)}) :
    (l.M : ℤ) ∣ Dw.EF x (a • y) := by
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  have : (b * (l.M : 𝓞 E)) • y = (l.M : ℤ) • (b • y) := by
    rw [mul_comm, mul_smul, ← Int.cast_smul_eq_zsmul (𝓞 E)]; simp
  rw [this, map_zsmul]
  exact Dvd.intro _ rfl
end GlobalTheory.LevelPairing
