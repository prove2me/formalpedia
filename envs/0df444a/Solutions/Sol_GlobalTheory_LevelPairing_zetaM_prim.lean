-- Prove2me | solution 1 for GlobalTheory.LevelPairing.zetaM_prim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:04.450573+00:00
-- url     : https://prove2.me/submissions/49aa0b22-97b7-419c-8cd6-7dc66056ecc7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Theorems.Thm_GlobalTheory_LevelPairing_zetaM_coe

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
theorem _root_.solution (c : Coeff l) : IsPrimitiveRoot (zetaM c) l.M := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  refine IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom) ?_ Subtype.val_injective
  have := zetaM_coe c
  change IsPrimitiveRoot ((zetaM c : c.F) : ℂ) l.M
  rw [this]
  exact Complex.isPrimitiveRoot_exp l.M hM
end GlobalTheory.LevelPairing
