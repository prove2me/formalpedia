-- Prove2me | solution 1 for GlobalTheory.Survey.BaseClassMove.isBeta_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:09:57.227962+00:00
-- url     : https://prove2.me/submissions/82eabec4-f227-4a97-a29a-6677182c8987

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BaseClassMove

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
open GlobalTheory GlobalTheory.Survey GlobalTheory.Survey.BaseClassMove
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
namespace GlobalTheory.Survey.BaseClassMove
theorem _root_.solution (n : ℕ) : IsBeta Dw c (unitLat E n) 1 := by
  have e : (unitLat E n).Ln = (unitLat E n).La := inf_idem _
  refine ⟨one_ne_zero, ?_, fun σ => ?_⟩
  · unfold BetaIs; rw [e, ← Submodule.one_eq_span, one_mul]
  · rw [e]; simp
end GlobalTheory.Survey.BaseClassMove
