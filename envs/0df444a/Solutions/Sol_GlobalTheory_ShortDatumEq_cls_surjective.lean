-- Prove2me | solution 1 for GlobalTheory.ShortDatumEq.cls_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:10:08.824205+00:00
-- url     : https://prove2.me/submissions/926d4fbf-4e03-4eed-9537-29d3cd29a78d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelIndexFourierCharacter
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdmissibleFalseIffFirstInvariant

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
open GlobalTheory GlobalTheory.ShortDatumEq
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation hiding zetaM
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
namespace GlobalTheory.ShortDatumEq
theorem _root_.solution (l : Level H) (n : ℕ) : Function.Surjective (cls (D := D) l (n := n)) := fun a =>
  ⟨fun b => qRep (a b), funext fun b => Classical.choose_spec (Submodule.Quotient.mk_surjective _ (a b))⟩
end GlobalTheory.ShortDatumEq
