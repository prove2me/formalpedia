-- Prove2me | solution 1 for GlobalTheory.HeckeFrCompare.pointHom_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:46:10.689928+00:00
-- url     : https://prove2.me/submissions/ab47434c-927e-486f-88ee-b9a1ee7f8736

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeFr
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_FibrePushforward
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HkRelFrOfTransportIff
import Theorems.Thm_GlobalTheory_HeckeFrCompare_sends_unique
import Theorems.Thm_GlobalTheory_HeckeFrCompare_sends_conj_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HeckeFrCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
namespace GlobalTheory.HeckeFrCompare
theorem _root_.solution {Ω : Type} [Field Ω] [IsAlgClosed Ω] {p : ℕ} {x x' : Sp Ω ⟶ Xo.X}
    {C : Subgroup (Over.mk x ⟶ Xo.univ.t.G)} {ψ : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x'}
    {f g : (Over.mk x ⟶ Xo.univ.t.G) →* (Over.mk x' ⟶ Xo.univ.t.G)} (hf : IsHkIsog p x x' C ψ f)
    (hg : IsHkIsog p x x' C ψ g) : f = g :=
  MonoidHom.ext fun a =>
    sends_unique ((sends_conj_iff ψ _ _).2 (hf.2.2.1 a)) ((sends_conj_iff ψ _ _).2 (hg.2.2.1 a))
end GlobalTheory.HeckeFrCompare
