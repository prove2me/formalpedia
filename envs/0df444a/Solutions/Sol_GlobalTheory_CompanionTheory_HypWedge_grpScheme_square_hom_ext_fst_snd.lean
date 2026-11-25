-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HypWedge.grpScheme_square_hom_ext_fst_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:54:21.36174+00:00
-- url     : https://prove2.me/submissions/bda31b62-f747-435f-aacd-f89de91a10da

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FormComponentOfWedgeClassZero

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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HypWedge
variable {R M N V W : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
namespace GlobalTheory.CompanionTheory.HypWedge
theorem _root_.solution {f g : ⋀[R]^2 M →ₗ[R] N}
    (h : ∀ a b, f (exteriorPower.ιMulti R 2 ![a, b]) = g (exteriorPower.ιMulti R 2 ![a, b])) : f = g := by
  refine LinearMap.ext_on (exteriorPower.ιMulti_span R 2 M) ?_
  rintro _ ⟨v, rfl⟩
  have hv : v = ![v 0, v 1] := by
    ext i; fin_cases i <;> rfl
  rw [hv]
  exact h _ _
end GlobalTheory.CompanionTheory.HypWedge
