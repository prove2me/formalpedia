-- Prove2me | solution 1 for GlobalTheory.Spread.dualMapR_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:41:31.479849+00:00
-- url     : https://prove2.me/submissions/c1e2e20f-2ebb-423d-b1b1-b650e5332cb3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Spread
variable {k : Type} [CommRing k] {B Z : Scheme.{0}} (pB : B ⟶ Sp k)
variable (A : Type) [CommRing A] [Algebra k A]
variable {A} (pZ : Z ⟶ Sp k)
open Chart
namespace GlobalTheory.Spread
theorem _root_.solution {R A : Type} [CommRing R] [CommRing A] {f : R →+* A}
    (hf : Function.Injective f) : Function.Injective (dualMapR f) := by
  intro a b h
  have h₁ := congrArg TrivSqZeroExt.fst h
  have h₂ := congrArg TrivSqZeroExt.snd h
  simp only [dualMapR, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.fst_add,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, TrivSqZeroExt.snd_add,
    TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at h₁ h₂
  exact TrivSqZeroExt.ext (hf h₁) (hf h₂)
end GlobalTheory.Spread
