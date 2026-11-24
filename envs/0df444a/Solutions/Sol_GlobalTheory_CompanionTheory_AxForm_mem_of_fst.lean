-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AxForm.mem_of_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:28:19.465528+00:00
-- url     : https://prove2.me/submissions/8d7ad6c9-8a0d-48fb-93cc-83f3f38fa2c9

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModuleHomCompSquareZeroSection

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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AxForm
variable {R : Type} [CommRing R] {X : Scheme.{0}}
namespace GlobalTheory.CompanionTheory.AxForm
theorem _root_.solution {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    (y : Sp (TrivSqZeroExt B M) ⟶ X) (W : X.Opens)
    (h : ∀ z, (spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ y) z ∈ W) (z : Sp (TrivSqZeroExt B M)) :
    y z ∈ W := by
  have hz : ∀ m : M, TrivSqZeroExt.inr m ∈ (z : PrimeSpectrum _).asIdeal := fun m ↦
    (z : PrimeSpectrum _).isPrime.mem_of_pow_mem 2 (by rw [sq, TrivSqZeroExt.inr_mul_inr]; exact Ideal.zero_mem _)
  let z' : PrimeSpectrum B := PrimeSpectrum.comap (TrivSqZeroExt.inlHom B M) z
  have e : (spMap (TrivSqZeroExt.fstHom B B M).toRingHom) z' = z := by
    change PrimeSpectrum.comap (TrivSqZeroExt.fstHom B B M).toRingHom z' = z
    ext a
    have ea := TrivSqZeroExt.inl_fst_add_inr_snd_eq a
    change TrivSqZeroExt.inl a.fst ∈ (z : PrimeSpectrum _).asIdeal ↔ a ∈ (z : PrimeSpectrum _).asIdeal
    constructor
    · intro h1
      rw [← ea]
      exact Ideal.add_mem _ h1 (hz _)
    · intro h1
      rw [eq_sub_of_add_eq ea]
      exact Ideal.sub_mem _ h1 (hz a.snd)
  have h2 : y ((spMap (TrivSqZeroExt.fstHom B B M).toRingHom) z') ∈ W := h z'
  rwa [e] at h2
end GlobalTheory.CompanionTheory.AxForm
