-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AbForms.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:24:47.596342+00:00
-- url     : https://prove2.me/submissions/6c12e27c-4b1f-4c34-9741-bf524d213bc2

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UOfIsBaseChange
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AbForms
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.AbForms
theorem _root_.solution {X : Scheme.{0}} {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
    [IsCentralScalar B M] (x : Sp B ⟶ X) [IsOpenImmersion x] (y : Sp (TrivSqZeroExt B M) ⟶ X)
    (h : spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ y = x) :
    ∃ σ : B →+* TrivSqZeroExt B M, y = spMap σ ≫ x := by
  have hs : Function.Surjective (spMap (TrivSqZeroExt.fstHom B B M).toRingHom) := by
    change Function.Surjective (PrimeSpectrum.comap (TrivSqZeroExt.fstHom B B M).toRingHom)
    rw [← Set.range_eq_univ, range_comap_of_surjective _ _ (fun b ↦ ⟨TrivSqZeroExt.inl b, rfl⟩)]
    refine Set.eq_univ_of_forall fun p a ha ↦ ?_
    have h0 : a.fst = 0 := ha
    have h2 : a ^ 2 = 0 := by
      rw [pow_two]
      ext <;> simp [h0]
    exact p.isPrime.mem_of_pow_mem 2 (h2 ▸ p.asIdeal.zero_mem)
  have hr : Set.range y ⊆ Set.range x := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, rfl⟩ := hs p
    refine ⟨q, ?_⟩
    rw [← h]; rfl
  refine ⟨(Spec.preimage (IsOpenImmersion.lift x y hr)).hom, ?_⟩
  have e : spMap (Spec.preimage (IsOpenImmersion.lift x y hr)).hom = IsOpenImmersion.lift x y hr :=
    Spec.map_preimage _
  rw [e, IsOpenImmersion.lift_fac]
end GlobalTheory.CompanionTheory.AbForms
