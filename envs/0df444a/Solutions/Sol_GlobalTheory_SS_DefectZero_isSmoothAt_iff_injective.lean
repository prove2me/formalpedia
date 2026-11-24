-- Prove2me | solution 1 for GlobalTheory.SS.DefectZero.isSmoothAt_iff_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:16:47.704121+00:00
-- url     : https://prove2.me/submissions/67a83231-44e5-4b72-b677-a8851e57c13c

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open TensorProduct KaehlerDifferential
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.DefectZero
namespace GlobalTheory.SS.DefectZero
theorem _root_.solution (R A B K : Type) [CommRing R] [CommRing A] [CommRing B] [Field K]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra B K] [Algebra A K]
    [IsScalarTower A B K] [IsNoetherianRing A] [Algebra.FormallySmooth R A]
    [Module.Free A Ω[A⁄R]] [Module.Finite A Ω[A⁄R]] (hs : Function.Surjective (algebraMap A B))
    (q : Ideal B) [q.IsPrime] (hq : q = RingHom.ker (algebraMap B K)) :
    Algebra.IsSmoothAt R q ↔ Function.Injective (cotangentComplexBaseChange R B A K) := by
  let p : Ideal A := q.comap (algebraMap A B)
  let P := Localization.AtPrime p
  let S := Localization.AtPrime q
  let : Algebra P S := (Localization.localRingHom p q (algebraMap A B) rfl).toAlgebra
  have : IsScalarTower A P S := .of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply A B S]
    exact (Localization.localRingHom_to_map p q (algebraMap A B) rfl x).symm
  have : IsScalarTower R P S := .to₁₃₄ R A P S
  have hu : ∀ y : q.primeCompl, IsUnit (algebraMap B K y) := fun y =>
    isUnit_iff_ne_zero.mpr fun h => y.2 (hq.ge h)
  let : Algebra S K := (IsLocalization.lift (S := S) hu).toAlgebra
  have : IsScalarTower B S K := .of_algebraMap_eq fun x => (IsLocalization.lift_eq hu x).symm
  let : Algebra P K := ((algebraMap S K).comp (algebraMap P S)).toAlgebra
  have : IsScalarTower P S K := .of_algebraMap_eq' rfl
  have : IsScalarTower A S K := .to₁₃₄ A B S K
  have : IsScalarTower A P K := .to₁₂₄ A P S K
  have : Algebra.FormallyEtale A P := .of_isLocalization p.primeCompl
  have : Algebra.FormallySmooth R P := .comp _ A _
  have : Module.Free P Ω[P⁄R] := .of_equiv (tensorKaehlerEquivOfFormallyEtale R A P)
  have : Module.Finite P Ω[P⁄R] := .equiv (tensorKaehlerEquivOfFormallyEtale R A P)
  have h₁ : Function.Surjective (algebraMap P S) :=
    (RingHom.surjectiveOnStalks_of_surjective hs).localRingHom_surjective _ _ rfl
  have h₃ : IsLocalRing.maximalIdeal S ≤ RingHom.ker (algebraMap S K) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, ← IsScalarTower.algebraMap_apply]
    exact hq.le hx
  rw [Algebra.IsSmoothAt, Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange P K h₁
    (IsNoetherian.noetherian _) h₃]
  have hker : (RingHom.ker (algebraMap A B)).localized' P p.primeCompl (Algebra.linearMap A P) =
      RingHom.ker (algebraMap P S) := by
    ext x
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
    have e : algebraMap P S (IsLocalization.mk' P x s) = 0 ↔ algebraMap A S x = 0 := by
      rw [IsScalarTower.algebraMap_apply A P S, ← IsLocalization.mk'_spec P x s, map_mul]
      exact ((IsLocalization.map_units P s).map _).mul_left_eq_zero.symm
    rw [RingHom.mem_ker, e, Submodule.localized'_eq_span]
    change _ ∈ Ideal.map (algebraMap A P) _ ↔ _
    rw [IsLocalization.mk'_mem_map_algebraMap_iff, IsScalarTower.algebraMap_apply A B S,
      IsLocalization.map_eq_zero_iff q.primeCompl]
    constructor
    · rintro ⟨t, ht, h⟩
      exact ⟨⟨algebraMap A B t, ht⟩, by simpa [RingHom.mem_ker] using h⟩
    · rintro ⟨⟨t, ht⟩, h⟩
      obtain ⟨t, rfl⟩ := hs t
      exact ⟨t, ht, by simpa [RingHom.mem_ker] using h⟩
  let e₁ : P ⊗[A] RingHom.ker (algebraMap A B) ≃ₗ[P] RingHom.ker (algebraMap P S) :=
    (IsLocalizedModule.isBaseChange p.primeCompl P ((RingHom.ker (algebraMap A B)).toLocalized' P
      p.primeCompl (Algebra.linearMap A P))).equiv ≪≫ₗ LinearEquiv.ofEq _ _ hker
  let eₗ : K ⊗[A] RingHom.ker (algebraMap A B) ≃ₗ[K] K ⊗[P] RingHom.ker (algebraMap P S) :=
    (AlgebraTensorModule.cancelBaseChange A P K K _).symm ≪≫ₗ
      AlgebraTensorModule.congr (.refl K K) e₁
  let eᵣ : K ⊗[A] Ω[A⁄R] ≃ₗ[K] K ⊗[P] Ω[P⁄R] :=
    (AlgebraTensorModule.cancelBaseChange A P K K _).symm ≪≫ₗ
      AlgebraTensorModule.congr (.refl K K) (tensorKaehlerEquivOfFormallyEtale R A P)
  have hc : cotangentComplexBaseChange R S P K ∘ₗ eₗ.toLinearMap =
      eᵣ.toLinearMap ∘ₗ cotangentComplexBaseChange R B A K := by
    ext x
    simp [eₗ, eᵣ, e₁, cotangentComplexBaseChange_tmul, IsBaseChange.equiv_tmul]
  rw [← eₗ.injective_comp, ← eᵣ.comp_injective]
  exact iff_of_eq (congrArg Function.Injective (congrArg DFunLike.coe hc))
end GlobalTheory.SS.DefectZero
