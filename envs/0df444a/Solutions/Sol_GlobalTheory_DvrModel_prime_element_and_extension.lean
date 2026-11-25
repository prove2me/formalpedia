-- Prove2me | solution 1 for GlobalTheory.DvrModel.prime_element_and_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:44:51.946812+00:00
-- url     : https://prove2.me/submissions/cd706474-8850-4d3e-b90b-47c13d7068a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Theorems.Thm_GlobalTheory_DvrModel_existsUnique_gen
import Theorems.Thm_GlobalTheory_DvrModel_sec_eq_zero_of_app_eq_zero
import Theorems.Thm_GlobalTheory_DvrModel_existsUnique_zpow_mul_sec
import Theorems.Thm_GlobalTheory_PrimeElement_eq_zero_of_forall_pow_dvd
import Theorems.Thm_GlobalTheory_PrimeElement_exists_unit_algebraMap_eq_of_valuation_eq_one
import Theorems.Thm_GlobalTheory_PrimeElement_irreducible_algebraMap
import Theorems.Thm_GlobalTheory_PrimeElement_isDiscreteValuationRing
import Theorems.Thm_GlobalTheory_PrimeElement_isDomain_atPrime
import Theorems.Thm_GlobalTheory_PrimeElement_range_inf_range


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.DvrModel
namespace GlobalTheory.DvrModel
theorem _root_.solution :
    (∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (π : R)
      [(Ideal.span {π}).IsPrime], π ≠ 0 →
      ∀ (A : Type u) [CommRing A] [Algebra R A] [IsLocalization.Away π A]
        (S : Type u) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S (Ideal.span {π})]
        (F : Type u) [Field F] [Algebra R F] [IsFractionRing R F]
        [Algebra A F] [IsScalarTower R A F] [Algebra S F] [IsScalarTower R S F],
      ∃ (_ : IsDomain S) (_ : IsDiscreteValuationRing S) (_ : IsFractionRing S F),
        Irreducible (algebraMap R S π) ∧
        (algebraMap A F).range ⊓ (algebraMap S F).range = (algebraMap R F).range ∧
        (∀ y : A, IsUnit y →
          (IsDiscreteValuationRing.maximalIdeal S).valuation F (algebraMap A F y) = 1 →
          ∃ r : R, IsUnit r ∧ algebraMap R A r = y) ∧
        ∀ x : R, (∀ n : ℕ, π ^ n ∣ x) → x = 0) ∧
    ∀ (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      (K : Type u) [Field K] [Algebra V K] [IsFractionRing V K] (ϖ : V), Irreducible ϖ →
      ∀ (H HK Hs : Scheme.{u}) (f : H ⟶ Spec (.of V)) [Flat f] [LocallyOfFiniteType f]
        (j : HK ⟶ H) (fK : HK ⟶ Spec (.of K)) [IsIntegral HK]
        (i : Hs ⟶ H) (fs : Hs ⟶ Spec (.of (ResidueField V))) [IsIntegral Hs],
      IsPullback j fK f (Spec.map (CommRingCat.ofHom (algebraMap V K))) →
      IsPullback i fs f (Spec.map (CommRingCat.ofHom (residue V))) →
      ∀ L : LB H, L.IsLB →
      (∀ (e : Spec (.of V) ⟶ H) (eK : Spec (.of K) ⟶ HK), e ≫ f = 𝟙 _ →
        eK ≫ j = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ e →
        ∀ (r : LB.Gen (L.pull j)) (ρ : LB.Gen (L.pull e)), r.IsGen →
        LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ r eK)
          (LB.pullGen L _ _ ρ (Spec.map (CommRingCat.ofHom (algebraMap V K)))) →
        ∃! r' : LB.Gen L, r'.IsGen ∧ LB.genPull L r' j = r) ∧
      (∀ s : L.Sec, (∀ a (n : ℕ), (pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span {ϖ ^ n}))))).app (L.U a) (s.f a) = 0) →
        ∀ a, s.f a = 0) ∧
      ∀ r : (L.pull j).Sec, (∃ a, r.f a ≠ 0) →
        ∃! n : ℤ, ∃ s : L.Sec,
          (∀ a : PUnit → L.ι,
            j.appLE (L.U (a ⟨⟩)) ((L.pull j).U a) (pull_U L j a).le (s.f (a ⟨⟩)) =
              HK.presheaf.map (homOfLE le_top).op
                (fK.appTop ((Scheme.ΓSpecIso (.of K)).inv (algebraMap V K ϖ ^ n))) * r.f a) ∧
          ∃ a, ∃ x, f x = closedPoint V ∧ x ∈ H.basicOpen (s.f a) := by
  refine ⟨fun R _ _ _ π _ hπ A _ _ _ S _ _ _ F _ _ _ _ _ _ _ ↦ ?_,
    fun V _ _ _ K _ _ _ ϖ hϖ H HK Hs f _ _ j fK _ i fs _ hK hs L hL ↦
      ⟨fun e eK he heK r ρ hr hρ ↦ existsUnique_gen hK hs he heK hL r hr ρ hρ,
        fun s h ↦ sec_eq_zero_of_app_eq_zero hK hs hϖ hL s (fun _ ↦ .of_hasPullback _ _) h,
        existsUnique_zpow_mul_sec hK hs hϖ hL⟩⟩
  have h₁ := PrimeElement.isDomain_atPrime (π := π) S
  have h₂ := PrimeElement.isDiscreteValuationRing (π := π) S hπ
  have h₃ : IsFractionRing S F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Ideal.span {π}).primeCompl S F
  exact ⟨h₁, h₂, h₃, PrimeElement.irreducible_algebraMap S hπ,
    PrimeElement.range_inf_range A S F hπ,
    fun y hy h ↦ PrimeElement.exists_unit_algebraMap_eq_of_valuation_eq_one S F hπ hy h,
    fun x ↦ PrimeElement.eq_zero_of_forall_pow_dvd
      ((Ideal.span_singleton_prime hπ).1 inferInstance).not_isUnit⟩
end GlobalTheory.DvrModel
