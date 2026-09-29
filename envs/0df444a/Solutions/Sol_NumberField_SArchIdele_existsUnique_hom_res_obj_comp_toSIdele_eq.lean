-- Prove2me | solution 1 for NumberField.SArchIdele.existsUnique_hom_res_obj_comp_toSIdele_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f33fd780-e947-5b70-9d6f-f1954dfc7732

import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_SArchIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_InfinitePlaceTransport

import Theorems.Thm_NumberField_SArchIdele_injective_comp_toSIdele_and_mem_range_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_SArchIdele_existsUnique_hom_res_obj_comp_toSIdele_eq

set_option autoImplicit false
open IsDedekindDomain NumberField M4aHerbrand
open scoped NumberField.PlaceTransport

namespace Pen5Jd

noncomputable def mkHom {k G : Type} [CommRing k] [Group G] (A B : Rep k G) (f : A → B)
    (hadd : ∀ a b, f (a + b) = f a + f b) (hsmul : ∀ (c : k) (a : A), f (c • a) = c • f a)
    (hcomm : ∀ (g : G) (a : A), f (A.ρ g a) = B.ρ g (f a)) : A ⟶ B :=
  Rep.ofHom ⟨⟨⟨f, hadd⟩, hsmul⟩, fun g => LinearMap.ext (hcomm g)⟩

theorem mkHom_hom_apply {k G : Type} [CommRing k] [Group G] (A B : Rep k G) (f : A → B)
    (hadd : ∀ a b, f (a + b) = f a + f b) (hsmul : ∀ (c : k) (a : A), f (c • a) = c • f a)
    (hcomm : ∀ (g : G) (a : A), f (A.ρ g a) = B.ρ g (f a)) (a : A) : (mkHom A B f hadd hsmul hcomm).hom a = f a := rfl

theorem map_smul_int {V W : Type} [AddCommGroup V] [AddCommGroup W] (iV : Module ℤ V) (iW : Module ℤ W)
    (f : V →+ W) (m : ℤ) (v : V) :
    f (@SMul.smul ℤ V iV.toSMul m v) = @SMul.smul ℤ W iW.toSMul m (f v) := by
  rw [int_smul_eq_zsmul, int_smul_eq_zsmul, map_zsmul]

noncomputable def mkHomInt {G : Type} [Group G] (A B : Rep ℤ G) (f : A → B)
    (hadd : ∀ a b, f (a + b) = f a + f b)
    (hcomm : ∀ (g : G) (a : A), f (A.ρ g a) = B.ρ g (f a)) : A ⟶ B :=
  mkHom A B f hadd (fun c a => map_smul_int _ _ (AddMonoidHom.mk' f hadd) c a) hcomm

theorem mkHomInt_hom_apply {G : Type} [Group G] (A B : Rep ℤ G) (f : A → B)
    (hadd : ∀ a b, f (a + b) = f a + f b)
    (hcomm : ∀ (g : G) (a : A), f (A.ρ g a) = B.ρ g (f a)) (a : A) : (mkHomInt A B f hadd hcomm).hom a = f a := rfl

end Pen5Jd

set_option maxHeartbeats 1600000 in
theorem solution
    (E K K' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K'] [NumberField K']
    [Algebra E K] [Algebra E K'] [Algebra K K'] [IsScalarTower E K K'] [IsGalois E K] [IsGalois E K']
    (S : Finset (HeightOneSpectrum (𝓞 E)))

    (Φ : NumberField.SIdele.obj E K S →+ Additive (AdeleRing (𝓞 K) K)ˣ)
    (hΦinj : Function.Injective Φ)
    (hΦrange : Φ.range = (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}).toAddSubgroup)
    (hΦS : ∀ (x : NumberField.SIdele.obj E K S) (v : {v // v ∈ S}) (w : HeightOneSpectrum (𝓞 K)) (y : K ≃ₐ[E] K)
      (hy : y • w = NumberField.PlaceAbove.above E K v.1),
      NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w) =
        ((Additive.toMul ((x (Sum.inl (Sum.inl v))).1 y) :
          ((NumberField.PlaceAbove.above E K v.1).adicCompletion K)ˣ) : (NumberField.PlaceAbove.above E K v.1).adicCompletion K))
    (hΦout : ∀ (x : NumberField.SIdele.obj E K S) (v : {v // v ∉ S}) (w : HeightOneSpectrum (𝓞 K)) (y : K ≃ₐ[E] K)
      (hy : y • w = NumberField.PlaceAbove.above E K v.1),
      NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w) =
        (((Additive.toMul ((x (Sum.inl (Sum.inr v))).1 y) :
          ((NumberField.PlaceAbove.above E K v.1).adicCompletionIntegers K)ˣ) :
            (NumberField.PlaceAbove.above E K v.1).adicCompletionIntegers K) : (NumberField.PlaceAbove.above E K v.1).adicCompletion K))
    (hΦinf : ∀ (x : NumberField.SIdele.obj E K S) (v : InfinitePlace E) (w : InfinitePlace K) (y : K ≃ₐ[E] K)
      (hy : y • w = NumberField.ArchIdele.above E K v),
      NumberField.InfinitePlaceTransport.transport y hy (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w) =
        ((Additive.toMul ((x (Sum.inr v)).1 y) : ((NumberField.ArchIdele.above E K v).Completion)ˣ) :
          (NumberField.ArchIdele.above E K v).Completion))
    (D : IdeleGaloisDescent (𝓞 K) E K)
    (hΦeq : ∀ (g : K ≃ₐ[E] K) (x : NumberField.SIdele.obj E K S),
      Φ ((NumberField.SIdele.obj E K S).ρ g x) = Additive.ofMul (D.unitsAct g (Additive.toMul (Φ x))))

    (Φ' : NumberField.SIdele.obj E K' S →+ Additive (AdeleRing (𝓞 K') K')ˣ)
    (hΦinj' : Function.Injective Φ')
    (hΦrange' : Φ'.range = (NumberField.AdeleRing.unitIdelesOutside (𝓞 K') K' {w | w.under (𝓞 E) ∈ S}).toAddSubgroup)
    (hΦS' : ∀ (x : NumberField.SIdele.obj E K' S) (v : {v // v ∈ S}) (w : HeightOneSpectrum (𝓞 K')) (y : K' ≃ₐ[E] K')
      (hy : y • w = NumberField.PlaceAbove.above E K' v.1),
      NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ' x) : (AdeleRing (𝓞 K') K')ˣ) : AdeleRing (𝓞 K') K').2 w) =
        ((Additive.toMul ((x (Sum.inl (Sum.inl v))).1 y) :
          ((NumberField.PlaceAbove.above E K' v.1).adicCompletion K')ˣ) : (NumberField.PlaceAbove.above E K' v.1).adicCompletion K'))
    (hΦout' : ∀ (x : NumberField.SIdele.obj E K' S) (v : {v // v ∉ S}) (w : HeightOneSpectrum (𝓞 K')) (y : K' ≃ₐ[E] K')
      (hy : y • w = NumberField.PlaceAbove.above E K' v.1),
      NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ' x) : (AdeleRing (𝓞 K') K')ˣ) : AdeleRing (𝓞 K') K').2 w) =
        (((Additive.toMul ((x (Sum.inl (Sum.inr v))).1 y) :
          ((NumberField.PlaceAbove.above E K' v.1).adicCompletionIntegers K')ˣ) :
            (NumberField.PlaceAbove.above E K' v.1).adicCompletionIntegers K') : (NumberField.PlaceAbove.above E K' v.1).adicCompletion K'))
    (hΦinf' : ∀ (x : NumberField.SIdele.obj E K' S) (v : InfinitePlace E) (w : InfinitePlace K') (y : K' ≃ₐ[E] K')
      (hy : y • w = NumberField.ArchIdele.above E K' v),
      NumberField.InfinitePlaceTransport.transport y hy (((Additive.toMul (Φ' x) : (AdeleRing (𝓞 K') K')ˣ) : AdeleRing (𝓞 K') K').1 w) =
        ((Additive.toMul ((x (Sum.inr v)).1 y) : ((NumberField.ArchIdele.above E K' v).Completion)ˣ) :
          (NumberField.ArchIdele.above E K' v).Completion))
    (D' : IdeleGaloisDescent (𝓞 K') E K')
    (hΦeq' : ∀ (g : K' ≃ₐ[E] K') (x : NumberField.SIdele.obj E K' S),
      Φ' ((NumberField.SIdele.obj E K' S).ρ g x) = Additive.ofMul (D'.unitsAct g (Additive.toMul (Φ' x))))

    (JJ : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 K') K')ˣ)
    (hJJ : ∀ z : (AdeleRing (𝓞 K) K)ˣ, (∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) ∉ S → finPart w z = 1) →
      ∀ w' : HeightOneSpectrum (𝓞 K'), w'.under (𝓞 E) ∉ S → finPart w' (JJ z) = 1)
    (hJJeq : ∀ (g' : K' ≃ₐ[E] K') (z : (AdeleRing (𝓞 K) K)ˣ),
      JJ (D.unitsAct (AlgEquiv.restrictNormalHom K g') z) = D'.unitsAct g' (JJ z)) :
    ∃! jJ : Rep.res (AlgEquiv.restrictNormalHom K : (K' ≃ₐ[E] K') →* (K ≃ₐ[E] K)) (NumberField.SArchIdele.obj E K S) ⟶
        NumberField.SArchIdele.obj E K' S,
      ∀ y : NumberField.SArchIdele.obj E K S,
        Φ' ((NumberField.SArchIdele.toSIdele E K' S).hom (jJ.hom y)) =
          Additive.ofMul (JJ (Additive.toMul (Φ ((NumberField.SArchIdele.toSIdele E K S).hom y)))) := by
  classical
  obtain ⟨-, hrange⟩ := NumberField.SArchIdele.injective_comp_toSIdele_and_mem_range_iff E K S Φ hΦinj hΦrange hΦS hΦout hΦinf
  obtain ⟨hinj', hrange'⟩ :=
    NumberField.SArchIdele.injective_comp_toSIdele_and_mem_range_iff E K' S Φ' hΦinj' hΦrange' hΦS' hΦout' hΦinf'

  have hex : ∀ y : NumberField.SArchIdele.obj E K S, ∃ y' : NumberField.SArchIdele.obj E K' S,
      Φ' ((NumberField.SArchIdele.toSIdele E K' S).hom y') =
        Additive.ofMul (JJ (Additive.toMul (Φ ((NumberField.SArchIdele.toSIdele E K S).hom y)))) := fun y =>
    (hrange' _).2 (hJJ _ ((hrange _).1 ⟨y, rfl⟩))
  choose f hf using hex

  have hf_add : ∀ y₁ y₂, f (y₁ + y₂) = f y₁ + f y₂ := fun y₁ y₂ => hinj' (by
    simp only [map_add, hf, toMul_add, map_mul, ofMul_mul])

  have hf_eq : ∀ (g' : K' ≃ₐ[E] K') (y : NumberField.SArchIdele.obj E K S),
      f ((Rep.res (AlgEquiv.restrictNormalHom K : (K' ≃ₐ[E] K') →* (K ≃ₐ[E] K)) (NumberField.SArchIdele.obj E K S)).ρ g' y) =
        (NumberField.SArchIdele.obj E K' S).ρ g' (f y) := fun g' y => hinj' (by
    show Φ' ((NumberField.SArchIdele.toSIdele E K' S).hom
        (f ((NumberField.SArchIdele.obj E K S).ρ (AlgEquiv.restrictNormalHom K g') y))) =
      Φ' ((NumberField.SArchIdele.toSIdele E K' S).hom ((NumberField.SArchIdele.obj E K' S).ρ g' (f y)))
    rw [hf, Rep.hom_comm_apply, hΦeq, toMul_ofMul, hJJeq, Rep.hom_comm_apply, hΦeq', hf, toMul_ofMul])
  refine ⟨Pen5Jd.mkHomInt _ _ f hf_add hf_eq, fun y => hf y, fun j hj => ?_⟩

  have huniq : ∀ y, j.hom y = f y := fun y => hinj' (by
    show Φ' ((NumberField.SArchIdele.toSIdele E K' S).hom (j.hom y)) = Φ' ((NumberField.SArchIdele.toSIdele E K' S).hom (f y))
    rw [hj y, hf y])
  exact Rep.hom_ext (DFunLike.ext _ _ huniq)

end S_NumberField_SArchIdele_existsUnique_hom_res_obj_comp_toSIdele_eq
end P2MW
export P2MW.S_NumberField_SArchIdele_existsUnique_hom_res_obj_comp_toSIdele_eq (solution)
