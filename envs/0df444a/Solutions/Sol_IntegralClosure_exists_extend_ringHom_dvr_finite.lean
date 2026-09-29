-- Prove2me | solution 1 for IntegralClosure.exists_extend_ringHom_dvr_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4eb61d84-0be0-5e77-ad2d-f22b308fdf36

import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Theorems.Thm_IsLocalRing_exists_fin_points_dvr_iInf_ker_eq_bot
import Theorems.Thm_IsLocalRing_of_isDomain_of_module_finite_of_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntegralClosure_exists_extend_ringHom_dvr_finite

set_option autoImplicit false

open Polynomial
open scoped TensorProduct

namespace DichE

theorem isIntegral_subalgebra (R : Subalgebra ℤ (integralClosure ℤ ℂ)) :
    Algebra.IsIntegral ℤ R := by
  refine ⟨fun x => ?_⟩
  have hx : IsIntegral ℤ ((x : integralClosure ℤ ℂ) : ℂ) := x.1.2
  let f : R →ₐ[ℤ] ℂ := (integralClosure ℤ ℂ).val.comp R.val
  have hf : Function.Injective f := fun a b h => Subtype.ext (Subtype.ext h)
  exact (isIntegral_algHom_iff f hf).mp hx

theorem ringHom_injective {O : Type*} [CommRing O] [IsDomain O] [CharZero O]
    (R : Subalgebra ℤ (integralClosure ℤ ℂ)) (φ : R →+* O) : Function.Injective φ := by
  haveI := isIntegral_subalgebra R
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast] at hn
  exact Ideal.mem_bot.mpr (Int.cast_eq_zero.mp hn)

theorem exists_domain_point_gen {Rd O T : Type} [CommRing Rd] [IsDomain Rd] [CommRing O] [IsDomain O]
    [CommRing T] [IsDomain T] [Algebra Rd T] (hRT : Function.Injective (algebraMap Rd T))
    (φ : Rd →+* O) (hφ : Function.Injective φ)
    {ι : Type} [Finite ι] (g : ι → T) (hgen : Algebra.adjoin Rd (Set.range g) = ⊤)
    (hint : ∀ i, IsIntegral ℤ (g i)) :
    ∃ (P : Type) (_ : CommRing P) (_ : IsDomain P) (_ : Algebra O P) (_ : Module.Finite O P),
      Function.Injective (algebraMap O P) ∧
      ∃ ψ : T →+* P, ∀ x : Rd, ψ (algebraMap Rd T x) = algebraMap O P (φ x) := by
  classical

  letI : Algebra Rd (FractionRing O) := ((algebraMap O (FractionRing O)).comp φ).toAlgebra
  have hRF : Function.Injective (algebraMap Rd (FractionRing T)) := by
    rw [IsScalarTower.algebraMap_eq Rd T (FractionRing T)]
    exact (IsFractionRing.injective T (FractionRing T)).comp hRT
  have hRK : Function.Injective (algebraMap Rd (FractionRing O)) :=
    (IsFractionRing.injective O (FractionRing O)).comp hφ

  haveI : Nontrivial (FractionRing T ⊗[Rd] FractionRing O) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain Rd (FractionRing T) (FractionRing O)
      hRF hRK
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (FractionRing T ⊗[Rd] FractionRing O)
  haveI := h𝔪
  letI : Field ((FractionRing T ⊗[Rd] FractionRing O) ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  let iF : FractionRing T →+* (FractionRing T ⊗[Rd] FractionRing O) ⧸ 𝔪 :=
    (Ideal.Quotient.mk 𝔪).comp Algebra.TensorProduct.includeLeftRingHom
  let iK : FractionRing O →+* (FractionRing T ⊗[Rd] FractionRing O) ⧸ 𝔪 :=
    (Ideal.Quotient.mk 𝔪).comp Algebra.TensorProduct.includeRight.toRingHom
  letI algOL : Algebra O ((FractionRing T ⊗[Rd] FractionRing O) ⧸ 𝔪) :=
    (iK.comp (algebraMap O (FractionRing O))).toAlgebra
  have hOL : Function.Injective (algebraMap O ((FractionRing T ⊗[Rd] FractionRing O) ⧸ 𝔪)) :=
    iK.injective.comp (IsFractionRing.injective O (FractionRing O))
  let ψL : T →+* (FractionRing T ⊗[Rd] FractionRing O) ⧸ 𝔪 := iF.comp (algebraMap T (FractionRing T))

  have key : ∀ x : Rd, ψL (algebraMap Rd T x) = algebraMap O _ (φ x) := by
    intro x
    show Ideal.Quotient.mk 𝔪 (algebraMap T (FractionRing T) (algebraMap Rd T x) ⊗ₜ[Rd] (1 : FractionRing O)) =
      Ideal.Quotient.mk 𝔪 ((1 : FractionRing T) ⊗ₜ[Rd] algebraMap O (FractionRing O) (φ x))
    congr 1
    rw [← IsScalarTower.algebraMap_apply Rd T (FractionRing T) x]
    show algebraMap Rd (FractionRing T) x ⊗ₜ[Rd] (1 : FractionRing O) =
      (1 : FractionRing T) ⊗ₜ[Rd] algebraMap Rd (FractionRing O) x
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul',
      TensorProduct.tmul_smul]

  have hSfin : (Set.range fun i => ψL (g i)).Finite := Set.finite_range _
  have hSint : ∀ y ∈ Set.range (fun i => ψL (g i)), IsIntegral O y := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨m, hm, hgm⟩ := hint i
    refine ⟨m.map (algebraMap ℤ O), hm.map _, ?_⟩
    rw [eval₂_map, Subsingleton.elim ((algebraMap O _).comp (algebraMap ℤ O)) (ψL.comp (algebraMap ℤ T)),
      ← hom_eval₂, hgm, map_zero]
  let P : Subalgebra O ((FractionRing T ⊗[Rd] FractionRing O) ⧸ 𝔪) :=
    Algebra.adjoin O (Set.range fun i => ψL (g i))
  haveI hfin : Module.Finite O P := Algebra.finite_adjoin_of_finite_of_isIntegral hSfin hSint
  have hOP : Function.Injective (algebraMap O P) := fun x y h => hOL (congrArg Subtype.val h)

  let P' : Subalgebra Rd T :=
    { carrier := {t | ψL t ∈ P}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul] at ha hb ⊢
        exact P.mul_mem ha hb
      one_mem' := by
        simp only [Set.mem_setOf_eq, map_one]
        exact P.one_mem
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
        exact P.add_mem ha hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq, map_zero]
        exact P.zero_mem
      algebraMap_mem' := fun x => by
        simp only [Set.mem_setOf_eq]
        rw [key]
        exact P.algebraMap_mem (φ x) }
  have hP' : ∀ t : T, ψL t ∈ P := by
    intro t
    have ht : t ∈ (⊤ : Subalgebra Rd T) := Algebra.mem_top
    rw [← hgen] at ht
    have hle : Algebra.adjoin Rd (Set.range g) ≤ P' := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨i, rfl⟩
      show ψL (g i) ∈ P
      exact Algebra.subset_adjoin ⟨i, rfl⟩
    exact hle ht
  let ψ : T →+* P := ψL.codRestrict P hP'
  exact ⟨P, inferInstance, inferInstance, inferInstance, hfin, hOP, ψ, fun x => Subtype.ext (key x)⟩

theorem exists_domain_extension_finset {O : Type} [CommRing O] [IsDomain O] [CharZero O]
    (R : Subalgebra ℤ (integralClosure ℤ ℂ)) (s : Finset (integralClosure ℤ ℂ)) (φ : R →+* O) :
    ∃ (P : Type) (_ : CommRing P) (_ : IsDomain P) (_ : Algebra O P) (_ : Module.Finite O P),
      Function.Injective (algebraMap O P) ∧
      ∃ ψ : ↥(R ⊔ Algebra.adjoin ℤ (↑s : Set (integralClosure ℤ ℂ))) →+* P,
        ∀ x : R, ψ (Subalgebra.inclusion le_sup_left x) = algebraMap O P (φ x) := by
  classical
  have hφ : Function.Injective φ := ringHom_injective R φ
  letI alg : Algebra R ↥(R ⊔ Algebra.adjoin ℤ (↑s : Set (integralClosure ℤ ℂ))) :=
    (Subalgebra.inclusion
      (le_sup_left : R ≤ R ⊔ Algebra.adjoin ℤ (↑s : Set (integralClosure ℤ ℂ)))).toRingHom.toAlgebra
  have hRT : Function.Injective (algebraMap R ↥(R ⊔ Algebra.adjoin ℤ (↑s : Set (integralClosure ℤ ℂ)))) := by
    intro x y h
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  let g : ↥s → ↥(R ⊔ Algebra.adjoin ℤ (↑s : Set (integralClosure ℤ ℂ))) := fun a =>
    ⟨(a : integralClosure ℤ ℂ), Algebra.mem_sup_right (Algebra.subset_adjoin (Finset.mem_coe.mpr a.2))⟩
  have hint : ∀ a, IsIntegral ℤ (g a) := by
    intro a
    let f : ↥(R ⊔ Algebra.adjoin ℤ (↑s : Set (integralClosure ℤ ℂ))) →ₐ[ℤ] ℂ :=
      (integralClosure ℤ ℂ).val.comp (R ⊔ Algebra.adjoin ℤ (↑s : Set (integralClosure ℤ ℂ))).val
    have hf : Function.Injective f := fun x y h => Subtype.ext (Subtype.ext h)
    have h1 : IsIntegral ℤ (f (g a)) := (a : integralClosure ℤ ℂ).2
    exact (isIntegral_algHom_iff f hf).mp h1
  have hgen : Algebra.adjoin R (Set.range g) = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    let Q : Subalgebra ℤ (integralClosure ℤ ℂ) :=
      ((Algebra.adjoin R (Set.range g)).restrictScalars ℤ).map
        (R ⊔ Algebra.adjoin ℤ (↑s : Set (integralClosure ℤ ℂ))).val
    have hRQ : R ≤ Q := fun x hx =>
      ⟨algebraMap R _ ⟨x, hx⟩, (Algebra.adjoin R (Set.range g)).algebraMap_mem ⟨x, hx⟩, rfl⟩
    have hsQ : Algebra.adjoin ℤ (↑s : Set (integralClosure ℤ ℂ)) ≤ Q :=
      Algebra.adjoin_le fun a ha =>
        ⟨g ⟨a, Finset.mem_coe.mp ha⟩, Algebra.subset_adjoin ⟨⟨a, Finset.mem_coe.mp ha⟩, rfl⟩, rfl⟩
    have hy : (y : integralClosure ℤ ℂ) ∈ Q := sup_le hRQ hsQ y.2
    obtain ⟨z, hz, hzy⟩ := hy
    have hzy' : z = y := Subtype.ext hzy
    rw [← hzy']
    exact hz
  obtain ⟨P, _, _, _, hfin, hOP, ψ, hψ⟩ := exists_domain_point_gen hRT φ hφ g hgen hint
  exact ⟨P, inferInstance, inferInstance, inferInstance, hfin, hOP, ψ, fun x => hψ x⟩

end DichE

namespace DichR2

private theorem exists_ker_eq_bot_of_iInf_eq_bot {P : Type} [CommRing P] [IsDomain P] {n : ℕ}
    (I : Fin n → Ideal P) (h : ⨅ i, I i = ⊥) : ∃ j, I j = ⊥ := by
  by_contra hne
  push Not at hne
  choose a hamem ha0 using fun j => (Submodule.ne_bot_iff _).mp (hne j)
  have hprod : ∏ j, a j ∈ ⨅ i, I i := Ideal.mem_iInf.mpr fun i => by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    exact Ideal.mul_mem_right _ _ (hamem i)
  rw [h, Ideal.mem_bot] at hprod
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => ha0 j) hprod

private theorem algebraMap_injective_of_isLocalHom
    {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    [Finite (IsLocalRing.ResidueField 𝒪')]
    {A : Type} [CommRing A] [IsDomain A] [CharZero A] [Algebra 𝒪' A]
    [IsLocalHom (algebraMap 𝒪' A)] :
    Function.Injective (algebraMap 𝒪' A) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hker

  obtain ⟨-, P₀, -, huniq⟩ := (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime 𝒪').mp ‹_›
  have h𝔪 : (IsLocalRing.maximalIdeal 𝒪').IsPrime := inferInstance
  have heqm : RingHom.ker (algebraMap 𝒪' A) = IsLocalRing.maximalIdeal 𝒪' :=
    (huniq _ ⟨hker, RingHom.ker_isPrime _⟩).trans
      (huniq _ ⟨IsDiscreteValuationRing.not_a_field 𝒪', h𝔪⟩).symm

  let ℓ := ringChar (IsLocalRing.ResidueField 𝒪')
  have hℓ0 : ℓ ≠ 0 :=
    CharP.char_ne_zero_of_finite (IsLocalRing.ResidueField 𝒪') ℓ
  have hℓm : (ℓ : 𝒪') ∈ IsLocalRing.maximalIdeal 𝒪' := by
    have : (ℓ : IsLocalRing.ResidueField 𝒪') = 0 := CharP.cast_eq_zero _ ℓ
    rwa [← map_natCast (IsLocalRing.residue 𝒪'), IsLocalRing.residue_eq_zero_iff] at this
  have hℓA : (ℓ : A) = 0 := by
    have hk : (ℓ : 𝒪') ∈ RingHom.ker (algebraMap 𝒪' A) := heqm ▸ hℓm
    have := RingHom.mem_ker.mp hk; rwa [map_natCast] at this
  exact hℓ0 (Nat.cast_eq_zero.mp hℓA)

end DichR2

theorem solution
    {𝒪' : Type} [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪') 𝒪'] [Finite (IsLocalRing.ResidueField 𝒪')]
    [CharZero 𝒪'] {p : ℕ} (hp𝒪' : (p : 𝒪') ∈ IsLocalRing.maximalIdeal 𝒪')
    (R : Subalgebra ℤ (integralClosure ℤ ℂ)) (s : Finset (integralClosure ℤ ℂ))
    (φ : R →+* 𝒪') :
    ∃ (𝒪'' : Type) (_ : CommRing 𝒪'') (_ : IsDomain 𝒪'') (_ : IsDiscreteValuationRing 𝒪'')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪'') 𝒪'')
      (_ : Finite (IsLocalRing.ResidueField 𝒪'')) (_ : CharZero 𝒪'')
      (_ : Algebra 𝒪' 𝒪'') (_ : Module.Finite 𝒪' 𝒪'') (_ : IsLocalHom (algebraMap 𝒪' 𝒪'')),
      (p : 𝒪'') ∈ IsLocalRing.maximalIdeal 𝒪'' ∧
      Function.Injective (algebraMap 𝒪' 𝒪'') ∧
      ∃ φ' : ↥(R ⊔ Algebra.adjoin ℤ (↑s : Set (integralClosure ℤ ℂ))) →+* 𝒪'',
        ∀ x : R, φ' (Subalgebra.inclusion le_sup_left x) = algebraMap 𝒪' 𝒪'' (φ x) := by

  obtain ⟨P, iP1, iP2, iP3, iP4, hinj, ψ, hψ⟩ :=
    DichE.exists_domain_extension_finset R s φ
  letI := iP1; haveI := iP2; letI := iP3; haveI := iP4

  haveI : IsLocalRing P :=
    IsLocalRing.of_isDomain_of_module_finite_of_isAdicComplete (R := 𝒪') (S := P)

  haveI : Module.IsTorsionFree 𝒪' P :=
    Module.IsTorsionFree.of_smul_eq_zero fun r m hrm => by
      rw [Algebra.smul_def] at hrm
      exact (mul_eq_zero.mp hrm).imp_left fun h0 => hinj (by simpa using h0)

  obtain ⟨n, A, iA1, iA2, iA3, iA4, iA5, iA6, iA7, iA8, iA9, χ, hχloc, hker, -⟩ :=
    IsLocalRing.exists_fin_points_dvr_iInf_ker_eq_bot (𝒪 := 𝒪') (P := P)

  obtain ⟨j, hj⟩ := DichR2.exists_ker_eq_bot_of_iInf_eq_bot _ hker

  letI := iA1 j; haveI := iA2 j; haveI := iA3 j; haveI := iA4 j; haveI := iA5 j
  haveI := iA6 j; letI := iA7 j; haveI := iA8 j; haveI := iA9 j
  have hp'' : (p : A j) ∈ IsLocalRing.maximalIdeal (A j) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hp𝒪' ⊢
    exact fun hu => hp𝒪' ((iA9 j).1 _ (by simpa using hu))
  exact ⟨A j, iA1 j, iA2 j, iA3 j, iA4 j, iA5 j, iA6 j, iA7 j, iA8 j, iA9 j, hp'',
    DichR2.algebraMap_injective_of_isLocalHom, (χ j).toRingHom.comp ψ,
    fun x => by rw [RingHom.comp_apply, hψ]; exact (χ j).commutes _⟩

end S_IntegralClosure_exists_extend_ringHom_dvr_finite
end P2MW
export P2MW.S_IntegralClosure_exists_extend_ringHom_dvr_finite (solution)
