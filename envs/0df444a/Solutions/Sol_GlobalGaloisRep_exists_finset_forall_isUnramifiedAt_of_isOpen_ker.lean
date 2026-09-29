-- Prove2me | solution 1 for GlobalGaloisRep.exists_finset_forall_isUnramifiedAt_of_isOpen_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/d64f0220-8587-534f-9428-36337282720b

import Mathlib
import Definitions.Def_GaloisRep_GlobalUnramifiedAt
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ValuationSubring_exists_inertiaSubgroup_restrictNormal_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GlobalGaloisRep_exists_finset_forall_isUnramifiedAt_of_isOpen_ker

open scoped Pointwise NumberField

namespace S18
namespace Unram

open IsLocalRing

attribute [local instance] Ideal.Quotient.field

theorem coe_ringOfIntegers_mem {L : Type*} [Field L] [NumberField L] (S : ValuationSubring L)
    (b : 𝓞 L) : (b : L) ∈ S := by
  have hint : IsIntegral ℤ (b : L) := b.2
  have hintS : IsIntegral S (b : L) := hint.tower_top
  have hv : S.valuation.Integers S :=
    { hom_inj := Subtype.val_injective
      map_le_one := fun x => S.valuation_le_one x
      exists_of_le_one := fun x hx => ⟨⟨x, (S.valuation_le_one_iff x).mp hx⟩, rfl⟩ }
  have := hv.mem_of_integral hintS
  exact (S.valuation_le_one_iff _).mp this

theorem isUnramifiedAt_of_not_dvd_discr (K : Type*) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime)
    (h : ¬ (p : ℤ) ∣ NumberField.discr K) (P : Ideal (𝓞 K)) [hPmax : P.IsMaximal]
    (hpP : ((p : ℤ) : 𝓞 K) ∈ P) : Algebra.IsUnramifiedAt ℤ P := by
  classical
  by_contra hram
  apply h
  have hdvd : P ∣ differentIdeal ℤ (𝓞 K) := by
    by_contra hnd
    exact hram (not_dvd_differentIdeal_iff.mp hnd)
  have hpint : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  haveI hspmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hp0).mpr hpint).isMaximal
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hp0)
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨hspmax.eq_of_le (Ideal.comap_ne_top _ hPmax.ne_top) ?_⟩
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_comap.mpr (by simpa using hpP)
  have hN := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd)
  rw [NumberField.absNorm_differentIdeal (K := K) (𝒪 := 𝓞 K), Ideal.absNorm_eq_pow_inertiaDeg' P hp] at hN
  have hf : 0 < (Ideal.span {(p : ℤ)}).inertiaDeg' P := Ideal.inertiaDeg'_pos _ _
  exact Int.natCast_dvd.mpr ((dvd_pow_self p hf.ne').trans hN)

theorem inertia_eq_one_of_not_dvd_discr (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    {p : ℕ} (hp : p.Prime) (hdisc : ¬ (p : ℤ) ∣ NumberField.discr L)
    (S : ValuationSubring L) (hS : ((p : ℕ) : S) ∈ maximalIdeal S)
    (τ : S.decompositionSubgroup ℚ) (hτ : τ ∈ S.inertiaSubgroup ℚ) :
    (τ : L ≃ₐ[ℚ] L) = 1 := by
  classical

  let ι : 𝓞 L →+* S :=
    { toFun := fun b => ⟨(b : L), coe_ringOfIntegers_mem S b⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  let P : Ideal (𝓞 L) := (maximalIdeal S).comap ι
  haveI hPprime : P.IsPrime := Ideal.comap_isPrime ι (maximalIdeal S)
  have hpP : ((p : ℤ) : 𝓞 L) ∈ P := by
    show ι ((p : ℤ) : 𝓞 L) ∈ maximalIdeal S
    rw [map_intCast]
    simpa using hS
  have hP0 : P ≠ ⊥ := by
    intro h
    have h1 : ((p : ℤ) : 𝓞 L) = 0 := by rw [← Ideal.mem_bot, ← h]; exact hpP
    exact (Int.cast_ne_zero.mpr (by exact_mod_cast hp.ne_zero)) h1
  haveI hPmax : P.IsMaximal := hPprime.isMaximal hP0

  have hunr : Algebra.IsUnramifiedAt ℤ P := isUnramifiedAt_of_not_dvd_discr L hp hdisc P hpP

  have hτP : (τ : L ≃ₐ[ℚ] L) ∈ P.inertia (L ≃ₐ[ℚ] L) := by
    rw [Ideal.inertia, AddSubgroup.mem_inertia]
    intro b
    show ι ((τ : L ≃ₐ[ℚ] L) • b - b) ∈ maximalIdeal S
    have hsmul : ι ((τ : L ≃ₐ[ℚ] L) • b) = τ • ι b := Subtype.ext rfl
    rw [map_sub, hsmul]
    have h1 : MulSemiringAction.toRingAut (S.decompositionSubgroup ℚ) (ResidueField S) τ = 1 := hτ
    have h2 := RingEquiv.ext_iff.mp h1 (residue S (ι b))
    have h4 : residue S (τ • ι b) = residue S (ι b) := by
      rw [ResidueField.residue_smul]
      exact h2
    exact Ideal.Quotient.eq.mp h4

  have hp0 : P.under ℤ ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hP0
  haveI : (P.under ℤ).IsMaximal := Ideal.IsMaximal.under ℤ P
  haveI : P.LiesOver (P.under ℤ) := ⟨rfl⟩
  have : Finite (ℤ ⧸ P.under ℤ) := Ring.HasFiniteQuotients.finiteQuotient hp0
  have : Finite (𝓞 L ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  have c1 := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[ℚ] L) (P.under ℤ) P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) P (L ≃ₐ[ℚ] L),
    Algebra.isUnramifiedAt_iff_of_isDedekindDomain.mp hunr] at c1
  have hbot : P.inertia (L ≃ₐ[ℚ] L) = ⊥ := Subgroup.eq_bot_of_card_eq _ c1
  rw [hbot] at hτP
  exact Subgroup.mem_bot.mp hτP

end S18.Unram

open S18.Unram in
theorem solution
    {G : Type*} [Group G] (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* G)
    (hker : IsOpen ((ρ.ker : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
      Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) :
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → GlobalGaloisRep.IsUnramifiedAt ρ p := by
  classical

  haveI hnorm : Normal ℚ (AlgebraicClosure ℚ) := by
    have h : @Normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
    exact h

  obtain ⟨L, hLfin, hLnorm, hLker⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal ℚ (AlgebraicClosure ℚ) _).mp
      (hker.mem_nhds ρ.ker.one_mem)
  haveI := hLfin
  haveI := hLnorm
  haveI : IsGalois ℚ L := @IsGalois.mk ℚ _ L _ _ inferInstance hLnorm
  haveI : NumberField L := NumberField.mk
  refine ⟨(NumberField.discr L).natAbs.primeFactors, fun p hp hpS A hA => ?_⟩
  have hdisc : ¬ (p : ℤ) ∣ NumberField.discr L := by
    intro h
    apply hpS
    rw [Nat.mem_primeFactors]
    exact ⟨hp, Int.natCast_dvd.mp h, Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero L)⟩

  set S : ValuationSubring L := A.comap (algebraMap L (AlgebraicClosure ℚ)) with hSdef
  let ιSA : S →+* A :=
    RingHom.codRestrict ((algebraMap L (AlgebraicClosure ℚ)).comp S.subtype) A.toSubring
      (fun x => ValuationSubring.mem_comap.mp x.2)
  have hpA : ((p : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
    refine ValuationSubring.coe_mem_nonunits_iff.mp ?_
    rw [show (((p : ℕ) : A) : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) by simp]
    exact hA
  have hpS' : ((p : ℕ) : S) ∈ IsLocalRing.maximalIdeal S := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 := hu.map ιSA
    rw [map_natCast] at h1
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp hpA) h1

  intro σ hσ
  obtain ⟨σ', hσ'I, rfl⟩ := hσ
  obtain ⟨τ, hτ⟩ := ValuationSubring.exists_inertiaSubgroup_restrictNormal_eq L A ⟨σ', hσ'I⟩
  have h1 : ((τ : S.decompositionSubgroup ℚ) : L ≃ₐ[ℚ] L) = 1 :=
    inertia_eq_one_of_not_dvd_discr L hp hdisc S hpS' τ.1 τ.2
  have hres : AlgEquiv.restrictNormalHom L (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = 1 := by
    rw [← h1]
    exact hτ.symm
  have hfix : ((σ' : A.decompositionSubgroup ℚ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈
      L.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker]
    exact hres
  exact hLker hfix

end S_GlobalGaloisRep_exists_finset_forall_isUnramifiedAt_of_isOpen_ker
end P2MW
export P2MW.S_GlobalGaloisRep_exists_finset_forall_isUnramifiedAt_of_isOpen_ker (solution)
