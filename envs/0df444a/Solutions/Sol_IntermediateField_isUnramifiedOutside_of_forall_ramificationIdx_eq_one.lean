-- Prove2me | solution 1 for IntermediateField.isUnramifiedOutside_of_forall_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/85a68fb5-a0e3-52eb-a7c7-58ebc94cc95b

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_isUnramifiedOutside_of_forall_ramificationIdx_eq_one

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand ExtCitation
open scoped Classical

namespace Bridge

section Generic

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

private theorem exists_smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroupIn (A : ValuationSubring E) {σ : E ≃ₐ[K] E}
    (hσ : σ ∈ A.inertiaSubgroupIn K) (a : A) :
    ∃ h : σ (a : E) ∈ A, (⟨σ (a : E), h⟩ : A) - a ∈ IsLocalRing.maximalIdeal A := by
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hσ
  refine ⟨(d • a : A).2, ?_⟩
  have hd' : MulSemiringAction.toRingAut (↥(ValuationSubring.decompositionSubgroup K A)) (IsLocalRing.ResidueField A) d = 1 :=
    (MonoidHom.mem_ker).mp hd
  have h1 : IsLocalRing.residue A (d • a) = IsLocalRing.residue A a := by
    rw [IsLocalRing.ResidueField.residue_smul]
    show (MulSemiringAction.toRingEquiv _ (IsLocalRing.ResidueField A) d) (IsLocalRing.residue A a) = _
    rw [← MulSemiringAction.toRingAut_apply, hd']
    rfl
  exact Ideal.Quotient.eq.mp h1

end Generic

end Bridge

namespace Bridge

section Place

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (A : ValuationSubring (AlgebraicClosure ℚ))

private theorem coe_coe_mem (x : 𝓞 ↥F) : ((x : ↥F) : AlgebraicClosure ℚ) ∈ A := by

  obtain ⟨p, hp, hpx⟩ := x.isIntegral_coe
  have hx : IsIntegral ↥A ((x : ↥F) : AlgebraicClosure ℚ) := by
    refine ⟨p.map (Int.castRingHom ↥A), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, Subsingleton.elim ((algebraMap ↥A (AlgebraicClosure ℚ)).comp (Int.castRingHom ↥A))
      ((algebraMap ↥F (AlgebraicClosure ℚ)).comp (algebraMap ℤ ↥F))]
    have h2 := congrArg (algebraMap ↥F (AlgebraicClosure ℚ)) hpx
    rw [Polynomial.hom_eval₂, map_zero] at h2
    exact h2
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
  rw [← hz]; exact z.2

private noncomputable def toPlace : 𝓞 ↥F →+* ↥A where
  toFun x := ⟨((x : ↥F) : AlgebraicClosure ℚ), coe_coe_mem F A x⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[scoped simp] private theorem coe_toPlace (x : 𝓞 ↥F) : ((toPlace F A x : ↥A) : AlgebraicClosure ℚ) = ((x : ↥F) : AlgebraicClosure ℚ) := rfl

end Place

end Bridge
p2m_reactivate "P2MW.S_IntermediateField_isUnramifiedOutside_of_forall_ramificationIdx_eq_one.Bridge"

set_option synthInstance.maxHeartbeats 1600000 in
open Bridge in

theorem solution
    (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] (hL : L.IsUnramifiedOutside S)
    [IsGalois ↥L ↥(IntermediateField.extendScalars hLF)]
    (h : ∀ w : HeightOneSpectrum (𝓞 ↥F), w ∉ NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes) →
      letI := (IntermediateField.inclusion hLF).toRingHom.toAlgebra
      Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ↥L)) w.asIdeal = 1) :
    F.IsUnramifiedOutside S := by
  classical
  letI algLF : Algebra ↥L ↥F := (IntermediateField.inclusion hLF).toRingHom.toAlgebra
  refine ⟨inferInstance, fun q hqS A hA σ hσ => ?_⟩
  have hq : (q : ℕ).Prime := q.2

  have hσL : σ ∈ L.fixingSubgroup := hL.2 q hqS A hA hσ

  haveI : NumberField ↥L := @NumberField.mk _ _ inferInstance inferInstance
  haveI : NumberField ↥F := @NumberField.mk _ _ inferInstance inferInstance
  haveI : IsScalarTower ↥L ↥F (AlgebraicClosure ℚ) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ℚ ↥L ↥F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FiniteDimensional ↥L ↥F := Module.Finite.of_restrictScalars_finite ℚ ↥L ↥F
  let e : ↥(IntermediateField.extendScalars hLF) →ₐ[↥L] ↥F :=
    { toFun := fun x => ⟨(x : AlgebraicClosure ℚ), (IntermediateField.mem_extendScalars hLF).1 x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  haveI : IsGalois ↥L ↥F := IsGalois.of_algEquiv (AlgEquiv.ofBijective e
    ⟨fun x y hxy => Subtype.ext (congrArg Subtype.val hxy), fun y => ⟨⟨(y : AlgebraicClosure ℚ), (IntermediateField.mem_extendScalars hLF).2 y.2⟩, rfl⟩⟩)

  let σL : AlgebraicClosure ℚ ≃ₐ[↥L] AlgebraicClosure ℚ :=
    { σ with commutes' := fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσL x x.2 }
  have hσL_apply : ∀ x, σL x = σ x := fun _ => rfl
  let τ : ↥F ≃ₐ[↥L] ↥F := σL.restrictNormal ↥F
  have hτ : ∀ x : ↥F, ((τ x : ↥F) : AlgebraicClosure ℚ) = σ x := fun x =>
    (AlgEquiv.restrictNormal_commutes σL ↥F x).trans (hσL_apply _)

  set w₀ : Ideal (𝓞 ↥F) := (IsLocalRing.maximalIdeal ↥A).comap (toPlace F A) with hw₀def
  haveI hw₀prime : w₀.IsPrime := Ideal.comap_isPrime _ _
  have hqw : ((q : ℕ) : 𝓞 ↥F) ∈ w₀ := by
    rw [hw₀def, Ideal.mem_comap, map_natCast, ← ValuationSubring.coe_mem_nonunits_iff]
    simpa [ValuationSubring.LiesOverPrime] using hA
  have hw₀bot : w₀ ≠ ⊥ := fun h0 => by
    have : ((q : ℕ) : 𝓞 ↥F) = 0 := by simpa [h0] using hqw
    exact hq.ne_zero (by exact_mod_cast this)
  let w : HeightOneSpectrum (𝓞 ↥F) := ⟨w₀, hw₀prime, hw₀bot⟩
  have hwS : w ∉ NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes) := by
    rintro ⟨p, hpS, hpw⟩
    have hpq : (p : ℕ) ≠ q := fun hh => hqS (by rwa [show p = q from Subtype.ext hh] at hpS)
    have hcop : Nat.Coprime p q := (Nat.coprime_primes p.2 hq).mpr hpq
    apply hw₀prime.ne_top
    rw [Ideal.eq_top_iff_one]
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have h1 : (1 : 𝓞 ↥F) = (u : 𝓞 ↥F) * ((p : ℕ) : 𝓞 ↥F) + (v : 𝓞 ↥F) * ((q : ℕ) : 𝓞 ↥F) := by
      have := congrArg (Int.cast : ℤ → 𝓞 ↥F) huv
      push_cast at this
      exact this.symm
    rw [h1]
    exact w₀.add_mem (w₀.mul_mem_left _ hpw) (w₀.mul_mem_left _ hqw)
  have he : Ideal.ramificationIdx' (w₀.under (𝓞 ↥L)) w₀ = 1 := h w hwS

  have hτI : τ ∈ w₀.inertia (↥F ≃ₐ[↥L] ↥F) := by
    intro x
    show τ • x - x ∈ w₀
    rw [hw₀def, Ideal.mem_comap, map_sub]
    obtain ⟨hmem, hsub⟩ := exists_smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroupIn A hσ (toPlace F A x)
    convert hsub using 2
    apply Subtype.ext
    simp only [coe_toPlace]
    exact (hτ (x : ↥F))

  haveI : IsScalarTower (𝓞 ↥L) (𝓞 ↥F) ↥F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite (𝓞 ↥L) (𝓞 ↥F) := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : Algebra.IsIntegral (𝓞 ↥L) (𝓞 ↥F) := Algebra.IsIntegral.of_finite _ _
  haveI : Finite (↥F ≃ₐ[↥L] ↥F) := inferInstance
  haveI hGG : IsGaloisGroup (↥F ≃ₐ[↥L] ↥F) (𝓞 ↥L) (𝓞 ↥F) :=
    IsGaloisGroup.of_isFractionRing (↥F ≃ₐ[↥L] ↥F) (𝓞 ↥L) (𝓞 ↥F) ↥L ↥F
  set v : Ideal (𝓞 ↥L) := w₀.under (𝓞 ↥L) with hvdef
  haveI : w₀.LiesOver v := ⟨rfl⟩
  have hv0 : v ≠ ⊥ := fun h0 => hw₀bot (Ideal.eq_bot_of_comap_eq_bot h0)
  haveI hw₀max : w₀.IsMaximal := hw₀prime.isMaximal hw₀bot
  haveI : v.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hv0
  letI : Field (𝓞 ↥L ⧸ v) := Ideal.Quotient.field v
  letI : Field (𝓞 ↥F ⧸ w₀) := Ideal.Quotient.field w₀
  haveI : Finite (𝓞 ↥F ⧸ w₀) := Ideal.finiteQuotientOfFreeOfNeBot w₀ hw₀bot
  haveI : Finite (𝓞 ↥L ⧸ v) := Ideal.finiteQuotientOfFreeOfNeBot v hv0
  haveI : Algebra.IsAlgebraic (𝓞 ↥L ⧸ v) (𝓞 ↥F ⧸ w₀) := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable (𝓞 ↥L ⧸ v) (𝓞 ↥F ⧸ w₀) := inferInstance
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := ↥F ≃ₐ[↥L] ↥F) v w₀
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v w₀ (↥F ≃ₐ[↥L] ↥F),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (p := v) (q := w₀) hv0, hvdef, he] at hcard
  have hτ1 : τ = 1 := by
    have hbot := Subgroup.eq_bot_of_card_eq _ hcard
    rw [hbot] at hτI
    exact Subgroup.mem_bot.mp hτI

  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hfin := hτ ⟨x, hx⟩
  rw [hτ1, AlgEquiv.one_apply] at hfin
  exact hfin.symm

end S_IntermediateField_isUnramifiedOutside_of_forall_ramificationIdx_eq_one
end P2MW
export P2MW.S_IntermediateField_isUnramifiedOutside_of_forall_ramificationIdx_eq_one (solution)
