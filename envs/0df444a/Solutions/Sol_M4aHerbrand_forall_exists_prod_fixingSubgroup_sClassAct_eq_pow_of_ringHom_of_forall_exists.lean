-- Prove2me | solution 1 for M4aHerbrand.forall_exists_prod_fixingSubgroup_sClassAct_eq_pow_of_ringHom_of_forall_exists
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/5ffe32d7-1951-58e5-b490-c0a73a86f134

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_unitsAct_map_genuineBaseChange
import Theorems.Thm_M4aHerbrand_GenuineDescent_map_beta_unitIdelesTrivialOn_placesOverPrimes_le
import Theorems.Thm_M4aHerbrand_GenuineDescent_unitsMap_beta_mem_principalIdeles_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_forall_exists_prod_fixingSubgroup_sClassAct_eq_pow_of_ringHom_of_forall_exists

set_option autoImplicit false
p2m_open "NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_forall_exists_prod_fixingSubgroup_sClassAct_eq_pow_of_ringHom_of_forall_exists.M4aHerbrand ExtCitation"
open scoped Classical

noncomputable section

namespace M4aHerbrand
p2m_export "M4aHerbrand" "IdeleGaloisDescent sClassKernel SIdeleClassGroup principalIdeles_le_sClassKernel unitIdelesTrivialOn_le_sClassKernel IdeleGaloisDescent.sClassAct_mk GenuineDescent.injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm IdeleGaloisDescent.unitsAct_map_genuineBaseChange GenuineDescent.map_beta_unitIdelesTrivialOn_placesOverPrimes_le GenuineDescent.unitsMap_beta_mem_principalIdeles_iff"
p2m_open "M4aHerbrand"

namespace TowerPrime

open M4aHerbrand.GenuineDescent

section OfTower

variable {R E E' L : Type*} [CommRing R] [IsDedekindDomain R] [Field E] [Field E'] [Field L]
  [Algebra R L] [IsFractionRing R L] [Algebra E L] [Algebra E' L] [Algebra E E'] [IsScalarTower E E' L]

variable (E) in

def resHom : (L ≃ₐ[E'] L) →* (L ≃ₐ[E] L) where
  toFun g := g.restrictScalars E
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

@[scoped simp] lemma resHom_apply (g : L ≃ₐ[E'] L) : resHom E g = g.restrictScalars E := rfl

variable (E') in

def ofTower (D : IdeleGaloisDescent R E L) : IdeleGaloisDescent R E' L where
  act := D.act.comp (resHom E)
  compat g x := D.compat (g.restrictScalars E) x
  continuous_act g := D.continuous_act (g.restrictScalars E)

@[scoped simp] lemma ofTower_act (D : IdeleGaloisDescent R E L) (g : L ≃ₐ[E'] L) :
    (ofTower E' D).act g = D.act (g.restrictScalars E) := rfl

@[scoped simp] lemma unitsAct_ofTower (D : IdeleGaloisDescent R E L) (g : L ≃ₐ[E'] L) :
    (ofTower E' D).unitsAct g = D.unitsAct (g.restrictScalars E) := rfl

lemma stabilizes_ofTower (D : IdeleGaloisDescent R E L) {T : Set (HeightOneSpectrum R)}
    (hD : D.StabilizesUnitIdeles T) : (ofTower E' D).StabilizesUnitIdeles T :=
  fun g x hx => hD (g.restrictScalars E) x hx

lemma sClassAct_ofTower (D : IdeleGaloisDescent R E L) {T : Set (HeightOneSpectrum R)}
    (hD : D.StabilizesUnitIdeles T) (g : L ≃ₐ[E'] L) (c : SIdeleClassGroup R L T) :
    (ofTower E' D).sClassAct (stabilizes_ofTower D hD) g c = D.sClassAct hD (g.restrictScalars E) c := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  rfl

omit [Algebra E E'] [IsScalarTower E E' L] in

def liftOfFix (σ : L ≃ₐ[E] L) (h : ∀ x : E', σ (algebraMap E' L x) = algebraMap E' L x) : L ≃ₐ[E'] L :=
  AlgEquiv.ofRingEquiv (f := (σ : L ≃+* L)) h

omit [Algebra E E'] [IsScalarTower E E' L] in
@[scoped simp] lemma liftOfFix_apply (σ : L ≃ₐ[E] L) (h : ∀ x : E', σ (algebraMap E' L x) = algebraMap E' L x) (y : L) :
    liftOfFix σ h y = σ y := rfl

@[scoped simp] lemma restrictScalars_liftOfFix (σ : L ≃ₐ[E] L) (h : ∀ x : E', σ (algebraMap E' L x) = algebraMap E' L x) :
    (liftOfFix σ h).restrictScalars E = σ := by ext; rfl

@[scoped simp] lemma liftOfFix_restrictScalars (τ : L ≃ₐ[E'] L) (h) :
    liftOfFix (τ.restrictScalars E) h = τ := by ext; rfl

end OfTower

section Ker

variable {K F₀ M : Type*} [Field K] [Field F₀] [Field M] [Algebra K F₀] [Algebra K M] [Algebra F₀ M]
  [IsScalarTower K F₀ M] [Normal K F₀]

lemma restrictNormalHom_eq_one_iff (σ : M ≃ₐ[K] M) :
    AlgEquiv.restrictNormalHom F₀ σ = 1 ↔ ∀ x : F₀, σ (algebraMap F₀ M x) = algebraMap F₀ M x := by
  constructor
  · intro h x
    have := AlgEquiv.restrictNormal_commutes σ F₀ x
    rw [show σ.restrictNormal F₀ = AlgEquiv.restrictNormalHom F₀ σ from rfl, h] at this
    exact this.symm
  · intro h
    ext x
    apply (algebraMap F₀ M).injective
    rw [show AlgEquiv.restrictNormalHom F₀ σ = σ.restrictNormal F₀ from rfl, AlgEquiv.restrictNormal_commutes]
    exact h x

lemma restrictNormalHom_restrictScalars (τ : M ≃ₐ[F₀] M) :
    AlgEquiv.restrictNormalHom F₀ (τ.restrictScalars K) = 1 :=
  (restrictNormalHom_eq_one_iff _).2 fun x => τ.commutes x

def fiberEquiv (j : F₀ ≃ₐ[K] F₀) (s : M ≃ₐ[K] M) (hs : AlgEquiv.restrictNormalHom F₀ s = j) :
    (M ≃ₐ[F₀] M) ≃ {σ : M ≃ₐ[K] M // AlgEquiv.restrictNormalHom F₀ σ = j} where
  toFun τ := ⟨s * τ.restrictScalars K, by rw [map_mul, hs, restrictNormalHom_restrictScalars, mul_one]⟩
  invFun σ := liftOfFix (s⁻¹ * σ.1) ((restrictNormalHom_eq_one_iff _).1
      (by rw [map_mul, map_inv, σ.2, hs, inv_mul_cancel]))
  left_inv τ := by
    ext x
    simp only [liftOfFix_apply, AlgEquiv.mul_apply]
    change s⁻¹ (s (τ x)) = τ x
    exact s.symm_apply_apply (τ x)
  right_inv σ := by
    apply Subtype.ext
    ext x
    change s ((s⁻¹ * σ.1) x) = σ.1 x
    rw [AlgEquiv.mul_apply]
    exact s.apply_symm_apply (σ.1 x)

end Ker

section Iota

variable (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
  (S : Set Nat.Primes)

abbrev βu : (AdeleRing (𝓞 E) E)ˣ →* (AdeleRing (𝓞 F) F)ˣ :=
  Units.map ((genuineBaseChange E F).β : AdeleRing (𝓞 E) E →+* AdeleRing (𝓞 F) F).toMonoidHom

lemma sClassKernel_le_comap_βu :
    sClassKernel (𝓞 E) E (NumberField.placesOverPrimes E S) ≤
      (sClassKernel (𝓞 F) F (NumberField.placesOverPrimes F S)).comap (βu E F) := by
  refine sup_le ?_ ?_
  · intro x hx
    exact principalIdeles_le_sClassKernel _ _ _
      ((M4aHerbrand.GenuineDescent.unitsMap_beta_mem_principalIdeles_iff E F x).mpr hx)
  · intro x hx
    exact unitIdelesTrivialOn_le_sClassKernel _ _ _
      (M4aHerbrand.GenuineDescent.map_beta_unitIdelesTrivialOn_placesOverPrimes_le E F S ⟨x, hx, rfl⟩)

def ι : SIdeleClassGroup (𝓞 E) E (NumberField.placesOverPrimes E S) →*
    SIdeleClassGroup (𝓞 F) F (NumberField.placesOverPrimes F S) :=
  QuotientGroup.map _ _ (βu E F) (sClassKernel_le_comap_βu E F S)

@[scoped simp] lemma ι_mk (x : (AdeleRing (𝓞 E) E)ˣ) :
    ι E F S (QuotientGroup.mk x) = QuotientGroup.mk (βu E F x) := rfl

end Iota

end TowerPrime
p2m_reactivate "P2MW.S_M4aHerbrand_forall_exists_prod_fixingSubgroup_sClassAct_eq_pow_of_ringHom_of_forall_exists.M4aHerbrand.TowerPrime"

end M4aHerbrand
p2m_reactivate "P2MW.S_M4aHerbrand_forall_exists_prod_fixingSubgroup_sClassAct_eq_pow_of_ringHom_of_forall_exists.M4aHerbrand.TowerPrime P2MW.S_M4aHerbrand_forall_exists_prod_fixingSubgroup_sClassAct_eq_pow_of_ringHom_of_forall_exists.M4aHerbrand"

end
p2m_reactivate "P2MW.S_M4aHerbrand_forall_exists_prod_fixingSubgroup_sClassAct_eq_pow_of_ringHom_of_forall_exists.M4aHerbrand.TowerPrime P2MW.S_M4aHerbrand_forall_exists_prod_fixingSubgroup_sClassAct_eq_pow_of_ringHom_of_forall_exists.M4aHerbrand"

open M4aHerbrand.TowerPrime M4aHerbrand.GenuineDescent

theorem solution
    {p : ℕ} (S : Finset Nat.Primes)
    (L' F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L' ≤ F) [NumberField ↥L'] [NumberField ↥F] [IsGalois ℚ ↥F]
    (F₀ : Type) [Field F₀] [NumberField F₀] [Algebra ↥L' F₀] [IsGalois ↥L' F₀]
    (e : F₀ →+* ↥F) (he : ∀ x : ↥L', e (algebraMap ↥L' F₀ x) = IntermediateField.inclusion hLF x)
    (D₀ : IdeleGaloisDescent (𝓞 F₀) ↥L' F₀) (hD₀ : D₀.StabilizesUnitIdeles (NumberField.placesOverPrimes F₀ (↑S : Set Nat.Primes)))
    (h₀ : ∀ c₀ : SIdeleClassGroup (𝓞 F₀) F₀ (NumberField.placesOverPrimes F₀ (↑S : Set Nat.Primes)),
      ∃ d₀ : SIdeleClassGroup (𝓞 F₀) F₀ (NumberField.placesOverPrimes F₀ (↑S : Set Nat.Primes)),
        (∀ g : F₀ ≃ₐ[↥L'] F₀, D₀.sClassAct hD₀ g d₀ = d₀) ∧ (∏ᶠ g : F₀ ≃ₐ[↥L'] F₀, D₀.sClassAct hD₀ g c₀) = d₀ ^ p)
    (D : IdeleGaloisDescent (𝓞 ↥F) ℚ ↥F) (hD : D.StabilizesUnitIdeles (NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes)))
    (c : SIdeleClassGroup (𝓞 ↥F) ↥F (NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes))) :
    ∃ d : SIdeleClassGroup (𝓞 ↥F) ↥F (NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes)),
      (∀ g ∈ ((IntermediateField.inclusion hLF).fieldRange).fixingSubgroup, D.sClassAct hD g d = d) ∧
      (∏ g : ↥((IntermediateField.inclusion hLF).fieldRange).fixingSubgroup,
          D.sClassAct hD g.1 c) = d ^ p := by

  letI algKM : Algebra ↥L' ↥F := (IntermediateField.inclusion hLF).toRingHom.toAlgebra
  have algKM_eq : ∀ y : ↥L', algebraMap ↥L' ↥F y = IntermediateField.inclusion hLF y := fun _ => rfl
  haveI : IsScalarTower ℚ ↥L' ↥F :=
    IsScalarTower.of_algebraMap_eq fun q => ((IntermediateField.inclusion hLF).commutes q).symm
  letI algF₀M : Algebra F₀ ↥F := e.toAlgebra
  haveI : IsScalarTower ↥L' F₀ ↥F := IsScalarTower.of_algebraMap_eq fun x => (he x).symm
  haveI : IsScalarTower ℚ F₀ ↥F := IsScalarTower.of_algebraMap_eq fun q =>
    (RingHom.congr_fun (RingHom.ext_rat ((algebraMap F₀ ↥F).comp (algebraMap ℚ F₀)) (algebraMap ℚ ↥F)) q).symm
  haveI : IsGalois ↥L' ↥F := IsGalois.tower_top_of_isGalois ℚ ↥L' ↥F
  haveI : IsGalois F₀ ↥F := IsGalois.tower_top_of_isGalois ↥L' F₀ ↥F
  have hDK : (ofTower ↥L' D).StabilizesUnitIdeles (NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes)) :=
    stabilizes_ofTower (E' := ↥L') D hD

  have key4 := (M4aHerbrand.GenuineDescent.injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm
    F₀ ↥F (ofTower F₀ D)).2.2.2
  have inter := M4aHerbrand.IdeleGaloisDescent.unitsAct_map_genuineBaseChange ↥L' F₀ ↥F D₀ (ofTower ↥L' D)

  have hfix : ∀ σ : ↥F ≃ₐ[↥L'] ↥F,
      σ.restrictScalars ℚ ∈ ((IntermediateField.inclusion hLF).fieldRange).fixingSubgroup := by
    intro σ
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 ?_
    rintro x hx
    obtain ⟨y, rfl⟩ := (AlgHom.mem_fieldRange).1 hx
    exact σ.commutes y
  have hfix' : ∀ g ∈ ((IntermediateField.inclusion hLF).fieldRange).fixingSubgroup,
      ∀ y : ↥L', g (algebraMap ↥L' ↥F y) = algebraMap ↥L' ↥F y := by
    intro g hg y
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _ ((AlgHom.mem_fieldRange).2 ⟨y, rfl⟩)
  let Φ : (↥F ≃ₐ[↥L'] ↥F) ≃ ↥((IntermediateField.inclusion hLF).fieldRange).fixingSubgroup :=
    { toFun := fun σ => ⟨σ.restrictScalars ℚ, hfix σ⟩
      invFun := fun g => liftOfFix g.1 (hfix' g.1 g.2)
      left_inv := fun σ => by ext; rfl
      right_inv := fun g => by apply Subtype.ext; ext; rfl }

  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨d₀, hd₀fix, hd₀⟩ := h₀ (QuotientGroup.mk ((genuineBaseChange F₀ ↥F).idelicNorm u))
  refine ⟨ι F₀ ↥F ↑S d₀, ?_, ?_⟩
  ·
    intro g hg
    obtain ⟨σ, rfl⟩ : ∃ σ : ↥F ≃ₐ[↥L'] ↥F, σ.restrictScalars ℚ = g :=
      ⟨liftOfFix g (hfix' g hg), restrictScalars_liftOfFix _ _⟩
    obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective d₀
    rw [ι_mk, IdeleGaloisDescent.sClassAct_mk]
    change (QuotientGroup.mk ((ofTower ↥L' D).unitsAct σ (βu F₀ ↥F y₀)) :
        SIdeleClassGroup (𝓞 ↥F) ↥F (NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes))) = _
    rw [inter σ y₀, ← ι_mk F₀ ↥F ↑S, ← IdeleGaloisDescent.sClassAct_mk D₀ hD₀, hd₀fix]
    rfl
  ·

    have ha : (∏ g : ↥((IntermediateField.inclusion hLF).fieldRange).fixingSubgroup, D.sClassAct hD g.1
          (QuotientGroup.mk u : SIdeleClassGroup (𝓞 ↥F) ↥F (NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes))))
        = QuotientGroup.mk (∏ σ : ↥F ≃ₐ[↥L'] ↥F, (ofTower ↥L' D).unitsAct σ u) := by
      simp only [IdeleGaloisDescent.sClassAct_mk]
      rw [← QuotientGroup.mk_prod]
      congr 1
      refine (Fintype.prod_equiv Φ _ _ fun σ => ?_).symm
      rw [unitsAct_ofTower]
      rfl

    have hb : (∏ σ : ↥F ≃ₐ[↥L'] ↥F, (ofTower ↥L' D).unitsAct σ u)
        = βu F₀ ↥F (∏ j : F₀ ≃ₐ[↥L'] F₀, D₀.unitsAct j ((genuineBaseChange F₀ ↥F).idelicNorm u)) := by
      rw [← Fintype.prod_fiberwise (fun σ : ↥F ≃ₐ[↥L'] ↥F => AlgEquiv.restrictNormalHom F₀ σ)
        (fun σ => (ofTower ↥L' D).unitsAct σ u), map_prod]
      refine Finset.prod_congr rfl fun j _ => ?_
      obtain ⟨s, hs⟩ := AlgEquiv.restrictNormalHom_surjective ↥F j
      calc (∏ σ : {σ : ↥F ≃ₐ[↥L'] ↥F // AlgEquiv.restrictNormalHom F₀ σ = j}, (ofTower ↥L' D).unitsAct σ.1 u)
          = ∏ τ : ↥F ≃ₐ[F₀] ↥F, (ofTower ↥L' D).unitsAct s ((ofTower F₀ D).unitsAct τ u) := by
            refine (Fintype.prod_equiv (fiberEquiv j s hs) _ _ fun τ => ?_).symm
            change _ = (ofTower ↥L' D).unitsAct (s * τ.restrictScalars ↥L') u
            rw [map_mul, MulAut.mul_apply]
            rfl
        _ = (ofTower ↥L' D).unitsAct s (∏ τ : ↥F ≃ₐ[F₀] ↥F, (ofTower F₀ D).unitsAct τ u) :=
            (map_prod ((ofTower ↥L' D).unitsAct s) _ _).symm
        _ = (ofTower ↥L' D).unitsAct s (βu F₀ ↥F ((genuineBaseChange F₀ ↥F).idelicNorm u)) := by
            rw [key4 u]
        _ = βu F₀ ↥F (D₀.unitsAct (AlgEquiv.restrictNormalHom F₀ s) ((genuineBaseChange F₀ ↥F).idelicNorm u)) :=
            inter s _
        _ = βu F₀ ↥F (D₀.unitsAct j ((genuineBaseChange F₀ ↥F).idelicNorm u)) := by rw [hs]

    have hc : (QuotientGroup.mk (βu F₀ ↥F (∏ j : F₀ ≃ₐ[↥L'] F₀, D₀.unitsAct j ((genuineBaseChange F₀ ↥F).idelicNorm u))) :
        SIdeleClassGroup (𝓞 ↥F) ↥F (NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes))) = (ι F₀ ↥F ↑S d₀) ^ p := by
      have h1 : (∏ᶠ g : F₀ ≃ₐ[↥L'] F₀, D₀.sClassAct hD₀ g
            (QuotientGroup.mk ((genuineBaseChange F₀ ↥F).idelicNorm u) :
              SIdeleClassGroup (𝓞 F₀) F₀ (NumberField.placesOverPrimes F₀ (↑S : Set Nat.Primes))))
          = QuotientGroup.mk (∏ j : F₀ ≃ₐ[↥L'] F₀, D₀.unitsAct j ((genuineBaseChange F₀ ↥F).idelicNorm u)) := by
        rw [finprod_eq_prod_of_fintype]
        simp only [IdeleGaloisDescent.sClassAct_mk]
        exact (QuotientGroup.mk_prod _ _).symm
      rw [← ι_mk, ← h1, hd₀, map_pow]
    rw [ha, hb, hc]

end S_M4aHerbrand_forall_exists_prod_fixingSubgroup_sClassAct_eq_pow_of_ringHom_of_forall_exists
end P2MW
export P2MW.S_M4aHerbrand_forall_exists_prod_fixingSubgroup_sClassAct_eq_pow_of_ringHom_of_forall_exists (solution)
