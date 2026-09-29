-- Prove2me | solution 1 for NumberField.SUnits.exists_ihom_extension_fixed_of_sLevel_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/ca60192e-a76f-514e-b36b-6c73ee42a777

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Theorems.Thm_IntermediateField_isUnramifiedOutside_sup_adjoin_of_pow_eq
import Theorems.Thm_NumberField_SUnits_algebraMap_mem_and_inv_mem_of_mem_sUnits_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_SUnits_exists_ihom_extension_fixed_of_sLevel_of_injective
set_option autoImplicit false
set_option maxHeartbeats 3200000
open CategoryTheory NumberField IsDedekindDomain ExtCitation

namespace GlobalHyp

universe u
variable {k : Type} [CommRing k] {H : Type} [Group H] {D : Type} [Group D] (π : H →* D)

def homAdd {V W : Rep.{0} k D} (χ : V ⟶ W) : V →+ W := χ.hom.toLinearMap.toAddMonoidHom
lemma homAdd_apply {V W : Rep.{0} k D} (χ : V ⟶ W) (v : V) : homAdd χ v = χ.hom v := rfl

def toIntLinearMapOfModules {V W : Type} [AddCommGroup V] [AddCommGroup W] (instV : Module ℤ V) (instW : Module ℤ W)
    (u : V →+ W) : @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) V W _ _ instV instW :=
  @LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) V W _ _ instV instW ⟨u, u.map_add⟩ (fun c m => by
    letI := instV
    letI := instW
    exact map_intCast_smul u ℤ ℤ c m)

lemma exists_extension_of_divisible {Q : Type} [AddCommGroup Q] (hQ : ∀ n : ℕ, n ≠ 0 → ∀ a : Q, ∃ b : Q, n • b = a)
    {V W : Type} [AddCommGroup V] [AddCommGroup W] (f : V →+ W) (hf : Function.Injective f) (φ : V →+ Q) :
    ∃ ψ : W →+ Q, ∀ v : V, ψ (f v) = φ v := by
  letI : DivisibleBy Q ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn a => hQ n hn a
  letI : DivisibleBy Q ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  haveI : Module.Injective ℤ Q := (Module.Baer.of_divisible _).injective
  obtain ⟨ψ, hψ⟩ := Module.Injective.out (Q := Q) f.toIntLinearMap hf φ.toIntLinearMap
  exact ⟨ψ.toAddMonoidHom, hψ⟩

lemma units_algClosure_divisible (n : ℕ) (hn : n ≠ 0) (a : Additive (AlgebraicClosure ℚ)ˣ) :
    ∃ b : Additive (AlgebraicClosure ℚ)ˣ, n • b = a := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul a : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) (Nat.pos_of_ne_zero hn)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hz
    exact (Additive.toMul a).ne_zero hz.symm
  refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  change ((Units.mk0 z hz0 ^ n : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = _
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz]

end GlobalHyp

open GlobalHyp in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    {R P B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)} (f : R ⟶ P) (g : P ⟶ B)
    (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
    [Module.Finite ℤ P] (hB : ∀ b : B, p • b = 0)
    (ιE : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE : ∀ x, Additive.toMul (ιE x) = Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x)) :
    ∀ φ : R →+ NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ,
      ∃ ψ : (ihom (Rep.res (AlgEquiv.restrictNormalHom ↥F) P)).obj (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)),
        (∀ x : R, LinearMap.toAddMonoidHom ψ (f.hom x) = ιE (φ x)) ∧
        ∃ F₂ : IntermediateField ℚ (AlgebraicClosure ℚ), F₂.IsUnramifiedOutside S ∧
          ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, s ∈ F₂.fixingSubgroup →
            ∀ x : P, (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ s (LinearMap.toAddMonoidHom ψ x) = LinearMap.toAddMonoidHom ψ x := by
  classical
  intro φ
  let K := AlgebraicClosure ℚ
  let π : (K ≃ₐ[ℚ] K) →* (↥F ≃ₐ[ℚ] ↥F) := AlgEquiv.restrictNormalHom ↥F
  let A : Rep ℤ (K ≃ₐ[ℚ] K) := Rep.ofAlgebraAutOnUnits ℚ K
  have _ := hg

  have qψ := exists_extension_of_divisible units_algClosure_divisible (homAdd f) hf (ιE.comp φ)
  rcases qψ with ⟨ψ, hψ⟩
  let Ψ : (ihom (Rep.res π P)).obj A := toIntLinearMapOfModules _ _ ψ
  refine ⟨Ψ, fun x => hψ x, ?_⟩

  obtain ⟨s₀, hs₀⟩ := Module.Finite.fg_top (R := ℤ) (M := P)
  have hpx : ∀ x : P, ∃ r : R, f.hom r = p • x := fun x => (hfg (p • x)).1 (by
    change homAdd g (p • x) = 0
    rw [map_nsmul, homAdd_apply]
    exact hB _)
  choose rOf hrOf using hpx
  let u : P → (↥F)ˣ := fun x => NumberField.SUnits.val ℚ ↥F Sℚ (φ (rOf x))
  let α : P → K := fun x => ((Additive.toMul (ψ x) : Kˣ) : K)
  have hα : ∀ x, α x ^ p = algebraMap ↥F K (u x : ↥F) := by
    intro x
    have h1 : ψ (p • x) = ιE (φ (rOf x)) := by rw [← hrOf]; exact hψ (rOf x)
    have h2 := congrArg (fun a => ((Additive.toMul a : Kˣ) : K)) h1
    simp only [map_nsmul, toMul_nsmul, Units.val_pow_eq_pow_val, hιE, Units.coe_map, MonoidHom.coe_coe] at h2
    exact h2
  have hxS : ∀ x, ∀ q : Nat.Primes, q ∉ S → ∀ Av : ValuationSubring K, Av.LiesOverPrime (q : ℕ) →
      algebraMap ↥F K (u x : ↥F) ∈ Av ∧ (algebraMap ↥F K (u x : ↥F))⁻¹ ∈ Av := fun x q hq Av hAv =>
    NumberField.SUnits.algebraMap_mem_and_inv_mem_of_mem_sUnits_of_liesOverPrime S Sℚ hSℚ F (u x)
      (NumberField.SUnits.val_mem ℚ ↥F Sℚ _) q hq Av hAv

  have hF₂ : ∀ t : Finset P, (F ⊔ IntermediateField.adjoin ℚ (α '' (↑t : Set P))).IsUnramifiedOutside S := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      rw [Finset.coe_empty, Set.image_empty, IntermediateField.adjoin_empty, sup_bot_eq]
      exact hF
    | insert x t hxt ih =>
      rw [Finset.coe_insert, Set.image_insert_eq, Set.insert_eq, IntermediateField.adjoin_union,
        sup_comm (IntermediateField.adjoin ℚ {α x}), ← sup_assoc]
      exact IntermediateField.isUnramifiedOutside_sup_adjoin_of_pow_eq S (pPrime p) hpS _ ih (algebraMap ↥F K (u x : ↥F))
        ((le_sup_left : F ≤ F ⊔ IntermediateField.adjoin ℚ (α '' ↑t)) (u x : ↥F).2) (hxS x) (α x) (hα x)
  refine ⟨F ⊔ IntermediateField.adjoin ℚ (α '' (↑s₀ : Set P)), hF₂ s₀, fun s hs => ?_⟩

  have hfixgen : ∀ x ∈ s₀, A.ρ s (ψ x) = ψ x := by
    intro x hx
    have hsα : s (α x) = α x := by
      rw [IntermediateField.mem_fixingSubgroup_iff] at hs
      exact hs _ ((le_sup_right : _ ≤ F ⊔ IntermediateField.adjoin ℚ (α '' ↑s₀)) (IntermediateField.subset_adjoin ℚ _ ⟨x, hx, rfl⟩))
    apply Additive.toMul.injective
    apply Units.ext
    exact hsα
  intro x
  change A.ρ s (ψ x) = ψ x
  have hxmem : x ∈ (Submodule.span ℤ (↑s₀ : Set P)).toAddSubgroup := by rw [hs₀]; trivial
  rw [Submodule.span_int_eq_addSubgroupClosure] at hxmem
  induction hxmem using AddSubgroup.closure_induction with
  | mem y hy => exact hfixgen y hy
  | zero =>
    rw [map_zero]
    exact map_zero (A.ρ s)
  | add y z _ _ hy hz =>
    rw [map_add]
    refine (map_add (A.ρ s) _ _).trans ?_
    rw [hy, hz]
    rfl
  | neg y _ hy =>
    rw [map_neg]
    refine (map_neg (A.ρ s) _).trans ?_
    rw [hy]
    rfl

end S_NumberField_SUnits_exists_ihom_extension_fixed_of_sLevel_of_injective
end P2MW
export P2MW.S_NumberField_SUnits_exists_ihom_extension_fixed_of_sLevel_of_injective (solution)
