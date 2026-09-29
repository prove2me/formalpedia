-- Prove2me | solution 1 for IntermediateField.exists_forall_norm_ne_of_isCyclic_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/cd4cbd75-092d-5e88-bde3-11e03e2fcb84

import Mathlib
import Definitions.Def_GroupCohomology_CyclicCarry
import Theorems.Thm_ExtCitation_LocalLevel_natCard_H2_units_eq_natCard_of_isCyclic
import Theorems.Thm_groupCohomology_exists_carry_H2pi_eq
import Theorems.Thm_groupCohomology_carry_H2pi_eq_zero_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_exists_forall_norm_ne_of_isCyclic_padic
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology

theorem solution
    (q : ℕ) [Fact q.Prime] (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (L : IntermediateField K (PadicAlgCl q)) [FiniteDimensional K L] [IsGalois K L]
    (hcyc : IsCyclic (L ≃ₐ[K] L)) (hL : Module.finrank K L ≠ 1) :
    ∃ a : (↥K)ˣ, ∀ w : L, Algebra.norm K w ≠ (a : K) := by
  classical
  by_contra hall
  have hall' : ∀ a : (↥K)ˣ, ∃ w : L, Algebra.norm K w = (a : K) := fun a => by
    by_contra h
    exact hall ⟨a, fun w hw => h ⟨w, hw⟩⟩

  let L' : IntermediateField ℚ_[q] (PadicAlgCl q) := IntermediateField.restrictScalars ℚ_[q] L
  haveI : FiniteDimensional ℚ_[q] L := Module.Finite.trans K L
  let eL : L ≃ₗ[ℚ_[q]] L' :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI hfdL' : FiniteDimensional ℚ_[q] L' := LinearEquiv.finiteDimensional eL
  letI iMSA : MulSemiringAction (L ≃ₐ[K] L) L' := (inferInstance : MulSemiringAction (L ≃ₐ[K] L) L)
  haveI iFS : FaithfulSMul (L ≃ₐ[K] L) L' := (inferInstance : FaithfulSMul (L ≃ₐ[K] L) L)
  letI iMDA : MulDistribMulAction (L ≃ₐ[K] L) (↥L')ˣ := (inferInstance : MulDistribMulAction (L ≃ₐ[K] L) (↥L)ˣ)
  have hGq : ∀ (g : L ≃ₐ[K] L) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x := by
    intro g x
    show g (algebraMap ℚ_[q] L x) = algebraMap ℚ_[q] L x
    rw [IsScalarTower.algebraMap_apply ℚ_[q] K L, AlgEquiv.commutes]
  have hcompat : ∀ (g : L ≃ₐ[K] L) (u : (↥L')ˣ), ((g • u : (↥L')ˣ) : L') = g • (u : L') := fun _ _ => rfl
  haveI : IsCyclic (L ≃ₐ[K] L) := hcyc
  have hcard := ExtCitation.LocalLevel.natCard_H2_units_eq_natCard_of_isCyclic q L' (L ≃ₐ[K] L) hGq hcompat

  let A : Rep ℤ (L ≃ₐ[K] L) := Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (↥L')ˣ
  obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  have hfin : IsOfFinOrder s := isOfFinOrder_of_finite s

  have hzero : ∀ c : H2 A, c = 0 := by
    intro c
    induction c using H2_induction_on with | h c =>
    obtain ⟨hb, hz, hcarry⟩ := groupCohomology.exists_carry_H2pi_eq s hs hfin c
    show (H2π A).hom c = 0
    rw [← hcarry, groupCohomology.carry_H2pi_eq_zero_iff s hs hfin _ hb hz]
    let u : (↥L')ˣ := Additive.toMul (cyclicInv s (⇑c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → A))
    have hsu : s • u = u := by
      have h1 : A.ρ s (cyclicInv s (⇑c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → A)) = cyclicInv s (⇑c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → A) := hb
      rw [Rep.ofMulDistribMulAction_ρ_apply_apply] at h1
      exact Additive.ofMul.injective h1
    have hfix : ∀ g : L ≃ₐ[K] L, g • u = u := by
      intro g
      have hstab : s ∈ MulAction.stabilizer (L ≃ₐ[K] L) u := hsu
      exact (Subgroup.zpowers_le.2 hstab) (hs g)

    let uL : L := ⟨((u : L') : PadicAlgCl q), (u : L').2⟩
    have huK : uL ∈ (⊥ : IntermediateField K L) := by
      rw [IsGalois.mem_bot_iff_fixed]
      intro f
      exact congrArg (fun v : (↥L')ˣ => (v : L')) (hfix f)
    obtain ⟨a₀, ha₀⟩ := IntermediateField.mem_bot.1 huK
    have ha₀0 : a₀ ≠ 0 := by
      rintro rfl
      apply u.ne_zero
      rw [map_zero] at ha₀
      exact ha₀.symm

    obtain ⟨w, hw⟩ := hall' (Units.mk0 a₀ ha₀0)
    rw [Units.val_mk0] at hw
    have hw0 : w ≠ 0 := by
      intro h
      have hprod := Algebra.norm_eq_prod_automorphisms K w
      rw [hw, h, Finset.prod_eq_zero (Finset.mem_univ (1 : L ≃ₐ[K] L)) (map_zero _), map_eq_zero] at hprod
      exact ha₀0 hprod
    let wu : (↥L')ˣ := Units.mk0 (w : L') hw0
    refine ⟨Additive.ofMul wu, ?_⟩

    show (∑ i ∈ Finset.range (orderOf s), Additive.ofMul ((s ^ i) • wu) : Additive ((↥L')ˣ)) = Additive.ofMul u
    rw [← ofMul_prod]
    congr 1
    apply Units.ext
    rw [Units.coe_prod]

    have himage : (Finset.univ : Finset (L ≃ₐ[K] L)) = (Finset.range (orderOf s)).image (fun i => s ^ i) := by
      ext g
      simp only [Finset.mem_univ, true_iff]
      exact (hfin.mem_zpowers_iff_mem_range_orderOf).1 (hs g)
    have hinj : ∀ i ∈ Finset.range (orderOf s), ∀ j ∈ Finset.range (orderOf s), s ^ i = s ^ j → i = j :=
      fun i hi j hj h => pow_injOn_Iio_orderOf (by simpa using hi) (by simpa using hj) h
    have huval : ((u : (↥L')ˣ) : L') = uL := rfl
    rw [huval, ← ha₀, ← hw, Algebra.norm_eq_prod_automorphisms K w, himage, Finset.prod_image hinj]
    rfl

  have h1 : Nat.card (H2 A) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun x y => by rw [hzero x, hzero y]⟩, ⟨0⟩⟩
  apply hL
  rw [← IsGalois.card_aut_eq_finrank K L, ← hcard]
  exact h1

end S_IntermediateField_exists_forall_norm_ne_of_isCyclic_padic
end P2MW
export P2MW.S_IntermediateField_exists_forall_norm_ne_of_isCyclic_padic (solution)
