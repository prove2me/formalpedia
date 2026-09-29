-- Prove2me | solution 1 for IntermediateField.exists_norm_eq_of_nnnorm_eq_one_adjoin_rootsOfUnity_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/d4812bd2-4dfc-58da-9f2a-3629039db2ac

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_LocalRing_PrincipalUnits
import Definitions.Def_GroupCohomology_CyclicCarry
import Theorems.Thm_IntermediateField_finiteDimensional_normal_adjoin_rootsOfUnity_padic
import Theorems.Thm_IntermediateField_exists_generator_frobenius_adjoin_rootsOfUnity_padic
import Theorems.Thm_IntermediateField_exists_norm_eq_adjoin_rootsOfUnity_padic
import Theorems.Thm_ExtCitation_LocalLevel_exists_subgroup_units_forall_isMulCocycle
import Theorems.Thm_groupCohomology_natCard_H1_eq_natCard_H2_ofMulDistribMulAction_of_subgroup
import Theorems.Thm_groupCohomology_subsingleton_H1_ofMulDistribMulAction
import Theorems.Thm_groupCohomology_carryFun_mem_cocycles2
import Theorems.Thm_groupCohomology_carry_H2pi_eq_zero_iff
import Theorems.Thm_ExtCitation_LocalLevel_exists_valuation_units_Kw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_exists_norm_eq_of_nnnorm_eq_one_adjoin_rootsOfUnity_padic

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1600000
open IntermediateField
open scoped NNReal

namespace Ws26T4D
open ExtCitation.LocalLevel

variable (q : ℕ) [Fact q.Prime] (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]

theorem mem_Rw_iff_norm_le_one (x : Kw) : x ∈ Rw q Kw ↔ ‖(x : PadicAlgCl q)‖ ≤ 1 := by
  rw [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff, PadicAlgCl.valuation_def]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

theorem norm_coe_eq_spectralNorm (x : Kw) : ‖(x : PadicAlgCl q)‖ = spectralNorm ℚ_[q] Kw x := by
  rw [spectralNorm.eq_of_tower (L := PadicAlgCl q), PadicAlgCl.spectralNorm_eq]; rfl

end Ws26T4D

set_option maxHeartbeats 0 in
open Ws26T4D ExtCitation.LocalLevel IsLocalRing groupCohomology in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (N : ℕ) (hN : 0 < N)
    [FiniteDimensional K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})]
    (u : K) (hu : ‖(u : PadicAlgCl q)‖ = 1) :
    ∃ w : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}), Algebra.norm K w = u := by
  classical
  set L := IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1} with hL
  haveI : Normal K L := (IntermediateField.finiteDimensional_normal_adjoin_rootsOfUnity_padic q K N hN).2
  obtain ⟨φ, hφ, -⟩ := IntermediateField.exists_generator_frobenius_adjoin_rootsOfUnity_padic q K N hN
  have hunram : ∀ x : L, x ≠ 0 → ∃ y : K, ‖(x : PadicAlgCl q)‖ = ‖((y : PadicAlgCl q))‖ :=
    fun x hx => IntermediateField.exists_norm_eq_adjoin_rootsOfUnity_padic q K N hN x hx
  haveI : IsGalois K L := ⟨⟩

  set L' : IntermediateField ℚ_[q] (PadicAlgCl q) := L.restrictScalars ℚ_[q] with hL'
  haveI : FiniteDimensional ℚ_[q] L := Module.Finite.trans K L
  haveI : FiniteDimensional ℚ_[q] L' := (inferInstance : FiniteDimensional ℚ_[q] L)

  letI actL' : MulSemiringAction (L ≃ₐ[K] L) L' := (inferInstance : MulSemiringAction (L ≃ₐ[K] L) L)
  haveI : FaithfulSMul (L ≃ₐ[K] L) L' := (inferInstance : FaithfulSMul (L ≃ₐ[K] L) L)
  letI actU : MulDistribMulAction (L ≃ₐ[K] L) (↥L')ˣ := Units.mulDistribMulActionRight
  have hcompat : ∀ (g : L ≃ₐ[K] L) (x : (↥L')ˣ), ((g • x : (↥L')ˣ) : L') = g • (x : L') := fun _ _ => rfl
  have hact : ∀ (g : L ≃ₐ[K] L) (x : L'), g • x = (g (x : L) : L) := fun _ _ => rfl
  have hG : ∀ (g : L ≃ₐ[K] L) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x := by
    intro g x
    show g (algebraMap ℚ_[q] L x) = algebraMap ℚ_[q] L x
    rw [IsScalarTower.algebraMap_apply ℚ_[q] K L, AlgEquiv.commutes]

  obtain ⟨U, V, hU, hUG, hVU, hVG, hfin, -, hV1, hV2⟩ :=
    ExtCitation.LocalLevel.exists_subgroup_units_forall_isMulCocycle q L' (L ≃ₐ[K] L) hG hcompat
  haveI := hfin
  haveI : IsCyclic (L ≃ₐ[K] L) := ⟨⟨φ, hφ⟩⟩

  obtain ⟨v, hvsurj, hvker, -, -⟩ := ExtCitation.LocalLevel.exists_valuation_units_Kw q L'
  have hnorm_one_iff : ∀ x : (↥L')ˣ, v x = 1 ↔ ‖((x : L') : PadicAlgCl q)‖ = 1 := by
    intro x
    rw [hvker, mem_Rw_iff_norm_le_one, mem_Rw_iff_norm_le_one]
    have hx0 : ((x : L') : PadicAlgCl q) ≠ 0 := by
      intro h; exact x.ne_zero (by exact_mod_cast h)
    have hinv : ((((x⁻¹ : (↥L')ˣ) : L') : PadicAlgCl q)) = (((x : L') : PadicAlgCl q))⁻¹ := by
      rw [Units.val_inv_eq_inv_val]; push_cast; rfl
    rw [hinv, norm_inv]
    constructor
    · rintro ⟨h1, h2⟩
      exact le_antisymm h1 ((inv_le_one₀ (norm_pos_iff.mpr hx0)).mp h2)
    · intro h; rw [h, inv_one]; exact ⟨le_rfl, le_rfl⟩
  have hU' : ∀ x : (↥L')ˣ, x ∈ U ↔ ‖((x : L') : PadicAlgCl q)‖ = 1 := fun x =>
    (hU x).trans ((hvker x).symm.trans (hnorm_one_iff x))

  obtain ⟨y₀, hy₀⟩ := hvsurj (Multiplicative.ofAdd 1)
  have hy₀ne : ((y₀ : L') : L) ≠ 0 := fun h => y₀.ne_zero h
  obtain ⟨πK, hπK⟩ := hunram (y₀ : L') hy₀ne
  have hπK0 : πK ≠ 0 := by
    intro h
    rw [h] at hπK
    have : ((y₀ : L') : PadicAlgCl q) = 0 := by
      rw [← norm_eq_zero, hπK]; simp
    exact y₀.ne_zero (by exact_mod_cast this)
  have hπL0 : (algebraMap K L πK : L) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap K L).injective]; exact hπK0
  set π : (↥L')ˣ := Units.mk0 (algebraMap K L πK : L) hπL0 with hπdef
  have hπfix : ∀ g : L ≃ₐ[K] L, g • π = π := fun g => by
    apply Units.ext
    show g (algebraMap K L πK) = algebraMap K L πK
    exact g.commutes πK
  have hvπ : v π = Multiplicative.ofAdd 1 := by

    have h1 : v (y₀ / π) = 1 := by
      rw [hnorm_one_iff]
      have : (((y₀ / π : (↥L')ˣ) : L') : PadicAlgCl q) = ((y₀ : L') : PadicAlgCl q) / ((π : L') : PadicAlgCl q) := by
        rw [Units.val_div_eq_div_val]; push_cast; rfl
      rw [this, norm_div, hπK]
      have hπcoe : ((π : L') : PadicAlgCl q) = (πK : PadicAlgCl q) := rfl
      rw [hπcoe, div_self]
      rw [norm_ne_zero_iff]
      exact fun h => hπK0 (by exact_mod_cast h)
    rw [_root_.map_div, div_eq_one] at h1
    rw [← h1, hy₀]

  have hU1 : ∀ f : (L ≃ₐ[K] L) → (↥L')ˣ, (∀ g, f g ∈ U) → IsMulCocycle₁ f → ∃ x ∈ U, ∀ g, g • x / x = f g := by
    intro f hfU hf
    have hx' : ∃ x : (↥L')ˣ, ∀ g, g • x / x = f g :=
      isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units (K := K) (L := L) f hf
    obtain ⟨x, hx⟩ := hx'
    set m : ℤ := Multiplicative.toAdd (v x) with hm
    refine ⟨x / π ^ m, ?_, fun g => ?_⟩
    · rw [hU', ← hnorm_one_iff, _root_.map_div, map_zpow, hvπ, ← ofAdd_zsmul, smul_eq_mul, mul_one, hm,
        ofAdd_toAdd, div_self']
    · rw [← hx g, smul_div', smul_zpow', hπfix, div_div_div_cancel_right]

  letI actUU : MulDistribMulAction (L ≃ₐ[K] L) ↥U :=
    { smul := fun g x => ⟨g • (x : (↥L')ˣ), hUG g x x.2⟩
      one_smul := fun x => Subtype.ext (one_smul _ (x : (↥L')ˣ))
      mul_smul := fun g h x => Subtype.ext (mul_smul g h (x : (↥L')ˣ))
      smul_mul := fun g x y => Subtype.ext (smul_mul' g (x : (↥L')ˣ) (y : (↥L')ˣ))
      smul_one := fun g => Subtype.ext (smul_one g) }
  have hactUU : ∀ (g : L ≃ₐ[K] L) (x : ↥U), ((g • x : ↥U) : (↥L')ˣ) = g • (x : (↥L')ˣ) := fun _ _ => rfl
  obtain ⟨hfin1, hfin2, hcard⟩ := groupCohomology.natCard_H1_eq_natCard_H2_ofMulDistribMulAction_of_subgroup
    U V hVU hUG hVG hV1 hV2 hactUU

  have hsub1 : Subsingleton (H1 (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) ↥U)) := by
    refine groupCohomology.subsingleton_H1_ofMulDistribMulAction fun f hf => ?_
    have hf' : IsMulCocycle₁ (fun g => ((f g : ↥U) : (↥L')ˣ)) := fun g h => by
      have := congrArg (fun x : ↥U => (x : (↥L')ˣ)) (hf g h)
      simpa only [Subgroup.coe_mul, hactUU] using this
    obtain ⟨x, hxU, hx⟩ := hU1 _ (fun g => (f g).2) hf'
    exact ⟨⟨x, hxU⟩, fun g => Subtype.ext (by rw [Subgroup.coe_div, hactUU]; exact hx g)⟩
  haveI := hfin1
  haveI := hfin2
  have hsub2 : Subsingleton (H2 (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) ↥U)) := by
    have h1 : Nat.card (H1 (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) ↥U)) = 1 := by
      haveI := hsub1; exact Nat.card_unique
    rw [h1] at hcard
    exact (Nat.card_eq_one_iff_unique.mp hcard.symm).1

  have hu0 : (algebraMap K L u : L) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap K L).injective]
    intro h; rw [h] at hu; simp at hu
  set uL : (↥L')ˣ := Units.mk0 (algebraMap K L u : L) hu0 with huL
  have huU : uL ∈ U := by rw [hU']; exact hu
  have hufix : ∀ g : L ≃ₐ[K] L, g • uL = uL := fun g => by
    apply Units.ext
    show g (algebraMap K L u) = algebraMap K L u
    exact g.commutes u

  set A := Rep.ofMulDistribMulAction (L ≃ₐ[K] L) ↥U with hA
  set a : A := Additive.ofMul (⟨uL, huU⟩ : ↥U) with ha
  have hφfin : IsOfFinOrder φ := isOfFinOrder_of_finite φ
  have haφ : A.ρ φ a = a := by
    change Additive.ofMul (φ • (⟨uL, huU⟩ : ↥U)) = Additive.ofMul ⟨uL, huU⟩
    congr 1
    exact Subtype.ext (hufix φ)
  have hcoc := groupCohomology.carryFun_mem_cocycles2 φ hφ hφfin a haφ
  have h0 : (H2π A).hom ⟨carryFun φ hφ hφfin a, hcoc⟩ = 0 := by
    haveI := hsub2; exact Subsingleton.elim _ _
  obtain ⟨b, hb⟩ := (groupCohomology.carry_H2pi_eq_zero_iff φ hφ hφfin a haφ hcoc).mp h0

  set bU : ↥U := Additive.toMul b with hbU
  have hprodU : (∏ i ∈ Finset.range (orderOf φ), (φ ^ i) • bU) = ⟨uL, huU⟩ := by
    have h2 : ∀ i, (A.ρ (φ ^ i)) b = Additive.ofMul ((φ ^ i) • bU) := fun i => rfl
    have h3 : Additive.ofMul (∏ i ∈ Finset.range (orderOf φ), (φ ^ i) • bU) = a := by
      rw [ofMul_prod]
      simp only [← h2]
      exact hb
    exact Additive.ofMul.injective (h3.trans ha)
  set bL : L := (((bU : (↥L')ˣ) : L') : L) with hbL
  have hprodL : (∏ i ∈ Finset.range (orderOf φ), (φ ^ i) bL) = algebraMap K L u := by
    have h1 := congrArg (fun x : ↥U => (((x : (↥L')ˣ) : L') : L)) hprodU
    simp only at h1
    have h2 : ((((∏ i ∈ Finset.range (orderOf φ), (φ ^ i) • bU : ↥U) : (↥L')ˣ) : L') : L)
        = ∏ i ∈ Finset.range (orderOf φ), (φ ^ i) bL := by
      rw [Subgroup.val_finset_prod]
      push_cast
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hactUU, hcompat, hact]
    rw [← h2, h1]
    rfl

  refine ⟨bL, (algebraMap K L).injective ?_⟩
  rw [Algebra.norm_eq_prod_automorphisms, ← hprodL]

  have hinj : Function.Injective (fun i : Fin (orderOf φ) => φ ^ (i : ℕ)) := by
    intro i j h
    exact Fin.ext (pow_injOn_Iio_orderOf i.isLt j.isLt h)
  have hsurj : Function.Surjective (fun i : Fin (orderOf φ) => φ ^ (i : ℕ)) := by
    intro σ
    have hmem : σ ∈ Submonoid.powers φ := by
      rw [mem_powers_iff_mem_zpowers]; exact hφ σ
    rw [mem_powers_iff_mem_range_orderOf] at hmem
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hmem
    exact ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩
  let e : Fin (orderOf φ) ≃ (L ≃ₐ[K] L) := Equiv.ofBijective _ ⟨hinj, hsurj⟩
  rw [← Fin.prod_univ_eq_prod_range (fun i => (φ ^ i) bL) (orderOf φ)]
  exact (Fintype.prod_equiv e (fun i => (φ ^ (i : ℕ)) bL) (fun σ => σ bL) (fun _ => rfl)).symm

end S_IntermediateField_exists_norm_eq_of_nnnorm_eq_one_adjoin_rootsOfUnity_padic
end P2MW
export P2MW.S_IntermediateField_exists_norm_eq_of_nnnorm_eq_one_adjoin_rootsOfUnity_padic (solution)
