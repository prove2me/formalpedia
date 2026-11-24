-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.intO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:13:16.41933+00:00
-- url     : https://prove2.me/submissions/04ff7b39-438a-4084-a26f-7288907451da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralIntegersUnramifiedInvolutionExt
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_intO_lift_of_val_nonneg
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_intO_val_algebraMap_nonneg
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_intO_val_ne_zero_of_mem
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_val_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_exists_pow_mem_map_maximalIdeal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_isLocalRing_finite_domain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial IsLocalRing
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → d ≠ 0 → ∀ y : K'.O,
    @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra (algebraMap K'.O K'.E y) := by
  intro K K' d φ hU hd y
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfr : Module.finrank K.E K'.E = d := hU.2.2.2.2
  haveI : FiniteDimensional K.E K'.E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsSeparable K.E K'.E := Algebra.IsSeparable.of_integral _ _
  let S := integralClosure K.O K'.E
  haveI : Module.Finite K.O S := IsIntegralClosure.finite K.O K.E K'.E S
  haveI : IsDedekindDomain S := IsIntegralClosure.isDedekindDomain K.O K.E K'.E S
  haveI : IsFractionRing S K'.E := IsIntegralClosure.isFractionRing_of_finite_extension K.O K.E K'.E S
  haveI : IsLocalRing S := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := K.O) S
  have hinj : Function.Injective (algebraMap K.O S) :=
    algebraMap_injective_of_field_isFractionRing K.O S K.E K'.E
  have hnf : ¬ IsField S := fun h =>
    IsDiscreteValuationRing.not_isField K.O (isField_of_isIntegral_of_isField hinj h)
  haveI : IsDiscreteValuationRing S := ((IsDiscreteValuationRing.TFAE S hnf).out 2 0).1
    (inferInstance : IsDedekindDomain S)

  have hv : ∀ a : K.O, 0 ≤ val K'.O (φ (algebraMap K.O K.E a)) := fun a => by
    rw [hU.2.2.1]; exact intO_val_algebraMap_nonneg K a
  choose ψf hψf using fun a : K.O => intO_lift_of_val_nonneg K' _ (hv a)
  have hinj' : Function.Injective (algebraMap K'.O K'.E) := IsFractionRing.injective _ _
  let ψ : K.O →+* K'.O :=
    { toFun := ψf
      map_one' := hinj' (by rw [hψf]; simp)
      map_mul' := fun a b => hinj' (by simp [hψf])
      map_zero' := hinj' (by rw [hψf]; simp)
      map_add' := fun a b => hinj' (by simp [hψf]) }
  have hψ : ∀ a, algebraMap K'.O K'.E (ψ a) = algebraMap K.O K'.E a := fun a => hψf a

  have hS : ∀ t : K'.E, IsIntegral K.O t → ∃ z : K'.O, algebraMap K'.O K'.E z = t := by
    intro t ht
    have : IsIntegral K'.O t :=
      IsIntegral.map_of_comp_eq (T := K'.O) (U := K'.E) ψ (RingHom.id K'.E) (by ext a; exact hψ a) ht
    exact IsIntegrallyClosed.isIntegral_iff.1 this
  set x := algebraMap K'.O K'.E y with hx
  rcases ValuationRing.isInteger_or_isInteger S x with ⟨s, hs⟩ | ⟨s, hs⟩
  · rw [← hs]; exact s.2
  by_cases hx0 : x = 0
  · rw [hx0]; exact isIntegral_zero
  by_cases hsu : IsUnit s
  · have hu1 : ((hsu.unit⁻¹ : Sˣ) : S) * s = 1 := by
      have := hsu.unit.inv_mul; rwa [IsUnit.unit_spec] at this
    have e : algebraMap S K'.E ((hsu.unit⁻¹ : Sˣ) : S) * algebraMap S K'.E s = 1 := by
      rw [← map_mul, hu1, map_one]
    have : x = algebraMap S K'.E ((hsu.unit⁻¹ : Sˣ) : S) := by
      rw [eq_inv_of_mul_eq_one_left e, hs, inv_inv]
    rw [this]; exact ((hsu.unit⁻¹ : Sˣ) : S).2
  exfalso
  have hall : ∀ n : Ideal S, n.IsMaximal → s ∈ n := fun n hn => by
    rw [IsLocalRing.eq_maximalIdeal hn]; exact (mem_maximalIdeal s).2 hsu
  obtain ⟨N, -, hN⟩ := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.exists_pow_mem_map_maximalIdeal (R := K.O) S s hall
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hN
  obtain ⟨t, ht⟩ := hN
  obtain ⟨z, hz⟩ := hS _ t.2
  have h1 : algebraMap K'.O K'.E (y ^ N * (ψ π * z)) = 1 := by
    have := congrArg (algebraMap S K'.E) ht
    rw [map_mul, map_pow, hs, ← IsScalarTower.algebraMap_apply] at this
    have h' : (t : K'.E) * algebraMap K.O K'.E π = x⁻¹ ^ N := this
    rw [map_mul, map_pow, map_mul, hψ, hz, ← hx, mul_comm (algebraMap K.O K'.E π), h', ← mul_pow,
      mul_inv_cancel₀ hx0, one_pow]
  have hu : IsUnit (ψ π) := by
    have : y ^ N * (ψ π * z) = 1 := hinj' (by rw [h1, map_one])
    exact IsUnit.of_mul_eq_one (z * y ^ N) (by rw [← this]; ring)
  have h2 := GlobalTheory.UnitLemma.Orbit.val_unit (K := K') _ hu
  rw [hψ] at h2
  have h3 := hU.2.2.1 (algebraMap K.O K.E π)
  change val K'.O (φ (algebraMap K.O K.E π)) = 0 at h2
  rw [h3] at h2
  exact intO_val_ne_zero_of_mem K π hπ.ne_zero hπ.not_isUnit h2
end GlobalTheory.UnitLemma.Unr
