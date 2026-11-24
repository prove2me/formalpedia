-- Prove2me | solution 1 for GlobalTheory.FlatThickenings.mem_pow_of_flat_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:27:10.364132+00:00
-- url     : https://prove2.me/submissions/3d4bf66b-ae81-49d4-965b-665a86952cdb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPushoutQuotientMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_MemPowOfFlatQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FlatThickenings
namespace GlobalTheory.FlatThickenings
theorem _root_.solution {V C : Type} [CommRing V] [IsDomain V] [CommRing C] (σ : V →+* C)
    {ϖ : V} (hϖ : ϖ ≠ 0) (I : Ideal V) (hI : I = Ideal.span {ϖ}) (e : ℕ)
    (h : (Ideal.quotientMap ((I ^ (e + 1)).map σ) σ (Ideal.le_comap_map (I := I ^ (e + 1)))).Flat)
    {a : C} (ha : σ ϖ * a = 0) : a ∈ Ideal.span {σ ϖ} ^ e := by
  set φ := Ideal.quotientMap ((I ^ (e + 1)).map σ) σ (Ideal.le_comap_map (I := I ^ (e + 1))) with hφ
  let _ := φ.toAlgebra
  have : Module.Flat (V ⧸ I ^ (e + 1)) (C ⧸ (I ^ (e + 1)).map σ) := h
  have hsm : ∀ (v : V) (c : C), (Ideal.Quotient.mk (I ^ (e + 1)) v) •
      (Ideal.Quotient.mk ((I ^ (e + 1)).map σ) c) = Ideal.Quotient.mk _ (σ v * c) := by
    intro v c
    rw [Algebra.smul_def, map_mul]
    rfl
  obtain ⟨l, c, y, hy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
    (R := V ⧸ I ^ (e + 1)) (M := C ⧸ (I ^ (e + 1)).map σ)
    (f := fun _ : Unit => Ideal.Quotient.mk _ ϖ) (x := fun _ => Ideal.Quotient.mk _ a)
    (by rw [Fintype.sum_unique, hsm, ha, map_zero])
  choose c' hc' using fun j => Ideal.Quotient.mk_surjective (c () j)
  choose y' hy' using fun j => Ideal.Quotient.mk_surjective (y j)
  have hd : ∀ j, ϖ ^ e ∣ c' j := by
    intro j
    have h1 := hc j
    rw [Fintype.sum_unique, ← hc', ← map_mul, Ideal.Quotient.eq_zero_iff_mem, hI,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_succ'] at h1
    exact (mul_dvd_mul_iff_left hϖ).1 h1
  have h2 : a - ∑ j, σ (c' j) * y' j ∈ (I ^ (e + 1)).map σ := by
    rw [← Ideal.Quotient.eq, map_sum]
    refine (hy ()).trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hc', ← hy', hsm]
  rw [hI, Ideal.map_pow, Ideal.map_span, Set.image_singleton] at h2
  have h3 : ∑ j, σ (c' j) * y' j ∈ Ideal.span {σ ϖ} ^ e := by
    refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ ?_
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← map_pow]
    exact map_dvd σ (hd j)
  simpa using Ideal.add_mem _ (Ideal.pow_le_pow_right (Nat.le_succ e) h2) h3
end GlobalTheory.FlatThickenings
