-- Prove2me | solution 1 for GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:39:44.233497+00:00
-- url     : https://prove2.me/submissions/fcec15fb-49d2-403d-a3c5-40a64ac616b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaPointsVanishingIdealRadicalHomogeneous
import Theorems.Thm_GlobalTheory_ZM_ThIdeal_hasTh_unit_mul
import Theorems.Thm_GlobalTheory_ZM_ThIdeal_component_eq_zero
import Theorems.Thm_GlobalTheory_ZM_ThIdeal_mem_thIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.ThIdeal
namespace GlobalTheory.ZM.ThIdeal
theorem _root_.solution :
    ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop), Function.Injective em → (thIdeal em C).IsRadical ∧ (∀ F ∈ thIdeal em C, ∀ e, MvPolynomial.homogeneousComponent e F ∈ thIdeal em C) ∧ ∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ thIdeal em C → F ∈ thIdeal em C := by
  intro o _ g N' J b em C hem
  refine ⟨fun F hF => ?_, fun F hF e => ?_, fun c F hc hF => ?_⟩
  · obtain ⟨n, hn⟩ := hF
    rw [mem_thIdeal] at hn ⊢
    intro t v ht hv
    have := hn t v ht hv
    rw [map_pow] at this
    exact pow_eq_zero_iff'.mp this |>.1
  · rw [mem_thIdeal] at hF ⊢
    intro t v ht hv
    exact component_eq_zero em v F e fun c hc => hF t _ ht (hasTh_unit_mul hv c hc.isUnit)
  · rw [mem_thIdeal] at hF ⊢
    intro t v ht hv
    have := hF t v ht hv
    rw [map_mul, MvPolynomial.eval₂Hom_C] at this
    exact (mul_eq_zero.mp this).resolve_left ((map_ne_zero_iff em hem).mpr hc)
end GlobalTheory.ZM.ThIdeal
