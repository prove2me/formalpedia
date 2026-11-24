-- Prove2me | solution 1 for GlobalTheory.ResultantNorm.countP_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:16:43.301312+00:00
-- url     : https://prove2.me/submissions/33a01b15-46e3-47e6-8bf4-03ced87e3da0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEq
import Theorems.Thm_GlobalTheory_ResultantNorm_norm_prod_add

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
open GlobalTheory
open GlobalTheory.ResultantNorm
open Polynomial Filter Topology
variable {K Ω : Type} [NontriviallyNormedField K] [NormedField Ω] [NormedAlgebra K Ω]
namespace GlobalTheory.ResultantNorm
theorem _root_.solution [DecidableEq Ω] (a b : Multiset Ω) (g : Ω → Ω)
    (h : ∀ t : K, ‖(a.map fun x => g x + algebraMap K Ω t).prod‖ =
      ‖(b.map fun x => g x + algebraMap K Ω t).prod‖) :
    b.countP (fun x => g x = 0) ≤ a.countP (fun x => g x = 0) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
  set A : K → ℝ := fun t =>
    ‖((a.filter fun x => ¬ g x = 0).map fun x => g x + algebraMap K Ω t).prod‖ with hA
  set B : K → ℝ := fun t =>
    ‖((b.filter fun x => ¬ g x = 0).map fun x => g x + algebraMap K Ω t).prod‖ with hB
  have hc : ∀ c : Multiset Ω, Continuous fun t : K =>
      ‖(c.map fun x => g x + algebraMap K Ω t).prod‖ := fun c =>
    (continuous_multiset_prod c fun x _ => continuous_const.add (continuous_algebraMap K Ω)).norm
  have hAc : Continuous A := hc _
  have hBc : Continuous fun t : K => ‖t‖ ^ (k + 1) * B t := (continuous_norm.pow _).mul (hc _)
  have heq : Set.EqOn A (fun t : K => ‖t‖ ^ (k + 1) * B t) {0}ᶜ := by
    intro t ht
    have ht0 : ‖t‖ ≠ 0 := norm_ne_zero_iff.2 ht
    have := h t
    rw [norm_prod_add a, norm_prod_add b, hk, add_assoc, pow_add, _root_.mul_assoc] at this
    exact mul_left_cancel₀ (pow_ne_zero _ ht0) this
  have h0 := congrFun (Continuous.ext_on (dense_compl_singleton (0 : K)) hAc hBc heq) 0
  simp only [hA, norm_zero, pow_succ, mul_zero, zero_mul, map_zero, add_zero, norm_eq_zero,
    Multiset.prod_eq_zero_iff, Multiset.mem_map, Multiset.mem_filter] at h0
  obtain ⟨x, ⟨-, hx⟩, hx'⟩ := h0
  exact hx hx'
end GlobalTheory.ResultantNorm
