-- Prove2me | solution 1 for GlobalTheory.formallyUnramified_mulN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:36:30.987422+00:00
-- url     : https://prove2.me/submissions/2864fa58-5436-4738-9114-f14325f3f417

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FormallyUnramifiedMulN
import Theorems.Thm_GlobalTheory_MulUnramified_comp_mulN
import Theorems.Thm_GlobalTheory_MulUnramified_eq_one_of_pow_eq_one
import Theorems.Thm_GlobalTheory_MulUnramified_mul_eq_zero_of_ker_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open MulUnramified
namespace GlobalTheory
theorem _root_.solution (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ)
    (hn : IsUnit (n : Γ(S, ⊤))) : FormallyUnramified (mulN G n).left := by
  refine FormallyUnramified.of_hom_ext _ fun R R₀ φ hφ hsq g₁ g₂ hi hg ↦ ?_
  have hS : g₂ ≫ G.hom = g₁ ≫ G.hom := by
    rw [← Over.w (mulN G n), reassoc_of% hg]
  let T : Over S := Over.mk (g₁ ≫ G.hom)
  let T₀ : Over S := Over.mk (Spec.map φ ≫ g₁ ≫ G.hom)
  let j : T₀ ⟶ T := Over.homMk (Spec.map φ) rfl
  let x : T ⟶ G := Over.homMk g₁ rfl
  let y : T ⟶ G := Over.homMk g₂ hS
  have hj : j ≫ x = j ≫ y := Over.OverMorphism.ext hi
  have hxy : x ^ n = y ^ n := by
    rw [← comp_mulN, ← comp_mulN]
    exact Over.OverMorphism.ext hg
  have hsurj : Function.Surjective (Spec.map φ) := by
    intro (p : PrimeSpectrum R)
    change p ∈ Set.range (PrimeSpectrum.comap φ.hom)
    rw [range_comap_of_surjective _ _ hφ, PrimeSpectrum.mem_zeroLocus]
    intro a ha
    refine p.isPrime.mem_of_pow_mem 2 ?_
    have : a ^ 2 ∈ RingHom.ker φ.hom ^ 2 := Ideal.pow_mem_pow ha 2
    rw [hsq, Ideal.mem_bot] at this
    rw [this]
    exact zero_mem _
  have := eq_one_of_pow_eq_one G j hsurj (mul_eq_zero_of_ker_sq φ hsq) n hn (x / y)
    (by rw [GrpObj.comp_div, hj, div_self']) (by rw [div_pow, hxy, div_self'])
  exact congrArg (·.left) (div_eq_one.mp this)
end GlobalTheory
