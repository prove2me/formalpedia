-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.exists_valuation_div_zpow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:49:49.356314+00:00
-- url     : https://prove2.me/submissions/c39c819d-8894-4703-8c2f-9a0815417043

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_eventually_pow_mul_mem
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset ValuativeRel
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
local notation "ϖ" => ((uniformizer F : 𝒪[F]) : F)
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution {x : F} (hx : x ≠ 0) :
    ∃ m : ℤ, valuation F (x / ϖ ^ m) = 1 := by
  obtain ⟨N, hN⟩ := (eventually_pow_mul_mem F x).exists
  have hϖ := uniformizer_ne_zero F
  have hy : (⟨ϖ ^ N * x, hN⟩ : 𝒪[F]) ≠ 0 := by
    intro h0
    have := congrArg Subtype.val h0
    exact mul_ne_zero (pow_ne_zero N hϖ) hx this
  obtain ⟨k, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy (irreducible_uniformizer F)
  have hu' : ϖ ^ N * x = ((u : 𝒪[F]) : F) * ϖ ^ k := by
    have := congrArg (fun z : 𝒪[F] => (z : F)) hu
    simpa using this
  refine ⟨(k : ℤ) - N, ?_⟩
  have hxu : x / ϖ ^ ((k : ℤ) - N) = ((u : 𝒪[F]) : F) := by
    rw [zpow_sub₀ hϖ, zpow_natCast, zpow_natCast, div_div_eq_mul_div, mul_comm x, hu',
      mul_div_assoc, div_self (pow_ne_zero _ hϖ), mul_one]
  rw [hxu]
  exact (Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one.mp u.isUnit
end GroundTheory.Automorphic.GLnLocal
