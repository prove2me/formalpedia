-- Prove2me | solution 1 for GlobalTheory.ResultantNorm.card_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:56:33.820725+00:00
-- url     : https://prove2.me/submissions/f9dd0016-ad01-4e3a-ae85-50abb53acb72

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEq

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
variable {l : ℕ} [Fact l.Prime] {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]
namespace GlobalTheory.ResultantNorm
theorem _root_.solution (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] Ω] (a b : Multiset Ω)
    (h : ∀ F : ℤ[X], ‖(a.map fun x => aeval x F).prod‖ = ‖(b.map fun x => aeval x F).prod‖) :
    a.card = b.card := by
  have h1 := h (C (l : ℤ))
  have hl : ‖(l : Ω)‖ = ‖(l : ℚ_[l])‖ := by
    rw [← norm_algebraMap' Ω (l : ℚ_[l]), map_natCast]
  simp only [aeval_C, map_natCast, Multiset.map_const', Multiset.prod_replicate, norm_pow,
    hl] at h1
  refine pow_right_injective₀ ?_ ?_ h1
  · exact norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  · exact Padic.norm_p_lt_one.ne
end GlobalTheory.ResultantNorm
