-- Prove2me | solution 1 for GlobalTheory.FinrankGrowthBounds.finrank_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:28:28.73561+00:00
-- url     : https://prove2.me/submissions/6f1d608b-1773-453d-8d06-d17790e73cbc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankSectionsLineBundlePowEqPow
import Theorems.Thm_GlobalTheory_FinrankGrowthBounds_finite_index

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory GlobalTheory.FinrankGrowthBounds
open Filter Topology
namespace GlobalTheory.FinrankGrowthBounds
theorem _root_.solution {R : Type*} [CommRing R] (hR : IsField R) {I A M B M' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup M] [Module R M] [AddCommGroup B] [Module R B]
    [AddCommGroup M'] [Module R M'] [Module.Finite R A] [Module.Finite R M']
    (hM : Module.finrank R M = 1) (e : A ≃ₗ[R] (I → M)) (e' : B ≃ₗ[R] (I → M')) :
    Module.finrank R B = Module.finrank R A * Module.finrank R M' := by
  letI := hR.toField
  haveI : Nontrivial M := Module.nontrivial_of_finrank_eq_succ hM
  haveI : Module.Finite R M := Module.finite_of_finrank_eq_succ hM
  haveI : Module.Finite R (I → M) := Module.Finite.equiv e
  haveI : Finite I := finite_index (R := R) (M := M)
  letI := Fintype.ofFinite I
  rw [e.finrank_eq, e'.finrank_eq, Module.finrank_pi_fintype, Module.finrank_pi_fintype]
  simp [hM]
end GlobalTheory.FinrankGrowthBounds
