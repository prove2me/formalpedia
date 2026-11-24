-- Prove2me | solution 1 for GlobalTheory.exists_smul_apply_eq_of_eq_on_invariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:46:56.452218+00:00
-- url     : https://prove2.me/submissions/819bdbdc-e6a9-4bd1-bf91-c0c5f464536a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants

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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {G B D : Type*} [Group G] [Finite G] [CommRing B]
    [CommRing D] [IsDomain D] [MulSemiringAction G B] (x y : B →+* D)
    (h : ∀ b, (∀ g : G, g • b = b) → x b = y b) (b : B) : ∃ g : G, y b = x (g • b) := by
  classical
  have := Fintype.ofFinite G
  set P : Polynomial B := ∏ g : G, (Polynomial.X - Polynomial.C (g • b)) with hP
  have hinvP : ∀ k : G, k • P = P := by
    intro k
    rw [hP, Finset.smul_prod']
    exact Fintype.prod_bijective (k • ·) (MulAction.bijective k) _ _ (fun g => by
      rw [smul_sub, Polynomial.smul_X, Polynomial.smul_C, smul_smul, smul_eq_mul])
  have hmap : P.map x = P.map y := by
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    apply h
    intro g
    rw [← Polynomial.coeff_smul, hinvP]
  have hb : P.eval b = 0 := by
    rw [hP, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ 1) (by simp)
  have h0 : (P.map y).eval (y b) = 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hb, map_zero]
  rw [← hmap, Polynomial.eval_map, hP, Polynomial.eval₂_finsetProd] at h0
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at h0
  obtain ⟨g, -, hg⟩ := Finset.prod_eq_zero_iff.mp h0
  exact ⟨g, sub_eq_zero.mp hg⟩
end GlobalTheory
