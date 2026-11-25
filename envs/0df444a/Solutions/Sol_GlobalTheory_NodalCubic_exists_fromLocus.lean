-- Prove2me | solution 1 for GlobalTheory.NodalCubic.exists_fromLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:54:20.913087+00:00
-- url     : https://prove2.me/submissions/8b986586-04e3-4fa7-81af-436dec55f535

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonsingularIffNodal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RangeSubsetOfForallField
import Theorems.Thm_GlobalTheory_NodalCubic_evalAt_comp
import Theorems.Thm_GlobalTheory_NodalCubic_evalAt_specMap
import Theorems.Thm_GlobalTheory_NodalCubic_isUnit_of_forall_evalAt
import Theorems.Thm_GlobalTheory_NodalCubic_unitOf_surjective
import Theorems.Thm_GlobalTheory_NodalCubic_valOf_comp
import Theorems.Thm_GlobalTheory_NodalCubic_exists_over_point
import Theorems.Thm_GlobalTheory_NodalCubic_range_subset_of_forall_field
import Theorems.Thm_GlobalTheory_NodalCubic_exists_nonsingular
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm
import Theorems.Thm_GlobalTheory_NodalCubic_nonsingular_points


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.NodalCubic
open GlobalTheory.WeierstrassCurve
variable (K : Type) [Field K]
variable {K}
variable (U : (scheme (node K)).Opens)
  (hU : ∀ (k : Type) [Field k] (ρ : K →+* k) (P : Fin 3 → k)
    (h : IsUnimodularSol ((node K).map ρ) P),
    ⊤ ≤ ptHom (node K) ρ P h ⁻¹ᵁ U ↔ ((node K).map ρ).toProjective.Nonsingular P)
include hU
namespace GlobalTheory.NodalCubic
theorem _root_.solution : ∃ g : Over.mk (U.ι ≫ toSpec (node K)) ⟶ splitTorus (Spec (.of K)) ℤ,
    ∀ (k : Type) [Field k] (ρ : K →+* k)
      (y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ Over.mk (U.ι ≫ toSpec (node K)))
      (P : Fin 3 → k) (h : IsUnimodularSol ((node K).map ρ) P),
      y.left ≫ U.ι = ptHom (node K) ρ P h → (valOf (y ≫ g) : k) = P 1 / (P 0 + P 1) := by
  have h : Set.range U.ι ⊆ Set.range (awayChart (node K) 1) := by
    rw [← (awayChart (node K) 1).coe_opensRange, opensRange_awayChart]
    refine range_subset_of_forall_field _ _ fun k _ x => ?_
    obtain ⟨ρ, y, rfl⟩ := exists_over_point (Z := Over.mk (U.ι ≫ toSpec (node K))) x
    obtain ⟨P, hP, e, hn⟩ := exists_nonsingular U hU y
    have h1 := ((nonsingular_points k).2.2 P hn).1
    refine le_of_eq (Eq.symm ?_)
    refine (congrArg (· ⁻¹ᵁ _) e).trans ?_
    rw [ptHom_preimage_coordOpen]
    exact top_le_iff.mp fun p _ hp => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp h1.isUnit)
  let j := IsOpenImmersion.lift (awayChart (node K) 1) U.ι h
  have hj : j ≫ awayChart (node K) 1 = U.ι := IsOpenImmersion.lift_fac _ _ h
  let s : Γ(U.toScheme, ⊤) := j.appTop.hom ((Scheme.ΓSpecIso (.of (AwayRing (node K) 1))).inv.hom
    (awayCoord (node K) 1 0 + 1))
  have key : ∀ (k : Type) [Field k] (ρ : K →+* k) (x : Spec (.of k) ⟶ U.toScheme)
      (P : Fin 3 → k) (h : IsUnimodularSol ((node K).map ρ) P),
      x ≫ U.ι = ptHom (node K) ρ P h →
        P 1 ≠ 0 ∧ P 0 + P 1 ≠ 0 ∧ evalAt x s * P 1 = P 0 + P 1 := by
    intro k _ ρ x P hP e
    have hn : (node k).toProjective.Nonsingular P := by
      rw [← node_map ρ, ← hU k ρ P hP, ← e]
      intro z _
      exact (x z).2
    obtain ⟨h1, h2, -⟩ := (nonsingular_points k).2.2 P hn
    refine ⟨h1, h2, ?_⟩
    have e2 : x ≫ j = Spec.map (CommRingCat.ofHom
        (awayEval (node K) 1 ρ P hP.equation h1.isUnit)) := by
      rw [← cancel_mono (awayChart (node K) 1), Category.assoc, hj, e,
        ptHom_eq_awayChart _ 1 _ _ _ h1.isUnit]
    rw [← evalAt_comp, e2, evalAt_specMap, CommRingCat.hom_ofHom, map_add, map_one, add_mul,
      awayEval_awayCoord_mul, _root_.one_mul]
  have hs : IsUnit s := by
    refine isUnit_of_forall_evalAt s fun k _ x h0 => ?_
    obtain ⟨ρ, y, rfl⟩ := exists_over_point (Z := Over.mk (U.ι ≫ toSpec (node K))) x
    obtain ⟨P, hP, e, -⟩ := exists_nonsingular U hU y
    obtain ⟨-, h2, h3⟩ := key k ρ y.left P hP e
    exact h2 (by rw [← h3]; exact mul_eq_zero_of_left h0 _)
  obtain ⟨g, hg⟩ := unitOf_surjective (Z := Over.mk (U.ι ≫ toSpec (node K))) hs.unit⁻¹
  refine ⟨g, fun k _ ρ y P hP e => ?_⟩
  obtain ⟨h1, h2, h3⟩ := key k ρ y.left P hP e
  have h4 : evalAt (k := k) y.left (unitOf g).val * evalAt (k := k) y.left s = 1 := by
    rw [hg]
    exact (map_mul _ _ _).symm.trans ((congrArg _ hs.val_inv_mul).trans (map_one _))
  rw [valOf_comp, eq_div_iff h2, ← h3, ← _root_.mul_assoc]
  exact (congrArg (· * P 1) h4).trans (_root_.one_mul _)
end GlobalTheory.NodalCubic
