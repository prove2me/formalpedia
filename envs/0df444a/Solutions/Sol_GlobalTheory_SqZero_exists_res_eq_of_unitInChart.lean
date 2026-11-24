-- Prove2me | solution 1 for GlobalTheory.SqZero.exists_res_eq_of_unitInChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:42:29.343214+00:00
-- url     : https://prove2.me/submissions/cb799ac9-2775-48bf-85d4-4d02e3fbd335

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
import Theorems.Thm_GlobalTheory_SqZero_addDers_apply
import Theorems.Thm_GlobalTheory_SqZero_exists_ders
import Theorems.Thm_GlobalTheory_SqZero_exists_chart_of_isTanOver
import Theorems.Thm_GlobalTheory_SqZero_snd_eq_sum
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_IsAway_surj_fin
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_SqZero_smooth_of_chart
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable {S S' S'' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
  [CommRing S''] [Algebra R S'']
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
variable [Smooth G.hom] {ρ : S →ₐ[R] S'} {g : S}
namespace GlobalTheory.SqZero
theorem _root_.solution (hS : UnitInChart G S) (hρ : IsAway ρ g)
    {w' : sp (R₀ := R) (DualNumber S') ⟶ G} (hw' : IsTanOver w') :
    ∃ (N : ℕ) (w : sp (R₀ := R) (DualNumber S) ⟶ G), IsTanOver w ∧
      res ρ w = scl (ρ g ^ N) w' := by
  obtain ⟨B, _, _, j, u, hj, hu⟩ := hS
  have := smooth_of_chart j
  obtain ⟨κ, _, β, τ, hτ⟩ := exists_ders R B
  have hu' : spMap (ρ.comp u) ≫ j = 1 := by rw [← spMap_comp, Category.assoc, hu, comp_one']
  obtain ⟨φ', rfl, hφ'⟩ := exists_chart_of_isTanOver j (ρ.comp u) hu' hw'
  obtain ⟨N, a, ha⟩ := hρ.surj_fin (fun i => (φ' (β i)).snd)
  let ψ := addDers τ ((inlS R S).comp u) (fun i => (inr (a i) : DualNumber S))
    (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)
  have hψ : (fstS R S).comp ψ = u := AlgHom.ext fun b => by simp [ψ, addDers_apply, TrivSqZeroExt.fst_sum]
  refine ⟨N, spMap ψ ≫ j, ?_, ?_⟩
  · show spMap (fstS R S) ≫ spMap ψ ≫ j = 1
    rw [← Category.assoc, spMap_comp, hψ, hu]
  · have e : (dualMap ρ).comp ψ = (dualScale R (ρ g ^ N)).comp φ' := by
      refine AlgHom.ext fun b => TrivSqZeroExt.ext ?_ ?_
      · simp [ψ, addDers_apply, hφ', TrivSqZeroExt.fst_sum]
      · have s := snd_eq_sum hτ (ρ.comp u) φ' hφ' b
        simp only [AlgHom.comp_apply, snd_dualScale, snd_dualMap, ψ, addDers_apply]
        rw [s, Finset.sum_mul]
        simp [TrivSqZeroExt.snd_sum, map_sum, mul_assoc, ha]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    dsimp only [res, scl]
    rw [← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, e]
end GlobalTheory.SqZero
