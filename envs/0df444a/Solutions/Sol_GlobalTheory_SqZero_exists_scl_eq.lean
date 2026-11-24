-- Prove2me | solution 1 for GlobalTheory.SqZero.exists_scl_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:57:02.285024+00:00
-- url     : https://prove2.me/submissions/ee4c541e-9d3d-4ae0-9daf-dc30d86831a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
import Theorems.Thm_GlobalTheory_SqZero_res_res
import Theorems.Thm_GlobalTheory_SqZero_res_scl
import Theorems.Thm_GlobalTheory_SqZero_exists_scl_eq_of_unitInChart
import Theorems.Thm_GlobalTheory_SqZero_scl_pow_eq_of_le
import Theorems.Thm_GlobalTheory_SqZero_dual_ext
import Theorems.Thm_GlobalTheory_SqZero_IsAway_lift
import Theorems.Thm_GlobalTheory_SqZero_exists_fin_unitInChart
import Theorems.Thm_GlobalTheory_SqZero_isAway_awayHom
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
theorem _root_.solution (hρ : IsAway ρ g)
    {w w' : sp (R₀ := R) (DualNumber S) ⟶ G} (hw : IsTanOver w) (hw' : IsTanOver w')
    (h : res ρ w = res ρ w') : ∃ N : ℕ, scl (g ^ N) w = scl (g ^ N) w' := by
  obtain ⟨κ, _, s, hs, hU⟩ := exists_fin_unitInChart G S
  have key : ∀ k, ∃ N : ℕ,
      res (awayHom R (s k)) (scl (g ^ N) w) = res (awayHom R (s k)) (scl (g ^ N) w') := by
    intro k
    obtain ⟨ψ, hψ⟩ := hρ.lift ((awayHom R (awayHom R (s k) g)).comp (awayHom R (s k)))
      (isAway_awayHom (R := R) (awayHom R (s k) g)).unit
    obtain ⟨N, hN⟩ := exists_scl_eq_of_unitInChart (hU k) (isAway_awayHom (awayHom R (s k) g))
      (hw.res _) (hw'.res _) (by rw [res_res, res_res, ← hψ, ← res_res, ← res_res, h])
    exact ⟨N, by rw [res_scl, res_scl, map_pow]; exact hN⟩
  choose N hN using key
  have := Fintype.ofFinite κ
  refine ⟨Finset.univ.sup N, dual_ext hs (fun k => awayHom R (s k)) (fun k => isAway_awayHom (s k))
    fun k => ?_⟩
  have h1 := hN k
  rw [res_scl, res_scl, map_pow] at h1 ⊢
  exact scl_pow_eq_of_le (Finset.le_sup (Finset.mem_univ k)) h1
end GlobalTheory.SqZero
