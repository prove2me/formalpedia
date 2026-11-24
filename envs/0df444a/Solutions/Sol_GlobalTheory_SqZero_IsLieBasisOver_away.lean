-- Prove2me | solution 1 for GlobalTheory.SqZero.IsLieBasisOver.away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:21:13.550964+00:00
-- url     : https://prove2.me/submissions/350f9b41-3a29-49db-9876-d99cbce29d57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Theorems.Thm_GlobalTheory_SqZero_res_tanExp
import Theorems.Thm_GlobalTheory_SqZero_scl_tanExp
import Theorems.Thm_GlobalTheory_SqZero_isTanOver_tanExp
import Theorems.Thm_GlobalTheory_SqZero_IsAway_surj_fin
import Theorems.Thm_GlobalTheory_SqZero_exists_res_eq
import Theorems.Thm_GlobalTheory_SqZero_exists_scl_eq
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_SqZero_scl_one
import Theorems.Thm_GlobalTheory_SqZero_scl_scl
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
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {S S' A : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
  [CommRing A] [Algebra R A]
variable {v : Fin n → (epsR R ⟶ G)}
variable [Smooth G.hom]
namespace GlobalTheory.SqZero
namespace IsLieBasisOver
theorem _root_.solution (hv : ∀ i, IsTangent (v i)) (h : IsLieBasisOver S v)
    {ρ : S →ₐ[R] S'} {g : S} (hρ : IsAway ρ g) : IsLieBasisOver S' v := by
  refine ⟨fun s s' e => ?_, fun w' hw' => ?_⟩
  · obtain ⟨N, a, ha⟩ := hρ.surj_fin (Sum.elim s s')
    have e₁ : res ρ (tanExp v fun i => a (.inl i)) = res ρ (tanExp v fun i => a (.inr i)) := by
      rw [res_tanExp, res_tanExp]
      simp only [← ha, Sum.elim_inl, Sum.elim_inr]
      rw [← scl_tanExp, ← scl_tanExp, e]
    obtain ⟨M, hM⟩ := exists_scl_eq hρ (isTanOver_tanExp hv _) (isTanOver_tanExp hv _) e₁
    rw [scl_tanExp, scl_tanExp] at hM
    funext i
    have e₂ := congrArg ρ (congrFun (h.1 _ _ hM) i)
    simp only [map_mul, map_pow, ← ha, Sum.elim_inl, Sum.elim_inr] at e₂
    exact (hρ.unit.pow N).mul_right_cancel ((hρ.unit.pow M).mul_right_cancel e₂)
  · obtain ⟨N, w, hw, e⟩ := exists_res_eq hρ hw'
    obtain ⟨s, rfl⟩ := h.2 w hw
    obtain ⟨t, ht⟩ := (hρ.unit.pow N).exists_left_inv
    refine ⟨fun i => ρ (s i) * t, ?_⟩
    rw [← scl_tanExp, ← res_tanExp, e, scl_scl, ht, scl_one]
end IsLieBasisOver
end GlobalTheory.SqZero
