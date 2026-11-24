-- Prove2me | solution 1 for GlobalTheory.SqZero.exists_scl_eq_of_unitInChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:42:30.23485+00:00
-- url     : https://prove2.me/submissions/bc8ef7fb-9e9e-4e69-addf-45ccf02e39c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
import Theorems.Thm_GlobalTheory_SqZero_exists_ders
import Theorems.Thm_GlobalTheory_SqZero_exists_chart_of_isTanOver
import Theorems.Thm_GlobalTheory_SqZero_snd_eq_sum
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ker_fin
import Theorems.Thm_GlobalTheory_SqZero_chart_inj
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
    {w w' : sp (R₀ := R) (DualNumber S) ⟶ G} (hw : IsTanOver w) (hw' : IsTanOver w')
    (h : res ρ w = res ρ w') : ∃ N : ℕ, scl (g ^ N) w = scl (g ^ N) w' := by
  obtain ⟨B, _, _, j, u, hj, hu⟩ := hS
  have := smooth_of_chart j
  obtain ⟨κ, _, β, τ, hτ⟩ := exists_ders R B
  obtain ⟨φ, rfl, hφ⟩ := exists_chart_of_isTanOver j u hu hw
  obtain ⟨φ', rfl, hφ'⟩ := exists_chart_of_isTanOver j u hu hw'
  have e : (dualMap ρ).comp φ = (dualMap ρ).comp φ' := by
    apply chart_inj j
    have h' := h
    dsimp only [res] at h'
    rwa [← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp] at h'
  have hz : ∀ i, ρ ((φ (β i)).snd - (φ' (β i)).snd) = 0 := fun i => by
    have := congrArg (fun f => (f (β i)).snd) e
    simpa [sub_eq_zero] using this
  obtain ⟨N, hN⟩ := hρ.ker_fin hz
  refine ⟨N, ?_⟩
  have e2 : (dualScale R (g ^ N)).comp φ = (dualScale R (g ^ N)).comp φ' := by
    refine AlgHom.ext fun b => TrivSqZeroExt.ext (by simp [hφ, hφ']) ?_
    have s1 := snd_eq_sum hτ u φ hφ b
    have s2 := snd_eq_sum hτ u φ' hφ' b
    simp only [AlgHom.comp_apply, snd_dualScale]
    rw [← sub_eq_zero, ← sub_mul, s1, s2, ← Finset.sum_sub_distrib, Finset.sum_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← mul_sub, mul_assoc, mul_comm _ (g ^ N), hN i, mul_zero]
  dsimp only [scl]
  rw [← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, e2]
end GlobalTheory.SqZero
