-- Prove2me | solution 1 for GlobalTheory.SqZero.redKer_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:41:22.158849+00:00
-- url     : https://prove2.me/submissions/2375225a-9ed3-42a5-ace5-f6f9bb0566e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Theorems.Thm_GlobalTheory_SqZero_map_sq
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_SqZero_comp_mem_redKer
import Theorems.Thm_GlobalTheory_SqZero_exists_fin_unitInChart
import Theorems.Thm_GlobalTheory_SqZero_exists_chart_of_mem_redKer
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_IsAway_lift
import Theorems.Thm_GlobalTheory_SqZero_away_ext
import Theorems.Thm_GlobalTheory_SqZero_chart_inj
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
variable (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
  {A A' A₀ : Type} [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A']
  [CommRing A₀] [Algebra R A₀]
variable {G}
namespace GlobalTheory.SqZero
theorem _root_.solution {J : Ideal A} (hJ : J ^ 2 = ⊥) {y y' : sp A ⟶ G} (hy : y ∈ redKer G J)
    (hy' : y' ∈ redKer G J) (q₁ : A →ₐ[R] A') (q₂ : A →ₐ[R] A₀)
    (hq : ∀ a, q₁ a = 0 → q₂ a = 0 → a = 0) (h₁ : spMap q₁ ≫ y = spMap q₁ ≫ y')
    (h₂ : spMap q₂ ≫ y = spMap q₂ ≫ y') : y = y' := by
  obtain ⟨κ, _, s, hs, hsm⟩ := exists_fin_unitInChart G A
  refine away_ext hs (fun k => awayHom R (s k)) (fun k => isAway_awayHom _) fun k => ?_
  obtain ⟨B, _, _, j, u, hj, hu⟩ := hsm k
  have hρ := isAway_awayHom (R := R) (s k)
  obtain ⟨φ, e, -⟩ := exists_chart_of_mem_redKer j u hu (map_sq hJ (awayHom R (s k)))
    (comp_mem_redKer hy (awayHom R (s k)) fun a ha => Ideal.mem_map_of_mem _ ha)
  obtain ⟨φ', e', -⟩ := exists_chart_of_mem_redKer j u hu (map_sq hJ (awayHom R (s k)))
    (comp_mem_redKer hy' (awayHom R (s k)) fun a ha => Ideal.mem_map_of_mem _ ha)
  rw [e, e']
  congr 2
  ext b
  obtain ⟨N, a, ha⟩ := hρ.surj (φ b - φ' b)
  have key : ∀ {T : Type} [CommRing T] [Algebra R T] (q : A →ₐ[R] T),
      spMap q ≫ y = spMap q ≫ y' → ∃ M : ℕ, q (s k ^ M * a) = 0 := by
    intro T _ _ q h
    have hρ' := isAway_awayHom (R := R) (q (s k))
    obtain ⟨ψ, hψ⟩ := hρ.lift ((awayHom R (q (s k))).comp q) hρ'.unit
    have : spMap (ψ.comp φ) ≫ j = spMap (ψ.comp φ') ≫ j := by
      rw [← spMap_comp, ← spMap_comp, Category.assoc, Category.assoc, ← e, ← e',
        ← Category.assoc, ← Category.assoc, spMap_comp, hψ, ← spMap_comp, Category.assoc,
        Category.assoc, h]
    have h3 : ψ (φ b) = ψ (φ' b) := AlgHom.congr_fun (chart_inj j this) b
    obtain ⟨M, hM⟩ := hρ'.ker (a := q a) (by
      rw [← AlgHom.comp_apply, ← hψ, AlgHom.comp_apply, ← ha, map_mul, map_sub, h3, sub_self,
        zero_mul])
    exact ⟨M, by rw [map_mul, map_pow, hM]⟩
  obtain ⟨M₁, e₁⟩ := key q₁ h₁
  obtain ⟨M₂, e₂⟩ := key q₂ h₂
  have h0 : s k ^ M₁ * s k ^ M₂ * a = 0 := hq _
    (by rw [mul_right_comm, map_mul, e₁, zero_mul]) (by rw [mul_assoc, map_mul, e₂, mul_zero])
  have h1 := congrArg (awayHom R (s k)) h0
  rw [map_mul, map_mul, map_pow, map_pow, map_zero, ← ha,
    ((hρ.unit.pow M₁).mul (hρ.unit.pow M₂)).mul_right_eq_zero,
    (hρ.unit.pow N).mul_left_eq_zero] at h1
  exact sub_eq_zero.1 h1
end GlobalTheory.SqZero
