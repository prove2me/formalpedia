-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_nonneg_avgOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:23:19.868752+00:00
-- url     : https://prove2.me/submissions/10a877d3-305b-46aa-9466-d0806fc1e704

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellSurjective
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_sum
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_rightStab
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {G : Type*} [Group G] {W E : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup E]
  [Module ℂ E]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (π : W →ₗ[ℂ] E) {K : Subgroup G} {f : G → W} (hf : AvgFinite K f)
    (x : G) (c₀ : E) (hterm : ∀ k ∈ K, ∃ r : ℝ, 0 ≤ r ∧ π (f (x * k)) = (r : ℂ) • c₀) :
    ∃ r : ℝ, 0 ≤ r ∧ π (avgOver K f x) = (r : ℂ) • c₀ ∧
      (∀ r₀ : ℝ, 0 < r₀ → π (f x) = (r₀ : ℂ) • c₀ → c₀ ≠ 0 → 0 < r) := by
  classical
  set S := (rightStab f).subgroupOf K
  have : S.FiniteIndex := ⟨hf⟩
  let _ := Fintype.ofFinite (K ⧸ S)
  choose rr hrr using fun q : K ⧸ S => hterm _ (Quotient.out q).2
  have hidx : (0 : ℝ) < (S.index : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hf)
  refine ⟨(S.index : ℝ)⁻¹ * ∑ q, rr q, ?_, ?_, ?_⟩
  · exact mul_nonneg (inv_nonneg.2 hidx.le) (Finset.sum_nonneg fun q _ => (hrr q).1)
  · rw [avgOver_eq_sum, map_smul, map_sum]
    simp_rw [fun q : K ⧸ S => (hrr q).2]
    rw [← Finset.sum_smul, smul_smul]
    congr 1
    push_cast
    rfl
  · intro r₀ hr₀ hfx hc₀
    set q₀ : K ⧸ S := QuotientGroup.mk 1
    have hq₀ : (Quotient.out q₀ : K) ∈ S := by
      have h := QuotientGroup.out_eq' q₀
      rw [QuotientGroup.eq] at h
      simpa using h
    have hst : ((Quotient.out q₀ : K) : G) ∈ rightStab f := Subgroup.mem_subgroupOf.1 hq₀
    have hval : f (x * ((Quotient.out q₀ : K) : G)) = f x := (mem_rightStab.1 hst) x
    have heq : ((rr q₀ : ℝ) : ℂ) • c₀ = ((r₀ : ℝ) : ℂ) • c₀ := by
      rw [← (hrr q₀).2, hval, hfx]
    have hr : rr q₀ = r₀ := by
      have := smul_left_injective ℂ hc₀ heq
      exact_mod_cast this
    have hsum : 0 < ∑ q, rr q :=
      lt_of_lt_of_le (hr ▸ hr₀) (Finset.single_le_sum (fun q _ => (hrr q).1) (Finset.mem_univ q₀))
    exact mul_pos (inv_pos.2 hidx) hsum
end GroundTheory.Automorphic.Parabolic
