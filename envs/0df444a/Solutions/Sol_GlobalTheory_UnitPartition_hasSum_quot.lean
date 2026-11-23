-- Prove2me | solution 1 for GlobalTheory.UnitPartition.hasSum_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:23:21.264909+00:00
-- url     : https://prove2.me/submissions/aee267ec-1832-41e6-bc4f-c11c14180677

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothCompactSupportHasSumLatticeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothHomogeneousHasSumUnitSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
open GlobalTheory.UnitPartition
open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace
namespace GlobalTheory.UnitPartition
theorem _root_.solution {G : Type} [Group G] (T : Subgroup G) [Finite T] (f : G ⧸ T → ℝ) (s : ℝ)
    (hf : HasSum f s) : HasSum (fun g : G => f (g : G ⧸ T) / Nat.card T) s := by
  classical
  have : Fintype T := Fintype.ofFinite T
  have hT : (Nat.card T : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  let e : G ≃ (G ⧸ T) × T := Subgroup.groupEquivQuotientProdSubgroup
  have he : ∀ g : G, (e g).1 = (g : G ⧸ T) := fun g => rfl
  have hp : ∀ p : (G ⧸ T) × T, ((e.symm p : G) : G ⧸ T) = p.1 := fun p => by
    rw [← he, e.apply_symm_apply]
  have hfun : (fun g : G => f (g : G ⧸ T) / Nat.card T) ∘ e.symm =
      fun p : (G ⧸ T) × T => f p.1 * (Nat.card T : ℝ)⁻¹ := by
    funext p
    simp only [Function.comp_apply, hp p, div_eq_mul_inv]
  have hg : HasSum (fun _ : T => (Nat.card T : ℝ)⁻¹) 1 := by
    have h0 := hasSum_fintype (fun _ : T => (Nat.card T : ℝ)⁻¹)
    rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
      mul_inv_cancel₀ hT] at h0
  have hprod : HasSum (fun p : (G ⧸ T) × T => f p.1 * (Nat.card T : ℝ)⁻¹) s := by
    have hs1 : Summable fun q : G ⧸ T => ‖f q‖ := by
      simpa only [Real.norm_eq_abs] using hf.summable.abs
    have hs2 : Summable fun _ : T => ‖(Nat.card T : ℝ)⁻¹‖ := Summable.of_finite
    have hs : Summable fun p : (G ⧸ T) × T => f p.1 * (fun _ : T => (Nat.card T : ℝ)⁻¹) p.2 :=
      summable_mul_of_summable_norm (R := ℝ) (f := f) (g := fun _ : T => (Nat.card T : ℝ)⁻¹) hs1 hs2
    have h0 := HasSum.mul (f := f) (g := fun _ : T => (Nat.card T : ℝ)⁻¹) hf hg hs
    rwa [mul_one] at h0
  rw [← e.symm.hasSum_iff, hfun]
  exact hprod
end GlobalTheory.UnitPartition
