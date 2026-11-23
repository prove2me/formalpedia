-- Prove2me | solution 1 for GlobalTheory.orthonormal_frames_bounded_of_definite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:24.192266+00:00
-- url     : https://prove2.me/submissions/c78084f8-dee7-4a90-8bf9-6f26b181221d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OrthonormalFramesBoundedOfDefinite
import Theorems.Thm_GlobalTheory_norm_entry_le_of_gram_eq_smul_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory
open NumberField MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), (X.p0 = 0 ∨ X.p0 = r) →
      ∃ R : ℝ, ∀ x, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ∀ τ a b, ‖x τ a b‖ ≤ R) := by
  intro r X hp
  refine ⟨1 + ∑ τ : X.Ψ, ∑ a : Fin r, ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a a‖,
    fun x hx τ a b => ?_⟩
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth at hx
  have hτ := hx τ
  obtain ⟨s, hs, hdiag⟩ : ∃ s : ℂ, s * s = 1 ∧
      Matrix.diagonal (fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ)) = s • 1 := by
    rcases hp with h | h
    · refine ⟨-1, by norm_num, ?_⟩
      ext i j
      simp [h, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, Matrix.diagonal_apply, Matrix.one_apply]
    · refine ⟨1, by norm_num, ?_⟩
      ext i j
      simp [h, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, Matrix.diagonal_apply, Matrix.one_apply]
  have key : (Matrix.of (x τ))ᵀ * X.Gm.map (τ : E →+* ℂ) * (Matrix.of (x τ)).map (starRingEnd ℂ)
      = s • 1 := by
    rw [← hdiag, ← hτ]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.gram _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.col, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hb := _root_.GlobalTheory.norm_entry_le_of_gram_eq_smul_one _ _ s hs key a b
  have h1 : ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a a‖ ≤ ∑ a' : Fin r, ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a' a'‖ :=
    Finset.single_le_sum (f := fun a' => ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a' a'‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  have h2 : ∑ a' : Fin r, ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a' a'‖ ≤
      ∑ τ' : X.Ψ, ∑ a' : Fin r, ‖((X.Gm.map (τ' : E →+* ℂ))⁻¹) a' a'‖ :=
    Finset.single_le_sum (f := fun τ' : X.Ψ => ∑ a' : Fin r, ‖((X.Gm.map (τ' : E →+* ℂ))⁻¹) a' a'‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ τ)
  have hx' : ‖x τ a b‖ = ‖Matrix.of (x τ) a b‖ := rfl
  linarith
end _root_.GlobalTheory
end GlobalTheory
