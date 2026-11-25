-- Prove2me | solution 1 for GlobalTheory.ProperDiscontinuity.propDisc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:10:41.42891+00:00
-- url     : https://prove2.me/submissions/1cee8231-44d9-4d5c-81b4-6dad71e53d22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RmulOneFrame
import Theorems.Thm_GlobalTheory_ProperDiscontinuity_oneFrame_mem
import Theorems.Thm_GlobalTheory_ProperDiscontinuity_rmul_oneFrame
import Theorems.Thm_GlobalTheory_ProperDiscontinuity_lact_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientDomain_isOpen_dom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.ProperDiscontinuity
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.ProperDiscontinuity
theorem _root_.solution :
    (∀ (r : ℕ) (X : Data E r) (γ : GL (Fin r) E), IsUStab X.Gm X.Λ γ → ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj (lact γ (rmul x b)) τ (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ.1) v) = X.maj x τ v) → (∀ (r : ℕ) (X : Data E r) (K : Set (Frame X.Ψ r)), IsCompact K → K ⊆ X.dom → ∃ c C : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ (τ : X.Ψ) (v : Fin r → ℂ), c * ‖v‖ ^ 2 ≤ X.maj x τ v ∧ X.maj x τ v ≤ C * ‖v‖ ^ 2) → (∀ (r : ℕ) (X : Data E r) (R : ℝ), {γ : GL (Fin r) E | IsUStab X.Gm X.Λ γ ∧ ∀ (τ : X.Ψ) (a b : Fin r), ‖τ.1 ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ R}.Finite) → (∀ (r : ℕ) (X : Data E r), PropDisc X) := by
  intro hinv hbd hfin r X x hx x' hx'
  have hO := FourierCoefficientDomain.isOpen_dom X
  obtain ⟨K, hK, hKd, hKc⟩ := local_compact_nhds (hO.mem_nhds hx)
  obtain ⟨K', hK', hKd', hKc'⟩ := local_compact_nhds (hO.mem_nhds hx')
  obtain ⟨c, C, hc, hb⟩ := hbd r X (K ∪ K') (hKc.union hKc') (Set.union_subset hKd hKd')
  refine ⟨K, hK, K', hK', (hfin r X (Real.sqrt (C / c))).subset ?_⟩
  rintro γ ⟨hγ, u, hu, u', hu', b, hbB, he⟩
  refine ⟨X.Γ_stab γ hγ, fun τ i j => ?_⟩
  set M : Matrix (Fin r) (Fin r) ℂ := (γ : Matrix (Fin r) (Fin r) E).map τ.1 with hM
  set v : Fin r → ℂ := Pi.single j 1 with hv
  have h1 := (hinv r X γ (X.Γ_stab γ hγ) u (hKd hu) _ (oneFrame_mem X.Ψ r)).2 τ v
  rw [rmul_oneFrame, he] at h1
  have h2 := (hinv r X 1 (X.Γ_stab 1 X.Γ.one_mem) u' (hKd' hu') b hbB).2 τ (M.mulVec v)
  rw [lact_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec] at h2
  have h3 := (hb u' (Or.inr hu') τ (M.mulVec v)).1
  have h4 := (hb u (Or.inl hu) τ v).2
  have hv1 : ‖v‖ = 1 := by rw [hv, Pi.norm_single, norm_one]
  rw [hv1] at h4
  have h5 : c * ‖M.mulVec v‖ ^ 2 ≤ C := by
    have : X.maj u' τ (M.mulVec v) = X.maj u τ v := h2.symm.trans h1
    linarith
  have h6 : ‖M.mulVec v‖ ≤ Real.sqrt (C / c) := by
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hc]
    linarith
  have h7 : M.mulVec v i = τ.1 ((γ : Matrix (Fin r) (Fin r) E) i j) := by
    simp [hv, hM]
  rw [← h7]
  exact (norm_le_pi_norm _ i).trans h6
end GlobalTheory.ProperDiscontinuity
