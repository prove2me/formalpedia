-- Prove2me | solution 1 for GlobalTheory.exists_short_basis_adapted_of_subset_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:16:13.919908+00:00
-- url     : https://prove2.me/submissions/b62fd54d-b617-4fa3-8cbf-9ecaa0e3a2f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsShortBasisAdaptedOfSubsetSpan
import Theorems.Thm_GlobalTheory_exists_short_family_adapted

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped InnerProductSpace
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace GlobalTheory
theorem _root_.solution (L : Submodule ℤ E) [DiscreteTopology L] {n : ℕ}
    {v : Fin n → E} (hv : LinearIndependent ℝ v) (hL : ∀ i, v i ∈ L)
    (hspan : (L : Set E) ⊆ span ℝ (Set.range v)) :
    ∃ b : Basis (Fin n) ℤ L,
      (∀ s : ℕ, span ℤ ((fun i => (b i : E)) '' {i : Fin n | (i : ℕ) < s}) =
        L ⊓ (span ℝ (v '' {i : Fin n | (i : ℕ) < s})).restrictScalars ℤ) ∧
      ∀ i, ‖(b i : E)‖ ^ 2 ≤ ‖v i‖ ^ 2 + (1 / 4) * ∑ j ∈ Finset.Iio i, ‖v j‖ ^ 2 := by
  obtain ⟨b, hb, hflag, hn⟩ := exists_short_family_adapted L hv hL
  have hu : {i : Fin n | (i : ℕ) < n} = Set.univ := by ext i; simp
  have h := hflag n
  rw [hu, Set.image_univ, Set.image_univ, inf_eq_left.2 (show L ≤ _ from hspan)] at h
  have hbZ : LinearIndependent ℤ b := hb.restrict_scalars' ℤ
  have hc : ∀ i, (((Basis.span hbZ).map (LinearEquiv.ofEq _ _ h) i : L) : E) = b i := by
    intro i; simp
  refine ⟨(Basis.span hbZ).map (LinearEquiv.ofEq _ _ h), ?_, ?_⟩
  · simpa only [hc] using hflag
  · simpa only [hc] using hn
end GlobalTheory
