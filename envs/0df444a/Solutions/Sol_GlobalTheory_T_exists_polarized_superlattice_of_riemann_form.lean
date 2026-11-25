-- Prove2me | solution 1 for GlobalTheory.T.exists_polarized_superlattice_of_riemann_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:19:13.809812+00:00
-- url     : https://prove2.me/submissions/8f3240d0-69ca-4c82-b557-fb13904c0502

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolarizedSuperlatticeOfRiemannForm
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolarizedSuperlatticeOfRiemannFormStatement
import Theorems.Thm_GlobalTheory_UnimodOver_exists_unimodular_overlattice


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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
    (∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (Λ₁ : Submodule ℤ (Fin g → ℂ)) (N : ℕ) (Ef : LinearMap.BilinForm ℤ Λ₁),
      Λ ≤ Λ₁ ∧ 0 < N ∧ (∀ x ∈ Λ₁, (N : ℂ) • x ∈ Λ) ∧ DiscreteTopology Λ₁ ∧
      Submodule.span ℝ (Λ₁ : Set (Fin g → ℂ)) = ⊤ ∧
      (∀ a b : Λ₁, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef := by
  first | exact @GlobalTheory.UnimodOver.exists_unimodular_overlattice | exact GlobalTheory.UnimodOver.exists_unimodular_overlattice | (intros; apply GlobalTheory.UnimodOver.exists_unimodular_overlattice <;> assumption)
end _root_.GlobalTheory.T
