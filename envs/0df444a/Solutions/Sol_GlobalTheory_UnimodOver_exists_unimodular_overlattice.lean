-- Prove2me | solution 1 for GlobalTheory.UnimodOver.exists_unimodular_overlattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:13:15.446402+00:00
-- url     : https://prove2.me/submissions/16b63e68-95f2-4338-b14f-8c32b533b6f0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolarizedSuperlatticeOfRiemannForm
import Theorems.Thm_GlobalTheory_UnimodOver_exists_unimodular
import Theorems.Thm_GlobalTheory_UnimodOver_imForm_apply
import Theorems.Thm_GlobalTheory_UnimodOver_imForm_isAlt
import Theorems.Thm_GlobalTheory_UnimodOver_imForm_nondegenerate

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
open GlobalTheory GlobalTheory.UnimodOver
open Module
namespace GlobalTheory.UnimodOver
theorem _root_.solution :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
    (∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (Λ₁ : Submodule ℤ (Fin g → ℂ)) (N : ℕ) (Ef : LinearMap.BilinForm ℤ Λ₁),
      Λ ≤ Λ₁ ∧ 0 < N ∧ (∀ x ∈ Λ₁, (N : ℂ) • x ∈ Λ) ∧ DiscreteTopology Λ₁ ∧
      Submodule.span ℝ (Λ₁ : Set (Fin g → ℂ)) = ⊤ ∧
      (∀ a b : Λ₁, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef := by
  intro g Λ Hm hd hs hH hp hint
  obtain ⟨M, N, Ef, h1, h2, h3, h4, h5, h6, h7⟩ :=
    exists_unimodular (imForm Hm) (imForm_nondegenerate hH hp) (imForm_isAlt hH) Λ hs
      (fun x hx y hy => by
        obtain ⟨n, hn⟩ := hint x hx y hy
        exact Submodule.mem_one.2 ⟨n, by rw [imForm_apply, hn]; simp⟩)
  refine ⟨M, N, Ef, h1, h2, fun x hx => ?_, h4, h5, h6, h7⟩
  rw [Nat.cast_smul_eq_nsmul]
  exact h3 x hx
end GlobalTheory.UnimodOver
