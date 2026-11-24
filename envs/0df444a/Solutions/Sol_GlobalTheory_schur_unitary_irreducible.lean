-- Prove2me | solution 1 for GlobalTheory.schur_unitary_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:39:43.621404+00:00
-- url     : https://prove2.me/submissions/9be25b61-4f00-4b9e-ad82-bd30982706bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfAdjointEqAlgebraMapOfCommuteIrreducible
import Theorems.Thm_GlobalTheory_selfAdjoint_eq_algebraMap_of_commute_irreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (G H : Type) [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : G →* (H →L[ℂ] H))
    (hπ : ∀ g u, ‖π g u‖ = ‖u‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ u ∈ S, π g u ∈ S) →
      S = ⊥ ∨ S = ⊤)
    (T : H →L[ℂ] H) (hT : ∀ g, T * π g = π g * T) : ∃ c : ℂ, T = c • 1 := by
  classical
  have hinner : ∀ g (u v : H), ⟪π g u, π g v⟫_ℂ = ⟪u, v⟫_ℂ := by
    intro g u v
    let L : H →ₗᵢ[ℂ] H := ⟨(π g).toLinearMap, hπ g⟩
    exact L.inner_map_map u v
  have hinv : ∀ g (v : H), π g (π g⁻¹ v) = v := by
    intro g v
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  have hadj : ∀ g, ContinuousLinearMap.adjoint (π g) = π g⁻¹ := by
    intro g
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro u v
    rw [← hinner g (π g⁻¹ u) v, hinv]
  have hstar : ∀ g, star (π g) = π g⁻¹ := hadj
  have hcT : ∀ g, Commute T (π g) := fun g => hT g
  have hcS : ∀ g, Commute (star T) (π g) := by
    intro g
    have h1 := (hcT g⁻¹).star_star
    rw [hstar, inv_inv] at h1
    exact h1
  have hre : ∀ g, Commute (realPart T : H →L[ℂ] H) (π g) := by
    intro g
    rw [realPart_apply_coe]
    exact ((hcT g).add_left (hcS g)).smul_left _
  have him : ∀ g, Commute (imaginaryPart T : H →L[ℂ] H) (π g) := by
    intro g
    rw [imaginaryPart_apply_coe]
    exact (((hcT g).sub_left (hcS g)).smul_left _).smul_left _
  obtain ⟨a, ha⟩ := selfAdjoint_eq_algebraMap_of_commute_irreducible (⇑π) hirr _ (realPart T).2 hre
  obtain ⟨b, hb⟩ := selfAdjoint_eq_algebraMap_of_commute_irreducible (⇑π) hirr _ (imaginaryPart T).2 him
  refine ⟨(a : ℂ) + Complex.I * (b : ℂ), ?_⟩
  rw [← realPart_add_I_smul_imaginaryPart T, ha, hb, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, add_smul, mul_smul, ← Complex.coe_smul, ← Complex.coe_smul]
end GlobalTheory
