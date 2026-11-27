-- Prove2me | solution 1 for GlobalTheory.exists_siegel_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:38:26.119512+00:00
-- url     : https://prove2.me/submissions/2cb182ab-5613-4db9-9ee5-9a19ea3615c5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsOpenPosDefOfContinuous
import Theorems.Thm_GlobalTheory_isOpen_posDef_of_continuous
import Theorems.Thm_GlobalTheory_card_sym2_fin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ h : ℕ, ∃ (B : Set (Fin (h * (h + 1) / 2) → ℂ)) (τ : (Fin (h * (h + 1) / 2) → ℂ) → Matrix (Fin h) (Fin h) ℂ), IsOpen B ∧ Convex ℝ B ∧ (∀ i j, Differentiable ℂ (fun b => τ b i j)) ∧ (∀ b ∈ B, (τ b).IsSymm ∧ ((τ b).map Complex.im).PosDef) ∧ ∀ t : Matrix (Fin h) (Fin h) ℂ, t.IsSymm → (t.map Complex.im).PosDef → ∃! b, b ∈ B ∧ τ b = t := by
  intro h
  let e : Sym2 (Fin h) ≃ Fin (h * (h + 1) / 2) := Fintype.equivFinOfCardEq (card_sym2_fin h)
  let τ : (Fin (h * (h + 1) / 2) → ℂ) → Matrix (Fin h) (Fin h) ℂ :=
    fun b => Matrix.of fun i j => b (e s(i, j))
  have hτ : ∀ b i j, τ b i j = b (e s(i, j)) := fun _ _ _ => rfl
  have hsymm : ∀ b, (τ b).IsSymm := by
    intro b
    ext i j
    rw [Matrix.transpose_apply, hτ, hτ, Sym2.eq_swap]
  refine ⟨{b | ((τ b).map Complex.im).PosDef}, τ, ?_, ?_, ?_, ?_, ?_⟩
  · apply isOpen_posDef_of_continuous (fun b => (τ b).map Complex.im)
    · refine continuous_matrix fun i j => ?_
      exact Complex.continuous_im.comp (continuous_apply (e s(i, j)))
    · intro b
      ext i j
      simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.map_apply, hτ]
      rw [Sym2.eq_swap]
  · intro x hx y hy a b ha hb hab
    have key : (τ (a • x + b • y)).map Complex.im
        = a • (τ x).map Complex.im + b • (τ y).map Complex.im := by
      ext i j
      simp [hτ]
    change ((τ (a • x + b • y)).map Complex.im).PosDef
    rw [key]
    rcases ha.eq_or_lt with rfl | ha'
    · have : b = 1 := by simpa using hab
      subst this
      simpa using hy
    · exact (Matrix.PosDef.smul hx ha').add_posSemidef
        (Matrix.PosSemidef.smul (Matrix.PosDef.posSemidef hy) hb)
  · intro i j
    exact differentiable_apply (𝕜 := ℂ) (e s(i, j))
  · intro b hb
    exact ⟨hsymm b, hb⟩
  · intro t ht hp
    let f : Sym2 (Fin h) → ℂ := Sym2.lift ⟨fun i j => t i j, fun i j => (ht.apply i j).symm⟩
    have hf : τ (fun k => f (e.symm k)) = t := by
      ext i j
      change f (e.symm (e s(i, j))) = t i j
      rw [Equiv.symm_apply_apply]
      rfl
    refine ⟨fun k => f (e.symm k), ⟨?_, hf⟩, ?_⟩
    · change ((τ (fun k => f (e.symm k))).map Complex.im).PosDef
      rw [hf]; exact hp
    · rintro b ⟨-, hb⟩
      funext k
      obtain ⟨z, rfl⟩ := e.surjective k
      induction z using Sym2.ind with
      | _ i j =>
        rw [Equiv.symm_apply_apply]
        exact congrFun (congrFun hb i) j
end GlobalTheory
