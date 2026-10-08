-- Prove2me | solution 1 for GrayStability.moser_equation_unique_solution
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T15:14:52.621659+00:00
-- url     : https://prove2.me/submissions/fa25dc79-1dcd-4cba-994e-7a4cca0f7d33

import Definitions.Def_GrayStability_Basic
import Theorems.Thm_ContactLinearAlgebra_moser_equation_exists_unique
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.Ring

set_option autoImplicit false
open GrayStability

theorem solution {n c : ℕ} (F : E n → (Fin c → ℝ))
    (hF : IsCompactRegularLevel F) (α : OneForm n) (y : E n) (hy : y ∈ levelSet F)
    (hα : IsContactFormAt F α y) (β : E n →L[ℝ] ℝ) :
    ∃! X : E n, X ∈ contactPlane F α y ∧ ∃ μ : ℝ,
      ∀ v ∈ tangentSpace F y, β v + extDerivOneForm α y X v = μ * α y v := by
  let T := (fderiv ℝ F y).toLinearMap.ker
  let a : T →ₗ[ℝ] ℝ := (α y).toLinearMap.comp T.subtype
  let b : T →ₗ[ℝ] T →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ
    (fun u v => extDerivOneForm α y u v)
    (by intros; simp [extDerivOneForm, map_add]; ring)
    (by intros; simp [extDerivOneForm, map_smul]; ring)
    (by intros; simp [extDerivOneForm, map_add]; ring)
    (by intros; simp [extDerivOneForm, map_smul]; ring)
  have ha : ∃ v, a v ≠ 0 := by
    obtain ⟨v, hv, h⟩ := hα.1
    exact ⟨⟨v, hv⟩, h⟩
  have hn : ∀ u, a u = 0 → (∀ v, a v = 0 → b u v = 0) → u = 0 := by
    intro u hu hz
    apply Subtype.ext
    change (u : E n) = 0
    by_contra h
    obtain ⟨v, hv, hne⟩ := hα.2 u ⟨u.property, hu⟩ h
    exact hne (hz ⟨v, hv.1⟩ hv.2)
  obtain ⟨X, hX, huniq⟩ := ContactLinearAlgebra.moser_equation_exists_unique
    a b ha hn (β.toLinearMap.comp T.subtype)
  obtain ⟨haX, μ, hμ⟩ := hX
  refine ⟨X, ⟨⟨X.property, haX⟩, μ, ?_⟩, ?_⟩
  · intro v hv
    exact hμ ⟨v, hv⟩
  · rintro Y ⟨hY, ν, hν⟩
    exact congrArg Subtype.val (huniq ⟨Y, hY.1⟩
      ⟨hY.2, ν, fun v => hν v v.property⟩)
