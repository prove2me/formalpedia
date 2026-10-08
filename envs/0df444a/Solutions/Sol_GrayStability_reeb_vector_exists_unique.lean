-- Prove2me | solution 1 for GrayStability.reeb_vector_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T14:46:59.272646+00:00
-- url     : https://prove2.me/submissions/bcb3e40a-c023-4225-bcf7-428955c78a7c

import Definitions.Def_GrayStability_Basic
import Theorems.Thm_ContactLinearAlgebra_reeb_exists_unique
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.Ring

set_option autoImplicit false
open GrayStability

theorem solution {n c : ℕ} (F : E n → (Fin c → ℝ))
    (hF : IsCompactRegularLevel F) (α : OneForm n) (y : E n) (hy : y ∈ levelSet F)
    (hα : IsContactFormAt F α y) :
    ∃! R : E n, R ∈ tangentSpace F y ∧ α y R = 1 ∧
      ∀ v ∈ tangentSpace F y, extDerivOneForm α y R v = 0 := by
  let T := (fderiv ℝ F y).toLinearMap.ker
  let a : T →ₗ[ℝ] ℝ := (α y).toLinearMap.comp T.subtype
  let b : T →ₗ[ℝ] T →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ
    (fun u v => extDerivOneForm α y u v)
    (by intros; simp [extDerivOneForm, map_add]; ring)
    (by intros; simp [extDerivOneForm, map_smul]; ring)
    (by intros; simp [extDerivOneForm, map_add]; ring)
    (by intros; simp [extDerivOneForm, map_smul]; ring)
  have hb : ∀ v, b v v = 0 := by intro v; exact sub_self _
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
  obtain ⟨R, hR, huniq⟩ := ContactLinearAlgebra.reeb_exists_unique a b hb ha hn
  refine ⟨R, ⟨R.property, hR.1, ?_⟩, ?_⟩
  · intro v hv
    exact hR.2 ⟨v, hv⟩
  · intro S hS
    exact congrArg Subtype.val (huniq ⟨S, hS.1⟩ ⟨hS.2.1, fun v => hS.2.2 v v.property⟩)
