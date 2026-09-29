-- Prove2me | solution 1 for LeanEval.Geometry.SpaceGroupsProblem.euclideanGroup_linPart_extension
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T08:25:55.915602+00:00
-- url     : https://prove2.me/submissions/3bfe65fd-6d22-4dc1-b11c-d860fec5a3d4

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupsPointGroupDefs

open LeanEval.Geometry.SpaceGroupsProblem

namespace SpaceGroupsExtension

variable {d : ℕ}

/-- The linear part homomorphism of a group of Euclidean isometries. -/
noncomputable def linPartHom (G : Subgroup (EuclideanIsom d)) : G →* (E d ≃ₗᵢ[ℝ] E d) where
  toFun g := linPart g.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The range of the linear part homomorphism is the point group. -/
theorem linPartHom_range (G : Subgroup (EuclideanIsom d)) :
    (linPartHom G).range = pointGroup G := by
  ext A
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

/-- An isometry with trivial linear part is a translation. -/
theorem isTranslation_of_linPart_eq_one {g : EuclideanIsom d} (h : linPart g = 1) :
    IsTranslationBy g (g 0) := by
  intro x
  have hx : linPart g x = g (0 + x) - g 0 := linPart_apply_add g 0 x
  rw [h] at hx
  simp only [LinearIsometryEquiv.coe_one, id_eq, zero_add] at hx
  exact sub_eq_iff_eq_add.mp hx.symm

/-- A translation has trivial linear part. -/
theorem linPart_eq_one_of_isTranslation {g : EuclideanIsom d} {v : E d}
    (hv : IsTranslationBy g v) : linPart g = 1 := by
  apply LinearIsometryEquiv.ext
  intro x
  have hx : linPart g x = g (0 + x) - g 0 := linPart_apply_add g 0 x
  rw [hv (0 + x), hv 0] at hx
  simp only [zero_add] at hx
  simp [hx]

end SpaceGroupsExtension

open SpaceGroupsExtension

theorem solution {d : ℕ} (G : Subgroup (EuclideanIsom d)) :
    ∃ f : G →* (E d ≃ₗᵢ[ℝ] E d),
      (∀ g : G, f g = linPart g.1) ∧
      f.range = pointGroup G ∧
      (∀ g : G, g ∈ f.ker ↔ ∃ v, IsTranslationBy g.1 v) ∧
      Nonempty ((G ⧸ f.ker) ≃* pointGroup G) := by
  refine ⟨linPartHom G, fun g => rfl, linPartHom_range G, ?_, ?_⟩
  · intro g
    constructor
    · intro h
      have h1 : linPart g.1 = 1 := h
      exact ⟨g.1 0, isTranslation_of_linPart_eq_one h1⟩
    · rintro ⟨v, hv⟩
      show linPart g.1 = 1
      exact linPart_eq_one_of_isTranslation hv
  · exact ⟨(QuotientGroup.quotientKerEquivRange (linPartHom G)).trans
      (MulEquiv.subgroupCongr (linPartHom_range G))⟩
