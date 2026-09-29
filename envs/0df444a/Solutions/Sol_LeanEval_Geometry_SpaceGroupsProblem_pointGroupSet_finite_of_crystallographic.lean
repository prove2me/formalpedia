-- Prove2me | solution 1 for LeanEval.Geometry.SpaceGroupsProblem.pointGroupSet_finite_of_crystallographic
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T07:33:14.345142+00:00
-- url     : https://prove2.me/submissions/77675ccc-0226-4351-9b19-571c327f8cc1

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupsPointGroupDefs

open LeanEval.Geometry.SpaceGroupsProblem

namespace SpaceGroupsPointGroupFinite

variable {d : ℕ}

/-- In a discrete group, only finitely many translation vectors are bounded by `r`. -/
theorem transVectors_bounded_finite {G : Subgroup (EuclideanIsom d)} (hd : IsDiscrete G)
    (r : ℝ) : {v | v ∈ transVectors G ∧ ‖v‖ ≤ r}.Finite := by
  have hpos : (0 : ℝ) < max r 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hfin := hd 0 (max r 1) hpos
  refine Set.Finite.subset (hfin.image (fun g : EuclideanIsom d => g 0)) ?_
  rintro v ⟨⟨g, hgG, hg⟩, hv⟩
  refine ⟨g, ⟨hgG, ?_⟩, ?_⟩
  · have hg0 : g 0 = v := by simpa using hg 0
    rw [hg0]
    simpa [dist_eq_norm] using le_trans hv (le_max_left _ _)
  · simpa using hg 0

/-- The point group acts on the translation vectors. -/
theorem linPart_mem_transVectors {G : Subgroup (EuclideanIsom d)} {g : EuclideanIsom d}
    (hg : g ∈ G) {v : E d} (hv : v ∈ transVectors G) : linPart g v ∈ transVectors G := by
  obtain ⟨t, htG, ht⟩ := hv
  refine ⟨g * t * g⁻¹, G.mul_mem (G.mul_mem hg htG) (G.inv_mem hg), ?_⟩
  intro x
  have h1 : (g * t * g⁻¹) x = g (t (g⁻¹ x)) := rfl
  rw [h1, ht (g⁻¹ x)]
  have h2 : linPart g v = g (g⁻¹ x + v) - g (g⁻¹ x) := linPart_apply_add g (g⁻¹ x) v
  have h3 : g (g⁻¹ x) = x := by
    have : (g * g⁻¹) x = x := by simp
    simpa using this
  rw [h3] at h2
  rw [h2]
  abel

/-- Two linear isometries agreeing on a spanning family are equal. -/
theorem linIsom_ext_of_span {A B : E d ≃ₗᵢ[ℝ] E d} {v : Fin d → E d}
    (hv : LinearIndependent ℝ v) (h : ∀ i, A (v i) = B (v i)) : A = B := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    exact LinearIsometryEquiv.ext fun x => Subsingleton.elim _ _
  · haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    have hspan : Submodule.span ℝ (Set.range v) = ⊤ :=
      hv.span_eq_top_of_card_eq_finrank (by simp)
    apply LinearIsometryEquiv.toLinearEquiv_injective
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext_on hspan
    rintro x ⟨i, rfl⟩
    exact h i

end SpaceGroupsPointGroupFinite

open SpaceGroupsPointGroupFinite

theorem solution {d : ℕ} {G : Subgroup (EuclideanIsom d)} (hG : IsCrystallographicGroup G) :
    (pointGroupSet G).Finite := by
  obtain ⟨v, hvli, hvmem⟩ := hG.cocompact
  have hvT : ∀ i, v i ∈ transVectors G := fun i => by
    obtain ⟨g, hgG, hg⟩ := hvmem i
    exact ⟨g, hgG, hg⟩
  set S : Set (Fin d → E d) :=
    {w | ∀ i, w i ∈ transVectors G ∧ ‖w i‖ ≤ ‖v i‖} with hS
  have hSfin : S.Finite := by
    have hsub : S ⊆ Set.univ.pi (fun i => {u | u ∈ transVectors G ∧ ‖u‖ ≤ ‖v i‖}) := by
      intro w hw i _
      exact hw i
    exact Set.Finite.subset
      (Set.Finite.pi (fun i => transVectors_bounded_finite hG.discrete (‖v i‖))) hsub
  have himg : (fun A : E d ≃ₗᵢ[ℝ] E d => fun i => A (v i)) '' pointGroupSet G ⊆ S := by
    rintro w ⟨A, ⟨g, hgG, rfl⟩, rfl⟩
    intro i
    refine ⟨linPart_mem_transVectors hgG (hvT i), ?_⟩
    simp [linPart]
  refine Set.Finite.of_finite_image (Set.Finite.subset hSfin himg) ?_
  intro A _ B _ hAB
  exact linIsom_ext_of_span hvli (fun i => congrFun hAB i)
