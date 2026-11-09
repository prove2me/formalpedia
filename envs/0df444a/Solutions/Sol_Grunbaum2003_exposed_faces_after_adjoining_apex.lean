-- Prove2me | solution 1 for Grunbaum2003.exposed_faces_after_adjoining_apex
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:41:02.724295+00:00
-- url     : https://prove2.me/submissions/973b7b4b-cb6d-482a-864c-976a4b4ab4f2

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003

private lemma exposed_eq_level {d : ℕ} {P : Set (Fin d → ℝ)}
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) {w : Fin d → ℝ} (hw : w ∈ P)
    (hmax : ∀ x ∈ P, φ x ≤ φ w) :
    φ.toExposed P = {x ∈ P | φ x = φ w} := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, le_antisymm (hmax x hx.1) (hx.2 w hw)⟩
  · rintro ⟨hx, heq⟩
    exact ⟨hx, fun z hz => by rw [heq]; exact hmax z hz⟩

private lemma hull_bound {d : ℕ} {P : Set (Fin d → ℝ)}
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (c : ℝ)
    (hmax : ∀ x ∈ P, φ x ≤ c) {y : Fin d → ℝ} (hy : φ y ≤ c) :
    ∀ x ∈ convexHull ℝ (insert y P), φ x ≤ c := by
  apply convexHull_min
  · intro x hx
    rcases hx with rfl | hx
    · exact hy
    · exact hmax x hx
  · exact (convex_Iic c).linear_preimage φ.toLinearMap

/-- Adding an apex changes each support maximizer set according to its height
relative to the old support value. -/
theorem exposed_insert_trichotomy {d : ℕ} {P : Set (Fin d → ℝ)} (hP : Convex ℝ P)
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (w : Fin d → ℝ) (hw : w ∈ P)
    (hmax : ∀ x ∈ P, φ x ≤ φ w) (y : Fin d → ℝ) :
    (φ y < φ w → φ.toExposed (convexHull ℝ (insert y P)) = φ.toExposed P) ∧
    (φ y = φ w → φ.toExposed (convexHull ℝ (insert y P)) =
      convexHull ℝ (insert y (φ.toExposed P))) ∧
    (φ w < φ y → φ.toExposed (convexHull ℝ (insert y P)) = {y}) := by
  have hrepr (x : Fin d → ℝ) (hx : x ∈ convexHull ℝ (insert y P)) :
      ∃ z ∈ P, ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧
        a • y + b • z = x := by
    rw [convexHull_insert ⟨w, hw⟩, hP.convexHull_eq, mem_convexJoin] at hx
    rcases hx with ⟨y', hy', z, hz, a, b, ha, hb, hab, hx⟩
    obtain rfl : y' = y := hy'
    exact ⟨z, hz, a, b, ha, hb, hab, hx⟩
  have hwHull : w ∈ convexHull ℝ (insert y P) :=
    subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hw)
  have hyHull : y ∈ convexHull ℝ (insert y P) :=
    subset_convexHull ℝ _ (Set.mem_insert _ _)
  refine ⟨?_, ?_, ?_⟩
  · intro hy
    rw [exposed_eq_level φ hwHull (hull_bound φ (φ w) hmax hy.le),
      exposed_eq_level φ hw hmax]
    ext x
    constructor
    · rintro ⟨hx, heq⟩
      obtain ⟨z, hz, a, b, ha, hb, hab, hrep⟩ := hrepr x hx
      have heq' := congrArg φ hrep
      simp only [map_add, map_smul, smul_eq_mul] at heq'
      have hs : a * φ w + b * φ w = φ w := by rw [← add_mul, hab, one_mul]
      have ha0 : a = 0 := by
        apply le_antisymm _ ha
        by_contra! hapos
        have hgap := mul_pos hapos (sub_pos.mpr hy)
        have hgap' := mul_nonneg hb (sub_nonneg.mpr (hmax z hz))
        nlinarith
      have hb1 : b = 1 := by linarith
      have hxz : x = z := by simpa [ha0, hb1] using hrep.symm
      exact ⟨hxz ▸ hz, heq⟩
    · rintro ⟨hx, heq⟩
      exact ⟨subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hx), heq⟩
  · intro hy
    rw [exposed_eq_level φ hwHull (hull_bound φ (φ w) hmax hy.le)]
    apply Set.Subset.antisymm
    · rintro x ⟨hx, heq⟩
      obtain ⟨z, hz, a, b, ha, hb, hab, hrep⟩ := hrepr x hx
      have heq' := congrArg φ hrep
      simp only [map_add, map_smul, smul_eq_mul, hy] at heq'
      have hs : a * φ w + b * φ w = φ w := by rw [← add_mul, hab, one_mul]
      by_cases hb0 : b = 0
      · have ha1 : a = 1 := by linarith
        have hxy : x = y := by simpa [hb0, ha1] using hrep.symm
        rw [hxy]
        exact subset_convexHull ℝ _ (Set.mem_insert _ _)
      · have hzmax : φ z = φ w := by
          apply le_antisymm (hmax z hz)
          by_contra! hzlt
          have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
          have hgap := mul_pos hbpos (sub_pos.mpr hzlt)
          nlinarith
        have hzF : z ∈ φ.toExposed P := by
          rw [exposed_eq_level φ hw hmax]
          exact ⟨hz, hzmax⟩
        rw [← hrep]
        exact (convex_convexHull ℝ _)
          (subset_convexHull ℝ _ (Set.mem_insert _ _))
          (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hzF)) ha hb hab
    · have hsub : insert y (φ.toExposed P) ⊆
          {x ∈ convexHull ℝ (insert y P) | φ x = φ w} := by
        intro x hx
        rcases hx with rfl | hx
        · exact ⟨hyHull, hy⟩
        · exact ⟨subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hx.1),
            le_antisymm (hmax x hx.1) (hx.2 w hw)⟩
      apply convexHull_min hsub
      exact (convex_convexHull ℝ _).inter
        ((convex_singleton (φ w)).linear_preimage φ.toLinearMap)
  · intro hy
    have hmaxY : ∀ x ∈ P, φ x ≤ φ y := fun x hx => (hmax x hx).trans hy.le
    rw [exposed_eq_level φ hyHull (hull_bound φ (φ y) hmaxY le_rfl)]
    ext x
    constructor
    · rintro ⟨hx, heq⟩
      obtain ⟨z, hz, a, b, ha, hb, hab, hrep⟩ := hrepr x hx
      have heq' := congrArg φ hrep
      simp only [map_add, map_smul, smul_eq_mul] at heq'
      have hs : a * φ y + b * φ y = φ y := by rw [← add_mul, hab, one_mul]
      have hb0 : b = 0 := by
        apply le_antisymm _ hb
        by_contra! hbpos
        have hgap := mul_pos hbpos (sub_pos.mpr (lt_of_le_of_lt (hmax z hz) hy))
        nlinarith
      have ha1 : a = 1 := by linarith
      simpa [hb0, ha1] using hrep.symm
    · intro hx
      obtain rfl : x = y := hx
      exact ⟨hyHull, rfl⟩

end Grunbaum2003

open Grunbaum2003

/-- Support-height formulas and the resulting classification of every nonempty
exposed face after adjoining a point to a compact convex set. -/
theorem solution {d : ℕ} {P : Set (Fin d → ℝ)} (hP : Convex ℝ P)
    (hcompact : IsCompact P) (hPne : P.Nonempty) (y : Fin d → ℝ) :
    (∀ (φ : (Fin d → ℝ) →L[ℝ] ℝ) (w : Fin d → ℝ), w ∈ P →
      (∀ x ∈ P, φ x ≤ φ w) →
      (φ y < φ w → φ.toExposed (convexHull ℝ (insert y P)) = φ.toExposed P) ∧
      (φ y = φ w → φ.toExposed (convexHull ℝ (insert y P)) =
        convexHull ℝ (insert y (φ.toExposed P))) ∧
      (φ w < φ y → φ.toExposed (convexHull ℝ (insert y P)) = {y})) ∧
    (∀ F : Set (Fin d → ℝ), F.Nonempty →
      IsExposed ℝ (convexHull ℝ (insert y P)) F →
      F = {y} ∨ IsExposed ℝ P F ∨
        ∃ G : Set (Fin d → ℝ), G.Nonempty ∧ IsExposed ℝ P G ∧
          F = convexHull ℝ (insert y G)) := by
  refine ⟨fun φ w hw hmax => exposed_insert_trichotomy hP φ w hw hmax y, ?_⟩
  intro F hFne hF
  obtain ⟨φ, hφ⟩ := hF hFne
  obtain ⟨w, hw, hmax⟩ := hcompact.exists_isMaxOn hPne φ.continuous.continuousOn
  have hEq : F = φ.toExposed (convexHull ℝ (insert y P)) := hφ
  have hsplit := exposed_insert_trichotomy hP φ w hw hmax y
  rcases lt_trichotomy (φ y) (φ w) with hlt | heq | hgt
  · right; left
    rw [hEq, hsplit.1 hlt]
    exact ContinuousLinearMap.toExposed.isExposed (l := φ)
  · right; right
    exact ⟨φ.toExposed P, ⟨w, hw, hmax⟩,
      ContinuousLinearMap.toExposed.isExposed (l := φ),
      hEq.trans (hsplit.2.1 heq)⟩
  · exact Or.inl (hEq.trans (hsplit.2.2 hgt))
