-- Prove2me | solution 1 for Grunbaum2003.polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T01:30:30.398738+00:00
-- url     : https://prove2.me/submissions/67e149ef-ae3f-45b4-94d3-38acc22b7d6e

import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Mathlib.LinearAlgebra.Dimension.Finrank
import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_faceCount
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

open scoped Classical

namespace Grunbaum2003

/-- A nonempty exposed face of `P` has affine direction finrank `0` if and only if
it is a singleton exposed vertex `{x}`. -/
theorem nonempty_exposed_finrank_zero_iff_singleton {d : ℕ}
    (P F : Set (Fin d → ℝ)) :
    (F.Nonempty ∧ IsExposed ℝ P F ∧
      Module.finrank ℝ (affineSpan ℝ F).direction = 0) ↔
    ∃ x : Fin d → ℝ, IsExposed ℝ P {x} ∧ F = {x} := by
  constructor
  · rintro ⟨hne, hF, hRank⟩
    have hDir : (affineSpan ℝ F).direction = ⊥ := Submodule.finrank_eq_zero.mp hRank
    have hSpan : vectorSpan ℝ F = ⊥ := by rwa [direction_affineSpan] at hDir
    have hSub : F.Subsingleton := (vectorSpan_eq_bot_iff_subsingleton ℝ).mp hSpan
    obtain ⟨x, hx⟩ := hne
    have hEq : F = {x} := hSub.eq_singleton_of_mem hx
    refine ⟨x, hEq ▸ hF, hEq⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨Set.singleton_nonempty x, hx, ?_⟩
    rw [direction_affineSpan, vectorSpan_singleton, finrank_bot]

/-- The zero-dimensional face count `faceCount P 0` equals the `Set.ncard` of singleton
exposed vertices of `P`. -/
theorem faceCount_zero_eq_exposed_vertices_ncard {d : ℕ}
    (P : Set (Fin d → ℝ)) :
    faceCount P 0 = {x : Fin d → ℝ | IsExposed ℝ P {x}}.ncard := by
  have hImg :
      (fun x : Fin d → ℝ => ({x} : Set (Fin d → ℝ))) ''
        {x : Fin d → ℝ | IsExposed ℝ P {x}} =
      {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = 0} := by
    ext F
    change F ∈ (fun x : Fin d → ℝ => ({x} : Set (Fin d → ℝ))) ''
        {x : Fin d → ℝ | IsExposed ℝ P {x}} ↔
      (F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = 0)
    rw [nonempty_exposed_finrank_zero_iff_singleton]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  unfold faceCount
  rw [← hImg]
  exact Set.ncard_image_of_injective _ Set.singleton_injective

/-- Every full-dimensional `d`-polytope `P ⊆ ℝ^d` satisfying the exposed-vertex hull
representation has at least `d + 1` zero-dimensional exposed faces (`d + 1 ≤ faceCount P 0`). -/
theorem d_add_one_le_faceCount_zero {d : ℕ} (P : Set (Fin d → ℝ))
    (hP : IsDPolytope P)
    (hHull : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) :
    d + 1 ≤ faceCount P 0 := by
  let V : Set (Fin d → ℝ) := {x : Fin d → ℝ | IsExposed ℝ P {x}}
  have hPEq : P = convexHull ℝ (P ∩ V) := hHull.2 ⟨P, IsExposed.refl P⟩
  have hPne : P.Nonempty := by
    obtain ⟨W, _, hWne, hPW⟩ := hP.1
    rw [hPW]
    exact hWne.convexHull
  have hPVne : (P ∩ V).Nonempty := by
    apply (convexHull_nonempty_iff (𝕜 := ℝ)).mp
    rwa [← hPEq]
  obtain ⟨v₀, _, hv₀⟩ := hPVne
  have hAffV : affineSpan ℝ V = ⊤ := by
    apply top_unique
    calc (⊤ : AffineSubspace ℝ (Fin d → ℝ))
      _ = affineSpan ℝ P := hP.2.symm
      _ = affineSpan ℝ (convexHull ℝ (P ∩ V)) := by rw [← hPEq]
      _ = affineSpan ℝ (P ∩ V) := affineSpan_convexHull (P ∩ V)
      _ ≤ affineSpan ℝ V := affineSpan_mono ℝ Set.inter_subset_right
  have hRankDir : Module.finrank ℝ (affineSpan ℝ V).direction = d := by
    rw [hAffV, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun]
  let S : Finset (Fin d → ℝ) := hHull.1.toFinset
  let T : Finset (Fin d → ℝ) := (S.erase v₀).image (fun x => x -ᵥ v₀)
  have hSpanLe : (affineSpan ℝ V).direction ≤ Submodule.span ℝ (T : Set (Fin d → ℝ)) := by
    rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ hv₀, Submodule.span_le]
    rintro u ⟨x, hxV, rfl⟩
    dsimp only
    by_cases hxv : x = v₀
    · subst x
      rw [vsub_self]
      exact Submodule.zero_mem _
    · apply Submodule.subset_span
      change x -ᵥ v₀ ∈ (T : Set (Fin d → ℝ))
      rw [Finset.coe_image]
      refine ⟨x, ?_, rfl⟩
      rw [Finset.mem_coe, Finset.mem_erase]
      exact ⟨hxv, hHull.1.mem_toFinset.mpr hxV⟩
  have hRankLe : d ≤ (S.erase v₀).card := by
    calc d = Module.finrank ℝ (affineSpan ℝ V).direction := hRankDir.symm
      _ ≤ Module.finrank ℝ (Submodule.span ℝ (T : Set (Fin d → ℝ))) :=
          Submodule.finrank_mono hSpanLe
      _ ≤ T.card := finrank_span_finset_le_card T
      _ ≤ (S.erase v₀).card := Finset.card_image_le
  have hv₀S : v₀ ∈ S := hHull.1.mem_toFinset.mpr hv₀
  have hCardS : (S.erase v₀).card + 1 = S.card := Finset.card_erase_add_one hv₀S
  have hNcardV : V.ncard = S.card := Set.ncard_eq_toFinset_card V hHull.1
  rw [faceCount_zero_eq_exposed_vertices_ncard P]
  change d + 1 ≤ V.ncard
  omega

end Grunbaum2003

namespace Grunbaum2003

theorem polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound_proved :
  ∀ (d : ℕ) (P : Set (Fin d → ℝ)),
    faceCount P 0 = {x : Fin d → ℝ | IsExposed ℝ P {x}}.ncard ∧
    (IsDPolytope P → d + 1 ≤ faceCount P 0) := by
  intro d P
  refine ⟨faceCount_zero_eq_exposed_vertices_ncard P, fun hP => ?_⟩
  exact d_add_one_le_faceCount_zero P hP
    (polytope_face_eq_convexHull_exposed_vertices d P hP)

end Grunbaum2003

theorem solution :
  ∀ (d : ℕ) (P : Set (Fin d → ℝ)),
    Grunbaum2003.faceCount P 0 = {x : Fin d → ℝ | IsExposed ℝ P {x}}.ncard ∧
    (Grunbaum2003.IsDPolytope P → d + 1 ≤ Grunbaum2003.faceCount P 0) :=
  Grunbaum2003.polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound_proved
