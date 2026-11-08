-- Prove2me | solution 1 for Grunbaum2003.skeleton_iso_preserves_exposed_vertices_and_reduces_downSet
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T01:30:29.815032+00:00
-- url     : https://prove2.me/submissions/24907cc4-60af-47fb-b9b5-4a0d96e98aac

import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

namespace Grunbaum2003

/-- The empty exposed face as an element of the `k`-skeleton poset. -/
def emptySkeletonFace {d : ℕ} (P : Set (Fin d → ℝ)) (k : ℕ) : SkeletonFace P k :=
  ⟨⟨∅, fun h => False.elim (Set.not_nonempty_empty h)⟩, Or.inl rfl⟩

/-- Any exposed singleton vertex `{x}` belongs to the `k`-skeleton poset for every `k : ℕ`. -/
def vertexSkeletonFace {d : ℕ} (P : Set (Fin d → ℝ)) (k : ℕ)
    (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}) : SkeletonFace P k :=
  ⟨⟨{x}, hx⟩, Or.inr (by
    rw [direction_affineSpan, vectorSpan_singleton, finrank_bot]
    exact Nat.zero_le k)⟩

@[simp]
theorem vertexSkeletonFace_val_val {d : ℕ} (P : Set (Fin d → ℝ)) (k : ℕ)
    (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}) :
    (vertexSkeletonFace P k x hx).val.val = {x} := rfl

theorem vertexSkeletonFace_le_iff {d : ℕ} {P : Set (Fin d → ℝ)} {k : ℕ}
    (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}) (S : SkeletonFace P k) :
    vertexSkeletonFace P k x hx ≤ S ↔ x ∈ S.val.val := by
  change ({x} : Set (Fin d → ℝ)) ⊆ S.val.val ↔ x ∈ S.val.val
  exact Set.singleton_subset_iff

/-- Under the exposed-vertex hull representation, exposed faces are ordered by
inclusion of their exposed vertex sets. -/
theorem polytopeFace_le_iff_exposed_vertices_subset {d : ℕ} {P : Set (Fin d → ℝ)}
    (hHull : ∀ E : PolytopeFace P,
      E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}))
    (E₁ E₂ : PolytopeFace P) :
    E₁ ≤ E₂ ↔ ∀ x : Fin d → ℝ, IsExposed ℝ P {x} → x ∈ E₁.val → x ∈ E₂.val := by
  constructor
  · intro h x _ hx
    exact h hx
  · intro h
    change E₁.val ⊆ E₂.val
    rw [hHull E₁, hHull E₂]
    apply convexHull_mono
    rintro x ⟨hx₁, hxExp⟩
    exact ⟨h x hxExp hx₁, hxExp⟩

/-- Under the exposed-vertex hull representation, an exposed face is nonempty if and only if
it contains at least one exposed vertex. -/
theorem polytopeFace_nonempty_iff_exists_exposed_vertex {d : ℕ} {P : Set (Fin d → ℝ)}
    (hHull : ∀ E : PolytopeFace P,
      E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}))
    (E : PolytopeFace P) :
    E.val.Nonempty ↔ ∃ x : Fin d → ℝ, IsExposed ℝ P {x} ∧ x ∈ E.val := by
  constructor
  · intro hne
    have hne' : (convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})).Nonempty := by
      rwa [← hHull E]
    obtain ⟨x, hxE, hxExp⟩ := (convexHull_nonempty_iff (𝕜 := ℝ)).mp hne'
    exact ⟨x, hxExp, hxE⟩
  · rintro ⟨x, _, hxE⟩
    exact ⟨x, hxE⟩

/-- The empty face is the unique minimum of the `k`-skeleton poset. -/
theorem skeletonFace_eq_empty_iff_le_all {d : ℕ} {P : Set (Fin d → ℝ)} {k : ℕ}
    (S : SkeletonFace P k) :
    S.val.val = ∅ ↔ ∀ T : SkeletonFace P k, S ≤ T := by
  constructor
  · intro hEmpty T
    change S.val.val ⊆ T.val.val
    rw [hEmpty]
    exact Set.empty_subset _
  · intro hAll
    have hSub : S.val.val ⊆ ∅ := hAll (emptySkeletonFace P k)
    exact Set.subset_empty_iff.mp hSub

/-- Any skeleton order isomorphism preserves the empty face and nonemptiness. -/
theorem skeletonIso_empty_iff {d e k l : ℕ}
    {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)}
    (φ : SkeletonFace P k ≃o SkeletonFace Q l) (S : SkeletonFace P k) :
    (φ S).val.val = ∅ ↔ S.val.val = ∅ := by
  rw [skeletonFace_eq_empty_iff_le_all, skeletonFace_eq_empty_iff_le_all]
  constructor
  · intro h T
    exact (φ.map_rel_iff).mp (h (φ T))
  · intro h T
    have h' := (φ.map_rel_iff).mpr (h (φ.symm T))
    simpa only [OrderIso.apply_symm_apply] using h'

theorem skeletonIso_nonempty_iff {d e k l : ℕ}
    {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)}
    (φ : SkeletonFace P k ≃o SkeletonFace Q l) (S : SkeletonFace P k) :
    (φ S).val.val.Nonempty ↔ S.val.val.Nonempty := by
  simp only [Set.nonempty_iff_ne_empty, not_iff_not, skeletonIso_empty_iff]

/-- Under the exposed-vertex hull representation, the atoms above `⊥` in `SkeletonFace P k`
are precisely the singleton exposed vertices. -/
theorem skeletonFace_atom_iff_exists_exposed_singleton {d : ℕ} {P : Set (Fin d → ℝ)} {k : ℕ}
    (hHull : ∀ E : PolytopeFace P,
      E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}))
    (S : SkeletonFace P k) :
    (S.val.val.Nonempty ∧ ∀ T : SkeletonFace P k, T.val.val.Nonempty → T ≤ S → S ≤ T) ↔
      ∃ x : Fin d → ℝ, IsExposed ℝ P {x} ∧ S.val.val = {x} := by
  constructor
  · rintro ⟨hne, hMin⟩
    obtain ⟨x, hxExp, hxS⟩ :=
      (polytopeFace_nonempty_iff_exists_exposed_vertex hHull S.val).mp hne
    let Vx := vertexSkeletonFace P k x hxExp
    have hVxNe : Vx.val.val.Nonempty := Set.singleton_nonempty x
    have hVxLe : Vx ≤ S := (vertexSkeletonFace_le_iff x hxExp S).mpr hxS
    have hSLe : S ≤ Vx := hMin Vx hVxNe hVxLe
    refine ⟨x, hxExp, Set.Subset.antisymm hSLe hVxLe⟩
  · rintro ⟨x, hxExp, hEq⟩
    refine ⟨hEq ▸ Set.singleton_nonempty x, ?_⟩
    intro T hTne hTS
    change S.val.val ⊆ T.val.val
    have hTS' : T.val.val ⊆ S.val.val := hTS
    rw [hEq] at hTS'
    have hTEq : T.val.val = {x} := (Set.Nonempty.subset_singleton_iff hTne).mp hTS'
    rw [hEq, hTEq]

/-- Any skeleton order isomorphism sends every singleton exposed vertex of `P` to a singleton
exposed vertex of `Q`. -/
theorem skeletonIso_maps_exposed_singleton {d e k l : ℕ}
    {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)}
    (hHullP : ∀ E : PolytopeFace P,
      E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}))
    (hHullQ : ∀ E : PolytopeFace Q,
      E.val = convexHull ℝ (E.val ∩ {y : Fin e → ℝ | IsExposed ℝ Q {y}}))
    (φ : SkeletonFace P k ≃o SkeletonFace Q l)
    (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}) :
    ∃ (y : Fin e → ℝ) (hy : IsExposed ℝ Q {y}),
      φ (vertexSkeletonFace P k x hx) = vertexSkeletonFace Q l y hy := by
  let Sx := vertexSkeletonFace P k x hx
  have hAtomP : Sx.val.val.Nonempty ∧
      ∀ T : SkeletonFace P k, T.val.val.Nonempty → T ≤ Sx → Sx ≤ T :=
    (skeletonFace_atom_iff_exists_exposed_singleton hHullP Sx).mpr ⟨x, hx, rfl⟩
  have hAtomQ : (φ Sx).val.val.Nonempty ∧
      ∀ U : SkeletonFace Q l, U.val.val.Nonempty → U ≤ φ Sx → φ Sx ≤ U := by
    refine ⟨(skeletonIso_nonempty_iff φ Sx).mpr hAtomP.1, ?_⟩
    intro U hUne hULe
    have hSymmNe : (φ.symm U).val.val.Nonempty :=
      (skeletonIso_nonempty_iff φ (φ.symm U)).mp (by simpa only [OrderIso.apply_symm_apply] using hUne)
    have hSymmLe : φ.symm U ≤ Sx :=
      (φ.map_rel_iff).mp (by simpa only [OrderIso.apply_symm_apply] using hULe)
    have hSxLe := hAtomP.2 (φ.symm U) hSymmNe hSymmLe
    simpa only [OrderIso.apply_symm_apply] using (φ.map_rel_iff).mpr hSxLe
  obtain ⟨y, hy, hyEq⟩ := (skeletonFace_atom_iff_exists_exposed_singleton hHullQ (φ Sx)).mp hAtomQ
  refine ⟨y, hy, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hyEq

/-- Under the exposed-vertex hull representation on both polytopes, a face `G` of `Q` has
the `φ`-image of the `k`-skeleton down-set of `F` if and only if `G` contains precisely the
`φ`-images of the exposed vertices of `F`. -/
theorem skeletonIso_downSet_iff_vertex_faces_le {d e k l : ℕ}
    {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)}
    (hHullP : ∀ E : PolytopeFace P,
      E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}))
    (hHullQ : ∀ E : PolytopeFace Q,
      E.val = convexHull ℝ (E.val ∩ {y : Fin e → ℝ | IsExposed ℝ Q {y}}))
    (φ : SkeletonFace P k ≃o SkeletonFace Q l)
    (F : PolytopeFace P) (G : PolytopeFace Q) :
    (∀ T : SkeletonFace Q l, T.val ≤ G ↔ (φ.symm T).val ≤ F) ↔
      (∀ (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
        (φ (vertexSkeletonFace P k x hx)).val ≤ G ↔ x ∈ F.val) := by
  constructor
  · intro h x hx
    have hTx := h (φ (vertexSkeletonFace P k x hx))
    rw [OrderIso.symm_apply_apply] at hTx
    exact hTx.trans Set.singleton_subset_iff
  · intro hVert T
    constructor
    · intro hTG
      rw [polytopeFace_le_iff_exposed_vertices_subset hHullP]
      intro x hx hxT
      have hVxLeSymm : vertexSkeletonFace P k x hx ≤ φ.symm T :=
        (vertexSkeletonFace_le_iff x hx (φ.symm T)).mpr hxT
      have hPhiVxLeT : φ (vertexSkeletonFace P k x hx) ≤ T := by
        have h' := (φ.map_rel_iff).mpr hVxLeSymm
        simpa only [OrderIso.apply_symm_apply] using h'
      have hPhiVxLeG : (φ (vertexSkeletonFace P k x hx)).val ≤ G :=
        le_trans hPhiVxLeT hTG
      exact (hVert x hx).mp hPhiVxLeG
    · intro hTF
      rw [polytopeFace_le_iff_exposed_vertices_subset hHullQ]
      intro y hy hyT
      obtain ⟨x, hx, hxEq⟩ :=
        skeletonIso_maps_exposed_singleton hHullQ hHullP φ.symm y hy
      have hPhiEq : φ (vertexSkeletonFace P k x hx) = vertexSkeletonFace Q l y hy := by
        rw [← hxEq, OrderIso.apply_symm_apply]
      have hVyLeT : vertexSkeletonFace Q l y hy ≤ T :=
        (vertexSkeletonFace_le_iff y hy T).mpr hyT
      have hVxLeSymm : vertexSkeletonFace P k x hx ≤ φ.symm T := by
        rw [← hxEq]
        exact (φ.symm.map_rel_iff).mpr hVyLeT
      have hxSymm : x ∈ (φ.symm T).val.val :=
        (vertexSkeletonFace_le_iff x hx (φ.symm T)).mp hVxLeSymm
      have hxF : x ∈ F.val := hTF hxSymm
      have hPhiVxLeG : (φ (vertexSkeletonFace P k x hx)).val ≤ G :=
        (hVert x hx).mpr hxF
      rw [hPhiEq] at hPhiVxLeG
      exact Set.singleton_subset_iff.mp hPhiVxLeG

end Grunbaum2003

namespace Grunbaum2003

theorem skeleton_iso_preserves_exposed_vertices_and_reduces_downSet_proved :
  ∃ (vertexSkeletonFace : ∀ {d : ℕ} (P : Set (Fin d → ℝ)) (k : ℕ)
      (x : Fin d → ℝ), IsExposed ℝ P {x} → SkeletonFace P k),
    (∀ {d : ℕ} (P : Set (Fin d → ℝ)) (k : ℕ) (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
      (vertexSkeletonFace P k x hx).val.val = {x}) ∧
    (∀ {d e k l : ℕ} {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)},
      (∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) →
      (∀ E : PolytopeFace Q,
        E.val = convexHull ℝ (E.val ∩ {y : Fin e → ℝ | IsExposed ℝ Q {y}})) →
      ∀ (φ : SkeletonFace P k ≃o SkeletonFace Q l),
      (∀ S : SkeletonFace P k, (φ S).val.val = ∅ ↔ S.val.val = ∅) ∧
      (∀ (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
        ∃ (y : Fin e → ℝ) (hy : IsExposed ℝ Q {y}),
          φ (vertexSkeletonFace P k x hx) = vertexSkeletonFace Q l y hy) ∧
      (∀ (F : PolytopeFace P) (G : PolytopeFace Q),
        (∀ T : SkeletonFace Q l, T.val ≤ G ↔ (φ.symm T).val ≤ F) ↔
          (∀ (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
            (φ (vertexSkeletonFace P k x hx)).val ≤ G ↔ x ∈ F.val))) := by
  refine ⟨@vertexSkeletonFace, fun P k x hx => rfl, ?_⟩
  intro d e k l P Q hHullP hHullQ φ
  refine ⟨skeletonIso_empty_iff φ,
    skeletonIso_maps_exposed_singleton hHullP hHullQ φ,
    skeletonIso_downSet_iff_vertex_faces_le hHullP hHullQ φ⟩

end Grunbaum2003

open Grunbaum2003 in
theorem solution :
  ∃ (vertexSkeletonFace : ∀ {d : ℕ} (P : Set (Fin d → ℝ)) (k : ℕ)
      (x : Fin d → ℝ), IsExposed ℝ P {x} → SkeletonFace P k),
    (∀ {d : ℕ} (P : Set (Fin d → ℝ)) (k : ℕ) (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
      (vertexSkeletonFace P k x hx).val.val = {x}) ∧
    (∀ {d e k l : ℕ} {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)},
      (∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) →
      (∀ E : PolytopeFace Q,
        E.val = convexHull ℝ (E.val ∩ {y : Fin e → ℝ | IsExposed ℝ Q {y}})) →
      ∀ (φ : SkeletonFace P k ≃o SkeletonFace Q l),
      (∀ S : SkeletonFace P k, (φ S).val.val = ∅ ↔ S.val.val = ∅) ∧
      (∀ (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
        ∃ (y : Fin e → ℝ) (hy : IsExposed ℝ Q {y}),
          φ (vertexSkeletonFace P k x hx) = vertexSkeletonFace Q l y hy) ∧
      (∀ (F : PolytopeFace P) (G : PolytopeFace Q),
        (∀ T : SkeletonFace Q l, T.val ≤ G ↔ (φ.symm T).val ≤ F) ↔
          (∀ (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
            (φ (vertexSkeletonFace P k x hx)).val ≤ G ↔ x ∈ F.val))) :=
  Grunbaum2003.skeleton_iso_preserves_exposed_vertices_and_reduces_downSet_proved
