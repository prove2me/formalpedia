-- Prove2me | solution 1 for Grunbaum2003.vertex_figure_lift_shared_skeleton_and_symmetric_forward_iff
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T03:24:26.647069+00:00
-- url     : https://prove2.me/submissions/d92f5aad-6694-4f14-8e58-75ef24457edf

import Definitions.Def_Grunbaum2003_IsDPolytope
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

open scoped BigOperators Classical
noncomputable section

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

/-- Any singleton exposed vertex `{w}` of `P` is extreme in `P`: if `w` lies strictly
between `a ∈ P` and `b ∈ P` on the line segment `[a, b]`, then `a = w` and `b = w`. -/
theorem exposed_singleton_eq_of_lineMap_mem {d : ℕ} {P : Set (Fin d → ℝ)}
    {w a b : Fin d → ℝ} (hw : IsExposed ℝ P {w})
    (ha : a ∈ P) (hb : b ∈ P) {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1)
    (hLine : AffineMap.lineMap a b t = w) :
    a = w ∧ b = w := by
  obtain ⟨l, hl⟩ := hw (Set.singleton_nonempty w)
  have hwMem : w ∈ {x ∈ P | ∀ y ∈ P, l y ≤ l x} := hl ▸ Set.mem_singleton w
  have hla : l a ≤ l w := hwMem.2 a ha
  have hlb : l b ≤ l w := hwMem.2 b hb
  have hLw : (1 - t) * l a + t * l b = l w := by
    have h1 := congrArg l hLine
    rw [AffineMap.lineMap_apply_module, map_add, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul] at h1
    exact h1
  have hlaEq : l a = l w := by nlinarith
  have hlbEq : l b = l w := by nlinarith
  have haMem : a ∈ ({w} : Set (Fin d → ℝ)) := by
    rw [hl]
    exact ⟨ha, fun y hy => (hwMem.2 y hy).trans_eq hlaEq.symm⟩
  have hbMem : b ∈ ({w} : Set (Fin d → ℝ)) := by
    rw [hl]
    exact ⟨hb, fun y hy => (hwMem.2 y hy).trans_eq hlbEq.symm⟩
  exact ⟨Set.mem_singleton_iff.mp haMem, Set.mem_singleton_iff.mp hbMem⟩

/-- The convex hull of two distinct points `{a, b}` has affine direction finrank `1`. -/
theorem finrank_direction_convexHull_pair_eq_one {d : ℕ} {a b : Fin d → ℝ} (hab : a ≠ b) :
    Module.finrank ℝ (affineSpan ℝ (convexHull ℝ ({a, b} : Set (Fin d → ℝ)))).direction = 1 := by
  rw [affineSpan_convexHull, direction_affineSpan, vectorSpan_pair ℝ a b]
  exact finrank_span_singleton (vsub_ne_zero.mpr hab)

/-- Under the exposed-vertex hull representation, a nonempty exposed face `F` of `P` has
affine direction finrank `1` if and only if its set of exposed vertices is a pair `{a, b}`
of two distinct exposed vertices of `P`. -/
theorem nonempty_exposed_finrank_one_iff_exposed_pair {d : ℕ} {P : Set (Fin d → ℝ)}
    (hHull : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}))
    (F : Set (Fin d → ℝ)) (hF : IsExposed ℝ P F) :
    (F.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F).direction = 1) ↔
      ∃ a b : Fin d → ℝ,
        IsExposed ℝ P {a} ∧ IsExposed ℝ P {b} ∧ a ≠ b ∧
        F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} = {a, b} ∧
        F = convexHull ℝ ({a, b} : Set (Fin d → ℝ)) := by
  let VF : Set (Fin d → ℝ) := F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}
  have hFEq : F = convexHull ℝ VF := hHull.2 ⟨F, hF⟩
  constructor
  · rintro ⟨hFne, hRank⟩
    have hVFne : VF.Nonempty := by
      apply (convexHull_nonempty_iff (𝕜 := ℝ)).mp
      rwa [← hFEq]
    obtain ⟨x₀, hx₀⟩ := hVFne
    have hNotSub : ¬VF ⊆ {x₀} := by
      intro hSub
      have hVFEq : VF = {x₀} := Set.Subset.antisymm hSub (Set.singleton_subset_iff.mpr hx₀)
      have hFSing : F = {x₀} := by rw [hFEq, hVFEq, convexHull_singleton]
      rw [hFSing, direction_affineSpan, vectorSpan_singleton, finrank_bot] at hRank
      exact zero_ne_one hRank
    obtain ⟨x₁, hx₁, hx₁Mem⟩ := Set.not_subset.mp hNotSub
    have hx₁₀ : x₁ ≠ x₀ := Set.mem_singleton_iff.not.mp hx₁Mem
    let u : Fin d → ℝ := x₁ -ᵥ x₀
    have hu : u ≠ 0 := vsub_ne_zero.mpr hx₁₀
    obtain ⟨idx, hidx⟩ : ∃ idx : Fin d, u idx ≠ 0 := Function.ne_iff.mp hu
    have huMemDir : u ∈ (affineSpan ℝ F).direction :=
      AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ F hx₁.1) (subset_affineSpan ℝ F hx₀.1)
    have hSpanLe : (ℝ ∙ u) ≤ (affineSpan ℝ F).direction :=
      (Submodule.span_singleton_le_iff_mem u (affineSpan ℝ F).direction).mpr huMemDir
    have hSpanEq : (ℝ ∙ u) = (affineSpan ℝ F).direction :=
      Submodule.eq_of_le_of_finrank_eq hSpanLe
        ((finrank_span_singleton hu).trans hRank.symm)
    let tau : (Fin d → ℝ) → ℝ := fun w => (w idx - x₀ idx) / u idx
    have hLineX : ∀ w ∈ F, AffineMap.lineMap x₀ x₁ (tau w) = w := by
      intro w hwF
      have hwDir : w -ᵥ x₀ ∈ (affineSpan ℝ F).direction :=
        AffineSubspace.vsub_mem_direction
          (subset_affineSpan ℝ F hwF) (subset_affineSpan ℝ F hx₀.1)
      rw [← hSpanEq, Submodule.mem_span_singleton] at hwDir
      obtain ⟨t, ht⟩ := hwDir
      have htIdx : t * u idx = w idx - x₀ idx := by
        have h := congrFun ht idx
        simpa only [Pi.smul_apply, smul_eq_mul, vsub_eq_sub, Pi.sub_apply] using h
      have htEq : tau w = t := by
        dsimp only [tau]
        rw [← htIdx, mul_div_cancel_right₀ _ hidx]
      rw [htEq, AffineMap.lineMap_apply]
      change t • u +ᵥ x₀ = w
      rw [ht, vsub_vadd]
    have hVFfin : VF.Finite := hHull.1.inter_of_right F
    let SF : Finset (Fin d → ℝ) := hVFfin.toFinset
    have hSFne : (SF.image tau).Nonempty :=
      ⟨tau x₀, Finset.mem_image_of_mem tau (hVFfin.mem_toFinset.mpr hx₀)⟩
    have haExists : ∃ a ∈ SF, tau a = (SF.image tau).min' hSFne :=
      Finset.mem_image.mp (Finset.min'_mem (SF.image tau) hSFne)
    have hbExists : ∃ b ∈ SF, tau b = (SF.image tau).max' hSFne :=
      Finset.mem_image.mp (Finset.max'_mem (SF.image tau) hSFne)
    obtain ⟨a, haSF, haMin⟩ := haExists
    obtain ⟨b, hbSF, hbMax⟩ := hbExists
    have haVF : a ∈ VF := hVFfin.mem_toFinset.mp haSF
    have hbVF : b ∈ VF := hVFfin.mem_toFinset.mp hbSF
    have hTauLe : ∀ w ∈ VF, tau a ≤ tau w ∧ tau w ≤ tau b := by
      intro w hwVF
      have hwImg : tau w ∈ SF.image tau :=
        Finset.mem_image_of_mem tau (hVFfin.mem_toFinset.mpr hwVF)
      exact ⟨haMin.symm ▸ Finset.min'_le (SF.image tau) (tau w) hwImg,
        hbMax.symm ▸ Finset.le_max' (SF.image tau) (tau w) hwImg⟩
    have hTauX₀ : tau x₀ = 0 := by
      dsimp only [tau]
      rw [sub_self, zero_div]
    have hTauX₁ : tau x₁ = 1 := by
      dsimp only [tau]
      change u idx / u idx = 1
      exact div_self hidx
    have hTauLt : tau a < tau b := by
      have h0 := (hTauLe x₀ hx₀).1
      have h1 := (hTauLe x₁ hx₁).2
      linarith
    have hab : a ≠ b := by
      intro hEq
      rw [hEq] at hTauLt
      exact lt_irrefl _ hTauLt
    have hVFPair : VF = {a, b} := by
      apply Set.Subset.antisymm
      · intro w hwVF
        let s : ℝ := (tau w - tau a) / (tau b - tau a)
        have hDen : 0 < tau b - tau a := sub_pos.mpr hTauLt
        have hs₀ : 0 ≤ s := div_nonneg (sub_nonneg.mpr (hTauLe w hwVF).1) hDen.le
        have hs₁ : s ≤ 1 := (div_le_one hDen).mpr (by linarith [(hTauLe w hwVF).2])
        have hLineAB : AffineMap.lineMap a b s = w := by
          have haEq := hLineX a haVF.1
          have hbEq := hLineX b hbVF.1
          have hwEq := hLineX w hwVF.1
          rw [← haEq, ← hbEq, ← hwEq]
          ext k
          simp only [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply, smul_eq_mul, s]
          have hDenNe : tau b - tau a ≠ 0 := hDen.ne'
          field_simp [hDenNe]
          ring
        rcases eq_or_lt_of_le hs₀ with hsZero | hsPos
        · rw [← hsZero, AffineMap.lineMap_apply_zero] at hLineAB
          exact Set.mem_insert_iff.mpr (Or.inl hLineAB.symm)
        · rcases eq_or_lt_of_le hs₁ with hsOne | hsLtOne
          · rw [hsOne, AffineMap.lineMap_apply_one] at hLineAB
            exact Set.mem_insert_of_mem a (Set.mem_singleton_iff.mpr hLineAB.symm)
          · have hEqs := exposed_singleton_eq_of_lineMap_mem hwVF.2
              (hF.subset haVF.1) (hF.subset hbVF.1) hsPos hsLtOne hLineAB
            exact False.elim (hab (hEqs.1.trans hEqs.2.symm))
      · rintro w (rfl | rfl)
        · exact haVF
        · exact hbVF
    refine ⟨a, b, haVF.2, hbVF.2, hab, hVFPair, ?_⟩
    rw [hFEq, hVFPair]
  · rintro ⟨a, b, _, _, hab, _, hFPair⟩
    refine ⟨?_, ?_⟩
    · rw [hFPair]
      exact (Set.insert_nonempty a {b}).convexHull
    · rw [hFPair]
      exact finrank_direction_convexHull_pair_eq_one hab

/-- Order-theoretic characterization of `1`-dimensional faces in `SkeletonFace P k`:
a skeleton face `S` has affine direction finrank `1` if and only if the exposed vertex
atoms below `S` are precisely `{a, b}` for two distinct exposed vertices `a ≠ b`. -/
theorem skeletonFace_finrank_one_iff_exists_vertex_pair {d k : ℕ} {P : Set (Fin d → ℝ)}
    (hHull : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}))
    (S : SkeletonFace P k) :
    (S.val.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ S.val.val).direction = 1) ↔
      ∃ (a b : Fin d → ℝ) (ha : IsExposed ℝ P {a}) (hb : IsExposed ℝ P {b}),
        a ≠ b ∧
        ∀ (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
          vertexSkeletonFace P k x hx ≤ S ↔ (x = a ∨ x = b) := by
  rw [nonempty_exposed_finrank_one_iff_exposed_pair hHull S.val.val S.val.property]
  constructor
  · rintro ⟨a, b, ha, hb, hab, hInter, _⟩
    refine ⟨a, b, ha, hb, hab, ?_⟩
    intro x hx
    rw [vertexSkeletonFace_le_iff]
    constructor
    · intro hxS
      have hxMem : x ∈ ({a, b} : Set (Fin d → ℝ)) := hInter ▸ ⟨hxS, hx⟩
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hxMem
    · intro hxAB
      have hxMem : x ∈ ({a, b} : Set (Fin d → ℝ)) := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hxAB
      exact (hInter ▸ hxMem).1
  · rintro ⟨a, b, ha, hb, hab, hVertIff⟩
    have hInter : S.val.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} = {a, b} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hxS, hx⟩
        exact (hVertIff x hx).mp ((vertexSkeletonFace_le_iff x hx S).mpr hxS)
      · rintro (rfl | rfl)
        · exact ⟨(vertexSkeletonFace_le_iff x ha S).mp ((hVertIff x ha).mpr (Or.inl rfl)), ha⟩
        · exact ⟨(vertexSkeletonFace_le_iff x hb S).mp ((hVertIff x hb).mpr (Or.inr rfl)), hb⟩
    refine ⟨a, b, ha, hb, hab, hInter, ?_⟩
    have hEq := hHull.2 S.val
    rwa [hInter] at hEq

/-- Any skeleton order isomorphism `φ : SkeletonFace P k ≃o SkeletonFace Q l` preserves
`1`-dimensional exposed faces (edges). -/
theorem skeletonIso_finrank_one_iff {d e k l : ℕ}
    {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)}
    (hHullP : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}))
    (hHullQ : {y : Fin e → ℝ | IsExposed ℝ Q {y}}.Finite ∧
      ∀ E : PolytopeFace Q,
        E.val = convexHull ℝ (E.val ∩ {y : Fin e → ℝ | IsExposed ℝ Q {y}}))
    (φ : SkeletonFace P k ≃o SkeletonFace Q l) (S : SkeletonFace P k) :
    ((φ S).val.val.Nonempty ∧
      Module.finrank ℝ (affineSpan ℝ (φ S).val.val).direction = 1) ↔
    (S.val.val.Nonempty ∧
      Module.finrank ℝ (affineSpan ℝ S.val.val).direction = 1) := by
  have hFwd :
      ∀ {d' e' k' l' : ℕ} {P' : Set (Fin d' → ℝ)} {Q' : Set (Fin e' → ℝ)}
        (hHP : {x : Fin d' → ℝ | IsExposed ℝ P' {x}}.Finite ∧
          ∀ E : PolytopeFace P',
            E.val = convexHull ℝ (E.val ∩ {x : Fin d' → ℝ | IsExposed ℝ P' {x}}))
        (hHQ : {y : Fin e' → ℝ | IsExposed ℝ Q' {y}}.Finite ∧
          ∀ E : PolytopeFace Q',
            E.val = convexHull ℝ (E.val ∩ {y : Fin e' → ℝ | IsExposed ℝ Q' {y}}))
        (ψ : SkeletonFace P' k' ≃o SkeletonFace Q' l') (T : SkeletonFace P' k'),
        (T.val.val.Nonempty ∧
          Module.finrank ℝ (affineSpan ℝ T.val.val).direction = 1) →
        ((ψ T).val.val.Nonempty ∧
          Module.finrank ℝ (affineSpan ℝ (ψ T).val.val).direction = 1) := by
    intro d' e' k' l' P' Q' hHP hHQ ψ T hT
    obtain ⟨a, b, ha, hb, hab, hVertT⟩ :=
      (skeletonFace_finrank_one_iff_exists_vertex_pair hHP T).mp hT
    obtain ⟨a', ha', ha'Eq⟩ :=
      skeletonIso_maps_exposed_singleton hHP.2 hHQ.2 ψ a ha
    obtain ⟨b', hb', hb'Eq⟩ :=
      skeletonIso_maps_exposed_singleton hHP.2 hHQ.2 ψ b hb
    have hab' : a' ≠ b' := by
      intro hEq
      subst b'
      have hSubEq : vertexSkeletonFace Q' l' a' ha' = vertexSkeletonFace Q' l' a' hb' := rfl
      have hPsiEq : ψ (vertexSkeletonFace P' k' a ha) = ψ (vertexSkeletonFace P' k' b hb) :=
        ha'Eq.trans (hSubEq.trans hb'Eq.symm)
      have hVab : vertexSkeletonFace P' k' a ha = vertexSkeletonFace P' k' b hb :=
        ψ.injective hPsiEq
      have hSetEq : ({a} : Set (Fin d' → ℝ)) = {b} :=
        congrArg (fun U : SkeletonFace P' k' => U.val.val) hVab
      exact hab (Set.singleton_eq_singleton_iff.mp hSetEq)
    rw [skeletonFace_finrank_one_iff_exists_vertex_pair hHQ (ψ T)]
    refine ⟨a', b', ha', hb', hab', ?_⟩
    intro y hy
    obtain ⟨x, hx, hxEq⟩ :=
      skeletonIso_maps_exposed_singleton hHQ.2 hHP.2 ψ.symm y hy
    have hPsiX : ψ (vertexSkeletonFace P' k' x hx) = vertexSkeletonFace Q' l' y hy := by
      rw [← hxEq, OrderIso.apply_symm_apply]
    rw [← hPsiX, ψ.map_rel_iff, hVertT x hx]
    have hxa : x = a ↔ y = a' := by
      constructor
      · rintro rfl
        have hEq : vertexSkeletonFace Q' l' y hy = vertexSkeletonFace Q' l' a' ha' :=
          hPsiX.symm.trans ha'Eq
        have hSetEq : ({y} : Set (Fin e' → ℝ)) = {a'} :=
          congrArg (fun U : SkeletonFace Q' l' => U.val.val) hEq
        exact Set.singleton_eq_singleton_iff.mp hSetEq
      · rintro rfl
        have hEq : ψ (vertexSkeletonFace P' k' x hx) = ψ (vertexSkeletonFace P' k' a ha) :=
          hPsiX.trans ha'Eq.symm
        have hVxa : vertexSkeletonFace P' k' x hx = vertexSkeletonFace P' k' a ha :=
          ψ.injective hEq
        have hSetEq : ({x} : Set (Fin d' → ℝ)) = {a} :=
          congrArg (fun U : SkeletonFace P' k' => U.val.val) hVxa
        exact Set.singleton_eq_singleton_iff.mp hSetEq
    have hxb : x = b ↔ y = b' := by
      constructor
      · rintro rfl
        have hEq : vertexSkeletonFace Q' l' y hy = vertexSkeletonFace Q' l' b' hb' :=
          hPsiX.symm.trans hb'Eq
        have hSetEq : ({y} : Set (Fin e' → ℝ)) = {b'} :=
          congrArg (fun U : SkeletonFace Q' l' => U.val.val) hEq
        exact Set.singleton_eq_singleton_iff.mp hSetEq
      · rintro rfl
        have hEq : ψ (vertexSkeletonFace P' k' x hx) = ψ (vertexSkeletonFace P' k' b hb) :=
          hPsiX.trans hb'Eq.symm
        have hVxb : vertexSkeletonFace P' k' x hx = vertexSkeletonFace P' k' b hb :=
          ψ.injective hEq
        have hSetEq : ({x} : Set (Fin d' → ℝ)) = {b} :=
          congrArg (fun U : SkeletonFace P' k' => U.val.val) hVxb
        exact Set.singleton_eq_singleton_iff.mp hSetEq
    rw [hxa, hxb]
  constructor
  · intro hPhiS
    have hSymm := hFwd hHullQ hHullP φ.symm (φ S) hPhiS
    rw [OrderIso.symm_apply_apply] at hSymm
    exact hSymm
  · exact hFwd hHullP hHullQ φ S

end Grunbaum2003

namespace Grunbaum2003

/-- Explicit vertex-figure hull identity for a hyperplane separating one generator from all others. -/
theorem convexHull_insert_inter_level_eq (d : ℕ) (v : Fin d → ℝ)
    (W : Set (Fin d → ℝ)) (hW : W.Nonempty)
    (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α) :
    convexHull ℝ (insert v W) ∩ l ⁻¹' {α} =
      convexHull ℝ ((fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))) '' W) := by
  let q : (Fin d → ℝ) → (Fin d → ℝ) :=
    fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))
  have hD : 0 < l v - α := sub_pos.mpr hα
  have hq (w : Fin d → ℝ) (hw : w ∈ W) :
      q w ∈ convexHull ℝ (insert v W) ∧ l (q w) = α := by
    have hDen : 0 < l v - l w := sub_pos.mpr ((hBelow w hw).trans hα)
    have ht0 : 0 ≤ (l v - α) / (l v - l w) := (div_pos hD hDen).le
    have ht1 : (l v - α) / (l v - l w) ≤ 1 :=
      (div_le_one hDen).mpr (by linarith [hBelow w hw])
    constructor
    · exact (convex_convexHull ℝ _).lineMap_mem
        (subset_convexHull ℝ _ (Set.mem_insert v W))
        (subset_convexHull ℝ _ (Set.mem_insert_of_mem v hw)) ⟨ht0, ht1⟩
    · have hMul : ((l v - α) / (l v - l w)) * (l v - l w) = l v - α :=
        div_mul_cancel₀ _ hDen.ne'
      dsimp [q]
      rw [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul]
      nlinarith [hMul]
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxLevel⟩
    change l x = α at hxLevel
    obtain ⟨ι, hι, a, z, ha, haSum, hz, haz⟩ := mem_convexHull_iff_exists_fintype.mp hx
    letI := hι
    obtain ⟨w₀, hw₀⟩ := hW
    let b : ι → ℝ := fun i => a i * (l v - l (z i)) / (l v - α)
    let u : ι → (Fin d → ℝ) := fun i => if z i = v then q w₀ else q (z i)
    have hzLe (i : ι) : l (z i) ≤ l v := by
      rcases hz i with h | h
      · simpa only [h] using le_refl (l v)
      · exact ((hBelow (z i) h).trans hα).le
    have hb (i : ι) : 0 ≤ b i := div_nonneg (mul_nonneg (ha i) (sub_nonneg.mpr (hzLe i))) hD.le
    have hlSum : ∑ i, a i * l (z i) = α := by
      have h := congrArg l haz
      simpa only [map_sum, map_smul, smul_eq_mul, hxLevel] using h
    have hbSum : ∑ i, b i = 1 := by
      calc
        ∑ i, b i = (∑ i, a i * (l v - l (z i))) / (l v - α) := by
          simp only [b, div_eq_mul_inv, Finset.sum_mul]
        _ = ((∑ i, a i) * l v - ∑ i, a i * l (z i)) / (l v - α) := by
          simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
        _ = 1 := by rw [haSum, hlSum, one_mul, div_self hD.ne']
    have hu (i : ι) : u i ∈ q '' W := by
      dsimp [u]
      split_ifs with hi
      · exact ⟨w₀, hw₀, rfl⟩
      · exact ⟨z i, (Set.mem_insert_iff.mp (hz i)).resolve_left hi, rfl⟩
    have hTerm (i : ι) : b i • u i = b i • v + a i • (z i - v) := by
      by_cases hi : z i = v
      · simp [u, b, hi]
      · have hzi : z i ∈ W := (Set.mem_insert_iff.mp (hz i)).resolve_left hi
        have hDen : l v - l (z i) ≠ 0 := (sub_pos.mpr ((hBelow (z i) hzi).trans hα)).ne'
        have hCoef : b i * ((l v - α) / (l v - l (z i))) = a i := by
          dsimp [b]
          field_simp [hD.ne', hDen] <;> ring
        dsimp [u]
        rw [if_neg hi]
        dsimp [q]
        rw [AffineMap.lineMap_apply_module', smul_add, smul_smul, hCoef, add_comm]
    apply mem_convexHull_of_exists_fintype b u hb hbSum hu
    calc
      ∑ i, b i • u i = ∑ i, (b i • v + a i • (z i - v)) := Finset.sum_congr rfl (fun i _ => hTerm i)
      _ = (∑ i, b i) • v + (∑ i, a i • z i - (∑ i, a i) • v) := by
        simp only [Finset.sum_add_distrib, smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]
      _ = x := by rw [hbSum, haSum, haz, one_smul]; abel
  · apply convexHull_min
    · rintro _ ⟨w, hw, rfl⟩
      exact hq w hw
    · apply (convex_convexHull ℝ _).inter
      intro x hx y hy a b _ _ hab
      change l x = α at hx
      change l y = α at hy
      change l (a • x + b • y) = α
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hx, hy]
      rw [← add_mul, hab, one_mul]

/-- Lift an exposed vertex-figure face to a face of the original hull containing the apex. -/
theorem exposed_vertex_figure_face_lift (d : ℕ) (v : Fin d → ℝ)
    (W : Set (Fin d → ℝ)) (hW : W.Nonempty)
    (l m : StrongDual ℝ (Fin d → ℝ)) (α β : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α)
    (hMax : ∀ x ∈ convexHull ℝ (insert v W) ∩ l ⁻¹' {α}, m x ≤ β) :
    let P := convexHull ℝ (insert v W)
    let n := m + ((β - m v) / (l v - α)) • l
    let G := {x ∈ P | n x = n v}
    (∀ x ∈ P, n x ≤ n v) ∧ IsExposed ℝ P G ∧ v ∈ G ∧
      {x ∈ P ∩ l ⁻¹' {α} | m x = β} = G ∩ l ⁻¹' {α} := by
  let P := convexHull ℝ (insert v W)
  let c : ℝ := (β - m v) / (l v - α)
  let n : StrongDual ℝ (Fin d → ℝ) := m + c • l
  let G := {x ∈ P | n x = n v}
  change (∀ x ∈ P, n x ≤ n v) ∧ IsExposed ℝ P G ∧ v ∈ G ∧
    {x ∈ P ∩ l ⁻¹' {α} | m x = β} = G ∩ l ⁻¹' {α}
  have hD : 0 < l v - α := sub_pos.mpr hα
  have hcMul : c * (l v - α) = β - m v := div_mul_cancel₀ _ hD.ne'
  have hvP : v ∈ P := subset_convexHull ℝ _ (Set.mem_insert _ _)
  have hGen (w : Fin d → ℝ) (hw : w ∈ insert v W) : n w ≤ n v := by
    rcases hw with rfl | hw
    · exact le_rfl
    · have hDen : 0 < l v - l w := sub_pos.mpr ((hBelow w hw).trans hα)
      let q := AffineMap.lineMap v w ((l v - α) / (l v - l w))
      have hq : q ∈ P ∩ l ⁻¹' {α} := by
        have hmem : q ∈ convexHull ℝ
            ((fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))) '' W) :=
          subset_convexHull ℝ _ ⟨w, hw, rfl⟩
        rwa [← convexHull_insert_inter_level_eq d v W hW l α hα hBelow] at hmem
      have hM := hMax q hq
      have hmq : m q = ((l v - α) * (m w - m v)) / (l v - l w) + m v := by
        dsimp [q]
        rw [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul]
        ring
      rw [hmq] at hM
      have hFrac : ((l v - α) * (m w - m v)) / (l v - l w) ≤ β - m v := by linarith
      have hWeighted : (l v - α) * (m w - m v) ≤ (l v - α) * (c * (l v - l w)) := by
        calc
          (l v - α) * (m w - m v) ≤ (β - m v) * (l v - l w) := (div_le_iff₀ hDen).mp hFrac
          _ = (c * (l v - α)) * (l v - l w) := by rw [hcMul]
          _ = (l v - α) * (c * (l v - l w)) := by ring
      have hBound : m w - m v ≤ c * (l v - l w) := (mul_le_mul_iff_right₀ hD).mp hWeighted
      change m w + c * l w ≤ m v + c * l v
      nlinarith [hBound]
  have hN : ∀ x ∈ P, n x ≤ n v := by
    apply convexHull_min hGen
    intro x hx y hy a b ha hb hab
    change n (a • x + b • y) ≤ n v
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    calc
      a * n x + b * n y ≤ a * n v + b * n v :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
      _ = n v := by rw [← add_mul, hab, one_mul]
  have hG : IsExposed ℝ P G := by
    intro _
    refine ⟨n, ?_⟩
    ext x
    constructor
    · rintro ⟨hxP, hxEq⟩
      refine ⟨hxP, fun y hy => ?_⟩
      calc n y ≤ n v := hN y hy
           _ = n x := hxEq.symm
    · rintro ⟨hxP, hxMax⟩
      exact ⟨hxP, le_antisymm (hN x hxP) (hxMax v hvP)⟩
  have hEq (x : Fin d → ℝ) (hx : l x = α) : n x = n v ↔ m x = β := by
    change m x + c * l x = m v + c * l v ↔ m x = β
    rw [hx]
    constructor <;> intro h <;> nlinarith [hcMul]
  refine ⟨hN, hG, ⟨hvP, rfl⟩, ?_⟩
  ext x
  constructor
  · rintro ⟨⟨hxP, hxLevel⟩, hxM⟩
    exact ⟨⟨hxP, (hEq x hxLevel).mpr hxM⟩, hxLevel⟩
  · rintro ⟨⟨hxP, hxN⟩, hxLevel⟩
    exact ⟨⟨hxP, hxLevel⟩, (hEq x hxLevel).mp hxN⟩

/-- Restriction of a supporting face to a subset, including the empty intersection. -/
theorem isExposed_inter_restrict {d : ℕ} {P G B : Set (Fin d → ℝ)}
    (hG : IsExposed ℝ P G) (hBP : B ⊆ P) : IsExposed ℝ B (G ∩ B) := by
  intro hNonempty
  obtain ⟨z, hzG, hzB⟩ := hNonempty
  obtain ⟨m, hm⟩ := hG ⟨z, hzG⟩
  have hzMax : ∀ y ∈ P, m y ≤ m z := by
    have hz := hzG
    rw [hm] at hz
    exact hz.2
  refine ⟨m, ?_⟩
  ext x
  constructor
  · rintro ⟨hxG, hxB⟩
    rw [hm] at hxG
    exact ⟨hxB, fun y hy => hxG.2 y (hBP hy)⟩
  · rintro ⟨hxB, hxMax⟩
    refine ⟨?_, hxB⟩
    rw [hm]
    refine ⟨hBP hxB, fun y hy => ?_⟩
    exact (hzMax y hy).trans (hxMax z hzB)

/-- For a face containing the apex, membership of an internal crossing point is equivalent to
membership of the other endpoint. -/
theorem lineMap_mem_face_iff {d : ℕ} {P G : Set (Fin d → ℝ)}
    (hP : Convex ℝ P) (hG : IsExposed ℝ P G)
    {v w : Fin d → ℝ} (hvG : v ∈ G) (hwP : w ∈ P)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    AffineMap.lineMap v w t ∈ G ↔ w ∈ G := by
  constructor
  · intro hx
    exact hG.isExtreme.right_mem_of_mem_openSegment (hG.subset hvG) hwP hx
      (lineMap_mem_openSegment ℝ v w ht)
  · intro hwG
    exact (hG.convex hP).lineMap_mem hvG hwG ⟨ht.1.le, ht.2.le⟩

/-- Cutting-plane sections reflect inclusion among polytope faces containing the chosen vertex. -/
theorem vertex_figure_section_order_reflects (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (hHull : ∀ E : PolytopeFace P,
      E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}))
    (v : Fin d → ℝ) (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
    (hα : α < l v)
    (hBelow : ∀ w : Fin d → ℝ, IsExposed ℝ P {w} → w ≠ v → l w < α)
    (G₁ G₂ : Set (Fin d → ℝ)) (hG₁ : IsExposed ℝ P G₁) (hG₂ : IsExposed ℝ P G₂)
    (hv₁ : v ∈ G₁) (hv₂ : v ∈ G₂)
    (hSections : G₁ ∩ l ⁻¹' {α} ⊆ G₂ ∩ l ⁻¹' {α}) : G₁ ⊆ G₂ := by
  have hPconv : Convex ℝ P := by
    obtain ⟨V, _, _, hPV⟩ := hP.1
    rw [hPV]
    exact convex_convexHull ℝ V
  calc
    G₁ = convexHull ℝ (G₁ ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}) := hHull ⟨G₁, hG₁⟩
    _ ⊆ G₂ := by
      apply convexHull_min ?_ (hG₂.convex hPconv)
      rintro w ⟨hw₁, hwVertex⟩
      by_cases hwv : w = v
      · simpa only [hwv] using hv₂
      · have hLow : l w < α := hBelow w hwVertex hwv
        have hDen : 0 < l v - l w := sub_pos.mpr (hLow.trans hα)
        let t : ℝ := (l v - α) / (l v - l w)
        have ht₀ : 0 < t := div_pos (sub_pos.mpr hα) hDen
        have ht₁ : t < 1 := (div_lt_one hDen).mpr (by linarith)
        have hwP : w ∈ P := hG₁.subset hw₁
        have hq₁ : AffineMap.lineMap v w t ∈ G₁ :=
          (lineMap_mem_face_iff hPconv hG₁ hv₁ hwP ⟨ht₀, ht₁⟩).mpr hw₁
        have htMul : t * (l v - l w) = l v - α := div_mul_cancel₀ _ hDen.ne'
        have hqLevel : l (AffineMap.lineMap v w t) = α := by
          rw [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul]
          nlinarith [htMul]
        have hq₂ : AffineMap.lineMap v w t ∈ G₂ := (hSections ⟨hq₁, hqLevel⟩).1
        exact (lineMap_mem_face_iff hPconv hG₂ hv₂ hwP ⟨ht₀, ht₁⟩).mp hq₂

/-- The vertex-figure face lattice is order-isomorphic to the interval of faces containing the apex. -/
theorem vertex_figure_face_orderIso (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (hHull : ∀ E : PolytopeFace P,
      E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}))
    (v : Fin d → ℝ) (hv : IsExposed ℝ P {v})
    (W : Set (Fin d → ℝ)) (hW : W.Nonempty)
    (hPgen : P = convexHull ℝ (insert v W))
    (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α) :
    ∃ Φ : {G : PolytopeFace P // v ∈ G.val} ≃o PolytopeFace (P ∩ l ⁻¹' {α}),
      ∀ G, (Φ G).val = G.val.val ∩ (P ∩ l ⁻¹' {α}) := by
  let Q := P ∩ l ⁻¹' {α}
  let A := {G : PolytopeFace P // v ∈ G.val}
  let f : A → PolytopeFace Q := fun G =>
    ⟨G.val.val ∩ Q, isExposed_inter_restrict G.val.property Set.inter_subset_left⟩
  have hBelowVertices (w : Fin d → ℝ) (hw : IsExposed ℝ P {w}) (hwv : w ≠ v) : l w < α := by
    have hwExt : w ∈ P.extremePoints ℝ :=
      exposedPoints_subset_extremePoints (mem_exposedPoints_iff_exposed_singleton.mpr hw)
    rw [hPgen] at hwExt
    have hwGen := extremePoints_convexHull_subset hwExt
    exact hBelow w ((Set.mem_insert_iff.mp hwGen).resolve_left hwv)
  have hMap (G₁ G₂ : A) : f G₁ ≤ f G₂ ↔ G₁ ≤ G₂ := by
    change G₁.val.val ∩ Q ⊆ G₂.val.val ∩ Q ↔ G₁.val.val ⊆ G₂.val.val
    constructor
    · intro h
      apply vertex_figure_section_order_reflects d P hP hHull v l α hα hBelowVertices
        G₁.val.val G₂.val.val G₁.val.property G₂.val.property G₁.property G₂.property
      rintro x ⟨hxG, hxLevel⟩
      have hxQ : x ∈ Q := ⟨G₁.val.property.subset hxG, hxLevel⟩
      have hx := h ⟨hxG, hxQ⟩
      exact ⟨hx.1, hx.2.2⟩
    · intro h x hx
      exact ⟨h hx.1, hx.2⟩
  let emb : A ↪o PolytopeFace Q := OrderEmbedding.ofMapLEIff f hMap
  have hSurj : Function.Surjective f := by
    intro R
    by_cases hEmpty : R.val = ∅
    · let G : A := ⟨⟨{v}, hv⟩, Set.mem_singleton v⟩
      refine ⟨G, ?_⟩
      apply Subtype.ext
      change {v} ∩ Q = R.val
      rw [hEmpty]
      apply Set.Subset.antisymm ?_ (Set.empty_subset _)
      rintro x ⟨hxv, hxQ⟩
      have hx : x = v := hxv
      subst x
      exact (hα.ne hxQ.2.symm).elim
    · have hRne : R.val.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
      obtain ⟨z, hz⟩ := hRne
      obtain ⟨m, hm⟩ := R.property ⟨z, hz⟩
      have hzQ : z ∈ Q := R.property.subset hz
      have hzMax : ∀ y ∈ Q, m y ≤ m z := by
        have hz' := hz
        rw [hm] at hz'
        exact hz'.2
      let β := m z
      have hRmax : R.val = {x ∈ Q | m x = β} := by
        ext x
        constructor
        · intro hx
          have hx' := hx
          rw [hm] at hx'
          exact ⟨hx'.1, le_antisymm (hzMax x hx'.1) (hx'.2 z hzQ)⟩
        · rintro ⟨hxQ, hxEq⟩
          rw [hm]
          refine ⟨hxQ, fun y hy => ?_⟩
          calc m y ≤ m z := hzMax y hy
               _ = m x := hxEq.symm
      have hMax : ∀ x ∈ convexHull ℝ (insert v W) ∩ l ⁻¹' {α}, m x ≤ β := by
        rw [← hPgen]
        exact hzMax
      obtain ⟨_, hExpose, hVertex, hSlice⟩ :=
        exposed_vertex_figure_face_lift d v W hW l m α β hα hBelow hMax
      let n := m + ((β - m v) / (l v - α)) • l
      let G : Set (Fin d → ℝ) := {x ∈ P | n x = n v}
      have hG : IsExposed ℝ P G := by simpa only [← hPgen] using hExpose
      have hvG : v ∈ G := by simpa only [← hPgen] using hVertex
      have hSlice' : {x ∈ Q | m x = β} = G ∩ l ⁻¹' {α} := by
        simpa only [← hPgen] using hSlice
      refine ⟨⟨⟨G, hG⟩, hvG⟩, ?_⟩
      apply Subtype.ext
      change G ∩ Q = R.val
      rw [hRmax, hSlice']
      ext x
      constructor
      · rintro ⟨hxG, hxQ⟩
        exact ⟨hxG, hxQ.2⟩
      · rintro ⟨hxG, hxLevel⟩
        exact ⟨hxG, ⟨hG.subset hxG, hxLevel⟩⟩
  let Φ : A ≃o PolytopeFace Q := OrderIso.ofSurjective emb hSurj
  refine ⟨Φ, ?_⟩
  intro G
  rfl

/-- The explicit vertex-figure generators span the complete cutting hyperplane. -/
theorem affineSpan_crossing_image_eq_level (d : ℕ) (v : Fin d → ℝ)
    (W : Set (Fin d → ℝ)) (hW : W.Nonempty)
    (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α)
    (hSpan : affineSpan ℝ (insert v W) = ⊤) :
    (affineSpan ℝ ((fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))) '' W) :
      Set (Fin d → ℝ)) = l ⁻¹' {α} := by
  let q : (Fin d → ℝ) → (Fin d → ℝ) :=
    fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))
  let A : AffineSubspace ℝ (Fin d → ℝ) := affineSpan ℝ (q '' W)
  let H : AffineSubspace ℝ (Fin d → ℝ) :=
    (affineSpan ℝ ({α} : Set ℝ)).comap l.toLinearMap.toAffineMap
  have hH (x : Fin d → ℝ) : x ∈ H ↔ l x = α := by
    change l x ∈ affineSpan ℝ ({α} : Set ℝ) ↔ _
    exact AffineSubspace.mem_affineSpan_singleton ℝ ℝ
  have hqLevel (w : Fin d → ℝ) (hw : w ∈ W) : l (q w) = α := by
    have hq : q w ∈ convexHull ℝ (q '' W) := subset_convexHull ℝ _ ⟨w, hw, rfl⟩
    rw [← convexHull_insert_inter_level_eq d v W hW l α hα hBelow] at hq
    exact hq.2
  have hAH : A ≤ H := by
    apply affineSpan_le_of_subset_coe
    rintro x ⟨w, hw, rfl⟩
    exact (hH _).mpr (hqLevel w hw)
  have hALevel (x : Fin d → ℝ) (hx : x ∈ A) : l x = α := (hH x).mp (hAH hx)
  obtain ⟨w₀, hw₀⟩ := hW
  have hq₀ : q w₀ ∈ A := subset_affineSpan ℝ _ ⟨w₀, hw₀, rfl⟩
  let S : AffineSubspace ℝ (Fin d → ℝ) := affineSpan ℝ (insert v (A : Set (Fin d → ℝ)))
  have hvS : v ∈ S := subset_affineSpan ℝ _ (Set.mem_insert _ _)
  have hCover : insert v W ⊆ S := by
    rintro w (rfl | hw)
    · exact hvS
    · have hqwS : q w ∈ S := subset_affineSpan ℝ _
        (Set.mem_insert_of_mem v (subset_affineSpan ℝ _ ⟨w, hw, rfl⟩))
      let t : ℝ := (l v - α) / (l v - l w)
      have ht : t ≠ 0 := div_ne_zero (sub_pos.mpr hα).ne'
        (sub_pos.mpr ((hBelow w hw).trans hα)).ne'
      have hLine : AffineMap.lineMap v (q w) t⁻¹ = w := by
        change AffineMap.lineMap v (AffineMap.lineMap v w t) t⁻¹ = w
        rw [AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ ht, AffineMap.lineMap_apply_one]
      have hm := AffineMap.lineMap_mem t⁻¹ hvS hqwS
      rwa [hLine] at hm
  have hSTop : S = ⊤ := by
    apply eq_top_iff.mpr
    have h := affineSpan_le_of_subset_coe hCover
    rwa [hSpan] at h
  ext x
  change x ∈ A ↔ l x = α
  constructor
  · exact hALevel x
  · intro hx
    have hxS : x ∈ S := by rw [hSTop]; trivial
    obtain ⟨r, p₀, hp₀, hxp₀⟩ := (AffineSubspace.mem_affineSpan_insert_iff hq₀ v x).mp hxS
    have hEq := congrArg l hxp₀
    simp only [vsub_eq_sub, vadd_eq_add, map_add, map_smul, map_sub, smul_eq_mul] at hEq
    rw [hx, hALevel p₀ hp₀, hALevel (q w₀) hq₀] at hEq
    have hMul : r * (l v - α) = 0 := by linarith
    have hr : r = 0 := (mul_eq_zero.mp hMul).resolve_right (sub_pos.mpr hα).ne'
    simp only [hr, zero_smul, zero_vadd] at hxp₀
    rwa [hxp₀]

/-- An actual finite vertex figure admits full-dimensional coordinates in dimension `d - 1`. -/
theorem exists_vertex_figure_coordinates (d : ℕ) (v : Fin d → ℝ)
    (W : Set (Fin d → ℝ)) (hWfin : W.Finite) (hW : W.Nonempty)
    (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α)
    (hSpan : affineSpan ℝ (insert v W) = ⊤) :
    let Q := (fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))) '' W
    letI : Nonempty (affineSpan ℝ Q) := by
      obtain ⟨w, hw⟩ := hW
      exact ⟨⟨_, subset_affineSpan ℝ Q ⟨w, hw, rfl⟩⟩⟩
    ∃ e : (affineSpan ℝ Q) ≃ᵃ[ℝ] (Fin (d - 1) → ℝ),
      IsDPolytope (convexHull ℝ (e '' (((↑) : affineSpan ℝ Q → (Fin d → ℝ)) ⁻¹' Q))) := by
  let q : (Fin d → ℝ) → (Fin d → ℝ) :=
    fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))
  let A : AffineSubspace ℝ (Fin d → ℝ) := affineSpan ℝ (q '' W)
  obtain ⟨w₀, hw₀⟩ := hW
  have hq₀ : q w₀ ∈ A := subset_affineSpan ℝ _ ⟨w₀, hw₀, rfl⟩
  haveI : Nonempty A := ⟨⟨q w₀, hq₀⟩⟩
  change ∃ e : A ≃ᵃ[ℝ] (Fin (d - 1) → ℝ),
    IsDPolytope (convexHull ℝ (e '' (((↑) : A → (Fin d → ℝ)) ⁻¹' (q '' W))))
  have hASet : (A : Set (Fin d → ℝ)) = l ⁻¹' {α} :=
    affineSpan_crossing_image_eq_level d v W ⟨w₀, hw₀⟩ l α hα hBelow hSpan
  have hALevel (x : Fin d → ℝ) (hx : x ∈ A) : l x = α := by
    have hx' : x ∈ (A : Set (Fin d → ℝ)) := hx
    rw [hASet] at hx'
    exact hx'
  have hDir : A.direction = LinearMap.ker l.toLinearMap := by
    ext z
    change z ∈ A.direction ↔ l z = 0
    rw [← AffineSubspace.vadd_mem_iff_mem_direction z hq₀]
    change z + q w₀ ∈ (A : Set (Fin d → ℝ)) ↔ l z = 0
    rw [hASet]
    change l (z + q w₀) = α ↔ l z = 0
    rw [map_add, hALevel (q w₀) hq₀]
    constructor <;> intro h <;> linarith
  have hlne : l.toLinearMap ≠ 0 := by
    intro hz
    have hzv := LinearMap.congr_fun hz v
    have hzw := LinearMap.congr_fun hz w₀
    change l v = 0 at hzv
    change l w₀ = 0 at hzw
    linarith [hBelow w₀ hw₀]
  have hRank : Module.finrank ℝ (LinearMap.ker l.toLinearMap) + 1 = d := by
    simpa using Module.Dual.finrank_ker_add_one_of_ne_zero hlne
  have hDim : Module.finrank ℝ A.direction = d - 1 := by
    rw [hDir]
    omega
  let eL : A.direction ≃ₗ[ℝ] (Fin (d - 1) → ℝ) :=
    LinearEquiv.ofFinrankEq A.direction (Fin (d - 1) → ℝ) (by simpa using hDim)
  let e : A ≃ᵃ[ℝ] (Fin (d - 1) → ℝ) :=
    (AffineEquiv.vaddConst ℝ (⟨q w₀, hq₀⟩ : A)).symm.trans eL.toAffineEquiv
  let V : Set A := ((↑) : A → (Fin d → ℝ)) ⁻¹' (q '' W)
  have hVfin : V.Finite := Set.Finite.preimage Subtype.val_injective.injOn (hWfin.image q)
  have hVne : V.Nonempty := ⟨⟨q w₀, hq₀⟩, ⟨w₀, hw₀, rfl⟩⟩
  haveI : Nonempty (q '' W) := ⟨⟨q w₀, ⟨w₀, hw₀, rfl⟩⟩⟩
  have hVSpan : affineSpan ℝ V = ⊤ := affineSpan_coe_preimage_eq_top (q '' W)
  refine ⟨e, ⟨⟨e '' V, hVfin.image e, hVne.image e, rfl⟩, ?_⟩⟩
  rw [affineSpan_convexHull]
  exact e.span_eq_top_iff.mp hVSpan

/-- In finite-dimensional ambient space, an exposing functional can be extended
along any injective affine map. -/
theorem isExposed_image_affineMap_of_injective {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f)
    {P S : Set E} (hS : IsExposed ℝ P S) : IsExposed ℝ (f '' P) (f '' S) := by
  intro hne
  have hSne : S.Nonempty := by
    obtain ⟨y, x, hx, rfl⟩ := hne
    exact ⟨x, hx⟩
  obtain ⟨l, hl⟩ := hS hSne
  have hlin : Function.Injective f.linear := f.linear_injective_iff.mpr hf
  obtain ⟨u, hu⟩ := f.linear.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hlin)
  have hu_apply : ∀ x : E, u (f.linear x) = x := by
    intro x
    exact congrArg (fun L : E →ₗ[ℝ] E => L x) hu
  let m : F →L[ℝ] ℝ := l.comp u.toContinuousLinearMap
  have hm : ∀ x : E, m (f x) = l x + l (u (f 0)) := by
    intro x
    have hfx : f x = f.linear x + f 0 := by
      simpa only [vadd_eq_add, add_zero] using f.map_vadd (0 : E) x
    change l (u (f x)) = _
    rw [hfx, map_add, hu_apply, map_add]
  refine ⟨m, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ P ∧ ∀ z ∈ P, l z ≤ l x := by
      simpa only [hl, Set.mem_ofPred_eq] using hx
    refine ⟨⟨x, hx'.1, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [hm, hm]
    exact add_le_add (hx'.2 z hz) le_rfl
  · rintro ⟨⟨x, hx, rfl⟩, hmax⟩
    refine ⟨x, ?_, rfl⟩
    rw [hl]
    refine ⟨hx, ?_⟩
    intro z hz
    have ht := hmax (f z) ⟨z, hz, rfl⟩
    rw [hm, hm] at ht
    exact (add_le_add_iff_right _).mp ht

/-- Pulling an exposed face back along an injective finite-dimensional affine
map preserves the exposed-face predicate. -/
theorem isExposed_preimage_affineMap_of_injective {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f)
    {P : Set E} {T : Set F} (hT : IsExposed ℝ (f '' P) T) :
    IsExposed ℝ P (f ⁻¹' T) := by
  intro hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨l, hl⟩ := hT ⟨f x, hx⟩
  let m : E →L[ℝ] ℝ := l.comp f.linear.toContinuousLinearMap
  have hm : ∀ x : E, m x = l (f x) - l (f 0) := by
    intro x
    have hv := f.linearMap_vsub x (0 : E)
    change f.linear (x - 0) = f x - f 0 at hv
    have hv' : f.linear x = f x - f 0 := by simpa only [sub_zero] using hv
    change l (f.linear x) = _
    rw [hv', map_sub]
  refine ⟨m, ?_⟩
  ext y
  constructor
  · intro hy
    change f y ∈ T at hy
    have hy' : f y ∈ f '' P ∧ ∀ z ∈ f '' P, l z ≤ l (f y) := by
      simpa only [hl, Set.mem_ofPred_eq] using hy
    refine ⟨hf.mem_set_image.mp hy'.1, ?_⟩
    intro z hz
    rw [hm, hm]
    exact sub_le_sub_right (hy'.2 (f z) ⟨z, hz, rfl⟩) _
  · rintro ⟨hy, hmax⟩
    change f y ∈ T
    rw [hl]
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have ht := hmax z hz
    rw [hm, hm] at ht
    exact (sub_le_sub_iff_right _).mp ht

/-- An injective affine map preserves the affine direction finrank of any subset. -/
theorem finrank_direction_affineSpan_image_injective {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) (S : Set E) :
    Module.finrank ℝ (affineSpan ℝ (f '' S)).direction =
      Module.finrank ℝ (affineSpan ℝ S).direction := by
  have hlin : Function.Injective f.linear := f.linear_injective_iff.mpr hf
  rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
  exact ((affineSpan ℝ S).direction.equivMapOfInjective f.linear hlin).symm.finrank_eq

/-- An injective affine map induces an order isomorphism between the face lattice of `Q₀`
and the face lattice of its image `Q = f '' Q₀`. -/
theorem polytopeFace_image_affineMap_orderIso {d e : ℕ}
    (f : (Fin e → ℝ) →ᵃ[ℝ] (Fin d → ℝ)) (hf : Function.Injective f)
    (Q₀ : Set (Fin e → ℝ)) (Q : Set (Fin d → ℝ)) (hQ : f '' Q₀ = Q) :
    ∃ Θ : PolytopeFace Q₀ ≃o PolytopeFace Q,
      ∀ R : PolytopeFace Q₀, (Θ R).val = f '' R.val := by
  let toFace : PolytopeFace Q₀ → PolytopeFace Q := fun R =>
    ⟨f '' R.val, hQ ▸ isExposed_image_affineMap_of_injective f hf R.property⟩
  have hMap (R₁ R₂ : PolytopeFace Q₀) : toFace R₁ ≤ toFace R₂ ↔ R₁ ≤ R₂ := by
    change f '' R₁.val ⊆ f '' R₂.val ↔ R₁.val ⊆ R₂.val
    exact Set.image_subset_image_iff hf
  let emb : PolytopeFace Q₀ ↪o PolytopeFace Q := OrderEmbedding.ofMapLEIff toFace hMap
  have hSurj : Function.Surjective toFace := by
    intro T
    have hTexp : IsExposed ℝ Q₀ (f ⁻¹' T.val) :=
      isExposed_preimage_affineMap_of_injective f hf (hQ.symm ▸ T.property)
    refine ⟨⟨f ⁻¹' T.val, hTexp⟩, ?_⟩
    apply Subtype.ext
    change f '' (f ⁻¹' T.val) = T.val
    apply Set.image_preimage_eq_iff.mpr
    calc T.val ⊆ Q := T.property.subset
      _ = f '' Q₀ := hQ.symm
      _ ⊆ Set.range f := Set.image_subset_range f Q₀
  refine ⟨OrderIso.ofSurjective emb hSurj, fun _ => rfl⟩

/-- For any positive-dimensional `d`-polytope `P` and ANY prescribed exposed vertex `v` of `P`,
the cutting hyperplane at `v` yields a full-dimensional `(d - 1)`-polytope `Q₀ ⊆ ℝ^(d - 1)`,
an injective affine map `f` with `f '' Q₀ = P ∩ l ⁻¹' {α}`, and an order isomorphism
`Ψ : {G : PolytopeFace P // v ∈ G.val} ≃o PolytopeFace Q₀` that shifts affine direction finrank
down by `1` on all faces strictly above `{v}` and restricts to an order isomorphism
`{S : SkeletonFace P (k + 1) // vertexSkeletonFace P (k + 1) v hv ≤ S} ≃o SkeletonFace Q₀ k`
for every `k : ℕ`. -/
theorem prescribed_vertex_figure_polytope_and_skeleton_iso
    (d : ℕ) (hd : 0 < d) (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (hHull : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}))
    (hCut :
      (∀ v : Fin d → ℝ, IsExposed ℝ P {v} →
        ∃ (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ),
          α < l v ∧ (∀ x ∈ P, l x ≤ l v) ∧
          ∀ w : Fin d → ℝ, IsExposed ℝ P {w} → w ≠ v →
            l w < α ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ l (AffineMap.lineMap v w t) = α) ∧
      (∀ (v : Fin d → ℝ) (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ),
        α < l v →
        (∀ w : Fin d → ℝ, IsExposed ℝ P {w} → w ≠ v → l w < α) →
        ∀ (G : Set (Fin d → ℝ)), IsExposed ℝ P G → v ∈ G →
          affineSpan ℝ (insert v (G ∩ l ⁻¹' {α})) = affineSpan ℝ G ∧
          ((G ∩ l ⁻¹' {α}).Nonempty ↔ G ≠ {v}) ∧
          (G ≠ {v} →
            (G ∩ l ⁻¹' {α}).Nonempty ∧
              Module.finrank ℝ (affineSpan ℝ G).direction =
                Module.finrank ℝ (affineSpan ℝ (G ∩ l ⁻¹' {α})).direction + 1)))
    (v : Fin d → ℝ) (hv : IsExposed ℝ P {v}) :
    ∃ (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
      (Q₀ : Set (Fin (d - 1) → ℝ))
      (f : (Fin (d - 1) → ℝ) →ᵃ[ℝ] (Fin d → ℝ))
      (Ψ : {G : PolytopeFace P // v ∈ G.val} ≃o PolytopeFace Q₀),
      α < l v ∧
      (∀ w : Fin d → ℝ, IsExposed ℝ P {w} → w ≠ v → l w < α) ∧
      IsDPolytope Q₀ ∧
      Function.Injective f ∧
      f '' Q₀ = P ∩ l ⁻¹' {α} ∧
      (∀ G : {G : PolytopeFace P // v ∈ G.val},
        f '' (Ψ G).val = G.val.val ∩ (P ∩ l ⁻¹' {α}) ∧
        ((Ψ G).val = ∅ ↔ G.val.val = {v}) ∧
        (G.val.val ≠ {v} →
          (Ψ G).val.Nonempty ∧
            Module.finrank ℝ (affineSpan ℝ G.val.val).direction =
              Module.finrank ℝ (affineSpan ℝ (Ψ G).val).direction + 1)) ∧
      (∀ k : ℕ,
        ∃ Ψ_skel : {S : SkeletonFace P (k + 1) // vertexSkeletonFace P (k + 1) v hv ≤ S} ≃o
            SkeletonFace Q₀ k,
          ∀ S : {S : SkeletonFace P (k + 1) // vertexSkeletonFace P (k + 1) v hv ≤ S},
            (Ψ_skel S).val =
              Ψ ⟨S.val.val, (vertexSkeletonFace_le_iff v hv S.val).mp S.property⟩) := by
  obtain ⟨l, α, hα, _, hCutV⟩ := hCut.1 v hv
  let V := {w : Fin d → ℝ | IsExposed ℝ P {w}}
  let W := V \ {v}
  have hVP : V ⊆ P := fun w hw => (mem_exposedPoints_iff_exposed_singleton.mpr hw).1
  have hHullP : P = convexHull ℝ V := by
    have h := hHull.2 ⟨P, IsExposed.refl P⟩
    change P = convexHull ℝ (P ∩ V) at h
    rwa [Set.inter_eq_right.mpr hVP] at h
  have hInsert : insert v W = V := by
    ext w
    constructor
    · rintro (rfl | hw)
      · exact hv
      · exact hw.1
    · intro hw
      by_cases hwv : w = v
      · exact Set.mem_insert_iff.mpr (Or.inl hwv)
      · exact Set.mem_insert_iff.mpr (Or.inr ⟨hw, hwv⟩)
  have hPgen : P = convexHull ℝ (insert v W) := by rw [hInsert]; exact hHullP
  have hW : W.Nonempty := by
    by_contra h
    have hEmpty : W = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hPSingle : P ⊆ {v} := by
      rw [hPgen, hEmpty, insert_empty_eq, convexHull_singleton]
    have hSub : P.Subsingleton := Set.subsingleton_of_subset_singleton hPSingle
    have : Subsingleton (Fin d → ℝ) :=
      AffineSubspace.subsingleton_of_subsingleton_span_eq_top hSub hP.2
    have hz : (0 : Fin d → ℝ) = 1 := Subsingleton.elim _ _
    exact zero_ne_one (congrFun hz ⟨0, hd⟩)
  have hWfin : W.Finite := hHull.1.sdiff
  have hSpan : affineSpan ℝ (insert v W) = ⊤ := by
    rw [← affineSpan_convexHull, ← hPgen]
    exact hP.2
  have hBelowW (w : Fin d → ℝ) (hw : w ∈ W) : l w < α := (hCutV w hw.1 hw.2).1
  have hBelowV (w : Fin d → ℝ) (hw : IsExposed ℝ P {w}) (hwv : w ≠ v) : l w < α :=
    (hCutV w hw hwv).1
  let R := (fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))) '' W
  let A := affineSpan ℝ R
  have : Nonempty A := by
    obtain ⟨w, hw⟩ := hW
    exact ⟨⟨_, subset_affineSpan ℝ R ⟨w, hw, rfl⟩⟩⟩
  obtain ⟨e, hPoly⟩ := exists_vertex_figure_coordinates d v W hWfin hW l α hα hBelowW hSpan
  have hQHull : P ∩ l ⁻¹' {α} = convexHull ℝ R := by
    rw [hPgen]
    exact convexHull_insert_inter_level_eq d v W hW l α hα hBelowW
  have hASpan : (A : Set (Fin d → ℝ)) = l ⁻¹' {α} :=
    affineSpan_crossing_image_eq_level d v W hW l α hα hBelowW hSpan
  let T : Set A := ((↑) : A → (Fin d → ℝ)) ⁻¹' R
  let f : (Fin (d - 1) → ℝ) →ᵃ[ℝ] (Fin d → ℝ) := A.subtype.comp e.symm.toAffineMap
  have hfInj : Function.Injective f := A.subtype_injective.comp e.symm.injective
  have hImageT : f '' (e '' T) = R := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      change (e.symm (e z)).val ∈ R
      rw [e.symm_apply_apply]
      exact hz
    · intro x hx
      let z : A := ⟨x, subset_affineSpan ℝ R hx⟩
      refine ⟨e z, ⟨z, hx, rfl⟩, ?_⟩
      change (e.symm (e z)).val = x
      rw [e.symm_apply_apply]
  let Q₀ : Set (Fin (d - 1) → ℝ) := convexHull ℝ (e '' T)
  have hQ₀Poly : IsDPolytope Q₀ := hPoly
  have hfQ₀ : f '' Q₀ = P ∩ l ⁻¹' {α} := by
    dsimp only [Q₀]
    rw [f.image_convexHull, hImageT, hQHull]
  obtain ⟨Φ, hΦ⟩ := vertex_figure_face_orderIso d P hP hHull.2 v hv W hW hPgen l α hα hBelowW
  obtain ⟨Θ, hΘ⟩ := polytopeFace_image_affineMap_orderIso f hfInj Q₀ (P ∩ l ⁻¹' {α}) hfQ₀
  let Ψ : {G : PolytopeFace P // v ∈ G.val} ≃o PolytopeFace Q₀ := Φ.trans Θ.symm
  have hΨimg : ∀ G : {G : PolytopeFace P // v ∈ G.val},
      f '' (Ψ G).val = G.val.val ∩ (P ∩ l ⁻¹' {α}) := by
    intro G
    have h1 := hΘ (Θ.symm (Φ G))
    rw [OrderIso.apply_symm_apply] at h1
    exact h1.symm.trans (hΦ G)
  have hGInterEq : ∀ G : {G : PolytopeFace P // v ∈ G.val},
      G.val.val ∩ (P ∩ l ⁻¹' {α}) = G.val.val ∩ l ⁻¹' {α} := by
    intro G
    ext x
    constructor
    · rintro ⟨hxG, _, hxL⟩
      exact ⟨hxG, hxL⟩
    · rintro ⟨hxG, hxL⟩
      exact ⟨hxG, G.val.property.subset hxG, hxL⟩
  have hΨprops : ∀ G : {G : PolytopeFace P // v ∈ G.val},
      f '' (Ψ G).val = G.val.val ∩ (P ∩ l ⁻¹' {α}) ∧
      ((Ψ G).val = ∅ ↔ G.val.val = {v}) ∧
      (G.val.val ≠ {v} →
        (Ψ G).val.Nonempty ∧
          Module.finrank ℝ (affineSpan ℝ G.val.val).direction =
            Module.finrank ℝ (affineSpan ℝ (Ψ G).val).direction + 1) := by
    intro G
    have hCutG := hCut.2 v l α hα hBelowV G.val.val G.val.property G.property
    have hImgEq : f '' (Ψ G).val = G.val.val ∩ l ⁻¹' {α} :=
      (hΨimg G).trans (hGInterEq G)
    have hEmptyIff : (Ψ G).val = ∅ ↔ G.val.val = {v} := by
      rw [← Set.not_nonempty_iff_eq_empty, ← Set.image_nonempty (f := f), hImgEq, hCutG.2.1, not_not]
    refine ⟨hΨimg G, hEmptyIff, ?_⟩
    intro hNeV
    obtain ⟨hSecNe, hRankEq⟩ := hCutG.2.2 hNeV
    have hΨNe : (Ψ G).val.Nonempty := by
      rw [← Set.image_nonempty (f := f), hImgEq]
      exact hSecNe
    have hRankImg :
        Module.finrank ℝ (affineSpan ℝ (G.val.val ∩ l ⁻¹' {α})).direction =
          Module.finrank ℝ (affineSpan ℝ (Ψ G).val).direction := by
      rw [← hImgEq]
      exact finrank_direction_affineSpan_image_injective f hfInj (Ψ G).val
    exact ⟨hΨNe, hRankEq.trans (by rw [hRankImg])⟩
  refine ⟨l, α, Q₀, f, Ψ, hα, hBelowV, hQ₀Poly, hfInj, hfQ₀, hΨprops, ?_⟩
  intro k
  let U := {S : SkeletonFace P (k + 1) // vertexSkeletonFace P (k + 1) v hv ≤ S}
  let toSkel : U → SkeletonFace Q₀ k := fun S =>
    let G : {G : PolytopeFace P // v ∈ G.val} :=
      ⟨S.val.val, (vertexSkeletonFace_le_iff v hv S.val).mp S.property⟩
    ⟨Ψ G, by
      by_cases hGv : G.val.val = {v}
      · exact Or.inl ((hΨprops G).2.1.mpr hGv)
      · right
        have hRankG : Module.finrank ℝ (affineSpan ℝ G.val.val).direction ≤ k + 1 := by
          rcases S.val.property with hEmp | hLe
          · exfalso
            have hvMem : v ∈ G.val.val := G.property
            rw [hEmp] at hvMem
            exact hvMem
          · exact hLe
        have hRankShift := ((hΨprops G).2.2 hGv).2
        omega⟩
  have hMapSkel (S₁ S₂ : U) : toSkel S₁ ≤ toSkel S₂ ↔ S₁ ≤ S₂ := by
    let G₁ : {G : PolytopeFace P // v ∈ G.val} :=
      ⟨S₁.val.val, (vertexSkeletonFace_le_iff v hv S₁.val).mp S₁.property⟩
    let G₂ : {G : PolytopeFace P // v ∈ G.val} :=
      ⟨S₂.val.val, (vertexSkeletonFace_le_iff v hv S₂.val).mp S₂.property⟩
    change Ψ G₁ ≤ Ψ G₂ ↔ G₁ ≤ G₂
    exact Ψ.map_rel_iff
  let embSkel : U ↪o SkeletonFace Q₀ k := OrderEmbedding.ofMapLEIff toSkel hMapSkel
  have hSurjSkel : Function.Surjective toSkel := by
    intro T
    let G : {G : PolytopeFace P // v ∈ G.val} := Ψ.symm T.val
    have hΨG : Ψ G = T.val := OrderIso.apply_symm_apply Ψ T.val
    have hGskel : G.val.val = ∅ ∨
        Module.finrank ℝ (affineSpan ℝ G.val.val).direction ≤ k + 1 := by
      right
      by_cases hGv : G.val.val = {v}
      · rw [hGv, direction_affineSpan, vectorSpan_singleton, finrank_bot]
        exact Nat.zero_le (k + 1)
      · have hRankShift := ((hΨprops G).2.2 hGv).2
        rw [hΨG] at hRankShift
        rcases T.property with hTEmp | hTLe
        · exfalso
          exact hGv (((hΨprops G).2.1).mp ((congrArg Subtype.val hΨG).trans hTEmp))
        · omega
    let S : SkeletonFace P (k + 1) := ⟨G.val, hGskel⟩
    have hvLeS : vertexSkeletonFace P (k + 1) v hv ≤ S :=
      (vertexSkeletonFace_le_iff v hv S).mpr G.property
    refine ⟨⟨S, hvLeS⟩, ?_⟩
    apply Subtype.ext
    exact hΨG
  refine ⟨OrderIso.ofSurjective embSkel hSurjSkel, fun _ => rfl⟩

end Grunbaum2003

namespace Grunbaum2003

/-- Any skeleton order isomorphism `φ : SkeletonFace P K ≃o SkeletonFace Q L` mapping
`vertexSkeletonFace P K v hv` to `vertexSkeletonFace Q L v' hv'` restricts to an order
isomorphism between the upper intervals of skeleton faces containing `v` and `v'`. -/
def skeletonIso_upperInterval_equiv {d e K L : ℕ}
    {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)}
    (φ : SkeletonFace P K ≃o SkeletonFace Q L)
    (v : Fin d → ℝ) (hv : IsExposed ℝ P {v})
    (v' : Fin e → ℝ) (hv' : IsExposed ℝ Q {v'})
    (hφv : φ (vertexSkeletonFace P K v hv) = vertexSkeletonFace Q L v' hv') :
    {S : SkeletonFace P K // v ∈ S.val.val} ≃o
      {T : SkeletonFace Q L // v' ∈ T.val.val} where
  toFun S := ⟨φ S.val, by
    rw [← vertexSkeletonFace_le_iff v' hv' (φ S.val), ← hφv, φ.le_iff_le]
    exact (vertexSkeletonFace_le_iff v hv S.val).mpr S.property⟩
  invFun T := ⟨φ.symm T.val, by
    rw [← vertexSkeletonFace_le_iff v hv (φ.symm T.val), ← φ.le_iff_le,
      φ.apply_symm_apply, hφv]
    exact (vertexSkeletonFace_le_iff v' hv' T.val).mpr T.property⟩
  left_inv S := Subtype.ext (φ.symm_apply_apply S.val)
  right_inv T := Subtype.ext (φ.apply_symm_apply T.val)
  map_rel_iff' := by
    intro S₁ S₂
    exact φ.map_rel_iff'

/-- Given `φ : SkeletonFace P K ≃o SkeletonFace Q L` mapping `{v}` to `{v'}` and
upper-interval skeleton isomorphisms `Ψ_skel_P` and `Ψ_skel_Q` onto vertex-figure polytopes
`P_v` and `Q_v'`, we obtain an induced skeleton order isomorphism
`φ_v : SkeletonFace P_v k ≃o SkeletonFace Q_v' l`. -/
def induced_vertex_figure_skeletonIso {d e d' e' K L k l : ℕ}
    {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)}
    {P_v : Set (Fin d' → ℝ)} {Q_v' : Set (Fin e' → ℝ)}
    (φ : SkeletonFace P K ≃o SkeletonFace Q L)
    (v : Fin d → ℝ) (hv : IsExposed ℝ P {v})
    (v' : Fin e → ℝ) (hv' : IsExposed ℝ Q {v'})
    (hφv : φ (vertexSkeletonFace P K v hv) = vertexSkeletonFace Q L v' hv')
    (Ψ_skel_P : {S : SkeletonFace P K // v ∈ S.val.val} ≃o SkeletonFace P_v k)
    (Ψ_skel_Q : {T : SkeletonFace Q L // v' ∈ T.val.val} ≃o SkeletonFace Q_v' l) :
    SkeletonFace P_v k ≃o SkeletonFace Q_v' l :=
  (Ψ_skel_P.symm.trans (skeletonIso_upperInterval_equiv φ v hv v' hv' hφv)).trans Ψ_skel_Q

/-- For `3 ≤ d`, reindexing `(d - 3) + 1 = d - 2` in the upper-interval skeleton isomorphism
yields `{S : SkeletonFace R (d - 2) // v ∈ S.val.val} ≃o SkeletonFace Q₀ (d - 3)` without
dependent casts on the underlying `PolytopeFace R`. -/
theorem exists_vertex_figure_codim_two_skeletonIso {d : ℕ} (hd : 3 ≤ d)
    {R : Set (Fin d → ℝ)} {Q₀ : Set (Fin (d - 1) → ℝ)} {v : Fin d → ℝ}
    (Ψ : {G : PolytopeFace R // v ∈ G.val} ≃o PolytopeFace Q₀)
    (hSkel : ∀ k : ℕ,
      ∃ Ψ_skel : {S : SkeletonFace R (k + 1) // v ∈ S.val.val} ≃o
          SkeletonFace Q₀ k,
        ∀ S : {S : SkeletonFace R (k + 1) // v ∈ S.val.val},
          (Ψ_skel S).val = Ψ ⟨S.val.val, S.property⟩) :
    ∃ Ψ_skel : {S : SkeletonFace R (d - 2) // v ∈ S.val.val} ≃o
        SkeletonFace Q₀ (d - 3),
      ∀ S : {S : SkeletonFace R (d - 2) // v ∈ S.val.val},
        (Ψ_skel S).val = Ψ ⟨S.val.val, S.property⟩ := by
  obtain ⟨Ψ_skel, hΨ_skel⟩ := hSkel (d - 3)
  have hSub : (d - 3) + 1 = d - 2 := by omega
  let eCast : {S : SkeletonFace R (d - 2) // v ∈ S.val.val} ≃o
      {S : SkeletonFace R ((d - 3) + 1) // v ∈ S.val.val} :=
    { toFun := fun S => ⟨⟨S.val.val, by rw [hSub]; exact S.val.property⟩, S.property⟩
      invFun := fun S => ⟨⟨S.val.val, by rw [← hSub]; exact S.val.property⟩, S.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  refine ⟨eCast.trans Ψ_skel, ?_⟩
  intro S
  exact hΨ_skel (eCast S)

/-- For `2 ≤ d`, any facet `F` of `P` (having direction finrank `d - 1`) that contains `v`
is strictly larger than `{v}` and therefore maps under the vertex-figure face isomorphism `Ψ`
to a facet of the `(d - 1)`-polytope `Q₀` (nonempty and of direction finrank `d - 2`). -/
theorem vertex_figure_facet_of_facet_containing_v {d : ℕ} (hd : 2 ≤ d)
    {P : Set (Fin d → ℝ)} {Q₀ : Set (Fin (d - 1) → ℝ)}
    {v : Fin d → ℝ}
    (Ψ : {G : PolytopeFace P // v ∈ G.val} ≃o PolytopeFace Q₀)
    (hΨdim : ∀ G : {G : PolytopeFace P // v ∈ G.val},
      G.val.val ≠ {v} →
        (Ψ G).val.Nonempty ∧
          Module.finrank ℝ (affineSpan ℝ G.val.val).direction =
            Module.finrank ℝ (affineSpan ℝ (Ψ G).val).direction + 1)
    (F : PolytopeFace P)
    (hFacet : F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d - 1)
    (hvF : v ∈ F.val) :
    (Ψ ⟨F, hvF⟩).val.Nonempty ∧
      Module.finrank ℝ (affineSpan ℝ (Ψ ⟨F, hvF⟩).val).direction = d - 2 := by
  have hFneV : F.val ≠ {v} := by
    intro hEq
    have hRank0 : Module.finrank ℝ (affineSpan ℝ F.val).direction = 0 := by
      rw [hEq, direction_affineSpan, vectorSpan_singleton, finrank_bot]
    have hRankFacet := hFacet.2
    omega
  obtain ⟨hNonempty, hRankShift⟩ := hΨdim ⟨F, hvF⟩ hFneV
  refine ⟨hNonempty, ?_⟩
  change Module.finrank ℝ (affineSpan ℝ F.val).direction =
    Module.finrank ℝ (affineSpan ℝ (Ψ ⟨F, hvF⟩).val).direction + 1 at hRankShift
  rw [hFacet.2] at hRankShift
  omega

/-- Lifting a vertex-figure target face `G_v' : PolytopeFace Q_v'` that realizes the
`φ_v`-down-set of `Ψ_P ⟨F, hvF⟩` back via `Ψ_Q.symm` produces an exposed face
`G = (Ψ_Q.symm G_v').val : PolytopeFace Q` containing `v'` such that for every
`S : SkeletonFace P K` containing `v`, `(φ S).val ≤ G ↔ S.val ≤ F`. -/
theorem lift_vertex_figure_downSet_to_upper_interval {d e d' e' K L k l : ℕ}
    {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)}
    {P_v : Set (Fin d' → ℝ)} {Q_v' : Set (Fin e' → ℝ)}
    (φ : SkeletonFace P K ≃o SkeletonFace Q L)
    (v : Fin d → ℝ) (hv : IsExposed ℝ P {v})
    (v' : Fin e → ℝ) (hv' : IsExposed ℝ Q {v'})
    (hφv : φ (vertexSkeletonFace P K v hv) = vertexSkeletonFace Q L v' hv')
    (Ψ_P : {G : PolytopeFace P // v ∈ G.val} ≃o PolytopeFace P_v)
    (Ψ_Q : {H : PolytopeFace Q // v' ∈ H.val} ≃o PolytopeFace Q_v')
    (Ψ_skel_P : {S : SkeletonFace P K // v ∈ S.val.val} ≃o SkeletonFace P_v k)
    (hΨ_skel_P : ∀ S : {S : SkeletonFace P K // v ∈ S.val.val},
      (Ψ_skel_P S).val = Ψ_P ⟨S.val.val, S.property⟩)
    (Ψ_skel_Q : {T : SkeletonFace Q L // v' ∈ T.val.val} ≃o SkeletonFace Q_v' l)
    (hΨ_skel_Q : ∀ T : {T : SkeletonFace Q L // v' ∈ T.val.val},
      (Ψ_skel_Q T).val = Ψ_Q ⟨T.val.val, T.property⟩)
    (F : PolytopeFace P) (hvF : v ∈ F.val)
    (G_v' : PolytopeFace Q_v')
    (hG_v' : ∀ T₀ : SkeletonFace Q_v' l,
      T₀.val ≤ G_v' ↔
        ((induced_vertex_figure_skeletonIso φ v hv v' hv' hφv Ψ_skel_P Ψ_skel_Q).symm T₀).val ≤
          Ψ_P ⟨F, hvF⟩) :
    let G : PolytopeFace Q := (Ψ_Q.symm G_v').val
    v' ∈ G.val ∧
    ∀ (S : SkeletonFace P K), v ∈ S.val.val →
      ((φ S).val ≤ G ↔ S.val ≤ F) := by
  intro G
  refine ⟨(Ψ_Q.symm G_v').property, ?_⟩
  intro S hvS
  let S_sub : {S : SkeletonFace P K // v ∈ S.val.val} := ⟨S, hvS⟩
  let T_sub : {T : SkeletonFace Q L // v' ∈ T.val.val} :=
    skeletonIso_upperInterval_equiv φ v hv v' hv' hφv S_sub
  let T₀ : SkeletonFace Q_v' l := Ψ_skel_Q T_sub
  have hT₀_val : T₀.val = Ψ_Q ⟨(φ S).val, T_sub.property⟩ := hΨ_skel_Q T_sub
  have hSymmT₀ :
      (induced_vertex_figure_skeletonIso φ v hv v' hv' hφv Ψ_skel_P Ψ_skel_Q).symm T₀ =
        Ψ_skel_P S_sub := by
    simp [induced_vertex_figure_skeletonIso, T₀, T_sub]
  have hLeQ :
      (φ S).val ≤ G ↔ T₀.val ≤ G_v' := by
    rw [hT₀_val]
    have hGeq : G_v' = Ψ_Q ⟨G, (Ψ_Q.symm G_v').property⟩ :=
      (Ψ_Q.apply_symm_apply G_v').symm
    rw [hGeq]
    exact (Ψ_Q.le_iff_le (x := ⟨(φ S).val, T_sub.property⟩)
      (y := ⟨G, (Ψ_Q.symm G_v').property⟩)).symm
  have hLeP :
      (Ψ_skel_P S_sub).val ≤ Ψ_P ⟨F, hvF⟩ ↔ S.val ≤ F := by
    rw [hΨ_skel_P S_sub]
    exact Ψ_P.le_iff_le (x := ⟨S.val, hvS⟩) (y := ⟨F, hvF⟩)
  rw [hLeQ, hG_v' T₀, hSymmT₀, hLeP]

end Grunbaum2003

namespace Grunbaum2003

/-- If an edge `S : SkeletonFace P k` (`finrank = 1`) contains two distinct exposed vertices
`v ≠ w` of `P`, then `S.val.val = convexHull ℝ {v, w}`, and for any exposed face `F : PolytopeFace P`
containing `v`, we have `S.val ≤ F ↔ w ∈ F.val`. -/
theorem skeletonFace_edge_le_face_iff_second_vertex_mem {d k : ℕ} {P : Set (Fin d → ℝ)}
    (hHull : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}))
    (S : SkeletonFace P k)
    (hEdge : S.val.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ S.val.val).direction = 1)
    {v w : Fin d → ℝ} (hv : IsExposed ℝ P {v}) (hw : IsExposed ℝ P {w}) (hvw : v ≠ w)
    (hvS : v ∈ S.val.val) (hwS : w ∈ S.val.val) :
    S.val.val = convexHull ℝ ({v, w} : Set (Fin d → ℝ)) ∧
    ∀ (F : PolytopeFace P), v ∈ F.val → (S.val ≤ F ↔ w ∈ F.val) := by
  obtain ⟨a, b, _, _, _, hInter, hHullAB⟩ :=
    (nonempty_exposed_finrank_one_iff_exposed_pair hHull S.val.val S.val.property).mp hEdge
  have hvAB : v = a ∨ v = b := by
    have h : v ∈ ({a, b} : Set (Fin d → ℝ)) := hInter ▸ ⟨hvS, hv⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have hwAB : w = a ∨ w = b := by
    have h : w ∈ ({a, b} : Set (Fin d → ℝ)) := hInter ▸ ⟨hwS, hw⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have hPairEq : ({a, b} : Set (Fin d → ℝ)) = {v, w} := by
    rcases hvAB with rfl | rfl <;> rcases hwAB with rfl | rfl
    · exact False.elim (hvw rfl)
    · rfl
    · exact Set.pair_comm w v
    · exact False.elim (hvw rfl)
  have hSHull : S.val.val = convexHull ℝ ({v, w} : Set (Fin d → ℝ)) := by
    rw [hHullAB, hPairEq]
  refine ⟨hSHull, ?_⟩
  intro F hvF
  constructor
  · intro hSF
    exact hSF hwS
  · intro hwF
    change S.val.val ⊆ F.val
    rw [hSHull, hHull.2 F]
    apply convexHull_mono
    rintro x (rfl | rfl)
    · exact ⟨hvF, hv⟩
    · exact ⟨hwF, hw⟩

/-- If `G : PolytopeFace Q` contains `v'` (where `φ({v}) = {v'}`) and satisfies the upper-interval
equivalence `∀ S : SkeletonFace P K, v ∈ S.val.val → ((φ S).val ≤ G ↔ S.val ≤ F)` for a face `F`
containing `v`, then `(φ({x})).val ≤ G ↔ x ∈ F.val` holds both at `x = v` and at every exposed
vertex `w` of `P` adjacent to `v` via an edge `E : SkeletonFace P K`. -/
theorem lifted_face_agrees_on_base_and_adjacent_vertices {d e K L : ℕ}
    {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)}
    (hHullP : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}))
    (hHullQ : {y : Fin e → ℝ | IsExposed ℝ Q {y}}.Finite ∧
      ∀ E : PolytopeFace Q,
        E.val = convexHull ℝ (E.val ∩ {y : Fin e → ℝ | IsExposed ℝ Q {y}}))
    (φ : SkeletonFace P K ≃o SkeletonFace Q L)
    (v : Fin d → ℝ) (hv : IsExposed ℝ P {v})
    (v' : Fin e → ℝ) (hv' : IsExposed ℝ Q {v'})
    (hφv : φ (vertexSkeletonFace P K v hv) = vertexSkeletonFace Q L v' hv')
    (F : PolytopeFace P) (hvF : v ∈ F.val)
    (G : PolytopeFace Q) (hv'G : v' ∈ G.val)
    (hUpper : ∀ (S : SkeletonFace P K), v ∈ S.val.val →
      ((φ S).val ≤ G ↔ S.val ≤ F)) :
    ((φ (vertexSkeletonFace P K v hv)).val ≤ G ↔ v ∈ F.val) ∧
    (∀ (w : Fin d → ℝ) (hw : IsExposed ℝ P {w}) (E : SkeletonFace P K),
      (E.val.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ E.val.val).direction = 1) →
      v ∈ E.val.val → w ∈ E.val.val →
      ((φ (vertexSkeletonFace P K w hw)).val ≤ G ↔ w ∈ F.val)) := by
  have hAtV : (φ (vertexSkeletonFace P K v hv)).val ≤ G ↔ v ∈ F.val := by
    rw [hφv]
    change ({v'} : Set (Fin e → ℝ)) ⊆ G.val ↔ v ∈ F.val
    rw [Set.singleton_subset_iff]
    exact ⟨fun _ => hvF, fun _ => hv'G⟩
  refine ⟨hAtV, ?_⟩
  intro w hw E hEdge hvE hwE
  by_cases hvw : v = w
  · subst hvw
    exact hAtV
  · obtain ⟨w', hw', hφw⟩ :=
      skeletonIso_maps_exposed_singleton hHullP.2 hHullQ.2 φ w hw
    have hv'w' : v' ≠ w' := by
      intro hEq
      subst w'
      have hSubEq : vertexSkeletonFace Q L v' hv' = vertexSkeletonFace Q L v' hw' := rfl
      have hPhiEq : φ (vertexSkeletonFace P K v hv) = φ (vertexSkeletonFace P K w hw) :=
        hφv.trans (hSubEq.trans hφw.symm)
      have hVW : vertexSkeletonFace P K v hv = vertexSkeletonFace P K w hw :=
        φ.injective hPhiEq
      have hSetEq : ({v} : Set (Fin d → ℝ)) = {w} :=
        congrArg (fun U : SkeletonFace P K => U.val.val) hVW
      exact hvw (Set.singleton_eq_singleton_iff.mp hSetEq)
    have hEdgeQ :
        (φ E).val.val.Nonempty ∧
          Module.finrank ℝ (affineSpan ℝ (φ E).val.val).direction = 1 :=
      (skeletonIso_finrank_one_iff hHullP hHullQ φ E).mpr hEdge
    have hv'PhiE : v' ∈ (φ E).val.val := by
      rw [← vertexSkeletonFace_le_iff v' hv' (φ E), ← hφv, φ.le_iff_le]
      exact (vertexSkeletonFace_le_iff v hv E).mpr hvE
    have hw'PhiE : w' ∈ (φ E).val.val := by
      rw [← vertexSkeletonFace_le_iff w' hw' (φ E), ← hφw, φ.le_iff_le]
      exact (vertexSkeletonFace_le_iff w hw E).mpr hwE
    have hEdgeQLe : (φ E).val ≤ G ↔ w' ∈ G.val :=
      (skeletonFace_edge_le_face_iff_second_vertex_mem hHullQ (φ E) hEdgeQ
        hv' hw' hv'w' hv'PhiE hw'PhiE).2 G hv'G
    have hEdgePLe : E.val ≤ F ↔ w ∈ F.val :=
      (skeletonFace_edge_le_face_iff_second_vertex_mem hHullP E hEdge
        hv hw hvw hvE hwE).2 F hvF
    have hPhiWLe : (φ (vertexSkeletonFace P K w hw)).val ≤ G ↔ w' ∈ G.val := by
      rw [hφw]
      change ({w'} : Set (Fin e → ℝ)) ⊆ G.val ↔ w' ∈ G.val
      exact Set.singleton_subset_iff
    rw [hPhiWLe, ← hEdgeQLe, hUpper E hvE, hEdgePLe]

end Grunbaum2003

namespace Grunbaum2003

/-- Two lifted faces `G_u, G_w ∈ PolytopeFace Q` satisfying the upper-interval equivalence
with respect to `F` at `u` and `w` agree on every skeleton face `R ∈ SkeletonFace P K`
containing both `u` and `w`. -/
theorem lifted_faces_agree_on_shared_skeleton_face
    {d e K L : ℕ} {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)}
    (φ : SkeletonFace P K ≃o SkeletonFace Q L)
    (F : PolytopeFace P)
    (u w : Fin d → ℝ)
    (G_u G_w : PolytopeFace Q)
    (hUpper_u : ∀ S : SkeletonFace P K, u ∈ S.val.val →
      ((φ S).val ≤ G_u ↔ S.val ≤ F))
    (hUpper_w : ∀ S : SkeletonFace P K, w ∈ S.val.val →
      ((φ S).val ≤ G_w ↔ S.val ≤ F))
    (R : SkeletonFace P K) (huR : u ∈ R.val.val) (hwR : w ∈ R.val.val) :
    ((φ R).val ≤ G_u ↔ (φ R).val ≤ G_w) ∧
    (R.val ≤ F → (φ R).val ≤ G_u ∧ (φ R).val ≤ G_w) := by
  have hu := hUpper_u R huR
  have hw := hUpper_w R hwR
  refine ⟨hu.trans hw.symm, fun hRF => ⟨hu.mpr hRF, hw.mpr hRF⟩⟩

/-- One-step propagation along a skeleton face `E ≤ F` (such as an edge of `F`):
if `G` satisfies the upper-interval equivalence at `u` and `E ∈ SkeletonFace P K`
satisfies `E.val ≤ F`, `u ∈ E.val.val`, and `w ∈ E.val.val`, then `(φ ({w})).val ≤ G`. -/
theorem forward_inclusion_along_facet_skeleton_face
    {d e K L : ℕ} {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)}
    (φ : SkeletonFace P K ≃o SkeletonFace Q L)
    (F : PolytopeFace P)
    (u w : Fin d → ℝ) (hw : IsExposed ℝ P {w})
    (G : PolytopeFace Q)
    (hUpper_u : ∀ S : SkeletonFace P K, u ∈ S.val.val →
      ((φ S).val ≤ G ↔ S.val ≤ F))
    (E : SkeletonFace P K) (hEF : E.val ≤ F)
    (huE : u ∈ E.val.val) (hwE : w ∈ E.val.val) :
    (φ (vertexSkeletonFace P K w hw)).val ≤ G := by
  have hφE : (φ E).val ≤ G := (hUpper_u E huE).mpr hEF
  have hw_le_E : vertexSkeletonFace P K w hw ≤ E :=
    (vertexSkeletonFace_le_iff w hw E).mpr hwE
  have hφw_le_φE : (φ (vertexSkeletonFace P K w hw)).val ≤ (φ E).val :=
    φ.monotone hw_le_E
  exact le_trans hφw_le_φE hφE

/-- Symmetric forward-inclusion equivalence: if `φ` maps exposed vertices of `F` into `G`
and `φ.symm` maps exposed vertices of `G` into `F`, then for every exposed vertex `x` of `P`,
`(φ ({x})).val ≤ G ↔ x ∈ F.val`. -/
theorem iff_exposed_vertex_mem_of_forward_and_symm_forward
    {d e K L : ℕ} {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)}
    (hHullP : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}))
    (hHullQ : {y : Fin e → ℝ | IsExposed ℝ Q {y}}.Finite ∧
      ∀ E : PolytopeFace Q,
        E.val = convexHull ℝ (E.val ∩ {y : Fin e → ℝ | IsExposed ℝ Q {y}}))
    (φ : SkeletonFace P K ≃o SkeletonFace Q L)
    (F : PolytopeFace P) (G : PolytopeFace Q)
    (hFwd : ∀ (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
      x ∈ F.val → (φ (vertexSkeletonFace P K x hx)).val ≤ G)
    (hSymmFwd : ∀ (y : Fin e → ℝ) (hy : IsExposed ℝ Q {y}),
      y ∈ G.val → (φ.symm (vertexSkeletonFace Q L y hy)).val ≤ F)
    (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}) :
    (φ (vertexSkeletonFace P K x hx)).val ≤ G ↔ x ∈ F.val := by
  refine ⟨?_, hFwd x hx⟩
  intro hφxG
  obtain ⟨y, hy, hφx⟩ :=
    skeletonIso_maps_exposed_singleton hHullP.2 hHullQ.2 φ x hx
  have hyG : y ∈ G.val := by
    rw [hφx] at hφxG
    exact hφxG (Set.mem_singleton y)
  have hSymm : (φ.symm (vertexSkeletonFace Q L y hy)).val ≤ F :=
    hSymmFwd y hy hyG
  have hSymmEq : φ.symm (vertexSkeletonFace Q L y hy) = vertexSkeletonFace P K x hx := by
    rw [← hφx, OrderIso.symm_apply_apply]
  rw [hSymmEq] at hSymm
  exact hSymm (Set.mem_singleton x)

end Grunbaum2003

namespace Grunbaum2003

theorem vertex_figure_lift_shared_skeleton_and_symmetric_forward_iff_proved :
  ∀ {d e K L : ℕ} {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)},
    ({x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) →
    ({y : Fin e → ℝ | IsExposed ℝ Q {y}}.Finite ∧
      ∀ E : PolytopeFace Q,
        E.val = convexHull ℝ (E.val ∩ {y : Fin e → ℝ | IsExposed ℝ Q {y}})) →
    ∀ (vertexSkeletonFace : ∀ {m : ℕ} (R : Set (Fin m → ℝ)) (r : ℕ)
        (x : Fin m → ℝ), IsExposed ℝ R {x} → SkeletonFace R r)
      (hVertexVal : ∀ {m : ℕ} (R : Set (Fin m → ℝ)) (r : ℕ)
        (x : Fin m → ℝ) (hx : IsExposed ℝ R {x}),
        (vertexSkeletonFace R r x hx).val.val = {x})
      (φ : SkeletonFace P K ≃o SkeletonFace Q L)
      (F : PolytopeFace P),
      (∀ (u w : Fin d → ℝ) (G_u G_w : PolytopeFace Q),
        (∀ S : SkeletonFace P K, u ∈ S.val.val → ((φ S).val ≤ G_u ↔ S.val ≤ F)) →
        (∀ S : SkeletonFace P K, w ∈ S.val.val → ((φ S).val ≤ G_w ↔ S.val ≤ F)) →
        ∀ R : SkeletonFace P K, u ∈ R.val.val → w ∈ R.val.val →
          (((φ R).val ≤ G_u ↔ (φ R).val ≤ G_w) ∧
            (R.val ≤ F → (φ R).val ≤ G_u ∧ (φ R).val ≤ G_w))) ∧
      (∀ (u w : Fin d → ℝ) (hw : IsExposed ℝ P {w}) (G : PolytopeFace Q),
        (∀ S : SkeletonFace P K, u ∈ S.val.val → ((φ S).val ≤ G ↔ S.val ≤ F)) →
        ∀ E : SkeletonFace P K, E.val ≤ F → u ∈ E.val.val → w ∈ E.val.val →
          (φ (vertexSkeletonFace P K w hw)).val ≤ G) ∧
      (∀ (G : PolytopeFace Q),
        (∀ (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
          x ∈ F.val → (φ (vertexSkeletonFace P K x hx)).val ≤ G) →
        (∀ (y : Fin e → ℝ) (hy : IsExposed ℝ Q {y}),
          y ∈ G.val → (φ.symm (vertexSkeletonFace Q L y hy)).val ≤ F) →
        ∀ (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
          ((φ (vertexSkeletonFace P K x hx)).val ≤ G ↔ x ∈ F.val)) := by
  intro d e K L P Q hHullP hHullQ vFace hVVal φ F
  have hEqV :
      ∀ {m : ℕ} (R : Set (Fin m → ℝ)) (r : ℕ) (x : Fin m → ℝ) (hx : IsExposed ℝ R {x}),
        vFace R r x hx = vertexSkeletonFace R r x hx := by
    intro m R r x hx
    ext z
    change z ∈ (vFace R r x hx).val.val ↔ z ∈ ({x} : Set (Fin m → ℝ))
    rw [hVVal R r x hx]
  refine ⟨?_, ?_, ?_⟩
  · intro u w G_u G_w hUpper_u hUpper_w R huR hwR
    exact lifted_faces_agree_on_shared_skeleton_face φ F u w G_u G_w hUpper_u hUpper_w R huR hwR
  · intro u w hw G hUpper_u E hEF huE hwE
    rw [hEqV P K w hw]
    exact forward_inclusion_along_facet_skeleton_face φ F u w hw G hUpper_u E hEF huE hwE
  · intro G hFwd hSymmFwd x hx
    rw [hEqV P K x hx]
    refine iff_exposed_vertex_mem_of_forward_and_symm_forward hHullP hHullQ φ F G ?_ ?_ x hx
    · intro x' hx' hx'F
      rw [← hEqV P K x' hx']
      exact hFwd x' hx' hx'F
    · intro y' hy' hy'G
      rw [← hEqV Q L y' hy']
      exact hSymmFwd y' hy' hy'G

end Grunbaum2003

end

open Grunbaum2003 in
theorem solution :
  ∀ {d e K L : ℕ} {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)},
    ({x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) →
    ({y : Fin e → ℝ | IsExposed ℝ Q {y}}.Finite ∧
      ∀ E : PolytopeFace Q,
        E.val = convexHull ℝ (E.val ∩ {y : Fin e → ℝ | IsExposed ℝ Q {y}})) →
    ∀ (vertexSkeletonFace : ∀ {m : ℕ} (R : Set (Fin m → ℝ)) (r : ℕ)
        (x : Fin m → ℝ), IsExposed ℝ R {x} → SkeletonFace R r)
      (hVertexVal : ∀ {m : ℕ} (R : Set (Fin m → ℝ)) (r : ℕ)
        (x : Fin m → ℝ) (hx : IsExposed ℝ R {x}),
        (vertexSkeletonFace R r x hx).val.val = {x})
      (φ : SkeletonFace P K ≃o SkeletonFace Q L)
      (F : PolytopeFace P),
      (∀ (u w : Fin d → ℝ) (G_u G_w : PolytopeFace Q),
        (∀ S : SkeletonFace P K, u ∈ S.val.val → ((φ S).val ≤ G_u ↔ S.val ≤ F)) →
        (∀ S : SkeletonFace P K, w ∈ S.val.val → ((φ S).val ≤ G_w ↔ S.val ≤ F)) →
        ∀ R : SkeletonFace P K, u ∈ R.val.val → w ∈ R.val.val →
          (((φ R).val ≤ G_u ↔ (φ R).val ≤ G_w) ∧
            (R.val ≤ F → (φ R).val ≤ G_u ∧ (φ R).val ≤ G_w))) ∧
      (∀ (u w : Fin d → ℝ) (hw : IsExposed ℝ P {w}) (G : PolytopeFace Q),
        (∀ S : SkeletonFace P K, u ∈ S.val.val → ((φ S).val ≤ G ↔ S.val ≤ F)) →
        ∀ E : SkeletonFace P K, E.val ≤ F → u ∈ E.val.val → w ∈ E.val.val →
          (φ (vertexSkeletonFace P K w hw)).val ≤ G) ∧
      (∀ (G : PolytopeFace Q),
        (∀ (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
          x ∈ F.val → (φ (vertexSkeletonFace P K x hx)).val ≤ G) →
        (∀ (y : Fin e → ℝ) (hy : IsExposed ℝ Q {y}),
          y ∈ G.val → (φ.symm (vertexSkeletonFace Q L y hy)).val ≤ F) →
        ∀ (x : Fin d → ℝ) (hx : IsExposed ℝ P {x}),
          ((φ (vertexSkeletonFace P K x hx)).val ≤ G ↔ x ∈ F.val)) :=
  Grunbaum2003.vertex_figure_lift_shared_skeleton_and_symmetric_forward_iff_proved
