-- Prove2me | solution 1 for Grunbaum2003.exposed_edge_pair_and_simplex_faceCount_choose
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T02:15:07.224979+00:00
-- url     : https://prove2.me/submissions/c870634e-4e91-4bf0-93d4-81a6e6edb276

import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_faceCount
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Independent

set_option autoImplicit false

open scoped BigOperators Classical
noncomputable section

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

/-- The convex hull of two distinct points `{a, b}` has affine direction finrank `1`
and is the convex hull of an affinely independent `2`-point family `![a, b]`. -/
theorem finrank_direction_convexHull_pair {d : ℕ} {a b : Fin d → ℝ} (hab : a ≠ b) :
    Module.finrank ℝ (affineSpan ℝ (convexHull ℝ ({a, b} : Set (Fin d → ℝ)))).direction = 1 ∧
    ∃ v : Fin 2 → (Fin d → ℝ),
      AffineIndependent ℝ v ∧
      convexHull ℝ ({a, b} : Set (Fin d → ℝ)) = convexHull ℝ (Set.range v) := by
  have hRange : Set.range (![a, b] : Fin 2 → (Fin d → ℝ)) = {a, b} := by
    ext x
    simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Set.mem_insert_iff, Set.mem_singleton_iff, eq_comm]
  refine ⟨?_, ![a, b], affineIndependent_of_ne ℝ hab, congrArg (convexHull ℝ) hRange.symm⟩
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
      exact (finrank_direction_convexHull_pair hab).1

/-- Every full-dimensional `2$-polytope `P ⊆ ℝ²` satisfying the exposed-vertex hull
representation is automatically a simplicial `2`-polytope (`IsSimplicialDPolytope P`). -/
theorem isSimplicialDPolytope_two_iff_isDPolytope (P : Set (Fin 2 → ℝ))
    (hHull : {x : Fin 2 → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin 2 → ℝ | IsExposed ℝ P {x}})) :
    IsSimplicialDPolytope P ↔ IsDPolytope P := by
  constructor
  · exact fun h => h.1
  · intro hP
    refine ⟨hP, ?_⟩
    intro F hFne hF hRankAdd
    have hRank : Module.finrank ℝ (affineSpan ℝ F).direction = 1 := by omega
    obtain ⟨a, b, _, _, hab, _, hFPair⟩ :=
      (nonempty_exposed_finrank_one_iff_exposed_pair hHull F hF).mp ⟨hFne, hRank⟩
    obtain ⟨_, v, hvInd, hvHull⟩ := finrank_direction_convexHull_pair hab
    exact ⟨v, hvInd, hFPair.trans hvHull⟩

end Grunbaum2003

namespace Grunbaum2003

/-- Any exposed face of a finite hull is the hull of its incident input points. -/
theorem exposedFace_eq_convexHull_incident_range {d n : ℕ}
    (v : Fin n → Fin d → ℝ) {F : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ (convexHull ℝ (Set.range v)) F) :
    F = convexHull ℝ (F ∩ Set.range v) := by
  have hPcomp : IsCompact (convexHull ℝ (Set.range v)) :=
    (Set.finite_range v).isCompact_convexHull ℝ
  have hFcomp : IsCompact F := hF.isCompact hPcomp
  have hFconv : Convex ℝ F := hF.convex (convex_convexHull ℝ (Set.range v))
  have hExtRange : F.extremePoints ℝ ⊆ Set.range v := by
    intro x hx
    rw [hF.isExtreme.extremePoints_eq] at hx
    exact extremePoints_convexHull_subset hx.2
  have hExtFin : (F.extremePoints ℝ).Finite := (Set.finite_range v).subset hExtRange
  have hKM := closure_convexHull_extremePoints hFcomp hFconv
  rw [(hExtFin.isCompact_convexHull ℝ).isClosed.closure_eq] at hKM
  apply Set.Subset.antisymm
  · apply hKM.symm.subset.trans
    apply convexHull_mono
    intro x hx
    exact ⟨extremePoints_subset hx, hExtRange hx⟩
  · exact convexHull_min Set.inter_subset_left hFconv

/-- A linear support certificate realizes an exposed face and certifies its exact
input-label incidence set. -/
theorem exposedFace_of_label_maximizers {d n : ℕ}
    (v : Fin n → Fin d → ℝ) (s : Set (Fin n)) (hs : s.Nonempty)
    (l : (Fin d → ℝ) →L[ℝ] ℝ) (b : ℝ)
    (hbound : ∀ i : Fin n, l (v i) ≤ b)
    (heq : ∀ i : Fin n, l (v i) = b ↔ i ∈ s) :
    IsExposed ℝ (convexHull ℝ (Set.range v)) (convexHull ℝ (v '' s)) ∧
      ∀ i : Fin n, v i ∈ convexHull ℝ (v '' s) ↔ i ∈ s := by
  let P := convexHull ℝ (Set.range v)
  let F := l.toExposed P
  have hPbound : ∀ x ∈ P, l x ≤ b := by
    have hconv : Convex ℝ {x : Fin d → ℝ | l x ≤ b} := by
      intro x hx y hy a c ha hc hac
      change l (a • x + c • y) ≤ b
      rw [map_add, map_smul, map_smul]
      change a * l x + c * l y ≤ b
      calc a * l x + c * l y ≤ a * b + c * b :=
          add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hc)
        _ = b := by rw [← add_mul, hac, one_mul]
    exact convexHull_min (by rintro _ ⟨i, rfl⟩; exact hbound i) hconv
  have hFlabels : ∀ i : Fin n, v i ∈ F ↔ i ∈ s := by
    intro i
    constructor
    · intro hi
      obtain ⟨j, hj⟩ := hs
      have hbj : l (v j) = b := (heq j).mpr hj
      have hbi : b ≤ l (v i) := by
        rw [← hbj]
        exact hi.2 (v j) (subset_convexHull ℝ _ (Set.mem_range_self j))
      exact (heq i).mp (le_antisymm (hbound i) hbi)
    · intro hi
      refine ⟨subset_convexHull ℝ _ (Set.mem_range_self i), ?_⟩
      intro x hx
      rw [(heq i).mpr hi]
      exact hPbound x hx
  have hInc : F ∩ Set.range v = v '' s := by
    ext x
    constructor
    · rintro ⟨hx, i, rfl⟩
      exact ⟨i, (hFlabels i).mp hx, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(hFlabels i).mpr hi, Set.mem_range_self i⟩
  have hFhull : F = convexHull ℝ (v '' s) := by
    calc F = convexHull ℝ (F ∩ Set.range v) :=
          exposedFace_eq_convexHull_incident_range v
            (ContinuousLinearMap.toExposed.isExposed (l := l) (A := P))
      _ = convexHull ℝ (v '' s) := congrArg (convexHull ℝ) hInc
  constructor
  · rw [← hFhull]
    exact (ContinuousLinearMap.toExposed.isExposed (l := l) (A := P))
  · intro i
    rw [← hFhull]
    exact hFlabels i

/-- A simplex with `d + 1` affinely independent vertices in `ℝ^d` has full affine span. -/
theorem simplex_affineSpan_eq_top (d : ℕ) (v : Fin (d + 1) → Fin d → ℝ)
    (hv : AffineIndependent ℝ v) : affineSpan ℝ (Set.range v) = ⊤ := by
  apply hv.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
  simp only [Fintype.card_fin, Module.finrank_fin_fun]

/-- The convex hull of `d + 1` affinely independent vertices in `ℝ^d` is a `d`-polytope. -/
theorem simplex_isDPolytope (d : ℕ) (v : Fin (d + 1) → Fin d → ℝ)
    (hv : AffineIndependent ℝ v) : IsDPolytope (convexHull ℝ (Set.range v)) := by
  refine ⟨⟨Set.range v, Set.finite_range v, Set.range_nonempty v, rfl⟩, ?_⟩
  rw [affineSpan_convexHull]
  exact simplex_affineSpan_eq_top d v hv

/-- Every vertex-subset hull of a simplex is an exposed face and has
exactly the selected incident vertices. -/
theorem simplex_subset_hull_isExposed_and_labels (d : ℕ)
    (v : Fin (d + 1) → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (I : Finset (Fin (d + 1))) :
    IsExposed ℝ (convexHull ℝ (Set.range v)) (convexHull ℝ (v '' (I : Set (Fin (d + 1))))) ∧
      ∀ j : Fin (d + 1), v j ∈ convexHull ℝ (v '' (I : Set (Fin (d + 1)))) ↔ j ∈ I := by
  rcases I.eq_empty_or_nonempty with rfl | hI
  · simp only [Finset.coe_empty, Set.image_empty, convexHull_empty, Set.mem_empty_iff_false,
      Finset.notMem_empty, implies_true, and_true]
    exact fun h => False.elim (Set.not_nonempty_empty h)
  let b : AffineBasis (Fin (d + 1)) ℝ (Fin d → ℝ) :=
    ⟨v, hv, simplex_affineSpan_eq_top d v hv⟩
  let L : (Fin d → ℝ) →ₗ[ℝ] ℝ := ∑ i ∈ I, (b.coord i).linear
  let c : ℝ := ∑ i ∈ I, b.coord i 0
  let l : StrongDual ℝ (Fin d → ℝ) := L.toContinuousLinearMap
  have hl : ∀ j : Fin (d + 1), l (v j) = (if j ∈ I then 1 else 0) - c := by
    intro j
    change L (v j) = _
    simp only [L, LinearMap.sum_apply]
    have hlin : ∀ i : Fin (d + 1), (b.coord i).linear (v j) =
        b.coord i (v j) - b.coord i 0 := by
      intro i
      exact congrFun (b.coord i).decomp' (v j)
    simp_rw [hlin]
    rw [Finset.sum_sub_distrib]
    change (∑ i ∈ I, b.coord i (b j)) - c = _
    simp only [AffineBasis.coord_apply, Finset.sum_ite_eq']
  apply exposedFace_of_label_maximizers v (I : Set (Fin (d + 1)))
    (Finset.coe_nonempty.mpr hI) l (1 - c)
  · intro j
    rw [hl j]
    by_cases hj : j ∈ I
    · simp only [hj, if_true, le_refl]
    · simp only [hj, if_false]
      exact sub_le_sub_right zero_le_one c
  · intro j
    rw [hl j]
    by_cases hj : j ∈ I
    · simp only [hj, if_true, SetLike.mem_coe]
    · simp only [hj, if_false, Finset.mem_coe, iff_false]
      exact fun h => zero_ne_one (sub_left_injective h)

/-- For any nonempty subset `I` of simplex vertex indices, the affine direction finrank
of `convexHull ℝ (v '' I)` plus `1` equals `I.card`. -/
theorem simplex_subset_hull_finrank_add_one (d : ℕ)
    (v : Fin (d + 1) → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (I : Finset (Fin (d + 1))) (hI : I.Nonempty) :
    Module.finrank ℝ
      (affineSpan ℝ (convexHull ℝ (v '' (I : Set (Fin (d + 1)))))).direction + 1 =
      I.card := by
  have : Nonempty ↥I := ⟨⟨hI.choose, hI.choose_spec⟩⟩
  let emb : ↥I ↪ Fin (d + 1) := ⟨Subtype.val, Subtype.val_injective⟩
  have hi : AffineIndependent ℝ (fun i : ↥I => v i.val) := hv.comp_embedding emb
  have hRange : Set.range (fun i : ↥I => v i.val) = v '' (I : Set (Fin (d + 1))) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.property, rfl⟩
    · rintro ⟨i, hiI, rfl⟩
      exact ⟨⟨i, hiI⟩, rfl⟩
  rw [affineSpan_convexHull, direction_affineSpan, ← hRange]
  simpa only [Fintype.card_coe] using hi.finrank_vectorSpan_add_one

/-- Every exposed face `F` of a simplex `convexHull ℝ (Set.range v)` is the convex hull
of `v '' I` where `I = Finset.univ.filter (fun j => v j ∈ F)`. -/
theorem simplex_exposedFace_eq_subset_hull (d : ℕ)
    (v : Fin (d + 1) → Fin d → ℝ) {F : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ (convexHull ℝ (Set.range v)) F) :
    F = convexHull ℝ (v '' ((Finset.univ.filter (fun j : Fin (d + 1) => v j ∈ F) :
      Finset (Fin (d + 1))) : Set (Fin (d + 1)))) := by
  have hInc : F ∩ Set.range v =
      v '' ((Finset.univ.filter (fun j : Fin (d + 1) => v j ∈ F) :
        Finset (Fin (d + 1))) : Set (Fin (d + 1))) := by
    ext x
    constructor
    · rintro ⟨hx, j, rfl⟩
      exact ⟨j, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hx⟩), rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨(Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2, Set.mem_range_self j⟩
  rw [← hInc]
  exact exposedFace_eq_convexHull_incident_range v hF

/-- The convex hull of `d + 1` affinely independent vertices in `ℝ^d` is a
simplicial `d`-polytope. -/
theorem simplex_isSimplicialDPolytope (d : ℕ) (v : Fin (d + 1) → Fin d → ℝ)
    (hv : AffineIndependent ℝ v) :
    IsSimplicialDPolytope (convexHull ℝ (Set.range v)) := by
  refine ⟨simplex_isDPolytope d v hv, ?_⟩
  intro F hne hF hdim
  let I : Finset (Fin (d + 1)) := Finset.univ.filter (fun j => v j ∈ F)
  have hFEq : F = convexHull ℝ (v '' (I : Set (Fin (d + 1)))) :=
    simplex_exposedFace_eq_subset_hull d v hF
  have hIne : I.Nonempty := by
    have hh : (convexHull ℝ (v '' (I : Set (Fin (d + 1))))).Nonempty := hFEq ▸ hne
    obtain ⟨_, j, hj, rfl⟩ := convexHull_nonempty_iff.mp hh
    exact ⟨j, Finset.mem_coe.mp hj⟩
  have hRank := simplex_subset_hull_finrank_add_one d v hv I hIne
  rw [← hFEq] at hRank
  have : Nonempty ↥I := ⟨⟨hIne.choose, hIne.choose_spec⟩⟩
  let emb : ↥I ↪ Fin (d + 1) := ⟨Subtype.val, Subtype.val_injective⟩
  have hi : AffineIndependent ℝ (fun i : ↥I => v i.val) := hv.comp_embedding emb
  have hCard : d = I.card := hdim.symm.trans hRank
  let e : Fin d ≃ ↥I :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_fin, Fintype.card_coe] using hCard)
  refine ⟨(fun i : ↥I => v i.val) ∘ e, hi.comp_embedding e.toEmbedding, ?_⟩
  rw [e.surjective.range_comp (fun i : ↥I => v i.val), hFEq]
  congr 1
  ext x
  constructor
  · rintro ⟨i, hiI, rfl⟩
    exact ⟨⟨i, hiI⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, i.property, rfl⟩

/-- Every `k`-dimensional exposed face of a `d`-simplex corresponds bijectively to a
`(k + 1)`-element subset of `Fin (d + 1)`, so `faceCount` equals `Nat.choose (d + 1) (k + 1)`. -/
theorem simplex_faceCount_eq_choose (d : ℕ) (v : Fin (d + 1) → Fin d → ℝ)
    (hv : AffineIndependent ℝ v) (k : ℕ) :
    faceCount (convexHull ℝ (Set.range v)) k = Nat.choose (d + 1) (k + 1) := by
  let P := convexHull ℝ (Set.range v)
  let S : Set (Set (Fin d → ℝ)) :=
    {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
      Module.finrank ℝ (affineSpan ℝ F).direction = k}
  let T : Finset (Finset (Fin (d + 1))) :=
    (Finset.univ : Finset (Fin (d + 1))).powersetCard (k + 1)
  let f : Finset (Fin (d + 1)) → Set (Fin d → ℝ) :=
    fun I => convexHull ℝ (v '' (I : Set (Fin (d + 1))))
  have hfInjOn : Set.InjOn f (T : Set (Finset (Fin (d + 1)))) := by
    intro I _ J _ hIJ
    change convexHull ℝ (v '' (I : Set (Fin (d + 1)))) =
      convexHull ℝ (v '' (J : Set (Fin (d + 1)))) at hIJ
    ext j
    rw [← (simplex_subset_hull_isExposed_and_labels d v hv I).2 j,
      ← (simplex_subset_hull_isExposed_and_labels d v hv J).2 j, hIJ]
  have hfImage : f '' (T : Set (Finset (Fin (d + 1)))) = S := by
    ext F
    constructor
    · rintro ⟨I, hIT, rfl⟩
      have hCard : I.card = k + 1 :=
        (Finset.mem_powersetCard.mp (Finset.mem_coe.mp hIT)).2
      have hIne : I.Nonempty := Finset.card_pos.mp (by omega)
      have hFne : (f I).Nonempty := by
        obtain ⟨j, hj⟩ := hIne
        exact ⟨v j, subset_convexHull ℝ _ ⟨j, Finset.mem_coe.mpr hj, rfl⟩⟩
      have hFexp : IsExposed ℝ P (f I) :=
        (simplex_subset_hull_isExposed_and_labels d v hv I).1
      have hRankAdd : Module.finrank ℝ (affineSpan ℝ (f I)).direction + 1 = I.card :=
        simplex_subset_hull_finrank_add_one d v hv I hIne
      exact ⟨hFne, hFexp, by omega⟩
    · rintro ⟨hFne, hFexp, hRank⟩
      let I : Finset (Fin (d + 1)) := Finset.univ.filter (fun j => v j ∈ F)
      have hFEq : F = f I := simplex_exposedFace_eq_subset_hull d v hFexp
      have hIne : I.Nonempty := by
        have hh : (f I).Nonempty := hFEq ▸ hFne
        obtain ⟨_, j, hj, rfl⟩ := convexHull_nonempty_iff.mp hh
        exact ⟨j, Finset.mem_coe.mp hj⟩
      have hRankAdd : Module.finrank ℝ (affineSpan ℝ (f I)).direction + 1 = I.card :=
        simplex_subset_hull_finrank_add_one d v hv I hIne
      rw [← hFEq] at hRankAdd
      have hCard : I.card = k + 1 := by omega
      have hIT : I ∈ (T : Set (Finset (Fin (d + 1)))) :=
        Finset.mem_coe.mpr (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ I, hCard⟩)
      exact ⟨I, hIT, hFEq.symm⟩
  change S.ncard = Nat.choose (d + 1) (k + 1)
  rw [← hfImage, Set.InjOn.ncard_image hfInjOn, Set.ncard_coe_finset]
  simp only [T, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- Standard `d`-simplex vertices in `ℝ^d`: vertex `0` is the origin and vertex `i.succ`
is the `i`-th standard basis vector `Pi.single i 1`. -/
def stdSimplexVertices (d : ℕ) : Fin (d + 1) → Fin d → ℝ :=
  Fin.cases 0 (fun i => Pi.single i 1)

theorem stdSimplexVertices_affineIndependent (d : ℕ) :
    AffineIndependent ℝ (stdSimplexVertices d) := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ (stdSimplexVertices d) 0]
  apply (linearIndependent_equiv (finSuccAboveEquiv (0 : Fin (d + 1)))).mp
  have hEq :
      ((fun i : {x : Fin (d + 1) // x ≠ 0} =>
          stdSimplexVertices d i -ᵥ stdSimplexVertices d 0) ∘
        ⇑(finSuccAboveEquiv (0 : Fin (d + 1)))) =
      ⇑(Pi.basisFun ℝ (Fin d)) := by
    funext k
    simp only [Function.comp_apply, finSuccAboveEquiv_apply, Fin.succAbove_zero,
      stdSimplexVertices, Fin.cases_zero, Fin.cases_succ, vsub_eq_sub, sub_zero,
      Pi.basisFun_apply]
  rw [hEq]
  exact (Pi.basisFun ℝ (Fin d)).linearIndependent

/-- In every dimension `d`, the standard `d`-simplex is a simplicial `d`-polytope
whose `k`-face count is `Nat.choose (d + 1) (k + 1)` for all `k`. -/
theorem exists_simplicial_simplex_with_choose_faceCounts (d : ℕ) :
    ∃ P : Set (Fin d → ℝ),
      IsSimplicialDPolytope P ∧
      ∀ k : ℕ, faceCount P k = Nat.choose (d + 1) (k + 1) := by
  refine ⟨convexHull ℝ (Set.range (stdSimplexVertices d)),
    simplex_isSimplicialDPolytope d (stdSimplexVertices d) (stdSimplexVertices_affineIndependent d),
    simplex_faceCount_eq_choose d (stdSimplexVertices d) (stdSimplexVertices_affineIndependent d)⟩

end Grunbaum2003

namespace Grunbaum2003

theorem exposed_edge_pair_and_simplex_faceCount_choose_proved :
  (∀ {d : ℕ} {P : Set (Fin d → ℝ)},
    ({x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) →
    ∀ (F : Set (Fin d → ℝ)), IsExposed ℝ P F →
      ((F.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F).direction = 1) ↔
        ∃ a b : Fin d → ℝ,
          IsExposed ℝ P {a} ∧ IsExposed ℝ P {b} ∧ a ≠ b ∧
          F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} = {a, b} ∧
          F = convexHull ℝ ({a, b} : Set (Fin d → ℝ)))) ∧
  (∀ P : Set (Fin 2 → ℝ), IsSimplicialDPolytope P ↔ IsDPolytope P) ∧
  (∀ (d : ℕ) (v : Fin (d + 1) → Fin d → ℝ),
    AffineIndependent ℝ v →
    IsSimplicialDPolytope (convexHull ℝ (Set.range v)) ∧
    ∀ k : ℕ, faceCount (convexHull ℝ (Set.range v)) k = Nat.choose (d + 1) (k + 1)) ∧
  (∀ d : ℕ,
    ∃ P : Set (Fin d → ℝ),
      IsSimplicialDPolytope P ∧
      ∀ k : ℕ, faceCount P k = Nat.choose (d + 1) (k + 1)) := by
  refine ⟨?_, ?_, ?_, exists_simplicial_simplex_with_choose_faceCounts⟩
  · intro d P hHull F hF
    exact nonempty_exposed_finrank_one_iff_exposed_pair hHull F hF
  · intro P
    constructor
    · exact fun h => h.1
    · intro hP
      exact (isSimplicialDPolytope_two_iff_isDPolytope P
        (polytope_face_eq_convexHull_exposed_vertices 2 P hP)).mpr hP
  · intro d v hv
    exact ⟨simplex_isSimplicialDPolytope d v hv, simplex_faceCount_eq_choose d v hv⟩

end Grunbaum2003

end

open Grunbaum2003 in
theorem solution :
  (∀ {d : ℕ} {P : Set (Fin d → ℝ)},
    ({x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) →
    ∀ (F : Set (Fin d → ℝ)), IsExposed ℝ P F →
      ((F.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F).direction = 1) ↔
        ∃ a b : Fin d → ℝ,
          IsExposed ℝ P {a} ∧ IsExposed ℝ P {b} ∧ a ≠ b ∧
          F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} = {a, b} ∧
          F = convexHull ℝ ({a, b} : Set (Fin d → ℝ)))) ∧
  (∀ P : Set (Fin 2 → ℝ), IsSimplicialDPolytope P ↔ IsDPolytope P) ∧
  (∀ (d : ℕ) (v : Fin (d + 1) → Fin d → ℝ),
    AffineIndependent ℝ v →
    IsSimplicialDPolytope (convexHull ℝ (Set.range v)) ∧
    ∀ k : ℕ, faceCount (convexHull ℝ (Set.range v)) k = Nat.choose (d + 1) (k + 1)) ∧
  (∀ d : ℕ,
    ∃ P : Set (Fin d → ℝ),
      IsSimplicialDPolytope P ∧
      ∀ k : ℕ, faceCount P k = Nat.choose (d + 1) (k + 1)) :=
  Grunbaum2003.exposed_edge_pair_and_simplex_faceCount_choose_proved
