-- Prove2me | solution 1 for Grunbaum2003.exists_stellar_subdivision_cone_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T07:41:46.34734+00:00
-- url     : https://prove2.me/submissions/907c869f-71f6-437f-943c-2817bf9f1ac5

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith
import Definitions.Def_Grunbaum2003_IsDPolytope
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

-- BEGIN StellarCone.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.StellarCone

/-- Adding a point outside the common support plane of an independent family
preserves affine independence. -/
theorem affineIndependent_cons {d n : ℕ} (v : Fin n → Fin d → ℝ)
    (hv : AffineIndependent ℝ v) (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (hlevel : ∀ i, φ (v i) = a) (y : Fin d → ℝ) (hy : a < φ y) :
    AffineIndependent ℝ (Fin.cons (α := fun _ => Fin d → ℝ) y v) := by
  let e : {i : Fin (n + 1) // i ≠ 0} ↪ Fin n :=
    ⟨fun i => i.val.pred i.property, fun i j h => Subtype.ext (Fin.pred_inj.mp h)⟩
  have hbase : AffineIndependent ℝ
      (fun i : {i : Fin (n + 1) // i ≠ 0} =>
        (Fin.cons (α := fun _ => Fin d → ℝ) y v : Fin (n + 1) → Fin d → ℝ) i.val) := by
    have heq : (fun i : {i : Fin (n + 1) // i ≠ 0} =>
        (Fin.cons (α := fun _ => Fin d → ℝ) y v : Fin (n + 1) → Fin d → ℝ) i.val) = v ∘ e := by
      funext i
      change Fin.cons (α := fun _ => Fin d → ℝ) y v i.val = v (i.val.pred i.property)
      conv_lhs => rw [← Fin.succ_pred i.val i.property]
      rfl
    rw [heq]
    exact hv.comp_embedding e
  apply hbase.affineIndependent_of_notMem_span
  let H : AffineSubspace ℝ (Fin d → ℝ) :=
    (affineSpan ℝ ({a} : Set ℝ)).comap φ.toLinearMap.toAffineMap
  have hH : (Fin.cons (α := fun _ => Fin d → ℝ) y v) '' {i : Fin (n + 1) | i ≠ 0} ⊆ H := by
    rintro x ⟨i, hi, rfl⟩
    have hval : φ (Fin.cons (α := fun _ => Fin d → ℝ) y v i) = a := by
      rw [← Fin.succ_pred i hi]
      exact hlevel _
    simpa [H, AffineSubspace.mem_comap] using hval
  intro hmem
  have hspan := (affineSpan_le_of_subset_coe hH) hmem
  have heq : φ y = a := by simpa [H, AffineSubspace.mem_comap] using hspan
  exact hy.ne heq.symm

/-- Every cone over a subset of the base vertices is a simplex of the expected size. -/
theorem cone_simplex {d n : ℕ} (v : Fin n → Fin d → ℝ)
    (hv : AffineIndependent ℝ v) (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (hlevel : ∀ i, φ (v i) = a) (y : Fin d → ℝ) (hy : a < φ y)
    (s : Finset (Fin n)) :
    ∃ w : Fin (s.card + 1) → Fin d → ℝ,
      AffineIndependent ℝ w ∧
        convexHull ℝ (insert y (v '' (s : Set (Fin n)))) = convexHull ℝ (Set.range w) := by
  let e : Fin s.card ≃ ↥s := Fintype.equivOfCardEq (by simp)
  let q : Fin s.card → Fin d → ℝ := fun i => v (e i).val
  have hq : AffineIndependent ℝ q :=
    (hv.comp_embedding ⟨Subtype.val, Subtype.val_injective⟩).comp_embedding e.toEmbedding
  have hqr : Set.range q = v '' (s : Set (Fin n)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(e i).val, (e i).property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
      exact ⟨j, by simp [q, hj]⟩
  refine ⟨Fin.cons y q, affineIndependent_cons q hq φ a (fun i => hlevel _) y hy, ?_⟩
  rw [Fin.range_cons, hqr]

/-- The cone over `s` has affine dimension exactly `s.card`, including the empty base. -/
theorem cone_finrank {d n : ℕ} (v : Fin n → Fin d → ℝ)
    (hv : AffineIndependent ℝ v) (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (hlevel : ∀ i, φ (v i) = a) (y : Fin d → ℝ) (hy : a < φ y)
    (s : Finset (Fin n)) :
    Module.finrank ℝ (affineSpan ℝ
      (convexHull ℝ (insert y (v '' (s : Set (Fin n)))))).direction = s.card := by
  obtain ⟨w, hw, heq⟩ := cone_simplex v hv φ a hlevel y hy s
  rw [heq, affineSpan_convexHull, direction_affineSpan]
  exact hw.finrank_vectorSpan (Fintype.card_fin _)

/-- Nonempty subsets of an independent family have one fewer affine dimension than points. -/
theorem subset_finrank {d n : ℕ} (v : Fin n → Fin d → ℝ)
    (hv : AffineIndependent ℝ v) (s : Finset (Fin n)) (hs : s.Nonempty) :
    Module.finrank ℝ (affineSpan ℝ (convexHull ℝ (v '' (s : Set (Fin n))))).direction + 1 =
      s.card := by
  have : Nonempty ↥s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  have hi : AffineIndependent ℝ (fun i : ↥s => v i.val) :=
    hv.comp_embedding (⟨Subtype.val, Subtype.val_injective⟩ : ↥s ↪ Fin n)
  have hrange : Set.range (fun i : ↥s => v i.val) = v '' (s : Set (Fin n)) := by
    ext x
    simp
  rw [affineSpan_convexHull, direction_affineSpan, ← hrange]
  simpa only [Fintype.card_coe] using hi.finrank_vectorSpan_add_one


/-- An apex strictly beyond a supporting hyperplane adds no points of the old
convex set to a cone over a subset of that hyperplane. -/
theorem convexHull_insert_inter_eq_of_supporting {d : ℕ}
    {P A : Set (Fin d → ℝ)} (hP : Convex ℝ P) (hAP : A ⊆ P)
    (φ : (Fin d → ℝ) →ₗ[ℝ] ℝ) (c : ℝ)
    (hbound : ∀ x ∈ P, φ x ≤ c) (hlevel : ∀ x ∈ A, φ x = c)
    (y : Fin d → ℝ) (hy : c < φ y) :
    convexHull ℝ (insert y A) ∩ P = convexHull ℝ A := by
  have hyP : y ∉ P := fun h => (not_le_of_gt hy) (hbound y h)
  have hsub : convexHull ℝ A ⊆ P := convexHull_min hAP hP
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hA : A.Nonempty
    · have hconst : ∀ z ∈ convexHull ℝ A, φ z = c := by
        exact convexHull_min hlevel ((convex_singleton c).linear_preimage φ)
      rcases hx with ⟨hx, hxP⟩
      rw [convexHull_insert hA, mem_convexJoin] at hx
      rcases hx with ⟨y', hy', z, hz, a, b, ha, hb, hab, hx⟩
      obtain rfl : y' = y := hy'
      subst x
      have hφ := hbound _ hxP
      simp only [map_add, map_smul, smul_eq_mul, hconst z hz] at hφ
      have ha0 : a = 0 := by
        apply le_antisymm _ ha
        by_contra! hapos
        nlinarith [mul_pos hapos (sub_pos.mpr hy), congrArg (fun t : ℝ => t * c) hab]
      have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using hz
    · have hA0 : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
      have hxy : x = y := by simpa [hA0] using hx.1
      exact False.elim (hyP (hxy ▸ hx.2))
  · intro x hx
    exact ⟨convexHull_mono (Set.subset_insert y A) hx, hsub hx⟩

/-- The cone over selected old exposed vertices has exactly those old exposed
vertices when the apex lies strictly beyond their supporting hyperplane. -/
theorem stellarCone_old_exposed_vertices_of_supporting {d : ℕ}
    {P : Set (Fin d → ℝ)} (hP : Convex ℝ P)
    (v : Fin d → Fin d → ℝ)
    (hv : ∀ i, IsExposed ℝ P {v i})
    (φ : (Fin d → ℝ) →ₗ[ℝ] ℝ) (c : ℝ)
    (hbound : ∀ x ∈ P, φ x ≤ c) (hlevel : ∀ i, φ (v i) = c)
    (y : Fin d → ℝ) (hy : c < φ y) (s : Finset (Fin d)) :
    convexHull ℝ (insert y (v '' (s : Set (Fin d)))) ∩
      {x : Fin d → ℝ | IsExposed ℝ P {x}} = v '' (s : Set (Fin d)) := by
  have hAP : v '' (s : Set (Fin d)) ⊆ P := by
    rintro _ ⟨i, _, rfl⟩
    exact (hv i).subset (Set.mem_singleton _)
  have hconv := convexHull_insert_inter_eq_of_supporting hP hAP φ c hbound
    (by rintro _ ⟨i, _, rfl⟩; exact hlevel i) y hy
  apply Set.Subset.antisymm
  · intro x hx
    have hxP := hx.2.subset (Set.mem_singleton _)
    have hxHull : x ∈ convexHull ℝ (v '' (s : Set (Fin d))) := by
      rw [← hconv]
      exact ⟨hx.1, hxP⟩
    exact extremePoints_convexHull_subset
      (inter_extremePoints_subset_extremePoints_of_subset
        (convexHull_min hAP hP) ⟨hxHull, hx.2.isExtreme.mem_extremePoints⟩)
  · rintro _ ⟨i, hi, rfl⟩
    exact ⟨subset_convexHull ℝ _ (Set.mem_insert_of_mem _ ⟨i, hi, rfl⟩), hv i⟩


end Grunbaum2003.StellarCone
-- END StellarCone.lean

-- BEGIN StellarFaceTools.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.StellarFaceTools

/-- Any exposed face of a finite hull is the hull of its incident input points. -/
theorem finite_face_hull {d : ℕ} {ι : Type*} [Finite ι]
    (v : ι → Fin d → ℝ) {F : Set (Fin d → ℝ)}
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
theorem finite_face_of_support {d : ℕ} {ι : Type*} [Finite ι]
    (v : ι → Fin d → ℝ) (s : Set (ι)) (hs : s.Nonempty)
    (l : (Fin d → ℝ) →L[ℝ] ℝ) (b : ℝ)
    (hbound : ∀ i : ι, l (v i) ≤ b)
    (heq : ∀ i : ι, l (v i) = b ↔ i ∈ s) :
    IsExposed ℝ (convexHull ℝ (Set.range v)) (convexHull ℝ (v '' s)) ∧
      ∀ i : ι, v i ∈ convexHull ℝ (v '' s) ↔ i ∈ s := by
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
  have hFlabels : ∀ i : ι, v i ∈ F ↔ i ∈ s := by
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
          finite_face_hull v
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
  apply finite_face_of_support v (I : Set (Fin (d + 1)))
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

theorem isExposed_trans_polytope (d : ℕ) (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (F G : Set (Fin d → ℝ)) (hF : IsExposed ℝ P F) (hG : IsExposed ℝ F G) :
    IsExposed ℝ P G := by
  classical
  by_cases hEmpty : G = ∅
  · rw [hEmpty]
    exact isExposed_empty
  obtain ⟨z, hzG⟩ := Set.nonempty_iff_ne_empty.mpr hEmpty
  have hzF : z ∈ F := hG.subset hzG
  have hzP : z ∈ P := hF.subset hzF
  obtain ⟨l, hFl⟩ := hF ⟨z, hzF⟩
  obtain ⟨m, hGm⟩ := hG ⟨z, hzG⟩
  have hlMax : ∀ x ∈ P, l x ≤ l z := by
    have hz := hzF
    rw [hFl] at hz
    exact hz.2
  have hmMax : ∀ x ∈ F, m x ≤ m z := by
    have hz := hzG
    rw [hGm] at hz
    exact hz.2
  have hFlevel (x : Fin d → ℝ) (hxP : x ∈ P) : x ∈ F ↔ l x = l z := by
    constructor
    · intro hxF
      rw [hFl] at hxF
      exact le_antisymm (hlMax x hxP) (hxF.2 z hzP)
    · intro hxEq
      rw [hFl]
      exact ⟨hxP, fun y hy => by rw [hxEq]; exact hlMax y hy⟩
  have hGlevel (x : Fin d → ℝ) (hxF : x ∈ F) : x ∈ G ↔ m x = m z := by
    constructor
    · intro hxG
      rw [hGm] at hxG
      exact le_antisymm (hmMax x hxF) (hxG.2 z hzF)
    · intro hxEq
      rw [hGm]
      exact ⟨hxF, fun y hy => by rw [hxEq]; exact hmMax y hy⟩
  obtain ⟨V, hVfin, _, hPgen⟩ := hP.1
  have hVP : V ⊆ P := by
    rw [hPgen]
    exact subset_convexHull ℝ V
  have hFaces (K : Set (Fin d → ℝ)) (hK : IsExposed ℝ P K) :
      K = convexHull ℝ (K ∩ V) := by
    have : Finite V := hVfin.to_subtype
    have hr : Set.range (fun i : V => i.val) = V := Subtype.range_coe
    rw [hPgen, ← hr] at hK
    simpa only [hr] using finite_face_hull (fun i : V => i.val) hK
  have hPconv : Convex ℝ P := hPgen ▸ convex_convexHull ℝ V
  let r : (Fin d → ℝ) → ℝ := fun w => (m w - m z) / (l z - l w)
  obtain ⟨M, hM⟩ := ((hVfin.image r).insert 0).bddAbove
  let C : ℝ := M + 1
  let n : StrongDual ℝ (Fin d → ℝ) := C • l + m
  have hStrict (w : Fin d → ℝ) (hwV : w ∈ V) (hwF : w ∉ F) : n w < n z := by
    have hwP : w ∈ P := hVP hwV
    have hlw : l w < l z := lt_of_le_of_ne (hlMax w hwP) (fun h => hwF ((hFlevel w hwP).mpr h))
    have hDen : 0 < l z - l w := sub_pos.mpr hlw
    have hRatio : r w < C := lt_of_le_of_lt (hM (Set.mem_insert_of_mem 0 ⟨w, hwV, rfl⟩)) (by dsimp [C]; linarith)
    have hNum : m w - m z < C * (l z - l w) := (div_lt_iff₀ hDen).mp hRatio
    change C * l w + m w < C * l z + m z
    nlinarith [hNum]
  have hGen (w : Fin d → ℝ) (hwV : w ∈ V) : n w ≤ n z := by
    by_cases hwF : w ∈ F
    · change C * l w + m w ≤ C * l z + m z
      rw [(hFlevel w (hVP hwV)).mp hwF]
      exact add_le_add le_rfl (hmMax w hwF)
    · exact (hStrict w hwV hwF).le
  have hnMax : ∀ x ∈ P, n x ≤ n z := by
    rw [hPgen]
    apply convexHull_min hGen
    intro x hx y hy a b ha hb hab
    change n (a • x + b • y) ≤ n z
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    calc
      a * n x + b * n y ≤ a * n z + b * n z :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
      _ = n z := by rw [← add_mul, hab, one_mul]
  let K := {x ∈ P | n x = n z}
  have hK : IsExposed ℝ P K := by
    intro _
    refine ⟨n, ?_⟩
    ext x
    constructor
    · rintro ⟨hxP, hxEq⟩
      exact ⟨hxP, fun y hy => (hnMax y hy).trans_eq hxEq.symm⟩
    · rintro ⟨hxP, hxMax⟩
      exact ⟨hxP, le_antisymm (hnMax x hxP) (hxMax z hzP)⟩
  have hKsubG : K ⊆ G := by
    have hHullK := hFaces K hK
    change K = convexHull ℝ (K ∩ V) at hHullK
    rw [hHullK]
    apply convexHull_min ?_ (hG.convex (hF.convex hPconv))
    rintro w ⟨hwK, hwV⟩
    have hwF : w ∈ F := by
      by_contra hnF
      exact (hStrict w hwV hnF).ne hwK.2
    apply (hGlevel w hwF).mpr
    have hEq : C * l w + m w = C * l z + m z := hwK.2
    rw [(hFlevel w hwK.1).mp hwF] at hEq
    linarith
  have hGsubK : G ⊆ K := by
    intro x hxG
    have hxF : x ∈ F := hG.subset hxG
    have hxP : x ∈ P := hF.subset hxF
    refine ⟨hxP, ?_⟩
    change C * l x + m x = C * l z + m z
    rw [(hFlevel x hxP).mp hxF, (hGlevel x hxF).mp hxG]
  have hKG : K = G := Set.Subset.antisymm hKsubG hGsubK
  rwa [hKG] at hK


end Grunbaum2003.StellarFaceTools
-- END StellarFaceTools.lean

-- BEGIN StellarPyramidGeometry.lean
set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003

/-- An apex beyond one supporting plane and beneath every other plane adds
exactly the pyramid over the chosen face. The family of other planes may be infinite. -/
theorem convexHull_insert_eq_union_pyramid
    {d : ℕ} {ι : Type*} (P : Set (Fin d → ℝ))
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (ψ : ι → (Fin d → ℝ) →L[ℝ] ℝ) (c : ι → ℝ)
    (hP : P = {x | φ x ≤ a ∧ ∀ j, ψ j x ≤ c j})
    (hPne : P.Nonempty) (y : Fin d → ℝ)
    (hyφ : a < φ y) (hyψ : ∀ j, ψ j y ≤ c j) :
    convexHull ℝ (insert y P) =
      P ∪ convexHull ℝ (insert y {x ∈ P | φ x = a}) := by
  have hmem (x : Fin d → ℝ) : x ∈ P ↔ φ x ≤ a ∧ ∀ j, ψ j x ≤ c j := by
    rw [hP]
    rfl
  have hconv : Convex ℝ P := by
    intro x hx z hz u v hu hv huv
    rw [hmem] at hx hz ⊢
    constructor
    · simp only [map_add, map_smul, smul_eq_mul]
      calc
        u * φ x + v * φ z ≤ u * a + v * a :=
          add_le_add (mul_le_mul_of_nonneg_left hx.1 hu)
            (mul_le_mul_of_nonneg_left hz.1 hv)
        _ = a := by rw [← add_mul, huv, one_mul]
    · intro j
      simp only [map_add, map_smul, smul_eq_mul]
      calc
        u * ψ j x + v * ψ j z ≤ u * c j + v * c j :=
          add_le_add (mul_le_mul_of_nonneg_left (hx.2 j) hu)
            (mul_le_mul_of_nonneg_left (hz.2 j) hv)
        _ = c j := by rw [← add_mul, huv, one_mul]
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hxP : x ∈ P
    · exact Or.inl hxP
    right
    rw [convexHull_insert hPne, hconv.convexHull_eq, mem_convexJoin] at hx
    obtain ⟨y', hy', z, hz, u, v, hu, hv, huv, hrep⟩ := hx
    have heqy : y' = y := hy'
    subst y'
    have hzφ := ((hmem z).mp hz).1
    have hzψ := ((hmem z).mp hz).2
    have hxψ (j : ι) : ψ j x ≤ c j := by
      rw [← hrep]
      simp only [map_add, map_smul, smul_eq_mul]
      calc
        u * ψ j y + v * ψ j z ≤ u * c j + v * c j :=
          add_le_add (mul_le_mul_of_nonneg_left (hyψ j) hu)
            (mul_le_mul_of_nonneg_left (hzψ j) hv)
        _ = c j := by rw [← add_mul, huv, one_mul]
    have hxφ : a < φ x := by
      by_contra! h
      exact hxP ((hmem x).mpr ⟨h, hxψ⟩)
    have hD : 0 < φ y - φ z := by linarith
    have hD0 : φ y - φ z ≠ 0 := ne_of_gt hD
    let r : ℝ := (a - φ z) / (φ y - φ z)
    let s : ℝ := (φ y - a) / (φ y - φ z)
    have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr hzφ) hD.le
    have hs : 0 < s := div_pos (sub_pos.mpr hyφ) hD
    have hrs : r + s = 1 := by
      dsimp [r, s]
      field_simp
      ring
    let w : Fin d → ℝ := r • y + s • z
    have hwφ : φ w = a := by
      dsimp [w]
      simp only [map_add, map_smul, smul_eq_mul]
      dsimp [r, s]
      field_simp
      ring
    have hwψ (j : ι) : ψ j w ≤ c j := by
      dsimp [w]
      simp only [map_add, map_smul, smul_eq_mul]
      calc
        r * ψ j y + s * ψ j z ≤ r * c j + s * c j :=
          add_le_add (mul_le_mul_of_nonneg_left (hyψ j) hr)
            (mul_le_mul_of_nonneg_left (hzψ j) hs.le)
        _ = c j := by rw [← add_mul, hrs, one_mul]
    have hw : w ∈ {x ∈ P | φ x = a} :=
      ⟨(hmem w).mpr ⟨hwφ.le, hwψ⟩, hwφ⟩
    have hvle : v ≤ s := by
      apply (le_div_iff₀ hD).mpr
      have hval := congrArg φ hrep
      simp only [map_add, map_smul, smul_eq_mul] at hval
      nlinarith [congrArg (fun q : ℝ => q * φ y) huv]
    have hvs : 0 ≤ v / s := div_nonneg hv hs.le
    have hvs1 : v / s ≤ 1 := (div_le_one hs).mpr hvle
    have hwHull : w ∈ convexHull ℝ (insert y {x ∈ P | φ x = a}) :=
      subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hw)
    have hyHull : y ∈ convexHull ℝ (insert y {x ∈ P | φ x = a}) :=
      subset_convexHull ℝ _ (Set.mem_insert _ _)
    have heq : (1 - v / s) • y + (v / s) • w = x := by
      rw [← hrep]
      dsimp [w]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hs0 : s ≠ 0 := ne_of_gt hs
      field_simp
      nlinarith [congrArg (fun q : ℝ => q * (v * y i)) hrs,
        congrArg (fun q : ℝ => q * (s * y i)) huv]
    rw [← heq]
    exact (convex_convexHull ℝ _) hyHull hwHull
      (sub_nonneg.mpr hvs1) hvs (by ring)
  · rintro x (hx | hx)
    · exact subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hx)
    · exact convexHull_mono (by
        intro z hz
        rcases hz with rfl | hz
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ hz.1) hx

end Grunbaum2003



set_option autoImplicit false
open scoped Classical Topology

namespace Grunbaum2003

/-- A proper supporting plane through an apex that violates only one of finitely
many defining inequalities meets the old polytope only in that chosen facet. -/
theorem support_through_apex_meets_chosen_face
    {d : ℕ} {ι : Type*} [Finite ι] (P : Set (Fin d → ℝ))
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (ψ : ι → (Fin d → ℝ) →L[ℝ] ℝ) (c : ι → ℝ)
    (hP : P = {x | φ x ≤ a ∧ ∀ j, ψ j x ≤ c j})
    (y : Fin d → ℝ) (hyφ : a < φ y) (hyψ : ∀ j, ψ j y < c j)
    (θ : (Fin d → ℝ) →L[ℝ] ℝ) (hθ : θ ≠ 0)
    (hmax : ∀ x ∈ P, θ x ≤ θ y) :
    ∀ x ∈ P, θ x = θ y → φ x = a := by
  intro x hx hθx
  have hxmem : φ x ≤ a ∧ ∀ j, ψ j x ≤ c j := by simpa [hP] using hx
  by_contra hxa
  have hxφ : φ x < a := lt_of_le_of_ne hxmem.1 hxa
  have hD : 0 < φ y - φ x := by linarith
  have hD0 : φ y - φ x ≠ 0 := ne_of_gt hD
  let s : ℝ := (a - φ x) / (2 * (φ y - φ x))
  have hs : 0 < s := div_pos (sub_pos.mpr hxφ) (by positivity)
  have hs1 : s < 1 := by
    apply (div_lt_one (by positivity : 0 < 2 * (φ y - φ x))).mpr
    linarith
  have hsD : s * (φ y - φ x) = (a - φ x) / 2 := by
    dsimp [s]
    field_simp
  let q : Fin d → ℝ := s • y + (1 - s) • x
  have hqφ : φ q < a := by
    dsimp [q]
    simp only [map_add, map_smul, smul_eq_mul]
    nlinarith [hsD]
  have hqψ (j : ι) : ψ j q < c j := by
    dsimp [q]
    simp only [map_add, map_smul, smul_eq_mul]
    calc
      s * ψ j y + (1 - s) * ψ j x < s * c j + (1 - s) * c j :=
        add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (hyψ j) hs)
          (mul_le_mul_of_nonneg_left (hxmem.2 j) (by linarith))
      _ = c j := by ring
  have hqθ : θ q = θ y := by
    dsimp [q]
    simp only [map_add, map_smul, smul_eq_mul, hθx]
    ring
  let U : Set (Fin d → ℝ) := {z | φ z < a ∧ ∀ j, ψ j z < c j}
  have hU : IsOpen U := by
    have hUeq : U = {z | φ z < a} ∩ ⋂ j, {z | ψ j z < c j} := by
      ext z
      simp [U]
    rw [hUeq]
    exact (isOpen_lt φ.continuous continuous_const).inter
      (isOpen_iInter_of_finite (fun j => isOpen_lt (ψ j).continuous continuous_const))
  have hqU : q ∈ U := ⟨hqφ, hqψ⟩
  have hmaxq : IsLocalMax (fun z => θ z) q := by
    filter_upwards [hU.mem_nhds hqU] with z hz
    have hzP : z ∈ P := by
      rw [hP]
      exact ⟨hz.1.le, fun j => (hz.2 j).le⟩
    simpa only [hqθ] using hmax z hzP
  exact hθ (hmaxq.hasFDerivAt_eq_zero θ.hasFDerivAt)

end Grunbaum2003


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

namespace Grunbaum2003

/-- Every new nonempty proper exposed face is an old face, the apex, or a cone
whose base is an old exposed face contained in the chosen supporting plane. -/
theorem exposed_faces_of_pyramid_extension
    {d : ℕ} {ι : Type*} [Finite ι] (P : Set (Fin d → ℝ))
    (hconv : Convex ℝ P) (hcompact : IsCompact P) (hPne : P.Nonempty)
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (ψ : ι → (Fin d → ℝ) →L[ℝ] ℝ) (c : ι → ℝ)
    (hP : P = {x | φ x ≤ a ∧ ∀ j, ψ j x ≤ c j})
    (y : Fin d → ℝ) (hyφ : a < φ y) (hyψ : ∀ j, ψ j y < c j)
    (H : Set (Fin d → ℝ)) (hHne : H.Nonempty)
    (hH : IsExposed ℝ (convexHull ℝ (insert y P)) H)
    (hproper : H ≠ convexHull ℝ (insert y P)) :
    H = {y} ∨ IsExposed ℝ P H ∨
      ∃ G : Set (Fin d → ℝ), G.Nonempty ∧ IsExposed ℝ P G ∧
        G ⊆ {x ∈ P | φ x = a} ∧ H = convexHull ℝ (insert y G) := by
  obtain ⟨θ, hθH⟩ := hH hHne
  change H = θ.toExposed (convexHull ℝ (insert y P)) at hθH
  have hθ : θ ≠ 0 := by
    intro hz
    apply hproper
    simpa [hz, ContinuousLinearMap.toExposed] using hθH
  obtain ⟨w, hw, hmaxOn⟩ := hcompact.exists_isMaxOn hPne θ.continuous.continuousOn
  have hmax : ∀ x ∈ P, θ x ≤ θ w := fun _ hx => hmaxOn hx
  have hsplit := exposed_insert_trichotomy hconv θ w hw hmax y
  rcases lt_trichotomy (θ y) (θ w) with hlt | heq | hgt
  · right; left
    rw [hθH, hsplit.1 hlt]
    exact ContinuousLinearMap.toExposed.isExposed (l := θ)
  · right; right
    refine ⟨θ.toExposed P, ⟨w, hw, hmax⟩,
      ContinuousLinearMap.toExposed.isExposed (l := θ), ?_, hθH.trans (hsplit.2.1 heq)⟩
    intro x hx
    have hmax' : ∀ z ∈ P, θ z ≤ θ y := by simpa only [heq] using hmax
    have hxθ : θ x = θ y := (le_antisymm (hmax x hx.1) (hx.2 w hw)).trans heq.symm
    exact ⟨hx.1, support_through_apex_meets_chosen_face P φ a ψ c hP y hyφ hyψ θ hθ
      hmax' x hx.1 hxθ⟩
  · exact Or.inl (hθH.trans (hsplit.2.2 hgt))

/-- Tilting an old support functional by the chosen facet normal exposes the
cone over every base face whose old support plane strictly separates the apex. -/
theorem cone_exposed_of_support_below_apex
    {d : ℕ} {P : Set (Fin d → ℝ)} (hconv : Convex ℝ P)
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ) (hφ : ∀ x ∈ P, φ x ≤ a)
    (ℓ : (Fin d → ℝ) →L[ℝ] ℝ) (w : Fin d → ℝ) (hw : w ∈ P)
    (hmax : ∀ x ∈ P, ℓ x ≤ ℓ w)
    (hface : ℓ.toExposed P ⊆ {x | φ x = a})
    (y : Fin d → ℝ) (hyφ : a < φ y) (hyℓ : ℓ y < ℓ w) :
    IsExposed ℝ (convexHull ℝ (insert y P))
      (convexHull ℝ (insert y (ℓ.toExposed P))) := by
  let t : ℝ := (ℓ w - ℓ y) / (φ y - a)
  have ht : 0 < t := div_pos (sub_pos.mpr hyℓ) (sub_pos.mpr hyφ)
  have htD : t * (φ y - a) = ℓ w - ℓ y :=
    div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hyφ))
  let θ : (Fin d → ℝ) →L[ℝ] ℝ := ℓ + t • φ
  have hwφ : φ w = a := hface ⟨hw, hmax⟩
  have hθw : θ w = ℓ w + t * a := by simp [θ, hwφ]
  have hθmax : ∀ x ∈ P, θ x ≤ θ w := by
    intro x hx
    simp only [θ, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hwφ]
    exact add_le_add (hmax x hx) (mul_le_mul_of_nonneg_left (hφ x hx) ht.le)
  have hθy : θ y = θ w := by
    simp only [θ, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hwφ]
    nlinarith [htD]
  have hfaces : θ.toExposed P = ℓ.toExposed P := by
    rw [exposed_eq_level θ hw hθmax, exposed_eq_level ℓ hw hmax]
    ext x
    constructor
    · rintro ⟨hx, hxθ⟩
      refine ⟨hx, ?_⟩
      have hnonneg := mul_nonneg ht.le (sub_nonneg.mpr (hφ x hx))
      simp only [θ, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at hxθ
      rw [hwφ] at hxθ
      linarith [hmax x hx]
    · rintro ⟨hx, hxℓ⟩
      have hxφ : φ x = a := hface ⟨hx, fun z hz => by rw [hxℓ]; exact hmax z hz⟩
      exact ⟨hx, by simp [θ, hxℓ, hwφ, hxφ]⟩
  have heq := (exposed_insert_trichotomy hconv θ w hw hθmax y).2.1 hθy
  rw [hfaces] at heq
  rw [← heq]
  exact ContinuousLinearMap.toExposed.isExposed (l := θ)

end Grunbaum2003


namespace Grunbaum2003

/-- Set and exposed-face geometry for adjoining a point beyond one facet. -/
theorem pyramid_extension_set_and_face_classification
    {d m : ℕ} (P : Set (Fin d → ℝ))
    (hconv : Convex ℝ P) (hcompact : IsCompact P) (hPne : P.Nonempty)
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (ψ : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hP : P = {x | φ x ≤ a ∧ ∀ j, ψ j x ≤ c j})
    (y : Fin d → ℝ) (hyφ : a < φ y) (hyψ : ∀ j, ψ j y < c j) :
    (convexHull ℝ (insert y P) =
      P ∪ convexHull ℝ (insert y {x ∈ P | φ x = a})) ∧
    (∀ H : Set (Fin d → ℝ), H.Nonempty →
      IsExposed ℝ (convexHull ℝ (insert y P)) H →
      H ≠ convexHull ℝ (insert y P) →
      H = {y} ∨ IsExposed ℝ P H ∨
        ∃ G : Set (Fin d → ℝ), G.Nonempty ∧ IsExposed ℝ P G ∧
          G ⊆ {x ∈ P | φ x = a} ∧ H = convexHull ℝ (insert y G)) ∧
    (∀ (ℓ : (Fin d → ℝ) →L[ℝ] ℝ) (w : Fin d → ℝ), w ∈ P →
      (∀ x ∈ P, ℓ x ≤ ℓ w) → ℓ y < ℓ w →
      IsExposed ℝ (convexHull ℝ (insert y P)) (ℓ.toExposed P) ∧
      (ℓ.toExposed P ⊆ {x | φ x = a} →
        IsExposed ℝ (convexHull ℝ (insert y P))
          (convexHull ℝ (insert y (ℓ.toExposed P))))) := by
  refine ⟨convexHull_insert_eq_union_pyramid P φ a ψ c hP hPne y hyφ
    (fun j => (hyψ j).le), ?_, ?_⟩
  · exact fun H hne hH hp => exposed_faces_of_pyramid_extension P hconv hcompact hPne
      φ a ψ c hP y hyφ hyψ H hne hH hp
  · intro ℓ w hw hmax hyℓ
    constructor
    · rw [← (exposed_insert_trichotomy hconv ℓ w hw hmax y).1 hyℓ]
      exact ContinuousLinearMap.toExposed.isExposed (l := ℓ)
    · intro hface
      apply cone_exposed_of_support_below_apex hconv φ a _ ℓ w hw hmax hface y hyφ hyℓ
      intro x hx
      rw [hP] at hx
      exact hx.1

end Grunbaum2003
-- END StellarPyramidGeometry.lean

-- BEGIN StellarSupportLowerFaces.lean
set_option autoImplicit false
open scoped Classical BigOperators

private lemma finite_strict_perturbation {d m : ℕ}
    (ψ : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin m → ℝ)
    (w u : Fin d → ℝ) (hw : ∀ i, ψ i w < c i) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ ∀ i, ψ i (w + t • u) < c i := by
  let r : Fin m → ℝ := fun i => |ψ i u| / (c i - ψ i w)
  let B : ℝ := ∑ i, r i
  have hr : ∀ i, 0 ≤ r i := fun i => div_nonneg (abs_nonneg _) (sub_pos.mpr (hw i)).le
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => hr i)
  have hden : 0 < 1 + B := by linarith
  let t : ℝ := 1 / (1 + B)
  have ht : 0 < t := div_pos zero_lt_one hden
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact (div_le_one hden).2 (by linarith)
  have htden : t * (1 + B) = 1 := by
    dsimp [t]
    exact div_mul_cancel₀ _ (ne_of_gt hden)
  refine ⟨t, ht, ht1, fun i => ?_⟩
  have hri : r i ≤ B := Finset.single_le_sum (fun j _ => hr j) (Finset.mem_univ i)
  have hsmall : t * r i < 1 := by
    calc
      t * r i < t * (1 + B) := mul_lt_mul_of_pos_left (by linarith) ht
      _ = 1 := htden
  have hδ : 0 < c i - ψ i w := sub_pos.mpr (hw i)
  have hratio : t * |ψ i u| / (c i - ψ i w) < 1 := by
    simpa only [r, mul_div_assoc] using hsmall
  have hgap : t * |ψ i u| < c i - ψ i w := (div_lt_one hδ).1 hratio
  have hslope := mul_le_mul_of_nonneg_left (le_abs_self (ψ i u)) ht.le
  rw [map_add, map_smul, smul_eq_mul]
  linarith

/-- A point can move strictly beyond one support plane while remaining strictly
beneath any given finite family of other support planes. -/
private theorem small_apex {d m : ℕ} {P : Set (Fin d → ℝ)}
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (w z : Fin d → ℝ)
    (hbound : ∀ x ∈ P, φ x ≤ φ w) (hz : φ z < φ w)
    (ψ : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hw : ∀ i, ψ i w < c i) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      φ w < φ (w + t • (w - z)) ∧
      w + t • (w - z) ∉ P ∧
      ∀ i, ψ i (w + t • (w - z)) < c i := by
  obtain ⟨t, ht, ht1, hplanes⟩ := finite_strict_perturbation ψ c w (w - z) hw
  have habove : φ w < φ (w + t • (w - z)) := by
    rw [map_add, map_smul, map_sub, smul_eq_mul]
    nlinarith [mul_pos ht (sub_pos.mpr hz)]
  exact ⟨t, ht, ht1, habove, fun h => (not_le_of_gt habove) (hbound _ h), hplanes⟩

/-- The barycenter of the selected support vertices admits an exterior
perturbation beneath every other finite support plane that does not contain
all of those vertices. -/
private theorem stellarSupportLower_barycenter_apex {d m : ℕ} (hd : 0 < d) {P : Set (Fin d → ℝ)}
    (hP : Convex ℝ P) (v : Fin d → Fin d → ℝ) (hvP : ∀ i, v i ∈ P)
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (hbound : ∀ x ∈ P, φ x ≤ a) (hlevel : ∀ i, φ (v i) = a)
    (z : Fin d → ℝ) (hz : φ z < a)
    (ψ : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hother : ∀ j, (∀ i, ψ j (v i) ≤ c j) ∧ ∃ i, ψ j (v i) < c j) :
    let w : Fin d → ℝ := (d : ℝ)⁻¹ • ∑ i, v i
    w ∈ P ∧ φ w = a ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
        a < φ (w + t • (w - z)) ∧
        w + t • (w - z) ∉ P ∧
        ∀ j, ψ j (w + t • (w - z)) < c j := by
  intro w
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  have hwP : w ∈ P := by
    have hmass := hP.centerMass_mem (t := Finset.univ) (w := fun _ : Fin d => (1 : ℝ))
      (z := v) (fun _ _ => zero_le_one) (by simpa using hdpos) (fun i _ => hvP i)
    simpa [Finset.centerMass] using hmass
  have hφw : φ w = a := by
    dsimp [w]
    rw [map_smul, map_sum]
    simp [hlevel, smul_eq_mul, hdne]
  have hplanes : ∀ j, ψ j w < c j := by
    intro j
    have hsum : (∑ i, ψ j (v i)) < (d : ℝ) * c j := by
      calc
        (∑ i, ψ j (v i)) < ∑ _i : Fin d, c j := by
          obtain ⟨i, hi⟩ := (hother j).2
          exact Finset.sum_lt_sum (fun i _ => (hother j).1 i) ⟨i, Finset.mem_univ i, hi⟩
        _ = (d : ℝ) * c j := by simp
    calc
      ψ j w = (d : ℝ)⁻¹ * ∑ i, ψ j (v i) := by
        dsimp [w]
        rw [map_smul, map_sum, smul_eq_mul]
      _ < (d : ℝ)⁻¹ * ((d : ℝ) * c j) :=
        mul_lt_mul_of_pos_left hsum (inv_pos.mpr hdpos)
      _ = c j := by rw [← mul_assoc, inv_mul_cancel₀ hdne, one_mul]
  refine ⟨hwP, hφw, ?_⟩
  have hbound' : ∀ x ∈ P, φ x ≤ φ w := by simpa [hφw] using hbound
  have hz' : φ z < φ w := by simpa [hφw] using hz
  obtain ⟨t, ht, ht1, hφ, hout, hrest⟩ := small_apex φ w z hbound' hz' ψ c hplanes
  exact ⟨t, ht, ht1, hφw ▸ hφ, hout, hrest⟩

set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003

/-- An exposed face is recovered by intersecting its affine span with the ambient set. -/
theorem stellarSupportLower_exposed_eq_inter_affineSpan {d : ℕ}
    {P F : Set (Fin d → ℝ)} (hF : IsExposed ℝ P F) (hne : F.Nonempty) :
    F = P ∩ (affineSpan ℝ F : Set (Fin d → ℝ)) := by
  obtain ⟨φ, hφ⟩ := hF hne
  obtain ⟨w, hwF⟩ := hne
  have hw : w ∈ P ∧ ∀ x ∈ P, φ x ≤ φ w := by simpa [hφ] using hwF
  let H := (affineSpan ℝ ({φ w} : Set ℝ)).comap φ.toLinearMap.toAffineMap
  have hFH : F ⊆ (H : Set (Fin d → ℝ)) := by
    intro x hx
    have hx' : x ∈ P ∧ ∀ y ∈ P, φ y ≤ φ x := by simpa [hφ] using hx
    have heq : φ x = φ w := le_antisymm (hw.2 x hx'.1) (hx'.2 w hw.1)
    simpa [H, AffineSubspace.mem_comap] using heq
  have hspanH := affineSpan_le_of_subset_coe hFH
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨hF.subset hx, subset_affineSpan ℝ F hx⟩
  · rintro x ⟨hxP, hxspan⟩
    have hxH := hspanH hxspan
    have heq : φ x = φ w := by simpa [H, AffineSubspace.mem_comap] using hxH
    rw [hφ]
    exact ⟨hxP, fun y hy => heq ▸ hw.2 y hy⟩

/-- Two comparable nonempty exposed faces with equal affine dimension coincide. -/
theorem stellarSupportLower_exposed_eq_of_subset_of_finrank_eq {d : ℕ}
    {P F G : Set (Fin d → ℝ)} (hF : IsExposed ℝ P F) (hne : F.Nonempty)
    (hG : IsExposed ℝ P G) (hFG : F ⊆ G)
    (hdim : Module.finrank ℝ (affineSpan ℝ F).direction =
      Module.finrank ℝ (affineSpan ℝ G).direction) : F = G := by
  have hle : affineSpan ℝ F ≤ affineSpan ℝ G := affineSpan_mono ℝ hFG
  have hdirection : (affineSpan ℝ F).direction = (affineSpan ℝ G).direction :=
    Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle) hdim
  have hspan : affineSpan ℝ F = affineSpan ℝ G :=
    AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdirection (hne.affineSpan ℝ) hle
  rw [stellarSupportLower_exposed_eq_inter_affineSpan hF hne,
    stellarSupportLower_exposed_eq_inter_affineSpan hG (hne.mono hFG), hspan]

/-- Every nonempty proper exposed face of a full-dimensional polytope has
affine dimension strictly smaller than the ambient dimension. -/
theorem stellarSupportLower_proper_face_finrank {d : ℕ} {P G : Set (Fin d → ℝ)}
    (hP : IsDPolytope P) (hG : IsExposed ℝ P G) (hGne : G.Nonempty) (hproper : G ≠ P) :
    Module.finrank ℝ (affineSpan ℝ G).direction + 1 ≤ d := by
  have hPdim : Module.finrank ℝ (affineSpan ℝ P).direction = d := by
    rw [hP.2, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun]
  have hle : Module.finrank ℝ (affineSpan ℝ G).direction ≤ d := by
    simpa only [Module.finrank_fin_fun] using
      Submodule.finrank_le (affineSpan ℝ G).direction
  have hne : Module.finrank ℝ (affineSpan ℝ G).direction ≠ d := by
    intro heq
    exact hproper (stellarSupportLower_exposed_eq_of_subset_of_finrank_eq hG hGne
      (IsExposed.refl P) hG.subset (heq.trans hPdim.symm))
  omega

/-- Choose a supporting functional with an exact level-set description of a nonempty face. -/
theorem stellarSupportLower_exists_support {d : ℕ} {P F : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ P F) (hne : F.Nonempty) :
    ∃ (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ),
      (∀ x ∈ P, φ x ≤ a) ∧ F = {x ∈ P | φ x = a} := by
  obtain ⟨φ, hφ⟩ := hF hne
  obtain ⟨w, hwF⟩ := hne
  have hw : w ∈ P ∧ ∀ x ∈ P, φ x ≤ φ w := by simpa [hφ] using hwF
  refine ⟨φ, φ w, hw.2, ?_⟩
  rw [hφ]
  ext x
  constructor
  · rintro ⟨hxP, hx⟩
    exact ⟨hxP, le_antisymm (hw.2 x hxP) (hx w hw.1)⟩
  · rintro ⟨hxP, hx⟩
    exact ⟨hxP, fun y hy => hx ▸ hw.2 y hy⟩

/-- A supporting plane of a distinct face of no greater dimension is strict
at some vertex of a generating simplex for the selected face. -/
theorem stellarSupportLower_exists_vertex_strict {d n : ℕ}
    {P F G : Set (Fin d → ℝ)} (hF : IsExposed ℝ P F) (hFne : F.Nonempty)
    (hG : IsExposed ℝ P G) (hFG : F ≠ G)
    (hdim_le : Module.finrank ℝ (affineSpan ℝ G).direction ≤
      Module.finrank ℝ (affineSpan ℝ F).direction)
    (v : Fin n → Fin d → ℝ) (hFv : F = convexHull ℝ (Set.range v))
    (ψ : (Fin d → ℝ) →L[ℝ] ℝ) (c : ℝ)
    (hbound : ∀ x ∈ P, ψ x ≤ c) (hGeq : G = {x ∈ P | ψ x = c}) :
    ∃ i, ψ (v i) < c := by
  have hvF : ∀ i, v i ∈ F := by
    intro i
    rw [hFv]
    exact subset_convexHull ℝ _ (Set.mem_range_self i)
  by_contra! hnotstrict
  have hveq : ∀ i, ψ (v i) = c :=
    fun i => le_antisymm (hbound (v i) (hF.subset (hvF i))) (hnotstrict i)
  have hconst : ∀ x ∈ F, ψ x = c := by
    rw [hFv]
    exact convexHull_min (by rintro _ ⟨i, rfl⟩; exact hveq i)
      ((convex_singleton c).linear_preimage ψ.toLinearMap)
  have hsub : F ⊆ G := by
    intro x hx
    rw [hGeq]
    exact ⟨hF.subset hx, hconst x hx⟩
  have hdim : Module.finrank ℝ (affineSpan ℝ F).direction =
      Module.finrank ℝ (affineSpan ℝ G).direction :=
    le_antisymm (Submodule.finrank_mono (AffineSubspace.direction_le
      (affineSpan_mono ℝ hsub))) hdim_le
  exact hFG (stellarSupportLower_exposed_eq_of_subset_of_finrank_eq hF hFne hG hsub hdim)

end Grunbaum2003

namespace Grunbaum2003

/-- A strict support inequality at a newly adjoined point preserves its old contact face. -/
theorem stellarSupportLower_face_survives_strict_apex {d : ℕ}
    {P G : Set (Fin d → ℝ)} (hconv : Convex ℝ P)
    (ψ : (Fin d → ℝ) →L[ℝ] ℝ) (c : ℝ)
    (hbound : ∀ x ∈ P, ψ x ≤ c) (hGeq : G = {x ∈ P | ψ x = c})
    (y : Fin d → ℝ) (hy : ψ y < c) :
    IsExposed ℝ (convexHull ℝ (insert y P)) G := by
  intro hGne
  obtain ⟨w, hwG⟩ := hGne
  have hw : w ∈ P ∧ ψ w = c := by simpa [hGeq] using hwG
  have hwQ : w ∈ convexHull ℝ (insert y P) :=
    subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hw.1)
  have hQbound : ∀ x ∈ convexHull ℝ (insert y P), ψ x ≤ c := by
    apply convexHull_min
    · intro x hx
      rcases hx with rfl | hx
      · exact hy.le
      · exact hbound x hx
    · exact (convex_Iic c).linear_preimage ψ.toLinearMap
  refine ⟨ψ, Set.Subset.antisymm ?_ ?_⟩
  · intro x hxG
    have hx : x ∈ P ∧ ψ x = c := by simpa [hGeq] using hxG
    exact ⟨subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hx.1),
      fun z hz => hx.2 ▸ hQbound z hz⟩
  · rintro x ⟨hxQ, hxmax⟩
    have hxlevel : ψ x = c :=
      le_antisymm (hQbound x hxQ) (hw.2 ▸ hxmax w hwQ)
    rw [convexHull_insert ⟨w, hw.1⟩, hconv.convexHull_eq, mem_convexJoin] at hxQ
    rcases hxQ with ⟨y', hy', z, hz, a, b, ha, hb, hab, hrepr⟩
    obtain rfl : y' = y := hy'
    have heq := congrArg ψ hrepr
    simp only [map_add, map_smul, smul_eq_mul, hxlevel] at heq
    have hsum : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
    have ha0 : a = 0 := by
      apply le_antisymm _ ha
      by_contra! hapos
      have hgap := mul_pos hapos (sub_pos.mpr hy)
      have hgap' := mul_nonneg hb (sub_nonneg.mpr (hbound z hz))
      nlinarith
    have hb1 : b = 1 := by linarith
    have hxz : x = z := by simpa [ha0, hb1] using hrepr.symm
    rw [hGeq]
    exact ⟨hxz ▸ hz, hxlevel⟩

/-- A simplicial facet has an apex beyond its prescribed support plane and
strictly beneath prescribed support planes of any finite family of other
proper faces. The selected facet ceases to be exposed after the apex is added. -/
theorem stellarSupportLower_exists_apex_prescribed_supports {d m : ℕ}
    {P F : Set (Fin d → ℝ)} (hP : IsSimplicialDPolytope P)
    (hFne : F.Nonempty) (hF : IsExposed ℝ P F)
    (hFdim : Module.finrank ℝ (affineSpan ℝ F).direction + 1 = d)
    (G : Fin m → Set (Fin d → ℝ))
    (hG : ∀ j, IsExposed ℝ P (G j))
    (hGproper : ∀ j, G j ≠ P)
    (hGF : ∀ j, G j ≠ F)
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (hbound : ∀ x ∈ P, φ x ≤ a) (hFeq : F = {x ∈ P | φ x = a})
    (ψ : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hother_bound : ∀ j x, x ∈ P → ψ j x ≤ c j)
    (hGeq : ∀ j, G j = {x ∈ P | ψ j x = c j}) :
    ∃ y : Fin d → ℝ, y ∉ P ∧ a < φ y ∧ (∀ j, ψ j y < c j) ∧
      (∀ j, IsExposed ℝ (convexHull ℝ (insert y P)) (G j)) ∧
      ¬ IsExposed ℝ (convexHull ℝ (insert y P)) F := by
  have hd : 0 < d := by omega
  obtain ⟨v, hv, hFv⟩ := hP.2 F hFne hF hFdim
  have hvF : ∀ i, v i ∈ F := by
    intro i
    rw [hFv]
    exact subset_convexHull ℝ _ (Set.mem_range_self i)
  have hvP : ∀ i, v i ∈ P := fun i => hF.subset (hvF i)
  have hlevel : ∀ i, φ (v i) = a := by
    intro i
    have hi := hvF i
    rw [hFeq] at hi
    exact hi.2
  have hproper : F ≠ P := by
    intro heq
    have hf := hFdim
    rw [heq, hP.1.2, AffineSubspace.direction_top, finrank_top,
      Module.finrank_fin_fun] at hf
    omega
  have hnot : ¬ P ⊆ F := fun h => hproper (Set.Subset.antisymm hF.subset h)
  obtain ⟨z, hzP, hzF⟩ := Set.not_subset.mp hnot
  have hz : φ z < a := by
    apply lt_of_le_of_ne (hbound z hzP)
    intro heq
    apply hzF
    rw [hFeq]
    exact ⟨hzP, heq⟩
  have hstrict : ∀ j, ∃ i, ψ j (v i) < c j := by
    intro j
    have hj : Module.finrank ℝ (affineSpan ℝ (G j)).direction + 1 ≤ d := by
      rcases (G j).eq_empty_or_nonempty with hE | hN
      · have hzero : Module.finrank ℝ (affineSpan ℝ (G j)).direction = 0 := by simp [hE]
        omega
      · exact stellarSupportLower_proper_face_finrank hP.1 (hG j) hN (hGproper j)
    have hdim : Module.finrank ℝ (affineSpan ℝ (G j)).direction ≤
        Module.finrank ℝ (affineSpan ℝ F).direction := by
      omega
    exact stellarSupportLower_exists_vertex_strict hF hFne (hG j) (Ne.symm (hGF j))
      hdim v hFv (ψ j) (c j) (hother_bound j) (hGeq j)
  have hconv : Convex ℝ P := by
    obtain ⟨V, _, _, rfl⟩ := hP.1.1
    exact convex_convexHull ℝ V
  let w : Fin d → ℝ := (d : ℝ)⁻¹ • ∑ i, v i
  have hsmall := stellarSupportLower_barycenter_apex hd hconv v hvP φ a hbound hlevel z hz ψ c
    (fun j => ⟨fun i => hother_bound j (v i) (hvP i), hstrict j⟩)
  change w ∈ P ∧ φ w = a ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
    a < φ (w + t • (w - z)) ∧ w + t • (w - z) ∉ P ∧
    ∀ j, ψ j (w + t • (w - z)) < c j at hsmall
  obtain ⟨hwP, hwφ, t, ht, _, habove, hout, hrest⟩ := hsmall
  let y := w + t • (w - z)
  refine ⟨y, hout, habove, hrest, ?_, ?_⟩
  · intro j
    exact stellarSupportLower_face_survives_strict_apex hconv (ψ j) (c j)
      (hother_bound j) (hGeq j) y (hrest j)
  intro hFQ
  have hwF : w ∈ F := by
    rw [hFeq]
    exact ⟨hwP, hwφ⟩
  have hzQ : z ∈ convexHull ℝ (insert y P) :=
    subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hzP)
  have hyQ : y ∈ convexHull ℝ (insert y P) :=
    subset_convexHull ℝ _ (Set.mem_insert _ _)
  let r : ℝ := 1 / (1 + t)
  have hden : 0 < 1 + t := by linarith
  have hr0 : 0 < r := div_pos zero_lt_one hden
  have hr1 : r < 1 := (div_lt_one hden).2 (by linarith)
  have hline : AffineMap.lineMap z y r = w := by
    rw [AffineMap.lineMap_apply_module']
    ext i
    change r * (y i - z i) + z i = w i
    dsimp [y, r]
    field_simp [ne_of_gt hden]
    <;> ring
  have hwseg : w ∈ openSegment ℝ z y := by
    rw [← hline]
    exact lineMap_mem_openSegment ℝ z y ⟨hr0, hr1⟩
  exact hout (hF.subset (hFQ.isExtreme.right_mem_of_mem_openSegment hzQ hyQ hwF hwseg))

end Grunbaum2003
-- END StellarSupportLowerFaces.lean

-- BEGIN StellarFacetPresentation.lean
set_option autoImplicit false

noncomputable section

namespace Grunbaum2003


theorem aux_pp_int_step {d : ℕ} {P : Set (Fin d → ℝ)} {c : Fin d → ℝ} (hc : c ∈ interior P)
    (u : Fin d → ℝ) : ∃ ε : ℝ, 0 < ε ∧ c + ε • u ∈ P := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior c hc
  refine ⟨r / (2 * (‖u‖ + 1)), by positivity, interior_subset (hball ?_)⟩
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  have h1 : ‖u‖ < ‖u‖ + 1 := by linarith
  calc r / (2 * (‖u‖ + 1)) * ‖u‖ ≤ r / (2 * (‖u‖ + 1)) * (‖u‖ + 1) := by
        gcongr
    _ = r / 2 := by field_simp
    _ < r := by linarith

theorem aux_pp_hull_le {d : ℕ} (V : Finset (Fin d → ℝ)) (c : Fin d → ℝ)
    (l : Module.Dual ℝ (Fin d → ℝ)) (β : ℝ) (hl : ∀ v ∈ V, l (v - c) ≤ β) :
    ∀ y ∈ convexHull ℝ (V : Set (Fin d → ℝ)), l (y - c) ≤ β := by
  intro y hy
  have hsub : convexHull ℝ (V : Set (Fin d → ℝ)) ⊆ {w | l w ≤ β + l c} :=
    convexHull_min (fun v hv => by
      have := hl v hv; rw [map_sub] at this; show l v ≤ β + l c; linarith)
      (convex_halfSpace_le l.isLinear _)
  have := hsub hy
  simp only [Set.mem_setOf_eq] at this
  rw [map_sub]; linarith

/-- Polar-vertex step: a separating normalized functional can be moved until its tight
vertices span the space. -/
theorem aux_pp_polar {d : ℕ} (V : Finset (Fin d → ℝ)) (c : Fin d → ℝ)
    (hc : c ∈ interior (convexHull ℝ (V : Set (Fin d → ℝ)))) (x : Fin d → ℝ) :
    ∀ n : ℕ, ∀ l : Module.Dual ℝ (Fin d → ℝ), (∀ v ∈ V, l (v - c) ≤ 1) → 1 < l (x - c) →
      (V.filter (fun v => l (v - c) < 1)).card = n →
      ∃ l' : Module.Dual ℝ (Fin d → ℝ), (∀ v ∈ V, l' (v - c) ≤ 1) ∧ 1 < l' (x - c) ∧
        Submodule.span ℝ ((fun v => v - c) '' ↑(V.filter (fun v => l' (v - c) = 1))) = ⊤ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hl hx hn
  by_cases hW : Submodule.span ℝ ((fun v => v - c) '' ↑(V.filter (fun v => l (v - c) = 1))) = ⊤
  · exact ⟨l, hl, hx, hW⟩
  obtain ⟨h0, h0ne, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hW)
  have hk : ∀ v ∈ V, l (v - c) = 1 → h0 (v - c) = 0 := fun v hv hv1 =>
    hle (Submodule.subset_span ⟨v, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hv, hv1⟩), rfl⟩)
  obtain ⟨h, hne, hker, hhx⟩ : ∃ h : Module.Dual ℝ (Fin d → ℝ), h ≠ 0 ∧
      (∀ v ∈ V, l (v - c) = 1 → h (v - c) = 0) ∧ 0 ≤ h (x - c) := by
    by_cases hs : 0 ≤ h0 (x - c)
    · exact ⟨h0, h0ne, hk, hs⟩
    · refine ⟨-h0, neg_ne_zero.mpr h0ne, fun v hv hv1 => by simp [hk v hv hv1], ?_⟩
      simp only [LinearMap.neg_apply]; linarith [not_le.mp hs]
  have hexists : ∃ v ∈ V, 0 < h (v - c) := by
    by_contra hcon
    push Not at hcon
    apply hne
    have hP := aux_pp_hull_le V c h 0 hcon
    refine LinearMap.ext (fun u => ?_)
    obtain ⟨ε, hε, hεu⟩ := aux_pp_int_step hc u
    obtain ⟨ε', hε', hεu'⟩ := aux_pp_int_step hc (-u)
    have h1 := hP _ hεu
    have h2 := hP _ hεu'
    simp only [add_sub_cancel_left, map_smul, map_neg, smul_eq_mul] at h1 h2
    have h3 : h u ≤ 0 := by nlinarith
    have h4 : 0 ≤ h u := by nlinarith
    rw [LinearMap.zero_apply]
    linarith
  set S := V.filter (fun v => 0 < h (v - c)) with hS
  have hSne : S.Nonempty := by
    obtain ⟨v, hv, hpos⟩ := hexists
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hpos⟩⟩
  obtain ⟨vs, hvsS, hvsmin⟩ := S.exists_min_image (fun v => (1 - l (v - c)) / h (v - c)) hSne
  have hvs : vs ∈ V ∧ 0 < h (vs - c) := Finset.mem_filter.mp hvsS
  set t := (1 - l (vs - c)) / h (vs - c) with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith [hl vs hvs.1]) hvs.2.le
  set l' := l + t • h with hl'def
  have hl'app : ∀ z, l' z = l z + t * h z := fun z => by
    simp [hl'def, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  have hl' : ∀ v ∈ V, l' (v - c) ≤ 1 := by
    intro v hv
    rw [hl'app]
    by_cases hpos : 0 < h (v - c)
    · have := hvsmin v (Finset.mem_filter.mpr ⟨hv, hpos⟩)
      rw [le_div_iff₀ hpos] at this
      linarith
    · push Not at hpos
      nlinarith [hl v hv]
  have hx' : 1 < l' (x - c) := by rw [hl'app]; nlinarith
  have hvs1 : l' (vs - c) = 1 := by
    rw [hl'app, ht, div_mul_cancel₀ _ hvs.2.ne']; ring
  have hvslt : l (vs - c) < 1 := by
    rcases lt_or_eq_of_le (hl vs hvs.1) with h' | h'
    · exact h'
    · exfalso; have := hker vs hvs.1 h'; linarith [hvs.2]
  have hsub : V.filter (fun v => l' (v - c) < 1) ⊂ V.filter (fun v => l (v - c) < 1) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨vs, Finset.mem_filter.mpr ⟨hvs.1, hvslt⟩, ?_⟩
      intro hmem
      have := (Finset.mem_filter.mp hmem).2
      linarith
    · intro v hv
      rw [Finset.mem_filter] at hv ⊢
      refine ⟨hv.1, ?_⟩
      by_contra hcon
      have heq : l (v - c) = 1 := le_antisymm (hl v hv.1) (not_lt.mp hcon)
      have h5 := hker v hv.1 heq
      have : l' (v - c) = 1 := by rw [hl'app, h5, heq]; ring
      linarith [hv.2]
  exact ih _ (hn ▸ Finset.card_lt_card hsub) l' hl' hx' rfl

/-- The face cut out by a polar vertex is a facet, and every exposing functional of it
separates `x`. -/
theorem aux_pp_facet {d : ℕ} (hd : 0 < d) (V : Finset (Fin d → ℝ)) (c : Fin d → ℝ)
    (hcP : c ∈ convexHull ℝ (V : Set (Fin d → ℝ))) (l : Module.Dual ℝ (Fin d → ℝ))
    (hl : ∀ v ∈ V, l (v - c) ≤ 1)
    (hspan : Submodule.span ℝ ((fun v => v - c) '' ↑(V.filter (fun v => l (v - c) = 1))) = ⊤)
    (x : Fin d → ℝ) (hx : 1 < l (x - c)) :
    ∃ G ∈ {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ (convexHull ℝ (V : Set (Fin d → ℝ))) F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = d - 1},
      ∀ g : StrongDual ℝ (Fin d → ℝ),
        G = {y ∈ convexHull ℝ (V : Set (Fin d → ℝ)) |
          ∀ y' ∈ convexHull ℝ (V : Set (Fin d → ℝ)), g y' ≤ g y} →
        ∀ f ∈ G, g f < g x := by
  set P := convexHull ℝ (V : Set (Fin d → ℝ)) with hPdef
  set T := V.filter (fun v => l (v - c) = 1) with hT
  have hPle : ∀ y ∈ P, l (y - c) ≤ 1 := aux_pp_hull_le V c l 1 hl
  have hTne : T.Nonempty := by
    by_contra hTe
    rw [Finset.not_nonempty_iff_eq_empty] at hTe
    rw [hTe, Finset.coe_empty, Set.image_empty, Submodule.span_empty] at hspan
    have h1 : Module.finrank ℝ (⊤ : Submodule ℝ (Fin d → ℝ)) = 0 := by rw [← hspan, finrank_bot]
    rw [finrank_top, Module.finrank_fin_fun] at h1
    omega
  obtain ⟨t0, ht0⟩ := hTne
  have ht0' := Finset.mem_filter.mp ht0
  set lc : StrongDual ℝ (Fin d → ℝ) := LinearMap.toContinuousLinearMap l with hlcdef
  have hlc : ∀ z, lc z = l z := fun z => by simp [hlcdef]
  set G := {y ∈ P | ∀ y' ∈ P, lc y' ≤ lc y} with hG
  have hTG : ∀ t ∈ T, t ∈ G := by
    intro t ht
    have ht' := Finset.mem_filter.mp ht
    refine ⟨subset_convexHull ℝ _ (Finset.mem_coe.mpr ht'.1), fun y' hy' => ?_⟩
    rw [hlc, hlc]
    have h1 := hPle y' hy'
    have h2 := ht'.2
    rw [map_sub] at h1 h2
    linarith
  have hG1 : ∀ y ∈ G, l (y - c) = 1 := by
    intro y hy
    have h1 := hy.2 t0 (hTG t0 ht0).1
    rw [hlc, hlc] at h1
    have h2 := hPle y hy.1
    have h3 := ht0'.2
    rw [map_sub] at h2 h3 ⊢
    linarith
  refine ⟨G, ⟨⟨t0, hTG t0 ht0⟩, fun _ => ⟨lc, rfl⟩, ?_⟩, ?_⟩
  · have hl0 : l ≠ 0 := by
      intro h0; have := ht0'.2; rw [h0, LinearMap.zero_apply] at this; norm_num at this
    have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hl0
    rw [Module.finrank_fin_fun] at hker
    set D := (affineSpan ℝ G).direction with hD
    have hDle : D ≤ LinearMap.ker l := by
      rw [hD, direction_affineSpan, vectorSpan_def, Submodule.span_le]
      rintro z ⟨y, hy, y', hy', rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub]
      have h1 := hG1 y hy
      have h2 := hG1 y' hy'
      rw [map_sub] at h1 h2 ⊢
      linarith
    have hup : Module.finrank ℝ D ≤ d - 1 := by
      have := Submodule.finrank_mono hDle
      omega
    have hdown : d ≤ Module.finrank ℝ D + 1 := by
      have htop : (⊤ : Submodule ℝ (Fin d → ℝ)) ≤ D ⊔ Submodule.span ℝ {t0 - c} := by
        rw [← hspan, Submodule.span_le]
        rintro z ⟨t, ht, rfl⟩
        have hsplit : t - c = (t - t0) + (t0 - c) := by abel
        simp only [SetLike.mem_coe]
        rw [hsplit]
        refine Submodule.add_mem_sup ?_ (Submodule.mem_span_singleton_self _)
        rw [hD, direction_affineSpan]
        exact vsub_mem_vectorSpan ℝ (hTG t ht) (hTG t0 ht0)
      have h1 := Submodule.finrank_mono htop
      rw [finrank_top, Module.finrank_fin_fun] at h1
      have h2 := Submodule.finrank_add_le_finrank_add_finrank D (Submodule.span ℝ {t0 - c})
      have h3 : Module.finrank ℝ (Submodule.span ℝ ({t0 - c} : Set (Fin d → ℝ))) ≤ 1 := by
        have := finrank_span_le_card (R := ℝ) ({t0 - c} : Set (Fin d → ℝ))
        simpa using this
      omega
    omega
  · intro g hg f hf
    have hGg : ∀ y ∈ G, ∀ y' ∈ P, g y' ≤ g y := by
      intro y hy; rw [hg] at hy; exact hy.2
    have hGP : ∀ y ∈ G, y ∈ P := fun y hy => hy.1
    have hTeq : ∀ t ∈ T, g t = g f := fun t ht =>
      le_antisymm (hGg f hf t (hGP t (hTG t ht))) (hGg t (hTG t ht) f (hGP f hf))
    set β := g f - g c with hβ
    have hlin : (g : (Fin d → ℝ) →ₗ[ℝ] ℝ) = β • l := by
      refine LinearMap.ext_on hspan ?_
      rintro z ⟨t, ht, rfl⟩
      have ht' := Finset.mem_filter.mp ht
      simp only [ContinuousLinearMap.coe_coe, LinearMap.smul_apply, smul_eq_mul]
      rw [ht'.2, mul_one, map_sub, hTeq t ht]
    have happ : ∀ z, g z = β * l z := fun z => by
      have := congrArg (fun φ : (Fin d → ℝ) →ₗ[ℝ] ℝ => φ z) hlin
      simpa using this
    have hβ0 : 0 ≤ β := by
      have := hGg f hf c hcP
      rw [hβ]; linarith
    have hβpos : 0 < β := by
      rcases lt_or_eq_of_le hβ0 with h | h
      · exact h
      · exfalso
        have hcG : c ∈ G := by
          rw [hg]
          exact ⟨hcP, fun y' _ => by rw [happ, happ, ← h]; simp⟩
        have := hG1 c hcG
        simp at this
    have hgx := happ (x - c)
    rw [map_sub] at hgx
    nlinarith

/-- A full-dimensional polytope is exactly the intersection of one prescribed
supporting halfspace per actual facet; an interior point is strictly feasible. -/
theorem stellarFacetPresentation_exists {d : ℕ} (hd : 0 < d)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (ℱ : Finset (Set (Fin d → ℝ)))
    (hℱ : (ℱ : Set (Set (Fin d → ℝ))) =
      {F | F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = d - 1}) :
    ∃ (φ : {F // F ∈ ℱ} → StrongDual ℝ (Fin d → ℝ)) (a : {F // F ∈ ℱ} → ℝ),
      P = {x | ∀ F, φ F x ≤ a F} ∧
      (∀ F, F.val = {x ∈ P | φ F x = a F}) ∧
      ∃ c ∈ interior P, ∀ F, φ F c < a F := by
  classical
  have hconv : Convex ℝ P := by
    obtain ⟨V, _, _, rfl⟩ := hP.1
    exact convex_convexHull ℝ V
  have hcompact : IsCompact P := by
    obtain ⟨V, hfin, _, rfl⟩ := hP.1
    exact hfin.isCompact_convexHull (𝕜 := ℝ)
  obtain ⟨c, hc⟩ := hconv.interior_nonempty_iff_affineSpan_eq_top.mpr hP.2
  have hcP : c ∈ P := interior_subset hc
  have hfacets (F : {F // F ∈ ℱ}) : F.val.Nonempty ∧ IsExposed ℝ P F.val ∧
      Module.finrank ℝ (affineSpan ℝ F.val).direction = d - 1 := by
    have hmem : F.val ∈ (ℱ : Set (Set (Fin d → ℝ))) := F.property
    rw [hℱ] at hmem
    exact hmem
  have hex (F : {F // F ∈ ℱ}) :
      ∃ (φ : StrongDual ℝ (Fin d → ℝ)) (w : Fin d → ℝ),
        w ∈ F.val ∧ F.val = {x ∈ P | ∀ z ∈ P, φ z ≤ φ x} := by
    obtain ⟨φ, hφ⟩ := (hfacets F).2.1 (hfacets F).1
    exact ⟨φ, (hfacets F).1.some, (hfacets F).1.some_mem, hφ⟩
  choose φ w hw hdesc using hex
  have hwP (F : {F // F ∈ ℱ}) : w F ∈ P := (hfacets F).2.1.subset (hw F)
  have hmax (F : {F // F ∈ ℱ}) : ∀ z ∈ P, φ F z ≤ φ F (w F) := by
    have h := hw F
    rw [hdesc F] at h
    exact h.2
  have hlevel (F : {F // F ∈ ℱ}) : F.val = {x ∈ P | φ F x = φ F (w F)} := by
    rw [hdesc F]
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, le_antisymm (hmax F x hx.1) (hx.2 (w F) (hwP F))⟩
    · rintro ⟨hx, hval⟩
      exact ⟨hx, fun z hz => hval ▸ hmax F z hz⟩
  refine ⟨φ, fun F => φ F (w F), ?_, hlevel, c, hc, ?_⟩
  · ext x
    constructor
    · exact fun hx F => hmax F x hx
    · intro hx
      by_contra hxP
      obtain ⟨V0, hVfin, _, hPV0⟩ := hP.1
      let V := hVfin.toFinset
      have hPV : P = convexHull ℝ (V : Set (Fin d → ℝ)) := by
        simpa only [V, hVfin.coe_toFinset] using hPV0
      have hc' : c ∈ interior (convexHull ℝ (V : Set (Fin d → ℝ))) := by
        rw [← hPV]
        exact hc
      obtain ⟨θ, u, hθP, hθx⟩ := geometric_hahn_banach_closed_point hconv hcompact.isClosed hxP
      have hθc := hθP c hcP
      let l0 : Module.Dual ℝ (Fin d → ℝ) :=
        (u - θ c)⁻¹ • (θ : (Fin d → ℝ) →ₗ[ℝ] ℝ)
      have hl0app : ∀ z, l0 z = θ z / (u - θ c) := by
        intro z
        simp [l0, div_eq_inv_mul]
      have hl0V : ∀ v ∈ V, l0 (v - c) ≤ 1 := by
        intro v hv
        rw [hl0app, div_le_one (by linarith), map_sub]
        have hvP : v ∈ P := by
          rw [hPV]
          exact subset_convexHull ℝ _ hv
        linarith [hθP v hvP]
      have hl0x : 1 < l0 (x - c) := by
        rw [hl0app, one_lt_div (by linarith), map_sub]
        linarith
      obtain ⟨l, hl, hlx, hlspan⟩ := aux_pp_polar V c hc' x _ l0 hl0V hl0x rfl
      have hcP' : c ∈ convexHull ℝ (V : Set (Fin d → ℝ)) := by
        rw [← hPV]
        exact hcP
      obtain ⟨G, hG, hGsep⟩ := aux_pp_facet hd V c hcP' l hl hlspan x hlx
      rw [← hPV] at hG hGsep
      have hGF : G ∈ ℱ := by
        change G ∈ (ℱ : Set (Set (Fin d → ℝ)))
        rw [hℱ]
        exact hG
      let I : {F // F ∈ ℱ} := ⟨G, hGF⟩
      have hsep := hGsep (φ I) (hdesc I) (w I) (hw I)
      exact (not_lt_of_ge (hx I)) hsep
  · intro F
    have hφne : φ F ≠ 0 := by
      intro hzero
      have hFP : F.val = P := by
        rw [hdesc F, hzero]
        ext x
        simp
      have hdim := (hfacets F).2.2
      rw [hFP, hP.2, AffineSubspace.direction_top, finrank_top,
        Module.finrank_fin_fun] at hdim
      omega
    obtain ⟨v, hv⟩ : ∃ v, 0 < φ F v := by
      by_contra! hn
      apply hφne
      ext v
      have hnneg := hn (-v)
      rw [map_neg] at hnneg
      simp only [ContinuousLinearMap.zero_apply]
      linarith [hn v]
    obtain ⟨ε, hε, hεv⟩ := aux_pp_int_step hc v
    have hbound := hmax F _ hεv
    rw [map_add, map_smul, smul_eq_mul] at hbound
    nlinarith

end Grunbaum2003
end
-- END StellarFacetPresentation.lean

-- BEGIN StellarBaseFaces.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.StellarCone

/-- All vertex-subset hulls of the selected simplex facet are old exposed faces. -/
theorem base_subset_exposed {d : ℕ} {P F : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    (hF : IsExposed ℝ P F) (v : Fin d → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (hFv : F = convexHull ℝ (Set.range v))
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ) (hlevel : ∀ i, φ (v i) = a)
    (y : Fin d → ℝ) (hy : a < φ y) (s : Finset (Fin d)) :
    IsExposed ℝ P (convexHull ℝ (v '' (s : Set (Fin d)))) := by
  let u : Fin (d + 1) → Fin d → ℝ := Fin.cons y v
  have hu : AffineIndependent ℝ u := affineIndependent_cons v hv φ a hlevel y hy
  have hface := (StellarFaceTools.simplex_subset_hull_isExposed_and_labels d u hu
    (s.image Fin.succ)).1
  have himage : u '' ((s.image Fin.succ : Finset (Fin (d + 1))) : Set (Fin (d + 1))) =
      v '' (s : Set (Fin d)) := by
    rw [Finset.coe_image, Set.image_image]
    congr 1
  rw [himage] at hface
  have hFU : F ⊆ convexHull ℝ (Set.range u) := by
    rw [hFv]
    apply convexHull_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i.succ, rfl⟩
  have hSF : convexHull ℝ (v '' (s : Set (Fin d))) ⊆ F := by
    rw [hFv]
    exact convexHull_mono (Set.image_subset_range _ _)
  exact StellarFaceTools.isExposed_trans_polytope d P hP F _ hF (hface.mono hFU hSF)

/-- In particular, the generating points of the selected facet are actual old vertices. -/
theorem base_vertices_exposed {d : ℕ} {P F : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    (hF : IsExposed ℝ P F) (v : Fin d → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (hFv : F = convexHull ℝ (Set.range v))
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ) (hlevel : ∀ i, φ (v i) = a)
    (y : Fin d → ℝ) (hy : a < φ y) (i : Fin d) : IsExposed ℝ P {v i} := by
  simpa using base_subset_exposed hP hF v hv hFv φ a hlevel y hy {i}

/-- Every old exposed face in the chosen simplex facet has a vertex-subset presentation. -/
theorem old_face_in_base {d : ℕ} {P F G : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ P F) (v : Fin d → Fin d → ℝ)
    (hFv : F = convexHull ℝ (Set.range v))
    (hG : IsExposed ℝ P G) (hGF : G ⊆ F) (hGne : G.Nonempty) :
    ∃ s : Finset (Fin d), s.Nonempty ∧ G = convexHull ℝ (v '' (s : Set (Fin d))) := by
  let s := Finset.univ.filter (fun i => v i ∈ G)
  have hGr : IsExposed ℝ (convexHull ℝ (Set.range v)) G := by
    rw [← hFv]
    exact hG.mono hF.subset hGF
  have hi : G ∩ Set.range v = v '' (s : Set (Fin d)) := by
    ext x
    constructor
    · rintro ⟨hx, i, rfl⟩
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(Finset.mem_filter.mp hi).2, Set.mem_range_self i⟩
  have heq : G = convexHull ℝ (v '' (s : Set (Fin d))) := by
    rw [← hi]
    exact StellarFaceTools.finite_face_hull v hGr
  refine ⟨s, ?_, heq⟩
  have hne := heq ▸ hGne
  obtain ⟨_, i, hi, rfl⟩ := convexHull_nonempty_iff.mp hne
  exact ⟨i, hi⟩

/-- An old face which survives after adding the apex exposes its cone whenever
it lies in the selected support plane. -/
theorem cone_exposed_of_survival {d : ℕ} {P G : Set (Fin d → ℝ)} (hconv : Convex ℝ P)
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ) (hbound : ∀ x ∈ P, φ x ≤ a)
    (y : Fin d → ℝ) (hy : a < φ y)
    (hGne : G.Nonempty) (hGP : G ⊆ P) (hlevel : ∀ x ∈ G, φ x = a)
    (hG : IsExposed ℝ (convexHull ℝ (insert y P)) G) :
    IsExposed ℝ (convexHull ℝ (insert y P)) (convexHull ℝ (insert y G)) := by
  obtain ⟨w, hw⟩ := hGne
  obtain ⟨ℓ, hdesc⟩ := hG ⟨w, hw⟩
  have hwP := hGP hw
  have hwQ : w ∈ convexHull ℝ (insert y P) :=
    subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hwP)
  have hyQ : y ∈ convexHull ℝ (insert y P) := subset_convexHull ℝ _ (Set.mem_insert _ _)
  have hmaxQ : ∀ z ∈ convexHull ℝ (insert y P), ℓ z ≤ ℓ w := by
    have hw' := hw
    rw [hdesc] at hw'
    exact hw'.2
  have hmaxP : ∀ z ∈ P, ℓ z ≤ ℓ w := fun z hz =>
    hmaxQ z (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hz))
  have hlow : ℓ y < ℓ w := by
    apply lt_of_le_of_ne (hmaxQ y hyQ)
    intro heq
    have hyG : y ∈ G := by
      rw [hdesc]
      exact ⟨hyQ, fun z hz => heq ▸ hmaxQ z hz⟩
    exact (not_le_of_gt hy) (hbound y (hGP hyG))
  have hface : ℓ.toExposed P = G := by
    ext x
    constructor
    · intro hx
      have heq : ℓ x = ℓ w := le_antisymm (hmaxP x hx.1) (hx.2 w hwP)
      rw [hdesc]
      exact ⟨subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hx.1),
        fun z hz => heq ▸ hmaxQ z hz⟩
    · intro hx
      have hx' := hx
      rw [hdesc] at hx'
      exact ⟨hGP hx, fun z hz => hx'.2 z (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hz))⟩
  rw [← hface]
  apply cone_exposed_of_support_below_apex hconv φ a hbound ℓ w hwP hmaxP _ y hy hlow
  rw [hface]
  exact hlevel

end Grunbaum2003.StellarCone
-- END StellarBaseFaces.lean

-- BEGIN StellarApexAssembly.lean
set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003.StellarAssembly

/-- Choose one facet and an apex preserving every other proper old face,
with a complete classification of the new proper exposed faces. -/
theorem exists_apex_data {d : ℕ} (hd : 0 < d)
    (P : Set (Fin d → ℝ)) (hP : IsSimplicialDPolytope P)
    (ℱ : ℕ → Finset (Set (Fin d → ℝ)))
    (hℱ : ∀ k, (ℱ k : Set (Set (Fin d → ℝ))) =
      {F | F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = k}) :
    ∃ (F : Set (Fin d → ℝ)) (y : Fin d → ℝ) (v : Fin d → Fin d → ℝ)
      (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ),
      F ∈ ℱ (d - 1) ∧ AffineIndependent ℝ v ∧ F = convexHull ℝ (Set.range v) ∧
      (∀ x ∈ P, φ x ≤ a) ∧ F = {x ∈ P | φ x = a} ∧ y ∉ P ∧ a < φ y ∧
      (∀ G : Set (Fin d → ℝ), G.Nonempty → IsExposed ℝ P G → G ≠ P → G ≠ F →
        IsExposed ℝ (convexHull ℝ (insert y P)) G) ∧
      (¬ IsExposed ℝ (convexHull ℝ (insert y P)) F) ∧
      (∀ H : Set (Fin d → ℝ), H.Nonempty →
        IsExposed ℝ (convexHull ℝ (insert y P)) H → H ≠ convexHull ℝ (insert y P) →
        H = {y} ∨ IsExposed ℝ P H ∨
          ∃ G : Set (Fin d → ℝ), G.Nonempty ∧ IsExposed ℝ P G ∧
            G ⊆ F ∧ H = convexHull ℝ (insert y G)) := by
  classical
  have hconv : Convex ℝ P := by
    obtain ⟨V, _, _, rfl⟩ := hP.1.1
    exact convex_convexHull ℝ V
  have hcompact : IsCompact P := by
    obtain ⟨V, hV, _, rfl⟩ := hP.1.1
    exact hV.isCompact_convexHull (𝕜 := ℝ)
  have hPne : P.Nonempty := by
    obtain ⟨V, _, hV, rfl⟩ := hP.1.1
    exact hV.mono (subset_convexHull ℝ V)
  have hdata (k : ℕ) (F : Set (Fin d → ℝ)) :
      F ∈ ℱ k ↔ F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = k := by
    change F ∈ (ℱ k : Set (Set (Fin d → ℝ))) ↔ _
    rw [hℱ k]
    rfl
  obtain ⟨φ, a, hrep, hcontact, _, _, _⟩ :=
    stellarFacetPresentation_exists hd P hP.1 (ℱ (d - 1)) (hℱ (d - 1))
  have hbound (F : {F // F ∈ ℱ (d - 1)}) (x : Fin d → ℝ) (hx : x ∈ P) :
      φ F x ≤ a F := by
    rw [hrep] at hx
    exact hx F
  have hfacne : (ℱ (d - 1)).Nonempty := by
    by_contra hnone
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    apply hcompact.ne_univ
    rw [hrep]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    intro F
    exact False.elim (hnone ⟨F.val, F.property⟩)
  obtain ⟨F, hFmem⟩ := hfacne
  let i0 : {F // F ∈ ℱ (d - 1)} := ⟨F, hFmem⟩
  obtain ⟨hFne, hF, hFrank⟩ := (hdata (d - 1) F).mp hFmem
  have hFdim : Module.finrank ℝ (affineSpan ℝ F).direction + 1 = d := by omega
  obtain ⟨v, hv, hFv⟩ := hP.2 F hFne hF hFdim
  let S : Finset (Set (Fin d → ℝ)) := (Finset.range d).biUnion ℱ
  let T := S.erase F
  have hSmem (G : Set (Fin d → ℝ)) :
      G ∈ S ↔ G.Nonempty ∧ IsExposed ℝ P G ∧ G ≠ P := by
    constructor
    · intro h
      obtain ⟨k, hk, hG⟩ := Finset.mem_biUnion.mp h
      obtain ⟨hne, hexp, hrank⟩ := (hdata k G).mp hG
      refine ⟨hne, hexp, ?_⟩
      intro heq
      rw [heq, hP.1.2, AffineSubspace.direction_top, finrank_top,
        Module.finrank_fin_fun] at hrank
      have := Finset.mem_range.mp hk
      omega
    · rintro ⟨hne, hexp, hproper⟩
      have hr := stellarSupportLower_proper_face_finrank hP.1 hexp hne hproper
      apply Finset.mem_biUnion.mpr
      exact ⟨_, Finset.mem_range.mpr (by omega), (hdata _ G).mpr ⟨hne, hexp, rfl⟩⟩
  let e : Fin T.card ≃ ↥T := Fintype.equivOfCardEq (by simp)
  let Gs : Fin T.card → Set (Fin d → ℝ) := fun j => (e j).val
  have hGs (j : Fin T.card) : (Gs j).Nonempty ∧ IsExposed ℝ P (Gs j) ∧
      Gs j ≠ P ∧ Gs j ≠ F := by
    have ht := Finset.mem_erase.mp (e j).property
    have h := (hSmem _).mp ht.2
    exact ⟨h.1, h.2.1, h.2.2, ht.1⟩
  have hsupp (j : Fin T.card) : ∃ (ψ : (Fin d → ℝ) →L[ℝ] ℝ) (b : ℝ),
      (∀ x ∈ P, ψ x ≤ b) ∧ Gs j = {x ∈ P | ψ x = b} ∧
      (∀ h : Gs j ∈ ℱ (d - 1), ψ = φ ⟨Gs j, h⟩ ∧ b = a ⟨Gs j, h⟩) := by
    by_cases hj : Gs j ∈ ℱ (d - 1)
    · exact ⟨φ ⟨Gs j, hj⟩, a ⟨Gs j, hj⟩, hbound ⟨Gs j, hj⟩, hcontact ⟨Gs j, hj⟩, fun _ => ⟨rfl, rfl⟩⟩
    · obtain ⟨ψ, b, hb, heq⟩ := stellarSupportLower_exists_support (hGs j).2.1 (hGs j).1
      exact ⟨ψ, b, hb, heq, fun h => False.elim (hj h)⟩
  choose ψ b hψbound hGeq hψfacet using hsupp
  obtain ⟨y, hyP, hyφ, hyψ, hsurvive, hremove⟩ :=
    stellarSupportLower_exists_apex_prescribed_supports hP hFne hF hFdim Gs
      (fun j => (hGs j).2.1) (fun j => (hGs j).2.2.1) (fun j => (hGs j).2.2.2)
      (φ i0) (a i0) (hbound i0) (hcontact i0) ψ b hψbound hGeq
  have hAllSurvive (G : Set (Fin d → ℝ)) (hne : G.Nonempty)
      (hG : IsExposed ℝ P G) (hGP : G ≠ P) (hGF : G ≠ F) :
      IsExposed ℝ (convexHull ℝ (insert y P)) G := by
    have hGT : G ∈ T := Finset.mem_erase.mpr ⟨hGF, (hSmem G).mpr ⟨hne, hG, hGP⟩⟩
    obtain ⟨j, hj⟩ := e.surjective ⟨G, hGT⟩
    simpa only [Gs, hj] using hsurvive j
  let J := {j : {F // F ∈ ℱ (d - 1)} // j ≠ i0}
  have hOther (j : J) : φ j.val y < a j.val := by
    have hjF : j.val.val ≠ F := by
      intro h
      apply j.property
      exact Subtype.ext h
    have hjS : j.val.val ∈ S := Finset.mem_biUnion.mpr
      ⟨d - 1, Finset.mem_range.mpr (by omega), j.val.property⟩
    have hjT : j.val.val ∈ T := Finset.mem_erase.mpr ⟨hjF, hjS⟩
    obtain ⟨k, hk⟩ := e.surjective ⟨j.val.val, hjT⟩
    have hkG : Gs k = j.val.val := congrArg Subtype.val hk
    have hkfacet : Gs k ∈ ℱ (d - 1) := hkG ▸ j.val.property
    have heqs := hψfacet k hkfacet
    have hψeq : ψ k = φ j.val := by simpa only [hkG] using heqs.1
    have hbeq : b k = a j.val := by simpa only [hkG] using heqs.2
    simpa only [hψeq, hbeq] using hyψ k
  have hsplit : P = {x | φ i0 x ≤ a i0 ∧ ∀ j : J, φ j.val x ≤ a j.val} := by
    rw [hrep]
    ext x
    constructor
    · intro hx
      exact ⟨hx i0, fun j => hx j.val⟩
    · rintro ⟨hx0, hx⟩ j
      by_cases hj : j = i0
      · simpa only [hj] using hx0
      · exact hx ⟨j, hj⟩
  refine ⟨F, y, v, φ i0, a i0, hFmem, hv, hFv, hbound i0, hcontact i0,
    hyP, hyφ, hAllSurvive, hremove, ?_⟩
  intro H hHne hH hproper
  have hclass := exposed_faces_of_pyramid_extension P hconv hcompact hPne
    (φ i0) (a i0) (fun j : J => φ j.val) (fun j : J => a j.val) hsplit
    y hyφ hOther H hHne hH hproper
  simpa only [← hcontact i0] using hclass

end Grunbaum2003.StellarAssembly
-- END StellarApexAssembly.lean

-- BEGIN StellarFaceFamilies.lean
set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003.StellarAssembly

/-- Adjoining one point to a full-dimensional polytope preserves the polytope conditions. -/
theorem isDPolytope_insert {d : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    (y : Fin d → ℝ) : IsDPolytope (convexHull ℝ (insert y P)) := by
  obtain ⟨V, hfin, hne, hPV⟩ := hP.1
  have heq : convexHull ℝ (insert y P) = convexHull ℝ (insert y V) := by
    rw [hPV, Set.insert_eq, convexHull_convexHull_union_right, ← Set.insert_eq]
  refine ⟨⟨insert y V, hfin.insert y, Set.insert_nonempty _ _, heq⟩, ?_⟩
  apply top_unique
  rw [← hP.2]
  apply affineSpan_mono ℝ
  exact fun x hx => subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hx)

/-- A finite polytope has only finitely many exposed faces, including the improper ones. -/
theorem finite_exposed_faces {d : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P) :
    {F : Set (Fin d → ℝ) | IsExposed ℝ P F}.Finite := by
  obtain ⟨V, hVfin, _, hPgen⟩ := hP.1
  have : Finite V := hVfin.to_subtype
  have hr : Set.range (fun i : V => i.val) = V := Subtype.range_coe
  have hFaces (F : Set (Fin d → ℝ)) (hF : IsExposed ℝ P F) :
      F = convexHull ℝ (F ∩ V) := by
    rw [hPgen, ← hr] at hF
    simpa only [hr] using StellarFaceTools.finite_face_hull (fun i : V => i.val) hF
  apply Set.Finite.of_finite_image (f := fun F => F ∩ V)
  · apply hVfin.finite_subsets.subset
    rintro _ ⟨F, _, rfl⟩
    exact Set.inter_subset_right
  · intro F hF G hG heq
    change F ∩ V = G ∩ V at heq
    rw [hFaces F hF, hFaces G hG, heq]

/-- Exact finite face families exist in every dimension, with the canonical `faceCount`. -/
theorem exists_face_families {d : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P) :
    ∃ ℱ : ℕ → Finset (Set (Fin d → ℝ)), ∀ k,
      (ℱ k : Set (Set (Fin d → ℝ))) =
        {F | F.Nonempty ∧ IsExposed ℝ P F ∧
          Module.finrank ℝ (affineSpan ℝ F).direction = k} ∧
      (ℱ k).card = faceCount P k := by
  let S := fun k : ℕ => {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
    Module.finrank ℝ (affineSpan ℝ F).direction = k}
  have hfin (k : ℕ) : (S k).Finite :=
    (finite_exposed_faces hP).subset (fun _ h => h.2.1)
  refine ⟨fun k => (hfin k).toFinset, fun k => ⟨(hfin k).coe_toFinset, ?_⟩⟩
  exact (Set.ncard_eq_toFinset_card (S k) (hfin k)).symm

end Grunbaum2003.StellarAssembly
-- END StellarFaceFamilies.lean

-- BEGIN StellarFaceCharacterization.lean
set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003.StellarAssembly

/-- The proper faces of a stellar extension are precisely retained old faces
and cones over subsets of the chosen simplex facet vertices. -/
theorem face_iff_old_or_cone {d : ℕ} {P F : Set (Fin d → ℝ)}
    (hP : IsSimplicialDPolytope P) (hFne : F.Nonempty) (hF : IsExposed ℝ P F)
    (hFdim : Module.finrank ℝ (affineSpan ℝ F).direction + 1 = d)
    (v : Fin d → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (hFv : F = convexHull ℝ (Set.range v))
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ) (hbound : ∀ x ∈ P, φ x ≤ a)
    (hFeq : F = {x ∈ P | φ x = a}) (y : Fin d → ℝ) (hy : a < φ y)
    (hsurvive : ∀ G : Set (Fin d → ℝ), G.Nonempty → IsExposed ℝ P G → G ≠ P → G ≠ F →
      IsExposed ℝ (convexHull ℝ (insert y P)) G)
    (hremove : ¬ IsExposed ℝ (convexHull ℝ (insert y P)) F)
    (hclass : ∀ H : Set (Fin d → ℝ), H.Nonempty →
      IsExposed ℝ (convexHull ℝ (insert y P)) H → H ≠ convexHull ℝ (insert y P) →
      H = {y} ∨ IsExposed ℝ P H ∨
        ∃ G : Set (Fin d → ℝ), G.Nonempty ∧ IsExposed ℝ P G ∧
          G ⊆ F ∧ H = convexHull ℝ (insert y G))
    (k : ℕ) (hk : k < d) (H : Set (Fin d → ℝ)) :
    (H.Nonempty ∧ IsExposed ℝ (convexHull ℝ (insert y P)) H ∧
      Module.finrank ℝ (affineSpan ℝ H).direction = k) ↔
    (H.Nonempty ∧ IsExposed ℝ P H ∧
      Module.finrank ℝ (affineSpan ℝ H).direction = k ∧ H ≠ F) ∨
    ∃ s : Finset (Fin d), s.card = k ∧ H = convexHull ℝ (insert y (v '' (s : Set (Fin d)))) := by
  have hconv : Convex ℝ P := by
    obtain ⟨V, _, _, rfl⟩ := hP.1.1
    exact convex_convexHull ℝ V
  have hQ : IsDPolytope (convexHull ℝ (insert y P)) := isDPolytope_insert hP.1 y
  have hvF (i : Fin d) : v i ∈ F := by
    rw [hFv]
    exact subset_convexHull ℝ _ (Set.mem_range_self i)
  have hlevel (i : Fin d) : φ (v i) = a := by
    have hi := hvF i
    rw [hFeq] at hi
    exact hi.2
  have hcollapse (s : Set (Fin d → ℝ)) :
      convexHull ℝ (insert y (convexHull ℝ s)) = convexHull ℝ (insert y s) := by
    rw [Set.insert_eq, convexHull_convexHull_union_right, ← Set.insert_eq]
  constructor
  · rintro ⟨hne, hH, hrank⟩
    have hproper : H ≠ convexHull ℝ (insert y P) := by
      intro heq
      rw [heq, hQ.2, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun] at hrank
      omega
    rcases hclass H hne hH hproper with hpoint | hold | ⟨G, hGne, hG, hGF, heq⟩
    · right
      refine ⟨∅, ?_, ?_⟩
      · have hz : k = 0 := by
          rw [hpoint, direction_affineSpan, vectorSpan_singleton, finrank_bot] at hrank
          exact hrank.symm
        simp [hz]
      · simpa using hpoint
    · left
      exact ⟨hne, hold, hrank, fun heq => hremove (heq ▸ hH)⟩
    · right
      obtain ⟨s, _, hGs⟩ := StellarCone.old_face_in_base hF v hFv hG hGF hGne
      rw [hGs, hcollapse] at heq
      refine ⟨s, ?_, heq⟩
      rw [heq, StellarCone.cone_finrank v hv φ a hlevel y hy s] at hrank
      exact hrank
  · rintro (⟨hne, hH, hrank, hHF⟩ | ⟨s, hsk, rfl⟩)
    · refine ⟨hne, hsurvive H hne hH ?_ hHF, hrank⟩
      intro heq
      rw [heq, hP.1.2, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun] at hrank
      omega
    · refine ⟨⟨y, subset_convexHull ℝ _ (Set.mem_insert _ _)⟩, ?_, ?_⟩
      · rcases s.eq_empty_or_nonempty with rfl | hs
        · simp only [Finset.coe_empty, Set.image_empty, insert_empty_eq, convexHull_singleton]
          obtain ⟨w, hwF⟩ := hFne
          have hwP := hF.subset hwF
          have hwφ : φ w = a := by
            rw [hFeq] at hwF
            exact hwF.2
          have hmax : ∀ x ∈ P, φ x ≤ φ w := by simpa only [hwφ] using hbound
          have hφy : φ w < φ y := by simpa only [hwφ] using hy
          have heq := (exposed_insert_trichotomy hconv φ w hwP hmax y).2.2 hφy
          rw [← heq]
          exact ContinuousLinearMap.toExposed.isExposed
        · let G := convexHull ℝ (v '' (s : Set (Fin d)))
          have hG : IsExposed ℝ P G :=
            StellarCone.base_subset_exposed hP.1 hF v hv hFv φ a hlevel y hy s
          have hGne : G.Nonempty := by
            obtain ⟨i, hi⟩ := hs
            exact ⟨v i, subset_convexHull ℝ _ ⟨i, hi, rfl⟩⟩
          have hGrank := StellarCone.subset_finrank v hv s hs
          change Module.finrank ℝ (affineSpan ℝ G).direction + 1 = s.card at hGrank
          have hGP : G ≠ P := by
            intro heq
            rw [heq, hP.1.2, AffineSubspace.direction_top, finrank_top,
              Module.finrank_fin_fun] at hGrank
            omega
          have hGF : G ≠ F := by
            intro heq
            rw [heq] at hGrank
            omega
          have hGinF : G ⊆ F := by
            rw [hFv]
            exact convexHull_mono (Set.image_subset_range _ _)
          have hGlevel : ∀ x ∈ G, φ x = a := by
            intro x hx
            have hxF := hGinF hx
            rw [hFeq] at hxF
            exact hxF.2
          have hexp := StellarCone.cone_exposed_of_survival hconv φ a hbound y hy
            hGne hG.subset hGlevel (hsurvive G hGne hG hGP hGF)
          change IsExposed ℝ (convexHull ℝ (insert y P))
            (convexHull ℝ (insert y (convexHull ℝ (v '' (s : Set (Fin d)))))) at hexp
          rwa [hcollapse] at hexp
      · exact (StellarCone.cone_finrank v hv φ a hlevel y hy s).trans hsk

end Grunbaum2003.StellarAssembly
-- END StellarFaceCharacterization.lean

-- BEGIN StellarCompletion.lean
set_option autoImplicit false
open scoped Classical

open Grunbaum2003
open Grunbaum2003.StellarAssembly

theorem solution (d : ℕ) (hd : 4 ≤ d)
    (P : Set (Fin d → ℝ)) (hP : IsSimplicialDPolytope P)
    (ℱ : ℕ → Finset (Set (Fin d → ℝ)))
    (hℱ : ∀ k : ℕ, (ℱ k : Set (Set (Fin d → ℝ))) =
      {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = k} ∧
      (ℱ k).card = faceCount P k) :
    ∃ (P' : Set (Fin d → ℝ)) (F₀ : Set (Fin d → ℝ))
      (y : Fin d → ℝ) (v : Fin d → Fin d → ℝ)
      (ℱ' : ℕ → Finset (Set (Fin d → ℝ))),
      IsSimplicialDPolytope P' ∧
      F₀ ∈ ℱ (d - 1) ∧
      y ∉ P ∧
      Function.Injective v ∧
      (∀ s : Finset (Fin d),
        convexHull ℝ (insert y (v '' (s : Set (Fin d)))) ∩
          {x : Fin d → ℝ | IsExposed ℝ P {x}} = v '' (s : Set (Fin d))) ∧
      (∀ k : ℕ, (ℱ' k : Set (Set (Fin d → ℝ))) =
        {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P' F ∧
          Module.finrank ℝ (affineSpan ℝ F).direction = k} ∧
        (ℱ' k).card = faceCount P' k) ∧
      let ℱ_new : ℕ → Finset (Set (Fin d → ℝ)) := fun k =>
        ((Finset.univ : Finset (Fin d)).powersetCard k).image
          (fun s : Finset (Fin d) => convexHull ℝ (insert y (v '' (s : Set (Fin d)))))
      (∀ j : Fin d, j.val + 1 < d → ℱ' j.val = ℱ j.val ∪ ℱ_new j.val) ∧
      ℱ' (d - 1) = (ℱ (d - 1)).erase F₀ ∪ ℱ_new (d - 1) := by
  classical
  obtain ⟨F, y, v, φ, a, hFmem, hv, hFv, hbound, hFeq, hyP, hy,
    hsurvive, hremove, hclass⟩ :=
    exists_apex_data (by omega) P hP ℱ (fun k => (hℱ k).1)
  have hdata (k : ℕ) (H : Set (Fin d → ℝ)) :
      H ∈ ℱ k ↔ H.Nonempty ∧ IsExposed ℝ P H ∧
        Module.finrank ℝ (affineSpan ℝ H).direction = k := by
    change H ∈ (ℱ k : Set (Set (Fin d → ℝ))) ↔ _
    rw [(hℱ k).1]
    rfl
  obtain ⟨hFne, hF, hFrank⟩ := (hdata (d - 1) F).mp hFmem
  have hFdim : Module.finrank ℝ (affineSpan ℝ F).direction + 1 = d := by omega
  have hlevel (i : Fin d) : φ (v i) = a := by
    have hi : v i ∈ F := by
      rw [hFv]
      exact subset_convexHull ℝ _ (Set.mem_range_self i)
    rw [hFeq] at hi
    exact hi.2
  let Q := convexHull ℝ (insert y P)
  have hQ : IsDPolytope Q := isDPolytope_insert hP.1 y
  have hchar (k : ℕ) (hk : k < d) (H : Set (Fin d → ℝ)) :=
    face_iff_old_or_cone hP hFne hF hFdim v hv hFv φ a hbound hFeq
      y hy hsurvive hremove hclass k hk H
  have hQs : IsSimplicialDPolytope Q := by
    refine ⟨hQ, ?_⟩
    intro H hHne hH hHdim
    have hk : Module.finrank ℝ (affineSpan ℝ H).direction < d := by omega
    rcases (hchar _ hk H).mp ⟨hHne, hH, rfl⟩ with hold | ⟨s, hsk, hHs⟩
    · exact hP.2 H hHne hold.2.1 hHdim
    · obtain ⟨w, hw, heq⟩ := StellarCone.cone_simplex v hv φ a hlevel y hy s
      have hcard : d = s.card + 1 := by omega
      let e : Fin d ≃ Fin (s.card + 1) := finCongr hcard
      refine ⟨w ∘ e, hw.comp_embedding e.toEmbedding, ?_⟩
      rw [e.surjective.range_comp w]
      exact hHs.trans heq
  obtain ⟨ℱ', hℱ'⟩ := exists_face_families hQ
  have hdata' (k : ℕ) (H : Set (Fin d → ℝ)) :
      H ∈ ℱ' k ↔ H.Nonempty ∧ IsExposed ℝ Q H ∧
        Module.finrank ℝ (affineSpan ℝ H).direction = k := by
    change H ∈ (ℱ' k : Set (Set (Fin d → ℝ))) ↔ _
    rw [(hℱ' k).1]
    rfl
  have hfamilies (k : ℕ) (hk : k < d) :
      ℱ' k = (ℱ k).erase F ∪
        ((Finset.univ : Finset (Fin d)).powersetCard k).image
          (fun s : Finset (Fin d) => convexHull ℝ (insert y (v '' (s : Set (Fin d))))) := by
    ext H
    rw [hdata', hchar k hk H, Finset.mem_union, Finset.mem_erase, Finset.mem_image]
    constructor
    · rintro (⟨hne, hH, hrank, hHF⟩ | ⟨s, hsk, heq⟩)
      · exact Or.inl ⟨hHF, (hdata k H).mpr ⟨hne, hH, hrank⟩⟩
      · exact Or.inr ⟨s, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ s, hsk⟩, heq.symm⟩
    · rintro (⟨hHF, hH⟩ | ⟨s, hs, heq⟩)
      · obtain ⟨hne, hH, hrank⟩ := (hdata k H).mp hH
        exact Or.inl ⟨hne, hH, hrank, hHF⟩
      · exact Or.inr ⟨s, (Finset.mem_powersetCard.mp hs).2, heq.symm⟩
  have hconv : Convex ℝ P := by
    obtain ⟨V, _, _, rfl⟩ := hP.1.1
    exact convex_convexHull ℝ V
  have hvExposed : ∀ i, IsExposed ℝ P {v i} :=
    StellarCone.base_vertices_exposed hP.1 hF v hv hFv φ a hlevel y hy
  refine ⟨Q, F, y, v, ℱ', hQs, hFmem, hyP, hv.injective, ?_, hℱ', ?_⟩
  · intro s
    exact StellarCone.stellarCone_old_exposed_vertices_of_supporting
      hconv v hvExposed φ.toLinearMap a hbound hlevel y hy s
  · constructor
    · intro j hj
      have hFnot : F ∉ ℱ j.val := by
        intro h
        have hrank := ((hdata j.val F).mp h).2.2
        omega
      simpa only [Finset.erase_eq_of_notMem hFnot] using hfamilies j.val j.isLt
    · exact hfamilies (d - 1) (by omega)
-- END StellarCompletion.lean
