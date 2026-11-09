-- Prove2me | solution 1 for Grunbaum2003.exists_polygon_vertex_count
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T20:50:31.258554+00:00
-- url     : https://prove2.me/submissions/62b7e1fd-f89a-4bbd-ab1c-100f18f68cd0

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Theorems.Thm_Grunbaum2003_polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.Convex.Join

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003Moment
open Grunbaum2003

/-- Moment-curve point `(s, s^2, …, s^d)`. -/
def mc (d : ℕ) (s : ℝ) : Fin d → ℝ := fun i => s ^ (i.val + 1)

/-- A point of a finite set that is the unique maximiser of a linear functional is an
exposed point of the convex hull. -/
lemma isExposed_convexHull_of_strict {d : ℕ} (V : Set (Fin d → ℝ)) (a : Fin d → ℝ)
    (ha : a ∈ V) (l : StrongDual ℝ (Fin d → ℝ)) (hl : ∀ v ∈ V, v ≠ a → l v < l a) :
    IsExposed ℝ (convexHull ℝ V) {a} := by
  intro _
  refine ⟨l, ?_⟩
  have hle : convexHull ℝ V ⊆ {y | l y ≤ l a} := by
    refine convexHull_min ?_ (convex_halfSpace_le (l : (Fin d → ℝ) →ₗ[ℝ] ℝ).isLinear (l a))
    intro v hv
    by_cases h : v = a
    · subst h; show l v ≤ l v; exact le_rfl
    · show l v ≤ l a; exact (hl v hv h).le
  ext x
  simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro rfl
    exact ⟨subset_convexHull ℝ V ha, fun y hy => hle hy⟩
  · rintro ⟨hx, hmax⟩
    have hxa : l a ≤ l x := hmax a (subset_convexHull ℝ V ha)
    have hax : l x ≤ l a := hle hx
    by_cases hW : (V \ {a}).Nonempty
    · have hV : V = insert a (V \ {a}) := by
        ext y; by_cases hy : y = a <;> simp [hy, ha]
      rw [hV, convexHull_insert hW] at hx
      obtain ⟨a', ha', w, hw, hxs⟩ := mem_convexJoin.1 hx
      rw [Set.mem_singleton_iff] at ha'
      subst ha'
      have hwlt : convexHull ℝ (V \ {a'}) ⊆ {y | l y < l a'} := by
        refine convexHull_min ?_ (convex_halfSpace_lt (l : (Fin d → ℝ) →ₗ[ℝ] ℝ).isLinear (l a'))
        intro v hv
        exact hl v hv.1 hv.2
      have hlw : l w < l a' := hwlt hw
      obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hxs
      have hlx : l (p • a' + q • w) = p * l a' + q * l w := by
        simp [map_add, map_smul, smul_eq_mul]
      have hq0 : q = 0 := by
        rw [hlx] at hxa
        have : p = 1 - q := by linarith
        subst this
        by_contra hq0
        have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
        nlinarith
      subst hq0
      have : p = 1 := by linarith
      subst this
      simp
    · have hV : V = {a} := by
        ext y; constructor
        · intro hy; by_contra hne
          exact hW ⟨y, hy, hne⟩
        · rintro rfl; exact ha
      rw [hV, convexHull_singleton] at hx
      exact hx

/-- The linear functional `x ↦ 2 t x₀ - x₁`. -/
noncomputable def lt2 (d : ℕ) (hd : 2 ≤ d) (t : ℝ) : StrongDual ℝ (Fin d → ℝ) :=
  (2 * t) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) ⟨0, by omega⟩ -
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) ⟨1, by omega⟩

lemma lt2_mc (d : ℕ) (hd : 2 ≤ d) (t s : ℝ) : lt2 d hd t (mc d s) = 2 * t * s - s ^ 2 := by
  simp [lt2, mc]

lemma mc_injective (d : ℕ) (hd : 1 ≤ d) : Function.Injective (mc d) := by
  intro s t h
  have := congrFun h ⟨0, by omega⟩
  simpa [mc] using this

/-- Any `k ≤ d + 1` distinct moment-curve points are affinely independent. -/
lemma affineIndependent_mc (d k : ℕ) (hk : k ≤ d + 1) (s : Fin k → ℝ)
    (hs : Function.Injective s) : AffineIndependent ℝ (fun i => mc d (s i)) := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw0 hwv
  have hlin : ∑ i, w i • mc d (s i) = 0 := by
    rw [← Finset.weightedVSub_eq_linear_combination _ hw0]; exact hwv
  have hvec : Matrix.vecMul w (Matrix.vandermonde s) = 0 := by
    funext j
    simp only [Matrix.vecMul, dotProduct, Matrix.vandermonde_apply, Pi.zero_apply]
    rcases Nat.eq_zero_or_pos j.val with hj | hj
    · simp only [hj, pow_zero, mul_one]; exact hw0
    · have hjd : j.val - 1 < d := by omega
      have := congrFun hlin ⟨j.val - 1, hjd⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mc, Pi.zero_apply] at this
      have he : j.val - 1 + 1 = j.val := by omega
      rw [he] at this
      exact this
  have hdet : (Matrix.vandermonde s).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.2 hs
  have := Matrix.eq_zero_of_vecMul_eq_zero hdet hvec
  intro i
  exact congrFun this i

/-- The moment polytope: convex hull of `m` integer moment-curve points. -/
def mcSet (d m : ℕ) : Set (Fin d → ℝ) := Set.range (fun i : Fin m => mc d (i : ℝ))

lemma mcSet_finite (d m : ℕ) : (mcSet d m).Finite := Set.finite_range _

lemma natCast_fin_injective (m : ℕ) : Function.Injective (fun i : Fin m => ((i : ℕ) : ℝ)) := by
  intro i j h
  have h' : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := h
  exact Fin.ext (by exact_mod_cast h')

lemma exposed_mcSet (d m : ℕ) (hd : 2 ≤ d) (a : Fin d → ℝ) :
    IsExposed ℝ (convexHull ℝ (mcSet d m)) {a} ↔ a ∈ mcSet d m := by
  constructor
  · intro h
    have hext : a ∈ Set.extremePoints ℝ (convexHull ℝ (mcSet d m)) := by
      exact h.isExtreme.mem_extremePoints
    exact extremePoints_convexHull_subset hext
  · rintro ⟨i, rfl⟩
    refine isExposed_convexHull_of_strict _ _ ⟨i, rfl⟩ (lt2 d hd (i : ℝ)) ?_
    rintro v ⟨j, rfl⟩ hne
    rw [lt2_mc, lt2_mc]
    have hij : ((j : ℕ) : ℝ) ≠ ((i : ℕ) : ℝ) := by
      intro h; apply hne; simp [h]
    have : 0 < (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) ^ 2 := by
      have := sub_ne_zero.2 hij; positivity
    nlinarith

lemma exposedSet_mcSet (d m : ℕ) (hd : 2 ≤ d) :
    {x : Fin d → ℝ | IsExposed ℝ (convexHull ℝ (mcSet d m)) {x}} = mcSet d m := by
  ext a; exact exposed_mcSet d m hd a

lemma ncard_mcSet (d m : ℕ) (hd : 1 ≤ d) : (mcSet d m).ncard = m := by
  unfold mcSet
  rw [Set.ncard_range_of_injective]
  · simp
  · exact (mc_injective d hd).comp (natCast_fin_injective m)

lemma isDPolytope_mcSet (d m : ℕ) (hm : d + 1 ≤ m) : IsDPolytope (convexHull ℝ (mcSet d m)) := by
  refine ⟨⟨mcSet d m, mcSet_finite d m, ⟨mc d 0, ⟨⟨0, by omega⟩, by simp⟩⟩, rfl⟩, ?_⟩
  rw [affineSpan_convexHull]
  let s : Fin (d + 1) → ℝ := fun i => ((i : ℕ) : ℝ)
  have hs : Function.Injective s := by
    intro i j h
    have h' : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := h
    exact Fin.ext (by exact_mod_cast h')
  have hind := affineIndependent_mc d (d + 1) le_rfl s hs
  have htop : affineSpan ℝ (Set.range (fun i => mc d (s i))) = ⊤ := by
    rw [hind.affineSpan_eq_top_iff_card_eq_finrank_add_one]
    simp
  rw [eq_top_iff, ← htop]
  apply affineSpan_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨i.val, by omega⟩, rfl⟩

lemma faceCount_zero_mcSet (d m : ℕ) (hd : 2 ≤ d) :
    faceCount (convexHull ℝ (mcSet d m)) 0 = m := by
  rw [(polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound d _).1,
    exposedSet_mcSet d m hd, ncard_mcSet d m (by omega)]


/-- Moment-curve (cyclic) polytopes are simplicial. -/
lemma isSimplicial_mcSet (d m : ℕ) (hd : 2 ≤ d) (hm : d + 1 ≤ m) :
    IsSimplicialDPolytope (convexHull ℝ (mcSet d m)) := by
  classical
  refine ⟨isDPolytope_mcSet d m hm, ?_⟩
  intro F hFne hFexp hFdim
  have hhull := (polytope_face_eq_convexHull_exposed_vertices d (convexHull ℝ (mcSet d m))
    (isDPolytope_mcSet d m hm)).2 ⟨F, hFexp⟩
  simp only at hhull
  rw [exposedSet_mcSet d m hd] at hhull
  let p : Fin m → (Fin d → ℝ) := fun i => mc d ((i : ℕ) : ℝ)
  let J : Finset (Fin m) := Finset.univ.filter (fun i => p i ∈ F)
  have hS : F ∩ mcSet d m = ((J.image p : Finset (Fin d → ℝ)) : Set (Fin d → ℝ)) := by
    ext x
    simp only [Set.mem_inter_iff, mcSet, Set.mem_range, Finset.coe_image, Set.mem_image,
      Finset.mem_coe, J, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, i, rfl⟩; exact ⟨i, hx, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨hi, i, rfl⟩
  rw [hS] at hhull
  have hdimS : Module.finrank ℝ (vectorSpan ℝ
      (((J.image p : Finset (Fin d → ℝ)) : Set (Fin d → ℝ)))) + 1 = d := by
    rw [← direction_affineSpan, ← affineSpan_convexHull, ← hhull]; exact hFdim
  have hcastinj : ∀ (k : ℕ) (o : Fin k → Fin m), Function.Injective o →
      Function.Injective (fun j : Fin k => (((o j : Fin m) : ℕ) : ℝ)) := by
    intro k o ho i j h
    exact ho ((natCast_fin_injective m) h)
  have hJcard : J.card = d := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rcases Nat.eq_zero_or_pos J.card with h0 | hpos
      · have hJ : J = ∅ := Finset.card_eq_zero.1 h0
        rw [hJ] at hhull
        simp only [Finset.image_empty, Finset.coe_empty, convexHull_empty] at hhull
        rw [hhull] at hFne
        exact Set.not_nonempty_empty hFne
      · obtain ⟨c, hc⟩ : ∃ c, J.card = c + 1 := ⟨J.card - 1, by omega⟩
        have := finrank_vectorSpan_image_finset_le ℝ p J hc
        omega
    · have hle : d + 1 ≤ J.card := hgt
      let o : Fin (d + 1) → Fin m := fun k => J.orderEmbOfFin rfl (Fin.castLE hle k)
      have ho : Function.Injective o := by
        intro i j h
        have := (J.orderEmbOfFin rfl).injective h
        exact Fin.castLE_injective hle this
      have hind := affineIndependent_mc d (d + 1) le_rfl _ (hcastinj _ o ho)
      have hfr := hind.finrank_vectorSpan (n := d) (by simp)
      have hsub : Set.range (fun k => mc d (((o k : Fin m) : ℕ) : ℝ)) ⊆
          (((J.image p : Finset (Fin d → ℝ)) : Set (Fin d → ℝ))) := by
        rintro _ ⟨k, rfl⟩
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
        exact ⟨o k, Finset.orderEmbOfFin_mem J rfl _, rfl⟩
      have := Submodule.finrank_mono (vectorSpan_mono ℝ hsub)
      omega
  let o := J.orderEmbOfFin hJcard
  refine ⟨fun k => mc d (((o k : Fin m) : ℕ) : ℝ), ?_, ?_⟩
  · exact affineIndependent_mc d d (by omega) _ (hcastinj _ o o.injective)
  · rw [hhull]
    congr 1
    ext x
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Set.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have : i ∈ Set.range o := by rw [Finset.range_orderEmbOfFin]; exact hi
      obtain ⟨k, rfl⟩ := this
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨o k, Finset.orderEmbOfFin_mem J hJcard k, rfl⟩

end Grunbaum2003Moment

open Grunbaum2003 Grunbaum2003Moment in
theorem solution (n : ℕ) :
    ∃ P : Set (Fin 2 → ℝ), IsDPolytope P ∧ faceCount P 0 = n + 3 :=
  ⟨convexHull ℝ (mcSet 2 (n + 3)), isDPolytope_mcSet 2 (n + 3) (by omega),
    faceCount_zero_mcSet 2 (n + 3) le_rfl⟩
