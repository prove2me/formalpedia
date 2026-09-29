-- Prove2me | solution 1 for NearEnemy.nearEnemy_noThreeCollinear_exists_projectionGeneric_image_generalPosition_rotationFree
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-18T15:10:38.815087+00:00
-- url     : https://prove2.me/submissions/23354195-ce13-4d05-988a-703e61606136

import Mathlib
import Definitions.Def_NearEnemyDefs
import Theorems.Thm_NearEnemy_circPoly_ne_zero_of_noThreeCollinear
import Theorems.Thm_NearEnemy_eq_zero_of_forall_inner_mul_inner_eq_zero
import Theorems.Thm_NearEnemy_eval_innerPoly
import Theorems.Thm_NearEnemy_eval_innerPoly_rows
import Theorems.Thm_NearEnemy_exists_smul_eq_of_forall_inner_det_eq_zero
import Theorems.Thm_NearEnemy_innerPoly_ne_zero
import Theorems.Thm_NearEnemy_nearEnemy_noThreeCollinear_parallel_midpoint_eq_samePair
import Theorems.Thm_NearEnemy_rowMap_apply

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy
namespace NearEnemy

/-- **Downstairs distance bridge**: if two projected pairs have equal planar
distance, the distance-class constraint polynomial of their difference
vectors evaluates to zero at the entry assignment. -/
theorem eval_distClassPoly_eq_zero_of_dist_eq
    {f : Fin 2 × ι → ℝ} {a b c e : EuclideanSpace ℝ ι}
    (h : dist (rowMap (rowOf f) a) (rowMap (rowOf f) b) =
      dist (rowMap (rowOf f) c) (rowMap (rowOf f) e)) :
    eval f (distClassPoly (a - b) (c - e)) = 0 := by
  have h2 : dist (rowMap (rowOf f) a) (rowMap (rowOf f) b) ^ 2 =
      dist (rowMap (rowOf f) c) (rowMap (rowOf f) e) ^ 2 := by rw [h]
  rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq] at h2
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs, rowMap_apply] at h2
  simp only [distClassPoly, map_add, map_sub, map_pow, eval_innerPoly,
    inner_sub_right]
  linear_combination h2

/-- **Distance-class separation**: if `⟪r, v - w⟫ * ⟪r, v + w⟫ = 0` for every
`r`, then `w = v` or `w = -v`.  Downstairs,
`‖Tv‖² - ‖Tw‖² = Σ_k ⟪T_k, v-w⟫⟪T_k, v+w⟫`; identical vanishing of each
summand is what a projection equating two distance classes would force, so
distinct `±`-classes stay separated generically. -/
theorem eq_or_eq_neg_of_forall_inner_sub_mul_inner_add {v w : V}
    (h : ∀ r : V, ⟪r, v - w⟫ * ⟪r, v + w⟫ = 0) : w = v ∨ w = -v := by
  by_cases hvw : v + w = 0
  · exact Or.inr (eq_neg_of_add_eq_zero_left (by rwa [add_comm] at hvw))
  · left
    have := eq_zero_of_forall_inner_mul_inner_eq_zero hvw h
    rw [sub_eq_zero] at this
    exact this.symm

/-- **Per-pair distance-class witness**: for difference vectors that are
neither equal nor opposite, the distance-class constraint polynomial is
nonzero as a polynomial.  No nondegeneracy or general-position hypothesis is
needed: identical vanishing forces `w = ±v` by the distance-class separation
lemma. -/
theorem distClassPoly_ne_zero {v w : EuclideanSpace ℝ ι}
    (h1 : w ≠ v) (h2 : w ≠ -v) : distClassPoly v w ≠ 0 := by
  intro h0
  have key : ∀ r : EuclideanSpace ℝ ι, ⟪r, v - w⟫ * ⟪r, v + w⟫ = 0 := by
    intro r
    have heval := congrArg (eval fun ki ↦ ![r, 0] ki.1 ki.2) h0
    rw [map_zero] at heval
    simp only [distClassPoly, map_add, map_sub, map_pow, eval_innerPoly_rows,
      Matrix.cons_val_zero, Matrix.cons_val_one, inner_zero_left] at heval
    rw [inner_sub_right, inner_add_right]
    linear_combination heval
  rcases eq_or_eq_neg_of_forall_inner_sub_mul_inner_add key with h | h
  · exact h1 h
  · exact h2 h

/-- **Downstairs concyclicity bridge**: if the four projected points lie on
one circle, the concyclicity constraint polynomial evaluates to zero at the
entry assignment.  The circle equation makes the first determinant column an
affine combination of the other three. -/
theorem eval_circPoly_eq_zero_of_dist_eq
    {f : Fin 2 × ι → ℝ} {a b c e : EuclideanSpace ℝ ι}
    {z : EuclideanSpace ℝ (Fin 2)} {ρ : ℝ}
    (ha : dist (rowMap (rowOf f) a) z = ρ)
    (hb : dist (rowMap (rowOf f) b) z = ρ)
    (hc : dist (rowMap (rowOf f) c) z = ρ)
    (he : dist (rowMap (rowOf f) e) z = ρ) :
    eval f (circPoly a b c e) = 0 := by
  have key : ∀ p : EuclideanSpace ℝ ι, dist (rowMap (rowOf f) p) z = ρ →
      ⟪rowOf f 0, p⟫ ^ 2 + ⟪rowOf f 1, p⟫ ^ 2 =
        2 * z 0 * ⟪rowOf f 0, p⟫ + 2 * z 1 * ⟪rowOf f 1, p⟫ +
          (ρ ^ 2 - z 0 ^ 2 - z 1 ^ 2) := by
    intro p hp
    have h2 : dist (rowMap (rowOf f) p) z ^ 2 = ρ ^ 2 := by rw [hp]
    rw [EuclideanSpace.dist_sq_eq] at h2
    simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs, rowMap_apply] at h2
    linear_combination h2
  have h₁ := key a ha
  have h₂ := key b hb
  have h₃ := key c hc
  have h₄ := key e he
  simp only [circPoly, map_add, map_sub, map_mul, map_pow, eval_innerPoly]
  linear_combination
    (⟪rowOf f 0, b⟫ * (⟪rowOf f 1, c⟫ - ⟪rowOf f 1, e⟫) -
      ⟪rowOf f 1, b⟫ * (⟪rowOf f 0, c⟫ - ⟪rowOf f 0, e⟫) +
      (⟪rowOf f 0, c⟫ * ⟪rowOf f 1, e⟫ - ⟪rowOf f 0, e⟫ * ⟪rowOf f 1, c⟫)) * h₁
    - (⟪rowOf f 0, a⟫ * (⟪rowOf f 1, c⟫ - ⟪rowOf f 1, e⟫) -
      ⟪rowOf f 1, a⟫ * (⟪rowOf f 0, c⟫ - ⟪rowOf f 0, e⟫) +
      (⟪rowOf f 0, c⟫ * ⟪rowOf f 1, e⟫ - ⟪rowOf f 0, e⟫ * ⟪rowOf f 1, c⟫)) * h₂
    + (⟪rowOf f 0, a⟫ * (⟪rowOf f 1, b⟫ - ⟪rowOf f 1, e⟫) -
      ⟪rowOf f 1, a⟫ * (⟪rowOf f 0, b⟫ - ⟪rowOf f 0, e⟫) +
      (⟪rowOf f 0, b⟫ * ⟪rowOf f 1, e⟫ - ⟪rowOf f 0, e⟫ * ⟪rowOf f 1, b⟫)) * h₃
    - (⟪rowOf f 0, a⟫ * (⟪rowOf f 1, b⟫ - ⟪rowOf f 1, c⟫) -
      ⟪rowOf f 1, a⟫ * (⟪rowOf f 0, b⟫ - ⟪rowOf f 0, c⟫) +
      (⟪rowOf f 0, b⟫ * ⟪rowOf f 1, c⟫ - ⟪rowOf f 0, c⟫ * ⟪rowOf f 1, b⟫)) * h₄

/-- **Per-quadruple witness, certificate-parameterized core**: if the two
identical-vanishing conditions cannot both hold for a quadruple, at least
one of the two constraint polynomials is nonzero as a polynomial.  This is
the polynomial-side form of the per-quadruple certificate. -/
theorem detPoly_ne_zero_or_orthPoly_ne_zero_of_not_both_vanish
    {a b c e : EuclideanSpace ℝ ι}
    (hnb : ¬ ((∀ p q : EuclideanSpace ℝ ι,
          ⟪p, a - b⟫ * ⟪q, c - e⟫ - ⟪p, c - e⟫ * ⟪q, a - b⟫ = 0) ∧
        (∀ r : EuclideanSpace ℝ ι, ⟪r, a + b - (c + e)⟫ * ⟪r, a - b⟫ = 0))) :
    detPoly a b c e ≠ 0 ∨ orthPoly a b c e ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨hd, ho⟩ := h
  refine hnb ⟨?_, ?_⟩
  · intro p q
    have h0 := congrArg (eval fun ki ↦ ![p, q] ki.1 ki.2) hd
    rw [map_zero] at h0
    simpa [detPoly, eval_innerPoly_rows] using h0
  · intro r
    have h0 := congrArg (eval fun ki ↦ ![r, 0] ki.1 ki.2) ho
    rw [map_zero] at h0
    simpa [orthPoly, eval_innerPoly_rows] using h0

/-- **Per-triple witness**: if the collinearity constraint polynomial of a
triple — the determinant polynomial of the difference vectors `b - a` and
`c - a` — vanishes as a polynomial, the triple is collinear upstairs.
Polynomial-side form of the parallelism lemma for triples; contrapositively,
a non-collinear triple has a nonzero constraint polynomial. -/
theorem collinear_of_detPoly_eq_zero
    {a b c : EuclideanSpace ℝ ι}
    (hd : detPoly b a c a = 0) :
    Collinear ℝ ({a, b, c} : Set (EuclideanSpace ℝ ι)) := by
  have hvan : ∀ p q : EuclideanSpace ℝ ι,
      ⟪p, b - a⟫ * ⟪q, c - a⟫ - ⟪p, c - a⟫ * ⟪q, b - a⟫ = 0 := by
    intro p q
    have h0 := congrArg (eval fun ki ↦ ![p, q] ki.1 ki.2) hd
    rw [map_zero] at h0
    simpa [detPoly, eval_innerPoly_rows] using h0
  rw [collinear_iff_of_mem (Set.mem_insert a {b, c})]
  rcases exists_smul_eq_of_forall_inner_det_eq_zero hvan with ⟨t, ht⟩ | ⟨t, ht⟩
  · -- `c - a = t • (b - a)`: the line through `a` with direction `b - a`.
    refine ⟨b - a, fun p hp => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by rw [vadd_eq_add]; module⟩
    · exact ⟨t, by rw [vadd_eq_add]; linear_combination (norm := module) ht⟩
  · -- `b - a = t • (c - a)`: the line through `a` with direction `c - a`.
    refine ⟨c - a, fun p hp => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨t, by rw [vadd_eq_add]; linear_combination (norm := module) ht⟩
    · exact ⟨1, by rw [vadd_eq_add]; module⟩

/-- **Per-quadruple certificate, rigidity-parameterized core**: for two
distinct pairs (the first nondegenerate) subject to a line-rigidity
hypothesis, the two identical-vanishing conditions that a
bisector-coincidence under projection would force cannot both hold: the
projected-determinant form (parallelism) and the orthogonality form
(midpoint relation) are not simultaneously identically zero over all row
vectors.

This is the input the existence-of-a-generic-projection argument consumes:
for each off-pair quadruple, at least one of the two constraint polynomials
in the projection entries is not identically zero, so a generic projection
avoids the coincidence.  Contrapositive assembly of the coefficient lemma,
the parallelism lemma, and the supplied line rigidity. -/
theorem nearEnemy_offPair_not_both_vanish_of_rigid
    {ι : Type*} [Fintype ι]
    {a b c e : EuclideanSpace ℝ ι}
    (hrigid : a + b = c + e → (∃ t : ℝ, c - e = t • (a - b)) →
      ({a, b} : Set (EuclideanSpace ℝ ι)) = {c, e})
    (hab : a ≠ b)
    (hne : ({a, b} : Set (EuclideanSpace ℝ ι)) ≠ {c, e}) :
    ¬ ((∀ p q : EuclideanSpace ℝ ι,
          ⟪p, a - b⟫ * ⟪q, c - e⟫ - ⟪p, c - e⟫ * ⟪q, a - b⟫ = 0) ∧
        (∀ r : EuclideanSpace ℝ ι, ⟪r, a + b - (c + e)⟫ * ⟪r, a - b⟫ = 0)) := by
  rintro ⟨hdet, hinn⟩
  have habv : a - b ≠ 0 := sub_ne_zero.mpr hab
  -- Coefficient lemma: identical vanishing of the orthogonality form forces
  -- equal midpoints upstairs.
  have hmid : a + b = c + e :=
    sub_eq_zero.mp (eq_zero_of_forall_inner_mul_inner_eq_zero habv hinn)
  -- Parallelism lemma: identical vanishing of the determinant form forces
  -- parallel difference vectors upstairs (the swap branch has a nonzero
  -- scalar, so it inverts).
  have hpar : ∃ t : ℝ, c - e = t • (a - b) := by
    rcases exists_smul_eq_of_forall_inner_det_eq_zero hdet with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨t, ht⟩
    · have ht0 : t ≠ 0 := by
        rintro rfl
        rw [zero_smul] at ht
        exact habv ht
      exact ⟨t⁻¹, by rw [ht, smul_smul, inv_mul_cancel₀ ht0, one_smul]⟩
  -- Line rigidity closes the contradiction.
  exact hne (hrigid hmid hpar)

/-- **Per-quadruple certificate, general-position form**: the
rigidity-parameterized core instantiated with no-three-collinear
rigidity. -/
theorem nearEnemy_noThreeCollinear_offPair_not_both_vanish
    {ι : Type*} [Fintype ι]
    {a b c e : EuclideanSpace ℝ ι}
    (hgp : a ≠ b → c ≠ a → c ≠ b →
      ¬ Collinear ℝ ({a, b, c} : Set (EuclideanSpace ℝ ι)))
    (hab : a ≠ b)
    (hne : ({a, b} : Set (EuclideanSpace ℝ ι)) ≠ {c, e}) :
    ¬ ((∀ p q : EuclideanSpace ℝ ι,
          ⟪p, a - b⟫ * ⟪q, c - e⟫ - ⟪p, c - e⟫ * ⟪q, a - b⟫ = 0) ∧
        (∀ r : EuclideanSpace ℝ ι, ⟪r, a + b - (c + e)⟫ * ⟪r, a - b⟫ = 0)) :=
  nearEnemy_offPair_not_both_vanish_of_rigid
    (nearEnemy_noThreeCollinear_parallel_midpoint_eq_samePair hgp) hab hne

end NearEnemy

open NearEnemy in
theorem solution {G : Finset (EuclideanSpace ℝ ι)}
    (hG : ∀ p₁ ∈ G, ∀ p₂ ∈ G, ∀ p₃ ∈ G, p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
      ¬ Collinear ℝ ({p₁, p₂, p₃} : Set (EuclideanSpace ℝ ι))) :
    ∃ T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
      ProjectionGeneric T G ∧
      (∀ p₁ ∈ G, ∀ p₂ ∈ G, ∀ p₃ ∈ G, p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
        ¬ Collinear ℝ ({T p₁, T p₂, T p₃} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
      (∀ p₁ ∈ G, ∀ p₂ ∈ G, ∀ p₃ ∈ G, ∀ p₄ ∈ G,
        p₁ ≠ p₂ → p₁ ≠ p₃ → p₁ ≠ p₄ → p₂ ≠ p₃ → p₂ ≠ p₄ → p₃ ≠ p₄ →
        ¬ EuclideanGeometry.Cospherical
          ({T p₁, T p₂, T p₃, T p₄} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
      ∀ a ∈ G, ∀ b ∈ G, ∀ c ∈ G, ∀ e ∈ G,
        a - b ≠ c - e → a - b ≠ -(c - e) →
        dist (T a) (T b) ≠ dist (T c) (T e) := by
  -- Constraint index sets.
  set Quads : Finset ((EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ×
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :=
    (G.offDiag ×ˢ G.offDiag).filter
      (fun pq ↦ ({pq.1.1, pq.1.2} : Set (EuclideanSpace ℝ ι)) ≠
        {pq.2.1, pq.2.2}) with hQuads
  set Triples : Finset (EuclideanSpace ℝ ι ×
      EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :=
    (G ×ˢ G ×ˢ G).filter
      (fun p ↦ p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2) with hTriples
  set Quads4 : Finset ((EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ×
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :=
    ((G ×ˢ G) ×ˢ (G ×ˢ G)).filter
      (fun q ↦ q.1.1 ≠ q.1.2 ∧ q.1.1 ≠ q.2.1 ∧ q.1.1 ≠ q.2.2 ∧
        q.1.2 ≠ q.2.1 ∧ q.1.2 ≠ q.2.2 ∧ q.2.1 ≠ q.2.2) with hQuads4
  set DPairs : Finset ((EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ×
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :=
    ((G ×ˢ G) ×ˢ (G ×ˢ G)).filter
      (fun q ↦ q.1.1 - q.1.2 ≠ q.2.1 - q.2.2 ∧
        q.1.1 - q.1.2 ≠ -(q.2.1 - q.2.2)) with hDPairs
  -- Per-constraint nonzero witnesses.
  have hwq_ne : ∀ pq ∈ Quads, quadWitness pq ≠ 0 := by
    intro pq hpq
    rw [hQuads, Finset.mem_filter, Finset.mem_product] at hpq
    obtain ⟨⟨h1, h2⟩, hne⟩ := hpq
    rw [Finset.mem_offDiag] at h1 h2
    rw [quadWitness]
    by_cases hdet : detPoly pq.1.1 pq.1.2 pq.2.1 pq.2.2 ≠ 0
    · rwa [if_pos hdet]
    · rw [if_neg hdet]
      push Not at hdet
      rcases detPoly_ne_zero_or_orthPoly_ne_zero_of_not_both_vanish
        (nearEnemy_noThreeCollinear_offPair_not_both_vanish
          (fun hab' hca hcb =>
            hG _ h1.1 _ h1.2.1 _ h2.1 hab' hca.symm hcb.symm)
          h1.2.2 hne) with h | h
      · exact absurd hdet h
      · exact h
  have htr_ne : ∀ tr ∈ Triples, detPoly tr.2.1 tr.1 tr.2.2 tr.1 ≠ 0 := by
    intro tr htr hd
    rw [hTriples, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product] at htr
    obtain ⟨⟨h1, h2, h3⟩, h12, h13, h23⟩ := htr
    exact hG _ h1 _ h2 _ h3 h12 h13 h23 (collinear_of_detPoly_eq_zero hd)
  have hq4_ne : ∀ q ∈ Quads4, circPoly q.1.1 q.1.2 q.2.1 q.2.2 ≠ 0 := by
    intro q hq
    rw [hQuads4, Finset.mem_filter, Finset.mem_product, Finset.mem_product,
      Finset.mem_product] at hq
    obtain ⟨⟨⟨ha, hb⟩, hc, he⟩, h12, h13, h14, h23, h24, h34⟩ := hq
    exact circPoly_ne_zero_of_noThreeCollinear h12 h14
      (hG _ ha _ hb _ hc h12 h13 h23)
      (hG _ hb _ hc _ he h23 h24 h34)
  have hdp_ne : ∀ q ∈ DPairs,
      distClassPoly (q.1.1 - q.1.2) (q.2.1 - q.2.2) ≠ 0 := by
    intro q hq
    rw [hDPairs, Finset.mem_filter] at hq
    exact distClassPoly_ne_zero (fun h ↦ hq.2.1 h.symm)
      (fun h ↦ hq.2.2 (by rw [h, neg_neg]))
  -- The master polynomial and its nonvanishing point.
  set master : MvPolynomial (Fin 2 × ι) ℝ :=
    ((((∏ ab ∈ G.offDiag, innerPoly 0 (ab.1 - ab.2)) *
        ∏ pq ∈ Quads, quadWitness pq) *
      ∏ tr ∈ Triples, detPoly tr.2.1 tr.1 tr.2.2 tr.1) *
      ∏ q ∈ Quads4, circPoly q.1.1 q.1.2 q.2.1 q.2.2) *
      ∏ q ∈ DPairs, distClassPoly (q.1.1 - q.1.2) (q.2.1 - q.2.2) with hmaster
  have hmaster_ne : master ≠ 0 := by
    rw [hmaster]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (Finset.prod_ne_zero_iff.mpr fun ab hab ↦
        innerPoly_ne_zero (Finset.mem_offDiag.mp hab).2.2)
      (Finset.prod_ne_zero_iff.mpr hwq_ne))
      (Finset.prod_ne_zero_iff.mpr htr_ne))
      (Finset.prod_ne_zero_iff.mpr hq4_ne))
      (Finset.prod_ne_zero_iff.mpr hdp_ne)
  have hpoint : ∃ f : Fin 2 × ι → ℝ, eval f master ≠ 0 := by
    by_contra h
    push Not at h
    exact hmaster_ne (MvPolynomial.funext fun f ↦ by simpa using h f)
  obtain ⟨f, hf⟩ := hpoint
  -- All factor evaluations are nonzero at `f`.
  rw [hmaster, map_mul, map_mul, map_mul, map_mul, map_prod, map_prod,
    map_prod, map_prod, map_prod] at hf
  have hpairs_eval : ∀ ab ∈ G.offDiag, eval f (innerPoly 0 (ab.1 - ab.2)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (left_ne_zero_of_mul (left_ne_zero_of_mul
      (left_ne_zero_of_mul (left_ne_zero_of_mul hf))))
  have hquads_eval : ∀ pq ∈ Quads, eval f (quadWitness pq) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul (left_ne_zero_of_mul
      (left_ne_zero_of_mul (left_ne_zero_of_mul hf))))
  have htriples_eval : ∀ tr ∈ Triples,
      eval f (detPoly tr.2.1 tr.1 tr.2.2 tr.1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul (left_ne_zero_of_mul
      (left_ne_zero_of_mul hf)))
  have hquads4_eval : ∀ q ∈ Quads4,
      eval f (circPoly q.1.1 q.1.2 q.2.1 q.2.2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul (left_ne_zero_of_mul hf))
  have hdpairs_eval : ∀ q ∈ DPairs,
      eval f (distClassPoly (q.1.1 - q.1.2) (q.2.1 - q.2.2)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hf)
  -- The projection with rows read off `f`.
  refine ⟨rowMap (rowOf f), ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- Injectivity / nondegeneracy.
    intro a ha b hb hab hT0
    have hmem : (a, b) ∈ G.offDiag := Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩
    apply hpairs_eval (a, b) hmem
    rw [eval_innerPoly]
    have h0 : rowMap (rowOf f) (a - b) 0 = 0 := by rw [hT0]; rfl
    rwa [rowMap_apply] at h0
  · -- Coincidence-avoidance.
    intro a ha b hb c hc e he hab hce hne hbad
    obtain ⟨⟨t, hpar⟩, horth⟩ := hbad
    have hmem : ((a, b), (c, e)) ∈ Quads := by
      rw [hQuads, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩,
        Finset.mem_offDiag.mpr ⟨hc, he, hce⟩⟩, hne⟩
    apply hquads_eval _ hmem
    rw [quadWitness]
    have hcomp : ∀ k : Fin 2, ⟪rowOf f k, c - e⟫ = t * ⟪rowOf f k, a - b⟫ := by
      intro k
      have h := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v k) hpar
      simpa [rowMap_apply, PiLp.smul_apply, smul_eq_mul, inner_sub_right]
        using h
    by_cases hdet : detPoly a b c e ≠ 0
    · rw [if_pos hdet]
      simp only [detPoly, map_sub, map_mul, eval_innerPoly]
      rw [hcomp 0, hcomp 1]
      ring
    · rw [if_neg hdet]
      simp only [orthPoly, map_add, map_mul, eval_innerPoly]
      have hexp : ⟪rowMap (rowOf f) (a + b - (c + e)),
          rowMap (rowOf f) (a - b)⟫ =
          ⟪rowOf f 0, a + b - (c + e)⟫ * ⟪rowOf f 0, a - b⟫ +
            ⟪rowOf f 1, a + b - (c + e)⟫ * ⟪rowOf f 1, a - b⟫ := by
        rw [PiLp.inner_apply]
        simp only [Fin.sum_univ_two, RCLike.inner_apply, rowMap_apply,
          starRingEnd_apply, star_trivial, inner_add_right, inner_sub_right]
        ring
      rw [← hexp, horth]
  · -- Triple non-collinearity downstairs.
    intro p₁ h₁ p₂ h₂ p₃ h₃ h₁₂ h₁₃ h₂₃ hcol
    have hmem : (p₁, p₂, p₃) ∈ Triples := by
      rw [hTriples, Finset.mem_filter, Finset.mem_product, Finset.mem_product]
      exact ⟨⟨h₁, h₂, h₃⟩, h₁₂, h₁₃, h₂₃⟩
    apply htriples_eval _ hmem
    rw [collinear_iff_of_mem (Set.mem_insert _ _)] at hcol
    obtain ⟨v, hv⟩ := hcol
    obtain ⟨r₂, hr₂⟩ := hv _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    obtain ⟨r₃, hr₃⟩ := hv _
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
    have hcomp₂ : ∀ k : Fin 2,
        ⟪rowOf f k, p₂⟫ - ⟪rowOf f k, p₁⟫ = r₂ * v k := by
      intro k
      have hT : rowMap (rowOf f) (p₂ - p₁) = r₂ • v := by
        rw [map_sub, hr₂, vadd_eq_add]
        abel
      have hk := congrArg (fun u : EuclideanSpace ℝ (Fin 2) ↦ u k) hT
      simpa [rowMap_apply, PiLp.smul_apply, smul_eq_mul] using hk
    have hcomp₃ : ∀ k : Fin 2,
        ⟪rowOf f k, p₃⟫ - ⟪rowOf f k, p₁⟫ = r₃ * v k := by
      intro k
      have hT : rowMap (rowOf f) (p₃ - p₁) = r₃ • v := by
        rw [map_sub, hr₃, vadd_eq_add]
        abel
      have hk := congrArg (fun u : EuclideanSpace ℝ (Fin 2) ↦ u k) hT
      simpa [rowMap_apply, PiLp.smul_apply, smul_eq_mul] using hk
    simp only [detPoly, map_sub, map_mul, eval_innerPoly, inner_sub_right]
    rw [hcomp₂ 0, hcomp₂ 1, hcomp₃ 0, hcomp₃ 1]
    ring
  · -- Quadruple non-concyclicity downstairs.
    intro p₁ h₁ p₂ h₂ p₃ h₃ p₄ h₄ h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄ hcos
    obtain ⟨z, ρ, hz⟩ := hcos
    have hmem : ((p₁, p₂), (p₃, p₄)) ∈ Quads4 := by
      rw [hQuads4, Finset.mem_filter, Finset.mem_product, Finset.mem_product,
        Finset.mem_product]
      exact ⟨⟨⟨h₁, h₂⟩, h₃, h₄⟩, h₁₂, h₁₃, h₁₄, h₂₃, h₂₄, h₃₄⟩
    exact hquads4_eval _ hmem (eval_circPoly_eq_zero_of_dist_eq
      (hz _ (Set.mem_insert _ _))
      (hz _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
      (hz _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_insert _ _))))
      (hz _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ rfl)))))
  · -- Distance-class separation downstairs.
    intro a ha b hb c hc e he hvw hvw' hdist
    have hmem : ((a, b), (c, e)) ∈ DPairs := by
      rw [hDPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_product,
        Finset.mem_product]
      exact ⟨⟨⟨ha, hb⟩, hc, he⟩, hvw, hvw'⟩
    exact hdpairs_eval _ hmem (eval_distClassPoly_eq_zero_of_dist_eq hdist)
