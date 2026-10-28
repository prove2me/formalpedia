-- Prove2me | solution 2 for MatousekLP.DIntervals.transversal_two_d_sq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T05:56:11.094384+00:00
-- url     : https://prove2.me/submissions/d362d424-15e9-43ef-ab38-0070a76c71ac

import Mathlib
import Definitions.Def_MatousekLP_DIntervals_DInterval
import Definitions.Def_MatousekLP_Duality_Cones
import Theorems.Thm_MatousekLP_Duality_farkas_geometric

-- carved verbatim out of submission b7b76719-19e3-4776-bc57-e4266b445bda, lines 622-663

section
open Finset
open Finset MatousekLP.DIntervals
variable {d : ℕ}

noncomputable def lefts (J : DInterval d) : Finset ℝ := Finset.univ.image J.left

lemma card_lefts_le (J : DInterval d) : (lefts J).card ≤ d := by
  have := Finset.card_image_le (s := (Finset.univ : Finset (Fin d))) (f := J.left)
  simpa [lefts] using this

end

section
open Finset
open Matrix MatousekLP.Duality

theorem farkas_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∃ x : Fin n → ℝ, 0 ≤ x ∧ A *ᵥ x = b) ↔ ∀ y : Fin m → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b := by
  constructor
  · rintro ⟨x, hx, rfl⟩ y hy
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
    exact dotProduct_nonneg_of_nonneg hx hy
  · intro h
    set a : Fin n → EuclideanSpace ℝ (Fin m) := fun j => WithLp.toLp 2 (fun i => A i j)
    rcases MatousekLP.Duality.farkas_geometric a (WithLp.toLp 2 b) with ⟨hb, -⟩ | ⟨⟨y, hy, hyb⟩, -⟩
    · obtain ⟨t, ht, hbt⟩ := hb
      refine ⟨t, fun i => ht i, ?_⟩
      have hb' : b = ∑ j, t j • (fun i => A i j) := by
        have := congrArg WithLp.ofLp hbt
        simpa [a, WithLp.ofLp_sum, WithLp.ofLp_smul] using this
      rw [hb']
      funext i
      simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
    · exfalso
      set y' : Fin m → ℝ := WithLp.ofLp y
      have hy' : 0 ≤ Aᵀ *ᵥ y' := by
        intro j
        have := hy j
        simp only [a] at this
        have hy_eq : y = WithLp.toLp 2 y' := rfl
        rw [hy_eq, EuclideanSpace.inner_toLp_toLp] at this
        simpa [mulVec, dotProduct, transpose_apply, mul_comm] using this
      have := h y' hy'
      have hy_eq : y = WithLp.toLp 2 y' := rfl
      rw [hy_eq, EuclideanSpace.inner_toLp_toLp] at hyb
      simp only [star_trivial] at hyb
      rw [dotProduct_comm] at hyb
      linarith

theorem farkas_eq_fintype {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ) :
    (∃ x : ι → ℝ, 0 ≤ x ∧ A *ᵥ x = b) ↔ ∀ y : Fin m → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b := by
  set e := Fintype.equivFin ι
  set A' : Matrix (Fin m) (Fin (Fintype.card ι)) ℝ := A.submatrix id e.symm
  have hmul : ∀ x : ι → ℝ, A' *ᵥ (x ∘ e.symm) = A *ᵥ x := by
    intro x; funext i
    simp only [A', mulVec, dotProduct, submatrix_apply, id, Function.comp]
    exact Equiv.sum_comp e.symm (fun j => A i j * x j)
  have htr : ∀ y : Fin m → ℝ, A'ᵀ *ᵥ y = (Aᵀ *ᵥ y) ∘ e.symm := by
    intro y; funext j; simp [A', mulVec, dotProduct, transpose_apply]
  have hnonneg : ∀ y : Fin m → ℝ, (0 ≤ A'ᵀ *ᵥ y ↔ 0 ≤ Aᵀ *ᵥ y) := by
    intro y; rw [htr]
    constructor
    · intro h j; simpa using h (e j)
    · intro h j; exact h _
  rw [show (∀ y : Fin m → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b) ↔
      (∀ y : Fin m → ℝ, 0 ≤ A'ᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b) from
      forall_congr' fun y => by rw [hnonneg]]
  rw [← farkas_eq A' b]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x ∘ e.symm, fun j => hx _, hmul x⟩
  · rintro ⟨x', hx', rfl⟩
    refine ⟨x' ∘ e, fun j => hx' _, ?_⟩
    rw [← hmul]; congr 1; funext j; simp

theorem farkas_eq_gen {ρ ι : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype ι] [DecidableEq ι]
    (A : Matrix ρ ι ℝ) (b : ρ → ℝ) :
    (∃ x : ι → ℝ, 0 ≤ x ∧ A *ᵥ x = b) ↔ ∀ y : ρ → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b := by
  set e := Fintype.equivFin ρ
  set A' : Matrix (Fin (Fintype.card ρ)) ι ℝ := A.submatrix e.symm id
  have h := farkas_eq_fintype A' (b ∘ e.symm)
  have hrow : ∀ x : ι → ℝ, A' *ᵥ x = (A *ᵥ x) ∘ e.symm := by
    intro x; funext r; simp [A', mulVec, dotProduct]
  have hcol : ∀ y' : Fin (Fintype.card ρ) → ℝ, A'ᵀ *ᵥ y' = Aᵀ *ᵥ (y' ∘ e) := by
    intro y'; funext j
    simp only [A', mulVec, dotProduct, transpose_apply, submatrix_apply, id, Function.comp]
    rw [← Equiv.sum_comp e (fun x => A (e.symm x) j * y' x)]
    simp
  have hdot : ∀ y' : Fin (Fintype.card ρ) → ℝ, y' ⬝ᵥ (b ∘ e.symm) = (y' ∘ e) ⬝ᵥ b := by
    intro y'
    simp only [dotProduct, Function.comp]
    rw [← Equiv.sum_comp e (fun x => y' x * b (e.symm x))]
    simp
  constructor
  · rintro ⟨x, hx, rfl⟩ y hy
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
    exact dotProduct_nonneg_of_nonneg hx hy
  · intro hy
    obtain ⟨x, hx, hAx⟩ := h.mpr fun y' hy' => by
      rw [hcol] at hy'; rw [hdot]; exact hy _ hy'
    refine ⟨x, hx, ?_⟩
    funext r
    have := congrFun hAx (e r)
    rw [hrow] at this; simpa using this

theorem farkas_le_gen {ρ ι : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype ι] [DecidableEq ι]
    (A : Matrix ρ ι ℝ) (b : ρ → ℝ) :
    (∃ x : ι → ℝ, 0 ≤ x ∧ A *ᵥ x ≤ b) ↔ ∀ y : ρ → ℝ, 0 ≤ y → 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b := by
  have h := farkas_eq_gen (fromCols A (1 : Matrix ρ ρ ℝ)) b
  have hleft : (∃ x : ι → ℝ, 0 ≤ x ∧ A *ᵥ x ≤ b) ↔
      ∃ z : ι ⊕ ρ → ℝ, 0 ≤ z ∧ fromCols A 1 *ᵥ z = b := by
    constructor
    · rintro ⟨x, hx, hAx⟩
      refine ⟨Sum.elim x (b - A *ᵥ x), fun j => ?_, ?_⟩
      · rcases j with j | j
        · exact hx j
        · simpa using hAx j
      · rw [fromCols_mulVec_sumElim, one_mulVec]; abel
    · rintro ⟨z, hz, hzb⟩
      refine ⟨fun j => z (Sum.inl j), fun j => hz _, ?_⟩
      have hz' : z = Sum.elim (fun j => z (Sum.inl j)) (fun j => z (Sum.inr j)) := by
        funext j; rcases j <;> rfl
      rw [hz', fromCols_mulVec_sumElim, one_mulVec] at hzb
      intro i
      have h1 := congrFun hzb i
      have h2 := hz (Sum.inr i)
      simp only [Pi.add_apply, Pi.zero_apply] at h1 h2
      linarith
  have hright : (∀ y : ρ → ℝ, 0 ≤ (fromCols A (1 : Matrix ρ ρ ℝ))ᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b) ↔
      ∀ y : ρ → ℝ, 0 ≤ y → 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b := by
    refine forall_congr' fun y => ?_
    rw [transpose_fromCols, transpose_one]
    constructor
    · intro hh hy hAy
      refine hh fun j => ?_
      rcases j with j | j
      · simpa [fromRows_mulVec] using hAy j
      · simpa [fromRows_mulVec] using hy j
    · intro hh hpos
      exact hh (fun i => by simpa [fromRows_mulVec] using hpos (Sum.inr i))
        (fun j => by simpa [fromRows_mulVec] using hpos (Sum.inl j))
  rw [hleft, h, hright]

end

section
open Finset
open Finset MatousekLP.DIntervals
variable {d : ℕ}

lemma left_in_other (J J' : DInterval d) (h : (J.toSet ∩ J'.toSet).Nonempty) :
    (∃ p ∈ lefts J, p ∈ J'.toSet) ∨ (∃ p ∈ lefts J', p ∈ J.toSet) := by
  obtain ⟨x, hx, hx'⟩ := h
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
  obtain ⟨k', hk'⟩ := Set.mem_iUnion.mp hx'
  rcases le_total (J'.left k') (J.left k) with hle | hle
  · left
    exact ⟨J.left k, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      Set.mem_iUnion.mpr ⟨k', hle, hk.1.trans hk'.2⟩⟩
  · right
    exact ⟨J'.left k', Finset.mem_image_of_mem _ (Finset.mem_univ _),
      Set.mem_iUnion.mpr ⟨k, hle, hk'.1.trans hk.2⟩⟩

lemma lefts_subset (J : DInterval d) : lefts J ⊆ J.endpoints :=
  Finset.subset_union_left

end

section
open Finset
open Finset MatousekLP.DIntervals

lemma quantile (E : Finset ℝ) (x : ℝ → ℝ) (hx : ∀ p ∈ E, 0 ≤ x p) (δ : ℝ) (hδ : 0 < δ) :
    ∃ X : Finset ℝ, (X.card : ℝ) ≤ (∑ p ∈ E, x p) / δ ∧
      ∀ a b : ℝ, a ≤ b → δ ≤ ∑ p ∈ E.filter (fun p => a ≤ p ∧ p ≤ b), x p →
        ∃ q ∈ X, a ≤ q ∧ q ≤ b := by
  classical
  set W := ∑ p ∈ E, x p
  set F : ℝ → ℝ := fun t => ∑ p ∈ E.filter (fun p => p ≤ t), x p
  set G : ℝ → ℝ := fun t => ∑ p ∈ E.filter (fun p => p < t), x p
  set K := ⌊W / δ⌋₊
  set S : ℕ → Finset ℝ := fun k => E.filter (fun q => (k : ℝ) * δ ≤ F q)
  set q : ℕ → ℝ := fun k => if h : (S k).Nonempty then (S k).min' h else 0
  have hsub_nonneg : ∀ T ⊆ E, 0 ≤ ∑ p ∈ T, x p := fun T hT =>
    Finset.sum_nonneg fun p hp => hx p (hT hp)
  have hW0 : 0 ≤ W := hsub_nonneg E le_rfl
  refine ⟨(Finset.Icc 1 K).image q, ?_, fun a b hab hmass => ?_⟩
  · calc ((Finset.Icc 1 K).image q).card ≤ ((Finset.Icc 1 K).card : ℝ) := by
          exact_mod_cast Finset.card_image_le
      _ = K := by simp
      _ ≤ W / δ := Nat.floor_le (div_nonneg hW0 hδ.le)
  · -- split `F b = G a + mass`
    have hsplit : F b = G a + ∑ p ∈ E.filter (fun p => a ≤ p ∧ p ≤ b), x p := by
      simp only [F, G]
      rw [← Finset.sum_filter_add_sum_filter_not (E.filter fun p => p ≤ b) (fun p => p < a),
        Finset.filter_filter, Finset.filter_filter]
      congr 1
      · exact Finset.sum_congr (Finset.filter_congr fun p _ => ⟨fun h => h.2,
          fun h => ⟨(h.le.trans hab), h⟩⟩) fun _ _ => rfl
      · exact Finset.sum_congr (Finset.filter_congr fun p _ => ⟨fun h => ⟨not_lt.mp h.2, h.1⟩,
          fun h => ⟨h.2, not_lt.mpr h.1⟩⟩) fun _ _ => rfl
    have hG0 : 0 ≤ G a := hsub_nonneg _ (Finset.filter_subset _ _)
    have hFW : F b ≤ W := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun p hp _ => hx p hp
    set k := ⌊G a / δ⌋₊ + 1
    have hk1 : G a < k * δ := by
      have := Nat.lt_floor_add_one (G a / δ)
      rw [div_lt_iff₀ hδ] at this
      simpa [k] using this
    have hk2 : (k : ℝ) * δ ≤ G a + δ := by
      have := Nat.floor_le (div_nonneg hG0 hδ.le)
      rw [le_div_iff₀ hδ] at this
      simp only [k, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      linarith
    have hkF : (k : ℝ) * δ ≤ F b := by linarith
    have hkK : k ∈ Finset.Icc 1 K := by
      refine Finset.mem_Icc.mpr ⟨by simp [k], Nat.le_floor ?_⟩
      rw [le_div_iff₀ hδ]; linarith
    -- the last point of `E` up to `b`
    have hEb : (E.filter fun p => p ≤ b).Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      have : (E.filter fun p => a ≤ p ∧ p ≤ b) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        have : p ∈ E.filter (fun p => p ≤ b) :=
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.2⟩
        rw [hne] at this; simp at this
      rw [this, Finset.sum_empty] at hmass; linarith
    set q₂ := (E.filter fun p => p ≤ b).max' hEb
    have hq₂E : q₂ ∈ E.filter (fun p => p ≤ b) := Finset.max'_mem _ _
    have hFq₂ : F q₂ = F b := by
      simp only [F]
      congr 1
      ext p
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hp, hpq⟩; exact ⟨hp, hpq.trans (Finset.mem_filter.mp hq₂E).2⟩
      · rintro ⟨hp, hpb⟩; exact ⟨hp, Finset.le_max' _ p (Finset.mem_filter.mpr ⟨hp, hpb⟩)⟩
    have hSk : (S k).Nonempty := ⟨q₂, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq₂E).1,
      by rw [hFq₂]; exact hkF⟩⟩
    have hqk : q k = (S k).min' hSk := dif_pos hSk
    refine ⟨q k, Finset.mem_image_of_mem _ hkK, ?_, ?_⟩
    · by_contra hlt; push_neg at hlt
      have hmem : (S k).min' hSk ∈ S k := Finset.min'_mem _ _
      rw [← hqk] at hmem
      have hFq : (k : ℝ) * δ ≤ F (q k) := (Finset.mem_filter.mp hmem).2
      have : F (q k) ≤ G a := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          simp only [Finset.mem_filter] at hp ⊢
          exact ⟨hp.1, lt_of_le_of_lt hp.2 hlt⟩
        · intro p hp _; exact hx p (Finset.mem_filter.mp hp).1
      linarith
    · rw [hqk]
      exact (Finset.min'_le _ q₂ (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq₂E).1,
        by rw [hFq₂]; exact hkF⟩)).trans (Finset.mem_filter.mp hq₂E).2

open Classical Matrix in
theorem weights {d : ℕ} (hd : 1 ≤ d) (𝒥 : Finset (DInterval d))
    (h𝒥 : PairwiseIntersecting 𝒥) :
    ∃ x : ℝ → ℝ, (∀ p ∈ endpointSet 𝒥, 0 ≤ x p) ∧
      (∀ J ∈ 𝒥, 1 ≤ ∑ p ∈ (endpointSet 𝒥).filter (fun p => p ∈ J.toSet), x p) ∧
      ∑ p ∈ endpointSet 𝒥, x p ≤ 2 * d := by
  set E := endpointSet 𝒥
  -- the system `-Mx ≤ -1`, `∑ x ≤ 2d`, `x ≥ 0`
  set A : Matrix (𝒥 ⊕ Unit) E ℝ := Matrix.of fun r q =>
    Sum.elim (fun J : 𝒥 => if (q : ℝ) ∈ (J : DInterval d).toSet then (-1 : ℝ) else 0)
      (fun _ => (1 : ℝ)) r with hA
  set b : 𝒥 ⊕ Unit → ℝ := Sum.elim (fun _ => -1) (fun _ => 2 * d) with hb
  have hF := (farkas_le_gen A b).mpr (by
    intro y hy0 hAy
    set s := y (Sum.inr ())
    set yJ : 𝒥 → ℝ := fun J => y (Sum.inl J)
    have hyJ0 : ∀ J, 0 ≤ yJ J := fun J => hy0 (Sum.inl J)
    have hs0 : 0 ≤ s := hy0 (Sum.inr ())
    -- dual constraint at an endpoint
    have hdual : ∀ q : E, ∑ J : 𝒥, (if (q : ℝ) ∈ (J : DInterval d).toSet then yJ J else 0) ≤ s := by
      intro q
      have := hAy q
      simp only [hA, mulVec, dotProduct, transpose_apply, Matrix.of_apply, Fintype.sum_sum_type,
        Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, Finset.univ_unique, Finset.sum_singleton,
        one_mul] at this
      have h2 : ∑ J : 𝒥, (if (q : ℝ) ∈ (J : DInterval d).toSet then (-1 : ℝ) else 0) * y (Sum.inl J) =
          -∑ J : 𝒥, (if (q : ℝ) ∈ (J : DInterval d).toSet then yJ J else 0) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun J _ => by split_ifs <;> simp [yJ]
      rw [h2] at this
      linarith
    set Y := ∑ J : 𝒥, yJ J
    -- each row: `∑_{J'} y_{J'} [left endpoint of J in J'] ≤ d s`
    set I : 𝒥 → 𝒥 → ℝ := fun J J' =>
      if ∃ p ∈ lefts (J : DInterval d), p ∈ (J' : DInterval d).toSet then 1 else 0
    have hI0 : ∀ J J', 0 ≤ I J J' := fun J J' => by simp only [I]; split_ifs <;> norm_num
    have hrow : ∀ J : 𝒥, ∑ J', yJ J' * I J J' ≤ d * s := by
      intro J
      have hmemE : ∀ p ∈ lefts (J : DInterval d), p ∈ E := fun p hp =>
        Finset.mem_biUnion.mpr ⟨J, J.2, lefts_subset _ hp⟩
      calc ∑ J', yJ J' * I J J'
          ≤ ∑ J' : 𝒥, ∑ p ∈ lefts (J : DInterval d),
              (if p ∈ (J' : DInterval d).toSet then yJ J' else 0) := by
            refine Finset.sum_le_sum fun J' _ => ?_
            simp only [I]
            split_ifs with h
            · obtain ⟨p, hp, hpJ'⟩ := h
              rw [mul_one]
              refine le_trans ?_ (Finset.single_le_sum (f := fun p =>
                if p ∈ (J' : DInterval d).toSet then yJ J' else 0)
                (fun q _ => by split_ifs <;> simp [hyJ0 J']) hp)
              simp [hpJ']
            · rw [mul_zero]
              exact Finset.sum_nonneg fun q _ => by split_ifs <;> simp [hyJ0 J']
        _ = ∑ p ∈ lefts (J : DInterval d), ∑ J' : 𝒥,
              (if p ∈ (J' : DInterval d).toSet then yJ J' else 0) := Finset.sum_comm
        _ ≤ ∑ p ∈ lefts (J : DInterval d), s := by
            refine Finset.sum_le_sum fun p hp => ?_
            exact hdual ⟨p, hmemE p hp⟩
        _ = (lefts (J : DInterval d)).card * s := by simp
        _ ≤ d * s := by gcongr; exact_mod_cast card_lefts_le _
    have hsq : Y ^ 2 ≤ 2 * (Y * (d * s)) := by
      have hpair : ∀ J J' : 𝒥, 1 ≤ I J J' + I J' J := by
        intro J J'
        rcases left_in_other _ _ (h𝒥 _ J.2 _ J'.2) with h | h
        · have : I J J' = 1 := if_pos h
          linarith [hI0 J' J]
        · have : I J' J = 1 := if_pos h
          linarith [hI0 J J']
      calc Y ^ 2 = ∑ J, ∑ J', yJ J * yJ J' := by rw [sq, Finset.sum_mul_sum]
        _ ≤ ∑ J, ∑ J', yJ J * yJ J' * (I J J' + I J' J) :=
            Finset.sum_le_sum fun J _ => Finset.sum_le_sum fun J' _ =>
              le_mul_of_one_le_right (mul_nonneg (hyJ0 J) (hyJ0 J')) (hpair J J')
        _ = 2 * ∑ J, yJ J * ∑ J', yJ J' * I J J' := by
            have h1 : ∑ J, ∑ J', yJ J * yJ J' * (I J J' + I J' J) =
                ∑ J, ∑ J', yJ J * yJ J' * I J J' + ∑ J, ∑ J', yJ J * yJ J' * I J' J := by
              simp only [mul_add, Finset.sum_add_distrib]
            have h2 : ∑ J, ∑ J', yJ J * yJ J' * I J' J = ∑ J, ∑ J', yJ J * yJ J' * I J J' := by
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun J' _ => by ring
            have h3 : ∑ J, yJ J * ∑ J', yJ J' * I J J' = ∑ J, ∑ J', yJ J * yJ J' * I J J' := by
              simp only [Finset.mul_sum]
              exact Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun J' _ => by ring
            rw [h1, h2, h3]; ring
        _ ≤ 2 * ∑ J, yJ J * (d * s) := by
            gcongr with J
            · exact hyJ0 J
            · exact hrow J
        _ = 2 * (Y * (d * s)) := by rw [← Finset.sum_mul]
    have hY0 : 0 ≤ Y := Finset.sum_nonneg fun J _ => hyJ0 J
    have hY : Y ≤ 2 * d * s := by
      rcases hY0.lt_or_eq with hpos | hzero
      · nlinarith
      · rw [← hzero]; positivity
    simp only [hb, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.univ_unique, Finset.sum_singleton]
    have : ∑ J : 𝒥, y (Sum.inl J) * (-1) = -Y := by
      simp [Y, yJ, Finset.sum_neg_distrib]
    rw [this]
    have : y (Sum.inr default) = s := rfl
    rw [this]
    nlinarith)
  obtain ⟨x, hx0, hAx⟩ := hF
  set X : ℝ → ℝ := fun p => if h : p ∈ E then x ⟨p, h⟩ else 0
  have hsumE : ∀ f : ℝ → ℝ, ∑ q : E, f q = ∑ p ∈ E, f p := fun f => Finset.sum_coe_sort E f
  have hXq : ∀ q : E, X q = x q := fun q => by simp [X, q.2]
  refine ⟨X, fun p hp => ?_, fun J hJ => ?_, ?_⟩
  · simp only [X, dif_pos hp]; exact hx0 ⟨p, hp⟩
  · have := hAx (Sum.inl ⟨J, hJ⟩)
    simp only [hA, hb, mulVec, dotProduct, Matrix.of_apply, Sum.elim_inl, ite_mul, neg_one_mul,
      zero_mul] at this
    rw [Finset.sum_filter, ← hsumE (fun p => if p ∈ J.toSet then X p else 0)]
    have h2 : ∑ q : E, (if (q : ℝ) ∈ J.toSet then -x q else 0) =
        -∑ q : E, (if (q : ℝ) ∈ J.toSet then X q else 0) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun q _ => by split_ifs <;> simp [hXq]
    rw [h2] at this
    linarith
  · have := hAx (Sum.inr ())
    simp only [hA, hb, mulVec, dotProduct, Matrix.of_apply, Sum.elim_inr, one_mul] at this
    rw [← hsumE X]
    simpa [hXq] using this

theorem solution {d : ℕ} (hd : 1 ≤ d) (𝒥 : Finset (DInterval d))
    (h𝒥 : PairwiseIntersecting 𝒥) :
    ∃ X : Finset ℝ, X.card ≤ 2 * d ^ 2 ∧ ∀ J ∈ 𝒥, ∃ p ∈ X, p ∈ J.toSet := by
  classical
  obtain ⟨x, hx0, hxJ, hxW⟩ := weights hd 𝒥 h𝒥
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨X, hXcard, hXhit⟩ := quantile (endpointSet 𝒥) x hx0 (1 / d) (by positivity)
  refine ⟨X, ?_, fun J hJ => ?_⟩
  · have : (X.card : ℝ) ≤ 2 * d ^ 2 := by
      calc (X.card : ℝ) ≤ (∑ p ∈ endpointSet 𝒥, x p) / (1 / d) := hXcard
        _ = (∑ p ∈ endpointSet 𝒥, x p) * d := by field_simp
        _ ≤ 2 * d * d := by gcongr
        _ = 2 * d ^ 2 := by ring
    exact_mod_cast this
  · -- some component of `J` carries mass at least `1/d`
    set E := endpointSet 𝒥
    set mass : Fin d → ℝ := fun k =>
      ∑ p ∈ E.filter (fun p => J.left k ≤ p ∧ p ≤ J.right k), x p
    have hcover : 1 ≤ ∑ k, mass k := by
      refine (hxJ J hJ).trans ?_
      rw [Finset.sum_filter]
      simp only [mass, Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun p hp => ?_
      split_ifs with hpJ
      · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hpJ
        refine le_trans ?_ (Finset.single_le_sum (f := fun k =>
          if J.left k ≤ p ∧ p ≤ J.right k then x p else 0)
          (fun k _ => by split_ifs <;> simp [hx0 p hp]) (Finset.mem_univ k))
        simp [hk.1, hk.2]
      · exact Finset.sum_nonneg fun k _ => by split_ifs <;> simp [hx0 p hp]
    have hk : ∃ k, 1 / (d : ℝ) ≤ mass k := by
      by_contra hall; push_neg at hall
      have : ∑ k, mass k < ∑ _k : Fin d, 1 / (d : ℝ) :=
        Finset.sum_lt_sum_of_nonempty ⟨⟨0, hd⟩, Finset.mem_univ _⟩ fun k _ => hall k
      simp at this
      field_simp at this
      linarith
    obtain ⟨k, hk⟩ := hk
    obtain ⟨q, hqX, hq1, hq2⟩ := hXhit _ _ (J.left_le_right k) hk
    exact ⟨q, hqX, Set.mem_iUnion.mpr ⟨k, hq1, hq2⟩⟩

end
