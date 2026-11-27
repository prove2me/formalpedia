-- Prove2me | solution 1 for GlobalTheory.column_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:37:48.445195+00:00
-- url     : https://prove2.me/submissions/d3706bb2-ba10-49b4-8d3a-c12461ac27a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ColumnDegreeLe
import Theorems.Thm_GlobalTheory_eval_rowOps_eq
import Theorems.Thm_GlobalTheory_eval_scale_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K σ : Type*} [Field K] [CharZero K] [DecidableEq σ] {p n : ℕ} (z : Fin p × Fin n → σ) (hz : Function.Injective z)
    (P : MvPolynomial σ K) (lam : Fin p → ℕ)
    (hrow : ∀ a, ∀ m ∈ P.support, ∑ k, m (z (a, k)) = lam a)
    (hinv : ∀ a b : Fin p, a < b → ∀ t : K, bind₁ (fun s => X s + ∑ k, if s = z (b, k) then C t * X (z (a, k)) else 0) P = P)
    (S : Finset (Fin n)) : ∀ m ∈ P.support,
      ∑ a, ∑ k ∈ S, m (z (a, k)) ≤ ∑ a ∈ Finset.univ.filter (fun a : Fin p => (a : ℕ) < S.card), lam a := by
  classical
  intro m0 hm0
  by_cases hpr : p ≤ S.card
  · have hfil : Finset.univ.filter (fun a : Fin p => (a : ℕ) < S.card) = Finset.univ := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact lt_of_lt_of_le a.isLt hpr
    rw [hfil]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← hrow a m0 hm0]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ S)
  push Not at hpr
  let Z : Finset σ := (Finset.univ ×ˢ S).image z
  let w : σ → ℕ := fun s => if s ∈ Z then 1 else 0
  have hwz : ∀ a k, w (z (a, k)) = if k ∈ S then 1 else 0 := by
    intro a k
    show (if z (a, k) ∈ Finset.image z (Finset.univ ×ˢ S) then 1 else 0) = _
    have hm : z (a, k) ∈ Finset.image z (Finset.univ ×ˢ S) ↔ k ∈ S := by
      rw [hz.mem_finset_image]
      simp
    by_cases hk : k ∈ S
    · rw [if_pos (hm.2 hk), if_pos hk]
    · rw [if_neg (fun h => hk (hm.1 h)), if_neg hk]
  have he : ∀ m : σ →₀ ℕ, ∑ s ∈ m.support, w s * m s = ∑ a, ∑ k ∈ S, m (z (a, k)) := by
    intro m
    have h1 : ∑ s ∈ m.support, w s * m s = ∑ s ∈ m.support, if s ∈ Z then m s else 0 := by
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [w]
      split_ifs <;> simp
    have h2 : ∑ s ∈ m.support ∩ Z, m s = ∑ s ∈ Z, m s := by
      refine Finset.sum_subset Finset.inter_subset_right fun s hsZ hs => ?_
      by_contra h
      exact hs (Finset.mem_inter.2 ⟨Finsupp.mem_support_iff.2 h, hsZ⟩)
    rw [h1, Finset.sum_ite_mem, h2, Finset.sum_image hz.injOn, Finset.sum_product]
  have hlow : ∀ m ∈ P.support, ∑ a ∈ Finset.univ.filter (fun a : Fin p => (a : ℕ) < S.card),
      ∑ k ∈ S, m (z (a, k)) ≤ ∑ a ∈ Finset.univ.filter (fun a : Fin p => (a : ℕ) < S.card), lam a := by
    intro m hm
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← hrow a m hm]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ S)
  by_contra hcon
  push Not at hcon
  set j := ∑ a, ∑ k ∈ S, m0 (z (a, k)) with hj
  let R : MvPolynomial σ K :=
    ∑ m ∈ P.support.filter (fun m => ∑ a, ∑ k ∈ S, m (z (a, k)) = j), monomial m (coeff m P)
  have hR0 : coeff m0 R ≠ 0 := by
    have hmem : m0 ∈ P.support.filter (fun m => ∑ a, ∑ k ∈ S, m (z (a, k)) = j) :=
      Finset.mem_filter.2 ⟨hm0, rfl⟩
    simp only [R, coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq' _ _ _, if_pos hmem]
    exact mem_support_iff.1 hm0
  let top : Fin S.card → Fin p := Fin.castLE hpr.le
  have htop : Function.Injective top := Fin.castLE_injective _
  let ee : Fin S.card → Fin n := S.orderEmbOfFin rfl
  have hee : ∀ k ∈ S, ∃ i, ee i = k := by
    intro k hk
    have : k ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hk
    exact this
  let D : MvPolynomial σ K :=
    (Matrix.of fun a b : Fin S.card => (X (z (top a, ee b)) : MvPolynomial σ K)).det
  have hevD : ∀ y : σ → K, eval y D = (Matrix.of fun a b : Fin S.card => y (z (top a, ee b))).det := by
    intro y
    simp only [D]
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp [RingHom.mapMatrix_apply]
  have hD : D ≠ 0 := by
    let x0 : σ → K := fun s => if ∃ a : Fin S.card, s = z (top a, ee a) then 1 else 0
    have hx0 : ∀ a b, x0 (z (top a, ee b)) = if a = b then 1 else 0 := by
      intro a b
      by_cases hab : a = b
      · subst hab
        simp only [x0]
        exact if_pos ⟨a, rfl⟩
      · simp only [x0, if_neg hab]
        rw [if_neg]
        rintro ⟨a', h⟩
        have h' := hz h
        simp only [Prod.mk.injEq] at h'
        exact hab ((htop h'.1).trans ((S.orderEmbOfFin rfl).injective h'.2).symm)
    intro h0
    have h1 := hevD x0
    rw [h0, map_zero] at h1
    have h2 : (Matrix.of fun a b : Fin S.card => x0 (z (top a, ee b))) = 1 := by
      ext a b
      rw [Matrix.of_apply, hx0, Matrix.one_apply]
    rw [h2, Matrix.det_one] at h1
    exact zero_ne_one h1
  let Q : (σ → K) → Polynomial K := fun y => ∑ m ∈ P.support,
    Polynomial.monomial (∑ s ∈ m.support, w s * m s) (coeff m P * ∏ s ∈ m.support, y s ^ m s)
  have hQcoeff : ∀ y : σ → K, (Q y).coeff j = ∑ m ∈ P.support,
      if ∑ a, ∑ k ∈ S, m (z (a, k)) = j then coeff m P * ∏ s ∈ m.support, y s ^ m s else 0 := by
    intro y
    simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, he]
  have key : ∀ x : σ → K, eval x D ≠ 0 → eval x R = 0 := by
    intro x hdet
    let M : Matrix (Fin S.card) (Fin S.card) K := Matrix.of fun a b => x (z (top a, ee b))
    have hMu : IsUnit M.det := isUnit_iff_ne_zero.2 (by rw [← hevD]; exact hdet)
    let v : Fin p → Fin S.card → K := fun b i => x (z (b, ee i))
    let c : Fin p × Fin p → K := fun q =>
      if h : (q.1 : ℕ) < S.card then -(Matrix.vecMul (v q.2) M⁻¹) ⟨q.1, h⟩ else 0
    let B : Finset (Fin p) := Finset.univ.filter fun b : Fin p => S.card ≤ (b : ℕ)
    let T : Finset (Fin p × Fin p) := (Finset.univ.image top) ×ˢ B
    have hT : ∀ q ∈ T, (q.1 : ℕ) < S.card ∧ S.card ≤ (q.2 : ℕ) := by
      intro q hq
      simp only [T, B, Finset.mem_product, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_filter] at hq
      obtain ⟨⟨a, ha⟩, hb⟩ := hq
      refine ⟨?_, hb⟩
      rw [← ha]
      exact a.isLt
    let op : (σ → K) → σ → K := fun y s =>
      y s + ∑ q ∈ T, ∑ k, if s = z (q.2, k) then c q * y (z (q.1, k)) else 0
    let sc : K → (σ → K) → σ → K := fun t y s => t ^ w s * y s
    have hcomm : ∀ t y, op (sc t y) = sc t (op y) := by
      intro t y
      funext s
      simp only [op, sc]
      rw [mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs with h
      · rw [h, hwz, hwz]
        ring
      · simp
    have hsum : ∀ b : Fin p, ∀ i, ∑ a, (Matrix.vecMul (v b) M⁻¹) a * M a i = v b i := by
      intro b i
      have h := congrFun (show Matrix.vecMul (Matrix.vecMul (v b) M⁻¹) M = v b by
        rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hMu, Matrix.vecMul_one]) i
      simpa [Matrix.vecMul, dotProduct] using h
    have hx'0 : ∀ b : Fin p, S.card ≤ (b : ℕ) → ∀ k ∈ S, op x (z (b, k)) = 0 := by
      intro b hb k hk
      obtain ⟨i, rfl⟩ := hee k hk
      have hinner : ∀ q : Fin p × Fin p, (∑ k, if z (b, ee i) = z (q.2, k)
          then c q * x (z (q.1, k)) else 0) = if b = q.2 then c q * x (z (q.1, ee i)) else 0 := by
        intro q
        simp only [hz.eq_iff, Prod.mk.injEq, ite_and]
        split_ifs with h
        · simp
        · simp
      simp only [op]
      rw [Finset.sum_congr rfl fun q _ => hinner q, Finset.sum_product]
      have hbB : b ∈ B := Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩
      simp only [Finset.sum_ite_eq, hbB, if_true]
      rw [Finset.sum_image fun a _ a' _ h => htop h]
      have hc : ∀ a : Fin S.card, c (top a, b) = -(Matrix.vecMul (v b) M⁻¹) a := by
        intro a
        simp only [c]
        rw [dif_pos (show ((top a : Fin p) : ℕ) < S.card from a.isLt)]
        rfl
      simp only [hc, neg_mul, Finset.sum_neg_distrib]
      have := hsum b i
      simp only [M, v, Matrix.of_apply] at this
      rw [this]
      ring
    have hQ : Q x = Q (op x) := by
      refine Polynomial.funext fun t => ?_
      rw [← eval_scale_eq w P x t, ← eval_scale_eq w P (op x) t]
      change eval (sc t x) P = eval (sc t (op x)) P
      rw [← hcomm]
      exact (eval_rowOps_eq z hz P hinv S.card c (sc t x) T hT).symm
    have hRx : eval x R = (Q x).coeff j := by
      rw [hQcoeff, ← Finset.sum_filter]
      simp only [R, map_sum, eval_monomial, Finsupp.prod]
    rw [hRx, hQ, hQcoeff]
    refine Finset.sum_eq_zero fun m hm => ?_
    split_ifs with hmj
    · have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun a : Fin p => (a : ℕ) < S.card) (fun a => ∑ k ∈ S, m (z (a, k)))
      have hup : ∑ a ∈ Finset.univ.filter (fun a : Fin p => ¬ (a : ℕ) < S.card),
          ∑ k ∈ S, m (z (a, k)) ≠ 0 := by
        intro h0
        have := hlow m hm
        omega
      obtain ⟨a, ha, ha0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hup
      obtain ⟨k, hk, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha0
      have hs : z (a, k) ∈ m.support := Finsupp.mem_support_iff.2 hk0
      have hza : op x (z (a, k)) = 0 :=
        hx'0 a (not_lt.1 (Finset.mem_filter.1 ha).2) k hk
      rw [Finset.prod_eq_zero hs (by rw [hza, zero_pow hk0]), mul_zero]
    · rfl
  have hRD : R * D = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero]
    by_cases hdet : eval x D = 0
    · rw [hdet, mul_zero]
    · rw [key x hdet, zero_mul]
  have hR : R = 0 := (mul_eq_zero.1 hRD).resolve_right hD
  exact hR0 (by rw [hR, coeff_zero])
end GlobalTheory
