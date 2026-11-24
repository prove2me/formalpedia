-- Prove2me | solution 1 for IntConeFPT.section_B3_unboundedness
-- status  : ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-24T12:29:18.470925+00:00
-- url     : https://prove2.me/submissions/1577d538-1548-49a9-b968-094493a83108

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem

set_option autoImplicit false

open OnlineCRS.Combine
open IntConeFPT

namespace IntConeFPT.SectionB3Proof

/-! ## 1. Exact Rational Fourier–Motzkin Elimination and Farkas' Lemma -/

private lemma sum_ite_subtype {m : ℕ} (S : Finset (Fin m)) (g : {i : Fin m // i ∈ S} → ℚ) :
    ∑ i : Fin m, (if h : i ∈ S then g ⟨i, h⟩ else 0) = ∑ x : S, g x := by
  calc ∑ i : Fin m, (if h : i ∈ S then g ⟨i, h⟩ else 0)
    _ = ∑ i ∈ S, (if h : i ∈ S then g ⟨i, h⟩ else 0) := by
        symm
        refine Finset.sum_subset (Finset.subset_univ S) fun i _ hi => ?_
        exact dif_neg hi
    _ = ∑ x ∈ S.attach, (if h : x.1 ∈ S then g ⟨x.1, h⟩ else 0) :=
        (Finset.sum_attach S fun i => if h : i ∈ S then g ⟨i, h⟩ else 0).symm
    _ = ∑ x : S, g x := by
        rw [← Finset.univ_eq_attach]
        refine Finset.sum_congr rfl fun x _ => ?_
        exact dif_pos x.2

lemma fm_exists_or_cert :
    ∀ (n m : ℕ) (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ),
      (∃ x : Fin n → ℚ, ∀ i, ∑ j, A i j * x j ≤ b i) ∨
      (∃ y : Fin m → ℚ, (∀ i, 0 ≤ y i) ∧ (∀ j, ∑ i, y i * A i j = 0) ∧ ∑ i, y i * b i < 0)
  | 0, m, _, b => by
    by_cases h : ∀ i : Fin m, 0 ≤ b i
    · exact Or.inl ⟨Fin.elim0, fun i => by simp [h i]⟩
    · push_neg at h
      obtain ⟨i₀, hi₀⟩ := h
      refine Or.inr ⟨Pi.single i₀ 1, ?_, ?_, ?_⟩
      · intro i
        by_cases hi : i = i₀ <;> simp [hi]
      · intro j
        exact j.elim0
      · simp only [Pi.single_apply, ite_mul, one_mul, zero_mul]
        rw [Finset.sum_ite_eq' Finset.univ i₀]
        simp [hi₀]
  | n + 1, m, A, b => by
    let a : Fin m → ℚ := fun i => A i 0
    let A' : Fin m → Fin n → ℚ := fun i j => A i j.succ
    let I0 : Finset (Fin m) := Finset.univ.filter fun i => a i = 0
    let Ip : Finset (Fin m) := Finset.univ.filter fun i => 0 < a i
    let Im : Finset (Fin m) := Finset.univ.filter fun i => a i < 0
    let Idx := {i : Fin m // i ∈ I0} ⊕ ({p : Fin m // p ∈ Ip} × {q : Fin m // q ∈ Im})
    let e : Idx ≃ Fin (Fintype.card Idx) := Fintype.equivFin Idx
    let m' : ℕ := Fintype.card Idx
    let B : Fin m' → Fin n → ℚ := fun r j =>
      match e.symm r with
      | Sum.inl i => A' i.1 j
      | Sum.inr pq => (-a pq.2.1) * A' pq.1.1 j + a pq.1.1 * A' pq.2.1 j
    let d : Fin m' → ℚ := fun r =>
      match e.symm r with
      | Sum.inl i => b i.1
      | Sum.inr pq => (-a pq.2.1) * b pq.1.1 + a pq.1.1 * b pq.2.1
    rcases fm_exists_or_cert n m' B d with ⟨x', hx'⟩ | ⟨y', hy'_nonneg, hy'_A, hy'_b⟩
    · let U : Fin m → ℚ := fun p => (b p - ∑ j, A' p j * x' j) / a p
      let L : Fin m → ℚ := fun q => (b q - ∑ j, A' q j * x' j) / a q
      have hLU : ∀ p ∈ Ip, ∀ q ∈ Im, L q ≤ U p := by
        intro p hp q hq
        have hap : 0 < a p := (Finset.mem_filter.mp hp).2
        have haq : a q < 0 := (Finset.mem_filter.mp hq).2
        have hnq : 0 < -a q := neg_pos.mpr haq
        let r : Fin m' := e (Sum.inr (⟨p, hp⟩, ⟨q, hq⟩))
        have hr := hx' r
        have hB : ∑ j, B r j * x' j =
            (-a q) * (∑ j, A' p j * x' j) + a p * (∑ j, A' q j * x' j) := by
          simp only [r, B, Equiv.symm_apply_apply]
          simp_rw [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
        have hd : d r = (-a q) * b p + a p * b q := by
          simp only [r, d, Equiv.symm_apply_apply]
        rw [hB, hd] at hr
        have hcross : 0 ≤ (-a q) * (b p - ∑ j, A' p j * x' j) +
            a p * (b q - ∑ j, A' q j * x' j) := by
          have hid : (-a q) * (b p - ∑ j, A' p j * x' j) + a p * (b q - ∑ j, A' q j * x' j) =
              ((-a q) * b p + a p * b q) -
                ((-a q) * (∑ j, A' p j * x' j) + a p * (∑ j, A' q j * x' j)) := by ring
          rw [hid, sub_nonneg]
          exact hr
        have hprod : 0 < (-a q) * a p := mul_pos hnq hap
        have hdiv : (b q - ∑ j, A' q j * x' j) / a q ≤
            (b p - ∑ j, A' p j * x' j) / a p := by
          rw [← sub_nonneg]
          have hap0 : a p ≠ 0 := hap.ne'
          have haq0 : a q ≠ 0 := haq.ne
          have hid : U p - L q =
              ((-a q) * (b p - ∑ j, A' p j * x' j) +
                a p * (b q - ∑ j, A' q j * x' j)) / ((-a q) * a p) := by
            simp only [U, L]
            rw [div_sub_div _ _ hap0 haq0]
            have hden : a p * a q = -((-a q) * a p) := by ring
            have hnum : (b p - ∑ j, A' p j * x' j) * a q - a p * (b q - ∑ j, A' q j * x' j) =
                -((-a q) * (b p - ∑ j, A' p j * x' j) + a p * (b q - ∑ j, A' q j * x' j)) := by ring
            rw [hnum, hden, neg_div_neg_eq]
          rw [hid]
          exact div_nonneg hcross hprod.le
        exact hdiv
      have hex : ∃ x₀ : ℚ,
          (∀ p ∈ Ip, x₀ ≤ U p) ∧ (∀ q ∈ Im, L q ≤ x₀) := by
        by_cases hp : Ip.Nonempty
        · refine ⟨Ip.inf' hp U, fun p hp' => Finset.inf'_le _ hp', fun q hq => ?_⟩
          exact Finset.le_inf' hp U fun p hp' => hLU p hp' q hq
        · rw [Finset.not_nonempty_iff_eq_empty] at hp
          by_cases hq : Im.Nonempty
          · refine ⟨Im.sup' hq L, fun p hp' => ?_, fun q hq' => Finset.le_sup' L hq'⟩
            simp [hp] at hp'
          · rw [Finset.not_nonempty_iff_eq_empty] at hq
            exact ⟨0, fun p hp' => by simp [hp] at hp', fun q hq' => by simp [hq] at hq'⟩
      obtain ⟨x₀, hxU, hxL⟩ := hex
      refine Or.inl ⟨Fin.cons x₀ x', fun i => ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      change a i * x₀ + ∑ j, A' i j * x' j ≤ b i
      rcases lt_trichotomy (a i) 0 with hai | hai | hai
      · have hi : i ∈ Im := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hai⟩
        have hli := hxL i hi
        simp only [L] at hli
        have hmul : a i * x₀ ≤ a i * ((b i - ∑ j, A' i j * x' j) / a i) :=
          mul_le_mul_of_nonpos_left hli hai.le
        rw [mul_div_cancel₀ _ hai.ne] at hmul
        linarith
      · have hi : i ∈ I0 := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hai⟩
        let r : Fin m' := e (Sum.inl ⟨i, hi⟩)
        have hr := hx' r
        simp only [B, d, r, Equiv.symm_apply_apply] at hr
        rw [hai, zero_mul, zero_add]
        exact hr
      · have hi : i ∈ Ip := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hai⟩
        have hui := hxU i hi
        simp only [U] at hui
        have hmul : a i * x₀ ≤ a i * ((b i - ∑ j, A' i j * x' j) / a i) :=
          mul_le_mul_of_nonneg_left hui hai.le
        rw [mul_div_cancel₀ _ hai.ne'] at hmul
        linarith
    · let w0 : Fin m → ℚ := fun i =>
        if h : i ∈ I0 then y' (e (Sum.inl ⟨i, h⟩)) else 0
      let wpm : Fin m → Fin m → ℚ := fun p q =>
        if hp : p ∈ Ip then if hq : q ∈ Im then y' (e (Sum.inr (⟨p, hp⟩, ⟨q, hq⟩))) else 0 else 0
      let y : Fin m → ℚ := fun i =>
        w0 i + (∑ q : Fin m, wpm i q * (-a q)) + (∑ p : Fin m, wpm p i * a p)
      have hpull : ∀ f : Fin m → ℚ,
          ∑ i, y i * f i = ∑ r : Fin m', y' r *
            (match e.symm r with
            | Sum.inl i => f i.1
            | Sum.inr pq => (-a pq.2.1) * f pq.1.1 + a pq.1.1 * f pq.2.1) := by
        intro f
        have h0 : ∑ i, w0 i * f i =
            ∑ i : {i : Fin m // i ∈ I0}, y' (e (Sum.inl i)) * f i.1 := by
          trans ∑ i : Fin m, (if h : i ∈ I0 then y' (e (Sum.inl ⟨i, h⟩)) * f i else 0)
          · refine Finset.sum_congr rfl fun i _ => ?_
            simp only [w0]
            split_ifs <;> ring
          · exact sum_ite_subtype I0 fun i => y' (e (Sum.inl i)) * f i.1
        have h12 :
            (∑ i, (∑ q, wpm i q * (-a q)) * f i) + (∑ i, (∑ p, wpm p i * a p) * f i) =
            ∑ pq : {p : Fin m // p ∈ Ip} × {q : Fin m // q ∈ Im},
              y' (e (Sum.inr pq)) * ((-a pq.2.1) * f pq.1.1 + a pq.1.1 * f pq.2.1) := by
          have hL : ∑ i, (∑ q, wpm i q * (-a q)) * f i =
              ∑ p, ∑ q, wpm p q * ((-a q) * f p) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun q _ => by ring
          have hR : ∑ i, (∑ p, wpm p i * a p) * f i =
              ∑ p, ∑ q, wpm p q * (a p * f q) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun p _ => by ring
          rw [hL, hR, ← Finset.sum_add_distrib]
          have hcomb :
              (∑ p, ((∑ q, wpm p q * ((-a q) * f p)) + (∑ q, wpm p q * (a p * f q)))) =
              ∑ p, ∑ q, wpm p q * ((-a q) * f p + a p * f q) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun q _ => by ring
          rw [hcomb]
          have hinner : ∀ p (hp : p ∈ Ip),
              (∑ q, wpm p q * ((-a q) * f p + a p * f q)) =
              ∑ q : {q : Fin m // q ∈ Im},
                y' (e (Sum.inr (⟨p, hp⟩, q))) * ((-a q.1) * f p + a p * f q.1) := by
            intro p hp
            trans ∑ q : Fin m, (if hq : q ∈ Im then
                y' (e (Sum.inr (⟨p, hp⟩, ⟨q, hq⟩))) * ((-a q) * f p + a p * f q) else 0)
            · refine Finset.sum_congr rfl fun q _ => ?_
              simp only [wpm, dif_pos hp]
              split_ifs <;> ring
            · exact sum_ite_subtype Im fun q =>
                y' (e (Sum.inr (⟨p, hp⟩, q))) * ((-a q.1) * f p + a p * f q.1)
          have houter :
              (∑ p, ∑ q, wpm p q * ((-a q) * f p + a p * f q)) =
              ∑ p : {p : Fin m // p ∈ Ip}, ∑ q : {q : Fin m // q ∈ Im},
                y' (e (Sum.inr (p, q))) * ((-a q.1) * f p.1 + a p.1 * f q.1) := by
            have hstep : ∀ p : Fin m,
                (∑ q, wpm p q * ((-a q) * f p + a p * f q)) =
                if hp : p ∈ Ip then
                  ∑ q : {q : Fin m // q ∈ Im},
                    y' (e (Sum.inr (⟨p, hp⟩, q))) * ((-a q.1) * f p + a p * f q.1) else 0 := by
              intro p
              by_cases hp : p ∈ Ip
              · rw [dif_pos hp, hinner p hp]
              · rw [dif_neg hp]
                refine Finset.sum_eq_zero fun q _ => ?_
                simp [wpm, hp]
            simp_rw [hstep]
            exact sum_ite_subtype Ip fun p =>
              ∑ q : {q : Fin m // q ∈ Im},
                y' (e (Sum.inr (p, q))) * ((-a q.1) * f p.1 + a p.1 * f q.1)
          rw [houter, Fintype.sum_prod_type]
        have hrhs : ∑ r : Fin m', y' r *
              (match e.symm r with
              | Sum.inl i => f i.1
              | Sum.inr pq => (-a pq.2.1) * f pq.1.1 + a pq.1.1 * f pq.2.1) =
            (∑ i : {i : Fin m // i ∈ I0}, y' (e (Sum.inl i)) * f i.1) +
            ∑ pq : {p : Fin m // p ∈ Ip} × {q : Fin m // q ∈ Im},
              y' (e (Sum.inr pq)) * ((-a pq.2.1) * f pq.1.1 + a pq.1.1 * f pq.2.1) := by
          rw [← Equiv.sum_comp e]
          simp only [Idx, Equiv.symm_apply_apply, Fintype.sum_sum_type]
        calc ∑ i, y i * f i
          _ = ∑ i, (w0 i * f i + ((∑ q, wpm i q * (-a q)) * f i + (∑ p, wpm p i * a p) * f i)) := by
              refine Finset.sum_congr rfl fun i _ => by simp only [y]; ring
          _ = (∑ i, w0 i * f i) + ((∑ i, (∑ q, wpm i q * (-a q)) * f i) +
                (∑ i, (∑ p, wpm p i * a p) * f i)) := by
              simp only [Finset.sum_add_distrib]
          _ = _ := by rw [h0, h12, hrhs]
      refine Or.inr ⟨y, ?_, ?_, ?_⟩
      · intro i
        have hw0 : 0 ≤ w0 i := by
          simp only [w0]
          split_ifs
          · exact hy'_nonneg _
          · exact le_rfl
        have h1 : 0 ≤ ∑ q : Fin m, wpm i q * (-a q) := by
          refine Finset.sum_nonneg fun q _ => ?_
          simp only [wpm]
          split_ifs with hp hq
          · have haq : a q < 0 := (Finset.mem_filter.mp hq).2
            exact mul_nonneg (hy'_nonneg _) (neg_nonneg.mpr haq.le)
          · simp
          · simp
        have h2 : 0 ≤ ∑ p : Fin m, wpm p i * a p := by
          refine Finset.sum_nonneg fun p _ => ?_
          simp only [wpm]
          split_ifs with hp hq
          · have hap : 0 < a p := (Finset.mem_filter.mp hp).2
            exact mul_nonneg (hy'_nonneg _) hap.le
          · simp
          · simp
        exact add_nonneg (add_nonneg hw0 h1) h2
      · intro j
        refine Fin.cases ?_ ?_ j
        · change ∑ i, y i * a i = 0
          rw [hpull a]
          refine Finset.sum_eq_zero fun r _ => ?_
          cases hr : e.symm r with
          | inl i =>
            have ha0 : a i.1 = 0 := (Finset.mem_filter.mp i.2).2
            simp [hr, ha0]
          | inr pq =>
            simp only [hr]
            ring
        · intro j'
          change ∑ i, y i * A' i j' = 0
          rw [hpull (fun i => A' i j')]
          have hBeq : ∀ r : Fin m',
              (match e.symm r with
              | Sum.inl i => A' i.1 j'
              | Sum.inr pq => (-a pq.2.1) * A' pq.1.1 j' + a pq.1.1 * A' pq.2.1 j') =
              B r j' := fun r => rfl
          simp_rw [hBeq]
          exact hy'_A j'
      · rw [hpull b]
        have hdeq : ∀ r : Fin m',
            (match e.symm r with
            | Sum.inl i => b i.1
            | Sum.inr pq => (-a pq.2.1) * b pq.1.1 + a pq.1.1 * b pq.2.1) = d r :=
          fun r => rfl
        simp_rw [hdeq]
        exact hy'_b

lemma farkas_hom_rat (m n : ℕ) (A : Fin m → Fin n → ℚ) (c : Fin n → ℚ) :
    (∃ d : Fin n → ℚ, (∀ i, ∑ j, A i j * d j ≤ 0) ∧ ∑ j, c j * d j < 0) ∨
    (∃ y : Fin m → ℚ, (∀ i, 0 ≤ y i) ∧ ∀ j, ∑ i, y i * A i j = -c j) := by
  let b' : Fin (m + 1) → ℚ := Fin.snoc (fun _ => 0) (-1)
  rcases fm_exists_or_cert n (m + 1) (Fin.snoc A c) b' with
    ⟨d, hd⟩ | ⟨y', hy'_nonneg, hy'_A, hy'_b⟩
  · refine Or.inl ⟨d, fun i => ?_, ?_⟩
    · simpa [b', Fin.snoc_castSucc] using hd i.castSucc
    · have hc := hd (Fin.last m)
      simp only [b', Fin.snoc_last] at hc
      linarith
  · rw [Fin.sum_univ_castSucc] at hy'_b
    have hb0 : ∀ i : Fin m, y' i.castSucc * b' i.castSucc = 0 := by
      intro i
      simp [b', Fin.snoc_castSucc]
    simp only [hb0, Finset.sum_const_zero, zero_add, b', Fin.snoc_last] at hy'_b
    have hylast : 0 < y' (Fin.last m) := by linarith
    refine Or.inr ⟨fun i => y' i.castSucc / y' (Fin.last m), ?_, ?_⟩
    · intro i
      exact div_nonneg (hy'_nonneg _) hylast.le
    · intro j
      have hj := hy'_A j
      rw [Fin.sum_univ_castSucc] at hj
      simp only [Fin.snoc_castSucc, Fin.snoc_last] at hj
      calc ∑ i : Fin m, (y' i.castSucc / y' (Fin.last m)) * A i j
        _ = (∑ i : Fin m, y' i.castSucc * A i j) / y' (Fin.last m) := by
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl fun i _ => by ring
        _ = (- (y' (Fin.last m) * c j)) / y' (Fin.last m) := by
            rw [eq_neg_of_add_eq_zero_left hj]
        _ = - c j := by
            have hne : y' (Fin.last m) ≠ 0 := hylast.ne'
            field_simp [hne]

lemma farkas_hom_rat_fintype {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → κ → ℚ) (c : κ → ℚ) :
    (∃ d : κ → ℚ, (∀ i, ∑ j, A i j * d j ≤ 0) ∧ ∑ j, c j * d j < 0) ∨
    (∃ y : ι → ℚ, (∀ i, 0 ≤ y i) ∧ ∀ j, ∑ i, y i * A i j = -c j) := by
  let eι := Fintype.equivFin ι
  let eκ := Fintype.equivFin κ
  rcases farkas_hom_rat (Fintype.card ι) (Fintype.card κ)
      (fun i j => A (eι.symm i) (eκ.symm j)) (fun j => c (eκ.symm j)) with
    ⟨d', hd'⟩ | ⟨y', hy'_nonneg, hy'_A⟩
  · refine Or.inl ⟨fun j => d' (eκ j), fun i => ?_, ?_⟩
    · have hi := hd'.1 (eι i)
      simp only [Equiv.symm_apply_apply] at hi
      rw [Fintype.sum_equiv eκ (fun j => A i j * d' (eκ j))
          (fun k => A i (eκ.symm k) * d' k) (fun j => by simp)]
      exact hi
    · have hc := hd'.2
      rw [Fintype.sum_equiv eκ (fun j => c j * d' (eκ j))
          (fun k => c (eκ.symm k) * d' k) (fun j => by simp)]
      exact hc
  · refine Or.inr ⟨fun i => y' (eι i), fun i => hy'_nonneg (eι i), fun j => ?_⟩
    have hj := hy'_A (eκ j)
    simp only [Equiv.symm_apply_apply] at hj
    rw [Fintype.sum_equiv eι (fun i => y' (eι i) * A i j)
        (fun k => y' k * A (eι.symm k) j) (fun i => by simp)]
    exact hj

/-! ## 2. Uniform Box Bound, Finiteness of Active Pairs, and Local Recession -/

lemma exists_uniform_box (I : Instance) (hI : I.Valid) :
    ∃ M : ℕ, ∀ t, ∀ p ∈ I.P t, InBox M p := by
  choose R hR using fun t => (Metric.isBounded_iff_subset_closedBall (0 : (Fin I.d → ℝ) × (Fin I.k → ℝ))).mp
    (hI.bounded t)
  refine ⟨Nat.ceil (∑ t, max (R t) 0), fun t p hp => ?_⟩
  have hdist : dist p 0 ≤ R t := Metric.mem_closedBall.mp (hR t hp)
  have hnorm : ‖p‖ ≤ R t := by simpa [dist_zero_right] using hdist
  have hRM : R t ≤ (Nat.ceil (∑ s, max (R s) 0) : ℝ) := by
    have h1 : R t ≤ max (R t) 0 := le_max_left _ _
    have h2 : max (R t) 0 ≤ ∑ s, max (R s) 0 :=
      Finset.single_le_sum (f := fun s => max (R s) 0) (fun s _ => le_max_right _ _) (Finset.mem_univ t)
    exact le_trans (le_trans h1 h2) (Nat.le_ceil _)
  refine ⟨fun i => ?_, fun j => ?_⟩
  · calc |p.1 i| = ‖p.1 i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖p.1‖ := norm_le_pi_norm p.1 i
      _ ≤ ‖p‖ := norm_fst_le p
      _ ≤ _ := le_trans hnorm hRM
  · calc |p.2 j| = ‖p.2 j‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖p.2‖ := norm_le_pi_norm p.2 j
      _ ≤ ‖p‖ := norm_snd_le p
      _ ≤ _ := le_trans hnorm hRM

lemma activePairs_finite (I : Instance) (hI : I.Valid) :
    ({tx : Fin I.τ × (Fin I.d → ℤ) | (fun i => (tx.2 i : ℝ)) ∈ I.Px tx.1}).Finite := by
  obtain ⟨M, hM⟩ := exists_uniform_box I hI
  let box : Finset (Fin I.τ × (Fin I.d → ℤ)) :=
    Finset.univ ×ˢ Fintype.piFinset (fun _ : Fin I.d => Finset.Icc (-(M : ℤ)) (M : ℤ))
  refine box.finite_toSet.subset fun tx htx => ?_
  rcases htx with ⟨p, hp, hpx⟩
  have hbx := (hM tx.1 p hp).1
  rw [Finset.mem_coe, Finset.mem_product]
  refine ⟨Finset.mem_univ _, Fintype.mem_piFinset.mpr fun i => ?_⟩
  rw [Finset.mem_Icc]
  have hi : |(tx.2 i : ℝ)| ≤ (M : ℝ) := by
    have := hbx i
    have hx : p.1 i = (tx.2 i : ℝ) := congrFun hpx i
    simpa [hx] using this
  have hiZ : |(tx.2 i : ℤ)| ≤ (M : ℤ) := by exact_mod_cast hi
  exact abs_le.mp hiZ

lemma local_recession_zero (I : Instance) (hI : I.Valid) (t : Fin I.τ) (x : Fin I.d → ℤ)
    (hx : (fun i => (x i : ℝ)) ∈ I.Px t) (w : Fin I.k → ℝ)
    (hw : ∀ i : Fin (I.m t), ∑ r, (I.Bloc t i r : ℝ) * w r ≤ 0) :
    w = 0 := by
  obtain ⟨M, hM⟩ := exists_uniform_box I hI
  rcases hx with ⟨⟨x₀, u₀⟩, hp₀, hpx₀⟩
  change x₀ = (fun i => (x i : ℝ)) at hpx₀
  subst hpx₀
  have hmem : ∀ α : ℝ, 0 ≤ α → ((fun i => (x i : ℝ)), u₀ + α • w) ∈ I.P t := by
    intro α hα i
    have hi₀ := hp₀ i
    have hwi := hw i
    have hsum : ∑ r, (I.Bloc t i r : ℝ) * (u₀ r + α * w r) =
        (∑ r, (I.Bloc t i r : ℝ) * u₀ r) + α * (∑ r, (I.Bloc t i r : ℝ) * w r) := by
      simp_rw [mul_add, Finset.sum_add_distrib, mul_left_comm, ← Finset.mul_sum]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsum]
    nlinarith
  ext r
  by_contra hne
  have habs_pos : 0 < |w r| := abs_pos.mpr hne
  let α : ℝ := ((M : ℝ) + |u₀ r| + 1) / |w r|
  have hα : 0 ≤ α := by positivity
  have hbx := (hM t _ (hmem α hα)).2 r
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hbx
  have htri : |α * w r| - |u₀ r| ≤ |u₀ r + α * w r| := by
    have := abs_sub_abs_le_abs_sub (α * w r) (-u₀ r)
    simpa [abs_neg, sub_neg_eq_add, add_comm] using this
  have hprod : |α * w r| = (M : ℝ) + |u₀ r| + 1 := by
    rw [abs_mul, abs_of_nonneg hα]
    simp only [α, div_mul_cancel₀ _ habs_pos.ne']
  linarith

/-! ## 3. Rational Polynomial Evaluation and Multiplicity Linearity Helpers -/

def ratEvalF (I : Instance) (t : Fin I.τ) (x : Fin I.d → ℤ) : ℚ :=
  ∑ j : Fin (monomials I.d (I.deg t)).length,
    I.coeff t j * ∏ i, (x i : ℚ) ^ ((monomials I.d (I.deg t)).get j i)

lemma ratEvalF_cast_real (I : Instance) (t : Fin I.τ) (x : Fin I.d → ℤ) :
    ((ratEvalF I t x : ℚ) : ℝ) = I.f t (fun i => (x i : ℝ)) := by
  unfold ratEvalF Instance.f
  push_cast
  rfl

lemma aggr_add {d k : ℕ} (μ₁ μ₂ : Gen d k →₀ ℕ) :
    aggr (μ₁ + μ₂) = aggr μ₁ + aggr μ₂ := by
  unfold aggr
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by
    simp only [Nat.cast_add, add_smul])

lemma aggr_nsmul {d k : ℕ} (m : ℕ) (μ : Gen d k →₀ ℕ) :
    aggr (m • μ) = (m : ℝ) • aggr μ := by
  induction m with
  | zero => simp [aggr]
  | succ m ih =>
    rw [add_nsmul, one_nsmul, aggr_add, ih]
    have h1 : aggr μ = (1 : ℝ) • aggr μ := (one_smul ℝ _).symm
    rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul]

lemma aggr_sum {d k : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Gen d k →₀ ℕ) :
    aggr (∑ i ∈ s, f i) = ∑ i ∈ s, aggr (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [aggr]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, aggr_add, ih]

lemma aggr_single {d k : ℕ} (g : Gen d k) (n : ℕ) :
    aggr (Finsupp.single g n) = (n : ℝ) • g.toReal := by
  unfold aggr
  exact Finsupp.sum_single_index (by simp)

lemma count_add {d k : ℕ} (μ₁ μ₂ : Gen d k →₀ ℕ) :
    count (μ₁ + μ₂) = count μ₁ + count μ₂ := by
  unfold count
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

lemma count_nsmul {d k : ℕ} (m : ℕ) (μ : Gen d k →₀ ℕ) :
    count (m • μ) = m * count μ := by
  induction m with
  | zero => simp [count]
  | succ m ih => rw [add_nsmul, one_nsmul, count_add, ih]; ring

lemma count_sum {d k : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Gen d k →₀ ℕ) :
    count (∑ i ∈ s, f i) = ∑ i ∈ s, count (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [count]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, count_add, ih]

lemma count_single {d k : ℕ} (g : Gen d k) (n : ℕ) :
    count (Finsupp.single g n) = n := by
  unfold count
  exact Finsupp.sum_single_index rfl

lemma costOf_add {d k : ℕ} (f : (Fin d → ℝ) → ℝ) (μ₁ μ₂ : Gen d k →₀ ℕ) :
    costOf f (μ₁ + μ₂) = costOf f μ₁ + costOf f μ₂ := by
  unfold costOf
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring)

lemma costOf_nsmul {d k : ℕ} (f : (Fin d → ℝ) → ℝ) (m : ℕ) (μ : Gen d k →₀ ℕ) :
    costOf f (m • μ) = (m : ℝ) * costOf f μ := by
  induction m with
  | zero => simp [costOf]
  | succ m ih =>
    rw [add_nsmul, one_nsmul, costOf_add, ih]
    push_cast
    ring

lemma costOf_sum {d k : ℕ} (f : (Fin d → ℝ) → ℝ) {ι : Type*} (s : Finset ι)
    (h : ι → Gen d k →₀ ℕ) :
    costOf f (∑ i ∈ s, h i) = ∑ i ∈ s, costOf f (h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [costOf]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, costOf_add, ih]

lemma costOf_single {d k : ℕ} (f : (Fin d → ℝ) → ℝ) (g : Gen d k) (n : ℕ) :
    costOf f (Finsupp.single g n) = (n : ℝ) * f (fun i => (g.1 i : ℝ)) := by
  unfold costOf
  exact Finsupp.sum_single_index (by simp)

/-! ## 4. Reverse Direction: Homogeneous Negative-Cost Certificate Implies Unboundedness -/

lemma unbounded_of_hom_neg (I : Instance) (hfeas : ∃ μ, I.Feasible μ)
    (hrec : ∃ μ₁ : Mult I, I.Supported μ₁ ∧ I.totalAgg μ₁ ∈ I.Qhat ∧
      (fun t => I.typeAgg μ₁ t) ∈ I.Ahat ∧ I.cost μ₁ < 0) :
    I.Unbounded := by
  obtain ⟨μ₀, hSupp₀, hQ₀, hA₀⟩ := hfeas
  obtain ⟨μ₁, hSupp₁, hQ₁, hA₁, hcost₁⟩ := hrec
  intro B
  obtain ⟨m, hm⟩ := exists_nat_gt ((B - I.cost μ₀) / I.cost μ₁)
  let μ : Mult I := fun t => μ₀ t + m • μ₁ t
  refine ⟨μ, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro t g hg
    rcases Finset.mem_union.mp (Finsupp.support_add (Finset.mem_coe.mp hg)) with hg₀ | hg₁
    · exact hSupp₀ t (Finset.mem_coe.mpr hg₀)
    · exact hSupp₁ t (Finset.mem_coe.mpr (Finsupp.support_smul hg₁))
  · have htot : I.totalAgg μ = I.totalAgg μ₀ + (m : ℝ) • I.totalAgg μ₁ := by
      ext i
      · simp [Instance.totalAgg, μ, aggr_add, aggr_nsmul, Finset.sum_add_distrib, Finset.smul_sum]
      · simp [Instance.totalAgg, μ, aggr_add, aggr_nsmul, Finset.sum_add_distrib, Finset.smul_sum]
    rw [htot]
    intro i
    have h0 := hQ₀ i
    have h1 := hQ₁ i
    have hstep :
        (∑ j, (I.QY i j : ℝ) * ((I.totalAgg μ₀).1 j + (m : ℝ) * (I.totalAgg μ₁).1 j)) +
        (∑ j, (I.QV i j : ℝ) * ((I.totalAgg μ₀).2 j + (m : ℝ) * (I.totalAgg μ₁).2 j)) =
        ((∑ j, (I.QY i j : ℝ) * (I.totalAgg μ₀).1 j) +
          (∑ j, (I.QV i j : ℝ) * (I.totalAgg μ₀).2 j)) +
        (m : ℝ) * ((∑ j, (I.QY i j : ℝ) * (I.totalAgg μ₁).1 j) +
          (∑ j, (I.QV i j : ℝ) * (I.totalAgg μ₁).2 j)) := by
      simp_rw [mul_add, Finset.sum_add_distrib, mul_left_comm, ← Finset.mul_sum]
      ring
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [hstep]
    nlinarith
  · intro i
    have h0 := hA₀ i
    have h1 := hA₁ i
    have htype : ∀ t,
        (I.typeAgg μ t).1 = (I.typeAgg μ₀ t).1 + (m : ℝ) • (I.typeAgg μ₁ t).1 ∧
        (I.typeAgg μ t).2.1 = (I.typeAgg μ₀ t).2.1 + (m : ℝ) • (I.typeAgg μ₁ t).2.1 ∧
        (I.typeAgg μ t).2.2 = (I.typeAgg μ₀ t).2.2 + (m : ℝ) * (I.typeAgg μ₁ t).2.2 := by
      intro t
      refine ⟨?_, ?_, ?_⟩
      · simp [Instance.typeAgg, μ, aggr_add, aggr_nsmul]
      · simp [Instance.typeAgg, μ, aggr_add, aggr_nsmul]
      · simp [Instance.typeAgg, μ, count_add, count_nsmul]
    have hsum :
        (∑ t, ((∑ j, (I.AY t i j : ℝ) * (I.typeAgg μ t).1 j) +
          (∑ j, (I.AV t i j : ℝ) * (I.typeAgg μ t).2.1 j) +
          (I.AN i t : ℝ) * (I.typeAgg μ t).2.2)) =
        (∑ t, ((∑ j, (I.AY t i j : ℝ) * (I.typeAgg μ₀ t).1 j) +
          (∑ j, (I.AV t i j : ℝ) * (I.typeAgg μ₀ t).2.1 j) +
          (I.AN i t : ℝ) * (I.typeAgg μ₀ t).2.2)) +
        (m : ℝ) * (∑ t, ((∑ j, (I.AY t i j : ℝ) * (I.typeAgg μ₁ t).1 j) +
          (∑ j, (I.AV t i j : ℝ) * (I.typeAgg μ₁ t).2.1 j) +
          (I.AN i t : ℝ) * (I.typeAgg μ₁ t).2.2)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      obtain ⟨h1t, h2t, h3t⟩ := htype t
      rw [h1t, h2t, h3t]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
        mul_left_comm, ← Finset.mul_sum]
      ring
    rw [hsum]
    nlinarith
  · have hcost : I.cost μ = I.cost μ₀ + (m : ℝ) * I.cost μ₁ := by
      unfold Instance.cost
      simp only [μ, costOf_add, costOf_nsmul, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hcost]
    have hmlt : (m : ℝ) * I.cost μ₁ < B - I.cost μ₀ := by
      exact (div_lt_iff_of_neg hcost₁).mp hm
    linarith

/-! ## 5. Perspective Rational Linear System on `Var I J` and `Row I J` -/

abbrev JType (I : Instance) (J : Finset (Fin I.τ × (Fin I.d → ℤ))) : Type :=
  {tx : Fin I.τ × (Fin I.d → ℤ) // tx ∈ J}

abbrev Var (I : Instance) (J : Finset (Fin I.τ × (Fin I.d → ℤ))) : Type :=
  JType I J ⊕ (JType I J × Fin I.k)

abbrev Row (I : Instance) (J : Finset (Fin I.τ × (Fin I.d → ℤ))) : Type :=
  JType I J ⊕ (Σ j : JType I J, Fin (I.m j.1.1)) ⊕ Fin I.mQ ⊕ Fin I.mA

def sysA {I : Instance} {J : Finset (Fin I.τ × (Fin I.d → ℤ))}
    (row : Row I J) (v : Var I J) : ℚ :=
  match row with
  | Sum.inl j0 =>
    match v with
    | Sum.inl j => if j = j0 then -1 else 0
    | Sum.inr _ => 0
  | Sum.inr (Sum.inl ⟨j0, i⟩) =>
    match v with
    | Sum.inl j =>
      if j = j0 then (∑ s, I.Aloc j0.1.1 i s * (j0.1.2 s : ℚ)) - I.bloc j0.1.1 i else 0
    | Sum.inr (j, r) =>
      if j = j0 then I.Bloc j0.1.1 i r else 0
  | Sum.inr (Sum.inr (Sum.inl i)) =>
    match v with
    | Sum.inl j => ∑ s, I.QY i s * (j.1.2 s : ℚ)
    | Sum.inr (_, r) => I.QV i r
  | Sum.inr (Sum.inr (Sum.inr i)) =>
    match v with
    | Sum.inl j => (∑ s, I.AY j.1.1 i s * (j.1.2 s : ℚ)) + I.AN i j.1.1
    | Sum.inr (j, r) => I.AV j.1.1 i r

def sysB {I : Instance} {J : Finset (Fin I.τ × (Fin I.d → ℤ))} (row : Row I J) : ℚ :=
  match row with
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (Sum.inl i)) => I.cQ i
  | Sum.inr (Sum.inr (Sum.inr i)) => I.cA i

def sysC {I : Instance} {J : Finset (Fin I.τ × (Fin I.d → ℤ))} (v : Var I J) : ℚ :=
  match v with
  | Sum.inl j => ratEvalF I j.1.1 j.1.2
  | Sum.inr _ => 0

section SysEval

variable {I : Instance} {J : Finset (Fin I.τ × (Fin I.d → ℤ))}

lemma sum_var_real (f : Var I J → ℝ) :
    ∑ v : Var I J, f v = (∑ j : JType I J, f (Sum.inl j)) +
      ∑ j : JType I J, ∑ r : Fin I.k, f (Sum.inr (j, r)) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]

lemma sum_var_rat (f : Var I J → ℚ) :
    ∑ v : Var I J, f v = (∑ j : JType I J, f (Sum.inl j)) +
      ∑ j : JType I J, ∑ r : Fin I.k, f (Sum.inr (j, r)) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]

lemma eval_sysA_inl_real (j0 : JType I J) (z : Var I J → ℝ) :
    ∑ v : Var I J, ((sysA (Sum.inl j0 : Row I J) v : ℚ) : ℝ) * z v = -z (Sum.inl j0) := by
  rw [sum_var_real]
  simp only [sysA, apply_ite (fun q : ℚ => (q : ℝ)), Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
    ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Finset.sum_const_zero, add_zero]

lemma eval_sysA_loc_real (j0 : JType I J) (i : Fin (I.m j0.1.1)) (z : Var I J → ℝ) :
    ∑ v : Var I J, ((sysA (Sum.inr (Sum.inl ⟨j0, i⟩) : Row I J) v : ℚ) : ℝ) * z v =
      ((∑ s, (I.Aloc j0.1.1 i s : ℝ) * (j0.1.2 s : ℝ)) - (I.bloc j0.1.1 i : ℝ)) *
          z (Sum.inl j0) +
        ∑ r : Fin I.k, (I.Bloc j0.1.1 i r : ℝ) * z (Sum.inr (j0, r)) := by
  rw [sum_var_real]
  have hL : (∑ j : JType I J,
      ((sysA (Sum.inr (Sum.inl ⟨j0, i⟩) : Row I J) (Sum.inl j) : ℚ) : ℝ) * z (Sum.inl j)) =
      ((∑ s, (I.Aloc j0.1.1 i s : ℝ) * (j0.1.2 s : ℝ)) - (I.bloc j0.1.1 i : ℝ)) *
        z (Sum.inl j0) := by
    simp only [sysA, apply_ite (fun q : ℚ => (q : ℝ)), Rat.cast_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    push_cast
    rfl
  have hR : (∑ j : JType I J, ∑ r : Fin I.k,
      ((sysA (Sum.inr (Sum.inl ⟨j0, i⟩) : Row I J) (Sum.inr (j, r)) : ℚ) : ℝ) *
        z (Sum.inr (j, r))) =
      ∑ r : Fin I.k, (I.Bloc j0.1.1 i r : ℝ) * z (Sum.inr (j0, r)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [sysA, apply_ite (fun q : ℚ => (q : ℝ)), Rat.cast_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [hL, hR]

lemma eval_sysA_Q_real (i : Fin I.mQ) (z : Var I J → ℝ) :
    ∑ v : Var I J, ((sysA (Sum.inr (Sum.inr (Sum.inl i)) : Row I J) v : ℚ) : ℝ) * z v =
      (∑ j : JType I J, (∑ s, (I.QY i s : ℝ) * (j.1.2 s : ℝ)) * z (Sum.inl j)) +
      (∑ j : JType I J, ∑ r : Fin I.k, (I.QV i r : ℝ) * z (Sum.inr (j, r))) := by
  rw [sum_var_real]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [sysA]
  push_cast
  rfl

lemma eval_sysA_A_real (i : Fin I.mA) (z : Var I J → ℝ) :
    ∑ v : Var I J, ((sysA (Sum.inr (Sum.inr (Sum.inr i)) : Row I J) v : ℚ) : ℝ) * z v =
      (∑ j : JType I J,
        ((∑ s, (I.AY j.1.1 i s : ℝ) * (j.1.2 s : ℝ)) + (I.AN i j.1.1 : ℝ)) * z (Sum.inl j)) +
      (∑ j : JType I J, ∑ r : Fin I.k, (I.AV j.1.1 i r : ℝ) * z (Sum.inr (j, r))) := by
  rw [sum_var_real]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [sysA]
  push_cast
  rfl

lemma eval_sysC_real (z : Var I J → ℝ) :
    ∑ v : Var I J, ((sysC (I := I) (J := J) v : ℚ) : ℝ) * z v =
      ∑ j : JType I J, I.f j.1.1 (fun s => (j.1.2 s : ℝ)) * z (Sum.inl j) := by
  rw [sum_var_real]
  have hR : ∑ j : JType I J, ∑ r : Fin I.k,
      ((sysC (I := I) (J := J) (Sum.inr (j, r)) : ℚ) : ℝ) * z (Sum.inr (j, r)) = 0 := by
    simp [sysC]
  rw [hR, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [sysC, ratEvalF_cast_real]

end SysEval

/-! ## 6. Embedding Feasible Multiplicities into `Var I J → ℝ` and Dual Contradiction -/

noncomputable def multToVar (I : Instance) (J : Finset (Fin I.τ × (Fin I.d → ℤ)))
    (μ : Mult I) : Var I J → ℝ
  | Sum.inl j => ∑ g ∈ (μ j.1.1).support, if g.1 = j.1.2 then (μ j.1.1 g : ℝ) else 0
  | Sum.inr (j, r) => ∑ g ∈ (μ j.1.1).support, if g.1 = j.1.2 then (μ j.1.1 g : ℝ) * g.2 r else 0

lemma sum_J_type_filter {I : Instance} {J : Finset (Fin I.τ × (Fin I.d → ℤ))}
    (μ : Mult I) (hsupp : I.Supported μ)
    (hmem : ∀ t x, (fun i => (x i : ℝ)) ∈ I.Px t → (t, x) ∈ J)
    (t : Fin I.τ) (F : Gen I.d I.k → ℝ) :
    ∑ j ∈ (Finset.univ : Finset (JType I J)).filter (fun j => j.1.1 = t),
      (∑ g ∈ (μ t).support, if g.1 = j.1.2 then F g else 0) =
    ∑ g ∈ (μ t).support, F g := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hgP : g ∈ I.S t := hsupp t hg
  have hgPx : (fun i => (g.1 i : ℝ)) ∈ I.Px t := ⟨g.toReal, hgP, rfl⟩
  let j₀ : JType I J := ⟨(t, g.1), hmem t g.1 hgPx⟩
  trans (if g.1 = j₀.1.2 then F g else 0)
  · apply Finset.sum_eq_single j₀
    · intro j hj hne
      have hjt : j.1.1 = t := (Finset.mem_filter.mp hj).2
      have hxne : g.1 ≠ j.1.2 := by
        intro heq
        apply hne
        apply Subtype.ext
        exact Prod.ext hjt heq.symm
      exact if_neg hxne
    · intro hnot
      exfalso
      apply hnot
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  · simp [j₀]

lemma multToVar_feasible (I : Instance) (J : Finset (Fin I.τ × (Fin I.d → ℤ)))
    (hmem : ∀ t x, (fun i => (x i : ℝ)) ∈ I.Px t → (t, x) ∈ J)
    (μ : Mult I) (hμ : I.Feasible μ) :
    (∀ row : Row I J, ∑ v, ((sysA row v : ℚ) : ℝ) * multToVar I J μ v ≤ (sysB row : ℝ)) ∧
    ∑ v, ((sysC (I := I) (J := J) v : ℚ) : ℝ) * multToVar I J μ v = I.cost μ := by
  rcases hμ with ⟨hsupp, hQ, hA⟩
  have hcount_t : ∀ t : Fin I.τ,
      ∑ j ∈ (Finset.univ : Finset (JType I J)).filter (fun j => j.1.1 = t),
        multToVar I J μ (Sum.inl j) = (count (μ t) : ℝ) := by
    intro t
    have h := sum_J_type_filter μ hsupp hmem t (fun g => (μ t g : ℝ))
    have hcongr : ∑ j ∈ (Finset.univ : Finset (JType I J)).filter (fun j => j.1.1 = t),
        multToVar I J μ (Sum.inl j) =
      ∑ j ∈ (Finset.univ : Finset (JType I J)).filter (fun j => j.1.1 = t),
        (∑ g ∈ (μ t).support, if g.1 = j.1.2 then (μ t g : ℝ) else 0) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjt : j.1.1 = t := (Finset.mem_filter.mp hj).2
      simp only [multToVar, hjt]
    rw [hcongr, h]
    simp [count, Finsupp.sum]
  have haggr1_t : ∀ (t : Fin I.τ) (s : Fin I.d),
      ∑ j ∈ (Finset.univ : Finset (JType I J)).filter (fun j => j.1.1 = t),
        (j.1.2 s : ℝ) * multToVar I J μ (Sum.inl j) = (aggr (μ t)).1 s := by
    intro t s
    have h := sum_J_type_filter μ hsupp hmem t (fun g => (μ t g : ℝ) * (g.1 s : ℝ))
    have hcongr : ∑ j ∈ (Finset.univ : Finset (JType I J)).filter (fun j => j.1.1 = t),
        (j.1.2 s : ℝ) * multToVar I J μ (Sum.inl j) =
      ∑ j ∈ (Finset.univ : Finset (JType I J)).filter (fun j => j.1.1 = t),
        (∑ g ∈ (μ t).support, if g.1 = j.1.2 then (μ t g : ℝ) * (g.1 s : ℝ) else 0) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjt : j.1.1 = t := (Finset.mem_filter.mp hj).2
      simp only [multToVar, hjt, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      split_ifs with heq
      · rw [heq, mul_comm]
      · simp
    rw [hcongr, h]
    simp [aggr, Finsupp.sum, Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Gen.toReal]
  have haggr2_t : ∀ (t : Fin I.τ) (r : Fin I.k),
      ∑ j ∈ (Finset.univ : Finset (JType I J)).filter (fun j => j.1.1 = t),
        multToVar I J μ (Sum.inr (j, r)) = (aggr (μ t)).2 r := by
    intro t r
    have h := sum_J_type_filter μ hsupp hmem t (fun g => (μ t g : ℝ) * g.2 r)
    have hcongr : ∑ j ∈ (Finset.univ : Finset (JType I J)).filter (fun j => j.1.1 = t),
        multToVar I J μ (Sum.inr (j, r)) =
      ∑ j ∈ (Finset.univ : Finset (JType I J)).filter (fun j => j.1.1 = t),
        (∑ g ∈ (μ t).support, if g.1 = j.1.2 then (μ t g : ℝ) * g.2 r else 0) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjt : j.1.1 = t := (Finset.mem_filter.mp hj).2
      simp only [multToVar, hjt]
    rw [hcongr, h]
    simp [aggr, Finsupp.sum, Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Gen.toReal]
  refine ⟨fun row => ?_, ?_⟩
  · cases row with
    | inl j0 =>
      rw [eval_sysA_inl_real]
      have h0 : 0 ≤ multToVar I J μ (Sum.inl j0) := by
        refine Finset.sum_nonneg fun g _ => ?_
        split_ifs <;> positivity
      simpa [sysB] using h0
    | inr r1 =>
      cases r1 with
      | inl loc =>
        rcases loc with ⟨j0, i⟩
        rw [eval_sysA_loc_real]
        simp only [sysB, Rat.cast_zero, multToVar]
        have hsum :
            ((∑ s, (I.Aloc j0.1.1 i s : ℝ) * (j0.1.2 s : ℝ)) - (I.bloc j0.1.1 i : ℝ)) *
              (∑ g ∈ (μ j0.1.1).support, if g.1 = j0.1.2 then (μ j0.1.1 g : ℝ) else 0) +
            ∑ r : Fin I.k, (I.Bloc j0.1.1 i r : ℝ) *
              (∑ g ∈ (μ j0.1.1).support, if g.1 = j0.1.2 then (μ j0.1.1 g : ℝ) * g.2 r else 0) =
            ∑ g ∈ (μ j0.1.1).support, if g.1 = j0.1.2 then
              (μ j0.1.1 g : ℝ) * (((∑ s, (I.Aloc j0.1.1 i s : ℝ) * (g.1 s : ℝ)) +
                (∑ r, (I.Bloc j0.1.1 i r : ℝ) * g.2 r)) - (I.bloc j0.1.1 i : ℝ)) else 0 := by
          rw [Finset.mul_sum]
          have hswap : (∑ r : Fin I.k, (I.Bloc j0.1.1 i r : ℝ) *
                (∑ g ∈ (μ j0.1.1).support, if g.1 = j0.1.2 then (μ j0.1.1 g : ℝ) * g.2 r else 0)) =
              ∑ g ∈ (μ j0.1.1).support, ∑ r : Fin I.k,
                if g.1 = j0.1.2 then (μ j0.1.1 g : ℝ) * ((I.Bloc j0.1.1 i r : ℝ) * g.2 r) else 0 := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun g _ => ?_
            split_ifs <;> ring
          rw [hswap, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun g _ => ?_
          by_cases heq : g.1 = j0.1.2
          · rw [if_pos heq, if_pos heq]
            have hite : ∀ r : Fin I.k,
                (if g.1 = j0.1.2 then (μ j0.1.1 g : ℝ) * ((I.Bloc j0.1.1 i r : ℝ) * g.2 r) else 0) =
                (μ j0.1.1 g : ℝ) * ((I.Bloc j0.1.1 i r : ℝ) * g.2 r) := fun r => if_pos heq
            simp_rw [hite, ← Finset.mul_sum, heq]
            ring
          · rw [if_neg heq, if_neg heq, mul_zero, zero_add]
            exact Finset.sum_eq_zero fun r _ => if_neg heq
        rw [hsum]
        refine Finset.sum_nonpos fun g hg => ?_
        split_ifs
        · have hgS := (hsupp j0.1.1 hg) i
          have hle : ((∑ s, (I.Aloc j0.1.1 i s : ℝ) * (g.1 s : ℝ)) +
              (∑ r, (I.Bloc j0.1.1 i r : ℝ) * g.2 r)) - (I.bloc j0.1.1 i : ℝ) ≤ 0 :=
            sub_nonpos.mpr hgS
          exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hle
        · exact le_rfl
      | inr qa =>
        cases qa with
        | inl i =>
          rw [eval_sysA_Q_real]
          simp only [sysB]
          have h1' : (∑ j : JType I J, (∑ s, (I.QY i s : ℝ) * (j.1.2 s : ℝ)) *
                multToVar I J μ (Sum.inl j)) =
              ∑ s, (I.QY i s : ℝ) * (I.totalAgg μ).1 s := by
            rw [← Finset.sum_fiberwise (Finset.univ : Finset (JType I J)) (fun j => j.1.1)]
            have hswap : ∀ t : Fin I.τ,
                (∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
                  (∑ s, (I.QY i s : ℝ) * (j.1.2 s : ℝ)) * multToVar I J μ (Sum.inl j)) =
                ∑ s, (I.QY i s : ℝ) * (aggr (μ t)).1 s := by
              intro t
              simp_rw [Finset.sum_mul]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun s _ => ?_
              calc ∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
                    (I.QY i s : ℝ) * (j.1.2 s : ℝ) * multToVar I J μ (Sum.inl j)
                _ = (I.QY i s : ℝ) * ∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
                      (j.1.2 s : ℝ) * multToVar I J μ (Sum.inl j) := by
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl fun j _ => by ring
                _ = (I.QY i s : ℝ) * (aggr (μ t)).1 s := by rw [haggr1_t t s]
            simp_rw [hswap]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun s _ => ?_
            simp [Instance.totalAgg, Prod.fst_sum, Finset.mul_sum]
          have h2' : (∑ j : JType I J, ∑ r : Fin I.k,
                (I.QV i r : ℝ) * multToVar I J μ (Sum.inr (j, r))) =
              ∑ r, (I.QV i r : ℝ) * (I.totalAgg μ).2 r := by
            rw [← Finset.sum_fiberwise (Finset.univ : Finset (JType I J)) (fun j => j.1.1)]
            have hswap : ∀ t : Fin I.τ,
                (∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
                  ∑ r : Fin I.k, (I.QV i r : ℝ) * multToVar I J μ (Sum.inr (j, r))) =
                ∑ r : Fin I.k, (I.QV i r : ℝ) * (aggr (μ t)).2 r := by
              intro t
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [← Finset.mul_sum, haggr2_t t r]
            simp_rw [hswap]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun r _ => ?_
            simp [Instance.totalAgg, Prod.snd_sum, Finset.mul_sum]
          rw [h1', h2']
          exact hQ i
        | inr i =>
          rw [eval_sysA_A_real]
          simp only [sysB]
          rw [← Finset.sum_fiberwise (Finset.univ : Finset (JType I J)) (fun j => j.1.1)]
          rw [← Finset.sum_fiberwise (Finset.univ : Finset (JType I J)) (fun j => j.1.1)]
          rw [← Finset.sum_add_distrib]
          have hA_t : ∀ t : Fin I.τ,
              (∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
                ((∑ s, (I.AY j.1.1 i s : ℝ) * (j.1.2 s : ℝ)) + (I.AN i j.1.1 : ℝ)) *
                  multToVar I J μ (Sum.inl j)) +
              (∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
                ∑ r : Fin I.k, (I.AV j.1.1 i r : ℝ) * multToVar I J μ (Sum.inr (j, r))) =
              (∑ s, (I.AY t i s : ℝ) * (I.typeAgg μ t).1 s) +
              (∑ r, (I.AV t i r : ℝ) * (I.typeAgg μ t).2.1 r) +
              (I.AN i t : ℝ) * (I.typeAgg μ t).2.2 := by
            intro t
            have hp1 : (∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
                  ((∑ s, (I.AY j.1.1 i s : ℝ) * (j.1.2 s : ℝ)) + (I.AN i j.1.1 : ℝ)) *
                    multToVar I J μ (Sum.inl j)) =
                (∑ s, (I.AY t i s : ℝ) * (aggr (μ t)).1 s) +
                (I.AN i t : ℝ) * (count (μ t) : ℝ) := by
              have hcongr : (∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
                    ((∑ s, (I.AY j.1.1 i s : ℝ) * (j.1.2 s : ℝ)) + (I.AN i j.1.1 : ℝ)) *
                      multToVar I J μ (Sum.inl j)) =
                  (∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
                    (∑ s, (I.AY t i s : ℝ) * (j.1.2 s : ℝ) * multToVar I J μ (Sum.inl j))) +
                  ∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
                    (I.AN i t : ℝ) * multToVar I J μ (Sum.inl j) := by
                rw [← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun j hj => ?_
                have hjt : j.1.1 = t := (Finset.mem_filter.mp hj).2
                rw [hjt, add_mul, Finset.sum_mul]
              rw [hcongr, Finset.sum_comm]
              congr 1
              · refine Finset.sum_congr rfl fun s _ => ?_
                rw [← haggr1_t t s, Finset.mul_sum]
                refine Finset.sum_congr rfl fun j _ => by ring
              · rw [← Finset.mul_sum, hcount_t t]
            have hp2 : (∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
                  ∑ r : Fin I.k, (I.AV j.1.1 i r : ℝ) * multToVar I J μ (Sum.inr (j, r))) =
                ∑ r, (I.AV t i r : ℝ) * (aggr (μ t)).2 r := by
              have hcongr : (∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
                    ∑ r : Fin I.k, (I.AV j.1.1 i r : ℝ) * multToVar I J μ (Sum.inr (j, r))) =
                  ∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
                    ∑ r : Fin I.k, (I.AV t i r : ℝ) * multToVar I J μ (Sum.inr (j, r)) := by
                refine Finset.sum_congr rfl fun j hj => ?_
                have hjt : j.1.1 = t := (Finset.mem_filter.mp hj).2
                rw [hjt]
              rw [hcongr, Finset.sum_comm]
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [← Finset.mul_sum, haggr2_t t r]
            rw [hp1, hp2]
            simp only [Instance.typeAgg]
            ring
          have hfull : (∑ t : Fin I.τ,
                ((∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
                  ((∑ s, (I.AY j.1.1 i s : ℝ) * (j.1.2 s : ℝ)) + (I.AN i j.1.1 : ℝ)) *
                    multToVar I J μ (Sum.inl j)) +
                (∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
                  ∑ r : Fin I.k, (I.AV j.1.1 i r : ℝ) * multToVar I J μ (Sum.inr (j, r))))) =
              ∑ t : Fin I.τ, ((∑ s, (I.AY t i s : ℝ) * (I.typeAgg μ t).1 s) +
                (∑ r, (I.AV t i r : ℝ) * (I.typeAgg μ t).2.1 r) +
                (I.AN i t : ℝ) * (I.typeAgg μ t).2.2) :=
            Finset.sum_congr rfl fun t _ => hA_t t
          rw [hfull]
          exact hA i
  · rw [eval_sysC_real]
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (JType I J)) (fun j => j.1.1)]
    unfold Instance.cost costOf
    refine Finset.sum_congr rfl fun t _ => ?_
    have h := sum_J_type_filter μ hsupp hmem t (fun g => (μ t g : ℝ) * I.f t (fun s => (g.1 s : ℝ)))
    have hcongr : (∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
          I.f j.1.1 (fun s => (j.1.2 s : ℝ)) * multToVar I J μ (Sum.inl j)) =
        ∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
          ∑ g ∈ (μ t).support, if g.1 = j.1.2 then
            (μ t g : ℝ) * I.f t (fun s => (g.1 s : ℝ)) else 0 := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjt : j.1.1 = t := (Finset.mem_filter.mp hj).2
      simp only [multToVar, hjt, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      split_ifs with heq
      · rw [heq, mul_comm]
      · simp
    rw [hcongr, h]
    rfl

lemma not_dual_of_unbounded (I : Instance) (J : Finset (Fin I.τ × (Fin I.d → ℤ)))
    (hmem : ∀ t x, (fun i => (x i : ℝ)) ∈ I.Px t → (t, x) ∈ J)
    (hunb : I.Unbounded)
    (y : Row I J → ℚ) (hy_nonneg : ∀ r, 0 ≤ y r)
    (hy_eq : ∀ v : Var I J, ∑ r : Row I J, y r * sysA r v = -sysC v) : False := by
  let B : ℝ := -∑ r : Row I J, (y r : ℝ) * (sysB r : ℝ)
  obtain ⟨μ, hμ, hcost⟩ := hunb B
  obtain ⟨hrows, hC⟩ := multToVar_feasible I J hmem μ hμ
  let z := multToVar I J μ
  have h1 : ∑ r : Row I J, (y r : ℝ) * (∑ v : Var I J, ((sysA r v : ℚ) : ℝ) * z v) ≤
      ∑ r : Row I J, (y r : ℝ) * (sysB r : ℝ) :=
    Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (hrows r) (by exact_mod_cast hy_nonneg r)
  have h2 : ∑ r : Row I J, (y r : ℝ) * (∑ v : Var I J, ((sysA r v : ℚ) : ℝ) * z v) =
      -I.cost μ := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc ∑ v : Var I J, ∑ r : Row I J, (y r : ℝ) * (((sysA r v : ℚ) : ℝ) * z v)
      _ = ∑ v : Var I J, (∑ r : Row I J, ((y r * sysA r v : ℚ) : ℝ)) * z v := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun r _ => by push_cast; ring
      _ = ∑ v : Var I J, ((-((sysC (I := I) (J := J) v : ℚ) : ℝ)) * z v) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          have heqR : (∑ r : Row I J, ((y r * sysA r v : ℚ) : ℝ)) =
              ((-((sysC (I := I) (J := J) v : ℚ) : ℝ))) := by
            have := congrArg (fun q : ℚ => (q : ℝ)) (hy_eq v)
            simpa [Rat.cast_sum, Rat.cast_neg] using this
          rw [heqR]
      _ = -∑ v : Var I J, ((sysC (I := I) (J := J) v : ℚ) : ℝ) * z v := by
          simp_rw [neg_mul, Finset.sum_neg_distrib]
      _ = -I.cost μ := by rw [hC]
  linarith

/-! ## 7. Forward Direction: From Unboundedness to Homogeneous Negative-Cost Representation -/

def recDenom {I : Instance} {J : Finset (Fin I.τ × (Fin I.d → ℤ))} (d : Var I J → ℚ) : ℕ :=
  ∏ j : JType I J, (d (Sum.inl j)).den

lemma recDenom_pos {I : Instance} {J : Finset (Fin I.τ × (Fin I.d → ℤ))} (d : Var I J → ℚ) :
    0 < recDenom d :=
  Finset.prod_pos fun _ _ => Rat.den_pos _

def recNNat {I : Instance} {J : Finset (Fin I.τ × (Fin I.d → ℤ))} (d : Var I J → ℚ)
    (j : JType I J) : ℕ :=
  (d (Sum.inl j)).num.toNat * (recDenom d / (d (Sum.inl j)).den)

lemma recNNat_cast_real {I : Instance} {J : Finset (Fin I.τ × (Fin I.d → ℤ))}
    (d : Var I J → ℚ) (hd_nonneg : ∀ j, 0 ≤ d (Sum.inl j)) (j : JType I J) :
    (recNNat d j : ℝ) = (recDenom d : ℝ) * (d (Sum.inl j) : ℝ) := by
  have hdvd : (d (Sum.inl j)).den ∣ recDenom d :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  obtain ⟨m, hm⟩ := hdvd
  have hden_pos : 0 < (d (Sum.inl j)).den := Rat.den_pos _
  have hdiv : recDenom d / (d (Sum.inl j)).den = m := by
    rw [hm, Nat.mul_div_cancel_left _ hden_pos]
  have hnum0 : 0 ≤ (d (Sum.inl j)).num := Rat.num_nonneg.mpr (hd_nonneg j)
  have hnumR : (((d (Sum.inl j)).num.toNat : ℕ) : ℝ) = ((d (Sum.inl j)).num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum0
  unfold recNNat
  rw [hdiv, hm, Rat.cast_def]
  push_cast
  rw [hnumR]
  have hdenR : ((d (Sum.inl j)).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hden_pos.ne'
  field_simp [hdenR]

noncomputable def recWReal {I : Instance} {J : Finset (Fin I.τ × (Fin I.d → ℤ))}
    (d : Var I J → ℚ) (j : JType I J) (r : Fin I.k) : ℝ :=
  (recDenom d : ℝ) * (d (Sum.inr (j, r)) : ℝ)

noncomputable def recGen {I : Instance} {J : Finset (Fin I.τ × (Fin I.d → ℤ))}
    (d : Var I J → ℚ) (j : JType I J) : Gen I.d I.k :=
  (j.1.2, fun r => (recNNat d j : ℝ)⁻¹ * recWReal d j r)

noncomputable def recMult (I : Instance) (J : Finset (Fin I.τ × (Fin I.d → ℤ)))
    (d : Var I J → ℚ) : Mult I :=
  fun t =>
    ∑ j ∈ (Finset.univ : Finset (JType I J)).filter (fun j => j.1.1 = t),
      Finsupp.single (recGen d j) (recNNat d j)

lemma recMult_supported (I : Instance) (J : Finset (Fin I.τ × (Fin I.d → ℤ)))
    (d : Var I J → ℚ)
    (hloc : ∀ (j : JType I J) (i : Fin (I.m j.1.1)),
      ((∑ s, (I.Aloc j.1.1 i s : ℝ) * (j.1.2 s : ℝ)) - (I.bloc j.1.1 i : ℝ)) *
          (recNNat d j : ℝ) +
        ∑ r, (I.Bloc j.1.1 i r : ℝ) * recWReal d j r ≤ 0) :
    I.Supported (recMult I J d) := by
  intro t g hg
  have hmem_supp : g ∈ (∑ j ∈ (Finset.univ : Finset (JType I J)).filter (fun j => j.1.1 = t),
      Finsupp.single (recGen d j) (recNNat d j)).support :=
    Finset.mem_coe.mp hg
  have hsub := Finsupp.support_finsetSum hmem_supp
  rw [Finset.mem_biUnion] at hsub
  obtain ⟨j, hj, hgj⟩ := hsub
  have hjt : j.1.1 = t := (Finset.mem_filter.mp hj).2
  have hnz : recNNat d j ≠ 0 := by
    intro hz
    rw [hz, Finsupp.single_zero, Finsupp.support_zero] at hgj
    exact Finset.notMem_empty _ hgj
  have hgeq : g = recGen d j := Finset.mem_singleton.mp (Finsupp.support_single_subset hgj)
  rw [hgeq, ← hjt]
  intro i
  have hl := hloc j i
  have hn0 : (recNNat d j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hnz
  have hn_pos : 0 < (recNNat d j : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hnz)
  have hsec : (recNNat d j : ℝ) *
        (∑ r, (I.Bloc j.1.1 i r : ℝ) * ((recNNat d j : ℝ)⁻¹ * recWReal d j r)) =
      ∑ r, (I.Bloc j.1.1 i r : ℝ) * recWReal d j r := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hmul : (recNNat d j : ℝ) * ((recNNat d j : ℝ)⁻¹ * recWReal d j r) = recWReal d j r :=
      mul_inv_cancel_left₀ hn0 _
    calc (recNNat d j : ℝ) * ((I.Bloc j.1.1 i r : ℝ) * ((recNNat d j : ℝ)⁻¹ * recWReal d j r))
      _ = (I.Bloc j.1.1 i r : ℝ) * ((recNNat d j : ℝ) * ((recNNat d j : ℝ)⁻¹ * recWReal d j r)) := by ring
      _ = (I.Bloc j.1.1 i r : ℝ) * recWReal d j r := by rw [hmul]
  have hid : (recNNat d j : ℝ) *
      ((∑ s, (I.Aloc j.1.1 i s : ℝ) * (j.1.2 s : ℝ)) +
        (∑ r, (I.Bloc j.1.1 i r : ℝ) * ((recNNat d j : ℝ)⁻¹ * recWReal d j r)) -
        (I.bloc j.1.1 i : ℝ)) =
      ((∑ s, (I.Aloc j.1.1 i s : ℝ) * (j.1.2 s : ℝ)) - (I.bloc j.1.1 i : ℝ)) *
        (recNNat d j : ℝ) + ∑ r, (I.Bloc j.1.1 i r : ℝ) * recWReal d j r := by
    rw [mul_sub, mul_add, hsec]
    ring
  have hscaled : (recNNat d j : ℝ) *
      ((∑ s, (I.Aloc j.1.1 i s : ℝ) * (j.1.2 s : ℝ)) +
        (∑ r, (I.Bloc j.1.1 i r : ℝ) * ((recNNat d j : ℝ)⁻¹ * recWReal d j r)) -
        (I.bloc j.1.1 i : ℝ)) ≤ 0 := by rw [hid]; exact hl
  have hnonpos : (∑ s, (I.Aloc j.1.1 i s : ℝ) * (j.1.2 s : ℝ)) +
      (∑ r, (I.Bloc j.1.1 i r : ℝ) * ((recNNat d j : ℝ)⁻¹ * recWReal d j r)) -
      (I.bloc j.1.1 i : ℝ) ≤ 0 := by nlinarith
  exact sub_nonpos.mp hnonpos

lemma recMult_Qhat (I : Instance) (J : Finset (Fin I.τ × (Fin I.d → ℤ)))
    (d : Var I J → ℚ)
    (hn_real : ∀ j : JType I J, (recNNat d j : ℝ) = (recDenom d : ℝ) * (d (Sum.inl j) : ℝ))
    (hj_aggr : ∀ j : JType I J,
      aggr (Finsupp.single (recGen d j) (recNNat d j)) =
        (fun s => (recNNat d j : ℝ) * (j.1.2 s : ℝ), recWReal d j))
    (hdQ : ∀ i : Fin I.mQ,
      ∑ v : Var I J, ((sysA (Sum.inr (Sum.inr (Sum.inl i)) : Row I J) v : ℚ) : ℝ) * (d v : ℝ) ≤ 0) :
    I.totalAgg (recMult I J d) ∈ I.Qhat := by
  intro i
  have hq := hdQ i
  rw [eval_sysA_Q_real] at hq
  have hagg1 : ∀ s, (I.totalAgg (recMult I J d)).1 s =
      ∑ j : JType I J, (j.1.2 s : ℝ) * ((recDenom d : ℝ) * (d (Sum.inl j) : ℝ)) := by
    intro s
    simp only [Instance.totalAgg, Prod.fst_sum, Finset.sum_apply, recMult, aggr_sum]
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (JType I J)) (fun j => j.1.1)]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [hj_aggr, hn_real]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hagg2 : ∀ r, (I.totalAgg (recMult I J d)).2 r =
      ∑ j : JType I J, (recDenom d : ℝ) * (d (Sum.inr (j, r)) : ℝ) := by
    intro r
    simp only [Instance.totalAgg, Prod.snd_sum, Finset.sum_apply, recMult, aggr_sum]
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (JType I J)) (fun j => j.1.1)]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [hj_aggr, recWReal]
  have htot_eq :
      ((∑ s, (I.QY i s : ℝ) * (I.totalAgg (recMult I J d)).1 s) +
        (∑ r, (I.QV i r : ℝ) * (I.totalAgg (recMult I J d)).2 r)) =
      (recDenom d : ℝ) *
        ((∑ j : JType I J, (∑ s, (I.QY i s : ℝ) * (j.1.2 s : ℝ)) * (d (Sum.inl j) : ℝ)) +
          (∑ j : JType I J, ∑ r : Fin I.k, (I.QV i r : ℝ) * (d (Sum.inr (j, r)) : ℝ))) := by
    simp_rw [hagg1, hagg2, Finset.mul_sum]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => by ring
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => by ring
  rw [htot_eq]
  exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hq

lemma recMult_Ahat (I : Instance) (J : Finset (Fin I.τ × (Fin I.d → ℤ)))
    (d : Var I J → ℚ)
    (hn_real : ∀ j : JType I J, (recNNat d j : ℝ) = (recDenom d : ℝ) * (d (Sum.inl j) : ℝ))
    (hj_aggr : ∀ j : JType I J,
      aggr (Finsupp.single (recGen d j) (recNNat d j)) =
        (fun s => (recNNat d j : ℝ) * (j.1.2 s : ℝ), recWReal d j))
    (hdA : ∀ i : Fin I.mA,
      ∑ v : Var I J, ((sysA (Sum.inr (Sum.inr (Sum.inr i)) : Row I J) v : ℚ) : ℝ) * (d v : ℝ) ≤ 0) :
    (fun t => I.typeAgg (recMult I J d) t) ∈ I.Ahat := by
  intro i
  have ha := hdA i
  rw [eval_sysA_A_real] at ha
  have htype_t : ∀ t : Fin I.τ,
      ((∑ s, (I.AY t i s : ℝ) * (I.typeAgg (recMult I J d) t).1 s) +
        (∑ r, (I.AV t i r : ℝ) * (I.typeAgg (recMult I J d) t).2.1 r) +
        (I.AN i t : ℝ) * (I.typeAgg (recMult I J d) t).2.2) =
      (recDenom d : ℝ) *
        ((∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
            ((∑ s, (I.AY j.1.1 i s : ℝ) * (j.1.2 s : ℝ)) + (I.AN i j.1.1 : ℝ)) *
              (d (Sum.inl j) : ℝ)) +
          (∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
            ∑ r : Fin I.k, (I.AV j.1.1 i r : ℝ) * (d (Sum.inr (j, r)) : ℝ))) := by
    intro t
    have h1 : (I.typeAgg (recMult I J d) t).1 =
        ∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
          fun s => (recNNat d j : ℝ) * (j.1.2 s : ℝ) := by
      simp only [Instance.typeAgg, recMult, aggr_sum, Prod.fst_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hj_aggr j]
    have h2 : (I.typeAgg (recMult I J d) t).2.1 =
        ∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t), recWReal d j := by
      simp only [Instance.typeAgg, recMult, aggr_sum, Prod.snd_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hj_aggr j]
    have h3 : (I.typeAgg (recMult I J d) t).2.2 =
        ∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t), (recNNat d j : ℝ) := by
      simp only [Instance.typeAgg, recMult, count_sum, Nat.cast_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [count_single]
    rw [h1, h2, h3]
    simp only [Finset.sum_apply, Finset.mul_sum]
    have ha1 : (∑ x : Fin I.d, ∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
          (I.AY t i x : ℝ) * ((recNNat d j : ℝ) * (j.1.2 x : ℝ))) =
        ∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
          ∑ x : Fin I.d, (I.AY t i x : ℝ) * ((recNNat d j : ℝ) * (j.1.2 x : ℝ)) :=
      Finset.sum_comm
    have ha2 : (∑ x : Fin I.k, ∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
          (I.AV t i x : ℝ) * recWReal d j x) =
        ∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
          ∑ x : Fin I.k, (I.AV t i x : ℝ) * recWReal d j x :=
      Finset.sum_comm
    rw [ha1, ha2, mul_add, Finset.mul_sum, Finset.mul_sum]
    rw [add_assoc, ← Finset.sum_add_distrib]
    have hadd_comm :
        (∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
          ∑ x : Fin I.d, (I.AY t i x : ℝ) * ((recNNat d j : ℝ) * (j.1.2 x : ℝ))) +
        (∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
          ((∑ x : Fin I.k, (I.AV t i x : ℝ) * recWReal d j x) +
            (I.AN i t : ℝ) * (recNNat d j : ℝ))) =
        ∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
          ((∑ x : Fin I.d, (I.AY t i x : ℝ) * ((recNNat d j : ℝ) * (j.1.2 x : ℝ))) +
            (∑ x : Fin I.k, (I.AV t i x : ℝ) * recWReal d j x) +
            (I.AN i t : ℝ) * (recNNat d j : ℝ)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [hadd_comm]
    have hrhs_split :
        (∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
          (recDenom d : ℝ) * (((∑ s, (I.AY j.1.1 i s : ℝ) * (j.1.2 s : ℝ)) + (I.AN i j.1.1 : ℝ)) *
            (d (Sum.inl j) : ℝ))) +
        (∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
          (recDenom d : ℝ) * ∑ r : Fin I.k, (I.AV j.1.1 i r : ℝ) * (d (Sum.inr (j, r)) : ℝ)) =
        ∑ j ∈ Finset.univ.filter (fun j : JType I J => j.1.1 = t),
          ((recDenom d : ℝ) * (((∑ s, (I.AY j.1.1 i s : ℝ) * (j.1.2 s : ℝ)) + (I.AN i j.1.1 : ℝ)) *
            (d (Sum.inl j) : ℝ)) +
          (recDenom d : ℝ) * ∑ r : Fin I.k, (I.AV j.1.1 i r : ℝ) * (d (Sum.inr (j, r)) : ℝ)) :=
      Finset.sum_add_distrib.symm
    rw [hrhs_split]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjt : j.1.1 = t := (Finset.mem_filter.mp hj).2
    rw [hjt, hn_real j, add_mul, mul_add, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    have hs_eq : (∑ x, (I.AY t i x : ℝ) * ((recDenom d : ℝ) * (d (Sum.inl j) : ℝ) * (j.1.2 x : ℝ))) =
        ∑ s, (recDenom d : ℝ) * ((I.AY t i s : ℝ) * (j.1.2 s : ℝ) * (d (Sum.inl j) : ℝ)) :=
      Finset.sum_congr rfl fun s _ => by ring
    have hr_eq : (∑ x, (I.AV t i x : ℝ) * recWReal d j x) =
        ∑ r, (recDenom d : ℝ) * ((I.AV t i r : ℝ) * (d (Sum.inr (j, r)) : ℝ)) :=
      Finset.sum_congr rfl fun r _ => by simp only [recWReal]; ring
    rw [hs_eq, hr_eq]
    ring
  have hA_eq :
      (∑ t, ((∑ s, (I.AY t i s : ℝ) * (I.typeAgg (recMult I J d) t).1 s) +
        (∑ r, (I.AV t i r : ℝ) * (I.typeAgg (recMult I J d) t).2.1 r) +
        (I.AN i t : ℝ) * (I.typeAgg (recMult I J d) t).2.2)) =
      (recDenom d : ℝ) *
        ((∑ j : JType I J,
            ((∑ s, (I.AY j.1.1 i s : ℝ) * (j.1.2 s : ℝ)) + (I.AN i j.1.1 : ℝ)) *
              (d (Sum.inl j) : ℝ)) +
          (∑ j : JType I J, ∑ r : Fin I.k, (I.AV j.1.1 i r : ℝ) * (d (Sum.inr (j, r)) : ℝ))) := by
    simp_rw [htype_t]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_add_distrib,
      Finset.sum_fiberwise (Finset.univ : Finset (JType I J)) (fun j => j.1.1),
      Finset.sum_fiberwise (Finset.univ : Finset (JType I J)) (fun j => j.1.1)]
  rw [hA_eq]
  exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) ha

lemma recMult_cost (I : Instance) (J : Finset (Fin I.τ × (Fin I.d → ℤ)))
    (d : Var I J → ℚ)
    (hn_real : ∀ j : JType I J, (recNNat d j : ℝ) = (recDenom d : ℝ) * (d (Sum.inl j) : ℝ))
    (hdC : ∑ v : Var I J, ((sysC (I := I) (J := J) v : ℚ) : ℝ) * (d v : ℝ) < 0) :
    I.cost (recMult I J d) < 0 := by
  have hcostQ := hdC
  rw [eval_sysC_real] at hcostQ
  have hcost_eq : I.cost (recMult I J d) =
      (recDenom d : ℝ) * ∑ j : JType I J, I.f j.1.1 (fun s => (j.1.2 s : ℝ)) * (d (Sum.inl j) : ℝ) := by
    unfold Instance.cost
    simp only [recMult, costOf_sum, costOf_single]
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (JType I J)) (fun j => j.1.1)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjt : j.1.1 = t := (Finset.mem_filter.mp hj).2
    rw [hjt, hn_real j]
    dsimp only [recGen]
    ring
  rw [hcost_eq]
  exact mul_neg_of_pos_of_neg (Nat.cast_pos.mpr (recDenom_pos d)) hcostQ

lemma hom_neg_of_unbounded (I : Instance) (hI : I.Valid) (hunb : I.Unbounded) :
    ∃ μ : Mult I, I.Supported μ ∧ I.totalAgg μ ∈ I.Qhat ∧
      (fun t => I.typeAgg μ t) ∈ I.Ahat ∧ I.cost μ < 0 := by
  let hfin := activePairs_finite I hI
  let J : Finset (Fin I.τ × (Fin I.d → ℤ)) := hfin.toFinset
  have hmem : ∀ t x, (fun i => (x i : ℝ)) ∈ I.Px t → (t, x) ∈ J :=
    fun t x hx => hfin.mem_toFinset.mpr hx
  have hmem_px : ∀ j : JType I J, (fun i => (j.1.2 i : ℝ)) ∈ I.Px j.1.1 :=
    fun j => hfin.mem_toFinset.mp j.2
  rcases farkas_hom_rat_fintype (sysA (I := I) (J := J)) (sysC (I := I) (J := J)) with
    ⟨d, hd_rows, hd_cost⟩ | ⟨y, hy_nonneg, hy_eq⟩
  · have hd_nonneg : ∀ j : JType I J, 0 ≤ d (Sum.inl j) := by
      intro j
      have hj := hd_rows (Sum.inl j)
      have hval : ∑ v : Var I J, sysA (Sum.inl j : Row I J) v * d v = -d (Sum.inl j) := by
        rw [sum_var_rat]
        simp [sysA]
      linarith
    have hn_real : ∀ j : JType I J, (recNNat d j : ℝ) = (recDenom d : ℝ) * (d (Sum.inl j) : ℝ) :=
      recNNat_cast_real d hd_nonneg
    have hloc_real : ∀ (j : JType I J) (i : Fin (I.m j.1.1)),
        ((∑ s, (I.Aloc j.1.1 i s : ℝ) * (j.1.2 s : ℝ)) - (I.bloc j.1.1 i : ℝ)) *
            (recNNat d j : ℝ) +
          ∑ r, (I.Bloc j.1.1 i r : ℝ) * recWReal d j r ≤ 0 := by
      intro j i
      have hq : ∑ v : Var I J,
          ((sysA (Sum.inr (Sum.inl ⟨j, i⟩) : Row I J) v : ℚ) : ℝ) * (d v : ℝ) ≤ 0 := by
        have hle : ((∑ v : Var I J, sysA (Sum.inr (Sum.inl ⟨j, i⟩) : Row I J) v * d v : ℚ) : ℝ) ≤ 0 := by
          exact_mod_cast hd_rows (Sum.inr (Sum.inl ⟨j, i⟩))
        simpa [Rat.cast_sum, Rat.cast_mul] using hle
      rw [eval_sysA_loc_real] at hq
      have hscaled : (recDenom d : ℝ) *
          (((∑ s, (I.Aloc j.1.1 i s : ℝ) * (j.1.2 s : ℝ)) - (I.bloc j.1.1 i : ℝ)) *
            (d (Sum.inl j) : ℝ) +
            ∑ r, (I.Bloc j.1.1 i r : ℝ) * (d (Sum.inr (j, r)) : ℝ)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hq
      calc ((∑ s, (I.Aloc j.1.1 i s : ℝ) * (j.1.2 s : ℝ)) - (I.bloc j.1.1 i : ℝ)) *
              (recNNat d j : ℝ) +
            ∑ r, (I.Bloc j.1.1 i r : ℝ) * recWReal d j r
        _ = (recDenom d : ℝ) *
            (((∑ s, (I.Aloc j.1.1 i s : ℝ) * (j.1.2 s : ℝ)) - (I.bloc j.1.1 i : ℝ)) *
              (d (Sum.inl j) : ℝ) +
              ∑ r, (I.Bloc j.1.1 i r : ℝ) * (d (Sum.inr (j, r)) : ℝ)) := by
            rw [hn_real j, mul_add, Finset.mul_sum]
            congr 1
            · ring
            · refine Finset.sum_congr rfl fun r _ => by simp only [recWReal]; ring
        _ ≤ 0 := hscaled
    have hj_aggr : ∀ j : JType I J,
        aggr (Finsupp.single (recGen d j) (recNNat d j)) =
          (fun s => (recNNat d j : ℝ) * (j.1.2 s : ℝ), recWReal d j) := by
      intro j
      rw [aggr_single]
      by_cases hn : recNNat d j = 0
      · have hw0 : recWReal d j = 0 := by
          refine local_recession_zero I hI j.1.1 j.1.2 (hmem_px j) (recWReal d j) fun i => ?_
          have hl := hloc_real j i
          rw [hn, Nat.cast_zero, mul_zero, zero_add] at hl
          exact hl
        rw [hn, Nat.cast_zero, zero_smul, hw0]
        ext s <;> simp
      · have hn0 : (recNNat d j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
        ext s
        · simp [recGen, Gen.toReal, smul_eq_mul]
        · simp [recGen, Gen.toReal, smul_eq_mul, mul_inv_cancel_left₀ hn0]
    have hdQ : ∀ i : Fin I.mQ,
        ∑ v : Var I J, ((sysA (Sum.inr (Sum.inr (Sum.inl i)) : Row I J) v : ℚ) : ℝ) * (d v : ℝ) ≤ 0 := by
      intro i
      have hle : ((∑ v : Var I J, sysA (Sum.inr (Sum.inr (Sum.inl i)) : Row I J) v * d v : ℚ) : ℝ) ≤ 0 := by
        exact_mod_cast hd_rows (Sum.inr (Sum.inr (Sum.inl i)))
      simpa [Rat.cast_sum, Rat.cast_mul] using hle
    have hdA : ∀ i : Fin I.mA,
        ∑ v : Var I J, ((sysA (Sum.inr (Sum.inr (Sum.inr i)) : Row I J) v : ℚ) : ℝ) * (d v : ℝ) ≤ 0 := by
      intro i
      have hle : ((∑ v : Var I J, sysA (Sum.inr (Sum.inr (Sum.inr i)) : Row I J) v * d v : ℚ) : ℝ) ≤ 0 := by
        exact_mod_cast hd_rows (Sum.inr (Sum.inr (Sum.inr i)))
      simpa [Rat.cast_sum, Rat.cast_mul] using hle
    have hdC : ∑ v : Var I J, ((sysC (I := I) (J := J) v : ℚ) : ℝ) * (d v : ℝ) < 0 := by
      have hlt : ((∑ v : Var I J, sysC (I := I) (J := J) v * d v : ℚ) : ℝ) < 0 := by
        exact_mod_cast hd_cost
      simpa [Rat.cast_sum, Rat.cast_mul] using hlt
    exact ⟨recMult I J d, recMult_supported I J d hloc_real,
      recMult_Qhat I J d hn_real hj_aggr hdQ,
      recMult_Ahat I J d hn_real hj_aggr hdA,
      recMult_cost I J d hn_real hdC⟩
  · exact False.elim (not_dual_of_unbounded I J hmem hunb y hy_nonneg hy_eq)

end IntConeFPT.SectionB3Proof

open IntConeFPT
open IntConeFPT.SectionB3Proof

theorem solution (I : Instance) (hI : I.Valid) (hfeas : ∃ μ, I.Feasible μ) :
    I.Unbounded ↔
      ∃ μ : Mult I, I.Supported μ ∧ I.totalAgg μ ∈ I.Qhat ∧
        (fun t => I.typeAgg μ t) ∈ I.Ahat ∧ I.cost μ < 0 :=
  ⟨hom_neg_of_unbounded I hI, unbounded_of_hom_neg I hfeas⟩
