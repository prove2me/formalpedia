-- Prove2me | solution 1 for IntConeFPT.sparse_perspective_projection
-- status  : ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-25T09:33:57.868974+00:00
-- url     : https://prove2.me/submissions/b3f4432f-80ca-499f-b93c-930aaf41100e

import Definitions.Def_IntConeFPT_Formulation
open IntConeFPT Matrix
namespace IntConeFPT.Perspective
open scoped Classical
private lemma sum_ite_subtypeR {m : ℕ} (S : Finset (Fin m)) (g : {i : Fin m // i ∈ S} → ℝ) :
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

lemma fm_exists_or_cert_real :
    ∀ (r m : ℕ) (E : Fin m → Fin r → ℝ) (rhs : Fin m → ℝ),
      (∃ w : Fin r → ℝ, ∀ i, ∑ j, E i j * w j ≤ rhs i) ∨
      (∃ η : Fin m → ℝ, (∀ i, 0 ≤ η i) ∧ (∀ j, ∑ i, η i * E i j = 0) ∧ ∑ i, η i * rhs i < 0)
  | 0, m, _, rhs => by
    by_cases h : ∀ i : Fin m, 0 ≤ rhs i
    · exact Or.inl ⟨Fin.elim0, fun i => by simp [h i]⟩
    · push Not at h
      obtain ⟨i₀, hi₀⟩ := h
      refine Or.inr ⟨Pi.single i₀ 1, ?_, ?_, ?_⟩
      · intro i
        by_cases hi : i = i₀ <;> simp [hi]
      · intro j
        exact j.elim0
      · simp only [Pi.single_apply, ite_mul, one_mul, zero_mul]
        rw [Finset.sum_ite_eq' Finset.univ i₀]
        simp [hi₀]
  | r + 1, m, E, rhs => by
    let a : Fin m → ℝ := fun i => E i 0
    let E' : Fin m → Fin r → ℝ := fun i j => E i j.succ
    let I0 : Finset (Fin m) := Finset.univ.filter fun i => a i = 0
    let Ip : Finset (Fin m) := Finset.univ.filter fun i => 0 < a i
    let Im : Finset (Fin m) := Finset.univ.filter fun i => a i < 0
    let Idx := {i : Fin m // i ∈ I0} ⊕ ({p : Fin m // p ∈ Ip} × {q : Fin m // q ∈ Im})
    let e : Idx ≃ Fin (Fintype.card Idx) := Fintype.equivFin Idx
    let m' : ℕ := Fintype.card Idx
    let B : Fin m' → Fin r → ℝ := fun idx j =>
      match e.symm idx with
      | Sum.inl i => E' i.1 j
      | Sum.inr pq => (-a pq.2.1) * E' pq.1.1 j + a pq.1.1 * E' pq.2.1 j
    let d : Fin m' → ℝ := fun idx =>
      match e.symm idx with
      | Sum.inl i => rhs i.1
      | Sum.inr pq => (-a pq.2.1) * rhs pq.1.1 + a pq.1.1 * rhs pq.2.1
    rcases fm_exists_or_cert_real r m' B d with ⟨w', hw'⟩ | ⟨η', hη'_nonneg, hη'_E, hη'_rhs⟩
    · let U : Fin m → ℝ := fun p => (rhs p - ∑ j, E' p j * w' j) / a p
      let L : Fin m → ℝ := fun q => (rhs q - ∑ j, E' q j * w' j) / a q
      have hLU : ∀ p ∈ Ip, ∀ q ∈ Im, L q ≤ U p := by
        intro p hp q hq
        have hap : 0 < a p := (Finset.mem_filter.mp hp).2
        have haq : a q < 0 := (Finset.mem_filter.mp hq).2
        have hnq : 0 < -a q := neg_pos.mpr haq
        let idx : Fin m' := e (Sum.inr (⟨p, hp⟩, ⟨q, hq⟩))
        have hr := hw' idx
        have hB : ∑ j, B idx j * w' j =
            (-a q) * (∑ j, E' p j * w' j) + a p * (∑ j, E' q j * w' j) := by
          simp only [idx, B, Equiv.symm_apply_apply]
          simp_rw [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
        have hd : d idx = (-a q) * rhs p + a p * rhs q := by
          simp only [idx, d, Equiv.symm_apply_apply]
        rw [hB, hd] at hr
        have hcross : 0 ≤ (-a q) * (rhs p - ∑ j, E' p j * w' j) +
            a p * (rhs q - ∑ j, E' q j * w' j) := by
          have hid : (-a q) * (rhs p - ∑ j, E' p j * w' j) + a p * (rhs q - ∑ j, E' q j * w' j) =
              ((-a q) * rhs p + a p * rhs q) -
                ((-a q) * (∑ j, E' p j * w' j) + a p * (∑ j, E' q j * w' j)) := by ring
          rw [hid, sub_nonneg]
          exact hr
        have hprod : 0 < (-a q) * a p := mul_pos hnq hap
        rw [← sub_nonneg]
        have hap0 : a p ≠ 0 := hap.ne'
        have haq0 : a q ≠ 0 := haq.ne
        have hid : U p - L q =
            ((-a q) * (rhs p - ∑ j, E' p j * w' j) +
              a p * (rhs q - ∑ j, E' q j * w' j)) / ((-a q) * a p) := by
          simp only [U, L]
          rw [div_sub_div _ _ hap0 haq0]
          have hden : a p * a q = -((-a q) * a p) := by ring
          have hnum : (rhs p - ∑ j, E' p j * w' j) * a q - a p * (rhs q - ∑ j, E' q j * w' j) =
              -((-a q) * (rhs p - ∑ j, E' p j * w' j) + a p * (rhs q - ∑ j, E' q j * w' j)) := by ring
          rw [hnum, hden, neg_div_neg_eq]
        rw [hid]
        exact div_nonneg hcross hprod.le
      have hex : ∃ w₀ : ℝ, (∀ p ∈ Ip, w₀ ≤ U p) ∧ (∀ q ∈ Im, L q ≤ w₀) := by
        by_cases hp : Ip.Nonempty
        · refine ⟨Ip.inf' hp U, fun p hp' => Finset.inf'_le _ hp', fun q hq => ?_⟩
          exact Finset.le_inf' hp U fun p hp' => hLU p hp' q hq
        · rw [Finset.not_nonempty_iff_eq_empty] at hp
          by_cases hq : Im.Nonempty
          · refine ⟨Im.sup' hq L, fun p hp' => ?_, fun q hq' => Finset.le_sup' L hq'⟩
            simp [hp] at hp'
          · rw [Finset.not_nonempty_iff_eq_empty] at hq
            exact ⟨0, fun p hp' => by simp [hp] at hp', fun q hq' => by simp [hq] at hq'⟩
      obtain ⟨w₀, hwU, hwL⟩ := hex
      refine Or.inl ⟨Fin.cons w₀ w', fun i => ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      change a i * w₀ + ∑ j, E' i j * w' j ≤ rhs i
      rcases lt_trichotomy (a i) 0 with hai | hai | hai
      · have hi : i ∈ Im := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hai⟩
        have hli := hwL i hi
        simp only [L] at hli
        have hmul : a i * w₀ ≤ a i * ((rhs i - ∑ j, E' i j * w' j) / a i) :=
          mul_le_mul_of_nonpos_left hli hai.le
        rw [mul_div_cancel₀ _ hai.ne] at hmul
        linarith
      · have hi : i ∈ I0 := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hai⟩
        let idx : Fin m' := e (Sum.inl ⟨i, hi⟩)
        have hr := hw' idx
        simp only [B, d, idx, Equiv.symm_apply_apply] at hr
        rw [hai, zero_mul, zero_add]
        exact hr
      · have hi : i ∈ Ip := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hai⟩
        have hui := hwU i hi
        simp only [U] at hui
        have hmul : a i * w₀ ≤ a i * ((rhs i - ∑ j, E' i j * w' j) / a i) :=
          mul_le_mul_of_nonneg_left hui hai.le
        rw [mul_div_cancel₀ _ hai.ne'] at hmul
        linarith
    · let u0 : Fin m → ℝ := fun i =>
        if h : i ∈ I0 then η' (e (Sum.inl ⟨i, h⟩)) else 0
      let upm : Fin m → Fin m → ℝ := fun p q =>
        if hp : p ∈ Ip then if hq : q ∈ Im then η' (e (Sum.inr (⟨p, hp⟩, ⟨q, hq⟩))) else 0 else 0
      let η : Fin m → ℝ := fun i =>
        u0 i + (∑ q : Fin m, upm i q * (-a q)) + (∑ p : Fin m, upm p i * a p)
      have hpull : ∀ f : Fin m → ℝ,
          ∑ i, η i * f i = ∑ idx : Fin m', η' idx *
            (match e.symm idx with
            | Sum.inl i => f i.1
            | Sum.inr pq => (-a pq.2.1) * f pq.1.1 + a pq.1.1 * f pq.2.1) := by
        intro f
        have h0 : ∑ i, u0 i * f i =
            ∑ i : {i : Fin m // i ∈ I0}, η' (e (Sum.inl i)) * f i.1 := by
          trans ∑ i : Fin m, (if h : i ∈ I0 then η' (e (Sum.inl ⟨i, h⟩)) * f i else 0)
          · refine Finset.sum_congr rfl fun i _ => ?_
            simp only [u0]
            split_ifs <;> ring
          · exact sum_ite_subtypeR I0 fun i => η' (e (Sum.inl i)) * f i.1
        have h12 :
            (∑ i, (∑ q, upm i q * (-a q)) * f i) + (∑ i, (∑ p, upm p i * a p) * f i) =
            ∑ pq : {p : Fin m // p ∈ Ip} × {q : Fin m // q ∈ Im},
              η' (e (Sum.inr pq)) * ((-a pq.2.1) * f pq.1.1 + a pq.1.1 * f pq.2.1) := by
          have hL : ∑ i, (∑ q, upm i q * (-a q)) * f i =
              ∑ p, ∑ q, upm p q * ((-a q) * f p) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun q _ => by ring
          have hR : ∑ i, (∑ p, upm p i * a p) * f i =
              ∑ p, ∑ q, upm p q * (a p * f q) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun p _ => by ring
          rw [hL, hR, ← Finset.sum_add_distrib]
          have hcomb :
              (∑ p, ((∑ q, upm p q * ((-a q) * f p)) + (∑ q, upm p q * (a p * f q)))) =
              ∑ p, ∑ q, upm p q * ((-a q) * f p + a p * f q) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun q _ => by ring
          rw [hcomb]
          have hinner : ∀ p (hp : p ∈ Ip),
              (∑ q, upm p q * ((-a q) * f p + a p * f q)) =
              ∑ q : {q : Fin m // q ∈ Im},
                η' (e (Sum.inr (⟨p, hp⟩, q))) * ((-a q.1) * f p + a p * f q.1) := by
            intro p hp
            trans ∑ q : Fin m, (if hq : q ∈ Im then
                η' (e (Sum.inr (⟨p, hp⟩, ⟨q, hq⟩))) * ((-a q) * f p + a p * f q) else 0)
            · refine Finset.sum_congr rfl fun q _ => ?_
              simp only [upm, dif_pos hp]
              split_ifs <;> ring
            · exact sum_ite_subtypeR Im fun q =>
                η' (e (Sum.inr (⟨p, hp⟩, q))) * ((-a q.1) * f p + a p * f q.1)
          have houter :
              (∑ p, ∑ q, upm p q * ((-a q) * f p + a p * f q)) =
              ∑ p : {p : Fin m // p ∈ Ip}, ∑ q : {q : Fin m // q ∈ Im},
                η' (e (Sum.inr (p, q))) * ((-a q.1) * f p.1 + a p.1 * f q.1) := by
            have hstep : ∀ p : Fin m,
                (∑ q, upm p q * ((-a q) * f p + a p * f q)) =
                if hp : p ∈ Ip then
                  ∑ q : {q : Fin m // q ∈ Im},
                    η' (e (Sum.inr (⟨p, hp⟩, q))) * ((-a q.1) * f p + a p * f q.1) else 0 := by
              intro p
              by_cases hp : p ∈ Ip
              · rw [dif_pos hp, hinner p hp]
              · rw [dif_neg hp]
                refine Finset.sum_eq_zero fun q _ => ?_
                simp [upm, hp]
            simp_rw [hstep]
            exact sum_ite_subtypeR Ip fun p =>
              ∑ q : {q : Fin m // q ∈ Im},
                η' (e (Sum.inr (p, q))) * ((-a q.1) * f p.1 + a p.1 * f q.1)
          rw [houter, Fintype.sum_prod_type]
        have hrhs : ∑ idx : Fin m', η' idx *
              (match e.symm idx with
              | Sum.inl i => f i.1
              | Sum.inr pq => (-a pq.2.1) * f pq.1.1 + a pq.1.1 * f pq.2.1) =
            (∑ i : {i : Fin m // i ∈ I0}, η' (e (Sum.inl i)) * f i.1) +
            ∑ pq : {p : Fin m // p ∈ Ip} × {q : Fin m // q ∈ Im},
              η' (e (Sum.inr pq)) * ((-a pq.2.1) * f pq.1.1 + a pq.1.1 * f pq.2.1) := by
          rw [← Equiv.sum_comp e]
          simp only [Idx, Equiv.symm_apply_apply, Fintype.sum_sum_type]
        calc ∑ i, η i * f i
          _ = ∑ i, (u0 i * f i + ((∑ q, upm i q * (-a q)) * f i + (∑ p, upm p i * a p) * f i)) := by
              refine Finset.sum_congr rfl fun i _ => by simp only [η]; ring
          _ = (∑ i, u0 i * f i) + ((∑ i, (∑ q, upm i q * (-a q)) * f i) +
                (∑ i, (∑ p, upm p i * a p) * f i)) := by
              simp only [Finset.sum_add_distrib]
          _ = _ := by rw [h0, h12, hrhs]
      refine Or.inr ⟨η, ?_, ?_, ?_⟩
      · intro i
        have hu0 : 0 ≤ u0 i := by
          simp only [u0]
          split_ifs
          · exact hη'_nonneg _
          · exact le_rfl
        have h1 : 0 ≤ ∑ q : Fin m, upm i q * (-a q) := by
          refine Finset.sum_nonneg fun q _ => ?_
          simp only [upm]
          split_ifs with hp hq
          · have haq : a q < 0 := (Finset.mem_filter.mp hq).2
            exact mul_nonneg (hη'_nonneg _) (neg_nonneg.mpr haq.le)
          · simp
          · simp
        have h2 : 0 ≤ ∑ p : Fin m, upm p i * a p := by
          refine Finset.sum_nonneg fun p _ => ?_
          simp only [upm]
          split_ifs with hp hq
          · have hap : 0 < a p := (Finset.mem_filter.mp hp).2
            exact mul_nonneg (hη'_nonneg _) hap.le
          · simp
          · simp
        exact add_nonneg (add_nonneg hu0 h1) h2
      · intro j
        refine Fin.cases ?_ ?_ j
        · change ∑ i, η i * a i = 0
          rw [hpull a]
          refine Finset.sum_eq_zero fun idx _ => ?_
          cases hr : e.symm idx with
          | inl i =>
            have ha0 : a i.1 = 0 := (Finset.mem_filter.mp i.2).2
            simp [hr, ha0]
          | inr pq =>
            simp only [hr]
            ring
        · intro j'
          change ∑ i, η i * E' i j' = 0
          rw [hpull (fun i => E' i j')]
          have hBeq : ∀ idx : Fin m',
              (match e.symm idx with
              | Sum.inl i => E' i.1 j'
              | Sum.inr pq => (-a pq.2.1) * E' pq.1.1 j' + a pq.1.1 * E' pq.2.1 j') =
              B idx j' := fun _ => rfl
          simp_rw [hBeq]
          exact hη'_E j'
      · rw [hpull rhs]
        have hdeq : ∀ idx : Fin m',
            (match e.symm idx with
            | Sum.inl i => rhs i.1
            | Sum.inr pq => (-a pq.2.1) * rhs pq.1.1 + a pq.1.1 * rhs pq.2.1) = d idx :=
          fun _ => rfl
        simp_rw [hdeq]
        exact hη'_rhs

lemma farkas_elim_real {m p r : ℕ} (C : Matrix (Fin m) (Fin p) ℝ)
    (E : Matrix (Fin m) (Fin r) ℝ) (rhs : Fin m → ℝ) (lam : Fin p → ℝ) :
    (∃ w : Fin r → ℝ, ∀ i, (C *ᵥ lam) i + (E *ᵥ w) i ≤ rhs i) ↔
      ∀ η : Fin m → ℝ, (∀ i, 0 ≤ η i) → (∀ l, ∑ i, η i * E i l = 0) →
        ∑ i, η i * (C *ᵥ lam) i ≤ ∑ i, η i * rhs i := by
  constructor
  · rintro ⟨w, hw⟩ η hη0 hηE
    have hsum : ∑ i, η i * ((C *ᵥ lam) i + (E *ᵥ w) i) ≤ ∑ i, η i * rhs i :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hw i) (hη0 i)
    have hkill : ∑ i, η i * (E *ᵥ w) i = 0 := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun l _ => ?_
      calc ∑ i, η i * (E i l * w l)
        _ = (∑ i, η i * E i l) * w l := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [hηE l, zero_mul]
    simp_rw [mul_add, Finset.sum_add_distrib] at hsum
    linarith
  · intro hdual
    rcases fm_exists_or_cert_real r m E (fun i => rhs i - (C *ᵥ lam) i) with
      ⟨w, hw⟩ | ⟨η, hη0, hηE, hηneg⟩
    · exact ⟨w, fun i => by have := hw i; simp only [Matrix.mulVec, dotProduct] at this ⊢; linarith⟩
    · have := hdual η hη0 hηE
      have hneg : ∑ i, η i * (rhs i - (C *ᵥ lam) i) =
          (∑ i, η i * rhs i) - ∑ i, η i * (C *ᵥ lam) i := by
        simp_rw [mul_sub, Finset.sum_sub_distrib]
      linarith

/-! ## 2. Determinant Bounds & Universal Cofactor Null-Vector Engine -/

lemma abs_det_le_fact_pow {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (B : ℕ)
    (hB : ∀ i j, |A i j| ≤ (B : ℤ)) :
    |A.det| ≤ (n.factorial * B ^ n : ℕ) := by
  rw [Matrix.det_apply']
  calc |∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) * ∏ i, A (σ i) i)|
    _ ≤ ∑ σ : Equiv.Perm (Fin n), |(Equiv.Perm.sign σ : ℤ) * ∏ i, A (σ i) i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm (Fin n), |∏ i, A (σ i) i| := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [abs_mul]
        have hs : |(Equiv.Perm.sign σ : ℤ)| = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
        rw [hs, one_mul]
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), (B : ℤ) ^ n := by
        refine Finset.sum_le_sum fun σ _ => ?_
        rw [Finset.abs_prod]
        calc ∏ i : Fin n, |A (σ i) i|
          _ ≤ ∏ _i : Fin n, (B : ℤ) :=
              Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => hB (σ i) i)
          _ = (B : ℤ) ^ n := by simp
    _ = (n.factorial * B ^ n : ℕ) := by
        simp [Fintype.card_perm, Fintype.card_fin]

def cofactorVec {q : ℕ} (F : Matrix (Fin (q + 1)) (Fin q) ℤ) : Fin (q + 1) → ℤ :=
  fun a => (-1 : ℤ) ^ (a : ℕ) * (F.submatrix a.succAbove id).det

lemma cofactorVec_bound {q : ℕ} (F : Matrix (Fin (q + 1)) (Fin q) ℤ) (B : ℕ)
    (hB : ∀ a j, |F a j| ≤ (B : ℤ)) (a : Fin (q + 1)) :
    |cofactorVec F a| ≤ (q.factorial * B ^ q : ℕ) := by
  unfold cofactorVec
  rw [abs_mul]
  have hsign : |(-1 : ℤ) ^ (a : ℕ)| = 1 := by simp [abs_pow]
  rw [hsign, one_mul]
  exact abs_det_le_fact_pow (F.submatrix a.succAbove id) B fun i j => hB _ _

lemma cofactorVec_orth {q : ℕ} (F : Matrix (Fin (q + 1)) (Fin q) ℤ) (j : Fin q) :
    ∑ a : Fin (q + 1), cofactorVec F a * F a j = 0 := by
  let G : Matrix (Fin (q + 1)) (Fin (q + 1)) ℤ :=
    Matrix.of fun a l => Fin.cases (F a j) (fun j' => F a j') l
  have hzero : G.det = 0 := by
    refine Matrix.det_zero_of_column_eq (Fin.succ_ne_zero j).symm fun k => ?_
    simp [G]
  rw [Matrix.det_succ_column_zero] at hzero
  have hid : ∑ a : Fin (q + 1), (-1 : ℤ) ^ (a : ℕ) * G a 0 * (G.submatrix a.succAbove Fin.succ).det =
      ∑ a : Fin (q + 1), cofactorVec F a * F a j := by
    refine Finset.sum_congr rfl fun a _ => ?_
    have hsub : G.submatrix a.succAbove Fin.succ = F.submatrix a.succAbove id := by
      ext i l
      simp [G]
    rw [hsub]
    simp only [G, Matrix.of_apply, Fin.cases_zero, cofactorVec]
    ring
  rw [← hid]
  exact hzero

private lemma det_ne_zero_of_cols_indep {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : LinearIndependent ℝ (fun l : Fin n => fun a : Fin n => H a l)) :
    H.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hHv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := H)).mpr hdet
  apply hv0
  have hlin : ∑ l : Fin n, v l • (fun a : Fin n => H a l) = 0 := by
    ext a
    have ha := congrFun hHv a
    simpa [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using ha
  exact funext ((Fintype.linearIndependent_iff.mp hH) v hlin)

private lemma det_col0_update_cols_indep {q : ℕ} (F : Matrix (Fin (q + 1)) (Fin q) ℤ)
    (hF : LinearIndependent ℝ (fun j : Fin q => fun a : Fin (q + 1) => (F a j : ℝ)))
    (w : Fin (q + 1) → ℝ) (hw0 : w ≠ 0)
    (hwF : ∀ j : Fin q, ∑ a : Fin (q + 1), w a * (F a j : ℝ) = 0) :
    (Matrix.of (fun a l => Fin.cases (motive := fun _ => ℝ) (w a) (fun j => (F a j : ℝ)) l)).det ≠ 0 := by
  let H : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ :=
    Matrix.of fun a l => Fin.cases (motive := fun _ => ℝ) (w a) (fun j => (F a j : ℝ)) l
  change H.det ≠ 0
  refine det_ne_zero_of_cols_indep H ?_
  rw [Fintype.linearIndependent_iff]
  intro α hα
  have hdot : ∑ a : Fin (q + 1), w a * (∑ l : Fin (q + 1), α l * H a l) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    have ha := congrFun hα a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at ha
    rw [show ∑ l, α l * H a l = ∑ l, H a l * α l from Finset.sum_congr rfl fun _ _ => mul_comm _ _]
    have ha' : ∑ l, H a l * α l = 0 := by
      simpa [mul_comm] using ha
    rw [ha', mul_zero]
  simp_rw [Finset.mul_sum] at hdot
  rw [Finset.sum_comm] at hdot
  have hdot2 : ∑ l : Fin (q + 1), α l * (∑ a : Fin (q + 1), w a * H a l) = 0 := by
    rw [← hdot]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [Fin.sum_univ_succ] at hdot2
  have hrest0 : ∑ j : Fin q, α j.succ * (∑ a, w a * H a j.succ) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    have hj := hwF j
    simp only [H, Matrix.of_apply, Fin.cases_succ]
    rw [hj, mul_zero]
  rw [hrest0, add_zero] at hdot2
  have hw_sq_pos : 0 < ∑ a : Fin (q + 1), w a * H a 0 := by
    simp only [H, Matrix.of_apply, Fin.cases_zero]
    have hex : ∃ a₀ : Fin (q + 1), w a₀ ≠ 0 := by
      by_contra hnone
      push Not at hnone
      exact hw0 (funext hnone)
    obtain ⟨a₀, ha₀⟩ := hex
    exact Finset.sum_pos' (fun a _ => mul_self_nonneg (w a))
      ⟨a₀, Finset.mem_univ a₀, mul_self_pos.mpr ha₀⟩
  have hα0 : α 0 = 0 := (mul_eq_zero.mp hdot2).resolve_right hw_sq_pos.ne'
  have htail : ∑ j : Fin q, α j.succ • (fun a : Fin (q + 1) => (F a j : ℝ)) = 0 := by
    ext a
    have ha := congrFun hα a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at ha ⊢
    rw [Fin.sum_univ_succ, hα0, zero_mul, zero_add] at ha
    simpa [H] using ha
  have hα_succ : ∀ j : Fin q, α j.succ = 0 := (Fintype.linearIndependent_iff.mp hF) _ htail
  intro l
  refine Fin.cases hα0 hα_succ l

private lemma cofactorVec_dot_eq_det {q : ℕ} (F : Matrix (Fin (q + 1)) (Fin q) ℤ)
    (w : Fin (q + 1) → ℝ) :
    (Matrix.of (fun a l => Fin.cases (motive := fun _ => ℝ) (w a) (fun j => (F a j : ℝ)) l)).det =
      ∑ a : Fin (q + 1), w a * (cofactorVec F a : ℝ) := by
  let H : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ :=
    Matrix.of fun a l => Fin.cases (motive := fun _ => ℝ) (w a) (fun j => (F a j : ℝ)) l
  change H.det = _
  rw [Matrix.det_succ_column_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hsub : H.submatrix a.succAbove Fin.succ =
      (Int.castRingHom ℝ).mapMatrix (F.submatrix a.succAbove id) := by
    ext i j
    simp [H]
  rw [hsub, ← RingHom.map_det]
  simp only [H, Matrix.of_apply, Fin.cases_zero, cofactorVec, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.coe_castRingHom]
  ring

lemma cofactorVec_proportional_of_orth {q : ℕ} (F : Matrix (Fin (q + 1)) (Fin q) ℤ)
    (hF : LinearIndependent ℝ (fun j : Fin q => fun a : Fin (q + 1) => (F a j : ℝ)))
    (y : Fin (q + 1) → ℝ) (hy0 : y ≠ 0)
    (hyF : ∀ j : Fin q, ∑ a : Fin (q + 1), y a * (F a j : ℝ) = 0) :
    (cofactorVec F ≠ 0) ∧
    (∀ v : Fin (q + 1) → ℝ, (∀ j : Fin q, ∑ a : Fin (q + 1), v a * (F a j : ℝ) = 0) →
      ∃ c : ℝ, v = c • y) ∧
    ∃ α : ℝ, α ≠ 0 ∧ (fun a => (cofactorVec F a : ℝ)) = α • y := by
  let uR : Fin (q + 1) → ℝ := fun a => (cofactorVec F a : ℝ)
  have hdet_ne : ∑ a : Fin (q + 1), y a * uR a ≠ 0 := by
    rw [← cofactorVec_dot_eq_det F y]
    exact det_col0_update_cols_indep F hF y hy0 hyF
  have hcf0 : cofactorVec F ≠ 0 := by
    intro hz
    apply hdet_ne
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [uR, hz]
  have hunique : ∀ v : Fin (q + 1) → ℝ,
      (∀ j : Fin q, ∑ a : Fin (q + 1), v a * (F a j : ℝ) = 0) →
      ∃ c : ℝ, v = c • y := by
    intro v hvF
    let D := ∑ a : Fin (q + 1), y a * uR a
    let c := (∑ a : Fin (q + 1), v a * uR a) / D
    refine ⟨c, ?_⟩
    let w := v - c • y
    have hwF : ∀ j : Fin q, ∑ a : Fin (q + 1), w a * (F a j : ℝ) = 0 := by
      intro j
      calc ∑ a, w a * (F a j : ℝ)
        _ = (∑ a, v a * (F a j : ℝ)) - c * (∑ a, y a * (F a j : ℝ)) := by
            simp only [w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul,
              Finset.sum_sub_distrib, ← Finset.mul_sum, mul_assoc]
        _ = 0 := by rw [hvF j, hyF j, mul_zero, sub_zero]
    have hwu : ∑ a : Fin (q + 1), w a * uR a = 0 := by
      calc ∑ a, w a * uR a
        _ = (∑ a, v a * uR a) - c * D := by
            simp only [w, D, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul,
              Finset.sum_sub_distrib, ← Finset.mul_sum, mul_assoc]
        _ = 0 := by rw [div_mul_cancel₀ _ hdet_ne, sub_self]
    have hw0 : w = 0 := by
      by_contra hwnz
      have hdet0 := det_col0_update_cols_indep F hF w hwnz hwF
      rw [cofactorVec_dot_eq_det F w] at hdet0
      exact hdet0 hwu
    exact sub_eq_zero.mp hw0
  have huR_orth : ∀ j : Fin q, ∑ a : Fin (q + 1), uR a * (F a j : ℝ) = 0 := by
    intro j
    have hz : ((∑ a : Fin (q + 1), cofactorVec F a * F a j : ℤ) : ℝ) = 0 := by
      rw [cofactorVec_orth F j]; simp
    simpa [uR, Int.cast_sum, Int.cast_mul] using hz
  obtain ⟨α, hα⟩ := hunique uR huR_orth
  have hα0 : α ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hα
    exact hcf0 (funext fun a => by
      have ha : (cofactorVec F a : ℝ) = (0 : ℝ) := congrFun hα a
      exact_mod_cast ha)
  exact ⟨hcf0, hunique, α, hα0, hα⟩

/-! ## 3. Bounded Integral Farkas Projection -/

private lemma exists_int_ray_of_minimal_supp {m r : ℕ} (E : Matrix (Fin m) (Fin r) ℤ)
    (U : ℕ) (hU : 1 ≤ U) (hE : ∀ i l, |E i l| ≤ (U : ℤ))
    (η : Fin m → ℝ) (hη0 : ∀ i, 0 ≤ η i) (hηE : ∀ l, ∑ i, η i * (E i l : ℝ) = 0)
    (hη_nz : η ≠ 0)
    (hmin : ∀ η' : Fin m → ℝ, (∀ i, 0 ≤ η' i) → (∀ l, ∑ i, η' i * (E i l : ℝ) = 0) →
      η' ≠ 0 → ({i : Fin m | η' i ≠ 0} ⊆ {i : Fin m | η i ≠ 0}) →
      {i : Fin m | η' i ≠ 0} = {i : Fin m | η i ≠ 0}) :
    ∃ (η_int : Fin m → ℤ) (c : ℝ),
      0 < c ∧
      (∀ i, 0 ≤ η_int i) ∧
      (∀ i, η_int i ≤ (r.factorial * U ^ r : ℕ)) ∧
      (Finset.univ.filter fun i => η_int i ≠ 0).card ≤ r + 1 ∧
      (∀ l, ∑ i, η_int i * E i l = 0) ∧
      (∀ i, η i = c * (η_int i : ℝ)) := by
  let S : Finset (Fin m) := Finset.univ.filter fun i => η i ≠ 0
  have hS_ne : S.Nonempty := by
    by_contra hsemp
    rw [Finset.not_nonempty_iff_eq_empty] at hsemp
    apply hη_nz
    ext i
    by_contra hi
    have him : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    rw [hsemp] at him
    exact Finset.notMem_empty i him
  let s := S.card
  let eS : Fin s ≃ S := (Fintype.equivFinOfCardEq (Fintype.card_coe S)).symm
  let cols : Set (Fin s → ℝ) := Set.range (fun l : Fin r => fun a : Fin s => (E (eS a).1 l : ℝ))
  obtain ⟨b, hb_sub, hb_span, hb_indep⟩ := exists_linearIndependent ℝ cols
  have hb_fin : b.Finite := Set.Finite.subset (Set.finite_range _) hb_sub
  let J_fin : Finset (Fin s → ℝ) := hb_fin.toFinset
  have hJ_coe : (J_fin : Set (Fin s → ℝ)) = b := hb_fin.coe_toFinset
  let q := J_fin.card
  have hcol_pick : ∀ v ∈ J_fin, ∃ l : Fin r, (fun a : Fin s => (E (eS a).1 l : ℝ)) = v := by
    intro v hv
    have hv_b : v ∈ b := by rw [← hJ_coe]; exact Finset.mem_coe.mpr hv
    exact hb_sub hv_b
  let eJ : Fin q ≃ J_fin := (Fintype.equivFinOfCardEq (Fintype.card_coe J_fin)).symm
  choose colIdx hcolIdx using fun j : Fin q => hcol_pick (eJ j).1 (eJ j).2
  have hq_le_r : q ≤ r := by
    have hinj : Function.Injective colIdx := by
      intro j₁ j₂ heq
      have h12 : (eJ j₁).1 = (eJ j₂).1 := by rw [← hcolIdx j₁, ← hcolIdx j₂, heq]
      exact eJ.injective (Subtype.ext h12)
    simpa [Fintype.card_fin] using Fintype.card_le_of_injective colIdx hinj
  let yS : Fin s → ℝ := fun a => η (eS a).1
  have hyS_pos : ∀ a : Fin s, 0 < yS a := fun a =>
    lt_of_le_of_ne (hη0 (eS a).1) (Finset.mem_filter.mp (eS a).2).2.symm
  have hyS_nz : yS ≠ 0 := by
    intro hz
    obtain ⟨i₀, hi₀⟩ := hS_ne
    have h0 := congrFun hz (eS.symm ⟨i₀, hi₀⟩)
    simp only [yS, Equiv.apply_symm_apply, Pi.zero_apply] at h0
    exact (Finset.mem_filter.mp hi₀).2 h0
  let F : Matrix (Fin s) (Fin q) ℤ := Matrix.of fun a j => E (eS a).1 (colIdx j)
  have hF_indep : LinearIndependent ℝ (fun j : Fin q => fun a : Fin s => (F a j : ℝ)) := by
    have heq : (fun j : Fin q => fun a : Fin s => (F a j : ℝ)) = Subtype.val ∘ eJ := by
      ext j a
      simp only [F, Matrix.of_apply, Function.comp_apply]
      exact congrFun (hcolIdx j) a
    rw [heq]
    have hJ_indep : LinearIndependent ℝ (Subtype.val : J_fin → (Fin s → ℝ)) := by
      refine LinearIndependent.comp hb_indep (fun x : J_fin => ⟨x.1, by rw [← hJ_coe]; exact x.2⟩) ?_
      intro x₁ x₂ h
      exact Subtype.ext (congrArg (Subtype.val : b → (Fin s → ℝ)) h)
    exact hJ_indep.comp eJ eJ.injective
  have hyS_orth : ∀ j : Fin q, ∑ a : Fin s, yS a * (F a j : ℝ) = 0 := by
    intro j
    have hl := hηE (colIdx j)
    have hsub : ∑ i : Fin m, η i * (E i (colIdx j) : ℝ) =
        ∑ i ∈ S, η i * (E i (colIdx j) : ℝ) := by
      symm
      refine Finset.sum_subset (Finset.subset_univ S) fun i _ hi => ?_
      have h0 : η i = 0 := by
        by_contra hne
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
      rw [h0, zero_mul]
    rw [hsub, ← Finset.sum_coe_sort S] at hl
    rw [← eS.sum_comp (fun x : S => η x.1 * (E x.1 (colIdx j) : ℝ))] at hl
    simpa [yS, F] using hl
  have hq1_le_s : q + 1 ≤ s := by
    let vecs : Fin (q + 1) → (Fin s → ℝ) := Fin.cases yS (fun j a => (F a j : ℝ))
    have hvis : LinearIndependent ℝ vecs := by
      rw [Fintype.linearIndependent_iff]
      intro α hα
      have hdot : ∑ a : Fin s, yS a * (∑ k : Fin (q + 1), α k * vecs k a) = 0 := by
        refine Finset.sum_eq_zero fun a _ => ?_
        have ha := congrFun hα a
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at ha
        rw [show ∑ k, α k * vecs k a = ∑ k, vecs k a * α k from Finset.sum_congr rfl fun _ _ => mul_comm _ _]
        have ha' : ∑ k, vecs k a * α k = 0 := by simpa [mul_comm] using ha
        rw [ha', mul_zero]
      simp_rw [Finset.mul_sum] at hdot
      rw [Finset.sum_comm] at hdot
      have hdot2 : ∑ k : Fin (q + 1), α k * (∑ a : Fin s, yS a * vecs k a) = 0 := by
        rw [← hdot]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => by ring
      rw [Fin.sum_univ_succ] at hdot2
      have hrest0 : ∑ j : Fin q, α j.succ * (∑ a : Fin s, yS a * vecs j.succ a) = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        simp only [vecs, Fin.cases_succ]
        rw [hyS_orth j, mul_zero]
      rw [hrest0, add_zero] at hdot2
      have hysq : 0 < ∑ a : Fin s, yS a * vecs 0 a := by
        obtain ⟨a₀, ha₀⟩ := show ∃ a₀ : Fin s, yS a₀ ≠ 0 from by
          by_contra hnone; push Not at hnone; exact hyS_nz (funext hnone)
        simp only [vecs, Fin.cases_zero]
        exact Finset.sum_pos' (fun a _ => mul_self_nonneg _)
          ⟨a₀, Finset.mem_univ a₀, mul_self_pos.mpr ha₀⟩
      have hα0 : α 0 = 0 := (mul_eq_zero.mp hdot2).resolve_right hysq.ne'
      have htail : ∑ j : Fin q, α j.succ • (fun a : Fin s => (F a j : ℝ)) = 0 := by
        ext a
        have ha := congrFun hα a
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at ha ⊢
        rw [Fin.sum_univ_succ, hα0, zero_mul, zero_add] at ha
        simpa [vecs] using ha
      have hαs := (Fintype.linearIndependent_iff.mp hF_indep) _ htail
      exact Fin.cases hα0 hαs
    simpa [Module.finrank_fin_fun] using hvis.fintype_card_le_finrank
  have hs_le_q1 : s ≤ q + 1 := by
    by_contra hgt
    have hq1_lt_s : q + 1 < s := Nat.lt_of_not_ge hgt
    let L : (Fin s → ℝ) →ₗ[ℝ] (Fin q → ℝ) :=
      { toFun := fun v j => ∑ a : Fin s, v a * (F a j : ℝ)
        map_add' := fun u v => by ext j; simp [add_mul, Finset.sum_add_distrib]
        map_smul' := fun c u => by ext j; simp [mul_assoc, Finset.mul_sum] }
    have hrk := LinearMap.finrank_range_add_finrank_ker L
    have hrange : Module.finrank ℝ (LinearMap.range L) ≤ q := by
      simpa [Module.finrank_fin_fun] using Submodule.finrank_le (LinearMap.range L)
    have hker_gt : 1 < Module.finrank ℝ (LinearMap.ker L) := by
      have : Module.finrank ℝ (Fin s → ℝ) = s := Module.finrank_fin_fun ℝ
      omega
    let y_ker : LinearMap.ker L := ⟨yS, by ext j; exact hyS_orth j⟩
    have hy_indep : LinearIndependent ℝ (fun _ : Fin 1 => y_ker) := by
      rw [linearIndependent_unique_iff]
      intro hz
      exact hyS_nz (congrArg Subtype.val hz)
    obtain ⟨v_ker, hv_indep⟩ := exists_linearIndependent_snoc_of_lt_finrank hy_indep hker_gt
    let vS : Fin s → ℝ := v_ker.1
    have hv_orth_J : ∀ j : Fin q, ∑ a : Fin s, vS a * (F a j : ℝ) = 0 := fun j =>
      congrFun v_ker.2 j
    have hv_orth_all : ∀ l : Fin r, ∑ a : Fin s, vS a * (E (eS a).1 l : ℝ) = 0 := by
      intro l
      let cl : Fin s → ℝ := fun a => (E (eS a).1 l : ℝ)
      have hcl_mem : cl ∈ Submodule.span ℝ (J_fin : Set (Fin s → ℝ)) := by
        rw [hJ_coe, hb_span]
        exact Submodule.subset_span ⟨l, rfl⟩
      rw [Submodule.mem_span_finset] at hcl_mem
      obtain ⟨β, _, hβ⟩ := hcl_mem
      calc ∑ a : Fin s, vS a * cl a
        _ = ∑ a : Fin s, vS a * (∑ u ∈ J_fin, β u * u a) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            have ha := congrFun hβ a
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at ha
            rw [← ha]
        _ = ∑ u ∈ J_fin, β u * (∑ a : Fin s, vS a * u a) := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun u _ => ?_
            refine Finset.sum_congr rfl fun a _ => by ring
        _ = 0 := by
            refine Finset.sum_eq_zero fun u hu => ?_
            obtain ⟨j, hj⟩ := eJ.surjective ⟨u, hu⟩
            have hu_eq : (eJ j).1 = u := congrArg (Subtype.val : J_fin → Fin s → ℝ) hj
            have huj : u = fun a => (F a j : ℝ) := by
              rw [← hu_eq, ← hcolIdx j]; rfl
            rw [huj, hv_orth_J j, mul_zero]
    let v : Fin m → ℝ := fun i => if h : i ∈ S then vS (eS.symm ⟨i, h⟩) else 0
    have hvE : ∀ l : Fin r, ∑ i : Fin m, v i * (E i l : ℝ) = 0 := by
      intro l
      calc ∑ i : Fin m, v i * (E i l : ℝ)
        _ = ∑ i : Fin m, if h : i ∈ S then vS (eS.symm ⟨i, h⟩) * (E i l : ℝ) else 0 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [v]; split_ifs <;> ring
        _ = ∑ x : S, vS (eS.symm x) * (E x.1 l : ℝ) :=
            sum_ite_subtypeR S fun x => vS (eS.symm x) * (E x.1 l : ℝ)
        _ = ∑ a : Fin s, vS a * (E (eS a).1 l : ℝ) := by
            rw [← eS.sum_comp (fun x : S => vS (eS.symm x) * (E x.1 l : ℝ))]
            refine Finset.sum_congr rfl fun a _ => by simp
        _ = 0 := hv_orth_all l
    have hv_nz : v ≠ 0 := by
      intro hzv
      have hvS0 : vS = 0 := by
        ext a
        have ha := congrFun hzv (eS a).1
        simp only [v, dif_pos (eS a).2, Subtype.coe_eta, Equiv.symm_apply_apply, Pi.zero_apply] at ha
        exact ha
      have hvker0 : v_ker = 0 := Subtype.ext hvS0
      have hlin : (0 : ℝ) • y_ker + (1 : ℝ) • v_ker = 0 := by
        rw [hvker0, zero_smul, smul_zero, add_zero]
      have hbad := (Fintype.linearIndependent_iff.mp hv_indep) ![0, 1] (by
        rw [Fin.sum_univ_two]; exact hlin)
      have h1 := hbad 1
      norm_num at h1
    have hnot_mult : ¬ ∃ c : ℝ, v = c • η := by
      rintro ⟨c, hc⟩
      have hv_eq : v_ker = c • y_ker := by
        apply Subtype.ext
        ext a
        have ha := congrFun hc (eS a).1
        simpa [v, yS, y_ker, vS] using ha
      have hlin : (-c) • y_ker + (1 : ℝ) • v_ker = 0 := by
        apply Subtype.ext
        change (-c) • yS + (1:ℝ) • vS = 0
        rw [show vS = c • yS from congrArg Subtype.val hv_eq, one_smul, neg_smul, neg_add_cancel]
      have hbad := (Fintype.linearIndependent_iff.mp hv_indep) ![-c, 1] (by
        rw [Fin.sum_univ_two]; exact hlin)
      have h1 := hbad 1
      norm_num at h1
    have hex_pos : ∃ i : Fin m, 0 < v i ∨ 0 < -v i := by
      obtain ⟨i₀, hi₀⟩ := show ∃ i₀ : Fin m, v i₀ ≠ 0 from by
        by_contra hnone; push Not at hnone; exact hv_nz (funext hnone)
      rcases lt_or_gt_of_ne hi₀ with hlt | hgt
      · exact ⟨i₀, Or.inr (neg_pos.mpr hlt)⟩
      · exact ⟨i₀, Or.inl hgt⟩
    have step_drop : ∀ w : Fin m → ℝ, (∀ i, η i = 0 → w i = 0) →
        (∀ l, ∑ i, w i * (E i l : ℝ) = 0) → (∃ i, 0 < w i) → ¬ (∃ c : ℝ, w = c • η) → False := by
      intro w hw_supp hwE ⟨iw, hiw⟩ hwnot
      let Iw := Finset.univ.filter fun i => 0 < w i
      have hIw_ne : Iw.Nonempty := ⟨iw, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiw⟩⟩
      let t := Iw.inf' hIw_ne fun i => η i / w i
      obtain ⟨i_min, hi_min_mem, hi_min_eq⟩ := Finset.exists_mem_eq_inf' hIw_ne fun i => η i / w i
      have hw_imin : 0 < w i_min := (Finset.mem_filter.mp hi_min_mem).2
      have hη_imin_ne : η i_min ≠ 0 := fun h0 => by linarith [hw_supp i_min h0]
      have hη_imin : 0 < η i_min := lt_of_le_of_ne (hη0 i_min) hη_imin_ne.symm
      have ht_pos : 0 < t := by dsimp only [t]; rw [hi_min_eq]; exact div_pos hη_imin hw_imin
      let η' : Fin m → ℝ := fun i => η i - t * w i
      have hη'0 : ∀ i, 0 ≤ η' i := by
        intro i
        by_cases hwi : 0 < w i
        · have hle : t ≤ η i / w i :=
            Finset.inf'_le (f := fun i => η i / w i) (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hwi⟩)
          have := (le_div_iff₀ hwi).mp hle
          simp only [η']; linarith
        · push Not at hwi
          have : 0 ≤ -(t * w i) := neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos ht_pos.le hwi)
          have h0 := hη0 i
          simp only [η']; linarith
      have hη'E : ∀ l, ∑ i, η' i * (E i l : ℝ) = 0 := by
        intro l
        calc ∑ i, η' i * (E i l : ℝ)
          _ = (∑ i, η i * (E i l : ℝ)) - t * (∑ i, w i * (E i l : ℝ)) := by
              simp only [η', sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, mul_assoc]
          _ = 0 := by rw [hηE l, hwE l, mul_zero, sub_zero]
      have hη'nz : η' ≠ 0 := by
        intro hz
        apply hwnot
        refine ⟨t⁻¹, funext fun i => ?_⟩
        have hi := congrFun hz i
        simp only [η', Pi.zero_apply] at hi
        have heq : t * w i = η i := by linarith
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [← heq, inv_mul_cancel_left₀ ht_pos.ne']
      have hsub_supp : {i : Fin m | η' i ≠ 0} ⊆ {i : Fin m | η i ≠ 0} := by
        intro i hi h0
        apply hi
        simp only [η', h0, hw_supp i h0, mul_zero, sub_zero]
      have heq_supp := hmin η' hη'0 hη'E hη'nz hsub_supp
      have hi_min_in : i_min ∈ {i : Fin m | η i ≠ 0} := hη_imin_ne
      rw [← heq_supp] at hi_min_in
      apply hi_min_in
      simp only [η', ← hi_min_eq]
      change η i_min - (Iw.inf' hIw_ne fun i => η i / w i) * w i_min = 0
      rw [hi_min_eq, div_mul_cancel₀ _ hw_imin.ne', sub_self]
    have hv_supp : ∀ i, η i = 0 → v i = 0 := fun i hi => by
      simp only [v]
      split_ifs with h
      · exact False.elim ((Finset.mem_filter.mp h).2 hi)
      · rfl
    rcases hex_pos with ⟨i₀, hi₀ | hi₀⟩
    · exact step_drop v hv_supp hvE ⟨i₀, hi₀⟩ hnot_mult
    · refine step_drop (-v) (fun i hi => by simp [hv_supp i hi]) (fun l => by
        simp [neg_mul, Finset.sum_neg_distrib, hvE l]) ⟨i₀, hi₀⟩ ?_
      rintro ⟨c, hc⟩
      exact hnot_mult ⟨-c, by ext i; have := congrFun hc i; simp at this ⊢; linarith⟩
  have hs_eq : s = q + 1 := Nat.le_antisymm hs_le_q1 hq1_le_s
  let e_sq : Fin (q + 1) ≃ Fin s := finCongr hs_eq.symm
  let F1 : Matrix (Fin (q + 1)) (Fin q) ℤ := F.submatrix e_sq id
  let y1 : Fin (q + 1) → ℝ := yS ∘ e_sq
  have hy1_nz : y1 ≠ 0 := fun hz => hyS_nz (funext fun a => by
    have := congrFun hz (e_sq.symm a); simpa [y1] using this)
  have hF1_indep : LinearIndependent ℝ (fun j : Fin q => fun a : Fin (q + 1) => (F1 a j : ℝ)) := by
    rw [Fintype.linearIndependent_iff]
    intro α hα
    refine Fintype.linearIndependent_iff.mp hF_indep α ?_
    ext a
    have ha := congrFun hα (e_sq.symm a)
    simpa [F1] using ha
  have hy1_orth : ∀ j : Fin q, ∑ a : Fin (q + 1), y1 a * (F1 a j : ℝ) = 0 := by
    intro j
    rw [← hyS_orth j]
    exact e_sq.sum_comp (fun a => yS a * (F a j : ℝ))
  obtain ⟨hcf0, _, α, hα0, hα⟩ := cofactorVec_proportional_of_orth F1 hF1_indep y1 hy1_nz hy1_orth
  let sgn : ℤ := if 0 < α then 1 else -1
  let cfS : Fin s → ℤ := fun a => sgn * cofactorVec F1 (e_sq.symm a)
  let c : ℝ := |(α⁻¹ : ℝ)|
  have hc_pos : 0 < c := abs_pos.mpr (inv_ne_zero hα0)
  have hyS_eq : ∀ a : Fin s, yS a = c * (cfS a : ℝ) := by
    intro a
    have ha := congrFun hα (e_sq.symm a)
    simp only [y1, Function.comp_apply, Equiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul] at ha
    have hcf : (cofactorVec F1 (e_sq.symm a) : ℝ) = α * yS a := ha
    rcases lt_or_gt_of_ne hα0 with hlt | hgt
    · have hsgn : sgn = -1 := by simp [sgn, hlt.not_gt]
      have hc_eq : c = -α⁻¹ := by
        simp only [c, abs_of_neg (inv_lt_zero.mpr hlt)]
      simp only [cfS, hsgn, Int.cast_mul, Int.cast_neg, Int.cast_one, hcf, hc_eq]
      field_simp [hlt.ne]
    · have hsgn : sgn = 1 := by simp [sgn, hgt]
      have hc_eq : c = α⁻¹ := by
        simp only [c, abs_of_pos (inv_pos.mpr hgt)]
      simp only [cfS, hsgn, Int.cast_mul, Int.cast_one, hcf, hc_eq]
      field_simp [hgt.ne']
  let η_int : Fin m → ℤ := fun i => if h : i ∈ S then cfS (eS.symm ⟨i, h⟩) else 0
  refine ⟨η_int, c, hc_pos, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp only [η_int]
    split_ifs with h
    · have hpos : 0 < c * (cfS (eS.symm ⟨i, h⟩) : ℝ) := by
        rw [← hyS_eq]; exact hyS_pos _
      have hposR : 0 < (cfS (eS.symm ⟨i, h⟩) : ℝ) := by nlinarith
      exact_mod_cast hposR.le
    · exact le_rfl
  · intro i
    simp only [η_int]
    split_ifs with h
    · have hbd : |cfS (eS.symm ⟨i, h⟩)| ≤ (q.factorial * U ^ q : ℕ) := by
        simp only [cfS]
        have hsgn_abs : |sgn| = 1 := by simp only [sgn]; split_ifs <;> simp
        rw [abs_mul, hsgn_abs, one_mul]
        exact cofactorVec_bound F1 U (fun _ _ => hE _ _) _
      have hmono : q.factorial * U ^ q ≤ r.factorial * U ^ r :=
        Nat.mul_le_mul (Nat.factorial_le hq_le_r) (Nat.pow_le_pow_right hU hq_le_r)
      exact le_trans (le_trans (le_abs_self _) hbd) (by exact_mod_cast hmono)
    · exact Int.natCast_nonneg _
  · have hsub : (Finset.univ.filter fun i => η_int i ≠ 0) ⊆ S := by
      intro i hi
      by_contra hni
      have h0 : η_int i = 0 := by simp [η_int, hni]
      exact (Finset.mem_filter.mp hi).2 h0
    have hcard := Finset.card_le_card hsub
    change _ ≤ r + 1
    omega
  · intro l
    have hη_eq : ∀ i, η i = c * (η_int i : ℝ) := by
      intro i
      simp only [η_int]
      split_ifs with h
      · have := hyS_eq (eS.symm ⟨i, h⟩)
        simpa [yS] using this
      · have h0 : η i = 0 := by
          by_contra hne; exact h (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
        rw [h0, Int.cast_zero, mul_zero]
    have hreal : (∑ i : Fin m, (η_int i : ℝ) * (E i l : ℝ)) = 0 := by
      have hc0 := hηE l
      have hid : ∑ i : Fin m, η i * (E i l : ℝ) = c * ∑ i : Fin m, (η_int i : ℝ) * (E i l : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hη_eq i, mul_assoc]
      rw [hid] at hc0
      exact (mul_eq_zero.mp hc0).resolve_left hc_pos.ne'
    exact_mod_cast hreal
  · intro i
    simp only [η_int]
    split_ifs with h
    · have := hyS_eq (eS.symm ⟨i, h⟩)
      simpa [yS] using this
    · have h0 : η i = 0 := by
        by_contra hne; exact h (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
      rw [h0, Int.cast_zero, mul_zero]

private lemma farkas_conic_decomp_aux {m p r : ℕ} (C : Matrix (Fin m) (Fin p) ℤ)
    (E : Matrix (Fin m) (Fin r) ℤ) (rhs : Fin m → ℤ) (U H : ℕ) (hU : 1 ≤ U)
    (hH : (r + 1).factorial * U ^ (r + 1) ≤ H)
    (hC : ∀ i j, |C i j| ≤ (U : ℤ)) (hE : ∀ i l, |E i l| ≤ (U : ℤ)) (hrhs : ∀ i, |rhs i| ≤ (U : ℤ))
    (lam : Fin p → ℝ)
    (h_small : ∀ η_int : Fin m → ℤ,
      (∀ i, 0 ≤ η_int i) → (∀ l, ∑ i, η_int i * E i l = 0) →
      (∀ j, |∑ i, η_int i * C i j| ≤ (H : ℤ)) →
      |∑ i, η_int i * rhs i| ≤ (H : ℤ) →
      ∑ i, (η_int i : ℝ) * ((C.map (Int.cast : ℤ → ℝ)) *ᵥ lam) i ≤
        ∑ i, (η_int i : ℝ) * (rhs i : ℝ)) :
    ∀ k : ℕ, ∀ η : Fin m → ℝ,
      (Finset.univ.filter fun i => η i ≠ 0).card ≤ k →
      (∀ i, 0 ≤ η i) → (∀ l, ∑ i, η i * (E i l : ℝ) = 0) →
      ∑ i, η i * ((C.map (Int.cast : ℤ → ℝ)) *ᵥ lam) i ≤ ∑ i, η i * (rhs i : ℝ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro η hcard hη0 hηE
    by_cases hη_nz : η = 0
    · simp [hη_nz]
    · by_cases hmin : ∀ η' : Fin m → ℝ, (∀ i, 0 ≤ η' i) → (∀ l, ∑ i, η' i * (E i l : ℝ) = 0) →
          η' ≠ 0 → ({i : Fin m | η' i ≠ 0} ⊆ {i : Fin m | η i ≠ 0}) →
          {i : Fin m | η' i ≠ 0} = {i : Fin m | η i ≠ 0}
      · obtain ⟨η_int, c, hc_pos, h0, hbd, hsupp_card, hE0, hη_eq⟩ :=
          exists_int_ray_of_minimal_supp E U hU hE η hη0 hηE hη_nz hmin
        let supp := Finset.univ.filter fun i => η_int i ≠ 0
        have hsum_int : ∀ f : Fin m → ℤ, (∀ i, |f i| ≤ (U : ℤ)) →
            |∑ i, η_int i * f i| ≤ (H : ℤ) := by
          intro f hf
          calc |∑ i : Fin m, η_int i * f i|
            _ = |∑ i ∈ supp, η_int i * f i| := by
                congr 1
                symm
                refine Finset.sum_subset (Finset.subset_univ supp) fun i _ hi => ?_
                have hi0 : η_int i = 0 := by
                  by_contra hne; exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
                rw [hi0, zero_mul]
            _ ≤ ∑ i ∈ supp, |η_int i * f i| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _i ∈ supp, ((r.factorial * U ^ r : ℕ) : ℤ) * (U : ℤ) := by
                refine Finset.sum_le_sum fun i _ => ?_
                rw [abs_mul, abs_of_nonneg (h0 i)]
                exact mul_le_mul (hbd i) (hf i) (abs_nonneg _) (Int.natCast_nonneg _)
            _ = (supp.card : ℤ) * (((r.factorial * U ^ r : ℕ) : ℤ) * (U : ℤ)) := by
                simp
            _ ≤ ((r + 1 : ℕ) : ℤ) * (((r.factorial * U ^ r : ℕ) : ℤ) * (U : ℤ)) := by
                refine mul_le_mul_of_nonneg_right (by exact_mod_cast hsupp_card)
                  (mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
            _ = (((r + 1).factorial * U ^ (r + 1) : ℕ) : ℤ) := by
                push_cast [Nat.factorial_succ, pow_succ]
                ring
            _ ≤ (H : ℤ) := by exact_mod_cast hH
        have h_base := h_small η_int h0 hE0 (fun j => hsum_int (fun i => C i j) (fun i => hC i j))
          (hsum_int rhs hrhs)
        have hL : ∑ i, η i * ((C.map (Int.cast : ℤ → ℝ)) *ᵥ lam) i =
            c * ∑ i, (η_int i : ℝ) * ((C.map (Int.cast : ℤ → ℝ)) *ᵥ lam) i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by rw [hη_eq i, mul_assoc]
        have hR : ∑ i, η i * (rhs i : ℝ) = c * ∑ i, (η_int i : ℝ) * (rhs i : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by rw [hη_eq i, mul_assoc]
        rw [hL, hR]
        exact mul_le_mul_of_nonneg_left h_base hc_pos.le
      · push Not at hmin
        obtain ⟨η', hη'0, hη'E, hη'_nz, hsub, hne⟩ := hmin
        have hproper : {i : Fin m | η' i ≠ 0} ⊂ {i : Fin m | η i ≠ 0} :=
          ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
        have hex_pos : ∃ i₀, 0 < η' i₀ := by
          obtain ⟨i₀, hi₀⟩ := show ∃ i₀ : Fin m, η' i₀ ≠ 0 from by
            by_contra hnone; push Not at hnone; exact hη'_nz (funext hnone)
          exact ⟨i₀, lt_of_le_of_ne (hη'0 i₀) hi₀.symm⟩
        let S' := Finset.univ.filter fun i => 0 < η' i
        have hS'_ne : S'.Nonempty := by
          obtain ⟨i₀, hi₀⟩ := hex_pos
          exact ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, hi₀⟩⟩
        let t := S'.inf' hS'_ne fun i => η i / η' i
        obtain ⟨i_min, hi_min_mem, hi_min_eq⟩ := Finset.exists_mem_eq_inf' hS'_ne fun i => η i / η' i
        have hη'_min : 0 < η' i_min := (Finset.mem_filter.mp hi_min_mem).2
        have hη_min_ne : η i_min ≠ 0 := hsub hη'_min.ne'
        have hη_min : 0 < η i_min := lt_of_le_of_ne (hη0 i_min) hη_min_ne.symm
        have ht_pos : 0 < t := by dsimp only [t]; rw [hi_min_eq]; exact div_pos hη_min hη'_min
        let η'' : Fin m → ℝ := fun i => η i - t * η' i
        have hη''0 : ∀ i, 0 ≤ η'' i := by
          intro i
          by_cases hwi : 0 < η' i
          · have hle : t ≤ η i / η' i :=
              Finset.inf'_le (f := fun i => η i / η' i) (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hwi⟩)
            have := (le_div_iff₀ hwi).mp hle
            simp only [η'']; linarith
          · have h0' : η' i = 0 := le_antisymm (not_lt.mp hwi) (hη'0 i)
            dsimp only [η'']
            rw [h0', mul_zero, sub_zero]
            exact hη0 i
        have hη''E : ∀ l, ∑ i, η'' i * (E i l : ℝ) = 0 := by
          intro l
          calc ∑ i, η'' i * (E i l : ℝ)
            _ = (∑ i, η i * (E i l : ℝ)) - t * (∑ i, η' i * (E i l : ℝ)) := by
                simp only [η'', sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, mul_assoc]
            _ = 0 := by rw [hηE l, hη'E l, mul_zero, sub_zero]
        have hS'_card_lt : (Finset.univ.filter fun i => η' i ≠ 0).card < k := by
          refine lt_of_lt_of_le ?_ hcard
          refine Finset.card_lt_card ?_
          rw [Finset.ssubset_iff_of_subset]
          · have hex_diff : ∃ i₀ : Fin m, η i₀ ≠ 0 ∧ η' i₀ = 0 := by
              by_contra hnone
              push Not at hnone
              apply hne
              exact Set.Subset.antisymm hsub fun i hi => hnone i hi
            obtain ⟨i₀, hi₀_mem, hi₀_nmem⟩ := hex_diff
            exact ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, hi₀_mem⟩,
              fun hmem => (Finset.mem_filter.mp hmem).2 hi₀_nmem⟩
          · intro i hi
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hsub (Finset.mem_filter.mp hi).2⟩
        have hS''_card_lt : (Finset.univ.filter fun i => η'' i ≠ 0).card < k := by
          refine lt_of_lt_of_le ?_ hcard
          refine Finset.card_lt_card ?_
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨i_min, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hη_min_ne⟩, fun hmem => ?_⟩
            apply (Finset.mem_filter.mp hmem).2
            change η i_min - (S'.inf' hS'_ne fun i => η i / η' i) * η' i_min = 0
            rw [hi_min_eq, div_mul_cancel₀ _ hη'_min.ne', sub_self]
          · intro i hi
            rw [Finset.mem_filter] at hi ⊢
            refine ⟨Finset.mem_univ i, fun h0 => hi.2 ?_⟩
            have h0' : η' i = 0 := by
              by_contra hne'
              exact hsub hne' h0
            simp [η'', h0, h0']
        have h1 := ih _ hS'_card_lt η' le_rfl hη'0 hη'E
        have h2 := ih _ hS''_card_lt η'' le_rfl hη''0 hη''E
        have hcombL : ∑ i, η i * ((C.map (Int.cast : ℤ → ℝ)) *ᵥ lam) i =
            t * (∑ i, η' i * ((C.map (Int.cast : ℤ → ℝ)) *ᵥ lam) i) +
            ∑ i, η'' i * ((C.map (Int.cast : ℤ → ℝ)) *ᵥ lam) i := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => by simp only [η'']; ring
        have hcombR : ∑ i, η i * (rhs i : ℝ) =
            t * (∑ i, η' i * (rhs i : ℝ)) + ∑ i, η'' i * (rhs i : ℝ) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => by simp only [η'']; ring
        rw [hcombL, hcombR]
        exact add_le_add (mul_le_mul_of_nonneg_left h1 ht_pos.le) h2

lemma farkas_project_bounded {m p r : ℕ} (C : Matrix (Fin m) (Fin p) ℤ)
    (E : Matrix (Fin m) (Fin r) ℤ) (rhs : Fin m → ℤ) (U H : ℕ) (hU : 1 ≤ U)
    (hH : (r + 1).factorial * U ^ (r + 1) ≤ H)
    (hC : ∀ i j, |C i j| ≤ (U : ℤ)) (hE : ∀ i l, |E i l| ≤ (U : ℤ)) (hrhs : ∀ i, |rhs i| ≤ (U : ℤ)) :
    ∃ (m_proj : ℕ) (M_proj : Matrix (Fin m_proj) (Fin p) ℤ) (b_proj : Fin m_proj → ℤ),
      (∀ i j, |M_proj i j| ≤ (H : ℤ)) ∧
      (∀ i, |b_proj i| ≤ (H : ℤ)) ∧
      ((rhs = 0) → ∀ i, b_proj i = 0) ∧
      ∀ lam : Fin p → ℝ,
        (∃ w : Fin r → ℝ, ∀ i,
          ((C.map (Int.cast : ℤ → ℝ)) *ᵥ lam) i + ((E.map (Int.cast : ℤ → ℝ)) *ᵥ w) i ≤ (rhs i : ℝ)) ↔
        ∀ i, ((M_proj.map (Int.cast : ℤ → ℝ)) *ᵥ lam) i ≤ (b_proj i : ℝ) := by
  let box : Finset ((Fin p → ℤ) × ℤ) :=
    (Fintype.piFinset fun _ : Fin p => Finset.Icc (-(H : ℤ)) (H : ℤ)) ×ˢ Finset.Icc (-(H : ℤ)) (H : ℤ)
  let P_wit : (Fin p → ℤ) × ℤ → Prop := fun ab =>
    ∃ η_int : Fin m → ℤ,
      (∀ i, 0 ≤ η_int i) ∧ (∀ l, ∑ i, η_int i * E i l = 0) ∧
      (∀ j, ab.1 j = ∑ i, η_int i * C i j) ∧ ab.2 = ∑ i, η_int i * rhs i
  let valid : Finset ((Fin p → ℤ) × ℤ) := box.filter P_wit
  let m_proj := valid.card
  let eV : Fin m_proj ≃ valid := (Fintype.equivFinOfCardEq (Fintype.card_coe valid)).symm
  let M_proj : Matrix (Fin m_proj) (Fin p) ℤ := Matrix.of fun i j => (eV i).1.1 j
  let b_proj : Fin m_proj → ℤ := fun i => (eV i).1.2
  refine ⟨m_proj, M_proj, b_proj, ?_, ?_, ?_, ?_⟩
  · intro i j
    have hmem : (eV i).1 ∈ box := (Finset.mem_filter.mp (eV i).2).1
    have h1 := (Fintype.mem_piFinset.mp (Finset.mem_product.mp hmem).1) j
    exact abs_le.mpr (Finset.mem_Icc.mp h1)
  · intro i
    have hmem : (eV i).1 ∈ box := (Finset.mem_filter.mp (eV i).2).1
    have h2 := Finset.mem_Icc.mp (Finset.mem_product.mp hmem).2
    exact abs_le.mpr h2
  · intro hr0 i
    obtain ⟨η_int, _, _, _, hb⟩ := (Finset.mem_filter.mp (eV i).2).2
    simp only [b_proj, hb, hr0, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  · intro lam
    let CR := C.map (Int.cast : ℤ → ℝ)
    let ER := E.map (Int.cast : ℤ → ℝ)
    rw [farkas_elim_real CR ER (fun i => (rhs i : ℝ)) lam]
    constructor
    · intro hdual i
      obtain ⟨η_int, hη0, hηE, hM, hb⟩ := (Finset.mem_filter.mp (eV i).2).2
      have hreal := hdual (fun k => (η_int k : ℝ))
        (fun k => Int.cast_nonneg (hη0 k))
        (fun l => by
          have hl : ((∑ k, η_int k * E k l : ℤ) : ℝ) = 0 := by rw [hηE l]; simp
          simpa [ER, Int.cast_sum, Int.cast_mul] using hl)
      have hL : ((M_proj.map (Int.cast : ℤ → ℝ)) *ᵥ lam) i =
          ∑ k, (η_int k : ℝ) * (CR *ᵥ lam) k := by
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, M_proj, Matrix.of_apply]
        calc ∑ j : Fin p, ((eV i).1.1 j : ℝ) * lam j
          _ = ∑ j : Fin p, (∑ k : Fin m, (η_int k : ℝ) * (C k j : ℝ)) * lam j := by
              refine Finset.sum_congr rfl fun j _ => ?_
              have hj : ((eV i).1.1 j : ℝ) = ∑ k, (η_int k : ℝ) * (C k j : ℝ) := by
                have := hM j
                exact_mod_cast this
              rw [hj]
          _ = ∑ k : Fin m, (η_int k : ℝ) * ∑ j : Fin p, (C k j : ℝ) * lam j := by
              simp_rw [Finset.sum_mul, mul_assoc]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Finset.mul_sum]
      have hR : (b_proj i : ℝ) = ∑ k, (η_int k : ℝ) * (rhs k : ℝ) := by
        have : (b_proj i : ℝ) = ((∑ k, η_int k * rhs k : ℤ) : ℝ) := by exact_mod_cast hb
        simpa [Int.cast_sum, Int.cast_mul] using this
      rw [hL, hR]
      exact hreal
    · intro hproj η hη0 hηE
      have hsmall : ∀ η_int : Fin m → ℤ,
          (∀ k, 0 ≤ η_int k) → (∀ l, ∑ k, η_int k * E k l = 0) →
          (∀ j, |∑ k, η_int k * C k j| ≤ (H : ℤ)) →
          |∑ k, η_int k * rhs k| ≤ (H : ℤ) →
          ∑ k, (η_int k : ℝ) * (CR *ᵥ lam) k ≤ ∑ k, (η_int k : ℝ) * (rhs k : ℝ) := by
        intro η_int h0 hE0 hbdC hbdr
        let ab : (Fin p → ℤ) × ℤ := (fun j => ∑ k, η_int k * C k j, ∑ k, η_int k * rhs k)
        have hab_mem : ab ∈ valid := by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun j =>
            Finset.mem_Icc.mpr (abs_le.mp (hbdC j)),
            Finset.mem_Icc.mpr (abs_le.mp hbdr)⟩,
            ⟨η_int, h0, hE0, fun _ => rfl, rfl⟩⟩
        let i := eV.symm ⟨ab, hab_mem⟩
        have hi := hproj i
        have hL : ((M_proj.map (Int.cast : ℤ → ℝ)) *ᵥ lam) i =
            ∑ k, (η_int k : ℝ) * (CR *ᵥ lam) k := by
          simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, M_proj, Matrix.of_apply,
            i, Equiv.apply_symm_apply, ab]
          calc ∑ j : Fin p, ((∑ k : Fin m, η_int k * C k j : ℤ) : ℝ) * lam j
            _ = ∑ j : Fin p, (∑ k : Fin m, (η_int k : ℝ) * (C k j : ℝ)) * lam j := by
                refine Finset.sum_congr rfl fun j _ => ?_
                simp [Int.cast_sum, Int.cast_mul]
            _ = ∑ k : Fin m, (η_int k : ℝ) * ∑ j : Fin p, (C k j : ℝ) * lam j := by
                simp_rw [Finset.sum_mul, mul_assoc]
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun k _ => ?_
                rw [Finset.mul_sum]
        have hR : (b_proj i : ℝ) = ∑ k, (η_int k : ℝ) * (rhs k : ℝ) := by
          simp only [b_proj, i, Equiv.apply_symm_apply, ab, Int.cast_sum, Int.cast_mul]
        rw [hL, hR] at hi
        exact hi
      exact farkas_conic_decomp_aux C E rhs U H hU hH hC hE hrhs lam hsmall
        (Finset.univ.filter fun k => η k ≠ 0).card η le_rfl hη0 (by simpa [ER] using hηE)


private lemma local_recession_zero_desc (I : Instance) (M : ℕ)
    (hbox : ∀ t, ∀ p ∈ I.P t, InBox M p) (D : IntDesc I) (hD : D.Describes)
    (t : Fin I.τ) (x : Fin I.d → ℤ) (u₀ : Fin I.k → ℝ)
    (hp₀ : (x, u₀) ∈ I.S t) (w : Fin I.k → ℝ)
    (hw : ∀ i : Fin (D.mL t), ∑ b, (D.LB t i b : ℝ) * w b ≤ 0) :
    w = 0 := by
  have hp₀_loc := (hD.2 t (Gen.toReal (x, u₀))).mpr hp₀
  have hmem : ∀ α : ℝ, 0 ≤ α → ((fun i => (x i : ℝ)), u₀ + α • w) ∈ I.P t := by
    intro α hα
    rw [← hD.2]
    intro i
    have hi₀ := hp₀_loc i
    have hwi := hw i
    have hsum : (∑ a, (D.LA t i a : ℝ) * (x a : ℝ)) +
          ∑ b, (D.LB t i b : ℝ) * (u₀ b + α * w b) =
        ((∑ a, (D.LA t i a : ℝ) * (x a : ℝ)) + ∑ b, (D.LB t i b : ℝ) * u₀ b) +
          α * ∑ b, (D.LB t i b : ℝ) * w b := by
      simp_rw [mul_add, Finset.sum_add_distrib, mul_left_comm, ← Finset.mul_sum]
      ring
    change (∑ a, (D.LA t i a : ℝ) * (x a : ℝ)) + ∑ b, (D.LB t i b : ℝ) * u₀ b ≤ _ at hi₀
    change (∑ a, (D.LA t i a : ℝ) * (x a : ℝ)) + ∑ b, (D.LB t i b : ℝ) * (u₀ b + α * w b) ≤ _
    rw [hsum]
    exact (add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos hα hwi)).trans hi₀
  ext b
  by_contra hne
  have habs_pos : 0 < |w b| := abs_pos.mpr hne
  let α : ℝ := ((M : ℝ) + |u₀ b| + 1) / |w b|
  have hα : 0 ≤ α := by positivity
  have hbx := (hbox t _ (hmem α hα)).2 b
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hbx
  have htri : |α * w b| - |u₀ b| ≤ |u₀ b + α * w b| := by
    have := abs_sub_abs_le_abs_sub (α * w b) (-u₀ b)
    simpa [abs_neg, sub_neg_eq_add, add_comm] using this
  have hprod : |α * w b| = (M : ℝ) + |u₀ b| + 1 := by
    rw [abs_mul, abs_of_nonneg hα, div_mul_cancel₀ _ habs_pos.ne']
  linarith


private def cx {I : Instance} (D : IntDesc I) (i : Fin D.mW) (t : Fin I.τ) (x : Fin I.d → ℤ) :=
  (∑ j, D.WY t i j * x j) + D.WN i t

private def rv {I : Instance} (D : IntDesc I) (i : Fin D.mW) (t : Fin I.τ) (g : Gen I.d I.k) : ℝ :=
  (cx D i t g.1 : ℝ) + ∑ j, (D.WV t i j : ℝ) * g.2 j

private lemma rhs_sum {I : Instance} (D : IntDesc I) (μ : Mult I) (i : Fin D.mW) :
    D.aggLHS (I.typeAgg μ) i = ∑ t, (μ t).sum (fun g n => (n : ℝ) * rv D i t g) := by
  unfold IntDesc.aggLHS
  apply Finset.sum_congr rfl; intro t _
  simp only [Instance.typeAgg, aggr, count, Finsupp.sum, Prod.fst_sum, Prod.snd_sum,
    Finset.sum_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Gen.toReal,
    Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.univ) (t := (μ t).support),
    Finset.sum_comm (s := Finset.univ) (t := (μ t).support), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro g _
  simp only [rv,cx,Int.cast_add,Int.cast_sum,Int.cast_mul,mul_add,Finset.mul_sum,mul_left_comm]
  ring

private lemma lift_sum {I : Instance} {p : ℕ} (tOf : Fin p → Fin I.τ)
    (g : Fin p → Gen I.d I.k) (z : Fin p → ℕ)
    (μ : Mult I) (he : ∀ t, μ t = ∑ j ∈ Finset.univ.filter (fun j => tOf j = t), Finsupp.single (g j) (z j))
    (f : Fin I.τ → Gen I.d I.k → ℝ) :
    (∑ t, (μ t).sum (fun v n => (n : ℝ) * f t v)) = ∑ j, (z j : ℝ) * f (tOf j) (g j) := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ tOf (fun j => (z j : ℝ) * f (tOf j) (g j))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [he, ← Finsupp.sum_finsetSum_index (fun _ => by simp) (fun _ _ _ => by simp [add_mul])]
  apply Finset.sum_congr rfl; intro j hj
  rw [Finsupp.sum_single_index (by simp), (Finset.mem_filter.mp hj).2]

end IntConeFPT.Perspective
open IntConeFPT.Perspective

set_option maxHeartbeats 2400000 in
theorem solution (I : Instance) (hI : I.Valid) (M U : ℕ)
    (hbox : ∀ t, ∀ p ∈ I.P t, InBox M p) (hU : 1 ≤ U) (D : IntDesc I) (hD : D.Describes)
    (hDU : D.BoundedBy M U)
    (μ : Mult I) (hs : I.Supported μ)
    (hcard : ∑ t, (μ t).support.card ≤ I.τ * 2 ^ I.d)
    (hpos : 0 < I.totalCount μ)
    (rhs : Fin D.mW → ℤ) (hrhs : ∀ i, |rhs i| ≤ (U : ℤ))
    (hagg : ∀ i, D.aggLHS (fun t => I.typeAgg μ t) i ≤ rhs i) :
    let s := I.τ * 2 ^ I.d
    let H := (s * I.k + 1).factorial * U ^ (s * I.k + 1)
    ∃ (p m : ℕ) (A : Matrix (Fin m) (Fin p) ℤ) (b : Fin m → ℤ)
      (c : Fin p → ℝ) (z : Fin p → ℕ),
      1 ≤ p ∧ p ≤ s ∧ (∀ i j, |A i j| ≤ (H : ℤ)) ∧ (∀ i, |b i| ≤ (H : ℤ)) ∧
      (rhs = 0 → b = 0) ∧ (∀ i, ∑ j, A i j * (z j : ℤ) ≤ b i) ∧
      (∑ j, (z j : ℝ) * c j) = I.cost μ ∧
      ∀ y : Fin p → ℕ, (∀ i, ∑ j, A i j * (y j : ℤ) ≤ b i) →
        ∃ ν : Mult I, I.Supported ν ∧
          (∀ i, D.aggLHS (fun t => I.typeAgg ν t) i ≤ rhs i) ∧
          I.totalCount ν = ∑ j, y j ∧ I.cost ν = ∑ j, (y j : ℝ) * c j := by
  classical
  intro s H
  let G := Σ t, {g : Gen I.d I.k // g ∈ (μ t).support}
  let p := Fintype.card G
  let e : Fin p ≃ G := (Fintype.equivFin G).symm
  let T := fun j : Fin p => (e j).1
  let g := fun j : Fin p => (e j).2.val
  let z := fun j : Fin p => μ (T j) (g j)
  let x := fun j : Fin p => (g j).1
  let u := fun j : Fin p => (g j).2
  let c := fun j : Fin p => I.f (T j) (fun a => (x j a : ℝ))
  have src (f : Fin I.τ → Gen I.d I.k → ℝ) :
      (∑ j, (z j : ℝ) * f (T j) (g j)) = ∑ t, (μ t).sum (fun v n => (n : ℝ) * f t v) := by
    rw [e.sum_comp (fun a : G => ((μ a.1 a.2.val : ℕ) : ℝ) * f a.1 a.2.val), Fintype.sum_sigma]
    apply Finset.sum_congr rfl; intro t _
    unfold Finsupp.sum
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach (μ t).support (fun v => (μ t v : ℝ) * f t v)
  have hp : 1 ≤ p := by
    by_contra! hp
    have hzero : ∀ t, μ t = 0 := by
      intro t
      ext v
      by_contra h
      have hm : v ∈ (μ t).support := Finsupp.mem_support_iff.mpr h
      have hpos := (e.symm ⟨t,v,hm⟩).isLt
      omega
    simp [Instance.totalCount,count,hzero] at hpos
  have hps : p ≤ s := by simpa [p,G,s,Fintype.card_sigma] using hcard
  have gm j : g j ∈ I.S (T j) := hs _ (e j).2.property
  have xbox j a : |x j a| ≤ (M : ℤ) := by
    have hh : |((x j a : ℤ) : ℝ)| ≤ M := (hbox _ _ (gm j)).1 a
    exact_mod_cast hh
  let Row := Fin D.mW ⊕ (Σ j : Fin p, Fin (D.mL (T j)))
  let eR := (Fintype.equivFin Row).symm
  let eW : Fin p × Fin I.k ≃ Fin (p*I.k) := finProdFinEquiv
  let lc := fun j (i : Fin (D.mL (T j))) => (∑ a, D.LA (T j) i a * x j a) - D.Lb (T j) i
  let C : Matrix (Fin (Fintype.card Row)) (Fin p) ℤ := Matrix.of fun l j =>
    match eR l with
    | .inl i => cx D i (T j) (x j)
    | .inr ⟨j',i⟩ => if j = j' then lc j' i else 0
  let E : Matrix (Fin (Fintype.card Row)) (Fin (p*I.k)) ℤ := Matrix.of fun l q =>
    match eR l with
    | .inl i => D.WV (T (eW.symm q).1) i (eW.symm q).2
    | .inr ⟨j,i⟩ => if (eW.symm q).1 = j then D.LB (T j) i (eW.symm q).2 else 0
  let f := fun l => Sum.elim rhs (fun _ => (0 : ℤ)) (eR l)
  have hC l j : |C l j| ≤ (U : ℤ) := by
    simp only [C, Matrix.of_apply]
    cases h : eR l with
    | inl i => exact hDU.2.2.2.2.2.2.2.2 _ _ _ (xbox j)
    | inr ji =>
      obtain ⟨j',i⟩ := ji
      by_cases h : j=j'
      · simp only [if_pos h,lc,abs_sub_comm]
        exact hDU.2.2.2.2.2.2.2.1 _ _ _ (xbox j')
      · simp [h]
  have hE l q : |E l q| ≤ (U : ℤ) := by
    simp only [E, Matrix.of_apply]
    cases eR l with
    | inl i => exact hDU.2.1 .. 
    | inr ji =>
      obtain ⟨j,i⟩ := ji
      by_cases he : (eW.symm q).1 = j
      · simp only [if_pos he]; exact hDU.2.2.2.2.2.1 .. 
      · simp [he]
  have hf l : |f l| ≤ (U : ℤ) := by
    cases h : eR l <;> simp [f,h,hrhs]
  have hn : p*I.k+1 ≤ s*I.k+1 := Nat.add_le_add_right (Nat.mul_le_mul_right _ hps) _
  obtain ⟨m,A,b,hA,hb,hb0,hiff⟩ := farkas_project_bounded C E f U H hU
    (Nat.mul_le_mul (Nat.factorial_le hn) (Nat.pow_le_pow_right hU hn)) hC hE hf
  let sys := fun (v : Fin p → ℕ) (w : Fin (p*I.k) → ℝ) => ∀ l,
    ((C.map (Int.cast : ℤ → ℝ)) *ᵥ fun j => (v j : ℝ)) l +
    ((E.map (Int.cast : ℤ → ℝ)) *ᵥ w) l ≤ (f l : ℝ)
  have spec (v : Fin p → ℕ) (w : Fin (p*I.k) → ℝ) :
      sys v w ↔ (∀ i, ∑ j, ((cx D i (T j) (x j) : ℝ) * v j +
        ∑ a, (D.WV (T j) i a : ℝ) * w (eW (j,a))) ≤ rhs i) ∧
        ∀ j i, (lc j i : ℝ) * v j + ∑ a, (D.LB (T j) i a : ℝ) * w (eW (j,a)) ≤ 0 := by
    let expr := fun l => ((C.map (Int.cast : ℤ → ℝ)) *ᵥ fun j => (v j : ℝ)) l +
      ((E.map (Int.cast : ℤ → ℝ)) *ᵥ w) l
    have hrow (l : Row) : expr (eR.symm l) =
      match l with
      | .inl i => ∑ j, ((cx D i (T j) (x j) : ℝ) * v j + ∑ a, (D.WV (T j) i a : ℝ) * w (eW (j,a)))
      | .inr ⟨j,i⟩ => (lc j i : ℝ) * v j + ∑ a, (D.LB (T j) i a : ℝ) * w (eW (j,a)) := by
      simp only [expr, Matrix.mulVec,dotProduct, Matrix.map_apply,C,E,Matrix.of_apply,Equiv.apply_symm_apply]
      rw [← eW.sum_comp (fun q => _ * w q),Fintype.sum_prod_type]
      cases l with
      | inl i => simp [Finset.sum_add_distrib]
      | inr ji =>
        obtain ⟨j,i⟩ := ji
        simp [ite_mul, Finset.sum_ite_eq', Finset.sum_ite_irrel]
    constructor
    · intro h
      constructor
      · intro i; simpa [← hrow (.inl i),f] using (show expr _ ≤ _ from h (eR.symm (.inl i)))
      · intro j i; simpa [← hrow (.inr ⟨j,i⟩),f] using (show expr _ ≤ _ from h (eR.symm (.inr ⟨j,i⟩)))
    · rintro ⟨ha,hl⟩ l
      change expr l ≤ _
      obtain ⟨q,rfl⟩ := eR.symm.surjective l
      rw [hrow]; cases q with
      | inl i => simpa [f] using ha i
      | inr ji => obtain ⟨j,i⟩ := ji; simpa [f] using hl j i
  let w0 := fun q => (z (eW.symm q).1 : ℝ) * u (eW.symm q).1 (eW.symm q).2
  have hz : sys z w0 := by
    apply (spec ..).2
    constructor
    · intro i
      refine le_trans (le_of_eq ?_) (hagg i)
      rw [rhs_sum, ← src]
      apply Finset.sum_congr rfl; intro j _
      simp only [w0,Equiv.symm_apply_apply,rv,mul_add,Finset.mul_sum]
      apply congrArg₂ (· + ·) (mul_comm ..)
      apply Finset.sum_congr rfl; intro l _
      exact mul_left_comm .. 
    · intro j i
      have hh := (hD.2 _ _ |>.2 (gm j)) i
      change (∑ a, (D.LA (T j) i a : ℝ) * (x j a : ℝ)) + ∑ a, (D.LB (T j) i a : ℝ) * u j a ≤ _ at hh
      simp only [lc,Int.cast_sub,Int.cast_sum,Int.cast_mul,w0,Equiv.symm_apply_apply]
      have he : (∑ a, (D.LB (T j) i a : ℝ) * ((z j : ℝ) * u j a)) =
          z j * ∑ a, (D.LB (T j) i a : ℝ) * u j a := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; exact mul_left_comm ..
      rw [he]; nlinarith [mul_nonneg (Nat.cast_nonneg (z j) : (0:ℝ) ≤ z j) (sub_nonneg.mpr hh)]
  refine ⟨p,m,A,b,c,z,hp,hps,hA,hb,fun hh => funext (hb0 (by ext l; cases h : eR l <;> simp [f,h,hh])),?_,
    src (fun t v => I.f t (fun a => (v.1 a : ℝ))),?_⟩
  · intro i
    have h := (hiff _).1 ⟨w0,hz⟩ i
    simp only [Matrix.mulVec, dotProduct,Matrix.map_apply] at h
    exact_mod_cast h
  · intro y hy
    obtain ⟨w,hw⟩ := (hiff (fun j => (y j : ℝ))).2 (fun i => by
      simp only [Matrix.mulVec, dotProduct,Matrix.map_apply]; exact_mod_cast hy i)
    obtain ⟨hwA,hwL⟩ := (spec y w).1 hw
    let W := fun j a => w (eW (j,a))
    have wzero j (h0 : y j = 0) : W j = 0 := local_recession_zero_desc I M hbox D hD
      (T j) (x j) (u j) (gm j) (W j) (fun i => by simpa [h0,W] using hwL j i)
    let gg := fun j => (x j, fun a => W j a / y j)
    let ν : Mult I := fun t => ∑ j ∈ Finset.univ.filter (fun j => T j = t), Finsupp.single (gg j) (y j)
    have hgg j (hnz : y j ≠ 0) : gg j ∈ I.S (T j) := by
      apply (hD.2 _ _).1; intro i
      have hpos : (0:ℝ) < y j := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hnz)
      change (∑ a, (D.LA (T j) i a : ℝ) * (x j a : ℝ)) +
        (∑ a, (D.LB (T j) i a : ℝ) * (W j a / y j)) ≤ _
      simp_rw [← mul_div_assoc, ← Finset.sum_div]
      rw [← le_sub_iff_add_le',div_le_iff₀ hpos]
      have h := hwL j i
      simp only [lc,Int.cast_sub,Int.cast_sum,Int.cast_mul] at h
      dsimp [W]; linarith
    have yW j a : (y j : ℝ) * (gg j).2 a = W j a := by
      by_cases h : y j = 0
      · simp [gg,h,wzero j h]
      · simp [gg,field, Nat.cast_ne_zero.mpr h]
    have eval := lift_sum T gg y ν (fun _ => rfl)
    refine ⟨ν,?_,?_,?_,eval (fun t v => I.f t (fun a => (v.1 a : ℝ)))⟩
    · intro t v hv
      have h := Finsupp.support_finsetSum (Finset.mem_coe.mp hv)
      obtain ⟨j,hj,hm⟩ := Finset.mem_biUnion.mp h
      have he := Finset.mem_singleton.mp (Finsupp.support_single_subset hm)
      have hnz : y j ≠ 0 := by intro hh; simp [hh] at hm
      rw [he, ← (Finset.mem_filter.mp hj).2]
      exact hgg j hnz
    · intro i
      rw [rhs_sum,eval]
      refine le_trans (le_of_eq ?_) (hwA i)
      apply Finset.sum_congr rfl; intro j _
      simp only [rv,mul_add,Finset.mul_sum]
      congr 1
      · exact mul_comm .. 
      · apply Finset.sum_congr rfl; intro a _
        rw [mul_left_comm, yW]
    · have h := eval (fun _ _ => 1)
      apply Nat.cast_injective (R := ℝ)
      simpa [Instance.totalCount,count,Finsupp.sum] using h
