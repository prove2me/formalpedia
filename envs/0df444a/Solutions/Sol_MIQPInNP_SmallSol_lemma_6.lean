-- Prove2me | solution 1 for MIQPInNP.SmallSol.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:18:37.809658+00:00
-- url     : https://prove2.me/submissions/5b85d475-69cf-4f3e-90ac-fb3000b01374

import Mathlib
import Definitions.Def_MIQPInNP_SmallSol_Setting

open MIQPInNP.SmallSol

namespace M5Core

open Finset Matrix

noncomputable def rdot {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (x : Fin n → ℝ) : ℝ :=
  ∑ j, (A i j : ℝ) * x j

lemma rdot_add_smul {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (x v : Fin n → ℝ) (t : ℝ) :
    rdot A i (x + t • v) = rdot A i x + t * rdot A i v := by
  unfold rdot
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intro j _; ring

lemma rdot_sub {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (x y : Fin n → ℝ) :
    rdot A i (x - y) = rdot A i x - rdot A i y := by
  unfold rdot
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma rdot_smul {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (v : Fin n → ℝ) (t : ℝ) :
    rdot A i (t • v) = t * rdot A i v := by
  have := rdot_add_smul A i 0 v t
  simpa [rdot] using this

lemma mem_poly_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (x : Fin n → ℝ) :
    x ∈ polyhedron A b ↔ ∀ i, rdot A i x ≤ b i := Iff.rfl

theorem descent {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (a : Fin n → ℝ)
    (hH : ∀ d : Fin n → ℝ, (∃ i, rdot A i d ≠ 0) →
      ∃ s : ℝ, ∑ j, a j * (s * d j) ≤ 0 ∧ ∃ i, 0 < s * rdot A i d) :
    ∀ x ∈ polyhedron A b, ∃ x' ∈ polyhedron A b, ∑ j, a j * x' j ≤ ∑ j, a j * x j ∧
      ∀ d : Fin n → ℝ, (∀ i, rdot A i x' = b i → rdot A i d = 0) → ∀ i, rdot A i d = 0 := by
  classical
  intro x hx
  induction hk : (univ.filter fun i => rdot A i x < b i).card using Nat.strong_induction_on
    generalizing x with
  | _ k ih =>
  by_cases hend : ∀ d : Fin n → ℝ, (∀ i, rdot A i x = b i → rdot A i d = 0) → ∀ i, rdot A i d = 0
  · exact ⟨x, hx, le_rfl, hend⟩
  push Not at hend
  obtain ⟨d, hdT, i1, hi1⟩ := hend
  obtain ⟨s, hsa, i2, hi2⟩ := hH d ⟨i1, hi1⟩
  set v : Fin n → ℝ := s • d with hv
  have hvT : ∀ i, rdot A i x = b i → rdot A i v = 0 := by
    intro i hi; rw [hv, rdot_smul, hdT i hi, mul_zero]
  have hvi2 : 0 < rdot A i2 v := by rw [hv, rdot_smul]; exact hi2
  set bad := univ.filter (fun i => 0 < rdot A i v) with hbad
  have hne : bad.Nonempty := ⟨i2, by simp [bad, hvi2]⟩
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image bad (fun i => (b i - rdot A i x) / rdot A i v) hne
  have hvi0 : 0 < rdot A i0 v := by simpa [bad] using hi0
  set τ := (b i0 - rdot A i0 x) / rdot A i0 v with hτ
  have hxi0 : rdot A i0 x < b i0 := by
    rcases (hx i0).lt_or_eq with h | h
    · exact h
    · exact absurd (hvT i0 h) hvi0.ne'
  have hτpos : 0 < τ := div_pos (by linarith) hvi0
  set x1 := x + τ • v with hx1
  have hx1P : x1 ∈ polyhedron A b := by
    intro i
    show rdot A i x1 ≤ b i
    rw [hx1, rdot_add_smul]
    by_cases hc : 0 < rdot A i v
    · have := hmin i (by simp [bad, hc])
      rw [div_le_div_iff₀ hvi0 hc] at this
      have h2 : τ * rdot A i v ≤ b i - rdot A i x := by
        rw [hτ, div_mul_eq_mul_div, div_le_iff₀ hvi0]; linarith
      linarith
    · push Not at hc
      have h3 : rdot A i x ≤ b i := hx i
      nlinarith
  have hx1i0 : rdot A i0 x1 = b i0 := by
    rw [hx1, rdot_add_smul, hτ, div_mul_cancel₀ _ hvi0.ne']; ring
  have hsub : (univ.filter fun i => rdot A i x1 < b i) ⊂ (univ.filter fun i => rdot A i x < b i) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨i0, by simp [hxi0], by simp [hx1i0]⟩
    · intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro h
      rcases (hx i).lt_or_eq with h' | h'
      · exact h'
      · rw [hx1, rdot_add_smul, hvT i h', mul_zero, add_zero] at h
        exact absurd h' h.ne
  have hlt := Finset.card_lt_card hsub
  obtain ⟨x', hx'P, hx'a, hx'end⟩ := ih _ (hk ▸ hlt) x1 hx1P rfl
  refine ⟨x', hx'P, le_trans hx'a ?_, hx'end⟩
  have : ∑ j, a j * x1 j = ∑ j, a j * x j + τ * ∑ j, a j * (s * d j) := by
    simp only [hx1, hv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1; apply Finset.sum_congr rfl; intro j _; ring
  rw [this]
  nlinarith


def rs {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (i : Fin m) : ℕ :=
  ∑ j, bitSize (A i j) + bitSize (b i)

def alpha (n S : ℕ) : ℕ := n * n + n * (2 * S)

lemma den_le_two_pow (q : ℚ) : q.den ≤ 2 ^ bitSize q := by
  have h1 := Nat.lt_size_self q.den
  have h2 : 2 ^ Nat.size q.den ≤ 2 ^ bitSize q := Nat.pow_le_pow_right (by norm_num) (by unfold bitSize; omega)
  omega

lemma natAbs_num_le_two_pow (q : ℚ) : q.num.natAbs ≤ 2 ^ bitSize q := by
  have h1 := Nat.lt_size_self q.num.natAbs
  have h2 : 2 ^ Nat.size q.num.natAbs ≤ 2 ^ bitSize q :=
    Nat.pow_le_pow_right (by norm_num) (by unfold bitSize; omega)
  omega

lemma scale_int (q : ℚ) (C : ℕ) (h : q.den ∣ C) :
    ∃ z : ℤ, (C : ℚ) * q = z ∧ z.natAbs ≤ C * q.num.natAbs := by
  obtain ⟨t, rfl⟩ := h
  refine ⟨t * q.num, ?_, ?_⟩
  · push_cast
    have := Rat.mul_den_eq_num q
    rw [← this]; ring
  · rw [Int.natAbs_mul, Int.natAbs_natCast]
    rw [mul_assoc]
    exact Nat.le_mul_of_pos_left _ q.den_pos

theorem small_solve {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (T : Finset (Fin m))
    (x : Fin n → ℝ) (hx : ∀ i ∈ T, rdot A i x = b i) :
    ∃ y : Fin n → ℚ, (∀ i ∈ T, rdot A i (toReal y) = b i) ∧
      ∃ I : Finset (Fin m), I.card ≤ n ∧ ∃ D : ℤ, D ≠ 0 ∧ |D| ≤ 2 ^ alpha n (∑ i ∈ I, rs A b i) ∧
        ∀ j, ∃ P : ℤ, |P| ≤ 2 ^ alpha n (∑ i ∈ I, rs A b i) ∧ (y j : ℚ) = P / D := by
  classical
  let v : T → (Fin n → ℚ) := fun i => A i.1
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℚ v
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hk : Fintype.card κ ≤ n := by
    have := hli.fintype_card_le_finrank; simpa using this
  let R : Matrix κ (Fin n) ℚ := fun l j => A (a l).1 j
  have hRrow : LinearIndependent ℚ R.row := hli
  have hcols : Submodule.span ℚ (Set.range R.col) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_row,
      finrank_span_eq_card hRrow, Module.finrank_fintype_fun_eq_card]
  obtain ⟨κ', a', ha', hspan', hli'⟩ := exists_linearIndependent' ℚ R.col
  have : Finite κ' := Finite.of_injective a' ha'
  let : Fintype κ' := Fintype.ofFinite κ'
  have hcard' : Fintype.card κ' = Fintype.card κ := by
    have h1 := linearIndependent_iff_card_eq_finrank_span.mp hli'
    rw [h1, Set.finrank, hspan', hcols, finrank_top, Module.finrank_fintype_fun_eq_card]
  let eqv : κ ≃ κ' := Fintype.equivOfCardEq hcard'.symm
  let f : κ → Fin n := fun c => a' (eqv c)
  have hf : Function.Injective f := ha'.comp eqv.injective
  let M : Matrix κ κ ℚ := fun l c => A (a l).1 (f c)
  have hMcol : LinearIndependent ℚ M.col := by
    have : M.col = R.col ∘ a' ∘ eqv := by ext c l; rfl
    rw [this]; exact hli'.comp eqv eqv.injective
  have hdet : M.det ≠ 0 := by
    have := Matrix.linearIndependent_cols_iff_isUnit.mp hMcol
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at this; exact this
  let β : κ → ℚ := fun l => b (a l).1
  let z : κ → ℚ := (M.det)⁻¹ • M.cramer β
  have hMz : M *ᵥ z = β := by
    simp only [z, Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul, inv_mul_cancel₀ hdet, one_smul]
  let y : Fin n → ℚ := fun j => ∑ c, if f c = j then z c else 0
  have hy : ∀ (w : Fin n → ℚ), ∑ j, w j * y j = ∑ c, w (f c) * z c := by
    intro w
    simp only [y, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro c _
    rw [Finset.sum_ite_eq]
    simp
  have hrow : ∀ l : κ, ∑ j, A (a l).1 j * y j = b (a l).1 := by
    intro l
    rw [hy]
    have := congrFun hMz l
    simpa [Matrix.mulVec, dotProduct, M, β] using this
  have hall : ∀ i ∈ T, ∑ j, A i j * y j = b i := by
    intro i hiT
    have hmem : v ⟨i, hiT⟩ ∈ Submodule.span ℚ (Set.range (v ∘ a)) := by
      rw [hspan]; exact Submodule.subset_span ⟨_, rfl⟩
    obtain ⟨μ, hμ⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hmem
    have hAi : ∀ j, A i j = ∑ l, μ l * A (a l).1 j := by
      intro j; have := congrFun hμ j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, v] at this
      rw [← this]
    have e1 : ∑ j, A i j * y j = ∑ l, μ l * b (a l).1 := by
      simp_rw [hAi, Finset.sum_mul]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro l _
      rw [← hrow l, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    have e2 : (b i : ℝ) = ∑ l, (μ l : ℝ) * b (a l).1 := by
      rw [← hx i hiT]; unfold rdot
      simp_rw [hAi]; push_cast; simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro l _
      rw [← hx _ (a l).2]; unfold rdot; rw [Finset.mul_sum]; apply Finset.sum_congr rfl
      intro j _; ring
    rw [e1]; exact_mod_cast e2.symm
  refine ⟨y, ?_, ?_⟩
  · intro i hi
    unfold rdot toReal
    exact_mod_cast hall i hi
  -- bounds
  let S := ∑ l, rs A b (a l).1
  let I : Finset (Fin m) := univ.image (fun l => (a l).1)
  have hinj : Function.Injective (fun l => (a l).1) := Subtype.val_injective.comp ha
  have hIcard : I.card = Fintype.card κ := by
    rw [Finset.card_image_of_injective _ hinj]; rfl
  have hIS : ∑ i ∈ I, rs A b i = S := Finset.sum_image (fun _ _ _ _ h => hinj h)
  refine ⟨I, hIcard ▸ hk, ?_⟩
  rw [hIS]
  let C : ℕ := ∏ l, ((∏ j, (A (a l).1 j).den) * (b (a l).1).den)
  have hCpos : 0 < C := by
    apply Finset.prod_pos; intro l _
    apply Nat.mul_pos (Finset.prod_pos (fun j _ => (A (a l).1 j).den_pos)) (b (a l).1).den_pos
  have hCle : C ≤ 2 ^ S := by
    have : ∀ l, (∏ j, (A (a l).1 j).den) * (b (a l).1).den ≤ 2 ^ rs A b (a l).1 := by
      intro l
      unfold rs
      rw [pow_add, ← Finset.prod_pow_eq_pow_sum]
      exact Nat.mul_le_mul (Finset.prod_le_prod' (fun j _ => den_le_two_pow _)) (den_le_two_pow _)
    calc C ≤ ∏ l, 2 ^ rs A b (a l).1 := Finset.prod_le_prod' (fun l _ => this l)
      _ = 2 ^ S := Finset.prod_pow_eq_pow_sum _ _ _
  have hbitle : ∀ l, (∀ j, bitSize (A (a l).1 j) ≤ S) ∧ bitSize (b (a l).1) ≤ S := by
    intro l
    have h1 : rs A b (a l).1 ≤ S := Finset.single_le_sum (f := fun l => rs A b (a l).1)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
    refine ⟨fun j => ?_, ?_⟩
    · have : bitSize (A (a l).1 j) ≤ ∑ j, bitSize (A (a l).1 j) :=
        Finset.single_le_sum (f := fun j => bitSize (A (a l).1 j)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j)
      unfold rs at h1; omega
    · unfold rs at h1; omega
  have hent : ∀ q : ℚ, q.den ∣ C → bitSize q ≤ S → ∃ zq : ℤ, (C : ℚ) * q = zq ∧ |zq| ≤ 2 ^ (2 * S) := by
    intro q hd hb
    obtain ⟨zq, hzq, hzb⟩ := scale_int q C hd
    refine ⟨zq, hzq, ?_⟩
    have h2 : zq.natAbs ≤ 2 ^ (2 * S) := by
      calc zq.natAbs ≤ C * q.num.natAbs := hzb
        _ ≤ 2 ^ S * 2 ^ S := Nat.mul_le_mul hCle
            (le_trans (natAbs_num_le_two_pow q) (Nat.pow_le_pow_right (by norm_num) hb))
        _ = 2 ^ (2 * S) := by rw [← pow_add]; ring_nf
    rw [Int.abs_eq_natAbs]; exact_mod_cast h2
  have hdvdA : ∀ l j, (A (a l).1 j).den ∣ C := by
    intro l j
    exact dvd_trans (dvd_trans (Finset.dvd_prod_of_mem (fun j => (A (a l).1 j).den) (Finset.mem_univ j))
      (dvd_mul_right _ _))
      (Finset.dvd_prod_of_mem (fun l => (∏ j, (A (a l).1 j).den) * (b (a l).1).den) (Finset.mem_univ l))
  have hdvdb : ∀ l, (b (a l).1).den ∣ C := by
    intro l
    exact dvd_trans (dvd_mul_left _ _)
      (Finset.dvd_prod_of_mem (fun l => (∏ j, (A (a l).1 j).den) * (b (a l).1).den) (Finset.mem_univ l))
  have hMent : ∀ l c, ∃ zq : ℤ, (C : ℚ) * M l c = zq ∧ |zq| ≤ 2 ^ (2 * S) :=
    fun l c => hent _ (hdvdA l (f c)) ((hbitle l).1 (f c))
  have hβent : ∀ l, ∃ zq : ℤ, (C : ℚ) * β l = zq ∧ |zq| ≤ 2 ^ (2 * S) :=
    fun l => hent _ (hdvdb l) (hbitle l).2
  choose NM hNM1 hNM2 using hMent
  choose Nβ hNβ1 hNβ2 using hβent
  let N : Matrix κ κ ℤ := Matrix.of NM
  have hNcast : N.map (Int.cast : ℤ → ℚ) = (C : ℚ) • M := by
    ext l c; simp [N, hNM1]
  have hdetcast : ∀ N' : Matrix κ κ ℤ, ((N'.det : ℤ) : ℚ) = (N'.map (Int.cast : ℤ → ℚ)).det := by
    intro N'
    have := RingHom.map_det (Int.castRingHom ℚ) N'
    simpa [RingHom.mapMatrix_apply] using this
  have hNdet : (N.det : ℚ) = (C : ℚ) ^ Fintype.card κ * M.det := by
    rw [hdetcast, hNcast, Matrix.det_smul]
  have hCq : (C : ℚ) ≠ 0 := by exact_mod_cast hCpos.ne'
  have hD0 : N.det ≠ 0 := by
    intro h
    have : (N.det : ℚ) = 0 := by rw [h]; simp
    rw [hNdet] at this
    exact (mul_ne_zero (pow_ne_zero _ hCq) hdet) this
  have hbound : ∀ N' : Matrix κ κ ℤ, (∀ l c, |N' l c| ≤ 2 ^ (2 * S)) →
      |N'.det| ≤ 2 ^ alpha n S := by
    intro N' hN'
    have h1 := Matrix.det_le (abv := AbsoluteValue.abs) hN'
    simp only [AbsoluteValue.abs_apply, nsmul_eq_mul] at h1
    refine le_trans h1 ?_
    have hfac : ((Fintype.card κ).factorial : ℤ) ≤ 2 ^ (n * n) := by
      have : (Fintype.card κ).factorial ≤ 2 ^ (n * n) := by
        calc (Fintype.card κ).factorial ≤ n.factorial := Nat.factorial_le hk
          _ ≤ n ^ n := Nat.factorial_le_pow _
          _ ≤ (2 ^ n) ^ n := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
          _ = 2 ^ (n * n) := by rw [← pow_mul]
      exact_mod_cast this
    have hpow : ((2 : ℤ) ^ (2 * S)) ^ Fintype.card κ ≤ 2 ^ (n * (2 * S)) := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (by rw [mul_comm]; exact Nat.mul_le_mul_right _ hk)
    unfold alpha
    rw [pow_add]
    exact mul_le_mul hfac hpow (by positivity) (by positivity)
  refine ⟨N.det, hD0, hbound N (fun l c => hNM2 l c), ?_⟩
  intro j
  by_cases hj : ∃ c, f c = j
  · obtain ⟨c, rfl⟩ := hj
    let Nc : Matrix κ κ ℤ := N.updateCol c Nβ
    refine ⟨Nc.det, hbound Nc ?_, ?_⟩
    · intro l c'
      simp only [Nc, Matrix.updateCol_apply]
      split_ifs
      · exact hNβ2 l
      · exact hNM2 l c'
    · have hyc : y (f c) = z c := by
        simp only [y]
        rw [Finset.sum_eq_single c]
        · simp
        · intro c' _ hc'; simp [hf.ne hc']
        · simp
      rw [hyc]
      have hNccast : Nc.map (Int.cast : ℤ → ℚ) = (C : ℚ) • M.updateCol c β := by
        ext l c'
        simp only [Nc, Matrix.map_apply, Matrix.updateCol_apply, Matrix.smul_apply, smul_eq_mul]
        split_ifs
        · rw [hNβ1]
        · simp [N, hNM1]
      rw [hdetcast Nc, hNccast, Matrix.det_smul, hNdet]
      simp only [z, Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply]
      field_simp
  · refine ⟨0, by simp, ?_⟩
    push Not at hj
    simp only [y]
    rw [Finset.sum_eq_zero (fun c _ => by simp [hj c])]
    simp


theorem small_point {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (a : Fin n → ℝ)
    (hH : ∀ d : Fin n → ℝ, (∃ i, rdot A i d ≠ 0) →
      ∃ s : ℝ, ∑ j, a j * (s * d j) ≤ 0 ∧ ∃ i, 0 < s * rdot A i d)
    (hH' : ∀ d : Fin n → ℝ, (∀ i, rdot A i d = 0) → ∑ j, a j * d j = 0)
    (x : Fin n → ℝ) (hx : x ∈ polyhedron A b) :
    ∃ y : Fin n → ℚ, toReal y ∈ polyhedron A b ∧ ∑ j, a j * toReal y j ≤ ∑ j, a j * x j ∧
      ∃ I : Finset (Fin m), I.card ≤ n ∧ ∃ D : ℤ, D ≠ 0 ∧ |D| ≤ 2 ^ alpha n (∑ i ∈ I, rs A b i) ∧
        ∀ j, ∃ P : ℤ, |P| ≤ 2 ^ alpha n (∑ i ∈ I, rs A b i) ∧ (y j : ℚ) = P / D := by
  classical
  obtain ⟨x', hx'P, hx'a, hend⟩ := descent A b a hH x hx
  obtain ⟨y, hyT, I, hI, D, hD, hDb, hP⟩ :=
    small_solve A b (univ.filter fun i => rdot A i x' = b i) x' (by simp)
  have hd : ∀ i, rdot A i (toReal y - x') = 0 :=
    hend _ (fun i hi => by rw [rdot_sub, hyT i (by simp [hi]), hi]; ring)
  refine ⟨y, fun i => ?_, ?_, I, hI, D, hD, hDb, hP⟩
  · show rdot A i (toReal y) ≤ b i
    have h1 := hd i
    rw [rdot_sub] at h1
    have h2 : rdot A i x' ≤ b i := hx'P i
    linarith
  · have := hH' _ hd
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib] at this
    linarith

lemma bitSize_div_le (P D : ℤ) (hD : D ≠ 0) (α : ℕ) (hP : |P| ≤ 2 ^ α) (hDb : |D| ≤ 2 ^ α) :
    bitSize ((P : ℚ) / D) ≤ 2 * α + 3 := by
  rw [← Rat.divInt_eq_div]
  have hnum : (Rat.divInt P D).num.natAbs ≤ 2 ^ α := by
    by_cases hP0 : P = 0
    · subst hP0; simp
    · have h1 := Int.natAbs_le_of_dvd_ne_zero (Rat.num_dvd P hD) hP0
      have h2 : P.natAbs ≤ 2 ^ α := by
        have : ((P.natAbs : ℕ) : ℤ) ≤ 2 ^ α := by rw [Int.natCast_natAbs]; exact hP
        exact_mod_cast this
      omega
  have hden : (Rat.divInt P D).den ≤ 2 ^ α := by
    have h1 := Int.le_of_dvd (by rw [abs_pos]; exact hD) ((Rat.den_dvd P D).trans (self_dvd_abs D))
    have : ((Rat.divInt P D).den : ℤ) ≤ 2 ^ α := le_trans h1 hDb
    exact_mod_cast this
  have s1 : Nat.size (Rat.divInt P D).num.natAbs ≤ α + 1 := by
    have := Nat.one_le_two_pow (n := α); rw [Nat.size_le, pow_succ]; omega
  have s2 : Nat.size (Rat.divInt P D).den ≤ α + 1 := by
    have := Nat.one_le_two_pow (n := α); rw [Nat.size_le, pow_succ]; omega
  unfold bitSize; omega

lemma vecSize_le_of_rep {n : ℕ} (y : Fin n → ℚ) (α : ℕ) (D : ℤ) (hD : D ≠ 0) (hDb : |D| ≤ 2 ^ α)
    (hP : ∀ j, ∃ P : ℤ, |P| ≤ 2 ^ α ∧ (y j : ℚ) = P / D) :
    vecSize y ≤ n * (2 * α + 4) := by
  unfold vecSize
  have : ∀ j, bitSize (y j) ≤ 2 * α + 3 := by
    intro j; obtain ⟨P, hPb, hPe⟩ := hP j; rw [hPe]; exact bitSize_div_le P D hD α hPb hDb
  have h2 := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => this j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  nlinarith

end M5Core

namespace M5G

open Finset

lemma cone_mem_iff {n s : ℕ} (v : Fin s → Fin n → ℝ) (x : Fin n → ℝ) :
    x ∈ cone (Set.range v) ↔ ∃ c : Fin s → ℝ, (∀ i, 0 ≤ c i) ∧ ∑ i, c i • v i = x := by
  unfold cone
  rw [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun i => c i, fun i => (c i).2, ?_⟩
    rw [← hc]; simp [NNReal.smul_def]
  · rintro ⟨c, hc0, hc⟩
    refine ⟨fun i => ⟨c i, hc0 i⟩, ?_⟩
    rw [← hc]
    exact Finset.sum_congr rfl (fun i _ => NNReal.smul_def _ _)

lemma euclidNorm_eq {n : ℕ} (x : Fin n → ℝ) :
    euclidNorm x = ‖(WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm x‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold euclidNorm
  congr 1
  apply Finset.sum_congr rfl; intro i _
  simp [sq_abs]

lemma euclidNorm_sum_le {n s : ℕ} (c : Fin s → ℝ) (hc : ∀ i, 0 ≤ c i) (v : Fin s → Fin n → ℝ) :
    euclidNorm (∑ i, c i • v i) ≤ ∑ i, c i * euclidNorm (v i) := by
  rw [euclidNorm_eq, map_sum]
  refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
  apply Finset.sum_congr rfl; intro i _
  rw [map_smul, norm_smul, Real.norm_of_nonneg (hc i), euclidNorm_eq]

lemma abs_le_euclidNorm {n : ℕ} (x : Fin n → ℝ) (j : Fin n) : |x j| ≤ euclidNorm x := by
  unfold euclidNorm
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)

lemma clm_apply_eq {n : ℕ} (F : (Fin n → ℝ) →L[ℝ] ℝ) (x : Fin n → ℝ) :
    F x = ∑ j, x j * F (Pi.single j 1) := by
  conv_lhs => rw [pi_eq_sum_univ x]
  rw [map_sum]
  apply Finset.sum_congr rfl; intro j _
  rw [map_smul, smul_eq_mul]
  congr 2
  funext i; simp [Pi.single_apply, eq_comm]

theorem gordan {n s : ℕ} (r : Fin s → Fin n → ℚ)
    (hpt : IsPointedCone (cone (Set.range fun i => toReal (r i)))) :
    ∃ g : Fin n → ℝ, ∀ i, r i ≠ 0 → 1 ≤ ∑ j, g j * toReal (r i) j := by
  classical
  let ι := {i : Fin s // r i ≠ 0}
  by_cases hι : IsEmpty ι
  · refine ⟨0, fun i hi => (hι.false ⟨i, hi⟩).elim⟩
  rw [not_isEmpty_iff] at hι
  let L : (ι → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Fintype.linearCombination ℝ (fun i : ι => toReal (r i.1))
  let K := L '' stdSimplex ℝ ι
  have hKc : Convex ℝ K := (convex_stdSimplex ℝ ι).linear_image L
  have hKk : IsCompact K := (isCompact_stdSimplex ℝ ι).image L.continuous_of_finiteDimensional
  have hdisj : Disjoint K {0} := by
    rw [Set.disjoint_singleton_right]
    rintro ⟨w, ⟨hw0, hw1⟩, hw⟩
    rw [Fintype.linearCombination_apply] at hw
    obtain ⟨i0, hi0⟩ : ∃ i0, 0 < w i0 := by
      by_contra h
      push Not at h
      have : ∑ i, w i = 0 := Finset.sum_eq_zero (fun i _ => le_antisymm (h i) (hw0 i))
      linarith
    have hsplit := Finset.add_sum_erase Finset.univ (fun i => w i • toReal (r i.1)) (Finset.mem_univ i0)
    rw [hw] at hsplit
    set xx := w i0 • toReal (r i0.1)
    have hmem : ∀ (t : ℝ) (i : Fin s), 0 ≤ t → t • toReal (r i) ∈ cone (Set.range fun i => toReal (r i)) := by
      intro t i ht
      rw [cone_mem_iff]
      refine ⟨Pi.single i t, fun k => ?_, ?_⟩
      · by_cases hk : k = i
        · subst hk; simp [ht]
        · simp [Pi.single_apply, hk]
      · rw [Finset.sum_eq_single i]
        · simp
        · intro k _ hk; simp [Pi.single_apply, hk]
        · simp
    have h1 : xx ∈ cone (Set.range fun i => toReal (r i)) := hmem _ _ (hw0 i0)
    have h2 : -xx ∈ cone (Set.range fun i => toReal (r i)) := by
      have : -xx = ∑ i ∈ Finset.univ.erase i0, w i • toReal (r i.1) := by
        rw [neg_eq_iff_add_eq_zero]; exact hsplit
      rw [this]
      exact Submodule.sum_mem _ (fun i _ => hmem _ _ (hw0 i))
    have h3 := hpt xx h1 h2
    have h4 : toReal (r i0.1) = 0 := by
      have := smul_eq_zero.mp h3
      rcases this with h | h
      · exact absurd h hi0.ne'
      · exact h
    apply i0.2
    funext j
    have := congrFun h4 j
    simpa [toReal] using this
  obtain ⟨F, u, v, hFu, huv, hFv⟩ :=
    geometric_hahn_banach_compact_closed hKc hKk (convex_singleton 0) isClosed_singleton hdisj
  have hv0 : v < 0 := by simpa using hFv 0 rfl
  have hu0 : u < 0 := by linarith
  refine ⟨fun j => F (Pi.single j 1) / u, fun i hi => ?_⟩
  have hiK : toReal (r i) ∈ K := by
    refine ⟨Pi.single ⟨i, hi⟩ 1, single_mem_stdSimplex ℝ _, ?_⟩
    rw [Fintype.linearCombination_apply, Finset.sum_eq_single ⟨i, hi⟩]
    · simp
    · intro k _ hk; simp [Pi.single_apply, hk]
    · simp
  have h1 := hFu _ hiK
  have h2 : ∑ j, F (Pi.single j 1) / u * toReal (r i) j = F (toReal (r i)) / u := by
    rw [clm_apply_eq F (toReal (r i)), Finset.sum_div]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [h2, le_div_iff_of_neg hu0]
  linarith

end M5G

open M5Core M5G

lemma bitSize_neg (q : ℚ) : bitSize (-q) = bitSize q := by
  unfold bitSize; simp

theorem lemma6_core : ∃ g : Polynomial ℕ, ∀ (n s : ℕ) (r : Fin s → Fin n → ℚ) (hs : 0 < s),
      IsPointedCone (cone (Set.range fun i => toReal (r i))) →
      ∃ f : Fin n → ℚ,
        vecSize f ≤ g.eval (Finset.univ.sup fun i => vecSize (r i)) ∧
        (∀ x ∈ cone (Set.range fun i => toReal (r i)), euclidNorm x = 1 →
          1 / (Finset.univ.sup' ⟨⟨0, hs⟩, Finset.mem_univ _⟩
                fun i => euclidNorm (toReal (r i))) ≤ ∑ j, (f j : ℝ) * x j) ∧
        Bornology.IsBounded (cone (Set.range fun i => toReal (r i)) ∩ hyperplane f) := by
  refine ⟨Polynomial.X * (2 * Polynomial.X ^ 2 + 4 * Polynomial.X ^ 2 * (Polynomial.X + 3) + 4), ?_⟩
  intro n s r hs hpt
  classical
  obtain ⟨g0, hg0⟩ := gordan r hpt
  let A : Matrix (Fin s) (Fin n) ℚ := fun i j => - r i j
  let b : Fin s → ℚ := fun i => if r i = 0 then 0 else -1
  have hdotA : ∀ i (x : Fin n → ℝ), rdot A i x = -∑ j, x j * (r i j : ℝ) := by
    intro i x
    simp only [rdot, A]
    rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _; push_cast; ring
  have hg0P : g0 ∈ polyhedron A b := by
    intro i
    show rdot A i g0 ≤ b i
    rw [hdotA]
    by_cases hi : r i = 0
    · simp [b, hi]
    · have := hg0 i hi
      simp only [b, hi, if_false, toReal] at this ⊢
      push_cast; linarith
  have hH : ∀ d : Fin n → ℝ, (∃ i, rdot A i d ≠ 0) →
      ∃ s : ℝ, ∑ j, (0 : Fin n → ℝ) j * (s * d j) ≤ 0 ∧ ∃ i, 0 < s * rdot A i d := by
    rintro d ⟨i, hi⟩
    exact ⟨rdot A i d, by simp, i, mul_self_pos.mpr hi⟩
  obtain ⟨f, hfP, -, I, hI, D, hD, hDb, hP⟩ :=
    small_point A b 0 hH (fun d _ => by simp) g0 hg0P
  have hfr : ∀ i, r i ≠ 0 → 1 ≤ ∑ j, (f j : ℝ) * toReal (r i) j := by
    intro i hi
    have h1 : rdot A i (toReal f) ≤ b i := hfP i
    rw [hdotA] at h1
    simp only [b, hi, if_false] at h1
    have e : ∑ j, (f j : ℝ) * toReal (r i) j = ∑ j, toReal f j * (r i j : ℝ) := by
      apply Finset.sum_congr rfl; intro j _; unfold toReal; ring
    rw [e]; push_cast at h1; linarith
  set Mx := Finset.univ.sup' ⟨⟨0, hs⟩, Finset.mem_univ _⟩ fun i => euclidNorm (toReal (r i)) with hMx
  have hle : ∀ i, euclidNorm (toReal (r i)) ≤ Mx := fun i =>
    Finset.le_sup' (fun i => euclidNorm (toReal (r i))) (Finset.mem_univ i)
  have hMx0 : 0 ≤ Mx := le_trans (Real.sqrt_nonneg _) (hle ⟨0, hs⟩)
  have key : ∀ x ∈ cone (Set.range fun i => toReal (r i)), euclidNorm x ≤ Mx * ∑ j, (f j : ℝ) * x j := by
    intro x hx
    obtain ⟨c, hc0, rfl⟩ := (cone_mem_iff _ x).mp hx
    have e : ∑ j, (f j : ℝ) * (∑ i, c i • toReal (r i)) j = ∑ i, c i * ∑ j, (f j : ℝ) * toReal (r i) j := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _; ring
    rw [e, Finset.mul_sum]
    refine le_trans (euclidNorm_sum_le c hc0 _) (Finset.sum_le_sum fun i _ => ?_)
    by_cases hi : r i = 0
    · have h0 : toReal (r i) = 0 := by funext j; simp [toReal, hi]
      rw [h0]; simp [euclidNorm]
    · have h1 := hfr i hi
      have h2 := hle i
      have hc := hc0 i
      have h3 : c i * euclidNorm (toReal (r i)) ≤ c i * Mx := mul_le_mul_of_nonneg_left h2 hc
      have h4 : c i * Mx ≤ c i * Mx * ∑ j, (f j : ℝ) * toReal (r i) j :=
        le_mul_of_one_le_right (mul_nonneg hc hMx0) h1
      linarith
  refine ⟨f, ?_, ?_, ?_⟩
  · -- size
    set S := Finset.univ.sup fun i => vecSize (r i) with hS
    have hrS : ∀ i, vecSize (r i) ≤ S := fun i =>
      Finset.le_sup (f := fun i => vecSize (r i)) (Finset.mem_univ i)
    have hnS : n ≤ S := le_trans (by unfold vecSize; omega) (hrS ⟨0, hs⟩)
    have hrs : ∀ i, rs A b i ≤ S + 3 := by
      intro i
      have hb : bitSize (b i) ≤ 3 := by
        by_cases hi : r i = 0 <;> simp [b, hi, bitSize]
      have : rs A b i = ∑ j, bitSize (r i j) + bitSize (b i) := by
        simp only [rs, A, bitSize_neg]
      have h2 := hrS i
      unfold vecSize at h2
      omega
    have hsum : ∑ i ∈ I, rs A b i ≤ S * (S + 3) := by
      calc ∑ i ∈ I, rs A b i ≤ I.card * (S + 3) := by
            have := Finset.sum_le_card_nsmul I (rs A b) (S + 3) (fun i _ => hrs i)
            simpa using this
        _ ≤ S * (S + 3) := Nat.mul_le_mul_right _ (le_trans hI hnS)
    have hα : alpha n (∑ i ∈ I, rs A b i) ≤ S * S + S * (2 * (S * (S + 3))) := by
      unfold alpha
      have := Nat.mul_le_mul hnS hnS
      have := Nat.mul_le_mul hnS (Nat.mul_le_mul_left 2 hsum)
      omega
    have hv := vecSize_le_of_rep f _ D hD hDb hP
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    calc vecSize f ≤ n * (2 * alpha n (∑ i ∈ I, rs A b i) + 4) := hv
      _ ≤ S * (2 * (S * S + S * (2 * (S * (S + 3)))) + 4) := by
          apply Nat.mul_le_mul hnS; omega
      _ = S * (2 * S ^ 2 + 4 * S ^ 2 * (S + 3) + 4) := by ring
  · intro x hx hx1
    have h1 := key x hx
    rw [hx1] at h1
    have hMpos : 0 < Mx := by
      rcases hMx0.lt_or_eq with h | h
      · exact h
      · rw [← h] at h1; linarith
    rw [div_le_iff₀ hMpos]; linarith
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨Mx, fun x hx => ?_⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hMx0]
    intro j
    have h1 := key x hx.1
    have h2 : ∑ j, (f j : ℝ) * x j = 1 := hx.2
    rw [h2, mul_one] at h1
    rw [Real.norm_eq_abs]
    exact le_trans (abs_le_euclidNorm x j) h1

theorem solution :
    ∃ g : Polynomial ℕ, ∀ (n s : ℕ) (r : Fin s → Fin n → ℚ) (hs : 0 < s),
      IsPointedCone (cone (Set.range fun i => toReal (r i))) →
      ∃ f : Fin n → ℚ,
        vecSize f ≤ g.eval (Finset.univ.sup fun i => vecSize (r i)) ∧
        (∀ x ∈ cone (Set.range fun i => toReal (r i)), euclidNorm x = 1 →
          1 / (Finset.univ.sup' ⟨⟨0, hs⟩, Finset.mem_univ _⟩
                fun i => euclidNorm (toReal (r i))) ≤ ∑ j, (f j : ℝ) * x j) ∧
        Bornology.IsBounded (cone (Set.range fun i => toReal (r i)) ∩ hyperplane f) :=
  lemma6_core
