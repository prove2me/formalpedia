-- Prove2me | solution 1 for MIQPInNP.SmallSol.claim_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:50:37.291822+00:00
-- url     : https://prove2.me/submissions/ad81dbc8-29a2-46ca-b8fe-287190d048a4

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


open M5Core
namespace M5C1

open M5Core

lemma abs_le_two_pow_bitSize (q : ℚ) : |q| ≤ 2 ^ bitSize q := by
  have h0 : (q.num : ℚ) / q.den = q := Rat.num_div_den q
  have hd : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
  have h1 : |q| ≤ |(q.num : ℚ)| := by
    conv_lhs => rw [← h0]
    rw [abs_div, abs_of_pos (by positivity : (0:ℚ) < q.den)]
    exact div_le_self (abs_nonneg _) hd
  have h2 : |(q.num : ℚ)| = (q.num.natAbs : ℚ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have h3 : (q.num.natAbs : ℚ) ≤ 2 ^ bitSize q := by exact_mod_cast natAbs_num_le_two_pow q
  linarith

lemma vecSize_le_of_rep' {n : ℕ} (y : Fin n → ℚ) (α : ℕ)
    (hP : ∀ j, ∃ P D : ℤ, D ≠ 0 ∧ |P| ≤ 2 ^ α ∧ |D| ≤ 2 ^ α ∧ (y j : ℚ) = P / D) :
    vecSize y ≤ n * (2 * α + 4) := by
  unfold vecSize
  have : ∀ j, bitSize (y j) ≤ 2 * α + 3 := by
    intro j; obtain ⟨P, D, hD, hPb, hDb, hPe⟩ := hP j; rw [hPe]; exact bitSize_div_le P D hD α hPb hDb
  have h2 := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => this j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  nlinarith

lemma no_rec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (hb : Bornology.IsBounded (polyhedron A b))
    (p : Fin n → ℝ) (hp : p ∈ polyhedron A b) (d : Fin n → ℝ) (hd : ∀ l, rdot A l d ≤ 0) : d = 0 := by
  obtain ⟨R, hR⟩ := hb.exists_norm_le
  by_contra hne
  obtain ⟨u, hu⟩ : ∃ u, d u ≠ 0 := by
    by_contra h; push Not at h; exact hne (funext h)
  have hdu : 0 < |d u| := abs_pos.mpr hu
  have hR0 : 0 ≤ R := le_trans (norm_nonneg p) (hR p hp)
  set t := (R + |p u| + 1) / |d u| with ht_def
  have ht : 0 ≤ t := div_nonneg (by linarith [abs_nonneg (p u)]) hdu.le
  have hmem : p + t • d ∈ polyhedron A b := by
    intro l
    show rdot A l (p + t • d) ≤ b l
    rw [rdot_add_smul]
    have h1 : rdot A l p ≤ b l := hp l
    have h2 := hd l
    nlinarith
  have h1 := hR _ hmem
  have h2 : ‖(p + t • d) u‖ ≤ ‖p + t • d‖ := norm_le_pi_norm (p + t • d) u
  have h3 : (p + t • d) u = p u + t * d u := by simp
  rw [h3, Real.norm_eq_abs] at h2
  have h4 : t * |d u| = R + |p u| + 1 := div_mul_cancel₀ _ hdu.ne'
  have h5 : t * |d u| - |p u| ≤ |p u + t * d u| := by
    have := abs_sub_abs_le_abs_sub (t * d u) (-(p u))
    rw [abs_mul, abs_of_nonneg ht, abs_neg, sub_neg_eq_add, add_comm (t * d u)] at this
    exact this
  linarith

lemma intCone_nonneg {n : ℕ} (S : Set (Fin n → ℝ)) (a : Fin n → ℝ)
    (h : ∀ g ∈ S, 0 ≤ ∑ u, a u * g u) : ∀ w ∈ intCone S, 0 ≤ ∑ u, a u * w u := by
  intro w hw
  induction hw using AddSubmonoid.closure_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; exact add_nonneg hx hy

lemma bit_le_sum {ι : Type*} [Fintype ι] (f : ι → ℕ) (i : ι) : f i ≤ ∑ j, f j :=
  Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

lemma prod_den_le {ι : Type*} [Fintype ι] (q : ι → ℚ) : ∏ j, (q j).den ≤ 2 ^ ∑ j, bitSize (q j) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod' (fun j _ => den_le_two_pow _)


lemma sum_abs_bound {n : ℕ} (f : Fin n → ℚ) (B : ℚ) (hf : ∀ u, |f u| ≤ B) : |∑ u, f u| ≤ n * B := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have := Finset.sum_le_sum (fun u (_ : u ∈ Finset.univ) => hf u)
  simpa using this

lemma abound {n Z : ℕ} (h r : Fin n → ℚ) (hh : ∀ v, |h v| ≤ 2 ^ Z) (hr : ∀ v, |r v| ≤ 2 ^ Z) :
    |2 * ∑ v, h v * r v| ≤ 2 * n * (2 ^ Z * 2 ^ Z) := by
  rw [abs_mul, abs_two]
  have := sum_abs_bound (fun v => h v * r v) (2 ^ Z * 2 ^ Z) (fun v => by
    rw [abs_mul]; exact mul_le_mul (hh v) (hr v) (abs_nonneg _) (by positivity))
  linarith

lemma Qbound {n Z α : ℕ} (a y c' r' : Fin n → ℚ) (ha : ∀ u, |a u| ≤ 2 * n * (2 ^ Z * 2 ^ Z))
    (hy : ∀ u, |y u| ≤ 2 ^ α) (hc : ∀ u, |c' u| ≤ 2 ^ Z) (hr : ∀ u, |r' u| ≤ 2 ^ Z) :
    |∑ u, a u * y u + ∑ u, c' u * r' u| ≤ 2 ^ (2 * n + 2 * Z + α + 2) := by
  have hn2 : (n : ℚ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
  have h1 := sum_abs_bound (fun u => a u * y u) (2 * n * (2 ^ Z * 2 ^ Z) * 2 ^ α) (fun u => by
    rw [abs_mul]; exact mul_le_mul (ha u) (hy u) (abs_nonneg _) (by positivity))
  have h2 := sum_abs_bound (fun u => c' u * r' u) (2 ^ Z * 2 ^ Z) (fun u => by
    rw [abs_mul]; exact mul_le_mul (hc u) (hr u) (abs_nonneg _) (by positivity))
  have h3 := abs_add_le (∑ u, a u * y u) (∑ u, c' u * r' u)
  have e : (2 : ℚ) ^ (2 * n + 2 * Z + α + 2) = 4 * (2 ^ n * 2 ^ n) * (2 ^ Z * 2 ^ Z) * 2 ^ α := by
    ring
  rw [e]
  have hn0 : (0 : ℚ) ≤ n := by positivity
  have hnn : (n : ℚ) * n ≤ 2 ^ n * 2 ^ n := mul_le_mul hn2 hn2 hn0 (by positivity)
  have h1n : (1 : ℚ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have h1α : (1 : ℚ) ≤ 2 ^ α := one_le_pow₀ (by norm_num)
  have hn' : (n : ℚ) ≤ 2 ^ n * 2 ^ n := le_trans hn2 (le_mul_of_one_le_right (by positivity) h1n)
  set X : ℚ := 2 ^ Z * 2 ^ Z with hX
  have hX0 : 0 ≤ X := by positivity
  set W : ℚ := 2 ^ α
  set N2 : ℚ := 2 ^ n * 2 ^ n
  have k1 : (n : ℚ) * (2 * n * X * W) = 2 * (n * n) * (X * W) := by ring
  have k2 : (n : ℚ) * (n * n) * 0 = 0 := by ring
  have hXW : 0 ≤ X * W := by positivity
  have t1 : 2 * ((n : ℚ) * n) * (X * W) ≤ 2 * N2 * (X * W) := by nlinarith
  have t2 : (n : ℚ) * X ≤ N2 * X * W := by
    have : (n : ℚ) * X ≤ N2 * X := mul_le_mul_of_nonneg_right hn' hX0
    have : N2 * X ≤ N2 * X * W := le_mul_of_one_le_right (by positivity) h1α
    linarith
  rw [k1] at h1
  nlinarith

lemma delta_lb {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (ri rj : Fin n → ℚ) (Z : ℕ)
    (hH : ∏ u, ∏ v, (H u v).den ≤ 2 ^ Z) (hi : ∏ v, (ri v).den ≤ 2 ^ Z)
    (hj : ∏ u, (rj u).den ≤ 2 ^ Z)
    (hpos : 0 < -∑ u, (2 * ∑ v, H u v * ri v) * rj u) :
    1 ≤ ((2 : ℚ) ^ Z * 2 ^ Z * 2 ^ Z) * (-∑ u, (2 * ∑ v, H u v * ri v) * rj u) := by
  classical
  set δ := -∑ u, (2 * ∑ v, H u v * ri v) * rj u with hδ
  let CH : ℕ := ∏ u, ∏ v, (H u v).den
  let Ci : ℕ := ∏ v, (ri v).den
  let Cj : ℕ := ∏ u, (rj u).den
  have hzH : ∀ u v, ∃ z : ℤ, (CH : ℚ) * H u v = z := fun u v =>
    (scale_int _ CH (dvd_trans (Finset.dvd_prod_of_mem (fun v => (H u v).den) (Finset.mem_univ v))
      (Finset.dvd_prod_of_mem (fun u => ∏ v, (H u v).den) (Finset.mem_univ u)))).imp fun _ h => h.1
  have hzi : ∀ v, ∃ z : ℤ, (Ci : ℚ) * ri v = z := fun v =>
    (scale_int _ Ci (Finset.dvd_prod_of_mem (fun v => (ri v).den) (Finset.mem_univ v))).imp
      fun _ h => h.1
  have hzj : ∀ u, ∃ z : ℤ, (Cj : ℚ) * rj u = z := fun u =>
    (scale_int _ Cj (Finset.dvd_prod_of_mem (fun u => (rj u).den) (Finset.mem_univ u))).imp
      fun _ h => h.1
  choose zH hzH using hzH
  choose zi hzi using hzi
  choose zj hzj using hzj
  have hδ2 : δ = ∑ u, ∑ v, (-2) * H u v * ri v * rj u := by
    rw [hδ, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro u _
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro v _
    ring
  have hδeq : ((CH : ℚ) * Ci * Cj) * δ = ((∑ u, ∑ v, (-2) * zH u v * zi v * zj u : ℤ) : ℚ) := by
    rw [hδ2, Finset.mul_sum]
    push_cast
    apply Finset.sum_congr rfl; intro u _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro v _
    rw [← hzH, ← hzi, ← hzj]
    ring
  have hC0 : (0 : ℚ) < (CH : ℚ) * Ci * Cj := by
    have h1 : 0 < CH := Finset.prod_pos (fun u _ => Finset.prod_pos (fun v _ => (H u v).den_pos))
    have h2 : 0 < Ci := Finset.prod_pos (fun v _ => (ri v).den_pos)
    have h3 : 0 < Cj := Finset.prod_pos (fun u _ => (rj u).den_pos)
    positivity
  have hCδ : (1 : ℚ) ≤ ((CH : ℚ) * Ci * Cj) * δ := by
    have hp : (0 : ℚ) < ((CH : ℚ) * Ci * Cj) * δ := mul_pos hC0 hpos
    rw [hδeq] at hp ⊢
    have : (0 : ℤ) < ∑ u, ∑ v, (-2) * zH u v * zi v * zj u := by exact_mod_cast hp
    exact_mod_cast this
  have hCle : ((CH : ℚ) * Ci * Cj) ≤ 2 ^ Z * 2 ^ Z * 2 ^ Z := by
    have h1 : (CH : ℚ) ≤ 2 ^ Z := by exact_mod_cast hH
    have h2 : (Ci : ℚ) ≤ 2 ^ Z := by exact_mod_cast hi
    have h3 : (Cj : ℚ) ≤ 2 ^ Z := by exact_mod_cast hj
    have : (CH : ℚ) * Ci ≤ 2 ^ Z * 2 ^ Z := mul_le_mul h1 h2 (by positivity) (by positivity)
    exact mul_le_mul this h3 (by positivity) (by positivity)
  have := mul_le_mul_of_nonneg_right hCle hpos.le
  linarith

lemma choose_K (Q δ : ℚ) (u0 Z : ℕ) (hQ : |Q| ≤ 2 ^ u0) (hδ : 0 < δ)
    (h1 : 1 ≤ ((2 : ℚ) ^ Z * 2 ^ Z * 2 ^ Z) * δ) : Q < 2 ^ (u0 + 3 * Z + 1) * δ := by
  have e : (2 : ℚ) ^ (u0 + 3 * Z + 1) = 2 ^ (u0 + 1) * (2 ^ Z * 2 ^ Z * 2 ^ Z) := by ring
  rw [e]
  have h3 : (2 : ℚ) ^ (u0 + 1) ≤ 2 ^ (u0 + 1) * ((2 ^ Z * 2 ^ Z * 2 ^ Z) * δ) :=
    le_mul_of_one_le_right (by positivity) h1
  have h4 : (2 : ℚ) ^ u0 < 2 ^ (u0 + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  have h5 := le_abs_self Q
  have e2 : (2 : ℚ) ^ (u0 + 1) * ((2 ^ Z * 2 ^ Z * 2 ^ Z) * δ) =
      2 ^ (u0 + 1) * (2 ^ Z * 2 ^ Z * 2 ^ Z) * δ := by ring
  linarith

lemma xt_rep (α Z K : ℕ) (P D : ℤ) (hD : D ≠ 0) (hPb : |P| ≤ 2 ^ α) (hDb : |D| ≤ 2 ^ α)
    (q : ℚ) (hq : bitSize q ≤ Z) :
    ∃ P' D' : ℤ, D' ≠ 0 ∧ |P'| ≤ 2 ^ (α + Z + K + 1) ∧ |D'| ≤ 2 ^ (α + Z + K + 1) ∧
      ((P : ℚ) / D + 2 ^ K * q) = P' / D' := by
  have hqden : ((q.den : ℤ)) ≤ 2 ^ Z := by
    have := le_trans (den_le_two_pow q) (Nat.pow_le_pow_right (by norm_num) hq)
    exact_mod_cast this
  have hqnum : |q.num| ≤ 2 ^ Z := by
    have := le_trans (natAbs_num_le_two_pow q) (Nat.pow_le_pow_right (by norm_num) hq)
    rw [Int.abs_eq_natAbs]; exact_mod_cast this
  have hqd0 : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
  have hden0 : (0 : ℤ) ≤ q.den := by positivity
  have hK1 : (1 : ℤ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
  refine ⟨P * q.den + 2 ^ K * q.num * D, D * q.den, mul_ne_zero hD hqd0, ?_, ?_, ?_⟩
  · have hA : |P * q.den + 2 ^ K * q.num * D| ≤ |P| * q.den + 2 ^ K * (|q.num| * |D|) := by
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hden0,
        abs_of_pos (by positivity : (0:ℤ) < 2 ^ K)]
      rw [mul_assoc]
    have h1 : |P| * (q.den : ℤ) ≤ 2 ^ α * 2 ^ Z := mul_le_mul hPb hqden hden0 (by positivity)
    have h2 : |q.num| * |D| ≤ 2 ^ Z * 2 ^ α := mul_le_mul hqnum hDb (abs_nonneg _) (by positivity)
    have h3 : 2 ^ K * (|q.num| * |D|) ≤ 2 ^ K * (2 ^ Z * 2 ^ α) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : (2 : ℤ) ^ α * 2 ^ Z ≤ 2 ^ K * (2 ^ Z * 2 ^ α) := by
      have : (2 : ℤ) ^ α * 2 ^ Z = 1 * (2 ^ Z * 2 ^ α) := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right hK1 (by positivity)
    have e : (2 : ℤ) ^ (α + Z + K + 1) = 2 * (2 ^ K * (2 ^ Z * 2 ^ α)) := by ring
    rw [e]; linarith
  · rw [abs_mul, abs_of_nonneg hden0]
    calc |D| * (q.den : ℤ) ≤ 2 ^ α * 2 ^ Z := mul_le_mul hDb hqden hden0 (by positivity)
      _ = 2 ^ (α + Z) := by ring
      _ ≤ 2 ^ (α + Z + K + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  · have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD
    have hq' : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
    conv_lhs => rw [← Rat.num_div_den q]
    push_cast
    field_simp

end M5C1


open M5Core M5C1
namespace M5C2

open Finset

noncomputable def phi {k : ℕ} (Gs : Matrix (Fin k) (Fin k) ℚ) (x : Fin k → ℝ) : ℝ :=
  ∑ u, ∑ v, x u * (Gs u v : ℝ) * x v

lemma phi_eq {k : ℕ} (Gs : Matrix (Fin k) (Fin k) ℚ) (x : Fin k → ℝ) :
    phi Gs x = ∑ u, x u * ∑ v, (Gs u v : ℝ) * x v := by
  unfold phi; apply Finset.sum_congr rfl; intro u _; rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro v _; ring

lemma phi_dir {k : ℕ} (Gs : Matrix (Fin k) (Fin k) ℚ) (hsym : ∀ u v, Gs u v = Gs v u)
    (x d : Fin k → ℝ) (t : ℝ) :
    phi Gs (x + t • d) = phi Gs x + 2 * t * ∑ u, d u * ∑ v, (Gs u v : ℝ) * x v + t ^ 2 * phi Gs d := by
  have e1 : phi Gs (x + t • d) = phi Gs x + t * ∑ u, ∑ v, x u * (Gs u v : ℝ) * d v
      + t * ∑ u, ∑ v, d u * (Gs u v : ℝ) * x v + t ^ 2 * phi Gs d := by
    unfold phi
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl; intro v _; ring
  have e2 : ∑ u, ∑ v, x u * (Gs u v : ℝ) * d v = ∑ u, d u * ∑ v, (Gs u v : ℝ) * x v := by
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro v _; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro u _; rw [hsym u v]; ring
  have e3 : ∑ u, ∑ v, d u * (Gs u v : ℝ) * x v = ∑ u, d u * ∑ v, (Gs u v : ℝ) * x v := by
    apply Finset.sum_congr rfl; intro u _; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro v _; ring
  rw [e1, e2, e3]; ring

lemma min_quad (g c m : ℝ) (hm : 0 < m) (h : ∀ t, |t| ≤ m → 0 ≤ 2 * t * g + t ^ 2 * c) : g = 0 := by
  by_contra hg
  have hg' : 0 < |g| := abs_pos.mpr hg
  set ε := min m (|g| / (|c| + 1)) with hε
  have hε0 : 0 < ε := lt_min hm (div_pos hg' (by positivity))
  have hεm : ε ≤ m := min_le_left _ _
  have hεg : ε ≤ |g| / (|c| + 1) := min_le_right _ _
  have h1 := h ε (by rw [abs_of_pos hε0]; exact hεm)
  have h2 := h (-ε) (by rw [abs_neg, abs_of_pos hε0]; exact hεm)
  have h3 : 2 * |g| ≤ ε * |c| := by
    rcases le_or_gt 0 g with hg0 | hg0
    · rw [abs_of_nonneg hg0]
      have : 2 * ε * g ≤ ε ^ 2 * c := by nlinarith
      have : 2 * g ≤ ε * c := by nlinarith
      nlinarith [le_abs_self c]
    · rw [abs_of_neg hg0]
      have : -(2 * ε * g) ≤ ε ^ 2 * c := by nlinarith
      have : -(2 * g) ≤ ε * c := by nlinarith
      nlinarith [le_abs_self c]
  have h4 : ε * (|c| + 1) ≤ |g| := by rwa [le_div_iff₀ (by positivity)] at hεg
  nlinarith [abs_nonneg c]

/-- KKT conditions for a minimizer of `phi` over the face of the simplex supported on `R`. -/
lemma kkt {k : ℕ} (Gs : Matrix (Fin k) (Fin k) ℚ) (hsym : ∀ u v, Gs u v = Gs v u)
    (R : Finset (Fin k)) (ls : Fin k → ℝ) (hls0 : ∀ j, 0 ≤ ls j) (hlsR : ∀ j, j ∉ R → ls j = 0)
    (hls1 : ∑ j, ls j = 1)
    (hmin : ∀ l : Fin k → ℝ, (∀ j, 0 ≤ l j) → (∀ j, j ∉ R → l j = 0) → ∑ j, l j = 1 →
      phi Gs ls ≤ phi Gs l) :
    ∀ u, 0 < ls u → ∑ v, (Gs u v : ℝ) * ls v = phi Gs ls := by
  classical
  set κ : Fin k → ℝ := fun u => ∑ v, (Gs u v : ℝ) * ls v with hκ
  have hpair : ∀ u w, 0 < ls u → 0 < ls w → κ u = κ w := by
    intro u w hu hw
    by_cases huw : u = w
    · rw [huw]
    let d : Fin k → ℝ := Pi.single u 1 - Pi.single w 1
    have hdsum : ∀ f : Fin k → ℝ, ∑ j, d j * f j = f u - f w := by
      intro f
      simp only [d, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      simp [Pi.single_apply]
    set m := min (ls u) (ls w)
    have hm : 0 < m := lt_min hu hw
    apply sub_eq_zero.mp
    apply min_quad _ (phi Gs d) m hm
    intro t ht
    have hmem0 : ∀ j, 0 ≤ (ls + t • d) j := by
      intro j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, d, Pi.sub_apply]
      have htm := abs_le.mp ht
      by_cases hju : j = u
      · subst hju
        simp [Pi.single_apply, huw]
        have : m ≤ ls j := min_le_left _ _
        linarith
      · by_cases hjw : j = w
        · subst hjw
          simp [Pi.single_apply, hju]
          have : m ≤ ls j := min_le_right _ _
          linarith
        · simp [Pi.single_apply, hju, hjw, hls0 j]
    have hmemR : ∀ j, j ∉ R → (ls + t • d) j = 0 := by
      intro j hj
      have hju : j ≠ u := by rintro rfl; have := hlsR j hj; linarith
      have hjw : j ≠ w := by rintro rfl; have := hlsR j hj; linarith
      simp [d, Pi.single_apply, hju, hjw, hlsR j hj]
    have hmem1 : ∑ j, (ls + t • d) j = 1 := by
      have : ∑ j, (ls + t • d) j = ∑ j, ls j + t * ∑ j, d j * 1 := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum,
          mul_one]
      rw [this, hdsum, hls1]; ring
    have h1 := hmin _ hmem0 hmemR hmem1
    rw [phi_dir Gs hsym, hdsum] at h1
    linarith
  intro u hu
  rw [phi_eq]
  have : ∀ w, ls w * κ w = ls w * κ u := by
    intro w
    rcases (hls0 w).lt_or_eq with hw | hw
    · rw [hpair w u hw hu]
    · rw [← hw]; ring
  change κ u = ∑ w, ls w * κ w
  rw [Finset.sum_congr rfl (fun w _ => this w), ← Finset.sum_mul, hls1, one_mul]

end M5C2

namespace M5C2

open Finset

def EG (k B : ℕ) : ℕ := (k + 1) * (k + 1) + (k + 1) * (2 * ((k + 1) * ((k + 1) * (B + 3) + 3)))

lemma bitSize_small (q : ℚ) (hq : q = 0 ∨ q = 1 ∨ q = -1) : bitSize q ≤ 3 := by
  rcases hq with rfl | rfl | rfl <;> simp [bitSize]

lemma mu_lower {k : ℕ} (Gs : Matrix (Fin k) (Fin k) ℚ) (hsym : ∀ u v, Gs u v = Gs v u)
    (B : ℕ) (hB : ∀ u v, bitSize (Gs u v) ≤ B)
    (R : Finset (Fin k)) (ls : Fin k → ℝ) (hls0 : ∀ j, 0 ≤ ls j) (hlsR : ∀ j, j ∉ R → ls j = 0)
    (hls1 : ∑ j, ls j = 1)
    (hmin : ∀ l : Fin k → ℝ, (∀ j, 0 ≤ l j) → (∀ j, j ∉ R → l j = 0) → ∑ j, l j = 1 →
      phi Gs ls ≤ phi Gs l)
    (hpos : 0 < phi Gs ls) : (1 : ℝ) ≤ 2 ^ EG k B * phi Gs ls := by
  classical
  have hk := kkt Gs hsym R ls hls0 hlsR hls1 hmin
  set μs := phi Gs ls with hμs
  let F : Finset (Fin k) := univ.filter (fun u => 0 < ls u)
  have hF : ∀ u, u ∈ F ↔ 0 < ls u := by intro u; simp [F]
  have hnF : ∀ u, u ∉ F → ls u = 0 := by
    intro u hu; rw [hF] at hu; push Not at hu; exact le_antisymm hu (hls0 u)
  let A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ := fun i j =>
    Fin.lastCases (motive := fun _ => ℚ) (Fin.lastCases (motive := fun _ => ℚ) 0 (fun _ => 1) j)
      (fun u => Fin.lastCases (motive := fun _ => ℚ) (if u ∈ F then -1 else 0)
        (fun v => if u ∈ F then Gs u v else if u = v then 1 else 0) j) i
  let b : Fin (k + 1) → ℚ := fun i => Fin.lastCases (motive := fun _ => ℚ) 1 (fun _ => 0) i
  let zs : Fin (k + 1) → ℝ := fun j => Fin.lastCases (motive := fun _ => ℝ) μs (fun v => ls v) j
  have hrowA : ∀ (u : Fin k) (z : Fin (k + 1) → ℚ),
      ∑ j, A (Fin.castSucc u) j * z j =
        (if u ∈ F then ∑ v, Gs u v * z (Fin.castSucc v) - z (Fin.last k) else z (Fin.castSucc u)) := by
    intro u z
    rw [Fin.sum_univ_castSucc]
    simp only [A, Fin.lastCases_castSucc, Fin.lastCases_last]
    split_ifs with hu
    · simp [sub_eq_add_neg]
    · simp
  have hrowL : ∀ (z : Fin (k + 1) → ℚ), ∑ j, A (Fin.last k) j * z j = ∑ v, z (Fin.castSucc v) := by
    intro z
    rw [Fin.sum_univ_castSucc]
    simp [A]
  have hzs : ∀ i ∈ (univ : Finset (Fin (k + 1))), rdot A i zs = b i := by
    intro i _
    unfold rdot
    rw [Fin.sum_univ_castSucc]
    induction i using Fin.lastCases with
    | last =>
      simp [A, b, zs, hls1]
    | cast u =>
      simp only [A, b, zs, Fin.lastCases_castSucc, Fin.lastCases_last]
      by_cases hu : u ∈ F
      · simp only [hu, if_true]
        push_cast
        have := hk u ((hF u).mp hu)
        rw [this]; ring
      · simp only [hu, if_false]
        rw [Finset.sum_eq_single u]
        · simp [hnF u hu]
        · intro v _ hv; simp [Ne.symm hv]
        · simp
  obtain ⟨z', hz', I, hI, D, hD, hDb, hP⟩ := small_solve A b univ zs hzs
  have hz'q : ∀ i, ∑ j, A i j * z' j = b i := by
    intro i
    have h1 := hz' i (mem_univ i)
    have h2 : rdot A i (toReal z') = ((∑ j, A i j * z' j : ℚ) : ℝ) := by
      unfold rdot toReal; push_cast; rfl
    rw [h2] at h1; exact_mod_cast h1
  set lp : Fin k → ℚ := fun v => z' (Fin.castSucc v)
  set μp : ℚ := z' (Fin.last k)
  have hF1 : ∀ u ∈ F, ∑ v, Gs u v * lp v = μp := by
    intro u hu
    have := hz'q (Fin.castSucc u)
    rw [hrowA] at this
    simp only [hu, if_true, b, Fin.lastCases_castSucc] at this
    linarith
  have hF0 : ∀ u, u ∉ F → lp u = 0 := by
    intro u hu
    have := hz'q (Fin.castSucc u)
    rw [hrowA] at this
    simpa [hu, b] using this
  have hF2 : ∑ v, lp v = 1 := by
    have := hz'q (Fin.last k)
    rw [hrowL] at this
    simpa [b] using this
  -- μp = μs
  have hS1 : ∑ u, ∑ v, ls u * (Gs u v : ℝ) * (lp v : ℝ) = μp := by
    have : ∀ u, ∑ v, ls u * (Gs u v : ℝ) * (lp v : ℝ) = ls u * μp := by
      intro u
      by_cases hu : u ∈ F
      · rw [← hF1 u hu]; push_cast; rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro v _; ring
      · simp [hnF u hu]
    rw [Finset.sum_congr rfl (fun u _ => this u), ← Finset.sum_mul, hls1, one_mul]
  have hS2 : ∑ u, ∑ v, ls u * (Gs u v : ℝ) * (lp v : ℝ) = μs := by
    rw [Finset.sum_comm]
    have : ∀ v, ∑ u, ls u * (Gs u v : ℝ) * (lp v : ℝ) = (lp v : ℝ) * μs := by
      intro v
      by_cases hv : v ∈ F
      · rw [← hk v ((hF v).mp hv), Finset.mul_sum]
        apply Finset.sum_congr rfl; intro u _; rw [hsym u v]; ring
      · simp [hF0 v hv]
    rw [Finset.sum_congr rfl (fun v _ => this v), ← Finset.sum_mul]
    have : ∑ v, (lp v : ℝ) = 1 := by exact_mod_cast hF2
    rw [this, one_mul]
  have hμeq : (μp : ℝ) = μs := by rw [← hS1, hS2]
  -- size bound
  have hent : ∀ i j, bitSize (A i j) ≤ B + 3 := by
    intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp only [A, Fin.lastCases_last]; have := bitSize_small 0 (by simp); omega
      | cast v => simp only [A, Fin.lastCases_last, Fin.lastCases_castSucc]; have := bitSize_small 1 (by simp); omega
    | cast u =>
      induction j using Fin.lastCases with
      | last =>
        simp only [A, Fin.lastCases_last, Fin.lastCases_castSucc]
        split_ifs
        · have := bitSize_small (-1) (by simp); omega
        · have := bitSize_small 0 (by simp); omega
      | cast v =>
        simp only [A, Fin.lastCases_castSucc]
        split_ifs
        · have := hB u v; omega
        · have := bitSize_small 1 (by simp); omega
        · have := bitSize_small 0 (by simp); omega
  have hrs : ∀ i, rs A b i ≤ (k + 1) * (B + 3) + 3 := by
    intro i
    unfold rs
    have h1 : ∑ j, bitSize (A i j) ≤ ∑ _j : Fin (k + 1), (B + 3) := Finset.sum_le_sum (fun j _ => hent i j)
    have h2 : bitSize (b i) ≤ 3 := by
      induction i using Fin.lastCases with
      | last => simp only [b, Fin.lastCases_last]; exact bitSize_small 1 (by simp)
      | cast u => simp only [b, Fin.lastCases_castSucc]; exact bitSize_small 0 (by simp)
    simp at h1
    omega
  have hsum : ∑ i ∈ I, rs A b i ≤ (k + 1) * ((k + 1) * (B + 3) + 3) := by
    calc ∑ i ∈ I, rs A b i ≤ I.card * ((k + 1) * (B + 3) + 3) := by
          have := Finset.sum_le_card_nsmul I (rs A b) _ (fun i _ => hrs i)
          simpa using this
      _ ≤ (k + 1) * ((k + 1) * (B + 3) + 3) := Nat.mul_le_mul_right _ hI
  have hαle : alpha (k + 1) (∑ i ∈ I, rs A b i) ≤ EG k B := by
    unfold alpha EG
    have := Nat.mul_le_mul_left (k + 1) (Nat.mul_le_mul_left 2 hsum)
    omega
  -- conclude
  obtain ⟨P, hPb, hPe⟩ := hP (Fin.last k)
  have hμp : (μp : ℝ) = (P : ℝ) / D := by
    have : μp = (P : ℚ) / D := hPe
    rw [this]; push_cast; rfl
  have hμpos : (0 : ℝ) < (P : ℝ) / D := by rw [← hμp, hμeq]; exact hpos
  have hP0 : P ≠ 0 := by rintro rfl; simp at hμpos
  have hPabs : (1 : ℝ) ≤ |(P : ℝ)| := by
    have : (1 : ℤ) ≤ |P| := Int.one_le_abs hP0
    exact_mod_cast this
  have hDabs : |(D : ℝ)| ≤ 2 ^ EG k B := by
    have h1 : |D| ≤ 2 ^ EG k B := le_trans hDb (pow_le_pow_right₀ (by norm_num) hαle)
    have : ((|D| : ℤ) : ℝ) ≤ ((2 ^ EG k B : ℤ) : ℝ) := by exact_mod_cast h1
    simpa using this
  have hD0 : (0 : ℝ) < |(D : ℝ)| := abs_pos.mpr (by exact_mod_cast hD)
  have hμabs : (P : ℝ) / D = |(P : ℝ)| / |(D : ℝ)| := by
    rw [← abs_div, abs_of_pos hμpos]
  rw [← hμeq, hμp, hμabs]
  rw [mul_div_assoc', le_div_iff₀ hD0, one_mul]
  calc |(D : ℝ)| ≤ 2 ^ EG k B := hDabs
    _ ≤ 2 ^ EG k B * |(P : ℝ)| := le_mul_of_one_le_right (by positivity) hPabs

end M5C2

namespace M5C2

open Finset

lemma intCone_rep {n k : ℕ} (r : Fin k → Fin n → ℚ) (Q : Fin k → Prop) [DecidablePred Q]
    (y : Fin n → ℝ) (hy : y ∈ intCone ((fun j => toReal (r j)) '' {j | Q j})) :
    ∃ l : Fin k → ℝ, (∀ j, 0 ≤ l j) ∧ (∀ j, ¬ Q j → l j = 0) ∧ y = ∑ j, l j • toReal (r j) := by
  classical
  induction hy using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    refine ⟨Pi.single j 1, fun j' => ?_, fun j' hj' => ?_, ?_⟩
    · by_cases h : j' = j
      · subst h; simp
      · simp [Pi.single_apply, h]
    · have : j' ≠ j := by rintro rfl; exact hj' hj
      simp [Pi.single_apply, this]
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [Pi.single_apply, hb]
      · simp
  | zero => exact ⟨0, fun _ => le_rfl, fun _ _ => rfl, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨l1, h1, h1', rfl⟩ := hx
    obtain ⟨l2, h2, h2', rfl⟩ := hz
    refine ⟨l1 + l2, fun j => add_nonneg (h1 j) (h2 j), fun j hj => by simp [h1' j hj, h2' j hj], ?_⟩
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

def Gm {n k : ℕ} (r : Fin k → Fin n → ℚ) (H : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin k) (Fin k) ℚ :=
  fun u v => ∑ a, ∑ b, r u a * H a b * r v b

def Gsym {n k : ℕ} (r : Fin k → Fin n → ℚ) (H : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin k) (Fin k) ℚ :=
  fun u v => (Gm r H u v + Gm r H v u) / 2

lemma Gsym_symm {n k : ℕ} (r : Fin k → Fin n → ℚ) (H : Matrix (Fin n) (Fin n) ℚ) (u v : Fin k) :
    Gsym r H u v = Gsym r H v u := by
  unfold Gsym; ring

lemma sum4_comm {ι κ : Type*} [Fintype ι] [Fintype κ] (F : ι → ι → κ → κ → ℝ) :
    ∑ a, ∑ b, ∑ u, ∑ v, F a b u v = ∑ u, ∑ v, ∑ a, ∑ b, F a b u v := by
  calc ∑ a, ∑ b, ∑ u, ∑ v, F a b u v = ∑ a, ∑ u, ∑ b, ∑ v, F a b u v := by
        apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_comm]
    _ = ∑ a, ∑ u, ∑ v, ∑ b, F a b u v := by
        apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro u _
        rw [Finset.sum_comm]
    _ = ∑ u, ∑ a, ∑ v, ∑ b, F a b u v := by rw [Finset.sum_comm]
    _ = ∑ u, ∑ v, ∑ a, ∑ b, F a b u v := by
        apply Finset.sum_congr rfl; intro u _; rw [Finset.sum_comm]

lemma quad_expand {n k : ℕ} (r : Fin k → Fin n → ℚ) (H : Matrix (Fin n) (Fin n) ℚ) (l : Fin k → ℝ) :
    quadForm H (∑ j, l j • toReal (r j)) = phi (Gsym r H) l := by
  have hphi : phi (Gsym r H) l = ∑ u, ∑ v, l u * (Gm r H u v : ℝ) * l v := by
    unfold phi Gsym
    push_cast
    have : ∑ u, ∑ v, l u * (Gm r H v u : ℝ) * l v = ∑ u, ∑ v, l u * (Gm r H u v : ℝ) * l v := by
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl
      intro v _; ring
    have e : ∑ u, ∑ v, l u * (((Gm r H u v : ℝ) + (Gm r H v u : ℝ)) / 2) * l v =
        (∑ u, ∑ v, l u * (Gm r H u v : ℝ) * l v + ∑ u, ∑ v, l u * (Gm r H v u : ℝ) * l v) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl; intro u _
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl; intro v _; ring
    rw [e, this]; ring
  rw [hphi]
  unfold quadForm
  have hy : ∀ a, (∑ j, l j • toReal (r j)) a = ∑ u, l u * (r u a : ℝ) := by
    intro a; simp [Finset.sum_apply, toReal]
  simp only [hy]
  have : ∀ a b, (∑ u, l u * (r u a : ℝ)) * (H a b : ℝ) * (∑ v, l v * (r v b : ℝ)) =
      ∑ u, ∑ v, l u * (r u a : ℝ) * (H a b : ℝ) * (l v * (r v b : ℝ)) := by
    intro a b
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro u _
    rw [Finset.mul_sum]
  simp only [this]
  rw [sum4_comm]
  apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl; intro v _
  unfold Gm; push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro b _
  ring

lemma phi_smul {k : ℕ} (Gs : Matrix (Fin k) (Fin k) ℚ) (c : ℝ) (l : Fin k → ℝ) :
    phi Gs (c • l) = c ^ 2 * phi Gs l := by
  unfold phi
  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _
  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _
  simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma cone_growth {k : ℕ} (Gs : Matrix (Fin k) (Fin k) ℚ) (hsym : ∀ u v, Gs u v = Gs v u)
    (B : ℕ) (hB : ∀ u v, bitSize (Gs u v) ≤ B) (R : Finset (Fin k))
    (hpos : ∀ l : Fin k → ℝ, (∀ j, 0 ≤ l j) → (∀ j, j ∉ R → l j = 0) → l ≠ 0 → 0 < phi Gs l) :
    ∀ l : Fin k → ℝ, (∀ j, 0 ≤ l j) → (∀ j, j ∉ R → l j = 0) →
      (∑ j, l j) ^ 2 ≤ 2 ^ EG k B * phi Gs l := by
  classical
  intro l hl0 hlR
  by_cases hl : l = 0
  · subst hl; simp [phi]
  have hΛ : 0 < ∑ j, l j := by
    obtain ⟨j, hj⟩ : ∃ j, l j ≠ 0 := by
      by_contra h; push Not at h; exact hl (funext h)
    have := Finset.single_le_sum (f := l) (fun j _ => hl0 j) (Finset.mem_univ j)
    have : 0 < l j := lt_of_le_of_ne (hl0 j) (Ne.symm hj)
    linarith
  set Λ := ∑ j, l j
  let S : Set (Fin k → ℝ) := stdSimplex ℝ (Fin k) ∩ ⋂ j ∈ (univ.filter (· ∉ R)), {x | x j = 0}
  have hmemS : ∀ x, x ∈ S ↔ (∀ j, 0 ≤ x j) ∧ (∀ j, j ∉ R → x j = 0) ∧ ∑ j, x j = 1 := by
    intro x
    simp only [S, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, stdSimplex, Finset.mem_filter,
      Finset.mem_univ, true_and]
    tauto
  have hSc : IsCompact S := by
    apply (isCompact_stdSimplex ℝ (Fin k)).inter_right
    apply isClosed_biInter; intro j _
    exact isClosed_eq (continuous_apply j) continuous_const
  have hl' : Λ⁻¹ • l ∈ S := by
    rw [hmemS]
    refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.mpr hΛ.le) (hl0 j)
    · simp [hlR j hj]
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]; exact inv_mul_cancel₀ hΛ.ne'
  have hcont : Continuous (phi Gs) := by unfold phi; fun_prop
  obtain ⟨ls, hlsS, hlsmin⟩ := hSc.exists_isMinOn ⟨_, hl'⟩ hcont.continuousOn
  obtain ⟨hls0, hlsR, hls1⟩ := (hmemS ls).mp hlsS
  have hls_ne : ls ≠ 0 := by rintro rfl; simp at hls1
  have hmin : ∀ l' : Fin k → ℝ, (∀ j, 0 ≤ l' j) → (∀ j, j ∉ R → l' j = 0) → ∑ j, l' j = 1 →
      phi Gs ls ≤ phi Gs l' := fun l' h1 h2 h3 => hlsmin ((hmemS l').mpr ⟨h1, h2, h3⟩)
  have h1 := mu_lower Gs hsym B hB R ls hls0 hlsR hls1 hmin (hpos ls hls0 hlsR hls_ne)
  have h2 : phi Gs ls ≤ phi Gs (Λ⁻¹ • l) := hlsmin hl'
  rw [phi_smul] at h2
  have h3 : (1 : ℝ) ≤ 2 ^ EG k B * (Λ⁻¹ ^ 2 * phi Gs l) :=
    le_trans h1 (mul_le_mul_of_nonneg_left h2 (by positivity))
  have e : Λ ^ 2 * (2 ^ EG k B * (Λ⁻¹ ^ 2 * phi Gs l)) = 2 ^ EG k B * phi Gs l := by
    field_simp
  have h4 : Λ ^ 2 * 1 ≤ Λ ^ 2 * (2 ^ EG k B * (Λ⁻¹ ^ 2 * phi Gs l)) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  rw [e, mul_one] at h4
  exact h4

end M5C2

namespace M5C2

open Finset

lemma Gsym_bitSize {n k : ℕ} (r : Fin k → Fin n → ℚ) (H : Matrix (Fin n) (Fin n) ℚ) (Z : ℕ)
    (hn : n ≤ Z) (hH : ∀ a b, bitSize (H a b) ≤ Z) (hr : ∀ j a, bitSize (r j a) ≤ Z)
    (hCH : ∏ a, ∏ b, (H a b).den ≤ 2 ^ Z) (hCr : ∀ j, ∏ a, (r j a).den ≤ 2 ^ Z) (u v : Fin k) :
    bitSize (Gsym r H u v) ≤ 16 * Z + 5 := by
  classical
  let CH : ℕ := ∏ a, ∏ b, (H a b).den
  let Cu : ℕ := ∏ a, (r u a).den
  let Cv : ℕ := ∏ a, (r v a).den
  have hzH : ∀ a b, ∃ z : ℤ, (CH : ℚ) * H a b = z := fun a b =>
    (scale_int _ CH (dvd_trans (Finset.dvd_prod_of_mem (fun b => (H a b).den) (Finset.mem_univ b))
      (Finset.dvd_prod_of_mem (fun a => ∏ b, (H a b).den) (Finset.mem_univ a)))).imp fun _ h => h.1
  have hzu : ∀ a, ∃ z : ℤ, (Cu : ℚ) * r u a = z := fun a =>
    (scale_int _ Cu (Finset.dvd_prod_of_mem (fun a => (r u a).den) (Finset.mem_univ a))).imp
      fun _ h => h.1
  have hzv : ∀ a, ∃ z : ℤ, (Cv : ℚ) * r v a = z := fun a =>
    (scale_int _ Cv (Finset.dvd_prod_of_mem (fun a => (r v a).den) (Finset.mem_univ a))).imp
      fun _ h => h.1
  choose zH hzH using hzH
  choose zu hzu using hzu
  choose zv hzv using hzv
  set C : ℕ := 2 * CH * Cu * Cv with hC
  set N : ℤ := ∑ a, ∑ b, (zu a * zH a b * zv b + zv a * zH a b * zu b) with hN
  have hCpos : 0 < C := by
    have h1 : 0 < CH := Finset.prod_pos (fun a _ => Finset.prod_pos (fun b _ => (H a b).den_pos))
    have h2 : 0 < Cu := Finset.prod_pos (fun a _ => (r u a).den_pos)
    have h3 : 0 < Cv := Finset.prod_pos (fun a _ => (r v a).den_pos)
    positivity
  have hNeq : (C : ℚ) * Gsym r H u v = N := by
    rw [hN]
    push_cast
    simp only [← hzH, ← hzu, ← hzv]
    have : ∑ a, ∑ b, ((Cu : ℚ) * r u a * ((CH : ℚ) * H a b) * ((Cv : ℚ) * r v b) +
        (Cv : ℚ) * r v a * ((CH : ℚ) * H a b) * ((Cu : ℚ) * r u b)) =
        ((CH : ℚ) * Cu * Cv) * (Gm r H u v + Gm r H v u) := by
      unfold Gm
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro b _
      ring
    rw [this, hC]; unfold Gsym; push_cast; ring
  -- bounds
  have habsZ : ∀ q : ℚ, bitSize q ≤ Z → |q| ≤ 2 ^ Z := fun q hq =>
    le_trans (abs_le_two_pow_bitSize q) (pow_le_pow_right₀ (by norm_num) hq)
  have hG : ∀ u v, |Gm r H u v| ≤ n * (n * (2 ^ Z * 2 ^ Z * 2 ^ Z)) := by
    intro u v
    apply sum_abs_bound
    intro a
    apply sum_abs_bound
    intro b
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (habsZ _ (hr u a)) (habsZ _ (hH a b)) (abs_nonneg _) (by positivity))
      (habsZ _ (hr v b)) (abs_nonneg _) (by positivity)
  have hn2 : (n : ℚ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hGs : |Gsym r H u v| ≤ 2 ^ n * (2 ^ n * (2 ^ Z * 2 ^ Z * 2 ^ Z)) := by
    unfold Gsym
    rw [abs_div, abs_two]
    have h1 := abs_add_le (Gm r H u v) (Gm r H v u)
    have h2 := hG u v
    have h3 := hG v u
    have h4 : (n : ℚ) * (n * (2 ^ Z * 2 ^ Z * 2 ^ Z)) ≤ 2 ^ n * (2 ^ n * (2 ^ Z * 2 ^ Z * 2 ^ Z)) :=
      mul_le_mul hn2 (mul_le_mul_of_nonneg_right hn2 (by positivity)) (by positivity) (by positivity)
    rw [div_le_iff₀ (by norm_num)]
    linarith
  have hCb : (C : ℚ) ≤ 2 * (2 ^ Z * 2 ^ Z * 2 ^ Z) := by
    have h1 : (CH : ℚ) ≤ 2 ^ Z := by exact_mod_cast hCH
    have h2 : (Cu : ℚ) ≤ 2 ^ Z := by exact_mod_cast hCr u
    have h3 : (Cv : ℚ) ≤ 2 ^ Z := by exact_mod_cast hCr v
    rw [hC]; push_cast
    have : (CH : ℚ) * Cu ≤ 2 ^ Z * 2 ^ Z := mul_le_mul h1 h2 (by positivity) (by positivity)
    have : (CH : ℚ) * Cu * Cv ≤ 2 ^ Z * 2 ^ Z * 2 ^ Z :=
      mul_le_mul this h3 (by positivity) (by positivity)
    linarith
  have hβ : (2 : ℚ) * (2 ^ Z * 2 ^ Z * 2 ^ Z) * (2 ^ n * (2 ^ n * (2 ^ Z * 2 ^ Z * 2 ^ Z))) ≤
      2 ^ (8 * Z + 1) := by
    have e : (2 : ℚ) * (2 ^ Z * 2 ^ Z * 2 ^ Z) * (2 ^ n * (2 ^ n * (2 ^ Z * 2 ^ Z * 2 ^ Z))) =
        2 ^ (6 * Z + 2 * n + 1) := by ring
    rw [e]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hNb : |N| ≤ 2 ^ (8 * Z + 1) := by
    have : |(N : ℚ)| ≤ 2 ^ (8 * Z + 1) := by
      rw [← hNeq, abs_mul, abs_of_pos (by exact_mod_cast hCpos : (0 : ℚ) < C)]
      calc (C : ℚ) * |Gsym r H u v| ≤ 2 * (2 ^ Z * 2 ^ Z * 2 ^ Z) * (2 ^ n * (2 ^ n * (2 ^ Z * 2 ^ Z * 2 ^ Z))) :=
            mul_le_mul hCb hGs (abs_nonneg _) (by positivity)
        _ ≤ _ := hβ
    exact_mod_cast this
  have hCb' : |(C : ℤ)| ≤ 2 ^ (8 * Z + 1) := by
    rw [abs_of_nonneg (by positivity)]
    have : (C : ℚ) ≤ 2 ^ (8 * Z + 1) := by
      refine le_trans hCb (le_trans ?_ hβ)
      have h1 : (1 : ℚ) ≤ 2 ^ n * (2 ^ n * (2 ^ Z * 2 ^ Z * 2 ^ Z)) := by
        have h2n : (1 : ℚ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
        have h2Z : (1 : ℚ) ≤ 2 ^ Z := one_le_pow₀ (by norm_num)
        have hT : (1 : ℚ) ≤ 2 ^ Z * 2 ^ Z * 2 ^ Z :=
          one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h2Z h2Z) h2Z
        exact one_le_mul_of_one_le_of_one_le h2n (one_le_mul_of_one_le_of_one_le h2n hT)
      nlinarith
    exact_mod_cast this
  have hq : Gsym r H u v = (N : ℚ) / (C : ℤ) := by
    rw [← hNeq]; push_cast; field_simp
  rw [hq]
  have := bitSize_div_le N C (by exact_mod_cast hCpos.ne') (8 * Z + 1) hNb hCb'
  omega

lemma bounded_small {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (hbdd : Bornology.IsBounded (polyhedron A b)) (p : Fin n → ℝ) (hp : p ∈ polyhedron A b)
    (a : Fin n → ℝ) (Z0 : ℕ) (hn : n ≤ Z0) (hAb : matSize A + vecSize b ≤ Z0) :
    ∃ y : Fin n → ℚ, toReal y ∈ polyhedron A b ∧ ∑ j, a j * toReal y j ≤ ∑ j, a j * p j ∧
      ∀ u, |y u| ≤ 2 ^ (3 * (Z0 * Z0)) := by
  classical
  have hnr := no_rec A b hbdd p hp
  have hH : ∀ d : Fin n → ℝ, (∃ l, rdot A l d ≠ 0) →
      ∃ s : ℝ, ∑ j, a j * (s * d j) ≤ 0 ∧ ∃ l, 0 < s * rdot A l d := by
    rintro d ⟨l, hl⟩
    have hd0 : d ≠ 0 := by rintro rfl; simp [rdot] at hl
    by_cases had : ∑ j, a j * d j ≤ 0
    · refine ⟨1, by simpa using had, ?_⟩
      by_contra hcon; push Not at hcon
      exact hd0 (hnr d (fun l => by simpa using hcon l))
    · refine ⟨-1, ?_, ?_⟩
      · push Not at had
        have : ∑ j, a j * (-1 * d j) = -∑ j, a j * d j := by
          rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _; ring
        linarith
      · by_contra hcon; push Not at hcon
        have : -d = 0 := hnr (-d) (fun l => by
          have := hcon l
          rw [show -d = (-1:ℝ) • d by simp, rdot_smul]; linarith)
        exact hd0 (neg_eq_zero.mp this)
  have hH' : ∀ d : Fin n → ℝ, (∀ l, rdot A l d = 0) → ∑ j, a j * d j = 0 := by
    intro d hd
    have := hnr d (fun l => (hd l).le)
    subst this; simp
  obtain ⟨y, hyP, hya, I, hI, D, hD, hDb, hP⟩ := small_point A b a hH hH' p hp
  refine ⟨y, hyP, hya, fun u => ?_⟩
  have hrs : ∑ l ∈ I, rs A b l ≤ Z0 := by
    have h1 : ∑ l ∈ I, rs A b l ≤ ∑ l, rs A b l :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ I)
    have h2 : ∑ l, rs A b l = ∑ l, ∑ j, bitSize (A l j) + ∑ l, bitSize (b l) := by
      simp only [rs, Finset.sum_add_distrib]
    have h3 : ∑ l, ∑ j, bitSize (A l j) ≤ matSize A := by unfold matSize; omega
    have h4 : ∑ l, bitSize (b l) ≤ vecSize b := by unfold vecSize; omega
    omega
  have hα : alpha n (∑ l ∈ I, rs A b l) ≤ 3 * (Z0 * Z0) := by
    unfold alpha
    have := Nat.mul_le_mul hn hn
    have := Nat.mul_le_mul hn (Nat.mul_le_mul_left 2 hrs)
    nlinarith
  obtain ⟨P, hPb, hPe⟩ := hP u
  have hDge : (1 : ℚ) ≤ |(D : ℚ)| := by
    have : (1 : ℤ) ≤ |D| := Int.one_le_abs hD
    exact_mod_cast this
  rw [hPe, abs_div]
  have : (|(P : ℚ)|) ≤ 2 ^ (3 * (Z0 * Z0)) := by
    have := le_trans hPb (pow_le_pow_right₀ (by norm_num) hα)
    exact_mod_cast this
  calc |(P : ℚ)| / |(D : ℚ)| ≤ |(P : ℚ)| := div_le_self (abs_nonneg _) hDge
    _ ≤ _ := this

lemma coord_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (hbdd : Bornology.IsBounded (polyhedron A b)) (p : Fin n → ℝ) (hp : p ∈ polyhedron A b)
    (Z0 : ℕ) (hn : n ≤ Z0) (hAb : matSize A + vecSize b ≤ Z0) (u : Fin n) :
    |p u| ≤ 2 ^ (3 * (Z0 * Z0)) := by
  classical
  obtain ⟨y1, -, hy1, hb1⟩ := bounded_small A b hbdd p hp (fun j => if j = u then 1 else 0) Z0 hn hAb
  obtain ⟨y2, -, hy2, hb2⟩ := bounded_small A b hbdd p hp (fun j => if j = u then -1 else 0) Z0 hn hAb
  simp only [ite_mul, one_mul, zero_mul, neg_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hy1 hy2
  have h1 : |(y1 u : ℝ)| ≤ 2 ^ (3 * (Z0 * Z0)) := by
    have := hb1 u; exact_mod_cast this
  have h2 : |(y2 u : ℝ)| ≤ 2 ^ (3 * (Z0 * Z0)) := by
    have := hb2 u; exact_mod_cast this
  simp only [toReal] at hy1 hy2
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h2.2]

end M5C2

open scoped Pointwise

namespace M5C2

lemma euclidNorm_eq {n : ℕ} (x : Fin n → ℝ) :
    euclidNorm x = ‖(WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm x‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold euclidNorm
  congr 1
  apply Finset.sum_congr rfl; intro i _
  simp [sq_abs]

lemma euclidNorm_le' {n : ℕ} (z : Fin n → ℝ) (M : ℝ) (hM : 0 ≤ M) (h : ∀ u, |z u| ≤ M) :
    euclidNorm z ≤ n * M := by
  unfold euclidNorm
  have h1 : ∑ u, z u ^ 2 ≤ ((n : ℝ) * M) ^ 2 := by
    have : ∑ u, z u ^ 2 ≤ ∑ _u : Fin n, M ^ 2 := Finset.sum_le_sum (fun u _ => by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h u) 2)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp
      · have : (1 : ℝ) ≤ n := by exact_mod_cast h0
        nlinarith
    nlinarith [sq_nonneg M]
  calc Real.sqrt (∑ u, z u ^ 2) ≤ Real.sqrt (((n : ℝ) * M) ^ 2) := Real.sqrt_le_sqrt h1
    _ = n * M := Real.sqrt_sq (by positivity)

lemma euclidNorm_add_le {n : ℕ} (x y : Fin n → ℝ) : euclidNorm (x + y) ≤ euclidNorm x + euclidNorm y := by
  rw [euclidNorm_eq, euclidNorm_eq, euclidNorm_eq, map_add]; exact norm_add_le _ _

lemma abs_sum2_le {n : ℕ} (f : Fin n → Fin n → ℝ) (B : ℝ) (h : ∀ a b, |f a b| ≤ B) :
    |∑ a, ∑ b, f a b| ≤ n * (n * B) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have : ∀ a, |∑ b, f a b| ≤ n * B := by
    intro a
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => h a b)
    simpa using this
  have := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => this a)
  simpa using this

lemma abs_sum1_le {n : ℕ} (f : Fin n → ℝ) (B : ℝ) (h : ∀ a, |f a| ≤ B) :
    |∑ a, f a| ≤ n * B := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => h a)
  simpa using this

end M5C2

open M5Core M5C1 M5C2


noncomputable def gpoly2 : Polynomial ℕ :=
  (Polynomial.X + 1) * (Polynomial.X + 1) + (Polynomial.X + 1) * (2 * ((Polynomial.X + 1) *
    ((Polynomial.X + 1) * (16 * Polynomial.X + 5 + 3) + 3))) + 3 +
    7 * (3 * (Polynomial.X * Polynomial.X) + 2 * Polynomial.X) + 3

theorem claim2_core :
    ∃ g : Polynomial ℕ, ∀ (n mP k : ℕ) (A' : Matrix (Fin mP) (Fin n) ℚ) (b' : Fin mP → ℚ)
      (r : Fin k → Fin n → ℚ) (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (d : ℚ),
      Bornology.IsBounded (polyhedron A' b') →
      LinearIndependent ℝ (fun j => toReal (r j)) →
      (∀ x ∈ cone ((fun j => toReal (r j)) '' {j | quadForm H (toReal (r j)) ≠ 0}),
          x ≠ 0 → 0 < quadForm H x) →
      ∃ v : ℚ,
        bitSize v ≤ g.eval (matSize A' + vecSize b' + ∑ j, vecSize (r j) + matSize H + vecSize c
          + bitSize d) ∧
        ∀ x ∈ polyhedron A' b' + intCone ((fun j => toReal (r j)) '' {j | quadForm H (toReal (r j)) ≠ 0}),
          quadVal H c d x ≤ 0 → euclidNorm x ≤ v := by
  refine ⟨gpoly2, ?_⟩
  intro n mP k A' b' r H c d hbdd hli hpos
  classical
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = matSize A' + vecSize b' + ∑ j, vecSize (r j) + matSize H + vecSize c
      + bitSize d := ⟨_, rfl⟩
  rw [← hZ]
  obtain ⟨E0, hE0⟩ : ∃ E0, E0 = 3 * (Z * Z) + 2 * Z := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = 16 * Z + 5 := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = EG Z B + 3 + 7 * E0 := ⟨_, rfl⟩
  refine ⟨(2 : ℚ) ^ E, ?_, ?_⟩
  · have e1 : ((2 : ℚ) ^ E) = ((2 ^ E : ℕ) : ℚ) := by push_cast; rfl
    have hbs : bitSize ((2 : ℚ) ^ E) = E + 3 := by
      unfold bitSize
      rw [e1, Rat.num_natCast, Rat.den_natCast, Int.natAbs_natCast, Nat.size_pow, Nat.size_one]
      ring
    rw [hbs]
    have : gpoly2.eval Z = (Z + 1) * (Z + 1) + (Z + 1) * (2 * ((Z + 1) * ((Z + 1) * (16 * Z + 5 + 3) + 3)))
        + 3 + 7 * (3 * (Z * Z) + 2 * Z) + 3 := by
      simp [gpoly2]
    rw [this, hE, hE0, hB]
    unfold EG
    ring_nf; omega
  intro x hx hq
  obtain ⟨p, hp, y, hy, rfl⟩ := Set.mem_add.mp hx
  obtain ⟨l, hl0, hlQ, rfl⟩ := intCone_rep r (fun j => quadForm H (toReal (r j)) ≠ 0) y hy
  set R : Finset (Fin k) := Finset.univ.filter (fun j => quadForm H (toReal (r j)) ≠ 0) with hR
  have hlR : ∀ j, j ∉ R → l j = 0 := by
    intro j hj; apply hlQ; simpa [hR] using hj
  -- size facts
  have hnZ : n ≤ Z := by
    have : n ≤ vecSize c := by unfold vecSize; omega
    omega
  have hbH : ∀ u v, bitSize (H u v) ≤ Z := by
    intro u v
    have h1 : bitSize (H u v) ≤ ∑ v, bitSize (H u v) := bit_le_sum (fun v => bitSize (H u v)) v
    have h2 : ∑ v, bitSize (H u v) ≤ ∑ u, ∑ v, bitSize (H u v) :=
      bit_le_sum (fun u => ∑ v, bitSize (H u v)) u
    have h3 : ∑ u, ∑ v, bitSize (H u v) ≤ matSize H := by unfold matSize; omega
    omega
  have hbr : ∀ j' v, bitSize (r j' v) ≤ Z := by
    intro j' v
    have h1 : bitSize (r j' v) ≤ ∑ v, bitSize (r j' v) := bit_le_sum (fun v => bitSize (r j' v)) v
    have h2 : vecSize (r j') ≤ ∑ j, vecSize (r j) := bit_le_sum (fun j' => vecSize (r j')) j'
    have h3 : ∑ v, bitSize (r j' v) ≤ vecSize (r j') := by unfold vecSize; omega
    omega
  have hbc : ∀ u, bitSize (c u) ≤ Z := by
    intro u
    have h1 : bitSize (c u) ≤ ∑ u, bitSize (c u) := bit_le_sum (fun u => bitSize (c u)) u
    have h3 : ∑ u, bitSize (c u) ≤ vecSize c := by unfold vecSize; omega
    omega
  have hbd : bitSize d ≤ Z := by omega
  have hCH : ∏ u, ∏ v, (H u v).den ≤ 2 ^ Z := by
    have h1 : ∏ u, ∏ v, (H u v).den ≤ ∏ u, 2 ^ (∑ v, bitSize (H u v)) :=
      Finset.prod_le_prod' (fun u _ => prod_den_le (fun v => H u v))
    rw [Finset.prod_pow_eq_pow_sum] at h1
    have h3 : ∑ u, ∑ v, bitSize (H u v) ≤ matSize H := by unfold matSize; omega
    exact le_trans h1 (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hCr : ∀ j', ∏ v, (r j' v).den ≤ 2 ^ Z := by
    intro j'
    have h1 := prod_den_le (fun v => r j' v)
    have h2 : vecSize (r j') ≤ ∑ j, vecSize (r j) := bit_le_sum (fun j' => vecSize (r j')) j'
    have h3 : ∑ v, bitSize (r j' v) ≤ vecSize (r j') := by unfold vecSize; omega
    exact le_trans h1 (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hk : k ≤ n := by
    have := hli.fintype_card_le_finrank
    simpa using this
  have hGB : ∀ u v, bitSize (Gsym r H u v) ≤ B := by
    intro u v; rw [hB]; exact Gsym_bitSize r H Z hnZ hbH hbr hCH hCr u v
  -- positivity in coefficient space
  have hpos' : ∀ l' : Fin k → ℝ, (∀ j, 0 ≤ l' j) → (∀ j, j ∉ R → l' j = 0) → l' ≠ 0 →
      0 < phi (Gsym r H) l' := by
    intro l' h0 hR' hne
    rw [← quad_expand]
    apply hpos
    · unfold cone
      apply Submodule.sum_mem
      intro j _
      by_cases hj : j ∈ R
      · have hmem : toReal (r j) ∈ (fun j => toReal (r j)) '' {j | quadForm H (toReal (r j)) ≠ 0} :=
          ⟨j, by simpa [hR] using hj, rfl⟩
        have := Submodule.smul_mem (Submodule.span NNReal _) (⟨l' j, h0 j⟩ : NNReal)
          (Submodule.subset_span hmem)
        have e : (⟨l' j, h0 j⟩ : NNReal) • toReal (r j) = l' j • toReal (r j) := NNReal.smul_def _ _
        rw [← e]; exact this
      · rw [hR' j hj, zero_smul]; exact Submodule.zero_mem _
    · intro h0'
      apply hne
      have := (Fintype.linearIndependent_iff.mp hli) l' h0'
      exact funext this
  have hgrow := cone_growth (Gsym r H) (Gsym_symm r H) B hGB R hpos' l hl0 hlR
  have hEG : EG k B ≤ EG Z B := by
    have hkZ : k ≤ Z := by omega
    unfold EG
    gcongr
  set Λ := ∑ j, l j with hΛ
  set G : ℝ := 2 ^ EG Z B with hG
  have hG1 : (1 : ℝ) ≤ G := one_le_pow₀ (by norm_num)
  have hgrow' : Λ ^ 2 ≤ G * phi (Gsym r H) l := by
    have hphi0 : 0 ≤ phi (Gsym r H) l := by
      by_contra h; push Not at h
      have : (2 : ℝ) ^ EG k B * phi (Gsym r H) l < 0 := mul_neg_of_pos_of_neg (by positivity) h
      linarith [sq_nonneg Λ]
    refine le_trans hgrow (mul_le_mul_of_nonneg_right ?_ hphi0)
    exact pow_le_pow_right₀ (by norm_num) hEG
  set W : ℝ := 2 ^ E0 with hW
  have hW1 : (1 : ℝ) ≤ W := one_le_pow₀ (by norm_num)
  have hZW : (2 : ℝ) ^ Z ≤ W := pow_le_pow_right₀ (by norm_num) (by omega)
  have hqW : ∀ q : ℚ, bitSize q ≤ Z → |(q : ℝ)| ≤ W := by
    intro q hq
    have : |q| ≤ 2 ^ Z := le_trans (abs_le_two_pow_bitSize q) (pow_le_pow_right₀ (by norm_num) hq)
    have : |(q : ℝ)| ≤ 2 ^ Z := by exact_mod_cast this
    linarith
  have hnW : (n : ℝ) ≤ W := by
    have : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
    have : (2 : ℝ) ^ n ≤ 2 ^ Z := pow_le_pow_right₀ (by norm_num) hnZ
    linarith
  have hpW : ∀ u, |p u| ≤ W := by
    intro u
    have := coord_bound A' b' hbdd p hp Z hnZ (by omega) u
    have h2 : (2 : ℝ) ^ (3 * (Z * Z)) ≤ W := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hΛ0 : 0 ≤ Λ := Finset.sum_nonneg (fun j _ => hl0 j)
  set y := ∑ j, l j • toReal (r j) with hy_def
  have hyW : ∀ b, |y b| ≤ Λ * W := by
    intro b
    have e : y b = ∑ j, l j * (r j b : ℝ) := by simp [hy_def, Finset.sum_apply, toReal]
    rw [e]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [hΛ, Finset.sum_mul]
    apply Finset.sum_le_sum; intro j _
    rw [abs_mul, abs_of_nonneg (hl0 j)]
    exact mul_le_mul_of_nonneg_left (hqW _ (hbr j b)) (hl0 j)
  have hexp : quadVal H c d (p + y) = quadForm H p + quadForm H y
      + ∑ a, ∑ b, (p a * (H a b : ℝ) * y b + y a * (H a b : ℝ) * p b)
      + ∑ a, (c a : ℝ) * p a + ∑ a, (c a : ℝ) * y a + d := by
    unfold quadVal quadForm
    simp only [Pi.add_apply]
    have e1 : ∑ i, ∑ j, (p i + y i) * (H i j : ℝ) * (p j + y j) =
        ∑ i, ∑ j, p i * (H i j : ℝ) * p j + ∑ i, ∑ j, y i * (H i j : ℝ) * y j +
        ∑ a, ∑ b, (p a * (H a b : ℝ) * y b + y a * (H a b : ℝ) * p b) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _; ring
    have e2 : ∑ i, (c i : ℝ) * (p i + y i) = ∑ a, (c a : ℝ) * p a + ∑ a, (c a : ℝ) * y a := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    rw [e1, e2]; ring
  have hX : |∑ a, ∑ b, (p a * (H a b : ℝ) * y b + y a * (H a b : ℝ) * p b)| ≤
      n * (n * (2 * (W * W * (Λ * W)))) := by
    apply abs_sum2_le; intro a b
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_mul, abs_mul, abs_mul]
    have h1 := hpW a; have h2 := hqW _ (hbH a b); have h3 := hyW b; have h4 := hyW a
    have h5 := hpW b
    have t1 : |p a| * |(H a b : ℝ)| * |y b| ≤ W * W * (Λ * W) :=
      mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by linarith)) h3 (abs_nonneg _) (by positivity)
    have t2 : |y a| * |(H a b : ℝ)| * |p b| ≤ (Λ * W) * W * W :=
      mul_le_mul (mul_le_mul h4 h2 (abs_nonneg _) (by positivity)) h5 (abs_nonneg _) (by positivity)
    nlinarith
  have hcy : |∑ a, (c a : ℝ) * y a| ≤ n * (W * (Λ * W)) := by
    apply abs_sum1_le; intro a; rw [abs_mul]
    exact mul_le_mul (hqW _ (hbc a)) (hyW a) (abs_nonneg _) (by linarith)
  have hqp : |quadForm H p| ≤ n * (n * (W * W * W)) := by
    unfold quadForm
    apply abs_sum2_le; intro a b; rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hpW a) (hqW _ (hbH a b)) (abs_nonneg _) (by linarith)) (hpW b)
      (abs_nonneg _) (by positivity)
  have hcp : |∑ a, (c a : ℝ) * p a| ≤ n * (W * W) := by
    apply abs_sum1_le; intro a; rw [abs_mul]
    exact mul_le_mul (hqW _ (hbc a)) (hpW a) (abs_nonneg _) (by linarith)
  have hdW : |(d : ℝ)| ≤ W := hqW d hbd
  have hqy : quadForm H y = phi (Gsym r H) l := quad_expand r H l
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have key : phi (Gsym r H) l ≤ 3 * W ^ 5 * Λ + 3 * W ^ 5 := by
    have hnn : (n:ℝ) * n ≤ W * W := mul_le_mul hnW hnW hn0 (by linarith)
    have h1 : (n:ℝ) * (n * (2 * (W * W * (Λ * W)))) ≤ 2 * W ^ 5 * Λ := by
      have hp : 0 ≤ 2 * (W * W * (Λ * W)) := by positivity
      calc (n:ℝ) * (n * (2 * (W * W * (Λ * W)))) = (n * n) * (2 * (W * W * (Λ * W))) := by ring
        _ ≤ (W * W) * (2 * (W * W * (Λ * W))) := mul_le_mul_of_nonneg_right hnn hp
        _ = 2 * W ^ 5 * Λ := by ring
    have h2 : (n:ℝ) * (W * (Λ * W)) ≤ W ^ 5 * Λ := by
      calc (n:ℝ) * (W * (Λ * W)) ≤ W * (W * (Λ * W)) := mul_le_mul_of_nonneg_right hnW (by positivity)
        _ = W ^ 3 * Λ := by ring
        _ ≤ W ^ 5 * Λ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hW1 (by norm_num)) hΛ0
    have h3 : (n:ℝ) * (n * (W * W * W)) ≤ W ^ 5 := by
      calc (n:ℝ) * (n * (W * W * W)) = (n * n) * (W * W * W) := by ring
        _ ≤ (W * W) * (W * W * W) := mul_le_mul_of_nonneg_right hnn (by positivity)
        _ = W ^ 5 := by ring
    have h4 : (n:ℝ) * (W * W) ≤ W ^ 5 := by
      calc (n:ℝ) * (W * W) ≤ W * (W * W) := mul_le_mul_of_nonneg_right hnW (by positivity)
        _ = W ^ 3 := by ring
        _ ≤ W ^ 5 := pow_le_pow_right₀ hW1 (by norm_num)
    have h5 : W ≤ W ^ 5 := by
      calc W = W ^ 1 := (pow_one W).symm
        _ ≤ W ^ 5 := pow_le_pow_right₀ hW1 (by norm_num)
    rw [hexp, hqy] at hq
    have := abs_le.mp hX; have := abs_le.mp hcy; have := abs_le.mp hqp; have := abs_le.mp hcp
    have := abs_le.mp hdW
    linarith
  have hΛb : Λ ≤ 6 * G * W ^ 5 := by
    have hGW : 1 ≤ G * W ^ 5 := one_le_mul_of_one_le_of_one_le hG1 (one_le_pow₀ hW1)
    by_cases h1 : Λ ≤ 1
    · linarith
    · push Not at h1
      have h2 : Λ ^ 2 ≤ G * (3 * W ^ 5 * Λ + 3 * W ^ 5) :=
        le_trans hgrow' (mul_le_mul_of_nonneg_left key (by linarith))
      have hGW0 : 0 ≤ G * W ^ 5 := by linarith
      have h3 : G * (3 * W ^ 5 * Λ + 3 * W ^ 5) ≤ 6 * G * W ^ 5 * Λ := by nlinarith
      have h4 : Λ * Λ ≤ (6 * G * W ^ 5) * Λ := by nlinarith
      exact le_of_mul_le_mul_right h4 (by linarith)
  have hnorm : euclidNorm (p + y) ≤ euclidNorm p + euclidNorm y := euclidNorm_add_le p y
  have hnp : euclidNorm p ≤ n * W := euclidNorm_le' p W (by linarith) hpW
  have hny : euclidNorm y ≤ n * (Λ * W) := euclidNorm_le' y (Λ * W) (by positivity) hyW
  have hfin : (n : ℝ) * W + n * (Λ * W) ≤ (2 : ℝ) ^ E := by
    have e : (2 : ℝ) ^ E = 8 * G * W ^ 7 := by rw [hE, hG, hW]; ring
    rw [e]
    have hW0 : (0 : ℝ) ≤ W := by linarith
    have h1 : (n : ℝ) * W ≤ W ^ 2 := by
      have := mul_le_mul_of_nonneg_right hnW hW0
      calc (n : ℝ) * W ≤ W * W := this
        _ = W ^ 2 := by ring
    have h2 : (n : ℝ) * (Λ * W) ≤ W ^ 2 * Λ := by
      have := mul_le_mul_of_nonneg_right hnW (by positivity : 0 ≤ Λ * W)
      calc (n : ℝ) * (Λ * W) ≤ W * (Λ * W) := this
        _ = W ^ 2 * Λ := by ring
    have h3 : W ^ 2 * Λ ≤ 6 * (G * W ^ 7) := by
      calc W ^ 2 * Λ ≤ W ^ 2 * (6 * G * W ^ 5) := mul_le_mul_of_nonneg_left hΛb (by positivity)
        _ = 6 * (G * W ^ 7) := by ring
    have h4 : W ^ 2 ≤ G * W ^ 7 := by
      have : W ^ 2 ≤ W ^ 7 := pow_le_pow_right₀ hW1 (by norm_num)
      have : W ^ 7 ≤ G * W ^ 7 := le_mul_of_one_le_left (by positivity) hG1
      linarith
    have e8 : 8 * G * W ^ 7 = 8 * (G * W ^ 7) := by ring
    rw [e8]
    have h5 : (0 : ℝ) ≤ G * W ^ 7 := by positivity
    linarith
  push_cast
  linarith

theorem solution :
    ∃ g : Polynomial ℕ, ∀ (n mP k : ℕ) (A' : Matrix (Fin mP) (Fin n) ℚ) (b' : Fin mP → ℚ)
      (r : Fin k → Fin n → ℚ) (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (d : ℚ),
      Bornology.IsBounded (polyhedron A' b') →
      LinearIndependent ℝ (fun j => toReal (r j)) →
      (∀ x ∈ cone ((fun j => toReal (r j)) '' {j | quadForm H (toReal (r j)) ≠ 0}),
          x ≠ 0 → 0 < quadForm H x) →
      ∃ v : ℚ,
        bitSize v ≤ g.eval (matSize A' + vecSize b' + ∑ j, vecSize (r j) + matSize H + vecSize c
          + bitSize d) ∧
        ∀ x ∈ polyhedron A' b' + intCone ((fun j => toReal (r j)) '' {j | quadForm H (toReal (r j)) ≠ 0}),
          quadVal H c d x ≤ 0 → euclidNorm x ≤ v :=
  claim2_core
