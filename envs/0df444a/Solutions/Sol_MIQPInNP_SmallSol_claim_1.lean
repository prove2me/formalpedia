-- Prove2me | solution 1 for MIQPInNP.SmallSol.claim_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:29:28.40871+00:00
-- url     : https://prove2.me/submissions/242656fb-fce9-402e-b9a8-0ff35ae552d3

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

open MIQPInNP.SmallSol M5Core M5C1
open scoped Pointwise

theorem claim1_core : ∃ g : Polynomial ℕ, ∀ (n mP k : ℕ) (A' : Matrix (Fin mP) (Fin n) ℚ) (b' : Fin mP → ℚ)
      (r : Fin k → Fin n → ℚ) (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (i : Fin k),
      Bornology.IsBounded (polyhedron A' b') →
      LinearIndependent ℝ (fun j => toReal (r j)) →
      quadForm H (toReal (r i)) = 0 →
      (∃ x ∈ polyhedron A' b' + intCone ((fun j => toReal (r j)) '' {j | j ≠ i}),
          2 * (∑ u, ∑ v, x u * (H u v : ℝ) * toReal (r i) v) + ∑ u, (c u : ℝ) * toReal (r i) u
            < 0) →
      ∃ xt : Fin n → ℚ,
        toReal xt ∈ polyhedron A' b' + intCone ((fun j => toReal (r j)) '' {j | j ≠ i}) ∧
        2 * (∑ u, ∑ v, toReal xt u * (H u v : ℝ) * toReal (r i) v)
            + ∑ u, (c u : ℝ) * toReal (r i) u < 0 ∧
        vecSize xt ≤ g.eval (matSize A' + vecSize b' + ∑ j, vecSize (r j) + matSize H + vecSize c) := by
  refine ⟨Polynomial.X * (12 * Polynomial.X ^ 2 + 16 * Polynomial.X + 12), ?_⟩
  intro n mP k A' b' r H c i hbdd _ _ hex
  obtain ⟨x, hx, hLx⟩ := hex
  classical
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = matSize A' + vecSize b' + ∑ j, vecSize (r j) + matSize H + vecSize c :=
    ⟨_, rfl⟩
  rw [← hZ]
  have hevalZ : (Polynomial.X * (12 * Polynomial.X ^ 2 + 16 * Polynomial.X + 12) : Polynomial ℕ).eval Z
      = Z * (12 * Z ^ 2 + 16 * Z + 12) := by
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_ofNat]
  rw [hevalZ]
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
  have habsZ : ∀ q : ℚ, bitSize q ≤ Z → |q| ≤ 2 ^ Z := fun q hq =>
    le_trans (abs_le_two_pow_bitSize q) (pow_le_pow_right₀ (by norm_num) hq)
  -- the linear functional
  let a : Fin n → ℚ := fun u => 2 * ∑ v, H u v * r i v
  let c0 : ℚ := ∑ u, c u * r i u
  have hL : ∀ z : Fin n → ℝ, 2 * (∑ u, ∑ v, z u * (H u v : ℝ) * toReal (r i) v)
      + ∑ u, (c u : ℝ) * toReal (r i) u = ∑ u, (a u : ℝ) * z u + c0 := by
    intro z
    simp only [a, c0, toReal]; push_cast
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl; intro v _; ring
  obtain ⟨p, hp, w, hw, rfl⟩ := Set.mem_add.mp hx
  have hnr := no_rec A' b' hbdd p hp
  have hH : ∀ d : Fin n → ℝ, (∃ l, rdot A' l d ≠ 0) →
      ∃ s : ℝ, ∑ j, toReal a j * (s * d j) ≤ 0 ∧ ∃ l, 0 < s * rdot A' l d := by
    rintro d ⟨l, hl⟩
    have hd0 : d ≠ 0 := by rintro rfl; simp [rdot] at hl
    by_cases had : ∑ j, toReal a j * d j ≤ 0
    · refine ⟨1, by simpa using had, ?_⟩
      by_contra hcon; push Not at hcon
      exact hd0 (hnr d (fun l => by simpa using hcon l))
    · refine ⟨-1, ?_, ?_⟩
      · push Not at had
        have : ∑ j, toReal a j * (-1 * d j) = -∑ j, toReal a j * d j := by
          rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _; ring
        linarith
      · by_contra hcon; push Not at hcon
        have : -d = 0 := hnr (-d) (fun l => by
          have := hcon l
          rw [show -d = (-1:ℝ) • d by simp, rdot_smul]; linarith)
        exact hd0 (neg_eq_zero.mp this)
  have hH' : ∀ d : Fin n → ℝ, (∀ l, rdot A' l d = 0) → ∑ j, toReal a j * d j = 0 := by
    intro d hd
    have := hnr d (fun l => (hd l).le)
    subst this; simp
  obtain ⟨y, hyP, hya, I, hI, D, hD, hDb, hP⟩ := small_point A' b' (toReal a) hH hH' p hp
  obtain ⟨α, hα_def⟩ : ∃ α, α = alpha n (∑ l ∈ I, rs A' b' l) := ⟨_, rfl⟩
  rw [← hα_def] at hDb hP
  have hrsZ : ∑ l ∈ I, rs A' b' l ≤ Z := by
    have h1 : ∑ l ∈ I, rs A' b' l ≤ ∑ l, rs A' b' l :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ I)
    have h2 : ∑ l, rs A' b' l = ∑ l, ∑ j, bitSize (A' l j) + ∑ l, bitSize (b' l) := by
      simp only [rs, Finset.sum_add_distrib]
    have h3 : ∑ l, ∑ j, bitSize (A' l j) ≤ matSize A' := by unfold matSize; omega
    have h4 : ∑ l, bitSize (b' l) ≤ vecSize b' := by unfold vecSize; omega
    omega
  have hαZ : α ≤ 3 * (Z * Z) := by
    rw [hα_def]; unfold alpha
    have := Nat.mul_le_mul hnZ hnZ
    have := Nat.mul_le_mul hnZ (Nat.mul_le_mul_left 2 hrsZ)
    nlinarith
  have hDge : (1 : ℚ) ≤ |(D : ℚ)| := by
    have : (1 : ℤ) ≤ |D| := Int.one_le_abs hD
    exact_mod_cast this
  have hyb : ∀ u, |y u| ≤ 2 ^ α := by
    intro u
    obtain ⟨P, hPb, hPe⟩ := hP u
    rw [hPe, abs_div]
    have : (|(P : ℚ)|) ≤ 2 ^ α := by exact_mod_cast hPb
    calc |(P : ℚ)| / |(D : ℚ)| ≤ |(P : ℚ)| := div_le_self (abs_nonneg _) hDge
      _ ≤ 2 ^ α := this
  have hyrep : ∀ u, ∃ P D : ℤ, D ≠ 0 ∧ |P| ≤ 2 ^ α ∧ |D| ≤ 2 ^ α ∧ (y u : ℚ) = P / D := by
    intro u; obtain ⟨P, hPb, hPe⟩ := hP u; exact ⟨P, D, hD, hPb, hDb, hPe⟩
  have hLsplit : ∑ u, (a u : ℝ) * (p + w) u = ∑ u, (a u : ℝ) * p u + ∑ u, (a u : ℝ) * w u := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [hL, hLsplit] at hLx
  have hya' : ∑ u, (a u : ℝ) * toReal y u ≤ ∑ u, (a u : ℝ) * p u := hya
  by_cases hcase : 0 ≤ ∑ u, (a u : ℝ) * w u
  · refine ⟨y, Set.mem_add.mpr ⟨toReal y, hyP, 0, (AddSubmonoid.closure _).zero_mem, add_zero _⟩, ?_, ?_⟩
    · rw [hL]; linarith
    · have hv := vecSize_le_of_rep' y α hyrep
      calc vecSize y ≤ n * (2 * α + 4) := hv
        _ ≤ Z * (12 * Z ^ 2 + 16 * Z + 12) := by
          apply Nat.mul_le_mul hnZ; nlinarith
  · push Not at hcase
    obtain ⟨j, hji, hjneg⟩ : ∃ j, j ≠ i ∧ ∑ u, (a u : ℝ) * toReal (r j) u < 0 := by
      by_contra hcon
      push Not at hcon
      have := intCone_nonneg _ (fun u => (a u : ℝ)) (by
        rintro g ⟨j, hj, rfl⟩; exact hcon j hj) w hw
      linarith
    have hδpos : 0 < -∑ u, a u * r j u := by
      have : ((∑ u, a u * r j u : ℚ) : ℝ) < 0 := by
        push_cast; simpa [toReal] using hjneg
      have : (∑ u, a u * r j u : ℚ) < 0 := by exact_mod_cast this
      linarith
    have hδlb := delta_lb H (r i) (r j) Z hCH (hCr i) (hCr j) hδpos
    have hQb := Qbound (Z := Z) a y c (r i) (fun u => abound _ _ (fun v => habsZ _ (hbH u v))
      (fun v => habsZ _ (hbr i v))) hyb (fun u => habsZ _ (hbc u)) (fun u => habsZ _ (hbr i u))
    have hK := choose_K _ _ _ Z hQb hδpos hδlb
    obtain ⟨K, hKdef⟩ : ∃ K, K = 2 * n + 2 * Z + α + 2 + 3 * Z + 1 := ⟨_, rfl⟩
    rw [← hKdef] at hK
    let xt : Fin n → ℚ := fun u => y u + 2 ^ K * r j u
    refine ⟨xt, ?_, ?_, ?_⟩
    · refine Set.mem_add.mpr ⟨toReal y, hyP, (2 ^ K : ℕ) • toReal (r j),
        AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure
          (Set.mem_image_of_mem _ (show j ∈ {j | j ≠ i} from hji))) _, ?_⟩
      funext u
      simp [toReal, xt, nsmul_eq_mul]
    · rw [hL]
      have e1 : ∑ u, a u * xt u = ∑ u, a u * y u + 2 ^ K * ∑ u, a u * r j u := by
        simp only [xt, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1; apply Finset.sum_congr rfl; intro u _; ring
      have e2 : ∑ u, (a u : ℝ) * toReal xt u + c0 = ((∑ u, a u * xt u + c0 : ℚ) : ℝ) := by
        simp [toReal]
      rw [e2]
      have : ∑ u, a u * xt u + c0 < 0 := by
        rw [e1]
        have h1 : 2 ^ K * ∑ u, a u * r j u = -(2 ^ K * -∑ u, a u * r j u) := by ring
        rw [add_right_comm, h1]
        linarith
      exact_mod_cast this
    · have hxrep : ∀ u, ∃ P D : ℤ, D ≠ 0 ∧ |P| ≤ 2 ^ (α + Z + K + 1) ∧ |D| ≤ 2 ^ (α + Z + K + 1) ∧
          (xt u : ℚ) = P / D := by
        intro u
        obtain ⟨P, hPb, hPe⟩ := hP u
        have := xt_rep α Z K P D hD hPb hDb (r j u) (hbr j u)
        simp only [xt]; rw [hPe]; exact this
      have hv := vecSize_le_of_rep' xt _ hxrep
      calc vecSize xt ≤ n * (2 * (α + Z + K + 1) + 4) := hv
        _ ≤ Z * (12 * Z ^ 2 + 16 * Z + 12) := by
          apply Nat.mul_le_mul hnZ
          rw [hKdef]
          nlinarith

theorem solution :
    ∃ g : Polynomial ℕ, ∀ (n mP k : ℕ) (A' : Matrix (Fin mP) (Fin n) ℚ) (b' : Fin mP → ℚ)
      (r : Fin k → Fin n → ℚ) (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (i : Fin k),
      Bornology.IsBounded (polyhedron A' b') →
      LinearIndependent ℝ (fun j => toReal (r j)) →
      quadForm H (toReal (r i)) = 0 →
      (∃ x ∈ polyhedron A' b' + intCone ((fun j => toReal (r j)) '' {j | j ≠ i}),
          2 * (∑ u, ∑ v, x u * (H u v : ℝ) * toReal (r i) v) + ∑ u, (c u : ℝ) * toReal (r i) u
            < 0) →
      ∃ xt : Fin n → ℚ,
        toReal xt ∈ polyhedron A' b' + intCone ((fun j => toReal (r j)) '' {j | j ≠ i}) ∧
        2 * (∑ u, ∑ v, toReal xt u * (H u v : ℝ) * toReal (r i) v)
            + ∑ u, (c u : ℝ) * toReal (r i) u < 0 ∧
        vecSize xt ≤ g.eval (matSize A' + vecSize b' + ∑ j, vecSize (r j) + matSize H + vecSize c) :=
  claim1_core
