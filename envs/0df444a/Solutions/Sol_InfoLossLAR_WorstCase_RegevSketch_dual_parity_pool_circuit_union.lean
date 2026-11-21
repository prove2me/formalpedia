-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.dual_parity_pool_circuit_union
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T06:13:32.766684+00:00
-- url     : https://prove2.me/submissions/ca8b3507-b400-4846-9b9f-753e28959238

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dual_parity_pool_circuit_pass_flags

set_option autoImplicit false
set_option maxHeartbeats 1000000
open QAlgorithms.Complexity
open scoped BigOperators Classical

open Matrix
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch

private theorem latVec_ne_zero_iff {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (z : Fin n → ℤ) : latVec B z ≠ 0 ↔ B.mulVec z ≠ 0 := by
  constructor
  · intro h hz
    apply h
    unfold latVec
    rw [hz]
    simp
    rfl
  · intro h hz
    apply h
    funext i
    have hi := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v.ofLp i) hz
    change ((B.mulVec z) i : ℝ) = 0 at hi
    exact_mod_cast hi

private theorem latVec_norm_sq_nat {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (z : Fin n → ℤ) :
    ‖latVec B z‖ ^ 2 = ((∑ a, ((B.mulVec z) a).natAbs ^ 2 : ℕ) : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq]
  push_cast
  apply Finset.sum_congr rfl
  intro a _
  change ‖((B.mulVec z) a : ℝ)‖ ^ 2 = (((B.mulVec z) a).natAbs : ℝ) ^ 2
  rw [Real.norm_eq_abs, sq_abs]
  simpa only [Int.cast_pow, Int.cast_natCast] using
    congrArg (fun t : ℤ => (t : ℝ)) (Int.natAbs_sq ((B.mulVec z) a)).symm

private theorem exists_short_odd_coeff {n : ℕ} (hn : 1 ≤ n)
    (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det ≠ 0)
    (δ : ℚ) (hδ : 0 < δ) (hyes : lam1 B ≤ δ) :
    ∃ z : Fin n → ℤ, ∃ i : Fin n, Odd (z i) ∧
      (∑ a, ((B.mulVec z) a : ℚ) ^ 2) ≤ δ ^ 2 := by
  let r (z : Fin n → ℤ) : ℕ := ∑ a, ((B.mulVec z) a).natAbs ^ 2
  have hex : ∃ k : ℕ, ∃ z : Fin n → ℤ, B.mulVec z ≠ 0 ∧ r z = k := by
    let i : Fin n := ⟨0, hn⟩
    let z : Fin n → ℤ := Pi.single i 1
    refine ⟨r z, z, ?_, rfl⟩
    intro h
    have hh := congrArg (fun v => B.adjugate.mulVec v) h
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_zero] at hh
    have hi := congrFun hh i
    simp [z, Pi.smul_apply, hdet] at hi
  obtain ⟨z, hz, hzr⟩ := Nat.find_spec hex
  have hmin (u : Fin n → ℤ) (hu : B.mulVec u ≠ 0) : r z ≤ r u := by
    rw [hzr]
    exact Nat.find_min' hex ⟨u, hu, rfl⟩
  have hnorm : lam1 B = ‖latVec B z‖ := by
    apply IsLeast.csInf_eq
    refine ⟨⟨latVec B z, ⟨z, rfl⟩, (latVec_ne_zero_iff B z).mpr hz, rfl⟩, ?_⟩
    rintro _ ⟨v, ⟨u, rfl⟩, hu, rfl⟩
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [latVec_norm_sq_nat, latVec_norm_sq_nat]
    exact_mod_cast hmin u ((latVec_ne_zero_iff B u).mp hu)
  have ho : ∃ i : Fin n, Odd (z i) := by
    by_contra hall
    push Not at hall
    have he (i : Fin n) : ∃ t : ℤ, z i = 2 * t :=
      even_iff_two_dvd.mp (Int.not_odd_iff_even.mp (hall i))
    choose u hu using he
    have hzu : z = (2 : ℤ) • u := funext hu
    have hmul : B.mulVec z = (2 : ℤ) • B.mulVec u := by
      rw [hzu, Matrix.mulVec_smul]
    have hnu : B.mulVec u ≠ 0 := by
      intro h
      exact hz (by rw [hmul, h, smul_zero])
    have hru : 0 < r u := by
      have hsq := latVec_norm_sq_nat B u
      have hp : 0 < ‖latVec B u‖ ^ 2 :=
        pow_pos (norm_pos_iff.mpr ((latVec_ne_zero_iff B u).mpr hnu)) _
      change ‖latVec B u‖ ^ 2 = (r u : ℝ) at hsq
      exact_mod_cast (hsq ▸ hp)
    have hrzu : r z = 4 * r u := by
      dsimp only [r]
      rw [hmul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      change (2 * (B.mulVec u) i).natAbs ^ 2 = 4 * ((B.mulVec u) i).natAbs ^ 2
      rw [Int.natAbs_mul, mul_pow]
      rfl
    have := hmin u hnu
    omega
  obtain ⟨i, hi⟩ := ho
  refine ⟨z, i, hi, ?_⟩
  rw [hnorm] at hyes
  have hsq := (sq_le_sq₀ (norm_nonneg (latVec B z)) (by exact_mod_cast hδ.le)).mpr hyes
  rw [EuclideanSpace.norm_sq_eq] at hsq
  change (∑ a, ‖((B.mulVec z) a : ℝ)‖ ^ 2) ≤ (δ : ℝ) ^ 2 at hsq
  simp only [Real.norm_eq_abs, sq_abs] at hsq
  exact_mod_cast hsq

private theorem parity_excludes_pool {n : ℕ} (hn : 1 ≤ n)
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (δ : ℚ) (hδ : 0 < δ)
    (z : Fin n → ℤ) (i : Fin n) (hodd : Odd (z i))
    (hs : (∑ a, ((B.mulVec z) a : ℚ)^2) ≤ δ^2) :
    let m := (n+1)^3
    let H : Matrix (Fin n) (Fin n) ℤ := fun a b => B a b * (if b = i then 2 else 1)
    let D := H.adjugate.transpose
    ∀ p : Fin m → Fin n → ℤ,
      ¬ (m ≤ 4 * (Finset.univ.filter (fun j => Odd (p j i))).card ∧
      ∀ x : Fin n → ℤ,
        64 * δ^2 * (∑ j, ((∑ a, x a * (D.mulVec (p j)) a : ℤ) : ℚ)^2) ≤
          (m : ℚ) * (H.det : ℚ)^2 * (∑ a, (x a : ℚ)^2)) := by
  intro m H D p he
  let x := B.mulVec z
  let w := (2 : ℤ) • z - Pi.single i (z i)
  let c : Fin n → ℤ := fun a => if a = i then 2 else 1
  have hH : H = B * Matrix.diagonal c := by
    ext a b
    simp [H, c, Matrix.mul_diagonal]
  have hd : H.det ≠ 0 := by
    rw [hH, Matrix.det_mul, Matrix.det_diagonal]
    simp [c, hB]
  have hHd : H.mulVec w = (2 : ℤ) • x := by
    rw [hH, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul]
    congr 1
    ext a
    rw [Matrix.mulVec_diagonal]
    by_cases ha : a = i
    · subst a
      simp [c,w,Pi.smul_apply, zsmul_eq_mul]
      ring
    · simp [c,w,ha,Pi.smul_apply, zsmul_eq_mul]
  have hpair (q : Fin n → ℤ) : 2 * (x ⬝ᵥ D.mulVec q) = H.det * (w ⬝ᵥ q) := by
    calc
      _ = ((2 : ℤ) • x) ⬝ᵥ D.mulVec q := by rw [smul_dotProduct]; rfl
      _ = w ⬝ᵥ H.transpose.mulVec (D.mulVec q) := by
        rw [← hHd, dotProduct_comm (H.mulVec w)]
        exact (Matrix.dotProduct_transpose_mulVec H w (D.mulVec q)).symm
      _ = H.det * (w ⬝ᵥ q) := by
        rw [Matrix.mulVec_mulVec]
        have hmat : H.transpose * D = H.det • 1 := by
          rw [show D = H.adjugate.transpose by rfl, ← Matrix.transpose_mul, Matrix.adjugate_mul,
            Matrix.transpose_smul, Matrix.transpose_one]
        rw [hmat, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
        exact zsmul_eq_mul _ _
  have hpairOdd (q : Fin n → ℤ) (hq : Odd (q i)) : Odd (w ⬝ᵥ q) := by
    rw [show w = (2 : ℤ) • z - Pi.single i (z i) by rfl, sub_dotProduct, smul_dotProduct,
      single_dotProduct, zsmul_eq_mul]
    exact (even_two_mul _).sub_odd (hodd.mul hq)
  let S := Finset.univ.filter (fun j : Fin m => Odd (p j i))
  let f (j : Fin m) : ℚ := ((x ⬝ᵥ D.mulVec (p j) : ℤ) : ℚ)^2
  let d := (H.det : ℚ)
  have hb (j : Fin m) (hj : j ∈ S) : d^2 ≤ 4 * f j := by
    have hoddj : Odd (p j i) := (Finset.mem_filter.mp hj).2
    have hwo := Int.odd_iff.mp (hpairOdd _ hoddj)
    have hnz : w ⬝ᵥ p j ≠ 0 := by omega
    have hsq : 1 ≤ (w ⬝ᵥ p j)^2 := by
      rcases (show w ⬝ᵥ p j ≤ -1 ∨ 1 ≤ w ⬝ᵥ p j by omega) with h | h
      · nlinarith
      · nlinarith
    have hsq' : (1 : ℚ) ≤ ((w ⬝ᵥ p j : ℤ) : ℚ)^2 := by exact_mod_cast hsq
    have hp : 2 * ((x ⬝ᵥ D.mulVec (p j) : ℤ) : ℚ) = d * ((w ⬝ᵥ p j : ℤ) : ℚ) := by
      dsimp [d]
      exact_mod_cast hpair (p j)
    calc
      d^2 = d^2 * 1 := by ring
      _ ≤ d^2 * ((w ⬝ᵥ p j : ℤ) : ℚ)^2 := mul_le_mul_of_nonneg_left hsq' (sq_nonneg _)
      _ = 4 * f j := by rw [← mul_pow, ← hp]; dsimp [f]; ring
  have hc : (m : ℚ) ≤ 4 * (S.card : ℚ) := by exact_mod_cast he.1
  have hsum : (m : ℚ) * d^2 ≤ 16 * ∑ j, f j := by
    calc
      _ ≤ (4 * (S.card : ℚ)) * d^2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
      _ = 4 * ∑ _j ∈ S, d^2 := by simp [mul_assoc]
      _ ≤ 4 * ∑ j ∈ S, 4 * f j := by gcongr; exact hb _ ‹_›
      _ = 16 * ∑ j ∈ S, f j := by rw [← Finset.mul_sum]; ring
      _ ≤ 16 * ∑ j, f j := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  have hupper : 64 * δ^2 * (∑ j, f j) ≤ (m : ℚ) * d^2 * δ^2 := by
    calc
      _ ≤ (m : ℚ) * d^2 * ∑ a, (x a : ℚ)^2 := he.2 x
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
  have hlower : 4 * ((m : ℚ) * d^2 * δ^2) ≤ 64 * δ^2 * (∑ j, f j) := by
    have hv := mul_le_mul_of_nonneg_right hsum (show 0 ≤ 4 * δ^2 by positivity)
    nlinarith
  have hm : (0 : ℚ) < m := by dsimp [m]; positivity
  have hdn : d ≠ 0 := by dsimp [d]; exact_mod_cast hd
  have hpos : 0 < (m : ℚ) * d^2 * δ^2 := by positivity
  linarith

private theorem flag_one_sub_mass {n : ℕ} (w : (Fin n → Bool) → ℝ)
    (hm : ∑ t, w t = 1) (i : Fin n) :
    (∑ t, if t i = false then w t else 0) =
      1 - ∑ t, if t i then w t else 0 := by
  apply eq_sub_of_add_eq
  rw [← Finset.sum_add_distrib, ← hm]
  apply Finset.sum_congr rfl
  intro t _
  cases t i <;> simp

private theorem flag_union_bound {n : ℕ} (w : (Fin n → Bool) → ℝ)
    (hw : ∀ t, 0 ≤ w t) (hm : ∑ t, w t = 1) :
    (∑ t, if ∃ i, t i = false then w t else 0) ≤
      ∑ i : Fin n, (1 - ∑ t, if t i then w t else 0) := by
  simp_rw [← flag_one_sub_mass w hm]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun t _ => ?_
  have hnonneg (i : Fin n) : 0 ≤ (if t i = false then w t else 0) := by
    split_ifs <;> simp [hw t]
  by_cases h : ∃ i, t i = false
  · obtain ⟨i, hi⟩ := h
    rw [if_pos ⟨i, hi⟩]
    simpa only [if_pos hi] using Finset.single_le_sum (fun a _ => hnonneg a) (Finset.mem_univ i)
  · rw [if_neg h]
    exact Finset.sum_nonneg fun i _ => hnonneg i

private theorem flag_union_mass_one {n : ℕ} (w : (Fin n → Bool) → ℝ)
    (hw : ∀ t, 0 ≤ w t) (hm : ∑ t, w t = 1) (i : Fin n)
    (hz : (∑ t, if t i then w t else 0) = 0) :
    (∑ t, if ∃ j, t j = false then w t else 0) = 1 := by
  apply le_antisymm
  · rw [← hm]
    exact Finset.sum_le_sum fun t _ => by split_ifs <;> simp [hw t]
  · have hi := flag_one_sub_mass w hm i
    rw [hz, sub_zero] at hi
    rw [← hi]
    refine Finset.sum_le_sum fun t _ => ?_
    by_cases h : t i = false
    · simp [h, show ∃ j, t j = false from ⟨i, h⟩]
    · simp only [if_neg h]
      split_ifs <;> simp [hw t]

private theorem outputProb_decodedPool_impossible
    (G : MFamily) (word : Str) {n m : ℕ} (E : (Fin m → Fin n → ℤ) → Prop)
    (h : ∀ pool, ¬ E pool) : outputProb G word (decodedPoolEvent E) = 0 := by
  have hE (out : Str) : ¬ decodedPoolEvent E out := by
    rintro ⟨pool, _, he⟩
    exact h pool he
  simp only [outputProb, hE, if_false, Finset.sum_const_zero]

theorem solution :
    ∀ G : MFamily, IsMQPT G → ∃ A : Family, IsQPT A ∧
    ∀ n : ℕ, 1 ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 → ∀ δ : ℚ, 0 < δ →
    let m := (n+1)^3
    let H (i : Fin n) : Matrix (Fin n) (Fin n) ℤ := fun a b => B a b * (if b = i then 2 else 1)
    let D (i : Fin n) := (H i).adjugate.transpose
    let r (i : Fin n) : ℚ := (Int.natAbs (H i).det : ℚ) / (100*δ)
    let E (i : Fin n) (p : Fin m → Fin n → ℤ) : Prop :=
      m ≤ 4 * (Finset.univ.filter (fun j => Odd (p j i))).card ∧
      ∀ x : Fin n → ℤ,
        64 * δ^2 * (∑ j, ((∑ a, x a * ((D i).mulVec (p j)) a : ℤ) : ℚ)^2) ≤
          (m : ℚ) * ((H i).det : ℚ)^2 * (∑ a, (x a : ℚ)^2)
    (lam1 B ≤ δ → acceptProb A (encGapInstance B δ) = 1) ∧
    acceptProb A (encGapInstance B δ) ≤ ∑ i : Fin n,
      (1-outputProb G (dgsInput (D i) (r i) m (16*(n+1))) (decodedPoolEvent (E i))) := by
  intro G hG
  obtain ⟨A, hA, hcompiler⟩ := dual_parity_pool_circuit_pass_flags G hG
  refine ⟨A, hA, ?_⟩
  intro n hn B hB δ hδ m H D r E
  obtain ⟨w, hnonneg, hmass, hmargin, haccept⟩ := hcompiler n hn B hB δ hδ
  change (∀ i : Fin n, (∑ t, if t i then w t else 0) =
    outputProb G (dgsInput (D i) (r i) m (16 * (n + 1))) (decodedPoolEvent (E i))) at hmargin
  rw [haccept]
  constructor
  · intro hyes
    obtain ⟨z, i, hi, hshort⟩ := exists_short_odd_coeff hn B hB δ hδ hyes
    have hbad : ∀ p, ¬ E i p := parity_excludes_pool hn B hB δ hδ z i hi hshort
    have hz := outputProb_decodedPool_impossible G
      (dgsInput (D i) (r i) m (16 * (n + 1))) (E i) hbad
    exact flag_union_mass_one w hnonneg hmass i ((hmargin i).trans hz)
  · simpa only [hmargin] using flag_union_bound w hnonneg hmass
