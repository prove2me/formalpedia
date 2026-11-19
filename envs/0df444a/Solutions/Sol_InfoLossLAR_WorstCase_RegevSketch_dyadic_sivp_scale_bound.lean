-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.dyadic_sivp_scale_bound
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-18T23:49:13.929064+00:00
-- url     : https://prove2.me/submissions/cf86aec1-e5d4-4c59-b513-cbefcb2ae2b9

import Definitions.Def_InfoLossLAR_RegevSketch_DGS
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_smoothing_le_lamN_log

set_option autoImplicit false
namespace InfoLossLAR.WorstCase.RegevSketch

private theorem inputModule_eq_sharpLattice {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (hdet : B.det ≠ 0) : inputModule B = IntegerBasis.inputLattice B hdet := by
  unfold inputModule IntegerBasis.inputLattice
  congr 2
  funext i
  simp [IntegerBasis.realBasis_apply, latVec, Matrix.mulVec_single]

/-- The published DGS threshold satisfies the required uniform estimate already with
C=128 and a single logarithm. No assumption of attainment of lamN is needed. -/
theorem dgsThreshold_scale_128 {n : ℕ} (hn : 1 ≤ n) (B : Matrix (Fin n) (Fin n) ℤ)
    (hdet : B.det ≠ 0) : 2 * Real.sqrt n * dgsThreshold B ≤
      (128 * (famq n : ℝ) * Real.logb 2 ((n : ℝ) + 2)^1) * lamN B := by
  have hs := smoothing_le_lamN_log B hdet (by omega)
  rw [← inputModule_eq_sharpLattice B hdet] at hs
  have hmin : 0 ≤ lamN B := by
    apply Real.sInf_nonneg
    rintro r ⟨v, _, _, h⟩
    exact (norm_nonneg (v ⟨0,by omega⟩)).trans (h ⟨0,by omega⟩)
  have hlog : 0 ≤ Real.logb 2 ((n : ℝ) + 2) :=
    Real.logb_nonneg (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hs' : RegevLWE.GaussConv.smoothingParam (inputModule B) (smoothingError n) ≤
      4 * Real.logb 2 ((n : ℝ) + 2) * lamN B := by
    simpa only [Real.logb, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hs
  have hns : (n : ℝ) / (famσ n : ℝ) ≤ 1 := by
    simp only [famσ, famL, Nat.cast_add, Nat.cast_ofNat]
    apply (div_le_one (by positivity)).mpr
    linarith
  have heq : 2 * Real.sqrt n * dgsThreshold B = (32 * (famq n : ℝ) * ((n : ℝ) / (famσ n : ℝ))) *
      RegevLWE.GaussConv.smoothingParam (inputModule B) (smoothingError n) := by
    unfold dgsThreshold
    have hsq := Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)
    simp only [div_eq_mul_inv]
    linear_combination 32 * (famq n : ℝ) * (famσ n : ℝ)⁻¹ *
      RegevLWE.GaussConv.smoothingParam (inputModule B) (smoothingError n) * hsq
  rw [heq, pow_one]
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left hs' (by positivity)
    _ ≤ (32 * (famq n : ℝ) * 1) * (4 * Real.logb 2 ((n : ℝ) + 2) * lamN B) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hns (by positivity)
    _ = _ := by ring

end InfoLossLAR.WorstCase.RegevSketch

namespace InfoLossLAR.WorstCase

private theorem memberFlatLength {α β : Type*} (f : α → List β) {a : α}
    {xs : List α} (ha : a ∈ xs) : (f a).length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    rcases List.mem_cons.mp ha with rfl | h
    · simp
    · have := ih h
      simp only [List.flatMap_cons, List.length_append]
      omega

private theorem memberEncLength {α : Type*} (f : α → List Bool) {a : α}
    {xs : List α} (h : a ∈ xs) : (f a).length ≤ (encL f xs).length := by
  simpa only [encL, List.length_append] using
    (memberFlatLength f h).trans (Nat.le_add_left _ _)

private theorem markedLength (xs : List Bool) : xs.length ≤
    (xs.flatMap (fun b => [true,b])).length := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    simp only [List.length_cons, List.flatMap_cons, List.length_append, List.length_nil]
    omega

theorem encodedEntry_le {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    |(B i j : ℝ)| ≤ (2 : ℝ) ^ (encMat encI B).length := by
  have hbit : (B i j).natAbs.size ≤ (encI (B i j)).length := by
    rw [← Nat.size_eq_bits_len]
    have h := markedLength (B i j).natAbs.bits
    simp only [encI, encB, List.length_cons, List.length_append, List.length_nil]
    omega
  have hrow : (encI (B i j)).length ≤ (encVec encI (B i)).length :=
    memberEncLength encI (List.mem_ofFn.mpr ⟨j,rfl⟩)
  have hmat : (encVec encI (B i)).length ≤ (encMat encI B).length :=
    memberEncLength (encVec encI) (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have hn := (Nat.size_le.mp (hbit.trans (hrow.trans hmat))).le
  have hr : ((B i j).natAbs : ℝ) ≤ (2 : ℝ) ^ (encMat encI B).length := by exact_mod_cast hn
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hr

end InfoLossLAR.WorstCase

namespace InfoLossLAR.WorstCase
open scoped BigOperators

private theorem height_column_family {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hd : B.det ≠ 0) :
    (∀ j, intVecE (B.col j) ∈ lattice B) ∧ LinearIndependent ℝ (fun j => intVecE (B.col j)) := by
  classical
  constructor
  · intro j
    refine ⟨Pi.single j 1, ?_⟩
    simp [latVec, intVecE, Matrix.mulVec_single]
  · let A : Matrix (Fin n) (Fin n) ℝ := B.map (fun x => (x : ℝ))
    have hA : A.det ≠ 0 := by
      change (B.map (fun x => (x : ℝ))).det ≠ 0
      rw [← Int.cast_det]
      exact_mod_cast hd
    let e := (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearEquiv
    exact (Matrix.linearIndependent_cols_of_det_ne_zero hA).map' e.toLinearMap e.ker

private theorem height_col_radius {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) {H : ℝ}
    (hH : 0 ≤ H) (hn : 1 ≤ n) (h : ∀ i j, |(B i j : ℝ)| ≤ H) (j : Fin n) :
    ‖intVecE (B.col j)‖ ≤ n * H := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (by positivity)]
  calc
    _ ≤ ∑ _i : Fin n, H ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      change ‖(B i j : ℝ)‖ ^ 2 ≤ H ^ 2
      rw [Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (h i j) 2
    _ = n * H ^ 2 := by simp
    _ ≤ _ := by
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) * (n - 1) by positivity) (sq_nonneg H)]

private theorem height_lattice_one {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ lattice B) (hne : v ≠ 0) : 1 ≤ ‖v‖ := by
  classical
  obtain ⟨z,rfl⟩ := hv
  have hex : ∃ i, (B.mulVec z) i ≠ 0 := by
    by_contra! hf
    apply hne
    ext i
    simp [latVec, hf]
  obtain ⟨i,hi⟩ := hex
  apply le_trans _ (PiLp.norm_apply_le (latVec B z) i)
  change 1 ≤ ‖((B.mulVec z i : ℤ) : ℝ)‖
  rw [Real.norm_eq_abs, ← Int.cast_abs]
  exact_mod_cast Int.one_le_abs hi

theorem one_le_lamN_encoded {n : ℕ} (hn : 1 ≤ n) (B : Matrix (Fin n) (Fin n) ℤ)
    (hd : B.det ≠ 0) : 1 ≤ lamN B := by
  obtain ⟨hm,hi⟩ := height_column_family B hd
  apply le_csInf
  · refine ⟨∑ j, ‖intVecE (B.col j)‖, _,hm,hi,?_⟩
    intro j
    exact Finset.single_le_sum (fun k _ => norm_nonneg (intVecE (B.col k))) (Finset.mem_univ j)
  · rintro r ⟨v,hm',hi',hr⟩
    let i : Fin n := ⟨0,by omega⟩
    exact (height_lattice_one B (hm' i) (hi'.ne_zero i)).trans (hr i)

private theorem height_linear_bound {n : ℕ} (hn : 1 ≤ n) (B : Matrix (Fin n) (Fin n) ℤ)
    (hd : B.det ≠ 0) (h : ∀ i j, |(B i j : ℝ)| ≤ (2:ℝ) ^ (encMat encI B).length) :
    lamN B ≤ (2:ℝ) ^ ((encMat encI B).length + n) := by
  obtain ⟨hm,hi⟩ := height_column_family B hd
  trans (n:ℝ) * (2:ℝ) ^ (encMat encI B).length
  · apply csInf_le
    · refine ⟨0, ?_⟩
      rintro r ⟨v,_,_,hr⟩
      exact (norm_nonneg _).trans (hr ⟨0,by omega⟩)
    · exact ⟨_,hm,hi,height_col_radius B (by positivity) hn h⟩
  · rw [pow_add, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact_mod_cast (Nat.lt_two_pow_self (n := n)).le

end InfoLossLAR.WorstCase
namespace InfoLossLAR.WorstCase

theorem lamN_le_encoded_linear {n : ℕ} (hn : 1 ≤ n) (B : Matrix (Fin n) (Fin n) ℤ)
    (hd : B.det ≠ 0) : lamN B ≤ (2:ℝ) ^ ((encMat encI B).length + n) :=
  height_linear_bound hn B hd (encodedEntry_le B)

theorem lamN_le_encoded_sq {n : ℕ} (hn : 1 ≤ n) (B : Matrix (Fin n) (Fin n) ℤ)
    (hd : B.det ≠ 0) : lamN B ≤ (2:ℝ) ^ (((encMat encI B).length + n + 2) ^ 2) := by
  apply (lamN_le_encoded_linear hn B hd).trans
  apply pow_le_pow_right₀ (by norm_num)
  nlinarith [Nat.zero_le (((encMat encI B).length + n) ^ 2)]

end InfoLossLAR.WorstCase

set_option autoImplicit false
set_option maxHeartbeats 800000
open QAlgorithms.Complexity
open scoped BigOperators Classical
namespace InfoLossLAR.WorstCase.RegevSketch
theorem famq_le_explicit_polynomial (lam : ℕ) :
    famq lam ≤ 2 ^ 17 * (lam + 2) ^ 64 := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul
    (2 ^ 16 * famL lam ^ 64) (by unfold famL; positivity)
  have hminimal : famq lam ≤ p :=
    Nat.find_min' (Nat.exists_infinite_primes (2 ^ 16 * famL lam ^ 64)) ⟨hlt.le, hp⟩
  calc
    famq lam ≤ p := hminimal
    _ ≤ 2 * (2 ^ 16 * famL lam ^ 64) := hle
    _ = 2 ^ 17 * (lam + 2) ^ 64 := by unfold famL; norm_num [← mul_assoc]

theorem security_le_famq (lam : ℕ) : lam ≤ famq lam := by
  have hspec := (Nat.find_spec (Nat.exists_infinite_primes (2 ^ 16 * famL lam ^ 64))).1
  have hpow : famL lam ≤ famL lam ^ 64 := le_self_pow (by unfold famL; omega) (by norm_num)
  have hfac : famL lam ^ 64 ≤ 2 ^ 16 * famL lam ^ 64 := by omega
  exact (by unfold famL; omega : lam ≤ famL lam).trans (hpow.trans (hfac.trans hspec))

private theorem absorb_budget (L c C k : ℕ) (hL : 2 ≤ L) :
    C+17+L*64+L*k+L^c ≤ L^(c+1+(C+82+k)) := by
  have h1 : 1 ≤ L^(c+1) := Nat.one_le_pow _ _ (by omega)
  have hl : L ≤ L^(c+1) := le_self_pow (by omega) (by omega)
  have hc : L^c ≤ L^(c+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hk : C+82+k ≤ L^(C+82+k) :=
    Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hL _)
  calc
    _ ≤ (C+82+k)*L^(c+1) := by nlinarith [Nat.mul_le_mul_left C h1, Nat.mul_le_mul_left k hl]
    _ ≤ _ := by rw [pow_add L (c+1) (C+82+k)]; simpa only [mul_comm] using Nat.mul_le_mul_right (L^(c+1)) hk

theorem dyadic_of_estimates (C k c : ℕ) (n : ℕ) (hn : 1 ≤ n)
    (B : Matrix (Fin n) (Fin n) ℤ)
    (hmin : 1 ≤ lamN B)
    (hmax : lamN B ≤ (2:ℝ)^(((encMat encI B).length+n+2)^c))
    (hth : 2 * Real.sqrt n * dgsThreshold B ≤
        ((C:ℝ)*(famq n:ℝ)*Real.logb 2 ((n:ℝ)+2)^k)*lamN B) :
    ∃ j : ℕ, j ≤ ((encMat encI B).length+n+2)^(c+1+(C+82+k)) ∧
      dgsThreshold B ≤ (2:ℝ)^j ∧ 2*Real.sqrt n*(2:ℝ)^j ≤
      (((2*C+2:ℕ):ℝ)*(famq n:ℝ)*Real.logb 2 ((n:ℝ)+2)^k)*lamN B := by
  classical
  let L := (encMat encI B).length+n+2
  have hL : 2 ≤ L := by dsimp [L]; omega
  have hnb : n+2 ≤ L := by dsimp [L]; omega
  have hr : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have hs : Real.sqrt n ≤ (n:ℝ) := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg n), mul_nonneg (sub_nonneg.mpr hr) (Real.sqrt_nonneg (n:ℝ))]
  have hqlo : (n:ℝ) ≤ famq n := by exact_mod_cast security_le_famq n
  have hlog1 : 1 ≤ Real.logb 2 ((n:ℝ)+2) := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) (by positivity)).mpr
    simp
  have hlog : Real.logb 2 ((n:ℝ)+2) ≤ L := by
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) (by positivity)).mpr
    rw [Real.rpow_natCast]; exact_mod_cast hnb.trans Nat.lt_two_pow_self.le
  have hbas : (n:ℝ)+2 ≤ (2:ℝ)^L := by exact_mod_cast hnb.trans Nat.lt_two_pow_self.le
  have hq : (famq n:ℝ) ≤ (2:ℝ)^(17+L*64) := by
    have h := famq_le_explicit_polynomial n
    calc
      _ ≤ (2:ℝ)^17*((n:ℝ)+2)^64 := by exact_mod_cast h
      _ ≤ (2:ℝ)^17*((2:ℝ)^L)^64 := by gcongr
      _ = _ := by rw [pow_add (2:ℝ) 17 (L*64), pow_mul]
  have hlogPow : Real.logb 2 ((n:ℝ)+2)^k ≤ (2:ℝ)^(L*k) := by
    rw [pow_mul]; gcongr
    exact hlog.trans (by exact_mod_cast (Nat.lt_two_pow_self (n:=L)).le)
  have hlognonneg := (zero_le_one.trans hlog1)
  have hC : (C:ℝ) ≤ 2^C := by exact_mod_cast (Nat.lt_two_pow_self (n:=C)).le
  let T := ((C:ℝ)*(famq n:ℝ)*Real.logb 2 ((n:ℝ)+2)^k)*lamN B
  have ht : dgsThreshold B ≤ T := by
    by_cases hd : 0 ≤ dgsThreshold B
    · exact le_trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hr) hd] : dgsThreshold B ≤ 2*Real.sqrt n*dgsThreshold B) hth
    · exact (le_of_not_ge hd).trans (by dsimp [T]; positivity)
  have ht' : T ≤ (2:ℝ)^(C+17+L*64+L*k+L^c) := by
    calc
      T ≤ 2^C * 2^(17+L*64) * 2^(L*k) * (2:ℝ)^(L^c) := by unfold T; gcongr
      _ = _ := by simp only [pow_add, mul_assoc]
  let N := C+17+L*64+L*k+L^c
  have he : ∃ j : ℕ, dgsThreshold B ≤ (2:ℝ)^j := ⟨N, ht.trans ht'⟩
  let j := Nat.find he
  have hj := Nat.find_spec he
  refine ⟨j, (Nat.find_min' he (m:=N) (ht.trans ht')).trans (absorb_budget L c C k hL), hj, ?_⟩
  have hlogk : 1 ≤ Real.logb 2 ((n:ℝ)+2)^k := one_le_pow₀ hlog1
  have hq0 : (0:ℝ) ≤ famq n := by positivity
  by_cases hz : j=0
  · simp only [hz, pow_zero, mul_one, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    calc
      2 * Real.sqrt n ≤ 2 * (famq n:ℝ) := by gcongr; exact hs.trans hqlo
      _ ≤ (2*(C:ℝ)+2) * (famq n:ℝ) * Real.logb 2 ((n:ℝ)+2)^k * lamN B := by
        calc
          _ = 2*(famq n:ℝ)*1*1 := by ring
          _ ≤ _ := by gcongr; linarith [show (0:ℝ) ≤ C by positivity]
  · have hjp : j-1 < j := by omega
    have hprev : (2:ℝ)^(j-1) < dgsThreshold B := lt_of_not_ge (Nat.find_min he hjp)
    have hpow : (2:ℝ)^j ≤ 2*dgsThreshold B := by
      conv_lhs => rw [show j=(j-1)+1 by omega,pow_succ];
      linarith
    calc
      _ ≤ 2 * Real.sqrt n * (2*dgsThreshold B) := by gcongr
      _ = 2 * (2 * Real.sqrt n * dgsThreshold B) := by ring
      _ ≤ 2*T := by gcongr
      _ ≤ _ := by
        dsimp [T]; push_cast
        rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
        gcongr; linarith
end InfoLossLAR.WorstCase.RegevSketch

namespace InfoLossLAR.WorstCase.RegevSketch

theorem _root_.solution :    ∃ C k d : ℕ, 1 ≤ C ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 →
        ∃ j : ℕ, j ≤ ((encMat encI B).length + n + 2)^d ∧
          dgsThreshold B ≤ (2 : ℝ)^j ∧
          2 * Real.sqrt n * (2 : ℝ)^j ≤
            ((C : ℝ) * (famq n : ℝ) * Real.logb 2 ((n : ℝ) + 2)^k) * lamN B  := by
  refine ⟨258, 1, 214, by decide, ?_⟩
  intro n hn B hd
  exact dyadic_of_estimates 128 1 2 n hn B (one_le_lamN_encoded hn B hd) (lamN_le_encoded_sq hn B hd) (dgsThreshold_scale_128 hn B hd)

end InfoLossLAR.WorstCase.RegevSketch
