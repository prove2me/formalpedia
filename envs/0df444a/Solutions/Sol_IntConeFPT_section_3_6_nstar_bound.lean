-- Prove2me | solution 1 for IntConeFPT.section_3_6_nstar_bound
-- status  : ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-24T11:16:46.976151+00:00
-- url     : https://prove2.me/submissions/9a2cd194-5b12-4538-ba7c-337eb0d4417e

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem
import Definitions.Def_IntConeFPT_Residue
import Definitions.Def_IntConeFPT_Formulation
import Definitions.Def_IntConeFPT_Homogenized

set_option autoImplicit false

open OnlineCRS.Combine
open RobustToDynamics (encMat)

namespace IntConeFPT.Section36Proof

lemma clearRat_cast_real (q : ℕ) (r : ℚ) (hq : r.den ∣ q) :
    ((clearRat q r : ℤ) : ℝ) = (q : ℝ) * (r : ℝ) := by
  obtain ⟨m, hm⟩ := hq
  have hd : 0 < r.den := r.den_pos
  have hdiv : q / r.den = m := by rw [hm, Nat.mul_div_cancel_left _ hd]
  unfold clearRat
  rw [hdiv, hm, Rat.cast_def]
  push_cast
  have hdR : (r.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  field_simp

lemma mul_nonpos_iff_of_pos {a b : ℝ} (ha : 0 < a) : a * b ≤ 0 ↔ b ≤ 0 :=
  ⟨fun h => by nlinarith, fun h => mul_nonpos_of_nonneg_of_nonpos ha.le h⟩

lemma rowDenomQ_pos (I : Instance) (i : Fin I.mQ) : 0 < rowDenomQ I i := by
  unfold rowDenomQ
  exact Nat.mul_pos
    (Nat.mul_pos (Finset.prod_pos fun _ _ => Rat.den_pos _)
      (Finset.prod_pos fun _ _ => Rat.den_pos _))
    (Rat.den_pos _)

lemma rowDenomA_pos (I : Instance) (i : Fin I.mA) : 0 < rowDenomA I i := by
  unfold rowDenomA
  refine Nat.mul_pos (Finset.prod_pos fun _ _ => ?_) (Rat.den_pos _)
  exact Nat.mul_pos
    (Nat.mul_pos (Finset.prod_pos fun _ _ => Rat.den_pos _)
      (Finset.prod_pos fun _ _ => Rat.den_pos _))
    (Rat.den_pos _)

lemma rowDenomLoc_pos (I : Instance) (t : Fin I.τ) (i : Fin (I.m t)) :
    0 < rowDenomLoc I t i := by
  unfold rowDenomLoc
  exact Nat.mul_pos
    (Nat.mul_pos (Finset.prod_pos fun _ _ => Rat.den_pos _)
      (Finset.prod_pos fun _ _ => Rat.den_pos _))
    (Rat.den_pos _)

lemma dvd_rowDenomQ_Y (I : Instance) (i : Fin I.mQ) (j : Fin I.d) :
    (I.QY i j).den ∣ rowDenomQ I i :=
  dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)) _) _

lemma dvd_rowDenomQ_V (I : Instance) (i : Fin I.mQ) (j : Fin I.k) :
    (I.QV i j).den ∣ rowDenomQ I i :=
  dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)) _) _

lemma dvd_rowDenomQ_c (I : Instance) (i : Fin I.mQ) :
    (I.cQ i).den ∣ rowDenomQ I i :=
  dvd_mul_left _ _

lemma dvd_rowDenomA_Y (I : Instance) (t : Fin I.τ) (i : Fin I.mA) (j : Fin I.d) :
    (I.AY t i j).den ∣ rowDenomA I i := by
  unfold rowDenomA
  refine dvd_mul_of_dvd_left ?_ _
  refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ t))
  exact dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)) _) _

lemma dvd_rowDenomA_V (I : Instance) (t : Fin I.τ) (i : Fin I.mA) (j : Fin I.k) :
    (I.AV t i j).den ∣ rowDenomA I i := by
  unfold rowDenomA
  refine dvd_mul_of_dvd_left ?_ _
  refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ t))
  exact dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)) _) _

lemma dvd_rowDenomA_N (I : Instance) (i : Fin I.mA) (t : Fin I.τ) :
    (I.AN i t).den ∣ rowDenomA I i := by
  unfold rowDenomA
  refine dvd_mul_of_dvd_left ?_ _
  refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ t))
  exact dvd_mul_left _ _

lemma dvd_rowDenomA_c (I : Instance) (i : Fin I.mA) :
    (I.cA i).den ∣ rowDenomA I i :=
  dvd_mul_left _ _

lemma dvd_rowDenomLoc_A (I : Instance) (t : Fin I.τ) (i : Fin (I.m t)) (j : Fin I.d) :
    (I.Aloc t i j).den ∣ rowDenomLoc I t i :=
  dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)) _) _

lemma dvd_rowDenomLoc_B (I : Instance) (t : Fin I.τ) (i : Fin (I.m t)) (j : Fin I.k) :
    (I.Bloc t i j).den ∣ rowDenomLoc I t i :=
  dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)) _) _

lemma dvd_rowDenomLoc_b (I : Instance) (t : Fin I.τ) (i : Fin (I.m t)) :
    (I.bloc t i).den ∣ rowDenomLoc I t i :=
  dvd_mul_left _ _

lemma aggLHS_castAdd (I : Instance) (Y : Fin I.τ → Pt I.d I.k) (i : Fin I.mQ) :
    (clearIntDesc I).aggLHS Y (Fin.castAdd I.mA i) =
      (rowDenomQ I i : ℝ) *
        ((∑ j, (I.QY i j : ℝ) * (∑ t, ((Y t).1, (Y t).2.1)).1 j) +
          (∑ j, (I.QV i j : ℝ) * (∑ t, ((Y t).1, (Y t).2.1)).2 j)) := by
  unfold IntDesc.aggLHS clearIntDesc
  simp only [Matrix.of_apply, Fin.addCases_left, Int.cast_zero, zero_mul, add_zero,
    Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Finset.sum_add_distrib, mul_add,
    Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => ?_
    rw [clearRat_cast_real _ _ (dvd_rowDenomQ_Y I i j)]
    ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => ?_
    rw [clearRat_cast_real _ _ (dvd_rowDenomQ_V I i j)]
    ring

lemma aggLHS_natAdd (I : Instance) (Y : Fin I.τ → Pt I.d I.k) (i : Fin I.mA) :
    (clearIntDesc I).aggLHS Y (Fin.natAdd I.mQ i) =
      (rowDenomA I i : ℝ) *
        ∑ t, ((∑ j, (I.AY t i j : ℝ) * (Y t).1 j) +
          (∑ j, (I.AV t i j : ℝ) * (Y t).2.1 j) +
          (I.AN i t : ℝ) * (Y t).2.2) := by
  unfold IntDesc.aggLHS clearIntDesc
  simp only [Matrix.of_apply, Fin.addCases_right]
  have hY (t : Fin I.τ) (j : Fin I.d) : ((clearRat (rowDenomA I i) (I.AY t i j) : ℤ) : ℝ) =
      (rowDenomA I i : ℝ) * (I.AY t i j : ℝ) :=
    clearRat_cast_real _ _ (dvd_rowDenomA_Y I t i j)
  have hV (t : Fin I.τ) (j : Fin I.k) : ((clearRat (rowDenomA I i) (I.AV t i j) : ℤ) : ℝ) =
      (rowDenomA I i : ℝ) * (I.AV t i j : ℝ) :=
    clearRat_cast_real _ _ (dvd_rowDenomA_V I t i j)
  have hN (t : Fin I.τ) : ((clearRat (rowDenomA I i) (I.AN i t) : ℤ) : ℝ) =
      (rowDenomA I i : ℝ) * (I.AN i t : ℝ) :=
    clearRat_cast_real _ _ (dvd_rowDenomA_N I i t)
  simp_rw [hY, hV, hN, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [mul_add, Finset.mul_sum, mul_assoc]

lemma clearIntDesc_describes (I : Instance) : (clearIntDesc I).Describes := by
  refine ⟨fun Y => ?_, fun t p => ?_⟩
  · change (∀ i : Fin (I.mQ + I.mA), (clearIntDesc I).aggLHS Y i ≤ ((clearIntDesc I).cW i : ℝ)) ↔ _
    rw [Fin.forall_fin_add]
    unfold Instance.Q Instance.A
    refine and_congr (forall_congr' fun i => ?_) (forall_congr' fun i => ?_)
    · rw [aggLHS_castAdd]
      simp only [clearIntDesc, Fin.addCases_left, clearRat_cast_real _ _ (dvd_rowDenomQ_c I i)]
      exact mul_le_mul_iff_of_pos_left (Nat.cast_pos.mpr (rowDenomQ_pos I i))
    · rw [aggLHS_natAdd]
      simp only [clearIntDesc, Fin.addCases_right, clearRat_cast_real _ _ (dvd_rowDenomA_c I i)]
      exact mul_le_mul_iff_of_pos_left (Nat.cast_pos.mpr (rowDenomA_pos I i))
  · unfold Instance.P
    refine forall_congr' fun i => ?_
    dsimp only [clearIntDesc, Matrix.of_apply]
    have hLHS :
        (∑ j, ((clearRat (rowDenomLoc I t i) (I.Aloc t i j) : ℤ) : ℝ) * p.1 j) +
          (∑ j, ((clearRat (rowDenomLoc I t i) (I.Bloc t i j) : ℤ) : ℝ) * p.2 j) =
        (rowDenomLoc I t i : ℝ) *
          ((∑ j, (I.Aloc t i j : ℝ) * p.1 j) + (∑ j, (I.Bloc t i j : ℝ) * p.2 j)) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [clearRat_cast_real _ _ (dvd_rowDenomLoc_A I t i j), mul_assoc]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [clearRat_cast_real _ _ (dvd_rowDenomLoc_B I t i j), mul_assoc]
    rw [hLHS, clearRat_cast_real _ _ (dvd_rowDenomLoc_b I t i)]
    exact mul_le_mul_iff_of_pos_left (Nat.cast_pos.mpr (rowDenomLoc_pos I t i))

lemma clearIntDesc_hom_iff (I : Instance) (Y : Fin I.τ → Pt I.d I.k) :
    (∀ i, (clearIntDesc I).aggLHS Y i ≤ 0) ↔
      ((∑ t, ((Y t).1, (Y t).2.1)) ∈ I.Qhat ∧ Y ∈ I.Ahat) := by
  change (∀ i : Fin (I.mQ + I.mA), (clearIntDesc I).aggLHS Y i ≤ 0) ↔ _
  rw [Fin.forall_fin_add]
  unfold Instance.Qhat Instance.Ahat
  refine and_congr (forall_congr' fun i => ?_) (forall_congr' fun i => ?_)
  · rw [aggLHS_castAdd]
    exact mul_nonpos_iff_of_pos (Nat.cast_pos.mpr (rowDenomQ_pos I i))
  · rw [aggLHS_natAdd]
    exact mul_nonpos_iff_of_pos (Nat.cast_pos.mpr (rowDenomA_pos I i))

lemma one_le_coeffBoundU (I : Instance) (M : ℕ) : 1 ≤ coeffBoundU I M := by
  unfold coeffBoundU
  exact Nat.mul_pos (Nat.succ_pos M) (by omega)

lemma natAbs_le_triple_sum {a b c : ℕ} (f : Fin a → Fin b → Fin c → ℤ)
    (i : Fin a) (j : Fin b) (k : Fin c) :
    (f i j k).natAbs ≤ ∑ i', ∑ j', ∑ k', (f i' j' k').natAbs := by
  have h1 := Finset.single_le_sum (f := fun k' => (f i j k').natAbs)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have h2 := Finset.single_le_sum (f := fun j' => ∑ k', (f i j' k').natAbs)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have h3 := Finset.single_le_sum (f := fun i' => ∑ j', ∑ k', (f i' j' k').natAbs)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact le_trans h1 (le_trans h2 h3)

lemma row_le_triple_sum {a b c : ℕ} (f : Fin a → Fin b → Fin c → ℤ)
    (i : Fin a) (j : Fin b) :
    (∑ k, (f i j k).natAbs) ≤ ∑ i', ∑ j', ∑ k', (f i' j' k').natAbs := by
  have h2 := Finset.single_le_sum (f := fun j' => ∑ k', (f i j' k').natAbs)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have h3 := Finset.single_le_sum (f := fun i' => ∑ j', ∑ k', (f i' j' k').natAbs)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact le_trans h2 h3

lemma natAbs_le_double_sum {a b : ℕ} (f : Fin a → Fin b → ℤ) (i : Fin a) (j : Fin b) :
    (f i j).natAbs ≤ ∑ i', ∑ j', (f i' j').natAbs := by
  have h1 := Finset.single_le_sum (f := fun j' => (f i j').natAbs)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have h2 := Finset.single_le_sum (f := fun i' => ∑ j', (f i' j').natAbs)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact le_trans h1 h2

lemma clearIntDesc_boundedBy (I : Instance) (M : ℕ) :
    (clearIntDesc I).BoundedBy M (coeffBoundU I M) := by
  set D := clearIntDesc I
  set S_all : ℕ := 1 +
    (∑ t, ∑ i, ∑ j, (D.WY t i j).natAbs) +
    (∑ t, ∑ i, ∑ j, (D.WV t i j).natAbs) +
    (∑ i, ∑ t, (D.WN i t).natAbs) +
    (∑ i, (D.cW i).natAbs) +
    (∑ t, ∑ i, ∑ j, (D.LA t i j).natAbs) +
    (∑ t, ∑ i, ∑ j, (D.LB t i j).natAbs) +
    (∑ t, ∑ i, (D.Lb t i).natAbs)
  have hU_eq : coeffBoundU I M = (M + 1) * S_all := rfl
  have entry_le : ∀ {z : ℤ}, z.natAbs ≤ S_all → |z| ≤ (coeffBoundU I M : ℤ) := by
    intro z hz
    rw [Int.abs_eq_natAbs, hU_eq]
    exact_mod_cast le_trans hz (Nat.le_mul_of_pos_left _ (Nat.succ_pos M))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t i j
    exact entry_le (by have := natAbs_le_triple_sum D.WY t i j; omega)
  · intro t i j
    exact entry_le (by have := natAbs_le_triple_sum D.WV t i j; omega)
  · intro i t
    exact entry_le (by have := natAbs_le_double_sum D.WN i t; omega)
  · intro i
    exact entry_le (by
      have := Finset.single_le_sum (f := fun i' => (D.cW i').natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega)
  · intro t i j
    exact entry_le (by
      have h1 := Finset.single_le_sum (f := fun j' => (D.LA t i j').natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have h2 := Finset.single_le_sum (f := fun i' => ∑ j', (D.LA t i' j').natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have h3 := Finset.single_le_sum (f := fun t' => ∑ i', ∑ j', (D.LA t' i' j').natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
      omega)
  · intro t i j
    exact entry_le (by
      have h1 := Finset.single_le_sum (f := fun j' => (D.LB t i j').natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have h2 := Finset.single_le_sum (f := fun i' => ∑ j', (D.LB t i' j').natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have h3 := Finset.single_le_sum (f := fun t' => ∑ i', ∑ j', (D.LB t' i' j').natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
      omega)
  · intro t i
    exact entry_le (by
      have h1 := Finset.single_le_sum (f := fun i' => (D.Lb t i').natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have h2 := Finset.single_le_sum (f := fun t' => ∑ i', (D.Lb t' i').natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
      omega)
  · intro t i x hx
    have hsum : |∑ j, D.LA t i j * x j| ≤ (∑ j, ((D.LA t i j).natAbs : ℤ)) * (M : ℤ) := by
      calc |∑ j, D.LA t i j * x j|
        _ ≤ ∑ j, |D.LA t i j * x j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, |D.LA t i j| * |x j| := by simp_rw [abs_mul]
        _ ≤ ∑ j, ((D.LA t i j).natAbs : ℤ) * (M : ℤ) := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [Int.abs_eq_natAbs]
            exact mul_le_mul_of_nonneg_left (hx j) (by positivity)
        _ = (∑ j, ((D.LA t i j).natAbs : ℤ)) * (M : ℤ) := by rw [Finset.sum_mul]
    have hb_le : (D.Lb t i).natAbs + ∑ j, (D.LA t i j).natAbs ≤ S_all := by
      have h1 := Finset.single_le_sum (f := fun i' => (D.Lb t i').natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have h2 := Finset.single_le_sum (f := fun t' => ∑ i', (D.Lb t' i').natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
      have h3 := Finset.single_le_sum (f := fun i' => ∑ j', (D.LA t i' j').natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have h4 := Finset.single_le_sum (f := fun t' => ∑ i', ∑ j', (D.LA t' i' j').natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
      omega
    have htri : |D.Lb t i - ∑ j, D.LA t i j * x j| ≤
        ((D.Lb t i).natAbs : ℤ) + |∑ j, D.LA t i j * x j| := by
      simpa only [← Int.abs_eq_natAbs] using abs_sub (D.Lb t i) (∑ j, D.LA t i j * x j)
    have hb_int : ((D.Lb t i).natAbs : ℤ) + ∑ j, ((D.LA t i j).natAbs : ℤ) ≤ (S_all : ℤ) := by
      exact_mod_cast hb_le
    have hU_int : (coeffBoundU I M : ℤ) = ((M : ℤ) + 1) * (S_all : ℤ) := by
      rw [hU_eq]; push_cast; rfl
    have hLA_nn : (0 : ℤ) ≤ ∑ j, ((D.LA t i j).natAbs : ℤ) := by positivity
    have hLb_nn : (0 : ℤ) ≤ ((D.Lb t i).natAbs : ℤ) := by positivity
    have hM_nn : (0 : ℤ) ≤ (M : ℤ) := by positivity
    nlinarith
  · intro t i x hx
    have hsum : |∑ j, D.WY t i j * x j| ≤ (∑ j, ((D.WY t i j).natAbs : ℤ)) * (M : ℤ) := by
      calc |∑ j, D.WY t i j * x j|
        _ ≤ ∑ j, |D.WY t i j * x j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, |D.WY t i j| * |x j| := by simp_rw [abs_mul]
        _ ≤ ∑ j, ((D.WY t i j).natAbs : ℤ) * (M : ℤ) := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [Int.abs_eq_natAbs]
            exact mul_le_mul_of_nonneg_left (hx j) (by positivity)
        _ = (∑ j, ((D.WY t i j).natAbs : ℤ)) * (M : ℤ) := by rw [Finset.sum_mul]
    have hb_le : (∑ j, (D.WY t i j).natAbs) + (D.WN i t).natAbs ≤ S_all := by
      have h1 := row_le_triple_sum D.WY t i
      have h2 := natAbs_le_double_sum D.WN i t
      omega
    have htri : |(∑ j, D.WY t i j * x j) + D.WN i t| ≤
        |∑ j, D.WY t i j * x j| + ((D.WN i t).natAbs : ℤ) := by
      simpa only [← Int.abs_eq_natAbs] using abs_add_le (∑ j, D.WY t i j * x j) (D.WN i t)
    have hb_int : (∑ j, ((D.WY t i j).natAbs : ℤ)) + ((D.WN i t).natAbs : ℤ) ≤ (S_all : ℤ) := by
      exact_mod_cast hb_le
    have hU_int : (coeffBoundU I M : ℤ) = ((M : ℤ) + 1) * (S_all : ℤ) := by
      rw [hU_eq]; push_cast; rfl
    have hWY_nn : (0 : ℤ) ≤ ∑ j, ((D.WY t i j).natAbs : ℤ) := by positivity
    have hWN_nn : (0 : ℤ) ≤ ((D.WN i t).natAbs : ℤ) := by positivity
    have hM_nn : (0 : ℤ) ≤ (M : ℤ) := by positivity
    nlinarith

lemma encodePosNum_lt_two_pow (p : PosNum) : (p : ℕ) < 2 ^ (Computability.encodePosNum p).length := by
  induction p with
  | one => decide
  | bit0 p ih =>
    simp only [Computability.encodePosNum, List.length_cons, PosNum.cast_bit0]
    omega
  | bit1 p ih =>
    simp only [Computability.encodePosNum, List.length_cons, PosNum.cast_bit1]
    omega

lemma nat_lt_two_pow_encNat_len (n : ℕ) : n < 2 ^ (encNat n).length := by
  unfold encNat Computability.encodeNat
  rw [List.length_map]
  cases h : (n : Num) with
  | zero =>
    have hn : n = 0 := by
      have := congr_arg ((↑) : Num → ℕ) h
      simpa using this
    subst hn
    decide
  | pos p =>
    have hn : n = (p : ℕ) := by
      have := congr_arg ((↑) : Num → ℕ) h
      simpa using this
    rw [hn]
    exact encodePosNum_lt_two_pow p

lemma encodePosNum_len_le_of_lt (p : PosNum) {b : ℕ} (h : (p : ℕ) < 2 ^ b) :
    (Computability.encodePosNum p).length ≤ b := by
  induction p generalizing b with
  | one =>
    cases b with
    | zero => norm_num at h
    | succ b => simp [Computability.encodePosNum]
  | bit0 p ih =>
    cases b with
    | zero =>
      have hp : 0 < (p : ℕ) := PosNum.cast_pos p
      simp [PosNum.cast_bit0] at h
      omega
    | succ b =>
      simp only [Computability.encodePosNum, List.length_cons]
      have hp : (p : ℕ) < 2 ^ b := by
        simp [PosNum.cast_bit0, pow_succ] at h
        omega
      exact Nat.succ_le_succ (ih hp)
  | bit1 p ih =>
    cases b with
    | zero =>
      simp [PosNum.cast_bit1] at h
    | succ b =>
      simp only [Computability.encodePosNum, List.length_cons]
      have hp : (p : ℕ) < 2 ^ b := by
        simp [PosNum.cast_bit1, pow_succ] at h
        omega
      exact Nat.succ_le_succ (ih hp)

lemma encNat_len_le_of_lt_two_pow {n b : ℕ} (h : n < 2 ^ b) : (encNat n).length ≤ b := by
  unfold encNat Computability.encodeNat
  rw [List.length_map]
  cases hn : (n : Num) with
  | zero => simp [Computability.encodeNum]
  | pos p =>
    have hp : (p : ℕ) = n := by
      have := congr_arg ((↑) : Num → ℕ) hn
      simpa using this.symm
    rw [← hp] at h
    exact encodePosNum_len_le_of_lt p h

lemma one_le_encNat_pos {n : ℕ} (hn : 1 ≤ n) : 1 ≤ (encNat n).length := by
  by_contra hlt
  have h0 : (encNat n).length = 0 := by omega
  have := nat_lt_two_pow_encNat_len n
  rw [h0] at this
  omega

lemma encRat_zero_len_le (q : ℚ) : (encRat 0).length ≤ (encRat q).length := by
  have h0 : (encRat 0).length = 3 := by decide
  rw [h0]
  unfold encRat encInt
  simp only [List.length_append, List.length_cons]
  have hden : 1 ≤ (encNat q.den).length := one_le_encNat_pos q.den_pos
  omega

lemma length_flatMap_finRange {n : ℕ} (f : Fin n → List Sym) :
    ((List.finRange n).flatMap f).length = ∑ i : Fin n, (f i).length := by
  rw [List.length_flatMap, Fin.sum_univ_def]

lemma encVec_zero_len_le {m : ℕ} (v : Fin m → ℚ) :
    (encVec (fun _ : Fin m => (0 : ℚ))).length ≤ (encVec v).length := by
  unfold encVec
  rw [length_flatMap_finRange, length_flatMap_finRange]
  refine Finset.sum_le_sum fun j _ => ?_
  simp only [List.length_append]
  exact Nat.add_le_add_right (encRat_zero_len_le (v j)) _

lemma homInstance_valid_and_len (I : Instance) (hI : I.Valid) :
    (homInstance I).Valid ∧ (encInstance (homInstance I)).length ≤ (encInstance I).length := by
  refine ⟨⟨hI.one_le_d, hI.one_le_τ, hI.bounded, hI.convex⟩, ?_⟩
  unfold encInstance homInstance
  simp only [List.length_append]
  have hQ := encVec_zero_len_le I.cQ
  have hA := encVec_zero_len_le I.cA
  omega

lemma encVec_len_eq {n : ℕ} (v : Fin n → ℚ) :
    (encVec v).length = ∑ j : Fin n, ((encRat (v j)).length + 1) := by
  unfold encVec
  rw [length_flatMap_finRange]
  simp [List.length_append]

lemma card_le_encVec_len {n : ℕ} (v : Fin n → ℚ) : n ≤ (encVec v).length := by
  rw [encVec_len_eq]
  calc n = ∑ _ : Fin n, 1 := by simp
    _ ≤ ∑ j : Fin n, ((encRat (v j)).length + 1) :=
        Finset.sum_le_sum fun j _ => by omega

lemma sum_encRat_le_encVec_len {n : ℕ} (v : Fin n → ℚ) :
    (∑ j : Fin n, (encRat (v j)).length) ≤ (encVec v).length := by
  rw [encVec_len_eq]
  exact Finset.sum_le_sum fun j _ => Nat.le_succ _

lemma encMat_len_eq {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) :
    (encMat A).length = ∑ i : Fin p, ((encVec (A i)).length + 1) := by
  unfold encMat
  rw [length_flatMap_finRange]
  simp [List.length_append]

lemma sum_encRat_le_encMat_len {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) :
    (∑ i : Fin p, ∑ j : Fin q, (encRat (A i j)).length) ≤ (encMat A).length := by
  rw [encMat_len_eq]
  exact Finset.sum_le_sum fun i _ => le_trans (sum_encRat_le_encVec_len (A i)) (Nat.le_succ _)

lemma cols_le_encMat_len {p q : ℕ} (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin q) ℚ) :
    q ≤ (encMat A).length := by
  let i₀ : Fin p := ⟨0, hp⟩
  rw [encMat_len_eq]
  calc q ≤ (encVec (A i₀)).length + 1 := le_trans (card_le_encVec_len (A i₀)) (Nat.le_succ _)
    _ ≤ ∑ i : Fin p, ((encVec (A i)).length + 1) :=
        Finset.single_le_sum (f := fun i : Fin p => (encVec (A i)).length + 1)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i₀)

lemma one_le_m_of_valid (I : Instance) (hI : I.Valid) (t : Fin I.τ) : 1 ≤ I.m t := by
  by_contra hm
  have hm0 : I.m t = 0 := by omega
  have hPuniv : I.P t = Set.univ := by
    ext p
    simp only [Instance.P, Set.mem_univ, iff_true]
    exact fun i => Fin.elim0 (hm0 ▸ i)
  have hbdd := hI.bounded t
  rw [hPuniv, Metric.isBounded_iff] at hbdd
  obtain ⟨C, hC⟩ := hbdd
  let R : ℝ := max C 0 + 1
  let p₁ : (Fin I.d → ℝ) × (Fin I.k → ℝ) := (fun _ => R, 0)
  let p₀ : (Fin I.d → ℝ) × (Fin I.k → ℝ) := (0, 0)
  have hdist : dist p₁ p₀ ≤ C := hC (Set.mem_univ p₁) (Set.mem_univ p₀)
  let i₀ : Fin I.d := ⟨0, hI.one_le_d⟩
  have hcoord : dist (p₁.1 i₀) (p₀.1 i₀) ≤ dist p₁ p₀ :=
    le_trans (dist_le_pi_dist p₁.1 p₀.1 i₀) (le_max_left _ _)
  have hR : |R| ≤ C := by
    simpa [p₁, p₀, Real.dist_eq] using le_trans hcoord hdist
  have hRpos : 0 < R := by positivity
  rw [abs_of_pos hRpos] at hR
  linarith [le_max_left C 0]

def locBlockLen (I : Instance) (t : Fin I.τ) : ℕ :=
  (encNat (I.m t) ++ [3] ++ encMat (I.Aloc t) ++ encMat (I.Bloc t) ++ encVec (I.bloc t) ++ [3] ++
    encNat (I.deg t) ++ [3] ++ encVec (I.coeff t) ++ [3]).length

lemma locBlockLen_ge (I : Instance) (t : Fin I.τ) :
    1 + (encMat (I.Aloc t)).length + (encMat (I.Bloc t)).length + (encVec (I.bloc t)).length ≤
      locBlockLen I t := by
  unfold locBlockLen
  simp only [List.length_append, List.length_singleton]
  omega

lemma sum_locBlockLen_le (I : Instance) :
    (∑ t : Fin I.τ, locBlockLen I t) +
      ((encMat I.QY).length + (encMat I.QV).length + (encVec I.cQ).length) +
      ((∑ t : Fin I.τ, ((encMat (I.AY t)).length + (encMat (I.AV t)).length)) +
        (encMat I.AN).length + (encVec I.cA).length) + 1 ≤
      (encInstance I).length := by
  have h1 : ((List.finRange I.τ).flatMap (fun t =>
      encNat (I.m t) ++ [3] ++ encMat (I.Aloc t) ++ encMat (I.Bloc t) ++ encVec (I.bloc t) ++ [3] ++
      encNat (I.deg t) ++ [3] ++ encVec (I.coeff t) ++ [3])).length =
      ∑ t : Fin I.τ, locBlockLen I t := length_flatMap_finRange _
  have h2 : ((List.finRange I.τ).flatMap (fun t => encMat (I.AY t) ++ encMat (I.AV t))).length =
      ∑ t : Fin I.τ, ((encMat (I.AY t)).length + (encMat (I.AV t)).length) := by
    rw [length_flatMap_finRange]
    simp [List.length_append]
  unfold encInstance
  simp only [List.length_append, List.length_singleton]
  omega

lemma instance_dim_bounds (I : Instance) (hI : I.Valid) :
    1 ≤ (encInstance I).length ∧
    I.d ≤ (encInstance I).length ∧
    I.k ≤ (encInstance I).length ∧
    I.τ ≤ (encInstance I).length ∧
    I.mQ ≤ (encInstance I).length ∧
    I.mA ≤ (encInstance I).length ∧
    ∀ t : Fin I.τ, I.m t ≤ (encInstance I).length := by
  have hMain := sum_locBlockLen_le I
  let t₀ : Fin I.τ := ⟨0, hI.one_le_τ⟩
  have hm₀ : 1 ≤ I.m t₀ := one_le_m_of_valid I hI t₀
  have ht₀_single := Finset.single_le_sum (f := locBlockLen I)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ t₀)
  have ht₀_ge := locBlockLen_ge I t₀
  have hd : I.d ≤ (encInstance I).length :=
    le_trans (cols_le_encMat_len hm₀ (I.Aloc t₀)) (by omega)
  have hk : I.k ≤ (encInstance I).length :=
    le_trans (cols_le_encMat_len hm₀ (I.Bloc t₀)) (by omega)
  have hτ : I.τ ≤ (encInstance I).length := by
    have h1 : I.τ ≤ ∑ t : Fin I.τ, locBlockLen I t := by
      calc I.τ = ∑ _ : Fin I.τ, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum fun t _ => by have := locBlockLen_ge I t; omega
    omega
  have hmQ : I.mQ ≤ (encInstance I).length := le_trans (card_le_encVec_len I.cQ) (by omega)
  have hmA : I.mA ≤ (encInstance I).length := le_trans (card_le_encVec_len I.cA) (by omega)
  have hm : ∀ t : Fin I.τ, I.m t ≤ (encInstance I).length := by
    intro t
    have hsingle := Finset.single_le_sum (f := locBlockLen I)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
    have hge := locBlockLen_ge I t
    have hb := card_le_encVec_len (I.bloc t)
    omega
  exact ⟨by omega, hd, hk, hτ, hmQ, hmA, hm⟩

lemma rat_num_den_lt_two_pow (q : ℚ) :
    q.num.natAbs < 2 ^ (encRat q).length ∧ q.den < 2 ^ (encRat q).length := by
  have hlen : (encNat q.num.natAbs).length + (encNat q.den).length + 2 = (encRat q).length := by
    unfold encRat encInt
    simp [List.length_append]
    omega
  exact ⟨lt_of_lt_of_le (nat_lt_two_pow_encNat_len q.num.natAbs)
      (Nat.pow_le_pow_right (by omega) (by omega)),
    lt_of_lt_of_le (nat_lt_two_pow_encNat_len q.den)
      (Nat.pow_le_pow_right (by omega) (by omega))⟩

lemma prod_den_le_two_pow_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    (∏ i ∈ s, (f i).den) ≤ 2 ^ (∑ i ∈ s, (encRat (f i)).length) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod' fun i _ => le_of_lt (rat_num_den_lt_two_pow (f i)).2

lemma clearRat_natAbs_lt (q : ℕ) (r : ℚ) {L : ℕ}
    (hq : q ≤ 2 ^ L) (hr : (encRat r).length ≤ L) :
    (clearRat q r).natAbs < 2 ^ (2 * L) := by
  unfold clearRat
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  have hdiv : q / r.den ≤ q := Nat.div_le_self q r.den
  have hnum : r.num.natAbs < 2 ^ L :=
    lt_of_lt_of_le (rat_num_den_lt_two_pow r).1 (Nat.pow_le_pow_right (by omega) hr)
  have hqL : q / r.den ≤ 2 ^ L := le_trans hdiv hq
  calc r.num.natAbs * (q / r.den)
    _ ≤ r.num.natAbs * 2 ^ L := Nat.mul_le_mul_left _ hqL
    _ < 2 ^ L * 2 ^ L := Nat.mul_lt_mul_of_pos_right hnum (by positivity)
    _ = 2 ^ (2 * L) := by rw [← pow_add, two_mul]

lemma rowDenom_and_entry_bounds (I : Instance) :
    let L := (encInstance I).length
    let D := clearIntDesc I
    (∀ t i j, (D.WY t i j).natAbs < 2 ^ (2 * L)) ∧
    (∀ t i j, (D.WV t i j).natAbs < 2 ^ (2 * L)) ∧
    (∀ i t, (D.WN i t).natAbs < 2 ^ (2 * L)) ∧
    (∀ i, (D.cW i).natAbs < 2 ^ (2 * L)) ∧
    (∀ t i j, (D.LA t i j).natAbs < 2 ^ (2 * L)) ∧
    (∀ t i j, (D.LB t i j).natAbs < 2 ^ (2 * L)) ∧
    (∀ t i, (D.Lb t i).natAbs < 2 ^ (2 * L)) := by
  have hMain := sum_locBlockLen_le I
  set L := (encInstance I).length
  have hRowQ : ∀ i : Fin I.mQ, rowDenomQ I i ≤ 2 ^ L ∧
      (∀ j, (encRat (I.QY i j)).length ≤ L) ∧
      (∀ j, (encRat (I.QV i j)).length ≤ L) ∧
      (encRat (I.cQ i)).length ≤ L := by
    intro i
    have h1 : (∑ j, (encRat (I.QY i j)).length) ≤ (encMat I.QY).length :=
      le_trans (Finset.single_le_sum (f := fun i' => ∑ j, (encRat (I.QY i' j)).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (sum_encRat_le_encMat_len I.QY)
    have h2 : (∑ j, (encRat (I.QV i j)).length) ≤ (encMat I.QV).length :=
      le_trans (Finset.single_le_sum (f := fun i' => ∑ j, (encRat (I.QV i' j)).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (sum_encRat_le_encMat_len I.QV)
    have h3 : (encRat (I.cQ i)).length ≤ (encVec I.cQ).length :=
      le_trans (Finset.single_le_sum (f := fun i' => (encRat (I.cQ i')).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (sum_encRat_le_encVec_len I.cQ)
    have hsum : (∑ j, (encRat (I.QY i j)).length) + (∑ j, (encRat (I.QV i j)).length) +
        (encRat (I.cQ i)).length ≤ L := by omega
    have hden : rowDenomQ I i ≤ 2 ^ L := by
      unfold rowDenomQ
      calc (∏ j, (I.QY i j).den) * (∏ j, (I.QV i j).den) * (I.cQ i).den
        _ ≤ 2 ^ (∑ j, (encRat (I.QY i j)).length) * 2 ^ (∑ j, (encRat (I.QV i j)).length) *
            2 ^ (encRat (I.cQ i)).length :=
          Nat.mul_le_mul (Nat.mul_le_mul (prod_den_le_two_pow_sum _ _) (prod_den_le_two_pow_sum _ _))
            (le_of_lt (rat_num_den_lt_two_pow (I.cQ i)).2)
        _ = 2 ^ ((∑ j, (encRat (I.QY i j)).length) + (∑ j, (encRat (I.QV i j)).length) +
            (encRat (I.cQ i)).length) := by rw [← pow_add, ← pow_add]
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) hsum
    refine ⟨hden, fun j => ?_, fun j => ?_, by omega⟩
    · have := Finset.single_le_sum (f := fun j' => (encRat (I.QY i j')).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      omega
    · have := Finset.single_le_sum (f := fun j' => (encRat (I.QV i j')).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      omega
  have hRowA : ∀ i : Fin I.mA, rowDenomA I i ≤ 2 ^ L ∧
      (∀ t j, (encRat (I.AY t i j)).length ≤ L) ∧
      (∀ t j, (encRat (I.AV t i j)).length ≤ L) ∧
      (∀ t, (encRat (I.AN i t)).length ≤ L) ∧
      (encRat (I.cA i)).length ≤ L := by
    intro i
    have h1 : (∑ t, ((∑ j, (encRat (I.AY t i j)).length) + (∑ j, (encRat (I.AV t i j)).length))) ≤
        ∑ t : Fin I.τ, ((encMat (I.AY t)).length + (encMat (I.AV t)).length) := by
      refine Finset.sum_le_sum fun t _ => add_le_add ?_ ?_
      · exact le_trans (Finset.single_le_sum (f := fun i' => ∑ j, (encRat (I.AY t i' j)).length)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (sum_encRat_le_encMat_len (I.AY t))
      · exact le_trans (Finset.single_le_sum (f := fun i' => ∑ j, (encRat (I.AV t i' j)).length)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (sum_encRat_le_encMat_len (I.AV t))
    have h2 : (∑ t, (encRat (I.AN i t)).length) ≤ (encMat I.AN).length :=
      le_trans (Finset.single_le_sum (f := fun i' => ∑ t, (encRat (I.AN i' t)).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (sum_encRat_le_encMat_len I.AN)
    have h3 : (encRat (I.cA i)).length ≤ (encVec I.cA).length :=
      le_trans (Finset.single_le_sum (f := fun i' => (encRat (I.cA i')).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (sum_encRat_le_encVec_len I.cA)
    have hsum : (∑ t, ((∑ j, (encRat (I.AY t i j)).length) +
        (∑ j, (encRat (I.AV t i j)).length) + (encRat (I.AN i t)).length)) +
        (encRat (I.cA i)).length ≤ L := by
      rw [Finset.sum_add_distrib]
      omega
    have hden : rowDenomA I i ≤ 2 ^ L := by
      unfold rowDenomA
      have hprodT : (∏ t : Fin I.τ, ((∏ j, (I.AY t i j).den) * (∏ j, (I.AV t i j).den) *
          (I.AN i t).den)) ≤
          2 ^ (∑ t : Fin I.τ, ((∑ j, (encRat (I.AY t i j)).length) +
            (∑ j, (encRat (I.AV t i j)).length) + (encRat (I.AN i t)).length)) := by
        rw [← Finset.prod_pow_eq_pow_sum]
        refine Finset.prod_le_prod' fun t _ => ?_
        calc (∏ j, (I.AY t i j).den) * (∏ j, (I.AV t i j).den) * (I.AN i t).den
          _ ≤ 2 ^ (∑ j, (encRat (I.AY t i j)).length) * 2 ^ (∑ j, (encRat (I.AV t i j)).length) *
              2 ^ (encRat (I.AN i t)).length :=
            Nat.mul_le_mul (Nat.mul_le_mul (prod_den_le_two_pow_sum _ _) (prod_den_le_two_pow_sum _ _))
              (le_of_lt (rat_num_den_lt_two_pow (I.AN i t)).2)
          _ = _ := by rw [← pow_add, ← pow_add]
      calc _ ≤ 2 ^ (∑ t : Fin I.τ, ((∑ j, (encRat (I.AY t i j)).length) +
            (∑ j, (encRat (I.AV t i j)).length) + (encRat (I.AN i t)).length)) *
            2 ^ (encRat (I.cA i)).length :=
          Nat.mul_le_mul hprodT (le_of_lt (rat_num_den_lt_two_pow (I.cA i)).2)
        _ = _ := by rw [← pow_add]
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) hsum
    refine ⟨hden, fun t j => ?_, fun t j => ?_, fun t => ?_, by omega⟩
    · have hj := Finset.single_le_sum (f := fun j' => (encRat (I.AY t i j')).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have ht := Finset.single_le_sum (f := fun t' : Fin I.τ =>
        (∑ j', (encRat (I.AY t' i j')).length) + (∑ j', (encRat (I.AV t' i j')).length))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
      omega
    · have hj := Finset.single_le_sum (f := fun j' => (encRat (I.AV t i j')).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have ht := Finset.single_le_sum (f := fun t' : Fin I.τ =>
        (∑ j', (encRat (I.AY t' i j')).length) + (∑ j', (encRat (I.AV t' i j')).length))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
      omega
    · have ht := Finset.single_le_sum (f := fun t' => (encRat (I.AN i t')).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
      omega
  have hRowLoc : ∀ (t : Fin I.τ) (i : Fin (I.m t)), rowDenomLoc I t i ≤ 2 ^ L ∧
      (∀ j, (encRat (I.Aloc t i j)).length ≤ L) ∧
      (∀ j, (encRat (I.Bloc t i j)).length ≤ L) ∧
      (encRat (I.bloc t i)).length ≤ L := by
    intro t i
    have hsingle := Finset.single_le_sum (f := locBlockLen I)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
    have hge := locBlockLen_ge I t
    have h1 : (∑ j, (encRat (I.Aloc t i j)).length) ≤ (encMat (I.Aloc t)).length :=
      le_trans (Finset.single_le_sum (f := fun i' => ∑ j, (encRat (I.Aloc t i' j)).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (sum_encRat_le_encMat_len (I.Aloc t))
    have h2 : (∑ j, (encRat (I.Bloc t i j)).length) ≤ (encMat (I.Bloc t)).length :=
      le_trans (Finset.single_le_sum (f := fun i' => ∑ j, (encRat (I.Bloc t i' j)).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (sum_encRat_le_encMat_len (I.Bloc t))
    have h3 : (encRat (I.bloc t i)).length ≤ (encVec (I.bloc t)).length :=
      le_trans (Finset.single_le_sum (f := fun i' => (encRat (I.bloc t i')).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (sum_encRat_le_encVec_len (I.bloc t))
    have hsum : (∑ j, (encRat (I.Aloc t i j)).length) + (∑ j, (encRat (I.Bloc t i j)).length) +
        (encRat (I.bloc t i)).length ≤ L := by omega
    have hden : rowDenomLoc I t i ≤ 2 ^ L := by
      unfold rowDenomLoc
      calc (∏ j, (I.Aloc t i j).den) * (∏ j, (I.Bloc t i j).den) * (I.bloc t i).den
        _ ≤ 2 ^ (∑ j, (encRat (I.Aloc t i j)).length) * 2 ^ (∑ j, (encRat (I.Bloc t i j)).length) *
            2 ^ (encRat (I.bloc t i)).length :=
          Nat.mul_le_mul (Nat.mul_le_mul (prod_den_le_two_pow_sum _ _) (prod_den_le_two_pow_sum _ _))
            (le_of_lt (rat_num_den_lt_two_pow (I.bloc t i)).2)
        _ = _ := by rw [← pow_add, ← pow_add]
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) hsum
    refine ⟨hden, fun j => ?_, fun j => ?_, by omega⟩
    · have := Finset.single_le_sum (f := fun j' => (encRat (I.Aloc t i j')).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      omega
    · have := Finset.single_le_sum (f := fun j' => (encRat (I.Bloc t i j')).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t i j
    refine Fin.addCases (fun iQ => ?_) (fun iA => ?_) i
    · simpa [clearIntDesc, Matrix.of_apply] using clearRat_natAbs_lt _ _ (hRowQ iQ).1 ((hRowQ iQ).2.1 j)
    · simpa [clearIntDesc, Matrix.of_apply] using clearRat_natAbs_lt _ _ (hRowA iA).1 ((hRowA iA).2.1 t j)
  · intro t i j
    refine Fin.addCases (fun iQ => ?_) (fun iA => ?_) i
    · simpa [clearIntDesc, Matrix.of_apply] using clearRat_natAbs_lt _ _ (hRowQ iQ).1 ((hRowQ iQ).2.2.1 j)
    · simpa [clearIntDesc, Matrix.of_apply] using clearRat_natAbs_lt _ _ (hRowA iA).1 ((hRowA iA).2.2.1 t j)
  · intro i t
    refine Fin.addCases (fun iQ => ?_) (fun iA => ?_) i
    · simp [clearIntDesc, Matrix.of_apply]
    · simpa [clearIntDesc, Matrix.of_apply] using clearRat_natAbs_lt _ _ (hRowA iA).1 ((hRowA iA).2.2.2.1 t)
  · intro i
    refine Fin.addCases (fun iQ => ?_) (fun iA => ?_) i
    · simpa [clearIntDesc] using clearRat_natAbs_lt _ _ (hRowQ iQ).1 (hRowQ iQ).2.2.2
    · simpa [clearIntDesc] using clearRat_natAbs_lt _ _ (hRowA iA).1 (hRowA iA).2.2.2.2
  · intro t i j
    dsimp only [clearIntDesc, Matrix.of_apply]
    exact clearRat_natAbs_lt _ _ (hRowLoc t i).1 ((hRowLoc t i).2.1 j)
  · intro t i j
    dsimp only [clearIntDesc, Matrix.of_apply]
    exact clearRat_natAbs_lt _ _ (hRowLoc t i).1 ((hRowLoc t i).2.2.1 j)
  · intro t i
    dsimp only [clearIntDesc]
    exact clearRat_natAbs_lt _ _ (hRowLoc t i).1 (hRowLoc t i).2.2.2

lemma nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n :=
  Nat.le_of_lt Nat.lt_two_pow_self

lemma factorial_le_two_pow_sq (n : ℕ) : n.factorial ≤ 2 ^ (n ^ 2) := by
  calc n.factorial ≤ n ^ n := Nat.factorial_le_pow n
    _ ≤ (2 ^ n) ^ n := Nat.pow_le_pow_left (nat_le_two_pow n) n
    _ = 2 ^ (n ^ 2) := by rw [← pow_mul, sq]

lemma nstar_lt_two_pow {τ d k U L LM : ℕ}
    (hd1 : 1 ≤ d) (hτ1 : 1 ≤ τ) (hL1 : 1 ≤ L) (hkL : k ≤ L)
    (hU_le : U ≤ 2 ^ (9 * (L + LM))) :
    Nstar τ d k U < 2 ^ (64 * (τ * 2 ^ d) ^ 3 * (L + LM) ^ 2) := by
  set s := τ * 2 ^ d
  have hs2 : 2 ≤ s := by
    have hd2 : 2 ≤ 2 ^ d := le_trans (by decide) (Nat.pow_le_pow_right (by omega) hd1 : 2 ^ 1 ≤ 2 ^ d)
    unfold s
    nlinarith
  set Rk := s * k
  have hRk1 : Rk + 1 ≤ 2 * s * (L + LM) := by
    have : Rk ≤ s * L := Nat.mul_le_mul_left s hkL
    nlinarith
  have hH_le : (Rk + 1).factorial * U ^ (Rk + 1) ≤ 2 ^ (22 * s ^ 2 * (L + LM) ^ 2) := by
    calc (Rk + 1).factorial * U ^ (Rk + 1)
      _ ≤ 2 ^ ((Rk + 1) ^ 2) * (2 ^ (9 * (L + LM))) ^ (Rk + 1) :=
          Nat.mul_le_mul (factorial_le_two_pow_sq _) (Nat.pow_le_pow_left hU_le _)
      _ = 2 ^ ((Rk + 1) ^ 2 + 9 * (L + LM) * (Rk + 1)) := by rw [← pow_mul, ← pow_add]
      _ ≤ 2 ^ ((2 * s * (L + LM)) ^ 2 + 9 * (L + LM) * (2 * s * (L + LM))) := by
          refine Nat.pow_le_pow_right (by omega) ?_
          exact add_le_add (Nat.pow_le_pow_left hRk1 2) (Nat.mul_le_mul_left _ hRk1)
      _ ≤ 2 ^ (22 * s ^ 2 * (L + LM) ^ 2) := by
          refine Nat.pow_le_pow_right (by omega) ?_
          have hss : s ≤ s ^ 2 := by nlinarith
          nlinarith
  have hPrefix : s * (s + 1) * s.factorial < 2 ^ (8 * s ^ 3 * (L + LM) ^ 2) := by
    have hLLM1 : 1 ≤ (L + LM) ^ 2 := by nlinarith
    have hsp : s < 2 ^ s := Nat.lt_two_pow_self
    have hs1p : s + 1 ≤ 2 ^ (s + 1) := nat_le_two_pow (s + 1)
    have hsfp : s.factorial ≤ 2 ^ (s ^ 2) := factorial_le_two_pow_sq s
    calc s * (s + 1) * s.factorial
      _ < 2 ^ s * 2 ^ (s + 1) * 2 ^ (s ^ 2) := by
          have hpos : 0 < 2 ^ (s + 1) * 2 ^ (s ^ 2) := by positivity
          calc s * (s + 1) * s.factorial
            _ ≤ s * (2 ^ (s + 1) * 2 ^ (s ^ 2)) := by
                rw [mul_assoc]
                exact Nat.mul_le_mul_left s (Nat.mul_le_mul hs1p hsfp)
            _ < 2 ^ s * (2 ^ (s + 1) * 2 ^ (s ^ 2)) := Nat.mul_lt_mul_of_pos_right hsp hpos
            _ = 2 ^ s * 2 ^ (s + 1) * 2 ^ (s ^ 2) := by ring
      _ = 2 ^ (s + (s + 1) + s ^ 2) := by rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ (8 * s ^ 3 * (L + LM) ^ 2) := by
          refine Nat.pow_le_pow_right (by omega) ?_
          have hs3 : s ^ 2 ≤ s ^ 3 := by
            calc s ^ 2 = s ^ 2 * 1 := by ring
              _ ≤ s ^ 2 * s := Nat.mul_le_mul_left _ (by omega)
              _ = s ^ 3 := by ring
          nlinarith
  have hHs : ((Rk + 1).factorial * U ^ (Rk + 1)) ^ s ≤ 2 ^ (22 * s ^ 3 * (L + LM) ^ 2) := by
    calc _ ≤ (2 ^ (22 * s ^ 2 * (L + LM) ^ 2)) ^ s := Nat.pow_le_pow_left hH_le s
      _ = 2 ^ (22 * s ^ 2 * (L + LM) ^ 2 * s) := by rw [← pow_mul]
      _ = 2 ^ (22 * s ^ 3 * (L + LM) ^ 2) := by congr 1; ring
  have hHs_pos : 0 < 2 ^ (22 * s ^ 3 * (L + LM) ^ 2) := by positivity
  unfold Nstar
  dsimp only []
  calc s * (s + 1) * s.factorial * ((Rk + 1).factorial * U ^ (Rk + 1)) ^ s
    _ ≤ (s * (s + 1) * s.factorial) * 2 ^ (22 * s ^ 3 * (L + LM) ^ 2) :=
        Nat.mul_le_mul_left _ hHs
    _ < 2 ^ (8 * s ^ 3 * (L + LM) ^ 2) * 2 ^ (22 * s ^ 3 * (L + LM) ^ 2) :=
        Nat.mul_lt_mul_of_pos_right hPrefix hHs_pos
    _ = 2 ^ (30 * s ^ 3 * (L + LM) ^ 2) := by rw [← pow_add]; congr 1; ring
    _ ≤ 2 ^ (64 * s ^ 3 * (L + LM) ^ 2) := by
        refine Nat.pow_le_pow_right (by omega) ?_
        exact Nat.mul_le_mul_right ((L + LM) ^ 2) (Nat.mul_le_mul_right (s ^ 3) (by decide))

lemma sall_comb {a b c d e f g X : ℕ}
    (h1 : 1 ≤ X) (ha : a ≤ 2 * X) (hb : b ≤ 2 * X) (hc : c ≤ 2 * X) (hd : d ≤ 2 * X)
    (he : e ≤ X) (hf : f ≤ X) (hg : g ≤ X) :
    1 + a + b + c + d + e + f + g ≤ 12 * X := by
  omega

lemma lm_add_9l (L LM : ℕ) : LM + 9 * L ≤ 9 * (L + LM) := by
  omega

lemma coeffBoundU_le_two_pow (I : Instance) (hI : I.Valid) (M : ℕ) :
    coeffBoundU I M ≤ 2 ^ (9 * ((encInstance I).length + (encNat M).length)) := by
  obtain ⟨hL1, hdL, hkL, hτL, hmQL, hmAL, hmL⟩ := instance_dim_bounds I hI
  obtain ⟨eWY, eWV, eWN, ecW, eLA, eLB, eLb⟩ := rowDenom_and_entry_bounds I
  set L := (encInstance I).length
  set LM := (encNat M).length
  set D := clearIntDesc I
  set S_all : ℕ := 1 +
    (∑ t, ∑ i, ∑ j, (D.WY t i j).natAbs) +
    (∑ t, ∑ i, ∑ j, (D.WV t i j).natAbs) +
    (∑ i, ∑ t, (D.WN i t).natAbs) +
    (∑ i, (D.cW i).natAbs) +
    (∑ t, ∑ i, ∑ j, (D.LA t i j).natAbs) +
    (∑ t, ∑ i, ∑ j, (D.LB t i j).natAbs) +
    (∑ t, ∑ i, (D.Lb t i).natAbs)
  have hU_eq : coeffBoundU I M = (M + 1) * S_all := rfl
  have hmW : D.mW = I.mQ + I.mA := rfl
  have hB_pos : 0 < 2 ^ (2 * L) := by positivity
  have sWY : (∑ t, ∑ i, ∑ j, (D.WY t i j).natAbs) ≤ 2 * L ^ 3 * 2 ^ (2 * L) := by
    calc (∑ t, ∑ i, ∑ j, (D.WY t i j).natAbs)
      _ ≤ ∑ _t : Fin I.τ, ∑ _i : Fin D.mW, ∑ _j : Fin I.d, 2 ^ (2 * L) :=
          Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun i _ =>
            Finset.sum_le_sum fun j _ => le_of_lt (eWY t i j)
      _ = I.τ * (I.mQ + I.mA) * I.d * 2 ^ (2 * L) := by simp [hmW, mul_assoc]
      _ ≤ L * (L + L) * L * 2 ^ (2 * L) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul hτL (Nat.add_le_add hmQL hmAL)) hdL)
      _ = 2 * L ^ 3 * 2 ^ (2 * L) := by ring
  have sWV : (∑ t, ∑ i, ∑ j, (D.WV t i j).natAbs) ≤ 2 * L ^ 3 * 2 ^ (2 * L) := by
    calc (∑ t, ∑ i, ∑ j, (D.WV t i j).natAbs)
      _ ≤ ∑ _t : Fin I.τ, ∑ _i : Fin D.mW, ∑ _j : Fin I.k, 2 ^ (2 * L) :=
          Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun i _ =>
            Finset.sum_le_sum fun j _ => le_of_lt (eWV t i j)
      _ = I.τ * (I.mQ + I.mA) * I.k * 2 ^ (2 * L) := by simp [hmW, mul_assoc]
      _ ≤ L * (L + L) * L * 2 ^ (2 * L) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul hτL (Nat.add_le_add hmQL hmAL)) hkL)
      _ = 2 * L ^ 3 * 2 ^ (2 * L) := by ring
  have sWN : (∑ i, ∑ t, (D.WN i t).natAbs) ≤ 2 * L ^ 3 * 2 ^ (2 * L) := by
    have hL23 : L ^ 2 ≤ L ^ 3 := Nat.pow_le_pow_right hL1 (by omega)
    calc (∑ i, ∑ t, (D.WN i t).natAbs)
      _ ≤ ∑ _i : Fin D.mW, ∑ _t : Fin I.τ, 2 ^ (2 * L) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun t _ => le_of_lt (eWN i t)
      _ = (I.mQ + I.mA) * I.τ * 2 ^ (2 * L) := by simp [hmW, mul_assoc]
      _ ≤ (L + L) * L * 2 ^ (2 * L) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.add_le_add hmQL hmAL) hτL)
      _ = 2 * L ^ 2 * 2 ^ (2 * L) := by ring
      _ ≤ 2 * L ^ 3 * 2 ^ (2 * L) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hL23)
  have scW : (∑ i, (D.cW i).natAbs) ≤ 2 * L ^ 3 * 2 ^ (2 * L) := by
    have hL13 : L ≤ L ^ 3 := le_trans (by simp) (Nat.pow_le_pow_right hL1 (by omega) : L ^ 1 ≤ L ^ 3)
    calc (∑ i, (D.cW i).natAbs)
      _ ≤ ∑ _i : Fin D.mW, 2 ^ (2 * L) := Finset.sum_le_sum fun i _ => le_of_lt (ecW i)
      _ = (I.mQ + I.mA) * 2 ^ (2 * L) := by simp [hmW]
      _ ≤ (L + L) * 2 ^ (2 * L) := Nat.mul_le_mul_right _ (Nat.add_le_add hmQL hmAL)
      _ = 2 * L * 2 ^ (2 * L) := by ring
      _ ≤ 2 * L ^ 3 * 2 ^ (2 * L) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hL13)
  have sLA : (∑ t, ∑ i, ∑ j, (D.LA t i j).natAbs) ≤ L ^ 3 * 2 ^ (2 * L) := by
    calc (∑ t, ∑ i, ∑ j, (D.LA t i j).natAbs)
      _ ≤ ∑ t : Fin I.τ, ∑ _i : Fin (I.m t), ∑ _j : Fin I.d, 2 ^ (2 * L) :=
          Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun i _ =>
            Finset.sum_le_sum fun j _ => le_of_lt (eLA t i j)
      _ = ∑ t : Fin I.τ, I.m t * I.d * 2 ^ (2 * L) := by simp [mul_assoc]
      _ ≤ ∑ _t : Fin I.τ, L * L * 2 ^ (2 * L) :=
          Finset.sum_le_sum fun t _ => Nat.mul_le_mul_right _ (Nat.mul_le_mul (hmL t) hdL)
      _ = I.τ * (L * L * 2 ^ (2 * L)) := by simp
      _ ≤ L * (L * L * 2 ^ (2 * L)) := Nat.mul_le_mul_right _ hτL
      _ = L ^ 3 * 2 ^ (2 * L) := by ring
  have sLB : (∑ t, ∑ i, ∑ j, (D.LB t i j).natAbs) ≤ L ^ 3 * 2 ^ (2 * L) := by
    calc (∑ t, ∑ i, ∑ j, (D.LB t i j).natAbs)
      _ ≤ ∑ t : Fin I.τ, ∑ _i : Fin (I.m t), ∑ _j : Fin I.k, 2 ^ (2 * L) :=
          Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun i _ =>
            Finset.sum_le_sum fun j _ => le_of_lt (eLB t i j)
      _ = ∑ t : Fin I.τ, I.m t * I.k * 2 ^ (2 * L) := by simp [mul_assoc]
      _ ≤ ∑ _t : Fin I.τ, L * L * 2 ^ (2 * L) :=
          Finset.sum_le_sum fun t _ => Nat.mul_le_mul_right _ (Nat.mul_le_mul (hmL t) hkL)
      _ = I.τ * (L * L * 2 ^ (2 * L)) := by simp
      _ ≤ L * (L * L * 2 ^ (2 * L)) := Nat.mul_le_mul_right _ hτL
      _ = L ^ 3 * 2 ^ (2 * L) := by ring
  have sLb : (∑ t, ∑ i, (D.Lb t i).natAbs) ≤ L ^ 3 * 2 ^ (2 * L) := by
    have hL23 : L ^ 2 ≤ L ^ 3 := Nat.pow_le_pow_right hL1 (by omega)
    calc (∑ t, ∑ i, (D.Lb t i).natAbs)
      _ ≤ ∑ t : Fin I.τ, ∑ _i : Fin (I.m t), 2 ^ (2 * L) :=
          Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun i _ => le_of_lt (eLb t i)
      _ = ∑ t : Fin I.τ, I.m t * 2 ^ (2 * L) := by simp
      _ ≤ ∑ _t : Fin I.τ, L * 2 ^ (2 * L) :=
          Finset.sum_le_sum fun t _ => Nat.mul_le_mul_right _ (hmL t)
      _ = I.τ * (L * 2 ^ (2 * L)) := by simp
      _ ≤ L * (L * 2 ^ (2 * L)) := Nat.mul_le_mul_right _ hτL
      _ = L ^ 2 * 2 ^ (2 * L) := by ring
      _ ≤ L ^ 3 * 2 ^ (2 * L) := Nat.mul_le_mul_right _ hL23
  have h12L3 : 12 * L ^ 3 ≤ 2 ^ (7 * L) := by
    have h43 : 4 + L * 3 ≤ 7 * L := by
      calc 4 + L * 3 ≤ 4 * L + L * 3 := Nat.add_le_add_right (Nat.le_mul_of_pos_right 4 hL1) _
        _ = 7 * L := by ring
    calc 12 * L ^ 3 ≤ 2 ^ 4 * (2 ^ L) ^ 3 :=
          Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left (nat_le_two_pow L) 3)
      _ = 2 ^ (4 + L * 3) := by rw [← pow_mul, ← pow_add]
      _ ≤ 2 ^ (7 * L) := Nat.pow_le_pow_right (by decide) h43
  have hSall : S_all ≤ 2 ^ (9 * L) := by
    have h1 : 1 ≤ L ^ 3 * 2 ^ (2 * L) := Nat.mul_pos (pow_pos hL1 3) hB_pos
    calc S_all ≤ 12 * (L ^ 3 * 2 ^ (2 * L)) :=
          sall_comb h1 (by simpa [mul_assoc] using sWY) (by simpa [mul_assoc] using sWV)
            (by simpa [mul_assoc] using sWN) (by simpa [mul_assoc] using scW) sLA sLB sLb
      _ = (12 * L ^ 3) * 2 ^ (2 * L) := by ring
      _ ≤ 2 ^ (7 * L) * 2 ^ (2 * L) := Nat.mul_le_mul_right _ h12L3
      _ = 2 ^ (9 * L) := by rw [← pow_add, show 7 * L + 2 * L = 9 * L by ring]
  have hMlt : M + 1 ≤ 2 ^ LM := nat_lt_two_pow_encNat_len M
  rw [hU_eq]
  calc (M + 1) * S_all
    _ ≤ 2 ^ LM * 2 ^ (9 * L) := Nat.mul_le_mul hMlt hSall
    _ = 2 ^ (LM + 9 * L) := by rw [← pow_add]
    _ ≤ 2 ^ (9 * (L + LM)) := Nat.pow_le_pow_right (by decide) (lm_add_9l L LM)

lemma nstar_encNat_bound (I : Instance) (hI : I.Valid) (M : ℕ) :
    (encNat (Nstar I.τ I.d I.k (coeffBoundU I M))).length ≤
      64 * (I.τ * 2 ^ I.d) ^ 3 * ((encInstance I).length + (encNat M).length) ^ 2 := by
  obtain ⟨hL1, _, hkL, _, _, _, _⟩ := instance_dim_bounds I hI
  exact encNat_len_le_of_lt_two_pow
    (nstar_lt_two_pow hI.one_le_d hI.one_le_τ hL1 hkL (coeffBoundU_le_two_pow I hI M))

end IntConeFPT.Section36Proof

open IntConeFPT
open IntConeFPT.Section36Proof

theorem solution (I : Instance) (hI : I.Valid) (M : ℕ) (_hM : 1 ≤ M) :
    (clearIntDesc I).Describes ∧
    (∀ Y : Fin I.τ → Pt I.d I.k,
      (∀ i, (clearIntDesc I).aggLHS Y i ≤ 0) ↔
        ((∑ t, ((Y t).1, (Y t).2.1)) ∈ I.Qhat ∧ Y ∈ I.Ahat)) ∧
    1 ≤ coeffBoundU I M ∧
    (clearIntDesc I).BoundedBy M (coeffBoundU I M) ∧
    (homInstance I).Valid ∧
    (encInstance (homInstance I)).length ≤ (encInstance I).length ∧
    1 ≤ (encInstance I).length ∧
    I.d ≤ (encInstance I).length ∧
    I.k ≤ (encInstance I).length ∧
    I.τ ≤ (encInstance I).length ∧
    (encNat (Nstar I.τ I.d I.k (coeffBoundU I M))).length ≤
      64 * (I.τ * 2 ^ I.d) ^ 3 * ((encInstance I).length + (encNat M).length) ^ 2 := by
  obtain ⟨hV, hLen⟩ := homInstance_valid_and_len I hI
  obtain ⟨hL1, hdL, hkL, hτL, _, _, _⟩ := instance_dim_bounds I hI
  exact ⟨clearIntDesc_describes I, clearIntDesc_hom_iff I, one_le_coeffBoundU I M,
    clearIntDesc_boundedBy I M, hV, hLen, hL1, hdL, hkL, hτL, nstar_encNat_bound I hI M⟩
