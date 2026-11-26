-- Prove2me | solution 1 for IntConeFPT.fiber_vertex_encoding_bound
-- status  : ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-26T14:25:37.568867+00:00
-- url     : https://prove2.me/submissions/72262c90-89f9-4f3b-9693-a3ddd378d8e0

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Machine
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem
import Definitions.Def_IntConeFPT_Residue
import Theorems.Thm_IntConeFPT_bounded_row_system_dyadic_radius

open OnlineCRS.Combine RobustToDynamics IntConeFPT

namespace FVEB

open Matrix

lemma encNat_len (n : ℕ) : (encNat n).length = n.size := by
  obtain ⟨m, rfl⟩ : ∃ m : Num, (m : ℕ) = n := ⟨n, Num.to_of_nat n⟩
  simp only [encNat, Computability.encodeNat, Num.of_to_nat, List.length_map]
  cases m with
  | zero => rfl
  | pos p =>
      change (Computability.encodePosNum p).length = Nat.size (p : ℕ)
      rw [← PosNum.natSize_to_nat]
      induction p <;> simp_all [Computability.encodePosNum, PosNum.natSize]

lemma lt_pow_len (n : ℕ) : n < 2 ^ (encNat n).length := by
  rw [encNat_len]; exact Nat.lt_size_self n

lemma len_le {n E : ℕ} (h : n ≤ 2 ^ E) : (encNat n).length ≤ E + 1 := by
  rw [encNat_len]; exact Nat.size_le.mpr (by rw [pow_succ]; have := Nat.one_le_two_pow (n := E); omega)

lemma len_flatMap {n : ℕ} (g : Fin n → List Sym) :
    ((List.finRange n).flatMap g).length = ∑ i, (g i).length := by
  rw [List.length_flatMap, Fin.sum_univ_def]

lemma encRat_len (q : ℚ) :
    (encRat q).length = (encNat q.num.natAbs).length + (encNat q.den).length + 2 := by
  simp [encRat, encInt]; omega

lemma encVec_len {k : ℕ} (v : Fin k → ℚ) :
    (encVec v).length = ∑ j, ((encRat (v j)).length + 1) := by
  unfold encVec; rw [len_flatMap]; simp

lemma encMat_len {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) :
    (encMat A).length = ∑ i, ((encVec (A i)).length + 1) := by
  unfold encMat; rw [len_flatMap]; simp

lemma encIntVec_len {d : ℕ} (x : Fin d → ℤ) :
    (encIntVec x).length = ∑ i, ((encNat (x i).natAbs).length + 2) := by
  unfold encIntVec; rw [len_flatMap]; simp [encInt]

lemma prod_le_pow {n : ℕ} (f : Fin n → ℕ) (g : Fin n → ℕ) (h : ∀ i, f i ≤ 2 ^ g i) :
    ∏ i, f i ≤ 2 ^ (∑ i, g i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod' (fun i _ => h i)

lemma den_vec {k : ℕ} (v : Fin k → ℚ) : ∏ j, (v j).den ≤ 2 ^ (encVec v).length := by
  rw [encVec_len]
  apply prod_le_pow
  intro j
  have := lt_pow_len (v j).den
  rw [encRat_len]
  calc (v j).den ≤ 2 ^ (encNat (v j).den).length := this.le
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma den_mat {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) :
    ∏ i, ∏ j, (A i j).den ≤ 2 ^ (encMat A).length := by
  rw [encMat_len]
  apply prod_le_pow
  intro i
  exact (den_vec (A i)).trans (Nat.pow_le_pow_right (by norm_num) (by omega))

lemma single_le_sum {n : ℕ} (g : Fin n → ℕ) (i : Fin n) : g i ≤ ∑ j, g j :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

lemma num_vec {k : ℕ} (v : Fin k → ℚ) (j : Fin k) :
    (v j).num.natAbs < 2 ^ (encVec v).length := by
  have h1 := lt_pow_len (v j).num.natAbs
  have h2 : (encNat (v j).num.natAbs).length ≤ (encVec v).length := by
    rw [encVec_len]
    have := single_le_sum (fun j => (encRat (v j)).length + 1) j
    simp only [encRat_len] at this ⊢
    omega
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) h2)

lemma vec_le_mat {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) (i : Fin p) :
    (encVec (A i)).length + 1 ≤ (encMat A).length := by
  rw [encMat_len]; exact single_le_sum (fun i => (encVec (A i)).length + 1) i

lemma num_mat {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) (i : Fin p) (j : Fin q) :
    (A i j).num.natAbs < 2 ^ (encMat A).length :=
  lt_of_lt_of_le (num_vec (A i) j)
    (Nat.pow_le_pow_right (by norm_num) (by have := vec_le_mat A i; omega))

lemma card_le_vec {k : ℕ} (v : Fin k → ℚ) : k ≤ (encVec v).length := by
  rw [encVec_len]
  calc k = ∑ _j : Fin k, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun _ _ => by omega)

lemma rows_le_mat {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℚ) : p ≤ (encMat A).length := by
  rw [encMat_len]
  calc p = ∑ _j : Fin p, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun _ _ => by omega)

lemma lin_add {k : ℕ} (c x y : Fin k → ℝ) (ε : ℝ) :
    ∑ j, c j * (x j + ε * y j) = ∑ j, c j * x j + ε * ∑ j, c j * y j := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]; congr 1; ext j; ring

lemma lin_sub {k : ℕ} (c x y : Fin k → ℝ) (ε : ℝ) :
    ∑ j, c j * (x j - ε * y j) = ∑ j, c j * x j - ε * ∑ j, c j * y j := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]; congr 1; ext j; ring

lemma extreme_den {m k : ℕ} (a : Matrix (Fin m) (Fin k) ℤ) (β : Fin m → ℤ) (U : ℕ)
    (ha : ∀ i j, (a i j).natAbs ≤ U) (u : Fin k → ℚ)
    (hu : (fun j => (u j : ℝ)) ∈ Set.extremePoints ℝ
      {v : Fin k → ℝ | ∀ i, ∑ j, (a i j : ℝ) * v j ≤ (β i : ℝ)}) :
    ∃ δ : ℤ, δ ≠ 0 ∧ δ.natAbs ≤ k.factorial * (m * U ^ 2) ^ k ∧
      ∀ j, ∃ z : ℤ, (δ : ℚ) * u j = z := by
  classical
  set T := Finset.univ.filter (fun i => ∑ j, (a i j : ℚ) * u j = β i) with hT
  set aT : Matrix (Fin m) (Fin k) ℤ := fun i j => if i ∈ T then a i j else 0 with haT
  set βT : Fin m → ℤ := fun i => if i ∈ T then β i else 0 with hβT
  set N : Matrix (Fin k) (Fin k) ℤ := aT.transpose * aT with hN
  have hfeas := hu.1
  refine ⟨N.det, ?_, ?_, ?_⟩
  · intro h0
    have hR : (N.map (Int.cast : ℤ → ℝ)).det = 0 := by
      have := RingHom.map_det (Int.castRingHom ℝ) N
      rw [h0] at this; simpa using this.symm
    obtain ⟨w, hw0, hNw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hR
    set aR := aT.map (Int.cast : ℤ → ℝ) with haR
    have hmap : N.map (Int.cast : ℤ → ℝ) = aR.transpose * aR := by
      ext j l; simp [hN, haR, Matrix.mul_apply]
    have haw : aR *ᵥ w = 0 := by
      have h1 : (aR *ᵥ w) ⬝ᵥ (aR *ᵥ w) = 0 := by
        have : w ⬝ᵥ (aR.transpose *ᵥ (aR *ᵥ w)) = 0 := by
          rw [Matrix.mulVec_mulVec, ← hmap, hNw]; simp
        rwa [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose] at this
      exact dotProduct_self_eq_zero.mp h1
    have hT0 : ∀ i ∈ T, ∑ j, (a i j : ℝ) * w j = 0 := by
      intro i hi
      have := congrFun haw i
      simp only [Matrix.mulVec, dotProduct, haR, Matrix.map_apply, Pi.zero_apply] at this
      simpa [haT, hi] using this
    have hev : ∀ i, ∀ᶠ ε in nhds (0:ℝ),
        ∑ j, (a i j : ℝ) * ((u j : ℝ) + ε * w j) ≤ β i ∧
        ∑ j, (a i j : ℝ) * ((u j : ℝ) - ε * w j) ≤ β i := by
      intro i
      simp only [lin_add, lin_sub]
      by_cases hi : i ∈ T
      · refine Filter.Eventually.of_forall (fun ε => ?_)
        rw [hT0 i hi]
        have := (Finset.mem_filter.mp hi).2
        have h' : ∑ j, (a i j : ℝ) * (u j : ℝ) = β i := by exact_mod_cast this
        constructor <;> simp [h']
      · have hle := hfeas i
        have hne : ∑ j, (a i j : ℝ) * (u j : ℝ) ≠ β i := by
          intro h; apply hi; rw [Finset.mem_filter]; refine ⟨Finset.mem_univ _, ?_⟩
          exact_mod_cast h
        have hlt := lt_of_le_of_ne hle hne
        set s := ∑ j, (a i j : ℝ) * (u j : ℝ)
        set c := ∑ j, (a i j : ℝ) * w j
        have e1 : ∀ᶠ ε in nhds (0:ℝ), s + ε * c < β i :=
          (Continuous.continuousAt (by fun_prop)).eventually_lt continuousAt_const (by simpa using hlt)
        have e2 : ∀ᶠ ε in nhds (0:ℝ), s - ε * c < β i :=
          (Continuous.continuousAt (by fun_prop)).eventually_lt continuousAt_const (by simpa using hlt)
        filter_upwards [e1, e2] with ε h1 h2 using ⟨h1.le, h2.le⟩
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (Filter.eventually_all.mpr hev)
    have hε := hball (y := δ / 2) (by rw [Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)
    have hm1 : (fun j => (u j : ℝ)) - (δ / 2) • w ∈
        {v : Fin k → ℝ | ∀ i, ∑ j, (a i j : ℝ) * v j ≤ (β i : ℝ)} := by
      intro i; simpa using (hε i).2
    have hm2 : (fun j => (u j : ℝ)) + (δ / 2) • w ∈
        {v : Fin k → ℝ | ∀ i, ∑ j, (a i j : ℝ) * v j ≤ (β i : ℝ)} := by
      intro i; simpa using (hε i).1
    have hseg : (fun j => (u j : ℝ)) ∈ openSegment ℝ ((fun j => (u j : ℝ)) - (δ / 2) • w)
        ((fun j => (u j : ℝ)) + (δ / 2) • w) := by
      refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
      ext j; simp; ring
    have := ((mem_extremePoints.mp hu).2 _ hm1 _ hm2 hseg).1
    have : (δ / 2) • w = 0 := by
      have h := congrArg (fun v => (fun j => (u j : ℝ)) - v) this
      simpa using h
    rcases smul_eq_zero.mp this with h | h
    · linarith
    · exact hw0 h
  · have hb : ∀ j l, |N j l| ≤ ((m * U ^ 2 : ℕ) : ℤ) := by
      intro j l
      simp only [hN, Matrix.mul_apply, Matrix.transpose_apply]
      calc |∑ i, aT i j * aT i l| ≤ ∑ i, |aT i j * aT i l| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin m, ((U ^ 2 : ℕ) : ℤ) := by
          apply Finset.sum_le_sum; intro i _
          rw [abs_mul]
          have h1 : |aT i j| ≤ U := by
            simp only [haT]; split_ifs
            · rw [Int.abs_eq_natAbs]; exact_mod_cast ha i j
            · simp
          have h2 : |aT i l| ≤ U := by
            simp only [haT]; split_ifs
            · rw [Int.abs_eq_natAbs]; exact_mod_cast ha i l
            · simp
          push_cast
          nlinarith [abs_nonneg (aT i j), abs_nonneg (aT i l)]
        _ = _ := by simp
    have := Matrix.det_le (abv := AbsoluteValue.abs) hb
    simp only [Fintype.card_fin, AbsoluteValue.abs_apply, nsmul_eq_mul] at this
    rw [← Int.natCast_natAbs] at this
    exact_mod_cast this
  · have hcast : ∀ (M : Matrix (Fin k) (Fin k) ℤ) (v : Fin k → ℤ),
        (M.map (Int.cast : ℤ → ℚ)) *ᵥ (fun j => (v j : ℚ)) = fun j => ((M *ᵥ v) j : ℚ) := by
      intro M v; ext j; simp [Matrix.mulVec, dotProduct]
    set aQ := aT.map (Int.cast : ℤ → ℚ) with haQ
    have h1 : aQ *ᵥ u = fun i => (βT i : ℚ) := by
      ext i
      simp only [Matrix.mulVec, dotProduct, haQ, Matrix.map_apply]
      by_cases hi : i ∈ T
      · simp only [haT, hβT, hi, if_true]; exact (Finset.mem_filter.mp hi).2
      · simp [haT, hβT, hi]
    have h2 : (N.map (Int.cast : ℤ → ℚ)) *ᵥ u = fun j => ((aT.transpose *ᵥ βT) j : ℚ) := by
      have : N.map (Int.cast : ℤ → ℚ) = aQ.transpose * aQ := by
        ext j l; simp [hN, haQ, Matrix.mul_apply]
      rw [this, ← Matrix.mulVec_mulVec, h1]
      ext j; simp [Matrix.mulVec, dotProduct, haQ]
    have h3 : (N.det : ℚ) • u = fun j => ((N.adjugate *ᵥ (aT.transpose *ᵥ βT)) j : ℚ) := by
      have hadj := RingHom.map_adjugate (Int.castRingHom ℚ) N
      have hdet := RingHom.map_det (Int.castRingHom ℚ) N
      simp only [RingHom.mapMatrix_apply, Int.coe_castRingHom] at hadj hdet
      rw [← hcast, ← h2, hadj, Matrix.mulVec_mulVec, Matrix.adjugate_mul, hdet,
        Matrix.smul_mulVec, Matrix.one_mulVec]
    intro j
    exact ⟨_, by simpa using congrFun h3 j⟩

lemma int_mul (q : ℚ) (D : ℕ) (h : q.den ∣ D) :
    ∃ z : ℤ, (D : ℚ) * q = z ∧ z.natAbs ≤ D * q.num.natAbs := by
  obtain ⟨c, rfl⟩ := h
  refine ⟨c * q.num, ?_, ?_⟩
  · push_cast
    rw [mul_comm (q.den : ℚ) c, mul_assoc, mul_comm (q.den : ℚ) q, Rat.mul_den_eq_num]
  · rw [Int.natAbs_mul, Int.natAbs_natCast]
    have := q.den_pos
    exact Nat.mul_le_mul_right _ (by nlinarith)

lemma rat_bound (q : ℚ) (δ z : ℤ) (hδ : δ ≠ 0) (h : (δ : ℚ) * q = z) :
    q.den ≤ δ.natAbs ∧ q.num.natAbs ≤ z.natAbs := by
  have hq : q = Rat.divInt z δ := by
    rw [Rat.divInt_eq_div, ← h]; field_simp
  constructor
  · have := Rat.den_dvd z δ
    rw [← hq] at this
    have h2 : q.den ∣ δ.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr this; simpa using this
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr hδ) h2
  · have := Rat.num_dvd z hδ
    rw [← hq] at this
    rcases eq_or_ne z 0 with hz | hz
    · subst hz; simp at hq; simp [hq]
    · exact Nat.le_of_dvd (Int.natAbs_pos.mpr hz) (Int.natAbs_dvd_natAbs.mpr this)

private theorem block_le {α β : Type} (f : α → List β) {x : α} {xs : List α}
    (hx : x ∈ xs) : (f x).length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp hx with rfl | h
    · omega
    · have := ih h
      omega


/-- The polytope of a row system. -/
def PS {m d k : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (B : Matrix (Fin m) (Fin k) ℚ) (b : Fin m → ℚ) :
    Set ((Fin d → ℝ) × (Fin k → ℝ)) :=
  {p | ∀ i, (∑ j, (A i j : ℝ) * p.1 j) + (∑ j, (B i j : ℝ) * p.2 j) ≤ (b i : ℝ)}

lemma fiber_scale {m d k : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (B : Matrix (Fin m) (Fin k) ℚ)
    (b : Fin m → ℚ) (x : Fin d → ℤ) (D : ℕ) (hDpos : 0 < D)
    (α : Fin m → Fin d → ℤ) (bB : Fin m → Fin k → ℤ) (γ : Fin m → ℤ)
    (hα : ∀ i j, (D : ℚ) * A i j = α i j) (hbB : ∀ i j, (D : ℚ) * B i j = bB i j)
    (hγ : ∀ i, (D : ℚ) * b i = γ i) :
    {v : Fin k → ℝ | ((fun i => (x i : ℝ)), v) ∈ PS A B b} =
      {v | ∀ i, ∑ j, (bB i j : ℝ) * v j ≤ ((γ i - ∑ j, α i j * x j : ℤ) : ℝ)} := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
  ext v
  simp only [PS, Set.mem_setOf_eq]
  apply forall_congr'
  intro i
  have cB : ∀ j, (bB i j : ℝ) = (D : ℝ) * (B i j : ℝ) := by
    intro j; have := congrArg (Rat.cast : ℚ → ℝ) (hbB i j); push_cast at this
    exact this.symm
  have cA : ∀ j, (α i j : ℝ) = (D : ℝ) * (A i j : ℝ) := by
    intro j; have := congrArg (Rat.cast : ℚ → ℝ) (hα i j); push_cast at this
    exact this.symm
  have cb : (γ i : ℝ) = (D : ℝ) * (b i : ℝ) := by
    have := congrArg (Rat.cast : ℚ → ℝ) (hγ i); push_cast at this
    exact this.symm
  have e1 : ∑ j, (bB i j : ℝ) * v j = D * ∑ j, (B i j : ℝ) * v j := by
    rw [Finset.mul_sum]; congr 1; ext j; rw [cB]; ring
  have e2 : ((γ i - ∑ j, α i j * x j : ℤ) : ℝ) =
      D * ((b i : ℝ) - ∑ j, (A i j : ℝ) * (x j : ℝ)) := by
    push_cast
    rw [cb, mul_sub, Finset.mul_sum]; congr 1; congr 1; ext j; rw [cA]; ring
  rw [e1, e2, mul_le_mul_iff_of_pos_left hDR]
  constructor <;> intro h <;> linarith

lemma delta_bound (ℓ k m : ℕ) (hk : k ≤ ℓ) (hm : m ≤ ℓ) (δ : ℤ)
    (hδb : δ.natAbs ≤ k.factorial * (m * (2 ^ (2 * ℓ)) ^ 2) ^ k) :
    δ.natAbs ≤ 2 ^ (6 * ℓ * ℓ) := by
  have f1 : k.factorial ≤ 2 ^ (ℓ * ℓ) := by
    calc k.factorial ≤ k ^ k := Nat.factorial_le_pow _
      _ ≤ ℓ ^ ℓ := by
        rcases Nat.eq_zero_or_pos k with h | h
        · subst h; rw [pow_zero]
          rcases Nat.eq_zero_or_pos ℓ with h' | h'
          · simp [h']
          · exact Nat.one_le_pow _ _ h'
        · exact (Nat.pow_le_pow_left hk _).trans (Nat.pow_le_pow_right (by omega) hk)
      _ ≤ (2 ^ ℓ) ^ ℓ := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
      _ = 2 ^ (ℓ * ℓ) := by rw [← pow_mul]
  have f2 : m * (2 ^ (2 * ℓ)) ^ 2 ≤ 2 ^ (5 * ℓ) := by
    calc m * (2 ^ (2 * ℓ)) ^ 2 ≤ 2 ^ ℓ * (2 ^ (2 * ℓ)) ^ 2 :=
          Nat.mul_le_mul_right _ (hm.trans (Nat.lt_two_pow_self).le)
      _ = 2 ^ (5 * ℓ) := by rw [← pow_mul, ← pow_add]; ring_nf
  have f3 : (m * (2 ^ (2 * ℓ)) ^ 2) ^ k ≤ 2 ^ (5 * ℓ * ℓ) := by
    calc _ ≤ (2 ^ (5 * ℓ)) ^ k := Nat.pow_le_pow_left f2 _
      _ ≤ (2 ^ (5 * ℓ)) ^ ℓ := Nat.pow_le_pow_right (Nat.one_le_two_pow) hk
      _ = _ := by rw [← pow_mul]
  calc δ.natAbs ≤ _ := hδb
    _ ≤ 2 ^ (ℓ * ℓ) * 2 ^ (5 * ℓ * ℓ) := Nat.mul_le_mul f1 f3
    _ = 2 ^ (6 * ℓ * ℓ) := by rw [← pow_add]; ring_nf

lemma final_arith (a ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ℓ * (2 * (1 + ℓ) ^ a + 12 * ℓ * ℓ + 8) ≤ (1 + ℓ) ^ (a + 8) := by
  have hn : 2 ≤ 1 + ℓ := by omega
  have p1 : (1 + ℓ) ^ a ≤ (1 + ℓ) ^ (a + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have p2 : (1 + ℓ) ^ 2 ≤ (1 + ℓ) ^ (a + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have p3 : 1 ≤ (1 + ℓ) ^ (a + 2) := Nat.one_le_pow _ _ (by omega)
  have p4 : 32 ≤ (1 + ℓ) ^ 5 := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ (1 + ℓ) ^ 5 := Nat.pow_le_pow_left hn 5
  have hll : ℓ * ℓ ≤ (1 + ℓ) ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have e : (1 + ℓ) ^ (a + 8) = (1 + ℓ) * ((1 + ℓ) ^ 5 * (1 + ℓ) ^ (a + 2)) := by
    rw [← pow_add, ← pow_succ']; ring_nf
  rw [e]
  have q1 : 2 * (1 + ℓ) ^ a + 12 * ℓ * ℓ + 8 ≤ 22 * (1 + ℓ) ^ (a + 2) := by
    have : 12 * ℓ * ℓ = 12 * (ℓ * ℓ) := by ring
    omega
  calc ℓ * (2 * (1 + ℓ) ^ a + 12 * ℓ * ℓ + 8) ≤ (1 + ℓ) * (22 * (1 + ℓ) ^ (a + 2)) :=
        Nat.mul_le_mul (by omega) q1
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))

lemma coord_bound (u : ℚ) (δ : ℤ) (hδ0 : δ ≠ 0) (R E : ℕ) (hδ : δ.natAbs ≤ 2 ^ E)
    (hub : |u| ≤ (2 ^ R : ℚ)) (hz : ∃ z : ℤ, (δ : ℚ) * u = z) :
    (encRat u).length + 1 ≤ R + 2 * E + 5 := by
  obtain ⟨z, hzj⟩ := hz
  obtain ⟨hden, hnum⟩ := rat_bound u δ z hδ0 hzj
  have hzb : z.natAbs ≤ 2 ^ E * 2 ^ R := by
    have h1 : |(z : ℚ)| ≤ |(δ : ℚ)| * 2 ^ R := by
      rw [← hzj, abs_mul]
      exact mul_le_mul_of_nonneg_left hub (abs_nonneg _)
    have h2 : |z| ≤ |δ| * 2 ^ R := by
      rw [← Int.cast_abs, ← Int.cast_abs] at h1; exact_mod_cast h1
    rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at h2
    have h3 : z.natAbs ≤ δ.natAbs * 2 ^ R := by exact_mod_cast h2
    exact h3.trans (Nat.mul_le_mul_right _ hδ)
  have l1 := len_le (n := u.num.natAbs) (E := E + R) (by rw [pow_add]; omega)
  have l2 := len_le (n := u.den) (E := E) (by omega)
  rw [encRat_len]
  omega

lemma core (a : ℕ) {m d k : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (B : Matrix (Fin m) (Fin k) ℚ)
    (b : Fin m → ℚ) (hd1 : 1 ≤ d)
    (hbox : ∀ p ∈ PS A B b,
      InBox (2 ^ ((1 + (encMat A ++ encMat B ++ encVec b).length) ^ a)) p)
    (x : Fin d → ℤ) (u : Fin k → ℚ)
    (hP : ((fun i => (x i : ℝ)), (fun j => (u j : ℝ))) ∈ PS A B b)
    (hext : (fun j => (u j : ℝ)) ∈ Set.extremePoints ℝ
      {v : Fin k → ℝ | ((fun i => (x i : ℝ)), v) ∈ PS A B b}) :
    (encGen x u).length ≤ (1 + (encMat A ++ encMat B ++ encVec b).length) ^ (a + 8) := by
  classical
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ, ℓ = (encMat A ++ encMat B ++ encVec b).length := ⟨_, rfl⟩
  rw [← hℓdef] at hbox ⊢
  obtain ⟨R, hR⟩ : ∃ R, R = (1 + ℓ) ^ a := ⟨_, rfl⟩
  rw [← hR] at hbox
  have hb0 := hbox _ hP
  have hxb : ∀ i, (x i).natAbs ≤ 2 ^ R := by
    intro i
    have h := hb0.1 i
    simp only at h
    rw [← Int.cast_abs] at h
    have h2 : |x i| ≤ ((2 ^ R : ℕ) : ℤ) := by exact_mod_cast h
    rw [Int.abs_eq_natAbs] at h2; exact_mod_cast h2
  have hub : ∀ j, |u j| ≤ (2 ^ R : ℚ) := by
    intro j
    have h := hb0.2 j
    simp only at h
    rw [← Rat.cast_abs] at h
    exact_mod_cast h
  have hm : 0 < m := by
    by_contra h0
    have h0' : m = 0 := by omega
    subst h0'
    have hp : ((fun _ => ((2 ^ R : ℕ) : ℝ) + 1, 0) : (Fin d → ℝ) × (Fin k → ℝ)) ∈ PS A B b := by
      intro i; exact i.elim0
    have := (hbox _ hp).1 ⟨0, hd1⟩
    simp only at this
    rw [abs_of_pos (by positivity)] at this
    linarith
  have hℓsplit : ℓ = (encMat A).length + (encMat B).length + (encVec b).length := by
    simp [hℓdef]; omega
  have hd : d ≤ ℓ := by
    have := card_le_vec (A ⟨0, hm⟩)
    have := vec_le_mat A ⟨0, hm⟩
    omega
  have hk : k ≤ ℓ := by
    have := card_le_vec (B ⟨0, hm⟩)
    have := vec_le_mat B ⟨0, hm⟩
    omega
  have hmℓ : m ≤ ℓ := by
    have := rows_le_mat A; omega
  obtain ⟨D, hDdef⟩ : ∃ D, D = (∏ i, ∏ j, (A i j).den) * (∏ i, ∏ j, (B i j).den) *
      ∏ i, (b i).den := ⟨_, rfl⟩
  have hD : D ≤ 2 ^ ℓ := by
    rw [hDdef, hℓsplit, pow_add, pow_add]
    exact Nat.mul_le_mul (Nat.mul_le_mul (den_mat _) (den_mat _)) (den_vec _)
  have hDpos : 0 < D := by
    rw [hDdef]
    apply Nat.mul_pos (Nat.mul_pos _ _) _
    · exact Finset.prod_pos (fun _ _ => Finset.prod_pos (fun _ _ => Rat.den_pos _))
    · exact Finset.prod_pos (fun _ _ => Finset.prod_pos (fun _ _ => Rat.den_pos _))
    · exact Finset.prod_pos (fun _ _ => Rat.den_pos _)
  have dA : ∀ i j, (A i j).den ∣ D := fun i j => by
    rw [hDdef]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_trans
      (Finset.dvd_prod_of_mem (fun j => (A i j).den) (Finset.mem_univ j))
      (Finset.dvd_prod_of_mem (fun i => ∏ j, (A i j).den) (Finset.mem_univ i))) _) _
  have dB : ∀ i j, (B i j).den ∣ D := fun i j => by
    rw [hDdef]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_trans
      (Finset.dvd_prod_of_mem (fun j => (B i j).den) (Finset.mem_univ j))
      (Finset.dvd_prod_of_mem (fun i => ∏ j, (B i j).den) (Finset.mem_univ i))) _) _
  have db : ∀ i, (b i).den ∣ D := fun i => by
    rw [hDdef]
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun i => (b i).den) (Finset.mem_univ i)) _
  choose α hα using fun i j => int_mul (A i j) D (dA i j)
  choose bB hbB using fun i j => int_mul (B i j) D (dB i j)
  choose γ hγ using fun i => int_mul (b i) D (db i)
  have hfib := fiber_scale A B b x D hDpos α bB γ (fun i j => (hα i j).1) (fun i j => (hbB i j).1)
    (fun i => (hγ i).1)
  have hbU : ∀ i j, (bB i j).natAbs ≤ 2 ^ (2 * ℓ) := by
    intro i j
    have h1 := (hbB i j).2
    have h2 := num_mat B i j
    have h4 : 2 ^ (encMat B).length ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc (bB i j).natAbs ≤ D * (B i j).num.natAbs := h1
      _ ≤ 2 ^ ℓ * 2 ^ ℓ := Nat.mul_le_mul hD (by omega)
      _ = 2 ^ (2 * ℓ) := by rw [← pow_add]; ring_nf
  rw [hfib] at hext
  obtain ⟨δ, hδ0, hδb, hz⟩ := extreme_den (Matrix.of bB) (fun i => γ i - ∑ j, α i j * x j)
    (2 ^ (2 * ℓ)) hbU u hext
  have hδ := delta_bound ℓ k m hk hmℓ δ hδb
  have hu_enc : ∀ j, (encRat (u j)).length + 1 ≤ R + 12 * ℓ * ℓ + 5 := by
    intro j
    have := coord_bound (u j) δ hδ0 R (6 * ℓ * ℓ) hδ (hub j) (hz j)
    have e : 2 * (6 * ℓ * ℓ) = 12 * ℓ * ℓ := by ring
    omega
  have hx_enc : ∀ i, (encNat (x i).natAbs).length + 2 ≤ R + 3 := by
    intro i; have := len_le (hxb i); omega
  have htot : (encGen x u).length ≤ ℓ * (2 * R + 12 * ℓ * ℓ + 8) := by
    unfold encGen
    rw [List.length_append, encIntVec_len, encVec_len]
    have s1 : ∑ i, ((encNat (x i).natAbs).length + 2) ≤ ℓ * (R + 3) :=
      calc _ ≤ ∑ _i : Fin d, (R + 3) := Finset.sum_le_sum (fun i _ => hx_enc i)
        _ = d * (R + 3) := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ hd
    have s2 : ∑ j, ((encRat (u j)).length + 1) ≤ ℓ * (R + 12 * ℓ * ℓ + 5) :=
      calc _ ≤ ∑ _j : Fin k, (R + 12 * ℓ * ℓ + 5) := Finset.sum_le_sum (fun j _ => hu_enc j)
        _ = k * (R + 12 * ℓ * ℓ + 5) := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ hk
    have : ℓ * (R + 3) + ℓ * (R + 12 * ℓ * ℓ + 5) = ℓ * (2 * R + 12 * ℓ * ℓ + 8) := by ring
    omega
  rw [hR] at htot
  exact htot.trans (final_arith a ℓ (by omega))

end FVEB

open FVEB

theorem solution :
    ∃ C : ℕ, ∀ I : Instance, I.Valid →
      ∀ (t : Fin I.τ) (r : Residue I.d) (x : Fin I.d → ℤ) (u : Fin I.k → ℚ),
        ratGen x u ∈ I.Vr t r → (encGen x u).length ≤ (encInstance I).length ^ C := by
  obtain ⟨a, geom⟩ := bounded_row_system_dyadic_radius
  refine ⟨a + 8, ?_⟩
  intro I hI t r x u hV
  have hs : 1 + (encMat (I.Aloc t) ++ encMat (I.Bloc t) ++ encVec (I.bloc t)).length ≤
      (encInstance I).length := by
    let f := fun t => encNat (I.m t) ++ [3] ++ encMat (I.Aloc t) ++ encMat (I.Bloc t) ++
      encVec (I.bloc t) ++ [3] ++ encNat (I.deg t) ++ [3] ++ encVec (I.coeff t) ++ [3]
    have hh := block_le f (List.mem_finRange t)
    simp only [encInstance, List.length_append, List.length_cons, List.length_nil]
    dsimp [f] at hh
    simp only [List.length_append, List.length_cons, List.length_nil] at hh
    omega
  have hc := core a (I.Aloc t) (I.Bloc t) (I.bloc t) hI.one_le_d
    (fun p hp => geom (I.Aloc t) (I.Bloc t) (I.bloc t) (hI.bounded t) p hp) x u hV.1.1 hV.2
  exact hc.trans (Nat.pow_le_pow_left hs _)
