-- Prove2me | solution 1 for InfoLossLAR.WorstCase.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-18T15:09:12.162705+00:00
-- url     : https://prove2.me/submissions/116f9277-14ee-4ef0-ad3c-ee87f6c3939a

import Definitions.Def_InfoLossLAR_WorstCase_Rounding


set_option autoImplicit false
namespace InfoLossLAR.WorstCase

private theorem larShift {q d : ℕ} [NeZero q] (T : Matrix (Fin d) (Fin d) ℤ)
    (x y c : Fin d → ℤ) (h : T.mulVec y = (q : ℤ) • c) :
    AR q T (x + y) = AR q T x + c := by
  funext i
  simp only [AR, carry, Matrix.mulVec_add, h, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Int.cast_add, Int.cast_mul, Int.cast_natCast]
  have hq : (q : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne q
  rw [show (((T.mulVec x i : ℤ) : ℚ) + (q : ℚ) * (c i : ℚ)) / (q : ℚ) =
    ((T.mulVec x i : ℤ) : ℚ) / (q : ℚ) + (c i : ℚ) by field_simp]
  exact Int.floor_add_intCast _ _

private theorem larModMul {q m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (x : Fin n → ℤ) :
    modq q (A.mulVec x) = (matModq q A).mulVec (modq q x) := by
  funext i
  simp [modq, matModq, Matrix.mulVec, dotProduct]

private theorem larModAdd {q n : ℕ} (x y : Fin n → ℤ) :
    modq q (x + y) = modq q x + modq q y := by
  ext i
  simp [modq]

private theorem larModLift {q n : ℕ} [NeZero q] (x : Fin n → ZMod q) :
    modq q (lift x) = x := by
  funext i
  simp [modq, lift]

private theorem larLiftDiff {q n : ℕ} (x y : Fin n → ℤ) (h : modq q x = modq q y) :
    ∃ z : Fin n → ℤ, x = y + (q : ℤ) • z := by
  have hd (i : Fin n) : (q : ℤ) ∣ x i - y i := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
    rw [Int.cast_sub, show (x i : ZMod q) = (y i : ZMod q) from congrFun h i, sub_self]
  choose z hz using hd
  refine ⟨z, funext fun i => ?_⟩
  simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_comm] using sub_eq_iff_eq_add.mp (hz i)

private def larTail {r d : ℕ} (h : r ≤ d) (i : Fin (d-r)) : Fin d :=
  ⟨r + i.val, by have := i.isLt; omega⟩

private theorem larExtract {r d : ℕ} (h : r ≤ d) (x : Fin d → ℤ) (i : Fin (d-r)) :
    (embE r d).transpose.mulVec x i = x (larTail h i) := by
  classical
  unfold Matrix.mulVec dotProduct
  rw [Finset.sum_eq_single (larTail h i)]
  · simp [embE, larTail]
  · intro b _ hb
    have hn : b.val ≠ r + i.val := fun he => hb (Fin.ext he)
    simp [embE, hn]
  · simp

private theorem larEmbed {r d : ℕ} (h : r ≤ d) (x : Fin (d-r) → ℤ) (i : Fin (d-r)) :
    (embE r d).mulVec x (larTail h i) = x i := by
  classical
  unfold Matrix.mulVec dotProduct
  rw [Finset.sum_eq_single i]
  · simp [embE, larTail]
  · intro b _ hb
    have hn : i.val ≠ b.val := fun he => hb (Fin.ext he.symm)
    simp [embE, larTail, hn]
  · simp

private theorem larDiagEmbed (q r d : ℕ) (a : Fin (d-r) → ℤ) :
    (smithDiag q r d).mulVec ((embE r d).mulVec a) = (q : ℤ) • ((embE r d).mulVec a) := by
  classical
  funext i
  simp only [smithDiag, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i.val < r
  · have hz : (embE r d).mulVec a i = 0 := by
      unfold Matrix.mulVec dotProduct
      apply Finset.sum_eq_zero
      intro j _
      have hn : i.val ≠ r + j.val := by omega
      simp [embE, hn]
    simp [hi, hz]
  · simp [hi]

private theorem larUInjective {q r d : ℕ} {T : Matrix (Fin d) (Fin d) ℤ}
    (S : SmithData q r d T) : Function.Injective S.U.mulVec := by
  intro x y h
  have hh := congrArg (fun z => S.U⁻¹.mulVec z) h
  simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ S.U_unimod, Matrix.one_mulVec] using hh

private theorem larLeftKill {q r d : ℕ} {T : Matrix (Fin d) (Fin d) ℤ}
    (S : SmithData q r d T) (z : Fin d → ℤ) : modq q (S.P.mulVec (T.mulVec z)) = 0 := by
  have hv : S.V.mulVec (S.V⁻¹.mulVec z) = z := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ S.V_unimod, Matrix.one_mulVec]
  have hs : S.U.mulVec (T.mulVec z) = (smithDiag q r d).mulVec (S.V⁻¹.mulVec z) := by
    conv_lhs => rw [← hv]
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, S.smith]
  funext i
  simp only [modq, SmithData.P, ← Matrix.mulVec_mulVec, hs, larExtract S.r_le, smithDiag,
    Matrix.mulVec_diagonal, Pi.zero_apply]
  have hh : ¬ (larTail S.r_le i).val < r := by simp [larTail]
  simp [hh]

private theorem larDir {q r d : ℕ} {T : Matrix (Fin d) (Fin d) ℤ}
    (S : SmithData q r d T) (a : Fin (d-r) → ℤ) :
    T.mulVec (S.Jint.mulVec a) = (q : ℤ) • (S.U⁻¹.mulVec ((embE r d).mulVec a)) := by
  apply larUInjective S
  have hu : S.U.mulVec (S.U⁻¹.mulVec ((embE r d).mulVec a)) = (embE r d).mulVec a := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ S.U_unimod, Matrix.one_mulVec]
  rw [Matrix.mulVec_smul, hu, ← larDiagEmbed]
  simp only [SmithData.Jint, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, S.smith]

private theorem larLiftIndependent {q r d : ℕ} [NeZero q] {T : Matrix (Fin d) (Fin d) ℤ}
    (S : SmithData q r d T) (x : Fin d → ℤ) : S.fT (modq q x) = modq q (S.P.mulVec (AR q T x)) := by
  obtain ⟨z,hz⟩ := larLiftDiff (lift (modq q x)) x (larModLift _)
  unfold SmithData.fT
  rw [hz, larShift T x _ (T.mulVec z) (Matrix.mulVec_smul _ _ _), Matrix.mulVec_add,
    larModAdd, larLeftKill S, add_zero]

private theorem larEquivariance {q r d : ℕ} [NeZero q] {T : Matrix (Fin d) (Fin d) ℤ}
    (S : SmithData q r d T) (x : Fin d → ZMod q) (a : Fin (d-r) → ZMod q) :
    S.fT (x + S.J.mulVec a) = S.fT x + a := by
  have hm : modq q (lift x + S.Jint.mulVec (lift a)) = x + S.J.mulVec a := by
    rw [larModAdd, larModMul, larModLift, larModLift, SmithData.J]
  rw [← hm, larLiftIndependent, larShift T _ _ _ (larDir S _), Matrix.mulVec_add, larModAdd]
  change S.fT x + _ = _
  congr 1
  have h : S.P.mulVec (S.U⁻¹.mulVec ((embE r d).mulVec (lift a))) = lift a := by
    unfold SmithData.P
    rw [← Matrix.mulVec_mulVec]
    have hu : S.U.mulVec (S.U⁻¹.mulVec ((embE r d).mulVec (lift a))) = (embE r d).mulVec (lift a) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ S.U_unimod, Matrix.one_mulVec]
    rw [hu]
    funext i
    rw [larExtract S.r_le, larEmbed S.r_le]
  rw [h, larModLift]

theorem _root_.solution (q r d : ℕ) [Fact q.Prime] (_hq2 : q ≠ 2)
    (T : Matrix (Fin d) (Fin d) ℤ) (S : SmithData q r d T) (_hℓ : r < d) :
    Function.Bijective
      (fun p : S.zeroFiber × (Fin (d - r) → ZMod q) => (p.1 : Fin d → ZMod q) + S.J.mulVec p.2) ∧
    ∀ (x : Fin d → ZMod q) (p : S.zeroFiber × (Fin (d - r) → ZMod q)),
      (p.1 : Fin d → ZMod q) + S.J.mulVec p.2 = x ↔
        ((p.1 : Fin d → ZMod q) = x - S.J.mulVec (S.fT x) ∧ p.2 = S.fT x) := by
  have hf (e : S.zeroFiber) (y : Fin (d - r) → ZMod q) :
      S.fT ((e : Fin d → ZMod q) + S.J.mulVec y) = y := by
    have hz : S.fT (e : Fin d → ZMod q) = 0 := e.property
    rw [larEquivariance, hz, zero_add]
  have hinv (x : Fin d → ZMod q) : S.fT (x - S.J.mulVec (S.fT x)) = 0 := by
    rw [sub_eq_add_neg, ← Matrix.mulVec_neg, larEquivariance, add_neg_cancel]
  have hiff (x : Fin d → ZMod q) (p : S.zeroFiber × (Fin (d - r) → ZMod q)) :
      (p.1 : Fin d → ZMod q) + S.J.mulVec p.2 = x ↔
        ((p.1 : Fin d → ZMod q) = x - S.J.mulVec (S.fT x) ∧ p.2 = S.fT x) := by
    constructor
    · intro h
      have hy : p.2 = S.fT x := (hf p.1 p.2).symm.trans (congrArg S.fT h)
      exact ⟨eq_sub_of_add_eq (by simpa only [hy] using h), hy⟩
    · rintro ⟨he, hy⟩
      rw [he, hy, sub_add_cancel]
  refine ⟨⟨?_, ?_⟩, hiff⟩
  · intro p p' h
    have ht := (hiff _ p).1 h
    have ht' := (hiff _ p').1 rfl
    exact Prod.ext (Subtype.ext (ht.1.trans ht'.1.symm)) (ht.2.trans ht'.2.symm)
  · intro x
    exact ⟨(⟨x - S.J.mulVec (S.fT x), hinv x⟩, S.fT x), (hiff _ _).2 ⟨rfl, rfl⟩⟩

end InfoLossLAR.WorstCase
