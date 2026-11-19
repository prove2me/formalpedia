-- Prove2me | solution 1 for InfoLossLAR.WorstCase.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-18T14:27:02.064087+00:00
-- url     : https://prove2.me/submissions/cf85bb33-f0a2-4bc4-bd01-f150f41e84d7

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

private theorem larFiber {q d r : ℕ} [NeZero q] (hr : r ≤ d)
    (f : (Fin d → ZMod q) → (Fin (d-r) → ZMod q))
    (j : (Fin (d-r) → ZMod q) →+ (Fin d → ZMod q))
    (hf : ∀ x a, f (x + j a) = f x + a) (y : Fin (d-r) → ZMod q) :
    Fintype.card {x // f x = y} = q^r := by
  classical
  let e : {x // f x = y} × (Fin (d-r) → ZMod q) ≃ (Fin d → ZMod q) :=
    { toFun := fun (x,a) => x.val + j a
      invFun := fun x => (⟨x + j (y - f x), by rw [hf]; abel⟩, f x - y)
      left_inv := fun (x,a) => by
        have h := hf x.val a
        simp only [h, x.property, add_sub_cancel_left]
        congr 1
        apply Subtype.ext
        change (x.val + j a) + j (y - (y + a)) = x.val
        have he : y - (y + a) = -a := by abel
        rw [he, map_neg]
        abel
      right_inv := fun x => by
        change x + j (y - f x) + j (f x - y) = x
        rw [add_assoc, ← map_add]
        have he : y - f x + (f x - y) = 0 := by abel
        rw [he, map_zero, add_zero] }
  have h := Fintype.card_congr e
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card] at h
  have he : q ^ d = q ^ r * q ^ (d-r) := by rw [← pow_add, Nat.add_sub_of_le hr]
  rw [he] at h
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.pos_of_ne_zero (NeZero.ne q)) _) h

private theorem larFiberForSmith {q r d : ℕ} [NeZero q] {T : Matrix (Fin d) (Fin d) ℤ}
    (S : SmithData q r d T) (y : Fin (d-r) → ZMod q) :
    Fintype.card {x // S.fT x = y} = q^r := by
  classical
  exact larFiber S.r_le S.fT
    { toFun := S.J.mulVec
      map_zero' := Matrix.mulVec_zero _
      map_add' := Matrix.mulVec_add _ }
    (larEquivariance S) y


private theorem larSurj {q r d : ℕ} [NeZero q] {T : Matrix (Fin d) (Fin d) ℤ}
    (S : SmithData q r d T) : Function.Surjective (fun z => modq q (S.P.mulVec z)) := by
  intro a
  refine ⟨S.U⁻¹.mulVec ((embE r d).mulVec (lift a)), ?_⟩
  have hu : S.U.mulVec (S.U⁻¹.mulVec ((embE r d).mulVec (lift a))) = (embE r d).mulVec (lift a) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ S.U_unimod, Matrix.one_mulVec]
  simp only [SmithData.P, ← Matrix.mulVec_mulVec, hu]
  have he : (embE r d).transpose.mulVec ((embE r d).mulVec (lift a)) = lift a := by
    funext i
    rw [larExtract S.r_le, larEmbed S.r_le]
  rw [he, larModLift]

private theorem larSmithApply {q r d : ℕ} {T : Matrix (Fin d) (Fin d) ℤ}
    (S : SmithData q r d T) (w : Fin d → ℤ) :
    S.U.mulVec (T.mulVec (S.V.mulVec w)) = (smithDiag q r d).mulVec w := by
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, S.smith]

private theorem larTailOf {r d : ℕ} (hr : r ≤ d) (i : Fin d) (hi : ¬ i.val < r) :
    ∃ j : Fin (d-r), larTail hr j = i := by
  refine ⟨⟨i.val-r, by have := i.isLt; omega⟩, Fin.ext ?_⟩
  simp only [larTail]
  omega

private theorem larIntKernel {q r d : ℕ} [NeZero q] {T : Matrix (Fin d) (Fin d) ℤ}
    (S : SmithData q r d T) (z : Fin d → ℤ) : modq q (S.P.mulVec z) = 0 ↔ z ∈ imageLattice T := by
  constructor
  · intro h
    have hex (i : Fin d) (hi : ¬ i.val < r) : (q : ℤ) ∣ S.U.mulVec z i := by
      obtain ⟨j, rfl⟩ := larTailOf S.r_le i hi
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
      have hh := congrFun h j
      simpa only [modq, SmithData.P, ← Matrix.mulVec_mulVec, larExtract S.r_le, Pi.zero_apply] using hh
    let w : Fin d → ℤ := fun i => if i.val < r then S.U.mulVec z i else S.U.mulVec z i / (q : ℤ)
    refine ⟨S.V.mulVec w, ?_⟩
    change T.mulVec (S.V.mulVec w) = z
    apply larUInjective S
    rw [larSmithApply]
    funext i
    by_cases hi : i.val < r
    · simp [smithDiag, Matrix.mulVec_diagonal, w, hi]
    · simp only [smithDiag, Matrix.mulVec_diagonal, w, if_neg hi]
      rw [mul_comm, Int.ediv_mul_cancel (hex i hi)]
  · rintro ⟨w, rfl⟩
    exact larLeftKill S w

private theorem larModZero {q n : ℕ} (v : Fin n → ℤ) : modq q ((q : ℤ) • v) = 0 := by
  funext i
  simp [modq]

private theorem larSpan {q r d : ℕ} [NeZero q] {T : Matrix (Fin d) (Fin d) ℤ}
    (S : SmithData q r d T) :
    Submodule.span (ZMod q) (Set.range fun j : Fin (d-r) => fun i : Fin d => S.J i j) =
      LinearMap.ker (Matrix.mulVecLin (matModq q T)) := by
  change Submodule.span (ZMod q) (Set.range S.J.col) = _
  rw [← Matrix.range_mulVecLin]
  ext x
  change (∃ a, S.J.mulVec a = x) ↔ (matModq q T).mulVec x = 0
  constructor
  · rintro ⟨a,rfl⟩
    have hm : modq q (S.Jint.mulVec (lift a)) = S.J.mulVec a := by
      rw [larModMul, larModLift, SmithData.J]
    rw [← hm, ← larModMul, larDir, larModZero]
  · intro hx
    let w := S.V⁻¹.mulVec (lift x)
    have hv : S.V.mulVec w = lift x := by
      dsimp [w]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ S.V_unimod, Matrix.one_mulVec]
    have hs : modq q ((smithDiag q r d).mulVec w) = 0 := by
      rw [← larSmithApply S, hv, larModMul, larModMul, larModLift, hx, Matrix.mulVec_zero]
    let b : Fin (d-r) → ℤ := fun j => w (larTail S.r_le j)
    have he : modq q ((embE r d).mulVec b) = modq q w := by
      funext i
      by_cases hi : i.val < r
      · have hz : (embE r d).mulVec b i = 0 := by
          unfold Matrix.mulVec dotProduct
          apply Finset.sum_eq_zero
          intro j _
          have hn : i.val ≠ r + j.val := by omega
          simp [embE, hn]
        have hh := congrFun hs i
        simpa [modq, hz, smithDiag, Matrix.mulVec_diagonal, hi] using hh.symm
      · obtain ⟨j,rfl⟩ := larTailOf S.r_le i hi
        simp only [modq, larEmbed S.r_le, b]
    refine ⟨modq q b, ?_⟩
    rw [SmithData.J, ← larModMul, SmithData.Jint, ← Matrix.mulVec_mulVec, larModMul, he,
      ← larModMul, hv, larModLift]

private theorem larIndependent {q r d : ℕ} [NeZero q] {T : Matrix (Fin d) (Fin d) ℤ}
    (S : SmithData q r d T) :
    LinearIndependent (ZMod q) (fun j : Fin (d-r) => fun i : Fin d => S.J i j) := by
  rw [linearIndependent_iff_injective_fintypeLinearCombination]
  intro a b h
  have hm (z : Fin (d-r) → ZMod q) :
      Fintype.linearCombination (ZMod q) (fun j : Fin (d-r) => fun i : Fin d => S.J i j) z = S.J.mulVec z := by
    ext i
    simp [Fintype.linearCombination, Matrix.mulVec, dotProduct, mul_comm]
  rw [hm, hm] at h
  have he := congrArg (fun z => S.fT ((0 : Fin d → ZMod q) + z)) h
  simpa only [larEquivariance, add_right_inj] using he


theorem _root_.solution (q r d : ℕ) [Fact q.Prime] (_hq2 : q ≠ 2) (_hd : 1 ≤ d)
    (T : Matrix (Fin d) (Fin d) ℤ) (S : SmithData q r d T) :
    (∀ x z : Fin d → ℤ, AR q T (x + (q : ℤ) • z) = AR q T x + T.mulVec z) ∧
    Function.Surjective (fun z : Fin d → ℤ => modq q (S.P.mulVec z)) ∧
    (∀ z : Fin d → ℤ, modq q (S.P.mulVec z) = 0 ↔ z ∈ imageLattice T) ∧
    (∀ (x : Fin d → ZMod q) (y : Fin d → ℤ), modq q y = x →
      modq q (S.P.mulVec (AR q T y)) = S.fT x) ∧
    LinearIndependent (ZMod q) (fun j : Fin (d - r) => fun i : Fin d => S.J i j) ∧
    Submodule.span (ZMod q) (Set.range fun j : Fin (d - r) => fun i : Fin d => S.J i j) =
      LinearMap.ker (Matrix.mulVecLin (matModq q T)) ∧
    (∀ (x : Fin d → ZMod q) (a : Fin (d - r) → ZMod q), S.fT (x + S.J.mulVec a) = S.fT x + a) ∧
    (∀ y : Fin (d - r) → ZMod q,
      (Finset.univ.filter fun x : Fin d → ZMod q => S.fT x = y).card = q ^ r) := by
  refine ⟨fun x z => larShift T x _ _ (Matrix.mulVec_smul _ _ _), larSurj S, larIntKernel S,
    ?_, larIndependent S, larSpan S, larEquivariance S, ?_⟩
  · rintro x y rfl
    exact (larLiftIndependent S y).symm
  · intro y
    rw [← Fintype.card_subtype]
    exact larFiberForSmith S y

end InfoLossLAR.WorstCase
