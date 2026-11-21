-- Prove2me | solution 1 for HeisenbergRep.Knill.stabilizer_abelian_elementary
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:55:44.185177+00:00
-- url     : https://prove2.me/submissions/a711ed49-dc55-4503-97db-103fdda5c821

import Mathlib
import Definitions.Def_HeisenbergRep_Knill_stabilizerOf

namespace Aux_HeisenbergRep_Knill_stabilizer_abelian_elementary

open QAlgorithms QAlgorithms.Stabilizer Matrix

lemma Ipow_mod (k : ℕ) : Complex.I ^ k = Complex.I ^ (k % 4) := by
  have h := Nat.mod_add_div k 4
  calc Complex.I ^ k = Complex.I ^ (k % 4 + 4 * (k / 4)) := by rw [h]
    _ = Complex.I ^ (k % 4) := by rw [pow_add, pow_mul, Complex.I_pow_four, one_pow, mul_one]

lemma Ipow_add (a b : ZMod 4) :
    Complex.I ^ (a + b).val = Complex.I ^ a.val * Complex.I ^ b.val := by
  rw [ZMod.val_add, ← Ipow_mod, pow_add]

lemma Ipow_sum {ι : Type*} (s : Finset ι) (c : ι → ZMod 4) :
    ∏ q ∈ s, Complex.I ^ (c q).val = Complex.I ^ (∑ q ∈ s, c q).val := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, Ipow_add, ih]

lemma mXX : Pauli.mul .X .X = (0, .I) := rfl
lemma mYY : Pauli.mul .Y .Y = (0, .I) := rfl
lemma mZZ : Pauli.mul .Z .Z = (0, .I) := rfl
lemma mII : Pauli.mul .I .I = (0, .I) := rfl
lemma mIX : Pauli.mul .I .X = (0, .X) := rfl
lemma mIY : Pauli.mul .I .Y = (0, .Y) := rfl
lemma mIZ : Pauli.mul .I .Z = (0, .Z) := rfl
lemma mXI : Pauli.mul .X .I = (0, .X) := rfl
lemma mYI : Pauli.mul .Y .I = (0, .Y) := rfl
lemma mZI : Pauli.mul .Z .I = (0, .Z) := rfl
lemma mXY : Pauli.mul .X .Y = (1, .Z) := rfl
lemma mYX : Pauli.mul .Y .X = (3, .Z) := rfl
lemma mYZ : Pauli.mul .Y .Z = (1, .X) := rfl
lemma mZY : Pauli.mul .Z .Y = (3, .X) := rfl
lemma mZX : Pauli.mul .Z .X = (1, .Y) := rfl
lemma mXZ : Pauli.mul .X .Z = (3, .Y) := rfl

lemma pauli_single (p q : Pauli) (a b : Bool) :
    (p.mat * q.mat) a b = Complex.I ^ (Pauli.mul p q).1.val * (Pauli.mul p q).2.mat a b := by
  have v0 : (0 : ZMod 4).val = 0 := rfl
  have v1 : (1 : ZMod 4).val = 1 := rfl
  have v3 : (3 : ZMod 4).val = 3 := rfl
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, pow_two, Complex.I_mul_I]; ring
  cases p <;> cases q <;> cases a <;> cases b <;>
    simp [Pauli.mat, mXX, mYY, mZZ, mII, mIX, mIY, mIZ, mXI, mYI, mZI, mXY, mYX, mYZ, mZY, mZX,
      mXZ, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fintype.sum_bool, v0, v1, v3, hI3,
      Matrix.one_apply]

lemma toMatrix_mul {n : ℕ} (P Q : PauliString n) :
    P.toMatrix * Q.toMatrix = (P.mul Q).toMatrix := by
  ext y z
  simp only [Matrix.mul_apply, PauliString.toMatrix, Matrix.of_apply, PauliString.mul]
  have h1 : ∀ m : Qubits n, (Complex.I ^ P.phase.val * ∏ q, (P.ops q).mat (y q) (m q)) *
      (Complex.I ^ Q.phase.val * ∏ q, (Q.ops q).mat (m q) (z q)) =
      (Complex.I ^ P.phase.val * Complex.I ^ Q.phase.val) *
        ∏ q, ((P.ops q).mat (y q) (m q) * (Q.ops q).mat (m q) (z q)) := by
    intro m
    rw [Finset.prod_mul_distrib]
    ring
  rw [Finset.sum_congr rfl (fun m _ => h1 m), ← Finset.mul_sum]
  have h2 : ∑ m : Qubits n, ∏ q, ((P.ops q).mat (y q) (m q) * (Q.ops q).mat (m q) (z q)) =
      ∏ q, ∑ b : Bool, (P.ops q).mat (y q) b * (Q.ops q).mat b (z q) :=
    (Fintype.prod_sum (fun q b => (P.ops q).mat (y q) b * (Q.ops q).mat b (z q))).symm
  rw [h2]
  have h3 : ∀ q, ∑ b : Bool, (P.ops q).mat (y q) b * (Q.ops q).mat b (z q) =
      Complex.I ^ (Pauli.mul (P.ops q) (Q.ops q)).1.val *
        (Pauli.mul (P.ops q) (Q.ops q)).2.mat (y q) (z q) := by
    intro q
    rw [← pauli_single, Matrix.mul_apply]
  rw [Finset.prod_congr rfl (fun q _ => h3 q), Finset.prod_mul_distrib, Ipow_sum, Ipow_add,
    Ipow_add]
  ring

lemma toMatrix_phase {n : ℕ} (c d : ZMod 4) (ops : Fin n → Pauli) :
    (⟨c + d, ops⟩ : PauliString n).toMatrix =
      Complex.I ^ d.val • (⟨c, ops⟩ : PauliString n).toMatrix := by
  ext y z
  simp only [PauliString.toMatrix, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Ipow_add]
  ring

lemma toMatrix_id {n : ℕ} (c : ZMod 4) :
    (⟨c, fun _ => .I⟩ : PauliString n).toMatrix =
      Complex.I ^ c.val • (1 : Matrix (Qubits n) (Qubits n) ℂ) := by
  ext y z
  simp only [PauliString.toMatrix, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Pauli.mat]
  by_cases h : y = z
  · subst h
    simp [Matrix.one_apply]
  · rw [Matrix.one_apply_ne h]
    obtain ⟨q, hq⟩ := Function.ne_iff.mp h
    have h0 : ∏ q', (1 : Matrix Bool Bool ℂ) (y q') (z q') = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ q) (Matrix.one_apply_ne hq)
    rw [h0]

lemma sq_toMatrix {n : ℕ} (P : PauliString n) :
    P.toMatrix * P.toMatrix =
      Complex.I ^ (2 * P.phase).val • (1 : Matrix (Qubits n) (Qubits n) ℂ) := by
  rw [toMatrix_mul]
  have hmm : ∀ p : Pauli, Pauli.mul p p = (0, .I) := by intro p; cases p <;> rfl
  have : P.mul P = ⟨2 * P.phase, fun _ => .I⟩ := by
    show (⟨P.phase + P.phase + ∑ q, (Pauli.mul (P.ops q) (P.ops q)).1,
      fun q => (Pauli.mul (P.ops q) (P.ops q)).2⟩ : PauliString n) = _
    congr 1
    · simp only [hmm, Finset.sum_const_zero, add_zero]
      ring
    · funext q
      rw [hmm]
  rw [this, toMatrix_id]

lemma commute_toMatrix {n : ℕ} (P Q : PauliString n) :
    ∃ s : ℂ, s * s = 1 ∧ P.toMatrix * Q.toMatrix = s • (Q.toMatrix * P.toMatrix) := by
  rw [toMatrix_mul, toMatrix_mul]
  have hops : ∀ p q : Pauli, (Pauli.mul p q).2 = (Pauli.mul q p).2 := by
    intro p q; cases p <;> cases q <;> rfl
  have h2 : ∀ p q : Pauli, 2 * ((Pauli.mul p q).1 - (Pauli.mul q p).1) = 0 := by
    intro p q; cases p <;> cases q <;> decide
  obtain ⟨D, hD⟩ : ∃ D : ZMod 4,
      D = ∑ q, ((Pauli.mul (P.ops q) (Q.ops q)).1 - (Pauli.mul (Q.ops q) (P.ops q)).1) :=
    ⟨_, rfl⟩
  have hPQ : P.mul Q = ⟨(Q.mul P).phase + D, (Q.mul P).ops⟩ := by
    show (⟨P.phase + Q.phase + ∑ q, (Pauli.mul (P.ops q) (Q.ops q)).1,
      fun q => (Pauli.mul (P.ops q) (Q.ops q)).2⟩ : PauliString n) =
      ⟨Q.phase + P.phase + ∑ q, (Pauli.mul (Q.ops q) (P.ops q)).1 + D,
        fun q => (Pauli.mul (Q.ops q) (P.ops q)).2⟩
    congr 1
    · rw [hD, Finset.sum_sub_distrib]; ring
    · funext q; exact hops _ _
  refine ⟨Complex.I ^ D.val, ?_, ?_⟩
  · rw [← Ipow_add]
    have : D + D = 0 := by
      rw [← two_mul, hD, Finset.mul_sum]
      exact Finset.sum_eq_zero (fun q _ => h2 _ _)
    rw [this]
    simp
  · rw [hPQ, toMatrix_phase]

lemma mem_pauliGroup {n : ℕ} (U : Matrix.unitaryGroup (Qubits n) ℂ) (hU : U ∈ pauliGroup n) :
    ∃ P : PauliString n, (U : Matrix (Qubits n) (Qubits n) ℂ) = P.toMatrix := by
  unfold pauliGroup at hU
  induction hU using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨P, hP⟩ := hx
    exact ⟨P, hP⟩
  | one =>
    refine ⟨⟨0, fun _ => .I⟩, ?_⟩
    rw [toMatrix_id]
    simp
  | mul x y _ _ hx hy =>
    obtain ⟨P, hP⟩ := hx
    obtain ⟨Q, hQ⟩ := hy
    refine ⟨P.mul Q, ?_⟩
    rw [← toMatrix_mul, ← hP, ← hQ]
    rfl
  | inv x _ hx =>
    obtain ⟨P, hP⟩ := hx
    have hsq : (x : Matrix (Qubits n) (Qubits n) ℂ) * (x : Matrix (Qubits n) (Qubits n) ℂ) =
        Complex.I ^ (2 * P.phase).val • (1 : Matrix (Qubits n) (Qubits n) ℂ) := by
      rw [hP]; exact sq_toMatrix P
    have h4 : ∀ φ : ZMod 4, 2 * φ + 2 * φ = 0 := by decide
    have hs : Complex.I ^ (2 * P.phase).val * Complex.I ^ (2 * P.phase).val = 1 := by
      rw [← Ipow_add, h4]; simp
    have hinv : ((x⁻¹ : Matrix.unitaryGroup (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ) *
        (x : Matrix (Qubits n) (Qubits n) ℂ) = 1 := by
      show ((x⁻¹ * x : Matrix.unitaryGroup (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ) = 1
      rw [inv_mul_cancel]
      rfl
    have hxinv : ((x⁻¹ : Matrix.unitaryGroup (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ) =
        Complex.I ^ (2 * P.phase).val • (x : Matrix (Qubits n) (Qubits n) ℂ) := by
      calc ((x⁻¹ : Matrix.unitaryGroup (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ)
          = ((x⁻¹ : Matrix.unitaryGroup (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ) *
              ((Complex.I ^ (2 * P.phase).val * Complex.I ^ (2 * P.phase).val) •
                (1 : Matrix (Qubits n) (Qubits n) ℂ)) := by rw [hs, one_smul, mul_one]
        _ = Complex.I ^ (2 * P.phase).val •
              ((((x⁻¹ : Matrix.unitaryGroup (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ) *
                (x : Matrix (Qubits n) (Qubits n) ℂ)) * (x : Matrix (Qubits n) (Qubits n) ℂ)) := by
              rw [mul_smul, ← hsq, Matrix.mul_smul, mul_assoc]
        _ = Complex.I ^ (2 * P.phase).val • (x : Matrix (Qubits n) (Qubits n) ℂ) := by
              rw [hinv, one_mul]
    refine ⟨⟨P.phase + 2 * P.phase, P.ops⟩, ?_⟩
    rw [hxinv, toMatrix_phase, hP]

lemma act_fix {n : ℕ} (A : Matrix (Qubits n) (Qubits n) ℂ) (ψ : EuclideanSpace ℂ (Qubits n))
    (h : act A ψ = ψ) : A *ᵥ WithLp.ofLp ψ = WithLp.ofLp ψ := by
  have := congrArg WithLp.ofLp h
  simpa [act] using this

lemma ofLp_ne {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) (hψ : ψ ≠ 0) : WithLp.ofLp ψ ≠ 0 := by
  intro h0
  apply hψ
  simpa using congrArg (WithLp.toLp 2) h0

lemma smul_fix {n : ℕ} (s : ℂ) (v : Qubits n → ℂ) (hv : v ≠ 0) (h : s • v = v) : s = 1 := by
  have h1 : (s - 1) • v = 0 := by rw [sub_smul, h, one_smul, sub_self]
  rcases smul_eq_zero.mp h1 with h2 | h2
  · linear_combination h2
  · exact absurd h2 hv

lemma finite_pauli : Finite Pauli := by
  refine Finite.of_injective (fun p : Pauli => match p with
    | .I => (0 : Fin 4) | .X => 1 | .Y => 2 | .Z => 3) ?_
  intro a b h
  cases a <;> cases b <;> first | rfl | (exfalso; revert h; decide)

end Aux_HeisenbergRep_Knill_stabilizer_abelian_elementary

open QAlgorithms QAlgorithms.Stabilizer HeisenbergRep.Knill Matrix
  Aux_HeisenbergRep_Knill_stabilizer_abelian_elementary in
theorem solution {n : ℕ} (Ψ : Set (EuclideanSpace ℂ (Qubits n)))
    (hΨ : ∃ ψ ∈ Ψ, ψ ≠ 0) :
    (∀ M ∈ stabilizerOf Ψ, ∀ N ∈ stabilizerOf Ψ, M * N = N * M) ∧
    (∀ M ∈ stabilizerOf Ψ, (∃ P : PauliString n, (P.phase = 0 ∨ P.phase = 2) ∧
        (M : Matrix (Qubits n) (Qubits n) ℂ) = P.toMatrix) ∧ M * M = 1) ∧
    ∃ k : ℕ, Nonempty (stabilizerOf Ψ ≃* Multiplicative (Fin k → ZMod 2)) := by
  obtain ⟨ψ, hψΨ, hψ0⟩ := hΨ
  have hv := ofLp_ne ψ hψ0
  have P1 : ∀ M ∈ stabilizerOf Ψ, ∀ N ∈ stabilizerOf Ψ, M * N = N * M := by
    intro M hM N hN
    obtain ⟨hMp, hMf⟩ := hM
    obtain ⟨hNp, hNf⟩ := hN
    obtain ⟨P, hP⟩ := mem_pauliGroup M hMp
    obtain ⟨Q, hQ⟩ := mem_pauliGroup N hNp
    obtain ⟨s, hs, hc⟩ := commute_toMatrix P Q
    rw [← hP, ← hQ] at hc
    have hMv := act_fix _ ψ (hMf ψ hψΨ)
    have hNv := act_fix _ ψ (hNf ψ hψΨ)
    have h1 : ((M : Matrix (Qubits n) (Qubits n) ℂ) * (N : Matrix (Qubits n) (Qubits n) ℂ)) *ᵥ
        WithLp.ofLp ψ = WithLp.ofLp ψ := by
      rw [← Matrix.mulVec_mulVec, hNv, hMv]
    have h2 : ((N : Matrix (Qubits n) (Qubits n) ℂ) * (M : Matrix (Qubits n) (Qubits n) ℂ)) *ᵥ
        WithLp.ofLp ψ = WithLp.ofLp ψ := by
      rw [← Matrix.mulVec_mulVec, hMv, hNv]
    rw [hc, Matrix.smul_mulVec, h2] at h1
    have hs1 := smul_fix s _ hv h1
    rw [hs1, one_smul] at hc
    exact Subtype.ext hc
  have P2 : ∀ M ∈ stabilizerOf Ψ, (∃ P : PauliString n, (P.phase = 0 ∨ P.phase = 2) ∧
      (M : Matrix (Qubits n) (Qubits n) ℂ) = P.toMatrix) ∧ M * M = 1 := by
    intro M hM
    obtain ⟨hMp, hMf⟩ := hM
    obtain ⟨P, hP⟩ := mem_pauliGroup M hMp
    have hsq := sq_toMatrix P
    rw [← hP] at hsq
    have hMv := act_fix _ ψ (hMf ψ hψΨ)
    have h1 : ((M : Matrix (Qubits n) (Qubits n) ℂ) * (M : Matrix (Qubits n) (Qubits n) ℂ)) *ᵥ
        WithLp.ofLp ψ = WithLp.ofLp ψ := by
      rw [← Matrix.mulVec_mulVec, hMv, hMv]
    rw [hsq, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
    have hs1 := smul_fix _ _ hv h1
    have hcase : ∀ φ : ZMod 4, φ = 0 ∨ φ = 2 ∨ (2 * φ).val = 2 := by decide
    refine ⟨⟨P, ?_, hP⟩, ?_⟩
    · rcases hcase P.phase with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        rw [h, Complex.I_sq] at hs1
        norm_num at hs1
    · apply Subtype.ext
      show (M : Matrix (Qubits n) (Qubits n) ℂ) * (M : Matrix (Qubits n) (Qubits n) ℂ) = 1
      rw [hsq, hs1, one_smul]
  refine ⟨P1, P2, ?_⟩
  -- the group structure
  have hcomm : ∀ a b : stabilizerOf Ψ, a * b = b * a := by
    intro a b
    exact Subtype.ext (P1 a a.2 b b.2)
  have hsq1 : ∀ a : stabilizerOf Ψ, a * a = 1 := by
    intro a
    exact Subtype.ext (P2 a a.2).2
  letI : CommGroup (stabilizerOf Ψ) := { (inferInstance : Group (stabilizerOf Ψ)) with
    mul_comm := hcomm }
  have h2 : ∀ x : Additive (stabilizerOf Ψ), 2 • x = 0 := by
    intro x
    rw [two_nsmul]
    exact hsq1 (Additive.toMul x)
  letI : Module (ZMod 2) (Additive (stabilizerOf Ψ)) := AddCommGroup.zmodModule h2
  haveI : Finite Pauli := finite_pauli
  haveI : Finite (PauliString n) := by
    refine Finite.of_injective (fun P : PauliString n => (P.phase, P.ops)) ?_
    rintro ⟨a, f⟩ ⟨b, g⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  haveI : Finite (Set.range (fun P : PauliString n => P.toMatrix)) :=
    (Set.finite_range _).to_subtype
  haveI : Finite (stabilizerOf Ψ) := by
    refine Finite.of_injective (fun g : stabilizerOf Ψ =>
      (⟨((g : Matrix.unitaryGroup (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ),
        by obtain ⟨P, _, hP⟩ := (P2 g g.2).1; exact ⟨P, hP.symm⟩⟩ :
        Set.range (fun P : PauliString n => P.toMatrix))) ?_
    intro g h hgh
    have := congrArg Subtype.val hgh
    exact Subtype.ext (Subtype.ext this)
  haveI : Finite (Additive (stabilizerOf Ψ)) := inferInstanceAs (Finite (stabilizerOf Ψ))
  haveI : Module.Finite (ZMod 2) (Additive (stabilizerOf Ψ)) := Module.Finite.of_finite
  refine ⟨Module.finrank (ZMod 2) (Additive (stabilizerOf Ψ)), ⟨?_⟩⟩
  exact AddEquiv.toMultiplicativeRight
    (Module.finBasis (ZMod 2) (Additive (stabilizerOf Ψ))).equivFun.toAddEquiv
