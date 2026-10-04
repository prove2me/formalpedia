-- Prove2me | solution 1 for HardyFiveAxioms.fiducialProjector_card_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T12:16:49.704867+00:00
-- url     : https://prove2.me/submissions/4ac01c78-de7a-459f-a02e-8dad6d3179dd

import Mathlib
import Definitions.Def_hardy2001_projectors

set_option autoImplicit false

namespace HardyFiveAxioms.FidAux
open HardyFiveAxioms

lemma c_sq : ((1 / Real.sqrt 2 : ℝ) : ℂ) * star ((1 / Real.sqrt 2 : ℝ) : ℂ) = 1 / 2 := by
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  have : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 / 2 : ℝ) := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]
  rw [this]; push_cast; ring

lemma proj_apply' {N : ℕ} (v : Fin N → ℂ) (a b : Fin N) : proj v a b = v a * star (v b) := by
  simp [proj, Matrix.vecMulVec_apply]

lemma ket_apply' {N : ℕ} (k a : Fin N) : ket k a = if a = k then 1 else 0 := by
  simp [ket, Pi.single_apply]

lemma projX_apply {N : ℕ} (m n a b : Fin N) : proj (ketX m n) a b =
    (1 / 2) * ((ket m a + ket n a) * star (ket m b + ket n b)) := by
  rw [proj_apply']
  simp only [ketX, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
  rw [star_mul', ← c_sq]; ring

lemma projY_apply {N : ℕ} (m n a b : Fin N) : proj (ketY m n) a b =
    (1 / 2) * ((ket m a + Complex.I * ket n a) * star (ket m b + Complex.I * ket n b)) := by
  rw [proj_apply']
  simp only [ketY, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
  rw [star_mul', ← c_sq]; ring

lemma card_lt (N : ℕ) : Fintype.card {p : Fin N × Fin N // p.1 < p.2} = N.choose 2 := by
  rw [Fintype.card_subtype]
  simpa using Fintype.card_product_filter_lt (α := Fin N)

lemma offdiag_entry {N : ℕ} (g : FiducialIndex N → ℝ) (p : {p : Fin N × Fin N // p.1 < p.2}) :
    (∑ i, g i • fiducialProjector i) p.1.1 p.1.2 =
      ((g (Sum.inr (p, false)) : ℂ) - (g (Sum.inr (p, true)) : ℂ) * Complex.I) / 2 := by
  obtain ⟨⟨m, n⟩, hmn⟩ := p
  simp only [Matrix.sum_apply, Matrix.smul_apply, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_bool, fiducialProjector]
  have hmn' : m ≠ n := ne_of_lt hmn
  have hmn2 : m.val < n.val := hmn
  have hA : ∀ k : Fin N, g (Sum.inl k) • proj (ket k) m n = 0 := by
    intro k
    rw [proj_apply', ket_apply', ket_apply']
    by_cases h : m = k
    · subst h; simp [hmn'.symm]
    · simp [h]
  have hB : ∀ q : {p : Fin N × Fin N // p.1 < p.2}, q ≠ ⟨(m, n), hmn⟩ →
      g (Sum.inr (q, true)) • proj (ketY q.1.1 q.1.2) m n +
        g (Sum.inr (q, false)) • proj (ketX q.1.1 q.1.2) m n = 0 := by
    rintro ⟨⟨a, b⟩, hab⟩ hne
    have hab2 : a.val < b.val := hab
    have hne' : ¬ (a.val = m.val ∧ b.val = n.val) := by
      rintro ⟨h1, h2⟩
      apply hne
      have e1 : a = m := Fin.ext h1
      have e2 : b = n := Fin.ext h2
      subst e1; subst e2; rfl
    simp only [projX_apply, projY_apply, ket_apply', Fin.ext_iff]
    split_ifs <;> first | omega | simp
  rw [Finset.sum_eq_zero (fun k _ => hA k), zero_add,
    Finset.sum_eq_single (⟨(m, n), hmn⟩ : {p : Fin N × Fin N // p.1 < p.2})
      (fun q _ hq => hB q hq) (fun h => absurd (Finset.mem_univ _) h)]
  simp only [projX_apply, projY_apply, ket_apply']
  simp [hmn', hmn'.symm, Complex.real_smul]
  try ring

lemma diag_entry {N : ℕ} (g : FiducialIndex N → ℝ)
    (h0 : ∀ q : {p : Fin N × Fin N // p.1 < p.2}, ∀ b : Bool, g (Sum.inr (q, b)) = 0) (k : Fin N) :
    (∑ i, g i • fiducialProjector i) k k = (g (Sum.inl k) : ℂ) := by
  simp only [Matrix.sum_apply, Matrix.smul_apply, Fintype.sum_sum_type,
    fiducialProjector, h0, zero_smul, add_zero, Finset.sum_const_zero]
  rw [Finset.sum_eq_single k]
  · rw [proj_apply', ket_apply']; simp [Complex.real_smul]
  · intro j _ hj
    rw [proj_apply', ket_apply']; simp [Ne.symm hj]
  · intro h; exact absurd (Finset.mem_univ _) h

end HardyFiveAxioms.FidAux

open HardyFiveAxioms in
theorem solution (N : ℕ) :
    Fintype.card (FiducialIndex N) = N ^ 2 ∧
      LinearIndependent ℝ (fiducialProjector (N := N)) := by
  constructor
  · rw [Fintype.card_sum, Fintype.card_prod, FidAux.card_lt, Fintype.card_fin, Fintype.card_bool]
    cases N with
    | zero => simp
    | succ n =>
      have h := Nat.add_one_mul_choose_eq n 1
      simp only [Nat.choose_one_right] at h
      nlinarith [h]
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : ∀ q : {p : Fin N × Fin N // p.1 < p.2}, ∀ b : Bool, g (Sum.inr (q, b)) = 0 := by
      intro q b
      have e := FidAux.offdiag_entry g q
      rw [hg] at e
      have hre := congrArg Complex.re e
      have him := congrArg Complex.im e
      simp at hre him
      cases b
      · linarith
      · linarith
    intro i
    rcases i with k | ⟨q, b⟩
    · have e := FidAux.diag_entry g h0 k
      rw [hg] at e
      have := congrArg Complex.re e
      simpa using this.symm
    · exact h0 q b
