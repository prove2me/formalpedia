-- Prove2me | solution 1 for HardyFiveAxioms.qutrit_D_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T11:33:18.18681+00:00
-- url     : https://prove2.me/submissions/e3861243-6510-4a2c-b5f2-b55d29b3bb5b

import Mathlib
import Definitions.Def_hardy2001_projectors

set_option autoImplicit false

namespace HardyFiveAxioms.Q784

open HardyFiveAxioms

noncomputable def s : ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ)

lemma star_s : star s = s := by
  simp [s, Complex.conj_ofReal]

lemma conj_s : (starRingEnd ℂ) s = s := by
  simp [s, Complex.conj_ofReal]

lemma s_sq : s ^ 2 = 1 / 2 := by
  unfold s
  rw [← Complex.ofReal_pow, div_pow, Real.sq_sqrt (by norm_num)]
  push_cast; ring

lemma s_four : s ^ 4 = 1 / 4 := by
  have : s ^ 4 = (s ^ 2) ^ 2 := by ring
  rw [this, s_sq]; norm_num

lemma trace_proj (u v : Fin 3 → ℂ) :
    (proj u * proj v).trace =
      (∑ i, u i * star (v i)) * (∑ j, v j * star (u j)) := by
  simp only [proj, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, Fin.sum_univ_three]
  ring

lemma k0 : ket (0 : Fin 3) = ![1, 0, 0] := by
  ext i; fin_cases i <;> simp [ket]
lemma k1 : ket (1 : Fin 3) = ![0, 1, 0] := by
  ext i; fin_cases i <;> simp [ket]
lemma k2 : ket (2 : Fin 3) = ![0, 0, 1] := by
  ext i; fin_cases i <;> simp [ket]
lemma x01 : ketX (0 : Fin 3) 1 = ![s, s, 0] := by
  ext i; fin_cases i <;> simp [ketX, ket, s]
lemma y01 : ketY (0 : Fin 3) 1 = ![s, s * Complex.I, 0] := by
  ext i; fin_cases i <;> simp [ketY, ket, s]
lemma x02 : ketX (0 : Fin 3) 2 = ![s, 0, s] := by
  ext i; fin_cases i <;> simp [ketX, ket, s]
lemma y02 : ketY (0 : Fin 3) 2 = ![s, 0, s * Complex.I] := by
  ext i; fin_cases i <;> simp [ketY, ket, s]
lemma x12 : ketX (1 : Fin 3) 2 = ![0, s, s] := by
  ext i; fin_cases i <;> simp [ketX, ket, s]
lemma y12 : ketY (1 : Fin 3) 2 = ![0, s, s * Complex.I] := by
  ext i; fin_cases i <;> simp [ketY, ket, s]

end HardyFiveAxioms.Q784

open HardyFiveAxioms in
theorem solution :
    let P : Fin 9 → Matrix (Fin 3) (Fin 3) ℂ :=
      ![proj (ket 0), proj (ket 1), proj (ket 2),
        proj (ketX 0 1), proj (ketY 0 1), proj (ketX 0 2), proj (ketY 0 2),
        proj (ketX 1 2), proj (ketY 1 2)]
    let h : ℝ := 1 / 2
    let q : ℝ := 1 / 4
    let D : Matrix (Fin 9) (Fin 9) ℝ :=
      !![1, 0, 0, h, h, h, h, 0, 0;
         0, 1, 0, h, h, 0, 0, h, h;
         0, 0, 1, 0, 0, h, h, h, h;
         h, h, 0, 1, h, q, q, q, q;
         h, h, 0, h, 1, q, q, q, q;
         h, 0, h, q, q, 1, h, q, q;
         h, 0, h, q, q, h, 1, q, q;
         0, h, h, q, q, q, q, 1, h;
         0, h, h, q, q, q, q, h, 1]
    ∀ i j : Fin 9, (P i * P j).trace = (D i j : ℂ) := by
  intro P h q D i j
  have hs2 := HardyFiveAxioms.Q784.s_sq
  have hs4 := HardyFiveAxioms.Q784.s_four
  simp only [P, D, h, q, HardyFiveAxioms.Q784.k0, HardyFiveAxioms.Q784.k1,
    HardyFiveAxioms.Q784.k2, HardyFiveAxioms.Q784.x01, HardyFiveAxioms.Q784.y01,
    HardyFiveAxioms.Q784.x02, HardyFiveAxioms.Q784.y02, HardyFiveAxioms.Q784.x12,
    HardyFiveAxioms.Q784.y12]
  fin_cases i <;> fin_cases j <;>
    simp [HardyFiveAxioms.Q784.trace_proj, Fin.sum_univ_three,
      HardyFiveAxioms.Q784.star_s, HardyFiveAxioms.Q784.conj_s]
  all_goals (try ring_nf)
  all_goals (try simp [hs2, hs4, Complex.I_sq])
  all_goals (try ring_nf)
