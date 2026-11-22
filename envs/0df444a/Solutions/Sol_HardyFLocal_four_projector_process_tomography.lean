-- Prove2me | solution 1 for HardyFLocal.four_projector_process_tomography
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T00:32:02.789068+00:00
-- url     : https://prove2.me/submissions/1db5cf21-a6fb-43ce-a813-a777192c41c7

import Definitions.Def_HardyFLocal_Superoperator

namespace HardyFLocal
open scoped Matrix ComplexOrder
private abbrev QMat := Matrix (Fin 2) (Fin 2) ℂ

private noncomputable def probe : Fin 4 → QMat :=
  ![!![1,0;0,0], !![0,0;0,1], !![1/2,1/2;1/2,1/2],
    !![1/2,-Complex.I/2;Complex.I/2,1/2]]

private theorem probe_herm (i : Fin 4) : (probe i).IsHermitian := by
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [probe, Matrix.conjTranspose_apply]

private theorem probe_idem (i : Fin 4) : probe i * probe i = probe i := by
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [probe, Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv] <;> ring_nf <;> norm_num

private theorem probe_physical (i : Fin 4) :
    (probe i).PosSemidef ∧ (1 - probe i).PosSemidef ∧ (probe i).trace = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [(probe_herm i).eq, probe_idem] using Matrix.posSemidef_conjTranspose_mul_self (probe i)
  · have her : (1 - probe i : QMat).IsHermitian := Matrix.isHermitian_one.sub (probe_herm i)
    have idem : (1 - probe i : QMat) * (1 - probe i) = 1 - probe i := by
      rw [sub_mul, one_mul, mul_sub, mul_one, probe_idem, sub_self, sub_zero]
    have hpos := Matrix.posSemidef_conjTranspose_mul_self (1 - probe i : QMat)
    rwa [her.eq, idem] at hpos
  · fin_cases i <;> norm_num [probe, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

private theorem probe_expansion (A : QMat) :
    ∃ c₀ c₁ c₂ c₃ : ℂ, A = c₀ • probe 0 + c₁ • probe 1 + c₂ • probe 2 + c₃ • probe 3 := by
  let x := A 0 1 + A 1 0
  let y := (A 0 1 - A 1 0) * Complex.I
  refine ⟨A 0 0 - (x+y)/2, A 1 1 - (x+y)/2, x, y, ?_⟩
  change A = _ • (!![1,0;0,0] : QMat) + _ • (!![0,0;0,1] : QMat) +
    x • (!![1/2,1/2;1/2,1/2] : QMat) + y • (!![1/2,-Complex.I/2;Complex.I/2,1/2] : QMat)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [x, y, Matrix.smul_apply, Matrix.add_apply] <;> ring_nf <;> norm_num <;> ring

private theorem probes_detect {B : QMat} (h : ∀ i, (probe i * B).trace = 0) : B = 0 := by
  have allTests (E : QMat) : (E * B).trace = 0 := by
    obtain ⟨a,b,c,d,he⟩ := probe_expansion E
    simp [he, add_mul, Matrix.trace_add, Matrix.trace_smul, h]
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (allTests Bᴴ)

private theorem real_trace_pair {A B : QMat} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (((A * B).trace.re : ℝ) : ℂ) = (A * B).trace := by
  apply Complex.conj_eq_iff_re.mp
  change star (A * B).trace = (A * B).trace
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq, Matrix.trace_mul_comm]

end HardyFLocal

open HardyFLocal
open scoped Matrix ComplexOrder

theorem solution :
    ∃ P : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ i, (P i).PosSemidef ∧ (1 - P i).PosSemidef ∧ (P i).trace = 1 ∧ P i * P i = P i) ∧
      ∀ Φ ∈ hpMaps (Fin 2), ∀ Ψ ∈ hpMaps (Fin 2),
        (∀ i j, (P j * Φ (P i)).trace.re = (P j * Ψ (P i)).trace.re) ↔ Φ = Ψ := by
  refine ⟨probe, fun i => ⟨(probe_physical i).1, (probe_physical i).2.1,
    (probe_physical i).2.2, probe_idem i⟩, fun Φ hΦ Ψ hΨ => ⟨?_, fun h _ _ => h ▸ rfl⟩⟩
  intro h
  have eqProbe (i) : Φ (probe i) = Ψ (probe i) := by
    apply sub_eq_zero.mp
    apply probes_detect
    intro j
    rw [mul_sub, Matrix.trace_sub, sub_eq_zero, ← real_trace_pair (probe_herm j) (hΦ _ (probe_herm i)),
      ← real_trace_pair (probe_herm j) (hΨ _ (probe_herm i)), h i j]
  apply LinearMap.ext
  intro A
  obtain ⟨a,b,c,d,hA⟩ := probe_expansion A
  simp only [hA, map_add, map_smul, eqProbe]

