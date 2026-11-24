-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.nodal_seed_normalized_trace
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T07:29:47.709368+00:00
-- url     : https://prove2.me/submissions/7b5a7a03-d153-461c-a453-f3cba7b25585

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section

namespace FP5SeedTrace

open Matrix HodgeComputer.FourPlusTwoResidual

lemma moment_traces {K : Type*} [CommRing K] (k u v : K) :
    let X := seedMulX k
    let adj := seedAdjugateNumerator k u v
    ((X ^ 3 * adj).trace, (X ^ 2 * adj).trace, (X * adj).trace) =
      (3 * k * u ^ 2, -(3 * k * u * v), 3 * k * v ^ 2) := by
  simp [seedMulX, seedAdjugateNumerator, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fin.sum_univ_three, pow_succ]
  exact ⟨by ring, by ring, by ring⟩

end FP5SeedTrace

theorem solution :
    (∀ {K : Type} [CommRing K] (k u v : K),
      ((u • (1 : Matrix (Fin 3) (Fin 3) K) + v • HodgeComputer.FourPlusTwoResidual.seedMulX k) *
          HodgeComputer.FourPlusTwoResidual.seedAdjugateNumerator k u v =
        (u ^ 3 + k * v ^ 3) • (1 : Matrix (Fin 3) (Fin 3) K)) ∧
      (∀ (a B C B' C' : K), a ^ 3 * B = -1 →
        let beta := -C * a ^ 2
        let g := C ^ 3 - B ^ 2
        let g' := 3 * C ^ 2 * C' - 2 * B * B'
        let Er := -(3 * a ^ 2 * B)
        let EZ := a ^ 3 * B'
        let EY := Er * (-C' * a ^ 2) + (-(2 * C * a)) * EZ
        a * (3 * g * beta * EY - beta ^ 2 * Er * g') - 6 * g * beta ^ 2 * EZ =
          3 * a ^ 4 * B * C * (2 * C * B' - 3 * B * C'))) ∧
    (∀ {F : Type} [Field F] [CharZero F] (B u v : F),
      B ≠ 0 → B ^ 2 * u ^ 3 + v ^ 3 ≠ 0 →
      let k := 1 / B ^ 2
      let d := 3 * (u ^ 3 + k * v ^ 3)
      let X := HodgeComputer.FourPlusTwoResidual.seedMulX k
      let adj := HodgeComputer.FourPlusTwoResidual.seedAdjugateNumerator k u v
      ((X ^ 3 * adj).trace / d, (X ^ 2 * adj).trace / d, (X * adj).trace / d) =
        (u ^ 2 / (B ^ 2 * u ^ 3 + v ^ 3),
          -(u * v) / (B ^ 2 * u ^ 3 + v ^ 3),
          v ^ 2 / (B ^ 2 * u ^ 3 + v ^ 3))) := by
  refine ⟨?_, ?_⟩
  · intro K _ k u v
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [HodgeComputer.FourPlusTwoResidual.seedMulX,
          HodgeComputer.FourPlusTwoResidual.seedAdjugateNumerator,
          Matrix.mul_apply, Fin.sum_univ_three] <;> ring
    · intro a B C B' C' ha
      dsimp only
      linear_combination -(3 * a ^ 4 * B * C * (2 * C * B' - 3 * B * C')) * ha
  · intro F _ _ B u v hB hd
    let k := 1 / B ^ 2
    let d := 3 * (u ^ 3 + k * v ^ 3)
    let normalize (p : F × F × F) := (p.1 / d, p.2.1 / d, p.2.2 / d)
    refine (congrArg normalize (FP5SeedTrace.moment_traces k u v)).trans ?_
    simp only [normalize, d, k, Prod.mk.injEq]
    exact ⟨by field_simp [hB, hd], by field_simp [hB, hd], by field_simp [hB, hd]⟩
