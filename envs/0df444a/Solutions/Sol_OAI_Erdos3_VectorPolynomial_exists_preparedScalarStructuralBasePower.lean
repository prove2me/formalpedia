-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_preparedScalarStructuralBasePower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T02:57:23.212955+00:00
-- url     : https://prove2.me/submissions/a85618f9-507f-4f35-85b1-3b32cb482f9c

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1324

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedScalarStructuralBasePower
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped NNReal ContDiff

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedScalarStructuralBasePower_oai (s : ℕ) :
    ∃ baseMin : ℕ, 1 ≤ baseMin ∧
      ∀ basePower : ℕ, baseMin ≤ basePower → ∀ p : ℝ, 2 ≤ p →
        let B := (p + 2) ^ basePower
        (scalarNativeDimension s : ℝ) ≤ B ∧
          (probabilityProfileLipschitz : ℝ) ≤ Real.exp B ∧
          (normalizedSiteCutoffBound : ℝ) ≤ Real.exp B ∧ p ≤ B := by
  let profileCeil := ⌈(probabilityProfileLipschitz : ℝ)⌉₊
  let cutoffCeil := ⌈(normalizedSiteCutoffBound : ℝ)⌉₊
  let baseMin := scalarNativeDimension s + profileCeil + cutoffCeil + 1
  refine ⟨baseMin, by dsimp [baseMin]; omega, ?_⟩
  intro basePower hbasePower p hp
  dsimp only
  have hdim : scalarNativeDimension s ≤ basePower := by
    dsimp [baseMin] at hbasePower
    omega
  have hprofile : profileCeil ≤ basePower := by
    dsimp [baseMin] at hbasePower
    omega
  have hcutoff : cutoffCeil ≤ basePower := by
    dsimp [baseMin] at hbasePower
    omega
  have hone : 1 ≤ basePower := by
    dsimp [baseMin] at hbasePower
    omega
  have hpower : (basePower : ℝ) ≤ (p + 2) ^ basePower := by
    calc
      (basePower : ℝ) ≤ (2 : ℝ) ^ basePower := by
        exact_mod_cast (show basePower < 2 ^ basePower from Nat.lt_two_pow_self).le
      _ ≤ (p + 2) ^ basePower :=
        pow_le_pow_left₀ (by norm_num) (by linarith) basePower
  have hexp : (p + 2) ^ basePower ≤ Real.exp ((p + 2) ^ basePower) :=
    le_trans (by linarith) (Real.add_one_le_exp _)
  refine ⟨(Nat.cast_le.mpr hdim).trans hpower, ?_, ?_,
    le_power_budget (by linarith) hone⟩
  · exact (Nat.le_ceil _).trans ((Nat.cast_le.mpr hprofile).trans (hpower.trans hexp))
  · exact (Nat.le_ceil _).trans ((Nat.cast_le.mpr hcutoff).trans (hpower.trans hexp))

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.exists_preparedScalarStructuralBasePower_oai := @OAI.Erdos3.VectorPolynomial.exists_preparedScalarStructuralBasePower_oai
