-- Prove2me | solution 1 for OAI.Laughlin.Fock.truncated_pair_window_return_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:35:16.018212+00:00
-- url     : https://prove2.me/submissions/764ba1d7-0a7b-4e7d-a70c-6b5fb67cf78b

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L017
import Theorems.Thm_OAI_Laughlin_Fock_truncatedScaling_normSq_le_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_Conjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem pair_radicand_factorization (Q p x y : ℕ) (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (hxy : x+y = p+1) :
    ((Q.descFactorial x : ℝ) / (Q : ℝ)^x) *
    ((Q.descFactorial y : ℝ) / (Q : ℝ)^y) *
    (((2 : ℝ)*Q)^p / ((2*Q-2).descFactorial p : ℝ)) *
    ((p.factorial : ℝ) / ((2 : ℝ)^p * (x.factorial : ℝ) * (y.factorial : ℝ))) =
    ((Q.descFactorial x : ℝ)*(Q.descFactorial y : ℝ)*(p.factorial : ℝ)) /
      ((Q : ℝ)*((2*Q-2).descFactorial p : ℝ)*(x.factorial : ℝ)*(y.factorial : ℝ)) := by
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
  have hd : ((2*Q-2).descFactorial p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hp))
  have hx : (x.factorial : ℝ) ≠ 0 := by positivity
  have hy : (y.factorial : ℝ) ≠ 0 := by positivity
  have hh : (Q : ℝ)^x * (Q : ℝ)^y = (Q : ℝ)^p * Q := by
    rw [← pow_add, hxy, pow_succ]
  rw [mul_pow]
  field_simp
  have he := congrArg (fun t : ℝ => (Q.descFactorial x : ℝ) * (Q.descFactorial y : ℝ) * t) hh
  nlinarith only [he]

theorem pairCoefficient_conjugation (Q p : ℕ) (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (x y : Fin (Q+1)) :
    pairCoefficient Q p x y =
      modeFactor Q x.val * modeFactor Q y.val * pairFactor Q p *
        pairLimitCoefficient p x.val y.val := by
  unfold pairCoefficient pairLimitCoefficient modeFactor pairFactor
  split_ifs with h
  · have hr := pair_radicand_factorization Q p x.val y.val hQ hp h
    have hs := congrArg Real.sqrt hr
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity)] at hs
    rw [← hs]
    ring_nf
  · simp

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_Scaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem contraction_map {Q : ℕ} (f : Orbital Q →ₗ[ℂ] Orbital Q)
    (d : Module.Dual ℂ (Orbital Q)) (x : Space Q) :
    CliffordAlgebra.contractLeft d (ExteriorAlgebra.map f x) =
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (d.comp f) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    change CliffordAlgebra.contractLeft d (ExteriorAlgebra.map f (ExteriorAlgebra.ι ℂ m*x)) =
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (d.comp f) (ExteriorAlgebra.ι ℂ m*x))
    simp only [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
      LinearMap.comp_apply, map_sub, map_smul, hx]

theorem projection_scaling (Q : ℕ) (d : Fin (Q+1) → ℂ) (i : Fin (Q+1)) :
    (LinearMap.proj i).comp (orbitalScaling Q d) = d i • LinearMap.proj i := by
  ext v
  rfl

theorem annihilate_scaling (Q : ℕ) (d : Fin (Q+1) → ℂ) (i : Fin (Q+1)) (x : Space Q) :
    annihilate i (exteriorScaling Q d x) = d i • exteriorScaling Q d (annihilate i x) := by
  unfold annihilate exteriorScaling
  rw [contraction_map, projection_scaling, map_smul, LinearMap.smul_apply, map_smul]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_PairConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem pairEnd_smul (Q : ℕ) (r : ℂ) (c : Fin (Q+1) → Fin (Q+1) → ℂ) :
    pairEnd Q (fun i j => r*c i j) = r • pairEnd Q c := by
  simp only [pairEnd, Finset.smul_sum, smul_smul]

theorem pairEnd_scaling (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
    (d : Fin (Q+1) → ℂ) (x : Space Q) :
    pairEnd Q c (exteriorScaling Q d x) =
      exteriorScaling Q d (pairEnd Q (fun i j => c i j*d i*d j) x) := by
  simp only [pairEnd, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    map_sum, map_smul, annihilate_scaling, smul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Exterior_OccupationMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology

theorem occupationNormSq_nonneg (Q : ℕ) (x : Space Q) : 0 ≤ occupationNormSq Q x := by
  unfold occupationNormSq
  positivity

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_FactorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem pairFactor_one_le (Q p : ℕ) (hp : p ≤ 2*Q-2) : 1 ≤ pairFactor Q p := by
  have hd : (0 : ℝ) < (2*Q-2).descFactorial p := by exact_mod_cast Nat.descFactorial_pos.mpr hp
  have hn : (2*Q-2).descFactorial p ≤ (2*Q)^p := by
    apply (Nat.descFactorial_le_pow (2*Q-2) p).trans
    exact Nat.pow_le_pow_left (Nat.sub_le _ _) p
  have hr : ((2*Q-2).descFactorial p : ℝ) ≤ ((2 : ℝ)*Q)^p := by exact_mod_cast hn
  have h := Real.sqrt_le_sqrt ((one_le_div hd).mpr hr)
  simpa [pairFactor] using h

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_EnergyReturn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationNormSq_smul (Q : ℕ) (c : ℂ) (x : Space Q) :
    occupationNormSq Q (c • x) = ‖c‖^2 * occupationNormSq Q x := by
  simp [occupationNormSq,mul_pow,Finset.mul_sum]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_TruncatedConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem truncated_sourcePair_intertwining (L Q p : ℕ) (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (hL : p+1 ≤ L) (x : Space Q) :
    truncatedScaling L Q (sourcePairEnd Q p x) =
      (pairFactor Q p : ℂ) • limitPairEnd Q p (truncatedScaling L Q x) := by
  have hc : (fun i j : Fin (Q+1) => ((pairCoefficient Q p i j / Real.sqrt 2 : ℝ) : ℂ)) =
      (fun i j => (pairFactor Q p : ℂ)*
        (((pairLimitCoefficient p i.val j.val / Real.sqrt 2 : ℝ) : ℂ)*
          (truncatedModeFactor L Q i : ℂ)*(truncatedModeFactor L Q j : ℂ))) := by
    funext i j
    rw [pairCoefficient_conjugation Q p hQ hp]
    by_cases hs : i.val+j.val=p+1
    · simp only [truncatedModeFactor,ite_eq_left (show i.val≤L by omega),ite_eq_left (show j.val≤L by omega)]
      push_cast
      ring
    · simp [pairLimitCoefficient,hs]
  unfold sourcePairEnd limitPairEnd truncatedScaling
  rw [hc,pairEnd_smul,LinearMap.smul_apply,map_smul,pairEnd_scaling]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_TruncatedPairReturn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem truncated_pair_energy_return (L Q p : ℕ) (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (hL : p+1 ≤ L) (x : Space Q) :
    occupationNormSq Q (limitPairEnd Q p (truncatedScaling L Q x)) ≤
      occupationNormSq Q (sourcePairEnd Q p x) := by
  have he := congrArg (occupationNormSq Q) (truncated_sourcePair_intertwining L Q p hQ hp hL x)
  rw [occupationNormSq_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ pairFactor Q p from Real.sqrt_nonneg _)] at he
  have hr := pairFactor_one_le Q p hp
  have hsq : 1 ≤ (pairFactor Q p)^2 := by nlinarith
  calc
    _ ≤ (pairFactor Q p)^2 * occupationNormSq Q (limitPairEnd Q p (truncatedScaling L Q x)) := by
      simpa using mul_le_mul_of_nonneg_right hsq (occupationNormSq_nonneg Q _)
    _ = occupationNormSq Q (truncatedScaling L Q (sourcePairEnd Q p x)) := he.symm
    _ ≤ _ := truncatedScaling_normSq_le_s50 L Q hQ _

theorem truncated_pair_window_return_s50_oai (Q : ℕ) (hQ : 24 ≤ Q) (x : Space Q) :
    limitPairWindow Q (truncatedScaling 24 Q x) ≤ sourcePairWindow Q x := by
  unfold limitPairWindow sourcePairWindow
  apply Finset.sum_le_sum
  intro p hp
  have hp' := Finset.mem_range.mp hp
  exact truncated_pair_energy_return 24 Q p (by omega) (by omega) (by omega) x

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.truncated_pair_window_return_s50_oai := @OAI.Laughlin.Fock.truncated_pair_window_return_s50_oai
