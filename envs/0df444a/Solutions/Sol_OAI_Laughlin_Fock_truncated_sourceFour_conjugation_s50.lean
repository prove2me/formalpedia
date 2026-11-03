-- Prove2me | solution 1 for OAI.Laughlin.Fock.truncated_sourceFour_conjugation_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:35:39.240405+00:00
-- url     : https://prove2.me/submissions/ed1317b2-3621-47cb-ba7f-4cbb38f2f0da

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L017

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

theorem exteriorScaling_inverse (Q : ℕ) (d : Fin (Q+1) → ℂ) (hd : ∀ i, d i ≠ 0)
    (x : Space Q) : exteriorScaling Q (fun i => (d i)⁻¹) (exteriorScaling Q d x) = x := by
  have h : (orbitalScaling Q (fun i => (d i)⁻¹)).comp (orbitalScaling Q d) = LinearMap.id := by
    apply LinearMap.ext
    intro v
    funext i
    change (d i)⁻¹*(d i*v i) = v i
    rw [← mul_assoc, inv_mul_cancel₀ (hd i), one_mul]
  change ((ExteriorAlgebra.map (orbitalScaling Q (fun i => (d i)⁻¹))).comp
    (ExteriorAlgebra.map (orbitalScaling Q d))) x = x
  rw [ExteriorAlgebra.map_comp_map, h, ExteriorAlgebra.map_id]
  rfl

theorem modeFactor_pos (Q : ℕ) (hQ : 0 < Q) (i : Fin (Q+1)) : 0 < modeFactor Q i.val := by
  unfold modeFactor
  apply Real.sqrt_pos.mpr
  apply div_pos
  · exact_mod_cast (Nat.descFactorial_pos.mpr (show i.val ≤ Q by omega))
  · exact pow_pos (by exact_mod_cast hQ) _

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_TruncatedScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem truncatedModeFactor_pos (L Q : ℕ) (hQ : 0 < Q) (i : Fin (Q+1)) :
    0 < truncatedModeFactor L Q i := by
  unfold truncatedModeFactor
  split_ifs
  · exact modeFactor_pos Q hQ i
  · norm_num

theorem truncatedScaling_left_inverse (L Q : ℕ) (hQ : 0 < Q) (x : Space Q) :
    truncatedScalingInv L Q (truncatedScaling L Q x) = x := by
  apply exteriorScaling_inverse
  intro i
  exact_mod_cast ne_of_gt (truncatedModeFactor_pos L Q hQ i)

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

theorem truncated_sourceFour_conjugation_s50_oai (L Q p : ℕ) (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (hL : p+1 ≤ L) (j k : Fin (Q+1))
    (hjL : j.val ≤ L) (hkL : k.val ≤ L) (x : Space Q) :
    sourceFourEnd Q p j k x =
      ((pairFactor Q p : ℂ)/((modeFactor Q j.val : ℂ)*(modeFactor Q k.val : ℂ))) •
        truncatedScalingInv L Q (limitFourEnd Q p j k (truncatedScaling L Q x)) := by
  have h := congrArg (fun y => annihilate k (annihilate j y))
    (truncated_sourcePair_intertwining L Q p hQ hp hL x)
  have he : ((modeFactor Q j.val : ℂ)*(modeFactor Q k.val : ℂ)) •
      truncatedScaling L Q (sourceFourEnd Q p j k x) =
        (pairFactor Q p : ℂ) • limitFourEnd Q p j k (truncatedScaling L Q x) := by
    simpa only [sourceFourEnd,limitFourEnd,Module.End.mul_apply,truncatedScaling,
      annihilate_scaling,map_smul,smul_smul,truncatedModeFactor,ite_eq_left hjL,ite_eq_left hkL] using h
  have h' := congrArg (truncatedScalingInv L Q) he
  rw [map_smul,truncatedScaling_left_inverse L Q hQ,map_smul] at h'
  have hj : (modeFactor Q j.val : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (modeFactor_pos Q hQ j)
  have hk : (modeFactor Q k.val : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (modeFactor_pos Q hQ k)
  have hd := mul_ne_zero hj hk
  calc
    _ = ((modeFactor Q j.val : ℂ)*(modeFactor Q k.val : ℂ))⁻¹ •
        (((modeFactor Q j.val : ℂ)*(modeFactor Q k.val : ℂ)) • sourceFourEnd Q p j k x) := by
      rw [smul_smul,inv_mul_cancel₀ hd,one_smul]
    _ = _ := by rw [h',smul_smul]; congr 1; ring

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.truncated_sourceFour_conjugation_s50_oai := @OAI.Laughlin.Fock.truncated_sourceFour_conjugation_s50_oai
