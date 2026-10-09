-- Prove2me | solution 1 for OAI.SevenEighths.ProbeEuler.sourceWeightedScalar_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T20:35:04.352189+00:00
-- url     : https://prove2.me/submissions/0044ba72-0a92-489f-893d-0a7b8f68b24d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B000
import Definitions.Def_OAIHecke78B003

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsTermBounds
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma sourceWeightedScalar_norm_le_oai (Q : ℝ) (hQ : 0<Q)
    (eta a gamma C omega x w z scalar : ℂ) (heta : ‖eta‖≤1) (ha : ‖a‖≤1)
    (hgamma : ‖gamma‖=1) (hC : ‖C‖=1) (ho : ‖omega‖=1) (e l k m : ℕ) :
    ‖sourceWeightedScalar Q eta a gamma C omega x w z scalar e l k m‖≤
      ‖scalar‖*Q^(-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)) := by
  let coeff : ℂ := (-1:ℂ)^e*gamma^(-(e:ℤ))*eta^e*(a*C)^l*
    omega^((((e+3*l)*k:ℕ):ℤ)-(e*l+l.choose 2:ℕ))
  have hn : ‖coeff‖≤1 := by
    simp only [coeff,norm_mul,norm_pow,norm_zpow,hgamma,hC,ho,norm_neg,norm_one,
      one_pow,one_zpow,mul_one,one_mul]
    exact (mul_le_of_le_one_left (by positivity) (pow_le_one₀ (norm_nonneg _) heta)).trans (pow_le_one₀ (norm_nonneg _) ha)
  change ‖coeff*scalar*(Q:ℂ)^_‖≤_
  rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  have he : (-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)).re=
      -(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ) := by simp
  rw [he]
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _) hn) (by positivity)

end SevenEighths.ProbeEuler
end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.ProbeEuler.sourceWeightedScalar_norm_le_oai := @OAI.SevenEighths.ProbeEuler.sourceWeightedScalar_norm_le_oai
