-- Prove2me | solution 1 for OAI.SevenEighths.ProbeEuler.rowClosedMarked_unramified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:07:15.709766+00:00
-- url     : https://prove2.me/submissions/f5b925f8-c882-406a-8ae1-479899768d97

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B017
import Theorems.Thm_OAI_SevenEighths_ProbeEuler_principalMarkedSeries_eq
import Theorems.Thm_OAI_SevenEighths_ProbeEuler_rowMarkedSeries_eq_closed

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsWeights
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

theorem rowWeightedScalar_parameters (Q eta a G1 C omega X W V rho scalar : ℂ)
    (e l k m : ℕ) :
    rowWeightedScalar Q eta a G1 C omega X W V rho scalar e l k m=
      weightedScalar Q (eta/rho) (a/rho^3) G1 C omega X (rho*W) V scalar e l k m := by
  unfold rowWeightedScalar weightedScalar
  simp only [pow_add,pow_mul,mul_pow,div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

theorem evenRatio_unit (Q a X V rho : ℂ) (hρ : rho^6=1) :
    evenRatio Q (a/rho^3) X V=evenRatio Q a X V := by
  unfold evenRatio
  rw [div_pow,←pow_mul,show 3*2=6 by decide,hρ,div_one]

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsUnramified
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

lemma rowMarkedTerm_unramified (eta a X W V rho : ℂ) (e l k m : ℕ) :
    rowMarkedTerm p hp hg eta a X W V rho 0 e l k m=
      principalMarkedTerm p hp hg (eta/rho) (a/rho^3) X (rho*W) V e l k m := by
  unfold rowMarkedTerm principalMarkedTerm
  split_ifs
  · rfl
  · simp only [zero_add,rowWeightedScalar_parameters]

lemma rowMarkedSeries_unramified (eta a X W V rho : ℂ) :
    rowMarkedSeries p hp hg eta a X W V rho 0=
      principalMarkedSeries p hp hg (eta/rho) (a/rho^3) X (rho*W) V := by
  unfold rowMarkedSeries principalMarkedSeries rowInner principalInner
  apply Finset.sum_congr rfl
  intro e he
  apply tsum_congr
  intro l
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  exact rowMarkedTerm_unramified p hp hg eta a X W V rho e.val l k m

include hc in
lemma rowClosedMarked_unramified_oai (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1) :
    rowClosedMarked p hp hg eta a X W V rho 0=
      markedFactor (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) V
        (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹
        (eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W)
        (-(eta/rho)*X+(rho*W)*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) 1 := by
  have hn : rho≠0 := by intro h; simp [h] at hρ
  rw [←rowMarkedSeries_eq_closed p hp hg hc eta a X W V rho hρ hV hR 0 (by decide),
    rowMarkedSeries_unramified p hp hg,
    principalMarkedSeries_eq p hp hg hc _ _ _ _ _ hV
      (by simpa only [evenRatio_unit _ _ _ _ _ hρ] using hR),
    evenRatio_unit _ _ _ _ _ hρ]
  congr 1
  field_simp

end SevenEighths.ProbeEuler
end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.ProbeEuler.rowClosedMarked_unramified_oai := @OAI.SevenEighths.ProbeEuler.rowClosedMarked_unramified_oai
