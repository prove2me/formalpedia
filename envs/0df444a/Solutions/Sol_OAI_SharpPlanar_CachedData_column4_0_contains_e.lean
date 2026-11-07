-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.column4_0_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T16:51:56.755202+00:00
-- url     : https://prove2.me/submissions/93d04173-b9f0-4ad4-beca-6399ce02ac6a

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_CachedData_amp4_0_contains_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_column4_0_eq_e
import Theorems.Thm_OAI_SharpPlanar_CachedData_power4_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_phase12_periodic_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma phase12_mod (n : ℕ) : phase12 (n%12) = phase12 n :=
  (show Function.Periodic phase12 12 from phase12_periodic_e).map_mod_nat n

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma u_factored (n j : ℕ) (t : ℝ) : u n j t =
    -2*(Real.pi:ℂ)^2*Complex.exp (-Complex.I*Real.pi*t*n)*
      (basisBeta n j-(t:ℂ)*basisAlpha n j) := by
  unfold u basisBeta basisAlpha spectralCoefficient
  congr 1
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring
lemma v_factored (n j : ℕ) (t : ℝ) : v n j t =
    2*Complex.I*Real.pi*Complex.exp (-Complex.I*Real.pi*t*n)*basisAlpha n j := by
  unfold v basisAlpha spectralCoefficient
  rfl

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma spectralCoefficient_eq_phase (n l : ℕ) :
    spectralCoefficient n l = Pcoeff l*phase12 (l*n) := by
  unfold spectralCoefficient phase12
  congr 2
  push_cast
  ring
lemma spectralCoefficient_mod (n l : ℕ) :
    spectralCoefficient (n%12) l = spectralCoefficient n l := by
  simp only [spectralCoefficient_eq_phase]
  rw [← phase12_mod (l*(n%12)),← phase12_mod (l*n)]
  congr 2
  simp only [Nat.mul_mod, Nat.mod_mod]
lemma basisAlpha_mod (n j : ℕ) : basisAlpha (n%12) j = basisAlpha n j := by
  unfold basisAlpha
  simp only [spectralCoefficient_mod]
lemma basisBeta_mod (n j : ℕ) : basisBeta (n%12) j = basisBeta n j := by
  unfold basisBeta
  simp only [spectralCoefficient_mod]

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma waveAmplitude_mod (d : Bool) (n j : ℕ) (t : ℝ) :
    waveAmplitude d (n%12) j t = waveAmplitude d n j t := by
  simp only [waveAmplitude,basisAlpha_mod,basisBeta_mod]
lemma basisFunction_wave (d : Bool) (n j : ℕ) (t : ℝ) :
    basisFunction d n j t = waveAmplitude d n j t*Complex.exp (-Complex.I*Real.pi*t*n) := by
  cases d <;> simp only [basisFunction,waveAmplitude,Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
  · rw [u_factored]; ring
  · rw [v_factored]; ring

end SharpPlanar.IntegerBasis

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma column4_0_contains_e_oai (j : Fin 6) (i k : Fin 16) :
    (column4_0 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*basisFunction false 4 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← column4_0_eq_e,basisFunction_wave,← mul_assoc]
  unfold column4_0Expr
  apply CBox.contains_mul_e
  · rw [← waveAmplitude_mod false 4 j.val (quadraturePoint j.val (16*i.val+k.val))]
    exact amp4_0_contains_e j i k
  · exact power4_contains_e j i k
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.column4_0_contains_e_oai := @OAI.SharpPlanar.CachedData.column4_0_contains_e_oai
