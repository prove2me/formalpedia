-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.inducedE3_eq_pow_three_mul_of_fibre_eq_pow_inertiaDeg_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/6204e618-b976-5c13-8d23-96bb4e182a43

import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_inducedE3_eq_pow_three_mul_of_fibre_eq_pow_inertiaDeg_mul

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg

private theorem inducedFactor_eq_comp_of_mem_primeFibre
    (K : Type) [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (v : HeightOneSpectrum (𝓞 ℚ)) (a : ℂ) (c c' : HeightOneSpectrum (𝓞 K) → ℂ)
    (hc : ∀ w ∈ primeFibre ℚ K v, c' w = a ^ (v.asIdeal.inertiaDeg' w.asIdeal) * c w)
    (w : HeightOneSpectrum (𝓞 K)) (hw : w ∈ primeFibre ℚ K v) :
    inducedFactor ℚ c' w = (inducedFactor ℚ c w).comp (Polynomial.C a * Polynomial.X) := by
  have hv : w.under (𝓞 ℚ) = v := hw
  simp only [inducedFactor, hv, hc w hw, Polynomial.sub_comp, Polynomial.C_comp, Polynomial.C_mul_comp,
    Polynomial.pow_comp, Polynomial.X_comp, mul_pow, ← Polynomial.C_pow, Polynomial.C_mul]
  ring

private theorem comp_finprod_mem_of_injective {ι : Type} (S : Set ι) (f : ι → Polynomial ℂ) (q : Polynomial ℂ)
    (hq : Function.Injective fun p : Polynomial ℂ => p.comp q) :
    (∏ᶠ i ∈ S, f i).comp q = ∏ᶠ i ∈ S, (f i).comp q := by
  have hinj : Function.Injective (Polynomial.compRingHom q).toMonoidHom := fun p p' h => hq (by simpa using h)
  have h1 := MonoidHom.map_finprod_of_injective (Polynomial.compRingHom q).toMonoidHom hinj
    (fun i => ∏ᶠ (_ : i ∈ S), f i)
  have h2 : ∀ i, (Polynomial.compRingHom q).toMonoidHom (∏ᶠ (_ : i ∈ S), f i) =
      ∏ᶠ (_ : i ∈ S), (Polynomial.compRingHom q).toMonoidHom (f i) :=
    fun i => MonoidHom.map_finprod_Prop _ _
  simp only [h2] at h1
  simpa using h1

private theorem inducedEulerPoly_eq_comp
    (K : Type) [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (v : HeightOneSpectrum (𝓞 ℚ)) (a : ℂ) (ha : a ≠ 0) (c c' : HeightOneSpectrum (𝓞 K) → ℂ)
    (hc : ∀ w ∈ primeFibre ℚ K v, c' w = a ^ (v.asIdeal.inertiaDeg' w.asIdeal) * c w) :
    inducedEulerPoly ℚ c' v = (inducedEulerPoly ℚ c v).comp (Polynomial.C a * Polynomial.X) := by
  have hinj : Function.Injective fun p : Polynomial ℂ => p.comp (Polynomial.C a * Polynomial.X) := by
    intro p p' h
    ext n
    have hn := congrArg (fun r : Polynomial ℂ => r.coeff n) h
    simp only [Polynomial.comp_C_mul_X_coeff] at hn
    exact mul_right_cancel₀ (pow_ne_zero n ha) hn
  unfold inducedEulerPoly
  rw [comp_finprod_mem_of_injective (primeFibre ℚ K v) (inducedFactor ℚ c) _ hinj]
  exact finprod_mem_congr rfl fun w hw => inducedFactor_eq_comp_of_mem_primeFibre K v a c c' hc w hw

theorem solution
    (K : Type) [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    (c c' : HeightOneSpectrum (𝓞 K) → ℂ)
    (hc : ∀ w ∈ primeFibre ℚ K v,
      c' w = (χ (uniformizerIdele ℚ v) : ℂ) ^ (v.asIdeal.inertiaDeg' w.asIdeal) * c w) :
    inducedE3 ℚ c' v = (χ (uniformizerIdele ℚ v) : ℂ) ^ 3 * inducedE3 ℚ c v := by
  unfold inducedE3
  rw [inducedEulerPoly_eq_comp K v (χ (uniformizerIdele ℚ v) : ℂ) (Units.ne_zero _) c c' hc,
    Polynomial.comp_C_mul_X_coeff]
  ring

end S_LanglandsTunnell_CubicInduction_inducedE3_eq_pow_three_mul_of_fibre_eq_pow_inertiaDeg_mul
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_inducedE3_eq_pow_three_mul_of_fibre_eq_pow_inertiaDeg_mul (solution)
