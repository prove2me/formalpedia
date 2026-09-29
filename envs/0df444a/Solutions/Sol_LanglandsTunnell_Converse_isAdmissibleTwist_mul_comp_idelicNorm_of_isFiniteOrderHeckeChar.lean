-- Prove2me | solution 1 for LanglandsTunnell.Converse.isAdmissibleTwist_mul_comp_idelicNorm_of_isFiniteOrderHeckeChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ea53b1e1-cd6b-55e0-b3b3-78742ebcfd2e

import Mathlib
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange
import Theorems.Thm_M4aHerbrand_GenuineDescent_adelicNorm_genuineBaseChange_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_isAdmissibleTwist_mul_comp_idelicNorm_of_isFiniteOrderHeckeChar

set_option autoImplicit false

open NumberField HeckeCharacter LanglandsTunnell.Converse M4aHerbrand.GenuineDescent

namespace LanglandsTunnell
namespace P2ind
p2m_open "LanglandsTunnell"

theorem norm_apply_eq_one_of_isOfFinOrder' {G : Type} [Group G] (χ : G →* ℂˣ) (hχ : IsOfFinOrder χ) (x : G) :
    ‖((χ x : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, hχn⟩ := hχ.exists_pow_eq_one
  have h1 : ((χ x : ℂˣ) : ℂ) ^ n = 1 := by
    have := congrArg (fun f : G →* ℂˣ => ((f x : ℂˣ) : ℂ)) hχn
    simpa using this
  have h2 : ‖((χ x : ℂˣ) : ℂ)‖ ^ n = 1 := by rw [← norm_pow, h1, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp h2

theorem _root_.P2MW.S_LanglandsTunnell_Converse_isAdmissibleTwist_mul_comp_idelicNorm_of_isFiniteOrderHeckeChar.solution
    (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (hξ : IsFiniteOrderHeckeChar M ξ)
    (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist E μ) :
    IsAdmissibleTwist M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) := by
  set N := (genuineBaseChange E M).idelicNorm with hN
  refine ⟨?_, ?_, ?_⟩
  ·
    intro u
    show ξ (Units.map (algebraMap M (AdeleRing (𝓞 M) M)) u) * μ (N (Units.map (algebraMap M (AdeleRing (𝓞 M) M)) u)) = 1
    rw [hξ.isIdeleClassChar u, one_mul]
    have hunit : (Algebra.norm E (u : M)) ≠ 0 := by
      rw [Ne, Algebra.norm_eq_zero_iff]
      exact u.ne_zero
    have hNu : N (Units.map (algebraMap M (AdeleRing (𝓞 M) M)) u) =
        Units.map (algebraMap E (AdeleRing (𝓞 E) E)) (Units.mk0 _ hunit) := by
      ext
      show (genuineBaseChange E M).adelicNorm (algebraMap M (AdeleRing (𝓞 M) M) (u : M)) = algebraMap E (AdeleRing (𝓞 E) E) (Algebra.norm E (u : M))
      exact M4aHerbrand.GenuineDescent.adelicNorm_genuineBaseChange_algebraMap E M (u : M)
    rw [hNu]
    exact hμ.1 _
  ·
    have hcontN : Continuous N := by
      rw [hN]
      exact Continuous.units_map _ (M4aHerbrand.GenuineDescent.continuous_adelicNorm_genuineBaseChange E M)
    show Continuous (fun x => ξ x * μ (N x))
    exact hξ.continuous.mul (hμ.2.1.comp hcontN)
  ·
    intro x
    show ‖((ξ x * μ (N x) : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_mul, norm_mul, norm_apply_eq_one_of_isOfFinOrder' ξ hξ.isOfFinOrder x, hμ.2.2 _, one_mul]

end LanglandsTunnell.P2ind

end S_LanglandsTunnell_Converse_isAdmissibleTwist_mul_comp_idelicNorm_of_isFiniteOrderHeckeChar
end P2MW
export P2MW.S_LanglandsTunnell_Converse_isAdmissibleTwist_mul_comp_idelicNorm_of_isFiniteOrderHeckeChar (solution)
