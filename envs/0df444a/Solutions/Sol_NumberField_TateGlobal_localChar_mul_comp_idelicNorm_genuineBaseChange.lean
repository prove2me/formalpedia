-- Prove2me | solution 1 for NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a64c1e27-5e9d-58f0-891b-d812fe2b6084

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_M4aHerbrand_genuineAdelicNorm_componentwise
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_NumberField_TateGlobal_localChar_mul_comp_idelicNorm_genuineBaseChange
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open NumberField NumberField.TateGlobal NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum M4aHerbrand.GenuineDescent

namespace Ws45
namespace G1

open M4aHerbrand M4aHerbrand.Bridge

theorem idelicNorm_finIncl_localUnit
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M)) (u : (w.1.adicCompletion M)ˣ) :
    (genuineBaseChange E M).idelicNorm (Units.map (finIncl (𝓞 M) M) (localUnit (𝓞 M) M w.1 u)) =
      Units.map (finIncl (𝓞 E) E)
        (localUnit (𝓞 E) E v (Units.map (Algebra.norm (v.adicCompletion E)) u)) := by
  classical
  apply Units.ext
  show (letI := (genuineβ E M).toAlgebra;
      Algebra.norm (AdeleRing (𝓞 E) E)
        (finIncl (𝓞 M) M ((localUnit (𝓞 M) M w.1 u : (FiniteAdeleRing (𝓞 M) M)ˣ) : FiniteAdeleRing (𝓞 M) M)))
      = finIncl (𝓞 E) E ((localUnit (𝓞 E) E v (Units.map (Algebra.norm (v.adicCompletion E)) u)
          : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E)
  obtain ⟨h1, h2⟩ := M4aHerbrand.genuineAdelicNorm_componentwise E M
    (finIncl (𝓞 M) M ((localUnit (𝓞 M) M w.1 u : (FiniteAdeleRing (𝓞 M) M)ˣ) : FiniteAdeleRing (𝓞 M) M))
  refine Prod.ext ?_ ?_
  · rw [h1, finIncl_apply_fst, finIncl_apply_fst, map_one]
  · rw [finIncl_apply_snd]
    ext v'
    rw [h2 v']
    rcases eq_or_ne v' v with rfl | hv'
    · rw [localUnit_apply_self, Finset.prod_eq_single w]
      · rw [finIncl_apply_snd, localUnit_apply_self, Units.coe_map]
      · intro w' _ hw'
        have hne : w'.1 ≠ w.1 := fun h => hw' (Subtype.ext h)
        rw [finIncl_apply_snd, localUnit_apply_of_ne (𝓞 M) M w.1 u hne, map_one]
      · intro h
        simp at h
    · rw [localUnit_apply_of_ne (𝓞 E) E v _ hv']
      refine Finset.prod_eq_one fun w' _ => ?_
      have hne : w'.1 ≠ w.1 := by
        intro h
        apply hv'
        calc v' = w'.1.under (𝓞 E) := w'.2.symm
          _ = w.1.under (𝓞 E) := by rw [h]
          _ = v := w.2
      rw [finIncl_apply_snd, localUnit_apply_of_ne (𝓞 M) M w.1 u hne, map_one]

end Ws45.G1

theorem solution
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M)) :
    localChar (ξ * μ.comp (genuineBaseChange E M).idelicNorm) w.1 =
      localChar ξ w.1 * (localChar μ v).comp (Units.map (Algebra.norm (v.adicCompletion E))) := by
  refine MonoidHom.ext fun u => ?_
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, localChar_apply]
  rw [Ws45.G1.idelicNorm_finIncl_localUnit]

end S_NumberField_TateGlobal_localChar_mul_comp_idelicNorm_genuineBaseChange
end P2MW
export P2MW.S_NumberField_TateGlobal_localChar_mul_comp_idelicNorm_genuineBaseChange (solution)
