-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.finite_setOf_isRamifiedIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/2fb2f6a8-46fd-5596-a8c5-4224e2806a5e

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_finite_setOf_isRamifiedIn

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

p2m_attr_erase "instance" "NumberField.RingOfIntegers.instAlgebra in"
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in
theorem solution
    (K : Type) [Field K] [NumberField K] :
    {v : HeightOneSpectrum (𝓞 ℚ) | IsRamifiedIn K v}.Finite := by
  classical
  haveI : Algebra.IsAlgebraic (FractionRing (𝓞 ℚ)) (FractionRing (𝓞 K)) :=
    isAlgebraic_of_isFractionRing (R := 𝓞 ℚ) (S := 𝓞 K) ..
  haveI : Algebra.IsSeparable (FractionRing (𝓞 ℚ)) (FractionRing (𝓞 K)) := inferInstance
  have hD : differentIdeal (𝓞 ℚ) (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  have hfinK : {𝔓 : HeightOneSpectrum (𝓞 K) | 𝔓.asIdeal ∣ differentIdeal (𝓞 ℚ) (𝓞 K)}.Finite :=
    Ideal.finite_factors hD
  refine (hfinK.image fun 𝔓 => 𝔓.under (𝓞 ℚ)).subset ?_
  rintro v ⟨𝔓, h𝔓, hne⟩
  refine ⟨𝔓, ?_, (LanglandsTunnell.RankinSelberg.mem_primeFibre ℚ v 𝔓).mp h𝔓⟩
  show 𝔓.asIdeal ∣ differentIdeal (𝓞 ℚ) (𝓞 K)
  by_contra hndvd
  haveI : Algebra.IsUnramifiedAt (𝓞 ℚ) 𝔓.asIdeal := not_dvd_differentIdeal_iff.mp hndvd
  have h1 := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 ℚ) (p := 𝔓.asIdeal)
  apply hne
  have hv : v.asIdeal = 𝔓.asIdeal.under (𝓞 ℚ) := by
    rw [← (LanglandsTunnell.RankinSelberg.mem_primeFibre ℚ v 𝔓).mp h𝔓]
    rfl
  rw [hv, Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.asIdeal.under (𝓞 ℚ)) 𝔓.asIdeal (hv ▸ v.ne_bot)]
  exact h1

end S_LanglandsTunnell_CubicInduction_finite_setOf_isRamifiedIn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_finite_setOf_isRamifiedIn (solution)
