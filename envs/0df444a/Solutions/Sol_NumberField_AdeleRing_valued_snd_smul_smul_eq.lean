-- Prove2me | solution 1 for NumberField.AdeleRing.valued_snd_smul_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/bb133a84-9d5c-5d13-a2ad-e4bab154c0c3

import Mathlib
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdeleRing_valued_snd_smul_smul_eq

set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped NumberField.PlaceTransport

theorem solution
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((((g • x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) (g • w)) =
      Valued.v (((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 K) E K
  have hD : D = M4aHerbrand.GenuineDescent.genuineDescentDatum E K := Subsingleton.elim _ _
  rw [hactI]
  have h1 : ((((D.unitsAct g x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) (g • w)) = ((D.act g (x : AdeleRing (𝓞 K) K)).2 : FiniteAdeleRing (𝓞 K) K) (g • w) := rfl
  rw [h1, hD, M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply E K g (x : AdeleRing (𝓞 K) K) (rfl : g • w = g • w),
    NumberField.PlaceTransport.valued_transport]

end S_NumberField_AdeleRing_valued_snd_smul_smul_eq
end P2MW
export P2MW.S_NumberField_AdeleRing_valued_snd_smul_smul_eq (solution)
