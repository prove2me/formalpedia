-- Prove2me | solution 1 for GlobalTheory.DiscrJacobian.map_mem_radical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:27:44.907174+00:00
-- url     : https://prove2.me/submissions/41251837-8261-49b9-ba43-186afde5690b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrMulDetEqNormOfAnnihilator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsUnitDetOfProductMapNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscrJacobian
open scoped TensorProduct
open MvPowerSeries IsLocalRing
open MvPowerSeries IsLocalRing
open scoped TensorProduct
namespace GlobalTheory.DiscrJacobian
namespace _root_.GlobalTheory.DiscrJacobian
theorem _root_.solution {R S B : Type} [CommRing R]
    [IsLocalRing R] [CommRing S] [CommRing B]
    [Algebra R B] [Algebra S B] [Module.Finite R B] (hsurj : Function.Surjective (algebraMap S B))
    {x : S} (hx : x ∈ (⊥ : Ideal S).jacobson) :
    algebraMap S B x ∈ ((maximalIdeal R).map (algebraMap R B)).radical := by
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  intro P hPmem
  have hP : Ideal.map (algebraMap R B) (maximalIdeal R) ≤ P := hPmem.1
  haveI hPprime : P.IsPrime := hPmem.2
  have hle : maximalIdeal R ≤ P.comap (algebraMap R B) := Ideal.map_le_iff_le_comap.mp hP
  haveI : (P.comap (algebraMap R B)).IsPrime := Ideal.IsPrime.comap (algebraMap R B)
  have hcomap : P.comap (algebraMap R B) = maximalIdeal R :=
    le_antisymm (IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top') hle
  have hm : (P.comap (algebraMap R B)).IsMaximal := by
    rw [hcomap]; exact maximalIdeal.isMaximal R
  haveI : Algebra.IsIntegral R B := Algebra.IsIntegral.of_finite R B
  haveI hPmax : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P hm
  have hmax : (P.comap (algebraMap S B)).IsMaximal := Ideal.comap_isMaximal_of_surjective _ hsurj
  unfold Ideal.jacobson at hx
  exact Ideal.mem_sInf.mp hx ⟨bot_le, hmax⟩
end _root_.GlobalTheory.DiscrJacobian
end GlobalTheory.DiscrJacobian
