-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.two_mul_ramificationIdx_mul_add_one_le_conductorExponentAt_of_depth_floor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/897a2e94-9c50-5d2e-b196-b71d5d26216b

import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_two_mul_ramificationIdx_mul_add_one_le_conductorExponentAt_of_depth_floor

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_two_mul_ramificationIdx_mul_add_one_le_conductorExponentAt_of_depth_floor.LanglandsTunnell.RankinSelberg"
open scoped nonZeroDivisors

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.addCharLevel TateLocal.addCharLevel_def TateLocal.conductorExponentAt TateLocal.psiLocal_eq_one_of_mem_integers"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "primeFibre mem_primeFibre"
namespace DepthFloorSol
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

theorem algebraMap_ringOfIntegers_rat_injective (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] : Function.Injective (algebraMap (𝓞 ℚ) (𝓞 K)) := by
  have hg : Function.Injective
      ((algebraMap (𝓞 ℚ) (𝓞 K)).comp Rat.ringOfIntegersEquiv.symm.toRingHom) :=
    RingHom.injective_int _
  intro x y hxy
  apply Rat.ringOfIntegersEquiv.injective
  apply hg
  change algebraMap (𝓞 ℚ) (𝓞 K) (Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv x)) =
    algebraMap (𝓞 ℚ) (𝓞 K) (Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv y))
  rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  exact hxy

theorem ramificationIdx_mul_le_count_map (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (w : HeightOneSpectrum (𝓞 K)) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (b : ℕ)
    (hb : (w.under (𝓞 ℚ)).asIdeal ^ b ∣ N) :
    ((Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal * b : ℕ) : ℤ) ≤
      FractionalIdeal.count K w
        (N.map (algebraMap (𝓞 ℚ) (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
  set q : Ideal (𝓞 ℚ) := (w.under (𝓞 ℚ)).asIdeal with hq
  set e : ℕ := Ideal.ramificationIdx' q w.asIdeal with he

  have h1 : Ideal.map (algebraMap (𝓞 ℚ) (𝓞 K)) q ≤ w.asIdeal ^ e := Ideal.le_pow_ramificationIdx

  have h2 : N ≤ q ^ b := Ideal.le_of_dvd hb

  have h3 : Ideal.map (algebraMap (𝓞 ℚ) (𝓞 K)) N ≤ w.asIdeal ^ (e * b) := by
    refine (Ideal.map_mono h2).trans ?_
    rw [Ideal.map_pow, pow_mul]
    exact Ideal.pow_right_mono h1 b
  set J : Ideal (𝓞 K) := Ideal.map (algebraMap (𝓞 ℚ) (𝓞 K)) N with hJ
  have hJne : J ≠ ⊥ :=
    fun h => hN ((Ideal.map_eq_bot_iff_of_injective
      (algebraMap_ringOfIntegers_rat_injective K)).mp h)
  have hJne' : (J : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hJne
  have h4 : (J : FractionalIdeal (𝓞 K)⁰ K) ≤
      (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (e * b) := by
    rw [← FractionalIdeal.coeIdeal_pow]
    exact (FractionalIdeal.coeIdeal_le_coeIdeal K).mpr h3
  have h5 := FractionalIdeal.count_mono K w hJne' h4
  rwa [FractionalIdeal.count_pow_self] at h5

theorem addCharLevel_psiLocal_nonneg (K : Type) [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) :
    0 ≤ LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) := by
  rw [LanglandsTunnell.TateLocal.addCharLevel_def]
  set S : Set ℤ := {n : ℤ | ∀ x : w.adicCompletion K, Valued.v x ≤ WithZero.exp n →
      NumberField.StandardAddChar.psiLocal K w x = 1} with hS
  have h0 : (0 : ℤ) ∈ S := by
    intro x hx
    rw [WithZero.exp_zero] at hx
    exact LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers K w x hx
  by_cases hbdd : BddAbove S
  · exact le_csSup hbdd h0
  · rw [Int.csSup_of_not_bddAbove hbdd]

end LanglandsTunnell.RankinSelberg.DepthFloorSol

open LanglandsTunnell.RankinSelberg.DepthFloorSol in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (N : Ideal (𝓞 ℚ))
    (hfloor : ∀ w ∈ primeFibre ℚ K p,
      4 * (FractionalIdeal.count K w
            ((N.map (algebraMap (𝓞 ℚ) (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) +
          LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 1) ≤
        LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w))
    (b : ℕ)
    (hNb : p.asIdeal ^ b ∣ N ∧ ¬ p.asIdeal ^ (b + 1) ∣ N) :
              (∀ w ∈ primeFibre ℚ K p,
            2 * (Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal * b) + 1 ≤
              LanglandsTunnell.TateLocal.conductorExponentAt K w (NumberField.TateGlobal.localChar μ w)) := by
  intro w hw
  have hwp : w.under (𝓞 ℚ) = p := (mem_primeFibre ℚ p w).mp hw

  have hN : N ≠ ⊥ := by
    rintro rfl
    exact hNb.2 (dvd_zero _)
  have hpb : (w.under (𝓞 ℚ)).asIdeal ^ b ∣ N := by
    rw [hwp]
    exact hNb.1
  have hA := ramificationIdx_mul_le_count_map K w N hN b hpb
  have hB := addCharLevel_psiLocal_nonneg K w
  have hF := hfloor w hw
  push_cast at hA hF
  omega

end S_LanglandsTunnell_RankinSelberg_two_mul_ramificationIdx_mul_add_one_le_conductorExponentAt_of_depth_floor
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_two_mul_ramificationIdx_mul_add_one_le_conductorExponentAt_of_depth_floor (solution)
