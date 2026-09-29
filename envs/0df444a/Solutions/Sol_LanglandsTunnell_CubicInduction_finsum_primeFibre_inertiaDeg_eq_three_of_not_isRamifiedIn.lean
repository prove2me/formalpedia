-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.finsum_primeFibre_inertiaDeg_eq_three_of_not_isRamifiedIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/a35a88e6-bc2b-5fc7-a7f9-94edcc0feb2c

import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_finsum_primeFibre_inertiaDeg_eq_three_of_not_isRamifiedIn

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.RankinSelberg

section

open LanglandsTunnell.RankinSelberg

variable (F : Type) [Field F] [NumberField F]

private theorem asIdeal_mem_primesOver_of_mem_primeFibre (p : HeightOneSpectrum (𝓞 ℚ))
    {𝔓 : HeightOneSpectrum (𝓞 F)} (h : 𝔓 ∈ primeFibre ℚ F p) :
    𝔓.asIdeal ∈ p.asIdeal.primesOver (𝓞 F) := by
  rw [mem_primeFibre] at h
  refine ⟨𝔓.isPrime, ⟨?_⟩⟩
  rw [← h]
  rfl

private theorem image_asIdeal_primeFibre (p : HeightOneSpectrum (𝓞 ℚ)) :
    HeightOneSpectrum.asIdeal '' primeFibre ℚ F p = p.asIdeal.primesOver (𝓞 F) := by
  ext Q
  constructor
  · rintro ⟨𝔓, h𝔓, rfl⟩
    exact asIdeal_mem_primesOver_of_mem_primeFibre F p h𝔓
  · intro hQ
    haveI : Q.IsPrime := hQ.1
    haveI : Q.LiesOver p.asIdeal := hQ.2
    refine ⟨⟨Q, hQ.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot hQ⟩, ?_, rfl⟩
    rw [mem_primeFibre]
    apply HeightOneSpectrum.ext
    exact (Ideal.over_def Q p.asIdeal).symm

private theorem primeFibre_finite (p : HeightOneSpectrum (𝓞 ℚ)) :
    (primeFibre ℚ F p).Finite := by
  have hfin : (p.asIdeal.primesOver (𝓞 F)).Finite := IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 F)
  rw [← image_asIdeal_primeFibre F p] at hfin
  exact hfin.of_finite_image HeightOneSpectrum.asIdeal_injective.injOn

private theorem finsum_fibre_ramificationIdx_mul_inertiaDeg (p : HeightOneSpectrum (𝓞 ℚ)) :
    ∑ᶠ 𝔓 ∈ primeFibre ℚ F p, p.asIdeal.ramificationIdx' 𝔓.asIdeal * p.asIdeal.inertiaDeg' 𝔓.asIdeal =
      Module.finrank ℚ F := by
  calc ∑ᶠ 𝔓 ∈ primeFibre ℚ F p, p.asIdeal.ramificationIdx' 𝔓.asIdeal * p.asIdeal.inertiaDeg' 𝔓.asIdeal
      = ∑ᶠ Q ∈ HeightOneSpectrum.asIdeal '' primeFibre ℚ F p,
          p.asIdeal.ramificationIdx' Q * p.asIdeal.inertiaDeg' Q :=
        (finsum_mem_image (f := fun Q : Ideal (𝓞 F) => p.asIdeal.ramificationIdx' Q * p.asIdeal.inertiaDeg' Q)
          HeightOneSpectrum.asIdeal_injective.injOn).symm
    _ = ∑ᶠ Q ∈ p.asIdeal.primesOver (𝓞 F), p.asIdeal.ramificationIdx' Q * p.asIdeal.inertiaDeg' Q := by
        rw [image_asIdeal_primeFibre]
    _ = ∑ Q ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 F),
          p.asIdeal.ramificationIdx' Q * p.asIdeal.inertiaDeg' Q := by
        rw [← IsDedekindDomain.coe_primesOverFinset p.ne_bot (𝓞 F), finsum_mem_coe_finset]
    _ = Module.finrank ℚ F := Ideal.sum_ramification_inertia (𝓞 F) ℚ F p.ne_bot

end

private theorem ringHom_ringOfIntegers_rat_ext {S : Type*} [Ring S] (f g : 𝓞 ℚ →+* S) : f = g := by
  have h : f.comp (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) = g.comp (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) :=
    Subsingleton.elim _ _
  ext x
  have hx : x = (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) (Rat.ringOfIntegersEquiv x) :=
    (Rat.ringOfIntegersEquiv.symm_apply_apply x).symm
  rw [hx]
  exact RingHom.congr_fun h _

private theorem algebra_ringOfIntegers_rat_eq (X : Type) [Field X] [NumberField X] (i : Algebra (𝓞 ℚ) (𝓞 X)) :
    i = NumberField.inst_ringOfIntegersAlgebra ℚ X :=
  Algebra.algebra_ext i (NumberField.inst_ringOfIntegersAlgebra ℚ X) fun r =>
    RingHom.congr_fun
      (ringHom_ringOfIntegers_rat_ext (@algebraMap (𝓞 ℚ) (𝓞 X) _ _ i)
        (@algebraMap (𝓞 ℚ) (𝓞 X) _ _ (NumberField.inst_ringOfIntegersAlgebra ℚ X))) r

open LanglandsTunnell.CubicInduction in
theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ IsRamifiedIn K v) :
    ∑ᶠ 𝔓 ∈ primeFibre ℚ K v, v.asIdeal.inertiaDeg' 𝔓.asIdeal = 3 := by
  obtain rfl := algebra_ringOfIntegers_rat_eq K ‹Algebra (𝓞 ℚ) (𝓞 K)›
  rw [IsRamifiedIn] at hv
  rw [← hdeg, ← finsum_fibre_ramificationIdx_mul_inertiaDeg K v]
  refine finsum_mem_congr rfl fun 𝔓 h𝔓 => ?_
  have he : v.asIdeal.ramificationIdx' 𝔓.asIdeal = 1 := by
    by_contra hne
    exact hv ⟨𝔓, h𝔓, hne⟩
  rw [he, one_mul]

end S_LanglandsTunnell_CubicInduction_finsum_primeFibre_inertiaDeg_eq_three_of_not_isRamifiedIn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_finsum_primeFibre_inertiaDeg_eq_three_of_not_isRamifiedIn (solution)
