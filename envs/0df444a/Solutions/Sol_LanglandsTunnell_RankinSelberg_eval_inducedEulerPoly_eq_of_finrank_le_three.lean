-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.eval_inducedEulerPoly_eq_of_finrank_le_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/e11b1141-ba1c-55b5-b327-b361f33adf60

import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib.NumberTheory.RamificationInertia.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_eval_inducedEulerPoly_eq_of_finrank_le_three

set_option autoImplicit false

open IsDedekindDomain NumberField

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

section

open LanglandsTunnell.RankinSelberg

variable (F : Type) [Field F] [NumberField F]

private theorem inertiaDeg_pos_of_mem_primeFibre (p : HeightOneSpectrum (𝓞 ℚ)) (𝔓 : HeightOneSpectrum (𝓞 F))
    (h : 𝔓 ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ F p) : 0 < p.asIdeal.inertiaDeg' 𝔓.asIdeal := by
  have hu : 𝔓.under (𝓞 ℚ) = p := h
  haveI : 𝔓.asIdeal.LiesOver p.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal hu).symm⟩
  haveI : p.asIdeal.IsMaximal := p.isMaximal
  exact Ideal.inertiaDeg'_pos p.asIdeal 𝔓.asIdeal

private theorem ramificationIdx_pos_of_mem_primeFibre (p : HeightOneSpectrum (𝓞 ℚ)) (𝔓 : HeightOneSpectrum (𝓞 F))
    (h : 𝔓 ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ F p) : 0 < p.asIdeal.ramificationIdx' 𝔓.asIdeal := by
  haveI : 𝔓.asIdeal.LiesOver p.asIdeal := (asIdeal_mem_primesOver_of_mem_primeFibre F p h).2
  exact Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver 𝔓.asIdeal p.ne_bot)

private theorem sum_toFinset_ramificationIdx_mul_inertiaDeg (p : HeightOneSpectrum (𝓞 ℚ)) :
    ∑ 𝔓 ∈ (primeFibre_finite F p).toFinset, p.asIdeal.ramificationIdx' 𝔓.asIdeal * p.asIdeal.inertiaDeg' 𝔓.asIdeal =
      Module.finrank ℚ F := by
  rw [← finsum_mem_eq_finite_toFinset_sum _ (primeFibre_finite F p)]
  exact finsum_fibre_ramificationIdx_mul_inertiaDeg F p

private theorem natDegree_inducedFactor_le {R : Type*} [CommRing R] (c : HeightOneSpectrum (𝓞 F) → R)
    (𝔓 : HeightOneSpectrum (𝓞 F)) :
    (LanglandsTunnell.RankinSelberg.inducedFactor ℚ c 𝔓).natDegree ≤
      (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal := by
  rw [LanglandsTunnell.RankinSelberg.inducedFactor]
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le ((Polynomial.natDegree_C _).le.trans (Nat.zero_le _)) (Polynomial.natDegree_C_mul_X_pow_le _ _))

private theorem natDegree_inducedEulerPoly_le {R : Type*} [CommRing R] (c : HeightOneSpectrum (𝓞 F) → R)
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    (LanglandsTunnell.RankinSelberg.inducedEulerPoly ℚ c p).natDegree ≤ Module.finrank ℚ F := by
  rw [LanglandsTunnell.RankinSelberg.inducedEulerPoly, finprod_mem_eq_finite_toFinset_prod _ (primeFibre_finite F p),
    ← sum_toFinset_ramificationIdx_mul_inertiaDeg F p]
  refine (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum fun 𝔓 h𝔓 => ?_)
  have hmem : 𝔓 ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ F p := (Set.Finite.mem_toFinset _).1 h𝔓
  have hu : 𝔓.under (𝓞 ℚ) = p := hmem
  refine (natDegree_inducedFactor_le F c 𝔓).trans ?_
  rw [hu]
  exact Nat.le_mul_of_pos_left _ (ramificationIdx_pos_of_mem_primeFibre F p 𝔓 hmem)

private theorem coeff_zero_inducedEulerPoly {R : Type*} [CommRing R] (c : HeightOneSpectrum (𝓞 F) → R)
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    (LanglandsTunnell.RankinSelberg.inducedEulerPoly ℚ c p).coeff 0 = 1 := by
  rw [LanglandsTunnell.RankinSelberg.inducedEulerPoly, finprod_mem_eq_finite_toFinset_prod _ (primeFibre_finite F p),
    Polynomial.coeff_zero_prod]
  refine Finset.prod_eq_one fun 𝔓 h𝔓 => ?_
  have hmem : 𝔓 ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ F p := (Set.Finite.mem_toFinset _).1 h𝔓
  have hu : 𝔓.under (𝓞 ℚ) = p := hmem
  have hf := inertiaDeg_pos_of_mem_primeFibre F p 𝔓 hmem
  rw [LanglandsTunnell.RankinSelberg.inducedFactor, hu, Polynomial.coeff_sub, Polynomial.coeff_C_zero,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hf.ne, mul_zero, sub_zero]

end

open LanglandsTunnell.RankinSelberg in
theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K ≤ 3)
    {R : Type*} [CommRing R] (c : HeightOneSpectrum (𝓞 K) → R) (p : HeightOneSpectrum (𝓞 ℚ)) (z : R) :
    (inducedEulerPoly ℚ c p).eval z =
      1 - inducedE1 ℚ c p * z + inducedE2 ℚ c p * z ^ 2 - inducedE3 ℚ c p * z ^ 3 := by
  obtain rfl := algebra_ringOfIntegers_rat_eq K ‹Algebra (𝓞 ℚ) (𝓞 K)›
  have hlt : (inducedEulerPoly ℚ c p).natDegree < 4 :=
    Nat.lt_succ_of_le ((natDegree_inducedEulerPoly_le K c p).trans hdeg)
  rw [Polynomial.eval_eq_sum_range' hlt, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, coeff_zero_inducedEulerPoly K c p, inducedE1, inducedE2, inducedE3]
  ring

end S_LanglandsTunnell_RankinSelberg_eval_inducedEulerPoly_eq_of_finrank_le_three
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_eval_inducedEulerPoly_eq_of_finrank_le_three (solution)
