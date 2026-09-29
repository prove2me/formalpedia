-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.inducedE3_eq_zero_of_isRamifiedIn_of_finrank_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/1625b6da-e05a-5df1-8917-a1a5a0971415

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalWhittakerDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_inducedE3_eq_zero_of_isRamifiedIn_of_finrank_eq_three

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker

open Polynomial

theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (c : HeightOneSpectrum (𝓞 K) → ℂ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hram : IsRamifiedIn K v) :
    LanglandsTunnell.RankinSelberg.inducedE3 ℚ c v = 0 := by
  classical

  have huniq : ∀ f g : 𝓞 ℚ →+* 𝓞 K, f = g := fun f g => by
    have h := RingHom.ext_int (f.comp Rat.ringOfIntegersEquiv.symm.toRingHom) (g.comp Rat.ringOfIntegersEquiv.symm.toRingHom)
    refine RingHom.ext fun x => ?_
    obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
    exact DFunLike.congr_fun h n
  have hinst : ‹Algebra (𝓞 ℚ) (𝓞 K)› = inst_ringOfIntegersAlgebra ℚ K :=
    Algebra.algebra_ext _ _ fun r => DFunLike.congr_fun (huniq _ _) r
  subst hinst

  obtain ⟨𝔓₀, h𝔓₀, he1⟩ := hram

  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have hsub : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ primeFibre ℚ K v →
      𝔓.asIdeal ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K) := by
    intro 𝔓 h𝔓
    rw [mem_primeFibre] at h𝔓
    rw [IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot]
    refine ⟨𝔓.isPrime, (Ideal.liesOver_iff _ _).mpr ?_⟩
    rw [← h𝔓]
    rfl
  have hfin : (primeFibre ℚ K v).Finite :=
    ((IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K)).finite_toSet.preimage
      (f := fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h)).subset
      (fun 𝔓 h𝔓 => hsub 𝔓 h𝔓)

  have hf : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ primeFibre ℚ K v →
      (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal = v.asIdeal.inertiaDeg' 𝔓.asIdeal := by
    intro 𝔓 h𝔓; rw [mem_primeFibre] at h𝔓; rw [h𝔓]

  have hfac : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), (inducedFactor ℚ c 𝔓).natDegree ≤
      (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal := by
    intro 𝔓
    unfold inducedFactor
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · rw [Polynomial.natDegree_C]; exact Nat.zero_le _
    · exact Polynomial.natDegree_C_mul_X_pow_le _ _

  have he : ∀ P ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K), v.asIdeal.ramificationIdx' P ≠ 0 := by
    intro P hP
    have hP' := (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot (𝓞 K)).mp hP
    exact Ideal.IsDedekindDomain.ramificationIdx_ne_zero
      ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 ℚ) (𝓞 K))).not.mpr v.ne_bot) hP'.1
      (Ideal.map_le_iff_le_comap.mpr (le_of_eq ((Ideal.liesOver_iff _ _).mp hP'.2)))
  have hP0 : 𝔓₀.asIdeal ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K) := hsub 𝔓₀ h𝔓₀
  have he2 : 2 ≤ v.asIdeal.ramificationIdx' 𝔓₀.asIdeal := by
    have h0 := he _ hP0
    omega
  have hf0 : 1 ≤ v.asIdeal.inertiaDeg' 𝔓₀.asIdeal := by
    haveI : 𝔓₀.asIdeal.LiesOver v.asIdeal := (Ideal.liesOver_iff _ _).mpr (by rw [mem_primeFibre] at h𝔓₀; rw [← h𝔓₀]; rfl)
    exact Ideal.inertiaDeg'_pos v.asIdeal 𝔓₀.asIdeal

  have hsumPO : ∑ P ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K), v.asIdeal.inertiaDeg' P ≤ 2 := by
    have htot : ∑ P ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K),
        v.asIdeal.ramificationIdx' P * v.asIdeal.inertiaDeg' P = 3 :=
      (Ideal.sum_ramification_inertia (𝓞 K) ℚ K v.ne_bot).trans hdeg
    have h1 : ∑ P ∈ (IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K)).erase 𝔓₀.asIdeal, v.asIdeal.inertiaDeg' P ≤
        ∑ P ∈ (IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K)).erase 𝔓₀.asIdeal,
          v.asIdeal.ramificationIdx' P * v.asIdeal.inertiaDeg' P :=
      Finset.sum_le_sum fun P hP =>
        Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (he P (Finset.mem_of_mem_erase hP)))
    have h2 : v.asIdeal.inertiaDeg' 𝔓₀.asIdeal + 1 ≤
        v.asIdeal.ramificationIdx' 𝔓₀.asIdeal * v.asIdeal.inertiaDeg' 𝔓₀.asIdeal := by nlinarith
    rw [← Finset.sum_erase_add _ _ hP0] at htot ⊢
    omega

  have hsumf : ∑ 𝔓 ∈ hfin.toFinset, v.asIdeal.inertiaDeg' 𝔓.asIdeal ≤ 2 := by
    have hinj : Set.InjOn (fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.asIdeal) ↑hfin.toFinset :=
      fun a _ b _ h => HeightOneSpectrum.ext h
    calc ∑ 𝔓 ∈ hfin.toFinset, v.asIdeal.inertiaDeg' 𝔓.asIdeal
        = ∑ P ∈ hfin.toFinset.image (fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.asIdeal), v.asIdeal.inertiaDeg' P := by
          rw [Finset.sum_image hinj]
      _ ≤ ∑ P ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K), v.asIdeal.inertiaDeg' P := by
          apply Finset.sum_le_sum_of_subset
          intro P hP
          rw [Finset.mem_image] at hP
          obtain ⟨𝔓, h𝔓, rfl⟩ := hP
          exact hsub 𝔓 (hfin.mem_toFinset.mp h𝔓)
      _ ≤ 2 := hsumPO

  have hdegle : (inducedEulerPoly ℚ c v).natDegree ≤ 2 := by
    unfold inducedEulerPoly
    rw [finprod_mem_eq_finite_toFinset_prod _ hfin]
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun 𝔓 h𝔓 => ?_) hsumf
    rw [← hf 𝔓 (hfin.mem_toFinset.mp h𝔓)]
    exact hfac 𝔓

  unfold LanglandsTunnell.RankinSelberg.inducedE3
  rw [neg_eq_zero]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

end S_LanglandsTunnell_CubicInduction_inducedE3_eq_zero_of_isRamifiedIn_of_finrank_eq_three
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_inducedE3_eq_zero_of_isRamifiedIn_of_finrank_eq_three (solution)
