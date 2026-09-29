-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.prod_sq_mul_finprod_localChar_neg_one_mul_neg_one_pow_eq_one_of_finprod_sq_mul_lamSqArch_eq_one_of_not_isBadPlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/0857abf7-d767-5d40-b1ee-8b6a0df7419f

import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_NumberField_TateGlobal_finprod_mem_primeFibre_localChar_comp_idelicNorm_apply_neg_one
import Theorems.Thm_NumberField_TateGlobal_prod_localChar_apply_neg_one_eq_neg_one_zpow_of_isArchCompAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_lamSqArch_eq_neg_one_pow_nrComplexPlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_prod_sq_mul_finprod_localChar_neg_one_mul_neg_one_pow_eq_one_of_finprod_sq_mul_lamSqArch_eq_one_of_not_isBadPlace

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

p2m_open "LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_prod_sq_mul_finprod_localChar_neg_one_mul_neg_one_pow_eq_one_of_finprod_sq_mul_lamSqArch_eq_one_of_not_isBadPlace.LanglandsTunnell.RankinSelberg"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist Converse.IsArchCompAt RankinSelberg.mem_primeFibre CubicInduction.lamSqArch_eq_neg_one_pow_nrComplexPlaces"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "primeFibre mem_primeFibre"
namespace RootSigns
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

theorem ringHom_ringOfIntegers_rat_ext {R : Type*} [NonAssocSemiring R] (f g : 𝓞 ℚ →+* R) : f = g := by
  have h : f.comp Rat.ringOfIntegersEquiv.symm.toRingHom = g.comp Rat.ringOfIntegersEquiv.symm.toRingHom :=
    RingHom.ext_int _ _
  refine RingHom.ext fun x => ?_
  obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
  exact RingHom.congr_fun h n

scoped instance subsingleton_algebra_ringOfIntegers_rat (R : Type*) [Semiring R] : Subsingleton (Algebra (𝓞 ℚ) R) :=
  ⟨fun P Q => Algebra.algebra_ext P Q fun r => RingHom.congr_fun (ringHom_ringOfIntegers_rat_ext _ _) r⟩

end LanglandsTunnell.RankinSelberg.RootSigns
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_prod_sq_mul_finprod_localChar_neg_one_mul_neg_one_pow_eq_one_of_finprod_sq_mul_lamSqArch_eq_one_of_not_isBadPlace.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_prod_sq_mul_finprod_localChar_neg_one_mul_neg_one_pow_eq_one_of_finprod_sq_mul_lamSqArch_eq_one_of_not_isBadPlace.LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_prod_sq_mul_finprod_localChar_neg_one_mul_neg_one_pow_eq_one_of_finprod_sq_mul_lamSqArch_eq_one_of_not_isBadPlace.LanglandsTunnell.RankinSelberg.RootSigns"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_prod_sq_mul_finprod_localChar_neg_one_mul_neg_one_pow_eq_one_of_finprod_sq_mul_lamSqArch_eq_one_of_not_isBadPlace.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_prod_sq_mul_finprod_localChar_neg_one_mul_neg_one_pow_eq_one_of_finprod_sq_mul_lamSqArch_eq_one_of_not_isBadPlace.LanglandsTunnell.RankinSelberg"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_prod_sq_mul_finprod_localChar_neg_one_mul_neg_one_pow_eq_one_of_finprod_sq_mul_lamSqArch_eq_one_of_not_isBadPlace.LanglandsTunnell"

open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)

    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSS' : SQ ⊆ S')
    (hgood : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → ¬ IsBadPlace K μ p)

    (ηA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hηA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ ηA)
    (hηoff : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → NumberField.TateGlobal.IsUnramifiedCharAt ηA p)
    (t : ℂ) (a : ZMod 2)
    (hηarch : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), LanglandsTunnell.Converse.IsArchCompAt ℚ ηA w t (a.val : ℤ))

    (lam : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (hlam1 : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v → lam v = 1)
    (hlam : (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), lam v ^ 2) * lamSqArch K = 1) :
    (∏ p ∈ SQ,
        (lam p ^ 2 *
          ((∏ᶠ w ∈ primeFibre ℚ K p,
              ((NumberField.TateGlobal.localChar
                (ηA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm * μ) w (-1) : ℂˣ) : ℂ)) *
            ∏ᶠ w ∈ primeFibre ℚ K p, ((NumberField.TateGlobal.localChar μ w (-1) : ℂˣ) : ℂ)))) *
        (∏ p ∈ S' \ SQ, lam p ^ 2) *
      ((-1 : ℂ) ^ a.val * (-1 : ℂ) ^ (Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).card) = 1 := by
  classical

  obtain rfl : ‹Algebra (𝓞 ℚ) (𝓞 K)› = NumberField.inst_ringOfIntegersAlgebra ℚ K := Subsingleton.elim _ _
  set N := (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm with hN
  have hfin : ∀ p : HeightOneSpectrum (𝓞 ℚ), (primeFibre ℚ K p).Finite := fun p => by
    have h := HeightOneSpectrum.preimage_comap_finite (𝓞 ℚ) ℚ K (𝓞 K) {p} (Set.finite_singleton p)
    refine h.subset fun 𝔓 h𝔓 => ?_
    rw [LanglandsTunnell.RankinSelberg.mem_primeFibre] at h𝔓
    exact h𝔓

  have hloc : ∀ w : HeightOneSpectrum (𝓞 K),
      NumberField.TateGlobal.localChar (ηA.comp N * μ) w (-1) * NumberField.TateGlobal.localChar μ w (-1) =
        NumberField.TateGlobal.localChar (ηA.comp N) w (-1) := fun w => by
    show NumberField.TateGlobal.localChar (ηA.comp N) w (-1) * NumberField.TateGlobal.localChar μ w (-1) *
        NumberField.TateGlobal.localChar μ w (-1) = _
    rw [mul_assoc, ← map_mul, neg_one_mul, neg_neg, map_one, mul_one]

  have hA : ∀ p : HeightOneSpectrum (𝓞 ℚ),
      (∏ᶠ w ∈ primeFibre ℚ K p, ((NumberField.TateGlobal.localChar (ηA.comp N * μ) w (-1) : ℂˣ) : ℂ)) *
          ∏ᶠ w ∈ primeFibre ℚ K p, ((NumberField.TateGlobal.localChar μ w (-1) : ℂˣ) : ℂ) =
        ((NumberField.TateGlobal.localChar ηA p (-1) : ℂˣ) : ℂ) := fun p => by
    rw [← finprod_mem_mul_distrib (hfin p)]
    have h := congrArg (Units.coeHom ℂ)
      (NumberField.TateGlobal.finprod_mem_primeFibre_localChar_comp_idelicNorm_apply_neg_one ℚ K ηA p)
    rw [MonoidHom.map_finprod_mem _ _ (hfin p), hdeg, Odd.neg_one_pow (by decide : Odd 3)] at h
    simp only [Units.coeHom_apply] at h
    rw [← h]
    refine finprod_mem_congr rfl fun w _ => ?_
    rw [← Units.val_mul, hloc w]

  have hB : ∏ p ∈ SQ, ((NumberField.TateGlobal.localChar ηA p (-1) : ℂˣ) : ℂ) = (-1 : ℂ) ^ a.val := by
    rw [← zpow_natCast]
    exact NumberField.TateGlobal.prod_localChar_apply_neg_one_eq_neg_one_zpow_of_isArchCompAt ηA hηA.1 hηA.2.1 SQ
      hηoff t (a.val : ℤ) hηarch

  have hlamS : (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), lam v ^ 2) =
      (∏ v ∈ S' \ SQ, lam v ^ 2) * ∏ v ∈ SQ, lam v ^ 2 := by
    rw [Finset.prod_sdiff hSS']
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    rw [Finset.mem_coe]
    by_contra hvS
    refine hv ?_
    show lam v ^ 2 = 1
    rw [hlam1 v (hgood v hvS), one_pow]
  have hC : lamSqArch K = (-1 : ℂ) ^ (Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).card := by
    rw [LanglandsTunnell.CubicInduction.lamSqArch_eq_neg_one_pow_nrComplexPlaces, Finset.card_univ]
  rw [hlamS, hC] at hlam

  rw [Finset.prod_mul_distrib, Finset.prod_congr rfl fun p _ => hA p, hB]
  have hsq : ((-1 : ℂ) ^ a.val) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  linear_combination ((-1 : ℂ) ^ a.val) ^ 2 * hlam + hsq

end S_LanglandsTunnell_RankinSelberg_prod_sq_mul_finprod_localChar_neg_one_mul_neg_one_pow_eq_one_of_finprod_sq_mul_lamSqArch_eq_one_of_not_isBadPlace
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_prod_sq_mul_finprod_localChar_neg_one_mul_neg_one_pow_eq_one_of_finprod_sq_mul_lamSqArch_eq_one_of_not_isBadPlace (solution)
