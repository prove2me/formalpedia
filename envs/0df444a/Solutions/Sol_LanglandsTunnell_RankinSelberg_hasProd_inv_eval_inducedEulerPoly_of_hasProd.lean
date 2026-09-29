-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.hasProd_inv_eval_inducedEulerPoly_of_hasProd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/1cce9043-35b1-547f-a8ef-7dd6ee105007

import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_hasProd_inv_eval_inducedEulerPoly_of_hasProd

set_option autoImplicit false

open IsDedekindDomain NumberField Polynomial
open LanglandsTunnell.RankinSelberg

section rsRegroupHelpers

variable (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra (𝓞 F) (𝓞 K)]

private theorem rsRegroup_algebraMap_injective : Function.Injective (algebraMap (𝓞 F) (𝓞 K)) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  have hmem := Ideal.absNorm_mem (RingHom.ker (algebraMap (𝓞 F) (𝓞 K)))
  have hnz : Ideal.absNorm (RingHom.ker (algebraMap (𝓞 F) (𝓞 K))) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hne
  rw [RingHom.mem_ker, map_natCast] at hmem
  exact hnz (Nat.cast_eq_zero.mp hmem)

private theorem rsRegroup_isTorsionFree : Module.IsTorsionFree (𝓞 F) (𝓞 K) :=
  (Module.isTorsionFree_iff_algebraMap_injective ..).mpr (rsRegroup_algebraMap_injective F K)

variable [Algebra.IsIntegral (𝓞 F) (𝓞 K)]

private theorem rsRegroup_primeFibre_finite (p : HeightOneSpectrum (𝓞 F)) : (primeFibre F K p).Finite := by
  haveI := rsRegroup_isTorsionFree F K
  haveI : p.asIdeal.IsMaximal := p.isPrime.isMaximal p.ne_bot
  have hfin : (Ideal.primesOver p.asIdeal (𝓞 K)).Finite := IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 K)
  refine (hfin.preimage (f := fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.asIdeal) ?_).subset ?_
  · intro a _ b _ hab
    exact HeightOneSpectrum.ext hab
  · intro 𝔓 h𝔓
    rw [mem_primeFibre] at h𝔓
    show 𝔓.asIdeal ∈ Ideal.primesOver p.asIdeal (𝓞 K)
    refine ⟨𝔓.isPrime, ⟨?_⟩⟩
    rw [← h𝔓]
    rfl

private theorem rsRegroup_absNorm_eq (𝔓 : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm 𝔓.asIdeal =
      Ideal.absNorm (𝔓.under (𝓞 F)).asIdeal ^ ((𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal) := by
  haveI : Module.Finite (𝓞 F) (𝓞 K) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 F) (𝓞 K)
  haveI : 𝔓.asIdeal.LiesOver (𝔓.under (𝓞 F)).asIdeal := ⟨rfl⟩
  exact Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver 𝔓.asIdeal (𝔓.under (𝓞 F)).asIdeal
    (𝔓.under (𝓞 F)).isPrime (𝔓.under (𝓞 F)).ne_bot

private theorem rsRegroup_eval_inducedFactor (c : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) (𝔓 : HeightOneSpectrum (𝓞 K)) :
    (inducedFactor F c 𝔓).eval (((Ideal.absNorm (𝔓.under (𝓞 F)).asIdeal : ℕ) : ℂ) ^ (-s)) =
      1 - c 𝔓 * ((Ideal.absNorm 𝔓.asIdeal : ℕ) : ℂ) ^ (-s) := by
  simp only [inducedFactor, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  congr 2
  rw [rsRegroup_absNorm_eq F K 𝔓, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, ← Complex.cpow_nat_mul]

private theorem rsRegroup_factor_eq (c : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) (p : HeightOneSpectrum (𝓞 F)) :
    ((inducedEulerPoly F c p).eval (((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ =
      ∏ 𝔓 ∈ (rsRegroup_primeFibre_finite F K p).toFinset,
        (1 - c 𝔓 * ((Ideal.absNorm 𝔓.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by
  unfold inducedEulerPoly
  rw [finprod_mem_eq_finite_toFinset_prod _ (rsRegroup_primeFibre_finite F K p), eval_prod,
    ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun 𝔓 h𝔓 => ?_
  rw [Set.Finite.mem_toFinset, mem_primeFibre] at h𝔓
  rw [← h𝔓, rsRegroup_eval_inducedFactor F K c s 𝔓]

end rsRegroupHelpers

theorem solution
    (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra (𝓞 F) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 F) (𝓞 K)] (c : HeightOneSpectrum (𝓞 K) → ℂ) (s Z : ℂ)
    (h : HasProd (fun 𝔓 : HeightOneSpectrum (𝓞 K) =>
      (1 - c 𝔓 * ((Ideal.absNorm 𝔓.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) Z) :
    HasProd (fun p : HeightOneSpectrum (𝓞 F) =>
      ((inducedEulerPoly F c p).eval (((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) Z := by
  classical
  let e := Equiv.sigmaFiberEquiv (fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 F))
  have h2 := (e.hasProd_iff).mpr h
  refine HasProd.sigma h2 fun p => ?_
  haveI : Finite {𝔓 : HeightOneSpectrum (𝓞 K) // 𝔓.under (𝓞 F) = p} := (rsRegroup_primeFibre_finite F K p).to_subtype
  haveI := Fintype.ofFinite {𝔓 : HeightOneSpectrum (𝓞 K) // 𝔓.under (𝓞 F) = p}
  rw [rsRegroup_factor_eq F K c s p,
    Finset.prod_subtype (rsRegroup_primeFibre_finite F K p).toFinset (p := fun 𝔓 => 𝔓.under (𝓞 F) = p)
      (fun 𝔓 => by rw [Set.Finite.mem_toFinset, mem_primeFibre])]
  exact hasProd_fintype _

end S_LanglandsTunnell_RankinSelberg_hasProd_inv_eval_inducedEulerPoly_of_hasProd
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_hasProd_inv_eval_inducedEulerPoly_of_hasProd (solution)
