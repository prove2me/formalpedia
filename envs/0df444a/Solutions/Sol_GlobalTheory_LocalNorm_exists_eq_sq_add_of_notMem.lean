-- Prove2me | solution 1 for GlobalTheory.LocalNorm.exists_eq_sq_add_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:27:15.231833+00:00
-- url     : https://prove2.me/submissions/f382213c-5de1-48f6-b79e-5a741e50b8f4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsBinaryEqAdicCompletion
import Theorems.Thm_GlobalTheory_LocalNorm_exists_binary_eq_adicCompletion
import Theorems.Thm_GlobalTheory_LocalNorm_exists_sub_notMem
import Theorems.Thm_GlobalTheory_LocalNorm_complexConj_rt
import Theorems.Thm_GlobalTheory_LocalNorm_exists_coords

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LocalNorm
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.LocalNorm
theorem _root_.solution (H : Host E)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    {u : 𝓞 (maximalRealSubfield E)} (hu : u ∉ v.asIdeal) :
    ∃ a b : v.adicCompletion (maximalRealSubfield E),
      algebraMap (maximalRealSubfield E) _ (u : maximalRealSubfield E) = a ^ 2 + H.d * b ^ 2 := by
  haveI := v.isMaximal
  haveI := H.unram
  obtain ⟨P, hP, hPv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) v.asIdeal
    (by simp [RingHom.ker_eq_bot_iff_eq_zero, (RingHom.injective_iff_ker_eq_bot _).1
      (FaithfulSMul.algebraMap_injective (𝓞 (maximalRealSubfield E)) (𝓞 E))])
  obtain ⟨w, hw⟩ := exists_sub_notMem
    (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →ₐ[𝓞 (maximalRealSubfield E)] 𝓞 E)
    ⟨H.rt, fun h => by
      have h1 : IsCMField.complexConj E (H.rt : E) = (H.rt : E) := congrArg (algebraMap (𝓞 E) E) h
      rw [complexConj_rt, neg_eq_self] at h1
      have h2 : H.rt = 0 := by exact_mod_cast h1
      have h3 := H.rt_sq
      rw [h2, zero_pow two_ne_zero, eq_comm, neg_eq_zero, Nat.cast_eq_zero] at h3
      exact H.d_prime.ne_zero h3⟩ P hP.ne_top
  have hcc : ∀ y, IsCMField.ringOfIntegersComplexConj E (IsCMField.ringOfIntegersComplexConj E y)
      = y := fun y => RingOfIntegers.ext (IsCMField.complexConj_apply_apply E (y : E))
  obtain ⟨a, ha⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E
    (w + IsCMField.ringOfIntegersComplexConj E w)).1 (by rw [map_add, hcc, add_comm])
  obtain ⟨n, hn⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E
    (w * IsCMField.ringOfIntegersComplexConj E w)).1 (by rw [map_mul, hcc, mul_comm])
  have hD : a ^ 2 - 4 * n ∉ v.asIdeal := by
    rw [← hPv, Ideal.mem_comap]
    intro h
    apply hw
    apply hP.isPrime.mem_of_pow_mem 2
    convert h using 1
    simp only [map_sub, map_mul, map_pow, map_ofNat, ha, hn, AlgEquiv.coe_algHom]
    ring
  obtain ⟨r, s, hrs⟩ := exists_binary_eq_adicCompletion v hD hu
  obtain ⟨α, β, hα, hβ⟩ := exists_coords H (w : E)
  have ha' : (a : maximalRealSubfield E) = 2 * α :=
    Subtype.ext ((congrArg (algebraMap (𝓞 E) E) ha).trans hα.symm)
  have hn' : (n : maximalRealSubfield E) = α ^ 2 + H.d * β ^ 2 :=
    Subtype.ext ((congrArg (algebraMap (𝓞 E) E) hn).trans hβ.symm)
  rw [ha', hn'] at hrs
  simp only [map_add, map_mul, map_pow, map_ofNat, map_natCast] at hrs
  refine ⟨r + algebraMap (maximalRealSubfield E) _ α * s,
    algebraMap (maximalRealSubfield E) _ β * s, ?_⟩
  linear_combination -hrs
end GlobalTheory.LocalNorm
