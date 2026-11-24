-- Prove2me | solution 1 for GlobalTheory.CNorm.isIntegral_iff_valued_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:21:37.308527+00:00
-- url     : https://prove2.me/submissions/ece7618e-32df-46ca-a694-44e7371ce23f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormCoeffMinpolyLeOneOfNormLeOne
import Theorems.Thm_GlobalTheory_CNorm_norm_coeff_minpoly_le_one_of_norm_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
namespace GlobalTheory.CNorm
theorem _root_.solution (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (L : Type) [Field L] [Algebra (v.adicCompletion F) L]
    [FiniteDimensional (v.adicCompletion F) L] [Algebra (v.adicCompletionIntegers F) L]
    [IsScalarTower (v.adicCompletionIntegers F) (v.adicCompletion F) L] (x : L) :
    IsIntegral (v.adicCompletionIntegers F) x ↔
      Valued.v (Algebra.norm (v.adicCompletion F) x) ≤ 1 := by
  constructor
  · intro h
    have h1 : IsIntegral (v.adicCompletionIntegers F) (Algebra.norm (v.adicCompletion F) x) :=
      Algebra.isIntegral_norm (v.adicCompletion F) h
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (K := v.adicCompletion F)).1 h1
    rw [← hy]
    exact y.2
  · intro h
    letI : NontriviallyNormedField (v.adicCompletion F) :=
      Valued.toNontriviallyNormedField (v.adicCompletion F) ℤᵐ⁰
    haveI : IsUltrametricDist (v.adicCompletion F) :=
      inferInstanceAs (@IsUltrametricDist (v.adicCompletion F)
        (Valued.toNormedField (v.adicCompletion F) ℤᵐ⁰).toDist)
    have hc : ∀ n, Valued.v ((minpoly (v.adicCompletion F) x).coeff n) ≤ 1 := fun n =>
      Valued.toNormedField.norm_le_one_iff.1
        (norm_coeff_minpoly_le_one_of_norm_le_one (v.adicCompletion F) L x
          (Valued.toNormedField.norm_le_one_iff.2 h) n)
    have hx : IsIntegral (v.adicCompletion F) x := Algebra.IsIntegral.isIntegral x
    have hl : minpoly (v.adicCompletion F) x ∈
        Polynomial.lifts (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, hc n⟩, rfl⟩
    obtain ⟨q, hq, -, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (minpoly.monic hx)
    refine ⟨q, hm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap (v.adicCompletion F), hq,
      minpoly.aeval]
end GlobalTheory.CNorm
