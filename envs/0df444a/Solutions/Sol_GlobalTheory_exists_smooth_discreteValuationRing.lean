-- Prove2me | solution 1 for GlobalTheory.exists_smooth_discreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:38:33.336641+00:00
-- url     : https://prove2.me/submissions/09cf5986-30b9-4a80-9a78-882241aad742

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_P2M_GlobalTheory_formMap__Multi_014b852379ac
import Theorems.Thm_GlobalTheory_dlogWedge_empty
import Theorems.Thm_GlobalTheory_ordTop_vw_zero
import Theorems.Thm_GlobalTheory_fracKaehlerBasis_apply
import Theorems.Thm_GlobalTheory_topFormCoeff_topFormGen
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15


attribute [local simp] GlobalTheory.formMap_ιMulti
attribute [local simp] GlobalTheory.dlogWedge_empty
attribute [local simp] GlobalTheory.ordTop_vw_zero
attribute [local simp] GlobalTheory.fracKaehlerBasis_apply
attribute [local simp] GlobalTheory.topFormCoeff_topFormGen

set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
open Polynomial
variable (K : Type*) [Field K]
namespace GlobalTheory
theorem _root_.solution :
    ∃ (V : Subalgebra K (RatFunc K)) (_ : IsDiscreteValuationRing V),
      Algebra.EssFiniteType K V ∧ Algebra.FormallySmooth K V ∧ IsFractionRing V (RatFunc K) ∧
        Algebra.trdeg K (RatFunc K) = (1 : ℕ) := by
  let 𝔭 : Ideal K[X] := Ideal.span {X}
  haveI : 𝔭.IsPrime := (Ideal.span_singleton_prime X_ne_zero).mpr prime_X
  have h𝔭 : 𝔭 ≠ ⊥ := by simp [𝔭]
  let W : Subalgebra K[X] (RatFunc K) :=
    Localization.subalgebra.ofField (RatFunc K) 𝔭.primeCompl 𝔭.primeCompl_le_nonZeroDivisors
  haveI : IsLocalization.AtPrime W 𝔭 := Localization.subalgebra.isLocalization_ofField ..
  haveI h₁ : IsDiscreteValuationRing W :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain K[X] h𝔭 W
  haveI : Algebra.EssFiniteType K[X] W := .of_isLocalization W 𝔭.primeCompl
  haveI : Algebra.FormallySmooth K[X] W := .of_isLocalization 𝔭.primeCompl
  have h₂ : Algebra.EssFiniteType K W := .comp K K[X] W
  have h₃ : Algebra.FormallySmooth K W := .comp K K[X] W
  have h₄ : IsFractionRing W (RatFunc K) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.primeCompl W (RatFunc K)
  refine ⟨W.restrictScalars K, h₁, h₂, h₃, h₄, ?_⟩
  haveI : Algebra.IsAlgebraic K[X] (RatFunc K) :=
    IsLocalization.isAlgebraic (RatFunc K) (nonZeroDivisors K[X])
  rw [← trdeg_add_eq K K[X], trdeg_eq_zero (R := K[X]) (A := RatFunc K)]
  simp
end GlobalTheory
