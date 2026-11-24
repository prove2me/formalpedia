-- Prove2me | solution 1 for GlobalTheory.DenseCompl.exists_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:39:01.457152+00:00
-- url     : https://prove2.me/submissions/7ae5fe99-ac38-4bef-b341-167118dfb46e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ContinuousOfValuationEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EqZeroOfForallLeExp
import Theorems.Thm_GlobalTheory_ValuationExtensionContinuous_exists_extension


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open WithZero
open GlobalTheory GlobalTheory.DenseCompl
open scoped WithZeroTopology
namespace GlobalTheory.DenseCompl
theorem _root_.solution {K : Type} [Field K] [NumberField K] {R L : Type} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (w : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum R) (f : K →+* u.adicCompletion L)
    (hf : ∀ x, Valued.v (f x) = w.valuation K x) :
    ∃ φ : w.adicCompletion K →+* u.adicCompletion L, Continuous φ ∧
      (∀ x : K, φ (algebraMap K _ x) = f x) ∧ ∀ y, Valued.v (φ y) = Valued.v y := by
  first
  | exact @_root_.GlobalTheory.ValuationExtensionContinuous.exists_extension
  | exact _root_.GlobalTheory.ValuationExtensionContinuous.exists_extension
  | (apply _root_.GlobalTheory.ValuationExtensionContinuous.exists_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.ValuationExtensionContinuous.exists_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ValuationExtensionContinuous.exists_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ValuationExtensionContinuous.exists_extension ..)
end GlobalTheory.DenseCompl
