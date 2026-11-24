-- Prove2me | solution 1 for GlobalTheory.ContinuousValuationExtension.exists_continuous_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:20:52.240598+00:00
-- url     : https://prove2.me/submissions/d47647e5-0f9d-4914-9621-7ca98b04908b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsContinuousExtension
import Theorems.Thm_GlobalTheory_ContinuousValuationExtension_continuous_of_valuation_eq
import Theorems.Thm_GlobalTheory_ContinuousValuationExtension_valuation_eq_of_denseRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open GlobalTheory GlobalTheory.ContinuousValuationExtension
namespace GlobalTheory.ContinuousValuationExtension
theorem _root_.solution {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] (w : HeightOneSpectrum (RingOfIntegers K))
    (u : HeightOneSpectrum (RingOfIntegers L)) (f : K →+* adicCompletion L u)
    (hf : ∀ x : K, (Valued.v (f x) : WithZero (Multiplicative ℤ)) = valuation K w x) :
    ∃ φ : adicCompletion K w →+* adicCompletion L u, Continuous φ ∧
      (∀ x : K, φ (algebraMap K (adicCompletion K w) x) = f x) ∧
      ∀ y : adicCompletion K w,
        (Valued.v (φ y) : WithZero (Multiplicative ℤ)) = Valued.v y := by
  let g : WithVal (w.valuation K) →+* adicCompletion L u :=
    f.comp (WithVal.equiv (w.valuation K)).toRingHom
  have hgv : ∀ x : WithVal (w.valuation K),
      (Valued.v (g x) : WithZero (Multiplicative ℤ)) = Valued.v x := fun x => hf x.ofVal
  have hsurj : Function.Surjective
      (Valued.v : WithVal (w.valuation K) → WithZero (Multiplicative ℤ)) := fun γ => by
    obtain ⟨a, ha⟩ := w.valuation_surjective K γ
    exact ⟨WithVal.toVal _ a, ha⟩
  have hgc : Continuous g := continuous_of_valuation_eq g hsurj hgv

  let φ : adicCompletion K w →+* adicCompletion L u :=
    (UniformSpace.Completion.extensionHom g hgc).comp (adicCompletion.equiv K w).toRingHom
  have hφc : Continuous φ :=
    UniformSpace.Completion.continuous_extension.comp (adicCompletion.continuous_toCompletion K w)
  have hφf : ∀ x : K, φ (algebraMap K (adicCompletion K w) x) = f x := fun x =>
    UniformSpace.Completion.extensionHom_coe g hgc (WithVal.toVal _ x)
  refine ⟨φ, hφc, hφf, fun y => ?_⟩
  refine valuation_eq_of_denseRange φ hφc (algebraMap K (adicCompletion K w))
    (denseRange_algebraMap (K := K) (v := w)) (fun x => ?_) y
  rw [hφf x, hf x]
  exact (adicCompletion.valued_coe K w x).symm
end GlobalTheory.ContinuousValuationExtension
