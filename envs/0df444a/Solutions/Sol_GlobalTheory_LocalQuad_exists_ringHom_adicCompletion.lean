-- Prove2me | solution 1 for GlobalTheory.LocalQuad.exists_ringHom_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:49:06.913489+00:00
-- url     : https://prove2.me/submissions/0ef2d042-b943-40bc-bbd6-0559ce19903c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRingHomAdicCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
namespace GlobalTheory.LocalQuad
theorem _root_.solution (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] (w : HeightOneSpectrum (𝓞 L)) :
    ∃ (v : HeightOneSpectrum (𝓞 K)) (φ : v.adicCompletion K →+* w.adicCompletion L),
      ∀ x : K, φ (algebraMap K (v.adicCompletion K) x) =
        algebraMap L (w.adicCompletion L) (algebraMap K L x) := by
  let v : HeightOneSpectrum (𝓞 K) := w.under (𝓞 K)
  have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver K L v w).continuous
  refine ⟨v, ((HeightOneSpectrum.adicCompletion.equiv L w).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv K v).toRingHom, fun x => ?_⟩
  apply HeightOneSpectrum.adicCompletion.ext
  exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)
end GlobalTheory.LocalQuad
