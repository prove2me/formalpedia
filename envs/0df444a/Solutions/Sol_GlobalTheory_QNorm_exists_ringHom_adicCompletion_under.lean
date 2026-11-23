-- Prove2me | solution 1 for GlobalTheory.QNorm.exists_ringHom_adicCompletion_under
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:53.640981+00:00
-- url     : https://prove2.me/submissions/bfc79b7a-70f2-419d-bf43-7ce16b0259b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRingHomAdicCompletionUnder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
namespace GlobalTheory.QNorm
theorem _root_.solution :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (w : HeightOneSpectrum (𝓞 E)),
      ∃ φ : (w.under (𝓞 F)).adicCompletion F →+* w.adicCompletion E,
        ∀ x : F, φ (algebraMap F ((w.under (𝓞 F)).adicCompletion F) x) =
          algebraMap E (w.adicCompletion E) (algebraMap F E x) := by
  intro K L _ _ _ _ _ w
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver K L (w.under (𝓞 K))
    w).continuous
  refine ⟨((HeightOneSpectrum.adicCompletion.equiv L w).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal ((w.under (𝓞 K)).valuation K)) (WithVal (w.valuation L))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv K (w.under (𝓞 K))).toRingHom, fun x => ?_⟩
  apply HeightOneSpectrum.adicCompletion.ext
  exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)
end GlobalTheory.QNorm
