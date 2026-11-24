-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BB.coordK_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:10:49.897946+00:00
-- url     : https://prove2.me/submissions/88826ea3-72eb-4dad-ace4-eda68283ace8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHomeomorphRankOneTuples

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.BB
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R]
    [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (e : R ⊗[F] E ≃ᵐ (Fin d → R))
    (he : ∀ y k, e y k = (Algebra.TensorProduct.basis R b).repr y k) :
    coordK R b lam = (Measure.pi fun _ => lam).map e.symm := by
  rw [MeasurableEquiv.map_symm]
  have : (e : R ⊗[F] E → Fin d → R) =
      fun (y : R ⊗[F] E) (k : Fin d) => (Algebra.TensorProduct.basis R b).repr y k := by
    funext y k; exact he y k
  rw [coordK, this]
end GlobalTheory.CompanionTheory.SW.BB
