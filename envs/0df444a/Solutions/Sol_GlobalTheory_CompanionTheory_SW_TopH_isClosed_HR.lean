-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.TopH.isClosed_HR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:35:07.763741+00:00
-- url     : https://prove2.me/submissions/2083d4fc-d8fc-4f1e-b901-cbe06e1ed8d4

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TopH
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
namespace GlobalTheory.CompanionTheory.SW.TopH
theorem _root_.solution [IsTopologicalRing (R ⊗[F] E)] [T2Space (R ⊗[F] E)] (σ : E →ₐ[F] E) (hs : Continuous (sigR R σ)) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) :
    IsClosed (HR R σ J : Set (GL (Fin M) (R ⊗[F] E))) := by
  have hv : Continuous fun g : GL (Fin M) (R ⊗[F] E) => (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    Units.continuous_val
  have hc : Continuous fun g : GL (Fin M) (R ⊗[F] E) =>
      cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) _) := by
    refine ((Continuous.matrix_transpose (Continuous.matrix_map hv hs)).matrix_mul continuous_const).matrix_mul hv
  exact isClosed_eq hc continuous_const
end GlobalTheory.CompanionTheory.SW.TopH
