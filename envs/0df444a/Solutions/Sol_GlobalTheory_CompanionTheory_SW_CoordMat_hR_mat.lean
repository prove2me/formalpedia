-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CoordMat.hR_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:30:45.226384+00:00
-- url     : https://prove2.me/submissions/d2c1bb31-b6af-492a-8d6b-5a8109bb7a29

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TraceGramDetNeZero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CoordMat_hform_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CoordMat
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.CoordMat
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) (x y : Fin M → R ⊗[F] E) :
    hR R σ J ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x)
      ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ y) = hR R σ J x y := by
  have hm : cT (sigR R σ) (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
      (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J := (show HR R σ J from h).2
  rw [hR, hform_mulVec, hm, hR]
end GlobalTheory.CompanionTheory.SW.CoordMat
