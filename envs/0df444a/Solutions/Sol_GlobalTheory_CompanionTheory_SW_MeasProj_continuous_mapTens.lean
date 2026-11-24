-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.MeasProj.continuous_mapTens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:28:00.182841+00:00
-- url     : https://prove2.me/submissions/cc2b6027-1bba-4fcc-aed1-132ab92d1a25

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjections
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_MeasProj_repr_map
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TopK_isHomeomorph_coord
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.MeasProj
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E]
  {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
variable [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace S] [IsTopologicalRing S]
namespace GlobalTheory.CompanionTheory.SW.MeasProj
theorem _root_.solution {d : ℕ} (b : Module.Basis (Fin d) F E) (f : R →ₐ[F] S) (hf : Continuous f) :
    Continuous (Algebra.TensorProduct.map f (AlgHom.id F E) : R ⊗[F] E → S ⊗[F] E) := by
  rw [(TopK.isHomeomorph_coord S b).isInducing.continuous_iff]
  refine continuous_pi fun k => ?_
  simp only [Function.comp_def, repr_map]
  exact hf.comp ((continuous_apply k).comp (TopK.isHomeomorph_coord R b).continuous)
end GlobalTheory.CompanionTheory.SW.MeasProj
