-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.MeasProj.coord_projV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:41.570897+00:00
-- url     : https://prove2.me/submissions/89ad0103-89f0-4550-9bce-aefd8317d772

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjections
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_MeasProj_repr_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.MeasProj
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.MeasProj
theorem _root_.solution {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (X : Fin n → Fin M → Af F ⊗[F] E) (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v X a i) k =
      ((Algebra.TensorProduct.basis (Af F) b).repr (X a i) k) v :=
  repr_map b (evalV F v) _ k
end GlobalTheory.CompanionTheory.SW.MeasProj
