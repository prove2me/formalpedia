-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Glue.crd_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:05.513144+00:00
-- url     : https://prove2.me/submissions/d451a1f7-dc68-497c-be76-9942eec903cf

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleLocalGlobalProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Glue_repr_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix RestrictedProduct
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Glue
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
variable {d M n : ℕ} (b : Module.Basis (Fin d) F E)
namespace GlobalTheory.CompanionTheory.SW.Glue
theorem _root_.solution (X : Fin n → Fin M → AF F ⊗[F] E) (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Ainf F) b).repr (projInf X a i) k =
      fstA F ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k) :=
  repr_map (fstA F) b (X a i) k
end GlobalTheory.CompanionTheory.SW.Glue
