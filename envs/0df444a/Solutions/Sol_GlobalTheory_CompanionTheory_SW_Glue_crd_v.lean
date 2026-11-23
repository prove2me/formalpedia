-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Glue.crd_v
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:43.019772+00:00
-- url     : https://prove2.me/submissions/10b2f5d9-4e6a-4b3d-bedd-cb6cb32db6f6

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (X : Fin n → Fin M → AF F ⊗[F] E)
    (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin X) a i) k =
      pV v ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k) := by
  have h1 := repr_map (evalV F v) b (projFin X a i) k
  have h2 := repr_map (sndA F) b (X a i) k
  refine h1.trans ?_
  exact congrArg (evalV F v) h2
end GlobalTheory.CompanionTheory.SW.Glue
