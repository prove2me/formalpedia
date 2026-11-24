-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Glue.tuple_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:19:00.120273+00:00
-- url     : https://prove2.me/submissions/4dd5f48c-6945-4b7b-a1b0-92f57ff346d1

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleLocalGlobalProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Glue_crd_inf
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Glue_crd_v

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
include b
namespace GlobalTheory.CompanionTheory.SW.Glue
theorem _root_.solution (X Y : Fin n → Fin M → AF F ⊗[F] E) (hinf : projInf X = projInf Y)
    (hv : ∀ v, projV v (projFin X) = projV v (projFin Y)) : X = Y := by
  funext a i
  refine (Algebra.TensorProduct.basis (AF F) b).ext_elem fun k => ?_
  refine Prod.ext ?_ ?_
  · have := crd_inf b X a i k
    rw [hinf, crd_inf b Y a i k] at this
    exact this.symm
  · refine Subtype.ext (funext fun v => ?_)
    have := crd_v b v X a i k
    rw [hv v, crd_v b v Y a i k] at this
    exact this.symm
end GlobalTheory.CompanionTheory.SW.Glue
