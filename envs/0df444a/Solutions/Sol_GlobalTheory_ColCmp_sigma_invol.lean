-- Prove2me | solution 1 for GlobalTheory.ColCmp.sigma_invol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:31:07.742486+00:00
-- url     : https://prove2.me/submissions/0f46b23d-c2f4-4b07-9086-3727ce940d45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelWeilLocal_HermitianPerpSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelWeilLocal_ColumnDimensionRational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MulVecMemHatSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped TensorProduct ENNReal Pointwise
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory GlobalTheory.ColCmp
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.ColCmp
theorem _root_.solution {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]
end GlobalTheory.ColCmp
