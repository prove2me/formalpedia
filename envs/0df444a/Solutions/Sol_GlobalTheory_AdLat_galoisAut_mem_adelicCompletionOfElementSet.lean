-- Prove2me | solution 1 for GlobalTheory.AdLat.galoisAut_mem_adelicCompletionOfElementSet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:33:11.86325+00:00
-- url     : https://prove2.me/submissions/b2f56e65-21a3-4633-919d-9c6a80e9617d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Theorems.Thm_GlobalTheory_AdLat_tmul_mem_adelicCompletion_of_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.AdLat
theorem _root_.solution (c : E ≃ₐ[F] E) {I J : Set E} (h : ∀ x ∈ I, c x ∈ J)
    {z : RA F E} (hz : z ∈ hat1 F I) : sg (FiniteAdeleRing (𝓞 F) F) c z ∈ hat1 F J := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hx
    exact tmul_mem_adelicCompletion_of_integral F ha (h x hx)
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | neg y _ h1 => rw [map_neg]; exact neg_mem h1
end GlobalTheory.AdLat
