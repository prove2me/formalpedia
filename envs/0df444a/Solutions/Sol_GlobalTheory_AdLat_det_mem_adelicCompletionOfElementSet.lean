-- Prove2me | solution 1 for GlobalTheory.AdLat.det_mem_adelicCompletionOfElementSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:20:14.461429+00:00
-- url     : https://prove2.me/submissions/4cece3a3-7842-4c5e-aa8d-cadf69d692a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemAdelicCompletionPseudoBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Theorems.Thm_GlobalTheory_AdLat_prod_mem_adelicCompletionOfElementSet

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
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.AdLat
theorem _root_.solution {n : ℕ} (r s : Fin n → FractionalIdeal (𝓞 E)⁰ E)
    (M : Matrix (Fin n) (Fin n) (RA F E))
    (h : ∀ i j, M i j ∈ hat1 F ((r i * s j : FractionalIdeal (𝓞 E)⁰ E) : Set E)) :
    M.det ∈ hat1 F (((∏ i, r i) * ∏ j, s j : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  rw [Matrix.det_apply]
  refine sum_mem fun σ _ => ?_
  have := prod_mem_adelicCompletionOfElementSet F Finset.univ (fun j => r (σ j) * s j) (fun j => M (σ j) j)
    (fun j _ => h _ _)
  rw [Finset.prod_mul_distrib, Equiv.prod_comp σ r] at this
  rw [Units.smul_def]
  exact zsmul_mem this _
end GlobalTheory.AdLat
