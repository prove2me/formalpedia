-- Prove2me | solution 1 for GlobalTheory.AdLat.cramer_mem_adelicCompletionOfElementSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:42:47.356451+00:00
-- url     : https://prove2.me/submissions/1cda0d07-0775-460d-9b3a-360ea7a0d6a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemAdelicCompletionPseudoBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Theorems.Thm_GlobalTheory_AdLat_det_mem_adelicCompletionOfElementSet

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
theorem _root_.solution {n : ℕ} (cI : Fin n → FractionalIdeal (𝓞 E)⁰ E) (hc : ∀ a, cI a ≠ 0)
    (M : Matrix (Fin n) (Fin n) (RA F E))
    (h : ∀ i j, M i j ∈ hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E))
    (w : Fin n → RA F E) (hw : ∀ i, w i ∈ hat1 F (cI i : Set E)) (a : Fin n) :
    M.cramer w a ∈ hat1 F (cI a : Set E) := by
  rw [Matrix.cramer_apply]
  have := det_mem_adelicCompletionOfElementSet F cI (Function.update (fun j => (cI j)⁻¹) a 1) (M.updateCol a w) (by
    intro i j
    by_cases hj : j = a
    · subst hj
      simpa using hw i
    · simpa [hj] using h i j)
  have e : (∏ i, cI i) * ∏ j, Function.update (fun j => (cI j)⁻¹) a 1 j = cI a := by
    rw [← Finset.prod_mul_distrib, Finset.prod_eq_single a]
    · simp
    · intro b _ hb
      simp [hb, hc b]
    · simp
  rwa [e] at this
end GlobalTheory.AdLat
