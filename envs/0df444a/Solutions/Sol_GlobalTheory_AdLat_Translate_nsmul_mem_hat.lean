-- Prove2me | solution 1 for GlobalTheory.AdLat.Translate.nsmul_mem_hat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:38:39.657905+00:00
-- url     : https://prove2.me/submissions/46282d5c-d59d-4050-840c-3298e96c24b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Theorems.Thm_GlobalTheory_AdLat_Translate_fv_nsmul
import Theorems.Thm_GlobalTheory_AdLat_Translate_gen_eq
import Theorems.Thm_GlobalTheory_AdLat_Translate_fv_mem_hat
import Theorems.Thm_GlobalTheory_AdLat_Translate_hat_smul_int
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Translate
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.AdLat.Translate
theorem _root_.solution {S S' : Set (Fin n → E)} {d : ℕ} (h : ∀ x ∈ S, d • x ∈ S') {z : Fin n → RA F E}
    (hz : z ∈ hat F S) : d • z ∈ hat F S' := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hz
    rw [gen_eq, smul_comm, ← fv_nsmul]
    exact hat_smul_int ha' (fv_mem_hat (h x hx))
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx
end GlobalTheory.AdLat.Translate
