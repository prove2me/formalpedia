-- Prove2me | solution 1 for GlobalTheory.AdLat.lim_int_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:25:57.408874+00:00
-- url     : https://prove2.me/submissions/6de25ca1-7aa1-4fa3-bd4e-9fd9fd446098

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionLatticeSeparatedCompleteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealDivisibleEqZero
import Theorems.Thm_GlobalTheory_AdLat_lim_hat_induction
import Theorems.Thm_GlobalTheory_AdLat_lim_adele_smul_mem
import Theorems.Thm_GlobalTheory_AdLat_lim_fv_smul
import Theorems.Thm_GlobalTheory_AdLat_cap_fv_mem
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
open GlobalTheory GlobalTheory.AdLat
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.AdLat
theorem _root_.solution (L : Submodule (𝓞 E) (Fin n → E)) (r : 𝓞 E) {z : Fin n → RA F E}
    (hz : z ∈ hat F (L : Set (Fin n → E))) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (r : E) : RA F E) • z ∈ hat F (L : Set (Fin n → E)) := by
  refine lim_hat_induction F (fun z => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (r : E) : RA F E) • z ∈
    hat F (L : Set (Fin n → E))) ?_ ?_ ?_ ?_ hz
  · simp
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx
  · intro b hb x hx
    rw [smul_comm, ← lim_fv_smul]
    exact lim_adele_smul_mem F b hb (cap_fv_mem F _ _ (L.smul_mem r hx))
end GlobalTheory.AdLat
