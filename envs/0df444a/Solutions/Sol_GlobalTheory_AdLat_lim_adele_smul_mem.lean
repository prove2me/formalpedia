-- Prove2me | solution 1 for GlobalTheory.AdLat.lim_adele_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:04:31.969877+00:00
-- url     : https://prove2.me/submissions/3fd1c208-f805-4d1e-ba76-9e98d1ab10f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionLatticeSeparatedCompleteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealDivisibleEqZero
import Theorems.Thm_GlobalTheory_AdLat_lim_gen_eq
import Theorems.Thm_GlobalTheory_AdLat_lim_hat_induction
import Theorems.Thm_GlobalTheory_AdLat_adele_mul_integral
import Theorems.Thm_GlobalTheory_AdLat_cap_gen_mem
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
theorem _root_.solution {L : Set (Fin n → E)} (a : FiniteAdeleRing (𝓞 F) F)
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) {z : Fin n → RA F E} (hz : z ∈ hat F L) :
    a • z ∈ hat F L := by
  refine lim_hat_induction F (fun z => a • z ∈ hat F L) ?_ ?_ ?_ ?_ hz
  · simp
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx
  · intro b hb x hx
    rw [smul_smul, ← lim_gen_eq]
    exact cap_gen_mem F L _ (fun v => adele_mul_integral F (ha v) (hb v)) x hx
end GlobalTheory.AdLat
