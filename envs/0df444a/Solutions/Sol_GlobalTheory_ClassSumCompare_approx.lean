-- Prove2me | solution 1 for GlobalTheory.ClassSumCompare.approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:30:51.709635+00:00
-- url     : https://prove2.me/submissions/e6d4ad7a-4c89-4bf2-af8a-de4125597b7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdelicNormWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNatMulInt
import Theorems.Thm_GlobalTheory_ClassSumCompare_tmul_eq
import Theorems.Thm_GlobalTheory_ClassSumCompare_incl_mem
import Theorems.Thm_GlobalTheory_ClassSumCompare_diag_int_mem
import Theorems.Thm_GlobalTheory_ClassSumCompare_diag_algebraMap
import Theorems.Thm_GlobalTheory_ClassSumCompare_exists_tmul_int
import Theorems.Thm_GlobalTheory_AdLat_exists_eq_algebraMap_add_nsmul
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
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassSumCompare
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight
open scoped TensorProduct nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
namespace GlobalTheory.ClassSumCompare
theorem _root_.solution (m : ℕ) (hm : 0 < m) (x : AdE E) : ∃ e : E, ∃ u ∈ intAd E, x = diagE E e + (m : AdE E) * u := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by show (0 : AdE E) = _; simp⟩
  | tmul a e =>
    obtain ⟨t, o, h⟩ := exists_tmul_int a e
    obtain ⟨x, a', ha', h'⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul _ m hm (algebraMap _ (AdF E) t * a)
    refine ⟨algebraMap _ E x * o, inclF E a' * diagE E o, mul_mem (incl_mem ha') (diag_int_mem o), ?_⟩
    refine (tmul_eq a e).trans ?_
    rw [h, h', map_add, map_mul, diag_algebraMap, map_nsmul, nsmul_eq_mul]
    ring
  | add x y hx hy =>
    obtain ⟨e, u, hu, hx⟩ := hx
    obtain ⟨e', u', hu', hy⟩ := hy
    refine ⟨e + e', u + u', add_mem hu hu', ?_⟩
    show (show AdE E from x) + (show AdE E from y) = _
    rw [show (show AdE E from x) = _ from hx, show (show AdE E from y) = _ from hy, map_add]
    ring
end GlobalTheory.ClassSumCompare
