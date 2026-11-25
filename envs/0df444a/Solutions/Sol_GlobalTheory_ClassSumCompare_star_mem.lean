-- Prove2me | solution 1 for GlobalTheory.ClassSumCompare.star_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:33:25.496863+00:00
-- url     : https://prove2.me/submissions/cc4b179d-a7df-48c7-b02b-012ecc80de2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdelicNormWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNatMulInt
import Theorems.Thm_GlobalTheory_ClassSumCompare_incl_mem
import Theorems.Thm_GlobalTheory_ClassSumCompare_diag_mem_iff
import Theorems.Thm_GlobalTheory_ClassSumCompare_star_diag
import Theorems.Thm_GlobalTheory_ClassSumCompare_star_incl
import Theorems.Thm_GlobalTheory_ClassSumCompare_conj_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassSumCompare
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight
open scoped TensorProduct nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
namespace GlobalTheory.ClassSumCompare
theorem _root_.solution {x : AdE E} (hx : x ∈ intAd E) : star x ∈ intAd E := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, ha, rfl⟩ | ⟨o, rfl⟩
    · rw [star_incl]; exact incl_mem ha
    · show star (diagE E o) ∈ _
      rw [star_diag, diag_mem_iff]; exact conj_int o
  | zero => rw [star_zero]; exact zero_mem _
  | one => rw [star_one]; exact one_mem _
  | add x y _ _ hx hy => rw [star_add]; exact add_mem hx hy
  | neg x _ hx => rw [star_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [star_mul]; exact mul_mem hy hx
end GlobalTheory.ClassSumCompare
