-- Prove2me | solution 1 for GlobalTheory.TateDecomp.norm_le_of_close
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:36:50.667302+00:00
-- url     : https://prove2.me/submissions/c68ff669-0c54-4325-be74-aa79f1e634f0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Theorems.Thm_GlobalTheory_TateDecomp_subC_mono
import Theorems.Thm_GlobalTheory_TateDecomp_Ks_le_Kinf
import Theorems.Thm_GlobalTheory_TateDecomp_Xsum_le
import Theorems.Thm_GlobalTheory_TateDecomp_decomp
import Theorems.Thm_GlobalTheory_TateDecomp_Xsum_inter
import Theorems.Thm_GlobalTheory_TateDecomp_natCast_mul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.TateDecomp
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.TateDecomp
theorem _root_.solution (K : FinExt l) {j : ℕ} (hj : 1 ≤ j) {y x : PadicComplex l}
    (hy : y ∈ subC (Ks K j)) (hx : x ∈ Xsum K j) (m : ℕ)
    (h : ‖y - x‖ ≤ ‖(l : PadicComplex l)‖ ^ m) : ‖y‖ ≤ ‖(l : PadicComplex l)‖ ^ m := by
  have hl : (l : PadicComplex l) ^ m ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hz : (y - x) / (l : PadicComplex l) ^ m ∈ intC (Kinf K) := by
    refine intC_iff.2 ⟨div_mem (sub_mem (subC_mono (Ks_le_Kinf K j) hy)
      (intC_iff.1 (Xsum_le K j hx)).1) (pow_mem (natCast_mem _ _) _), ?_⟩
    rw [norm_div, norm_pow]
    exact div_le_one_of_le₀ h (by positivity)
  obtain ⟨y', hy', h'⟩ := decomp K hj hz
  have h1 := add_mem (natCast_mul_mem h' m) hx
  have h2 : (l : PadicComplex l) ^ m * ((y - x) / (l : PadicComplex l) ^ m - y') + x
      = y - (l : PadicComplex l) ^ m * y' := by
    field_simp
    ring
  rw [h2] at h1
  have h3 := Xsum_inter K hj h1
    (sub_mem hy (mul_mem (pow_mem (natCast_mem _ _) _) (intC_iff.1 hy').1))
  rw [sub_eq_zero.1 h3, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) hy'.2
end GlobalTheory.TateDecomp
