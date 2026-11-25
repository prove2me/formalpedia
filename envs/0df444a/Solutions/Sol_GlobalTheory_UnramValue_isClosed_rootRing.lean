-- Prove2me | solution 1 for GlobalTheory.UnramValue.isClosed_rootRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:11:40.103791+00:00
-- url     : https://prove2.me/submissions/31ec8f73-3cf4-4fdd-9a05-b465d6714e93

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfield
import Theorems.Thm_GlobalTheory_UnramValue_norm_algebraMap_int
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
noncomputable section
namespace GlobalTheory.UnramValue
variable {l : ℕ} [Fact l.Prime]
private lemma rootRing_eq_span_roots_of_unity (m : ℕ) :
    (rootRing l m : Set (Om l)) = Submodule.span ℤ_[l] {x : Om l | x ^ m = 1} := by
  have h := Algebra.adjoin_eq_span_of_subset (R := ℤ_[l]) (s := {x : Om l | x ^ m = 1}) (by
    intro x hx
    apply Submodule.subset_span
    induction hx using Submonoid.closure_induction with
    | mem y hy => exact hy
    | one => exact one_pow m
    | mul y z _ _ hy hz =>
      have hy' : y ^ m = 1 := hy
      have hz' : z ^ m = 1 := hz
      show (y * z) ^ m = 1
      rw [mul_pow, hy', hz', one_mul])
  rw [← h]
  rfl
end GlobalTheory.UnramValue
end
end

set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
noncomputable section
open GlobalTheory GlobalTheory.UnramValue
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.UnramValue
theorem _root_.solution {m : ℕ} (hm : 0 < m) : IsClosed (rootRing l m : Set (Om l)) := by
  classical
  set T : Finset (Om l) := (Polynomial.nthRoots m (1 : Om l)).toFinset with hT
  have hS : {x : Om l | x ^ m = 1} = Set.range (fun i : T => (i : Om l)) := by
    ext x
    simp [T, Polynomial.mem_nthRoots hm]
  have hc : Continuous (algebraMap ℤ_[l] (Om l)) :=
    (AddMonoidHomClass.isometry_of_norm (algebraMap ℤ_[l] (Om l)) norm_algebraMap_int).continuous
  have hf : Continuous (fun c : T → ℤ_[l] => ∑ i, c i • (i : Om l)) := by
    refine continuous_finsetSum _ (fun i _ => ?_)
    simp only [Algebra.smul_def]
    exact (hc.comp (continuous_apply i)).mul continuous_const
  have heq : (rootRing l m : Set (Om l)) =
      Set.range (fun c : T → ℤ_[l] => ∑ i, c i • (i : Om l)) := by
    rw [rootRing_eq_span_roots_of_unity, hS]
    ext x
    simp only [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun, Set.mem_range]
  rw [heq]
  exact (isCompact_range hf).isClosed
end GlobalTheory.UnramValue
