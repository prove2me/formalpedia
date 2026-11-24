-- Prove2me | solution 1 for GlobalTheory.AdLat.adelicHermitianFormGalois_mem_of_mem_completion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:23:12.835947+00:00
-- url     : https://prove2.me/submissions/432771c8-f17d-4e28-88d0-e09ed7df703c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionSelfDualOfSelfDualLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicHermitianFormGaloisMemOfMemCompletion
import Theorems.Thm_GlobalTheory_AdLat_hermA_tmul_right
import Theorems.Thm_GlobalTheory_AdLat_mul_mem_adelicCompletionOfElementSet_of_mul_mem
import Theorems.Thm_GlobalTheory_AdLat_tmul_mem_adelicCompletion_of_integral
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
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
  (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.AdLat
theorem _root_.solution {S : Set (Fin n → E)} {J : Set E} {z : Fin n → RA F E}
    (hz : ∀ y ∈ S, hermA c G z (fv F y) ∈ hat1 F J) {w : Fin n → RA F E} (hw : w ∈ hat F S) :
    hermA c G z w ∈ hat1 F J := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨t, ht, x, hx, rfl⟩ := hw
    rw [hermA_tmul_right]
    exact mul_mem_adelicCompletionOfElementSet_of_mul_mem F (I := {1}) (fun a ha b hb => by
      rw [Set.mem_singleton_iff.1 ha, one_mul]; exact hb) (tmul_mem_adelicCompletion_of_integral F ht rfl) (hz x hx)
  | zero =>
    have : hermA c G z 0 = 0 := by simp [hermA]
    rw [this]; exact zero_mem _
  | add w w' _ _ h h' =>
    have : hermA c G z (w + w') = hermA c G z w + hermA c G z w' := by
      simp only [hermA, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
    rw [this]; exact add_mem h h'
  | neg w _ h =>
    have : hermA c G z (-w) = - hermA c G z w := by
      simp only [hermA, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]
    rw [this]; exact neg_mem h
end GlobalTheory.AdLat
