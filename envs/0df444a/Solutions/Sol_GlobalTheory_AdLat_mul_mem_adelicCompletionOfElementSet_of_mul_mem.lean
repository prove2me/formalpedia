-- Prove2me | solution 1 for GlobalTheory.AdLat.mul_mem_adelicCompletionOfElementSet_of_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:02.463803+00:00
-- url     : https://prove2.me/submissions/d63f2342-1b48-428b-9cde-adcd16db731f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Theorems.Thm_GlobalTheory_AdLat_adele_mul_integral
import Theorems.Thm_GlobalTheory_AdLat_tmul_mem_adelicCompletion_of_integral

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
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.AdLat
theorem _root_.solution {I J K : Set E} (h : ∀ x ∈ I, ∀ y ∈ J, x * y ∈ K)
    {x y : RA F E} (hx : x ∈ hat1 F I) (hy : y ∈ hat1 F J) : x * y ∈ hat1 F K := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨b, hb, y, hy, rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_adelicCompletion_of_integral F (fun v => adele_mul_integral F (ha v) (hb v))
        (h x hx y hy)
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | neg y _ h1 => rw [mul_neg]; exact neg_mem h1
  | zero => rw [zero_mul]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | neg y _ h1 => rw [neg_mul]; exact neg_mem h1
end GlobalTheory.AdLat
