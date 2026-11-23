-- Prove2me | solution 1 for GlobalTheory.IntegralMultiples.exists_int_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:57:42.9625+00:00
-- url     : https://prove2.me/submissions/1968aeb7-7361-4d9f-ba13-494c6f369cd1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralMultiples
namespace GlobalTheory.IntegralMultiples
theorem _root_.solution {E : Type} [Field E] [NumberField E] {r : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin r → E))
    (hΛ : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (v : Fin r → E) :
    ∃ k : ℤ, k ≠ 0 ∧ k • v ∈ Λ := by
  classical
  have hv : v ∈ Submodule.span E (Λ : Set (Fin r → E)) := by
    rw [hΛ]
    exact Submodule.mem_top
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.mp hv
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image f)
  refine ⟨y, hy0, ?_⟩
  rw [← hfg, Finset.smul_sum]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  have hi := hy (f i) (Finset.mem_image_of_mem f (Finset.mem_univ i))
  let o : NumberField.RingOfIntegers E := ⟨y • f i, hi⟩
  have e : y • f i • (g i : Fin r → E) = o • (g i : Fin r → E) := by
    rw [← smul_assoc, ← algebraMap_smul E o]
    rfl
  rw [e]
  exact Λ.smul_mem o (g i).2
end GlobalTheory.IntegralMultiples
