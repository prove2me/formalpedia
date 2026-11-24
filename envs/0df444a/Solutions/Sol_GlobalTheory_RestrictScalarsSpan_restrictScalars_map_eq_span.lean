-- Prove2me | solution 1 for GlobalTheory.RestrictScalarsSpan.restrictScalars_map_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:15:33.601535+00:00
-- url     : https://prove2.me/submissions/8ee40472-9851-4af2-a0e2-c05464a0af7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_RestrictScalarsMapEqSpan
import Theorems.Thm_GlobalTheory_RestrictScalarsSpan_mul_mem_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3 u_4
open GlobalTheory GlobalTheory.RestrictScalarsSpan
namespace GlobalTheory.RestrictScalarsSpan
theorem _root_.solution {K : Type u_1} {L : Type u_2} {A : Type u_3} {B : Type u_4}
    [Field K] [Field L] [Algebra K L] [Ring A] [Ring B] [Algebra K A] [Algebra K B] [Algebra L B]
    [IsScalarTower K L B] {j : A →ₐ[K] B} (h : IsBaseChange L (AlgHom.toLinearMap j))
    (I : Ideal A) :
    Submodule.restrictScalars L (Ideal.map j I) =
      Submodule.span L ((⇑(AlgHom.toLinearMap j) : A → B) ''
        (↑(Submodule.restrictScalars K I) : Set A)) := by
  change _ = Submodule.span L ((j : A → B) '' (I : Set A))
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ Submodule.span B ((j : A → B) '' (I : Set A)) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul b y _ hy => exact mul_mem_span h I b y hy
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact Ideal.mem_map_of_mem j hi
end GlobalTheory.RestrictScalarsSpan
