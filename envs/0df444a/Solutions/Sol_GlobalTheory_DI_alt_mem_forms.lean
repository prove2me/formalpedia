-- Prove2me | solution 1 for GlobalTheory.DI.alt_mem_forms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:52:43.735718+00:00
-- url     : https://prove2.me/submissions/4d57bfef-c7ac-4e10-b675-a85e0152b7f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExteriorFormsSpanOfSetsMulSmulMonoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlternatingProductIntegral
import Theorems.Thm_GlobalTheory_DI_prodL_mem_forms_and_vanish

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI
namespace GlobalTheory.DI
theorem _root_.solution : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type}
    [LinearOrder ι] (f : ι → V →+ V) (h : ι → ι → V →+ K) (A : Subring K) (L : Set V) (s : Finset ι),
    (∀ i ∈ s, ∀ v ∈ L, ExteriorAlgebra.ι K (f i v) ∈ forms (A : Set K) L 1) →
    (∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L, h i j v ∈ A) →
    ∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), (∀ k, v k ∈ L) → t ⊆ s →
      ∀ q, q + t.card = a + 1 → alt f h a v t ∈ forms (A : Set K) L q := by
  intro K _ V _ _ ι _ f h A L s hf hh a v t hv hts q hq
  rw [alt, Finset.sum_apply]
  refine AddSubgroup.sum_mem _ fun σ _ => ?_
  rw [Pi.smul_apply]
  refine zsmul_mem ?_ _
  refine (prodL_mem_forms_and_vanish f h A L s hf hh _ ?_ t).1 hts q (by rw [List.length_ofFn]; exact hq)
  intro w hw
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hw
  exact hv _
end GlobalTheory.DI
