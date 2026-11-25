-- Prove2me | solution 1 for GlobalTheory.MultilinearSpanImage.multilinear_apply_mem_span_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:04:29.2568+00:00
-- url     : https://prove2.me/submissions/58703a3b-d9d2-445a-bda1-a0c5309d4536

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MultilinearMemSpanImagePartial
import Theorems.Thm_GlobalTheory_MultilinearSpanImage_multilinear_mem_span_image_partial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultilinearSpanImage
namespace GlobalTheory.MultilinearSpanImage
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type}
    [inst : (i : ι) → AddCommGroup (M i)] [inst_1 : (i : ι) → Module ℂ (M i)] {N : Type}
    [inst_2 : AddCommGroup N] [inst_3 : Module ℂ N] (Φ : MultilinearMap ℂ M N)
    (s : (i : ι) → Set (M i)) (f : (i : ι) → M i) (hf : ∀ (i : ι), f i ∈ Submodule.span ℂ (s i)) :
    (Φ : ((i : ι) → M i) → N) f ∈ Submodule.span ℂ
      {y : N | ∃ (g : (i : ι) → M i), (∀ (i : ι), g i ∈ s i) ∧ y = (Φ : ((i : ι) → M i) → N) g} :=
  multilinear_mem_span_image_partial Φ s Finset.univ f (fun i _ => hf i) (fun i hi => absurd (Finset.mem_univ i) hi)
end GlobalTheory.MultilinearSpanImage
