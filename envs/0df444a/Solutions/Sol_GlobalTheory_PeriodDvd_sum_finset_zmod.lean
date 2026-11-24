-- Prove2me | solution 1 for GlobalTheory.PeriodDvd.sum_finset_zmod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:22:52.778595+00:00
-- url     : https://prove2.me/submissions/235385cb-d7e5-4ca6-95da-89e309fd258e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDvdSumOfInvariantOfCardStabilizerDvd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvdOfPeriodOfDvdSumPowersetCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Pointwise
open GlobalTheory
open GlobalTheory.PeriodDvd
namespace GlobalTheory.PeriodDvd
theorem _root_.solution {d : ℕ} [NeZero d] (s : ℕ) (f : ℕ → ℤ) (q : ℕ) :
    ∑ I : Finset (ZMod d), (if I.card = s then f (∑ x ∈ I, q ^ x.val) else 0)
      = ∑ I ∈ (Finset.range d).powersetCard s, f (∑ i ∈ I, q ^ i) := by
  have hinj : Function.Injective (ZMod.val : ZMod d → ℕ) := ZMod.val_injective d
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun I _ => I.image ZMod.val) ?_ ?_ ?_ ?_
  · intro I hI
    rw [Finset.mem_powersetCard, Finset.card_image_of_injective _ hinj]
    refine ⟨fun y hy => ?_, (Finset.mem_filter.mp hI).2⟩
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_range.mpr (ZMod.val_lt x)
  · intro I _ J _ hIJ
    exact Finset.image_injective hinj hIJ
  · intro J hJ
    rw [Finset.mem_powersetCard] at hJ
    have hJ' : (J.image (fun n : ℕ => (n : ZMod d))).image ZMod.val = J := by
      rw [Finset.image_image]
      refine (Finset.image_congr (g := id) fun n hn => ?_).trans Finset.image_id
      exact ZMod.val_cast_of_lt (Finset.mem_range.mp (hJ.1 hn))
    refine ⟨J.image (fun n : ℕ => (n : ZMod d)), ?_, hJ'⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← Finset.card_image_of_injective _ hinj, hJ', hJ.2]
  · intro I _
    rw [Finset.sum_image fun x _ y _ h => hinj h]
end GlobalTheory.PeriodDvd
