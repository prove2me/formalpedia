-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.nonempty_splitPlace_five
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:53:11.639869+00:00
-- url     : https://prove2.me/submissions/cbae86b3-151e-4092-a4fb-6aaea6ed00c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SplitUnramifiedPlaces
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SplitUnramifiedPlaces_exists_sqrt_neg_one_five

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
variable {p : ℕ} [Fact p.Prime]
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces._p2m_local_instance_3272e94269_226
namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
theorem _root_.solution : Nonempty (SplitPlace 5 GaussianInt) := by
  obtain ⟨s, h, hs, hh⟩ := exists_sqrt_neg_one_five
  exact ⟨gaussPlace s h hs hh⟩
end GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
