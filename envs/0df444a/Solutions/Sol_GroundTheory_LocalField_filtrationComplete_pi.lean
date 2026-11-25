-- Prove2me | solution 1 for GroundTheory.LocalField.filtrationComplete_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:13:39.014545+00:00
-- url     : https://prove2.me/submissions/408c8f2c-e669-4c48-82b5-735e8708fc09

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Finset Filter
variable {V : Type*} [CommGroup V]
namespace GroundTheory.LocalField
theorem _root_.solution {ι : Type*} [Fintype ι] {F : ℕ → Subgroup V}
    (hc : FiltrationComplete F) :
    FiltrationComplete fun n => Subgroup.pi Set.univ fun _ : ι => F n := by
  intro x hx
  have hxi : ∀ i, FiltrationCauchy F fun k => x k i := by
    intro i N
    obtain ⟨M, hM⟩ := hx N
    exact ⟨M, fun m hm n hn => (Subgroup.mem_pi _).mp (hM m hm n hn) i (Set.mem_univ i)⟩
  choose y hy using fun i => hc _ (hxi i)
  refine ⟨y, fun N => ?_⟩
  choose M hM using fun i => hy i N
  refine ⟨Finset.univ.sup M, fun n hn => (Subgroup.mem_pi _).mpr fun i _ => ?_⟩
  exact hM i n ((Finset.le_sup (Finset.mem_univ i)).trans hn)
end GroundTheory.LocalField
