-- Prove2me | solution 1 for GroundTheory.Global.cycHerbrand_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:08:43.972175+00:00
-- url     : https://prove2.me/submissions/be5cbfae-0c3e-4d93-890c-ad8e3f0dd486

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Theorems.Thm_GroundTheory_Global_cycHerbrand_eq
import Theorems.Thm_GroundTheory_Global_piRep_apply
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply


attribute [local simp] GroundTheory.Global.piRep_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
variable {k G ι : Type*} [CommRing k] [Group G] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
  [∀ i, Module k (V i)]
variable [Fintype G]
namespace GroundTheory.Global
theorem _root_.solution [Fintype ι] (ρ : ∀ i, Representation k G (V i)) (σ : G) :
    cycHerbrand (piRep ρ) σ = ∏ i, cycHerbrand (ρ i) σ := by
  simp only [cycHerbrand_eq]
  rw [Nat.card_congr (cycTateZeroPiEquiv ρ σ).toEquiv,
    Nat.card_congr (cycTateNegOnePiEquiv ρ σ).toEquiv, Nat.card_pi, Nat.card_pi,
    Nat.cast_prod, Nat.cast_prod, Finset.prod_div_distrib]
end GroundTheory.Global
