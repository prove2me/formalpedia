-- Prove2me | solution 1 for GroundTheory.Global.sum_smul_eq_of_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:34:24.450393+00:00
-- url     : https://prove2.me/submissions/59f8ed46-e588-4bce-910d-cceff7944817

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Theorems.Thm_GroundTheory_Global_orbitPoint_mem
import Theorems.Thm_GroundTheory_Global_orbitPoint_smul
import Theorems.Thm_GroundTheory_Global_card_filter_smul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh MulAction
variable (G : Type*) {X : Type*} [Group G] [MulAction G X]
variable {G}
variable [Fintype G]
namespace GroundTheory.Global
theorem _root_.solution (F : X → ℤ) (hF : ∀ y, F y ≠ 0 → orbitPoint G y = y) (p : X) :
    ∑ g : G, F (g • p) = Nat.card (stabilizer G p) * F (orbitPoint G p) := by
  classical
  have h1 : ∀ g : G, F (g • p) = if g • p = orbitPoint G p then F (orbitPoint G p) else 0 := by
    intro g
    split_ifs with hg
    · rw [hg]
    · by_contra hne
      apply hg
      rw [← hF _ hne, orbitPoint_smul]
  rw [Finset.sum_congr rfl fun g _ => h1 g, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  obtain ⟨g₀, hg₀⟩ := orbitPoint_mem (G := G) p
  rw [← show g₀ • p = orbitPoint G p from hg₀, ← card_filter_smul_eq p g₀]
end GroundTheory.Global
