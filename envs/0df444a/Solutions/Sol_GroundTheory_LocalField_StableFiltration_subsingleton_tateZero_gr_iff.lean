-- Prove2me | solution 1 for GroundTheory.LocalField.StableFiltration.subsingleton_tateZero_gr_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:37.035878+00:00
-- url     : https://prove2.me/submissions/9106632a-4b00-4f0b-97d8-f460fdfa76c7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Theorems.Thm_GroundTheory_LocalField_subsingleton_tateZero_iff
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_grMk_eq_grMk_iff
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_smul_grMk
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_tateNorm_F
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_tateNorm_grMk

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
open GroundTheory.LocalField.StableFiltration
variable {G V : Type*} [Group G] [CommGroup V] [MulDistribMulAction G V]
  (S : StableFiltration G V)
variable [Fintype G]
namespace GroundTheory.LocalField.StableFiltration
theorem _root_.solution (n : ℕ) :
    Subsingleton (TateZero G (S.gr n)) ↔
      ∀ x ∈ S.F n, (∀ g : G, g • x / x ∈ S.F (n + 1)) →
        ∃ y ∈ S.F n, x / tateNorm G V y ∈ S.F (n + 1) := by
  rw [subsingleton_tateZero_iff]
  constructor
  · intro h x hx hinv
    obtain ⟨q, hq⟩ := h (S.grMk n ⟨x, hx⟩) fun g => by
      rw [smul_grMk, grMk_eq_grMk_iff]
      exact hinv g
    obtain ⟨y, rfl⟩ := S.grMk_surjective n q
    rw [tateNorm_grMk, eq_comm, grMk_eq_grMk_iff, coe_tateNorm_F] at hq
    exact ⟨y, y.2, hq⟩
  · intro h q hq
    obtain ⟨x, rfl⟩ := S.grMk_surjective n q
    obtain ⟨y, hy, hxy⟩ := h x x.2 fun g => by
      have := hq g
      rw [smul_grMk, grMk_eq_grMk_iff] at this
      exact this
    refine ⟨S.grMk n ⟨y, hy⟩, ?_⟩
    rw [tateNorm_grMk, eq_comm, grMk_eq_grMk_iff, coe_tateNorm_F]
    exact hxy
end GroundTheory.LocalField.StableFiltration
