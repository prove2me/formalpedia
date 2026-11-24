-- Prove2me | solution 1 for GlobalTheory.GradedFixed.mem_of_orbits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:12:50.894425+00:00
-- url     : https://prove2.me/submissions/d3be3ae0-51fb-47ef-b0f8-3391276cd8cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FixedMemOfOrbitHeight
import Theorems.Thm_GlobalTheory_GradedFixed_WA_mono
import Theorems.Thm_GlobalTheory_GradedFixed_WA_union
import Theorems.Thm_GlobalTheory_GradedFixed_orbit_stable
import Theorems.Thm_GlobalTheory_GradedFixed_fixed_part

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule MulAction
open GlobalTheory GlobalTheory.GradedFixed
variable {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.GradedFixed
theorem _root_.solution (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M) (hV : iSupIndep V)
    (hπ : ∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i)) (S : Submodule ℂ M) (F : Finset ι) :
    (∀ i ∈ F, ∀ x, (∀ g, π g x = x) → x ∈ WA V (orbit G i) → x ∈ S) →
    ∀ u, (∀ g, π g u = u) → u ∈ WA V (⋃ i ∈ F, orbit G i) → u ∈ S := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    intro _ u _ hu
    have : u = 0 := by simpa [WA] using hu
    rw [this]; exact zero_mem S
  | insert i F hi ih =>
    intro hT u hu huF
    have hset : (⋃ j ∈ insert i F, orbit G j) = orbit G i ∪ ((⋃ j ∈ F, orbit G j) \ orbit G i) := by
      rw [Finset.set_biUnion_insert, Set.union_diff_self]
    rw [hset, WA_union, Submodule.mem_sup] at huF
    obtain ⟨a, ha, b, hb, rfl⟩ := huF
    have hA : ∀ (g : G), ∀ j ∈ orbit G i, g • j ∈ orbit G i := fun g j hj => orbit_stable i g hj
    have hU : ∀ (g : G), ∀ j ∈ (⋃ k ∈ F, orbit G k), g • j ∈ (⋃ k ∈ F, orbit G k) := by
      intro g j hj
      obtain ⟨k, hk, hjk⟩ := Set.mem_iUnion₂.mp hj
      exact Set.mem_iUnion₂.mpr ⟨k, hk, orbit_stable k g hjk⟩
    have hB : ∀ (g : G), ∀ j ∈ ((⋃ k ∈ F, orbit G k) \ orbit G i),
        g • j ∈ ((⋃ k ∈ F, orbit G k) \ orbit G i) := by
      intro g j hj
      exact ⟨hU g j hj.1, fun h => hj.2 (by simpa using orbit_stable i g⁻¹ h)⟩
    have hAB : Disjoint (orbit G i) ((⋃ k ∈ F, orbit G k) \ orbit G i) := Set.disjoint_sdiff_right
    have hafix := fixed_part π V hV hπ hA hB hAB ha hb hu
    have hbfix : ∀ g, π g b = b :=
      fixed_part π V hV hπ hB hA hAB.symm hb ha (fun g => by rw [add_comm]; exact hu g)
    exact add_mem (hT i (Finset.mem_insert_self i F) a hafix ha)
      (ih (fun j hj => hT j (Finset.mem_insert_of_mem hj)) b hbfix (WA_mono V Set.diff_subset hb))
end GlobalTheory.GradedFixed
