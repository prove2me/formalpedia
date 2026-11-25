-- Prove2me | solution 1 for GroundTheory.GroupCoh.exists_chain_ker_of_isZero_groupHomology_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:59:36.498288+00:00
-- url     : https://prove2.me/submissions/ab60c2f7-84a1-4be5-b31c-43233099c5e7

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_TateAddEquivAbelianizationTateClass
import Definitions.Def_GroundTheory_TateCohomology_PGroupFixed
import Definitions.Def_GroundTheory_TateCohomology_PGroupFree
import Theorems.Thm_P2M_GroundTheory_GroupCoh_d___mapRange_f2a791e02ad3
import Theorems.Thm_P2M_GroundTheory_GroupCoh_d___mapRange_cf7c0094db79

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits groupHomology Representation Finsupp
open scoped MonoidAlgebra
universe u
variable {k G : Type u} [CommRing k] [Group G] {A B : Rep.{u} k G}
namespace GroundTheory.GroupCoh
theorem _root_.solution (f : A ⟶ B)
    (hsurj : Function.Surjective f.hom) (hB : IsZero (groupHomology B 1)) {x : A}
    (hx : f.hom x = 0) (hxI : x ∈ Coinvariants.ker A.ρ) :
    ∃ z : G →₀ A, (∀ g, f.hom (z g) = 0) ∧ d₁₀ A z = x := by
  have hsurj' : Function.Surjective f.hom.toLinearMap := hsurj
  obtain ⟨y, hy⟩ : x ∈ LinearMap.range (d₁₀ A).hom := by
    rw [range_d₁₀_eq_coinvariantsKer]
    exact hxI
  let L := Finsupp.mapRange.linearMap (α := G) f.hom.toLinearMap
  have hY : L y ∈ cycles₁ B := by
    change d₁₀ B (L y) = 0
    rw [d₁₀_mapRange f y]
    change f.hom (d₁₀ A y) = 0
    rw [show d₁₀ A y = x from hy]
    exact hx
  have h0 : H1π B ⟨L y, hY⟩ = 0 :=
    @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero hB) _ _
  obtain ⟨c, hc⟩ := (H1π_eq_zero_iff _).mp h0
  obtain ⟨c', rfl⟩ := Finsupp.mapRange_surjective f.hom.toLinearMap (map_zero _) hsurj' c
  refine ⟨y - d₂₁ A c', fun g => ?_, ?_⟩
  · have h2 : L (d₂₁ A c') = L y := (d₂₁_mapRange f c').symm.trans hc
    have h4 : L (y - d₂₁ A c') = 0 := by
      have h5 : L (y - d₂₁ A c') = L y - L (d₂₁ A c') := map_sub L y _
      rw [h5, h2, sub_self]
    have := congrArg (fun w => w g) h4
    simpa [L] using this
  · have h3 : d₁₀ A (d₂₁ A c') = 0 := by simp
    have h5 : d₁₀ A (y - d₂₁ A c') = d₁₀ A y - d₁₀ A (d₂₁ A c') := map_sub (d₁₀ A).hom y _
    rw [h5, h3, sub_zero]
    exact hy
end GroundTheory.GroupCoh
