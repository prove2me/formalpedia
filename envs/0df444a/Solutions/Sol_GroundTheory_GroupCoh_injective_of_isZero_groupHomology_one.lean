-- Prove2me | solution 1 for GroundTheory.GroupCoh.injective_of_isZero_groupHomology_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:35:42.809401+00:00
-- url     : https://prove2.me/submissions/84b363cd-94d1-4cd0-a227-84c3a1c064a9

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_TateAddEquivAbelianizationTateClass
import Definitions.Def_GroundTheory_TateCohomology_PGroupFixed
import Definitions.Def_GroundTheory_TateCohomology_PGroupFree
import Theorems.Thm_P2M_GroundTheory_GroupCoh_d___apply_eq_sum_78c801493460
import Theorems.Thm_GroundTheory_GroupCoh_exists_chain_ker_of_isZero_groupHomology_one
import Theorems.Thm_GroundTheory_GroupCoh_subsingleton_of_coinvariantsKer_eq_top


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
variable {k G : Type u} [Field k] [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] [CharP k p]
namespace GroundTheory.GroupCoh
theorem _root_.solution (hG : IsPGroup p G) {A B : Rep.{u} k G} (f : A ⟶ B)
    (hsurj : Function.Surjective f.hom) (hB : IsZero (groupHomology B 1))
    (hker : ∀ x, f.hom x = 0 → x ∈ Coinvariants.ker A.ρ) : Function.Injective f.hom := by
  let K := LinearMap.ker f.hom.toLinearMap
  have hK : ∀ g, K ≤ K.comap (A.ρ g) := fun g x hx => by
    have hx' : f.hom x = 0 := LinearMap.mem_ker.mp hx
    refine LinearMap.mem_ker.mpr ?_
    change f.hom (A.ρ g x) = 0
    rw [Rep.hom_comm_apply, hx', map_zero]
  let ρK : @Representation k G K _ _ AddCommGroup.toAddCommMonoid _ := A.ρ.subrepresentation K hK
  have hKI : Coinvariants.ker (k := k) (G := G) (V := K) ρK = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx0 : f.hom x = 0 := LinearMap.mem_ker.mp hx
    obtain ⟨z, hz, hdz⟩ := exists_chain_ker_of_isZero_groupHomology_one f hsurj hB hx0 (hker x hx0)
    have hzK : ∀ g, z g ∈ K := fun g => LinearMap.mem_ker.mpr (hz g)
    have hmem : (⟨x, hx⟩ : K) = ∑ g ∈ z.support, (ρK g⁻¹ ⟨z g, hzK g⟩ - ⟨z g, hzK g⟩) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      change x = _
      rw [← hdz, d₁₀_apply_eq_sum]
      rfl
    rw [hmem]
    exact Submodule.sum_mem _ fun g _ => Coinvariants.sub_mem_ker g⁻¹ _
  have hKs : Subsingleton K := by
    apply subsingleton_of_coinvariantsKer_eq_top hG ρK
    exact hKI
  intro x y hxy
  have hxy' : x - y ∈ K := LinearMap.mem_ker.mpr (by
    change f.hom (x - y) = 0
    rw [map_sub, hxy, sub_self])
  exact sub_eq_zero.mp (congrArg Subtype.val (Subsingleton.elim (⟨x - y, hxy'⟩ : K) 0))
end GroundTheory.GroupCoh
