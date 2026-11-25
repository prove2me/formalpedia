-- Prove2me | solution 1 for GroundTheory.Global.ker_normHom_le_range_cycSub_ofMulAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:41:57.618253+00:00
-- url     : https://prove2.me/submissions/9cbc4ea9-0985-4b72-b418-0835e9ef3430

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Theorems.Thm_GroundTheory_Global_orbitPoint_mem
import Theorems.Thm_GroundTheory_Global_orbitPoint_orbitPoint
import Theorems.Thm_GroundTheory_Global_sum_smul_eq_of_support
import Theorems.Thm_GroundTheory_Global_coeff_normHom_ofMulAction
import Theorems.Thm_GroundTheory_Global_coeff_permOfFun
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_normHom_cycSub
import Theorems.Thm_GroundTheory_Global_sub_mem_range_cycSub
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply


attribute [local simp] GroundTheory.Global.coeff_permOfFun

set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh MulAction
variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X] {σ : G}
namespace GroundTheory.Global
theorem _root_.solution (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    (normHom (Representation.ofMulAction ℤ G X)).ker ≤
      (cycSub (Representation.ofMulAction ℤ G X) σ).range := by
  classical
  have := Fintype.ofFinite X
  intro f hf
  let u : MonoidAlgebra ℤ X := ∑ x, f.coeff x • MonoidAlgebra.single (orbitPoint G x) 1
  have hcoeff_u : ∀ y, u.coeff y = ∑ x, if orbitPoint G x = y then f.coeff x else 0 := by
    intro y
    simp [u, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply]
  have hfu : f - u ∈ (cycSub (Representation.ofMulAction ℤ G X) σ).range := by
    have hf' : f - u = ∑ x, f.coeff x • (MonoidAlgebra.single x (1 : ℤ) -
        MonoidAlgebra.single (orbitPoint G x) 1) := by
      ext y
      rw [MonoidAlgebra.coeff_sub, Finsupp.sub_apply, hcoeff_u]
      simp [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single,
        Finsupp.single_apply, mul_sub, Finset.sum_sub_distrib]
    rw [hf']
    refine AddSubgroup.sum_mem _ fun x _ => AddSubgroup.zsmul_mem _ ?_ _
    obtain ⟨g, hg⟩ := orbitPoint_mem (G := G) x
    have : MonoidAlgebra.single (orbitPoint G x) (1 : ℤ) = (Representation.ofMulAction ℤ G X) g (MonoidAlgebra.single x 1) := by
      rw [Representation.ofMulAction_single, ← show g • x = orbitPoint G x from hg]
    rw [this, ← neg_sub]
    exact neg_mem (sub_mem_range_cycSub (Representation.ofMulAction ℤ G X) hσ g _)
  have hNu : normHom (Representation.ofMulAction ℤ G X) u = 0 := by
    obtain ⟨v, hv⟩ := hfu
    have : u = f - cycSub (Representation.ofMulAction ℤ G X) σ v := by rw [hv]; abel
    rw [this, map_sub, AddMonoidHom.mem_ker.1 hf, normHom_cycSub, sub_zero]
  have hsupp : ∀ y, u.coeff y ≠ 0 → orbitPoint G y = y := by
    intro y hy
    rw [hcoeff_u] at hy
    obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
    have hxy : orbitPoint G x = y := by
      by_contra h
      exact hx (if_neg h)
    rw [← hxy, orbitPoint_orbitPoint]
  have hu : u = 0 := by
    ext p
    rw [MonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    by_contra hp
    have hrep := hsupp p hp
    have h1 := congrArg (fun f : MonoidAlgebra ℤ X => f.coeff p) hNu
    simp only [MonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h1
    rw [coeff_normHom_ofMulAction] at h1
    rw [sum_smul_eq_of_support (fun y => u.coeff y) hsupp p, hrep] at h1
    have hs : (Nat.card (stabilizer G p) : ℤ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    exact hp ((mul_eq_zero.1 h1).resolve_left hs)
  rwa [hu, sub_zero] at hfu
end GroundTheory.Global
