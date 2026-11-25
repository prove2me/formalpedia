-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.fiber_eq_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:29:01.073197+00:00
-- url     : https://prove2.me/submissions/1a594ac3-daa4-4896-a240-7b4fffe7c210

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_biAction_smul
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_bruhatCell_eq_of_mem
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_mem_cellLe_of_eq
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_bruhatCell_smul
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_cellMinor_smul
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_bruhatCell_diag_perm
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_cellMinor_mul_mul
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_eq_mul_diag_perm_mul
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_eq_mul_mul_of_cellMinor_eq
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Whittaker.transl_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction Matrix DoubleCoset ValuativeRel
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] {n : ℕ}
attribute [local instance] biAction
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
attribute [local instance] totallyDisconnectedSpace_localField
attribute [local instance] continuousSMul_biAction
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {g : GL (Fin n) F} {U : Set (GL (Fin n) F)} (hUge : U ⊆ cellGe g)
    (hcellU : ∀ h, bruhatCell h = bruhatCell g → h ∈ U) {x : GL (Fin n) F} (hxU : x ∈ U)
    (hxC : x ∈ cellLe g) :
    ∃ t : Fin n → Fˣ, U ∩ (cellLe g ∩ cellMinor (bruhatCell g) ⁻¹' {cellMinor (bruhatCell g) x}) =
      orbit (NN F n) (Iwasawa.diagGL F n t * permGL F (bruhatCell g)) := by
  set w := bruhatCell g with hw
  have hxw : bruhatCell x = w := bruhatCell_eq_of_mem (hUge hxU) hxC
  obtain ⟨t, a, ha, b, hb, hx⟩ := exists_eq_mul_diag_perm_mul hxw
  have hx0w : bruhatCell (Iwasawa.diagGL F n t * permGL F w) = w := bruhatCell_diag_perm t w
  refine ⟨t, Set.Subset.antisymm ?_ ?_⟩
  · rintro z ⟨hzU, hzC, hzp⟩
    have hzw : bruhatCell z = w := bruhatCell_eq_of_mem (hUge hzU) hzC
    have hp : cellMinor w (Iwasawa.diagGL F n t * permGL F w) = cellMinor w z := by
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hzp
      rw [hzp, hx, cellMinor_mul_mul hx0w ha hb]
    obtain ⟨a', ha', b', hb', hz⟩ := exists_eq_mul_mul_of_cellMinor_eq hx0w hzw hp
    refine ⟨(⟨a', ha'⟩, ⟨b'⁻¹, (Iwasawa.unipotent F n).inv_mem hb'⟩), ?_⟩
    show (_ : NN F n) • _ = z
    rw [biAction_smul, hz]
    simp
  · rintro _ ⟨k, rfl⟩
    have hkw : bruhatCell (k • (Iwasawa.diagGL F n t * permGL F w)) = w := by
      rw [bruhatCell_smul, hx0w]
    refine ⟨hcellU _ hkw, mem_cellLe_of_eq hkw, ?_⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff, cellMinor_smul hx0w, hx,
      cellMinor_mul_mul hx0w ha hb]
end GroundTheory.Automorphic.Whittaker
