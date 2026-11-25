-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.elimCol_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:38:25.932805+00:00
-- url     : https://prove2.me/submissions/af54ce9e-8e84-4ecf-97ff-ecddcfbe3eaf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {β}
variable (β)
variable {β}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (h : Matrix (Fin n) (Fin n) F) (a i l : Fin n) :
    (elimCol β h a * h) i l = if elimKey β a < elimKey β i then h i a / h a a * h a l else 0 := by
  rw [mul_apply]
  simp only [elimCol_apply]
  split_ifs with hi
  · rw [Finset.sum_eq_single a]
    · rw [if_pos ⟨rfl, hi⟩]
    · intro k _ hk
      rw [if_neg (fun h => hk h.1), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  · refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg (fun h => hi h.2), zero_mul]
end GroundTheory.Automorphic.Parabolic
