-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.canon_mul_e_diag_of_not_hasUpper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:07:40.583071+00:00
-- url     : https://prove2.me/submissions/7655e859-3092-4dca-a4bc-74fdb5eb372e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_VermaCoordEqZeroOfMemNPlusU
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_blockW_congr
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_blockW_eq_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_eq_triangular
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_diagExp_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_expand_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcEmb_X
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProj0_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_lowL
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_upL
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_not_lower_of_diag
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_not_upper_of_diag
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_pbw_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.canon_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.diagExp_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.expand_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.hcEmb_X
attribute [local simp] GroundTheory.Automorphic.HarishChandra.hcProj0_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_nil
attribute [local simp] GroundTheory.Automorphic.HarishChandra.pbw_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_nil



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution {m : Fin n × Fin n →₀ ℕ} (h : ¬ HasUpper m) (k : Fin n) :
    canon m * e (k, k) = canon (m + Finsupp.single (k, k) 1) := by
  have hup : ∀ a ∈ upL n, m a = 0 := fun a ha => by
    by_contra hne; exact h ⟨a, mem_upL.1 ha, hne⟩
  have hk : ¬ IsUpper (k, k) := not_upper_of_diag (a := (k, k)) rfl
  have hup' : ∀ a ∈ upL n, (m + Finsupp.single (k, k) 1 : Fin n × Fin n →₀ ℕ) a = 0 := fun a ha => by
    have hne : a ≠ (k, k) := fun hak => hk (hak ▸ mem_upL.1 ha)
    simp [hup a ha, Ne.symm hne]
  have hlow : blockW (lowL n) (m + Finsupp.single (k, k) 1) = blockW (lowL n) m := by
    refine blockW_congr fun a ha => ?_
    have hne : a ≠ (k, k) := fun hak => not_lower_of_diag (a := (k, k)) rfl (hak ▸ mem_lowL.1 ha)
    simp [Finsupp.single_apply, Ne.symm hne]
  have hdiag : diagExp (m + Finsupp.single (k, k) 1) = diagExp m + Finsupp.single k 1 := by
    ext i
    simp only [diagExp_apply, Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq, and_self]
  rw [canon_eq_triangular, canon_eq_triangular, blockW_eq_nil hup, blockW_eq_nil hup', hlow, hdiag,
    show monomial (diagExp m + Finsupp.single k 1) (1 : ℂ) = monomial (diagExp m) 1 * X k by
      rw [X, monomial_mul, mul_one], map_mul, hcEmb_X]
  simp only [word_nil, mul_one, mul_assoc]
end GroundTheory.Automorphic.HarishChandra
