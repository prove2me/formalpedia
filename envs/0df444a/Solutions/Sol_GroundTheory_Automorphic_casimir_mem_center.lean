-- Prove2me | solution 1 for GroundTheory.Automorphic.casimir_mem_center
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:45:52.997811+00:00
-- url     : https://prove2.me/submissions/286ba857-0bcd-41e2-889b-af3a48f722bc

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ZKFinite
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Theorems.Thm_P2M_GroundTheory_Automorphic_mem_center_of_forall___commute_47468f82d060
import Theorems.Thm_GroundTheory_Automorphic_eq_sum_of_orthogonal
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
variable (B : LinearMap.BilinForm ℝ L)
variable {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ L) (ε : ι → ℝ)
variable {B b ε}
namespace GroundTheory.Automorphic
theorem _root_.solution [DecidableEq ι] (hε : ∀ i, ε i * ε i = 1)
    (horth : ∀ i j, B (b i) (b j) = if i = j then ε i else 0)
    (hsymm : ∀ X Y : L, B X Y = B Y X) (hinv : ∀ X Y Z : L, B ⁅X, Y⁆ Z = -B Y ⁅X, Z⁆) :
    casimir b ε ∈ Subalgebra.center ℝ (UniversalEnvelopingAlgebra ℝ L) := by
  apply mem_center_of_forall_ι_commute
  intro X
  rw [← sub_eq_zero]
  set ιu := UniversalEnvelopingAlgebra.ι ℝ (L := L)
  set a : ι → ι → ℝ := fun i j => ε i * (ε j * B (b j) ⁅X, b i⁆)
  set T : ι → ι → UniversalEnvelopingAlgebra ℝ L := fun i j => ιu (b j) * ιu (b i) + ιu (b i) * ιu (b j)
  have hanti : ∀ i j, a j i = -a i j := by
    intro i j
    simp only [a]
    rw [hsymm (b i), hinv, hsymm]
    ring
  have hT : ∀ i j, T j i = T i j := by intro i j; simp only [T]; abel
  have hcomm : ∀ i, ιu X * (ιu (b i) * ιu (b i)) - ιu (b i) * ιu (b i) * ιu X =
      ∑ j, (ε j * B (b j) ⁅X, b i⁆) • T i j := by
    intro i
    have e1 : ιu X * (ιu (b i) * ιu (b i)) - ιu (b i) * ιu (b i) * ιu X =
        ιu ⁅X, b i⁆ * ιu (b i) + ιu (b i) * ιu ⁅X, b i⁆ := by
      rw [LieHom.map_lie, Ring.lie_def]
      noncomm_ring
    rw [e1]
    conv_lhs => rw [eq_sum_of_orthogonal hε horth ⁅X, b i⁆]
    simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      ← Finset.sum_add_distrib, ← smul_add, T]
  have hS : ∑ i, ∑ j, a i j • T i j = 0 := by
    set S := ∑ i, ∑ j, a i j • T i j
    have : S = -S := by
      conv_lhs => rw [show S = ∑ i, ∑ j, a i j • T i j from rfl, Finset.sum_comm]
      simp only [S, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hanti, hT, neg_smul]
    have h2 : (2 : ℝ) • S = 0 := by rw [two_smul]; nth_rewrite 2 [this]; exact add_neg_cancel S
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  simp only [casimir, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    ← Finset.sum_sub_distrib, ← smul_sub]
  calc ∑ i, ε i • (ιu X * (ιu (b i) * ιu (b i)) - ιu (b i) * ιu (b i) * ιu X)
      = ∑ i, ∑ j, a i j • T i j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hcomm, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul]
    _ = 0 := hS
end GroundTheory.Automorphic
