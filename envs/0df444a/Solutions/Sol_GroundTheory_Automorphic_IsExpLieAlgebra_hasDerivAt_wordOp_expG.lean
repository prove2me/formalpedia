-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.hasDerivAt_wordOp_expG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:37:34.414299+00:00
-- url     : https://prove2.me/submissions/b3db9f02-73c4-4664-95a5-9262f2740bdf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_ContinuousMultilinearOfFiniteDimensional
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_isSmoothVector_wordOp
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_wordOp_map
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_exists_wordOp_cml
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivOp_wordOp
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_sum_wordOp_update
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_hasDerivAt_expG_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_expG_smul_inv
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_hasDerivAt_Ad_expG
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_5d0ada4687d5
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_af7e43e2c7fe
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
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_5d0ada4687d5
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_af7e43e2c7fe
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology Asymptotics
open scoped ContDiff
open GroundTheory.Automorphic.IsExpLieAlgebra
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution (hπ : ∀ g, ‖π g‖ ≤ 1) {v : E} (hv : h.IsSmoothVector π v)
    (X : 𝔤) {k : ℕ} (Y : Fin k → 𝔤) :
    HasDerivAt (fun t : ℝ => h.wordOp π Y (π (h.expG (t • X)) v))
      (h.wordOp π Y (h.derivOp π X v)) 0 := by
  obtain ⟨Φ, hΦ⟩ := h.exists_wordOp_cml π hv k
  set c : ℝ → (Fin k → 𝔤) := fun t i => h.Ad (h.expG (-(t • X))) (Y i) with hcdef
  have hfun : (fun t : ℝ => h.wordOp π Y (π (h.expG (t • X)) v)) =
      fun t => π (h.expG (t • X)) (Φ (c t)) := by
    funext t
    rw [h.wordOp_map π hv, hΦ, h.expG_smul_inv]
  have hc0 : c 0 = Y := by
    funext i
    simp [hcdef]
  have hcd : HasDerivAt c (fun i => -(h.bracket X (Y i))) 0 := by
    rw [hasDerivAt_pi]
    intro i
    have := (h.hasDerivAt_Ad_expG X (Y i)).scomp_of_eq 0 (hasDerivAt_neg (0 : ℝ)) (by simp)
    simpa [hcdef, Function.comp_def] using this
  have hΦc : HasDerivAt (fun t => Φ (c t))
      (∑ i, Φ (Function.update Y i (-(h.bracket X (Y i))))) 0 := by
    let _inst : NormedSpace ℝ (Fin k → 𝔤) := Pi.normedSpace
    have hF := Φ.hasFDerivAt (c 0)
    have := hF.comp_hasDerivAt (𝕜 := ℝ) (0 : ℝ) hcd
    rw [hc0, ContinuousMultilinearMap.linearDeriv_apply] at this
    exact this
  have hsum : ∑ i, Φ (Function.update Y i (-(h.bracket X (Y i)))) = -h.brSum π X Y v := by
    rw [← h.sum_wordOp_update π hv X Y, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hΦ, ← neg_one_smul ℝ (h.bracket X (Y i)), Φ.map_update_smul, neg_one_smul]
  have hw0 : h.IsSmoothVector π (Φ (c 0)) := by
    rw [hc0, hΦ]; exact h.isSmoothVector_wordOp π hv Y
  have hP := h.hasDerivAt_expG_apply π hπ hΦc hw0 X
  rw [hfun]
  convert hP using 1
  rw [hsum, hc0, hΦ, h.derivOp_wordOp π hv X Y]
  abel
end GroundTheory.Automorphic.IsExpLieAlgebra
