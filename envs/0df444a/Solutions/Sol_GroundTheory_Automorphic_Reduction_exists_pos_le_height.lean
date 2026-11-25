-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.exists_pos_le_height
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:32:43.34065+00:00
-- url     : https://prove2.me/submissions/4ccc6033-0e54-4cdb-a5bc-1f7693df3460

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionFinite
import Theorems.Thm_GroundTheory_Automorphic_Reduction_exists_finite_forall_mem_integralGL
import Theorems.Thm_GroundTheory_Automorphic_Reduction_adelicNorm_le_of_local
import Theorems.Thm_GroundTheory_Automorphic_Reduction_norm_vecMul_le_of_norm_le
import Theorems.Thm_GroundTheory_Automorphic_Reduction_euclidNorm_vecMul_le
import Theorems.Thm_GroundTheory_Automorphic_Reduction_exists_one_le_bound
import Theorems.Thm_GroundTheory_Automorphic_Reduction_continuous_infAt
import Theorems.Thm_GroundTheory_Automorphic_Reduction_continuous_finAt
import Theorems.Thm_GroundTheory_Automorphic_Reduction_continuous_GL_apply
import Theorems.Thm_GroundTheory_Automorphic_AdelicGLn_diagonal_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_HasFiniteContent_vecMul
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finAt_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finComp_vecMul_GL
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finEval_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_hasFiniteContent_height
import Theorems.Thm_GroundTheory_Automorphic_Reduction_infAt_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_infComp_vecMul_GL
import Theorems.Thm_GroundTheory_Automorphic_Reduction_infEval_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_norm_vecMul_integralGL
import Theorems.Thm_GroundTheory_Automorphic_Reduction_one_le_adelicNorm_ratVec
import Theorems.Thm_GroundTheory_Automorphic_RestrictedProduct_matrixUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_standardOpenSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_unitsToUnits
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.AdelicGLn.diagonal_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.finAt_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.finEval_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.infAt_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.infEval_apply
attribute [local simp] GroundTheory.Automorphic.RestrictedProduct.matrixUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_standardOpenSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_unitsToUnits
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution {C : Set (AdelicGLn.AdelicGL K n)} (hC : IsCompact C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ C, ∀ x : Fin n → K, x ≠ 0 → ε ≤ height g x := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, one_pos, fun g _ x hx => absurd (Subsingleton.elim x 0) hx⟩
  obtain ⟨S, hS⟩ := exists_finite_forall_mem_integralGL hC

  have hinf : ∀ w : InfinitePlace K, ∃ m : ℝ, 1 ≤ m ∧ ∀ g ∈ C, ∀ i j : Fin n,
      ‖((infAt w g)⁻¹ : GL (Fin n) w.Completion) i j‖ ≤ m := fun w => by
    obtain ⟨m, hm1, hm⟩ := exists_one_le_bound hC (f := fun g : AdelicGLn.AdelicGL K n =>
      ∑ i, ∑ j, ‖((infAt w g)⁻¹ : GL (Fin n) w.Completion) i j‖)
      (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        ((continuous_GL_apply i j).comp ((continuous_infAt w).inv)).norm)
    refine ⟨m, hm1, fun g hg i j => le_trans ?_ (hm g hg)⟩
    exact (Finset.single_le_sum (f := fun j => ‖((infAt w g)⁻¹ : GL (Fin n) w.Completion) i j‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖((infAt w g)⁻¹ : GL (Fin n) w.Completion) i j‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  have hfin : ∀ v : HeightOneSpectrum (𝓞 K), ∃ m : ℝ, 1 ≤ m ∧ ∀ g ∈ C, ∀ i j : Fin n,
      ‖((finAt v g)⁻¹ : GL (Fin n) (v.adicCompletion K)) i j‖ ≤ m := fun v => by
    obtain ⟨m, hm1, hm⟩ := exists_one_le_bound hC (f := fun g : AdelicGLn.AdelicGL K n =>
      ∑ i, ∑ j, ‖((finAt v g)⁻¹ : GL (Fin n) (v.adicCompletion K)) i j‖)
      (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        ((continuous_GL_apply i j).comp ((continuous_finAt v).inv)).norm)
    refine ⟨m, hm1, fun g hg i j => le_trans ?_ (hm g hg)⟩
    exact (Finset.single_le_sum (f := fun j => ‖((finAt v g)⁻¹ : GL (Fin n) (v.adicCompletion K)) i j‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖((finAt v g)⁻¹ : GL (Fin n) (v.adicCompletion K)) i j‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  choose a ha1 ha using hinf
  choose b hb1 hb using hfin
  set b' : HeightOneSpectrum (𝓞 K) → ℝ := fun v => if v ∈ S then b v else 1 with hb'
  set P : ℝ := (∏ w, (√n * (n * a w)) ^ w.mult) * ∏ v ∈ S, b' v with hP
  have hPpos : 0 < P := by
    refine mul_pos (Finset.prod_pos fun w _ => pow_pos ?_ _) (Finset.prod_pos fun v _ => ?_)
    · have : (0 : ℝ) < n := Nat.cast_pos.2 hn
      exact mul_pos (Real.sqrt_pos.2 this) (mul_pos this (lt_of_lt_of_le one_pos (ha1 w)))
    · rw [hb']
      dsimp only
      split_ifs
      exact lt_of_lt_of_le one_pos (hb1 v)
  refine ⟨P⁻¹, inv_pos.2 hPpos, fun g hg x hx => ?_⟩
  rw [inv_le_iff_one_le_mul₀' hPpos]
  set y := ratVec x ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K]) with hy
  have hxy : ratVec x = y ᵥ* ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) := by
    rw [hy, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
  refine (one_le_adelicNorm_ratVec hx).trans ?_
  rw [hxy]
  refine (adelicNorm_le_of_local ((hasFiniteContent_height g hx).vecMul g⁻¹)
    (hasFiniteContent_height g hx) (fun w => √n * (n * a w)) b' S (fun w => ?_)
    (fun v hv => by rw [hb']; dsimp only; rw [if_neg hv]) (fun v => ?_)).trans (le_of_eq rfl)
  · rw [infComp_vecMul_GL, show infAt w g⁻¹ = (infAt w g)⁻¹ by simp [infAt, map_inv]]
    exact euclidNorm_vecMul_le (zero_le_one.trans (ha1 w)) (ha w g hg) _
  · rw [finComp_vecMul_GL, show finAt v g⁻¹ = (finAt v g)⁻¹ by
      simp [finAt, map_inv, RestrictedProduct.inv_apply]]
    rw [hb']
    dsimp only
    split_ifs with hv
    · exact norm_vecMul_le_of_norm_le v (zero_le_one.trans (hb1 v)) (hb v g hg) _
    · rw [norm_vecMul_integralGL v (inv_mem (hS g hg v hv)), one_mul]
end GroundTheory.Automorphic.Reduction
