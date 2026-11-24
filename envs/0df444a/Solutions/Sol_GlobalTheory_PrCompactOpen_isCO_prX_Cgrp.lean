-- Prove2me | solution 1 for GlobalTheory.PrCompactOpen.isCO_prX_Cgrp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:23:17.754397+00:00
-- url     : https://prove2.me/submissions/51d58936-7bae-4f15-9c97-300bdbe190b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralParabolicUnfolding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsCOPrXCgrp
import Theorems.Thm_GlobalTheory_PrCompactOpen_eq_one_of_isCompact
import Theorems.Thm_GlobalTheory_QuotInt_block_left
import Theorems.Thm_GlobalTheory_QuotInt_block_right
import Theorems.Thm_GlobalTheory_QuotInt_continuous_embX
import Theorems.Thm_GlobalTheory_RootEx_Model_conj_mem
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_RootEx_Radical_conj_mem
import Theorems.Thm_GlobalTheory_RootEx_Radical_exists_of_mem_R
import Theorems.Thm_GlobalTheory_RootEx_VolN_exists_of_mem_R
import Theorems.Thm_GlobalTheory_RootEx_VolN_mem_R_iff
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_mul
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_pos
import Theorems.Thm_GlobalTheory_SplitWeil_isLocallyConstant_nabs
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_eq_one_iff
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_mul
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_pos
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_StepData_mem_Cgrp
import Theorems.Thm_GlobalTheory_StepData_mem_prX


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.PrCompactOpen
namespace GlobalTheory.PrCompactOpen
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)
    (J : Subgroup (GL (n ⊕ Fin c) k)) (hJ : IsCO J) (h : GL (n ⊕ Fin c) k) :
    IsCO (prX (Cgrp J h)) ∧ ∀ g ∈ prX (Cgrp J h),
      valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 ∧ deltaR c g = 1 := by
  have := GlobalTheory.SplitWeil.t2Space k
  have key : ∀ F : GL (n ⊕ Fin c) k → GL (n ⊕ Fin c) k, Continuous (fun x => (F x).val) →
      IsClosed {x | GlobalTheory.RootEx.VolN.InR 1 (F x)} := by
    intro F hF
    have e : {x | GlobalTheory.RootEx.VolN.InR 1 (F x)} = ⋂ r, ⋂ s, {x | lev 1 s ≤ lev 1 r →
        (r.isRight ∨ s.isRight) → (F x).val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} := by
      ext x
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, GlobalTheory.RootEx.VolN.InR]
    rw [e]
    exact isClosed_iInter fun r => isClosed_iInter fun s => isClosed_imp isOpen_const
      (isClosed_imp isOpen_const (isClosed_eq (hF.matrix_elem r s) continuous_const))
  have hRcl : IsClosed (R k n c 1 : Set (GL (n ⊕ Fin c) k)) := by
    have e : (R k n c 1 : Set (GL (n ⊕ Fin c) k)) =
        {x | GlobalTheory.RootEx.VolN.InR 1 (id x)} ∩ {x | GlobalTheory.RootEx.VolN.InR 1 x⁻¹} := by
      ext x
      exact GlobalTheory.RootEx.VolN.mem_R_iff
    rw [e]
    exact (key id Units.continuous_val).inter (key (fun x => x⁻¹) Units.continuous_coe_inv)
  have hconj : {x : GL (n ⊕ Fin c) k | h⁻¹ * x * h ∈ J} = (fun y => h * y * h⁻¹) '' (J : Set _) := by
    ext x
    constructor
    · intro hx
      exact ⟨h⁻¹ * x * h, hx, by group⟩
    · rintro ⟨y, hy, rfl⟩
      show h⁻¹ * (h * y * h⁻¹) * h ∈ J
      have e : h⁻¹ * (h * y * h⁻¹) * h = y := by group
      rw [e]
      exact hy
  have hCset : (Cgrp J h : Set (GL (n ⊕ Fin c) k)) =
      {x : GL (n ⊕ Fin c) k | h⁻¹ * x * h ∈ J} ∩ (R k n c 1 : Set _) := by
    ext x
    exact GlobalTheory.StepData.mem_Cgrp.trans and_comm
  have hCc : IsCompact (Cgrp J h : Set (GL (n ⊕ Fin c) k)) := by
    rw [hCset, hconj]
    exact (hJ.2.image ((continuous_const.mul continuous_id).mul continuous_const)).inter_right hRcl
  have hOpen : IsOpen (prX (Cgrp J h) : Set (GL n k)) := by
    apply Subgroup.isOpen_of_mem_nhds
    have hV : IsOpen {g : GL n k | h⁻¹ * embX c g * h ∈ J} :=
      hJ.1.preimage ((continuous_const.mul GlobalTheory.QuotInt.continuous_embX).mul continuous_const)
    have h1V : (1 : GL n k) ∈ {g : GL n k | h⁻¹ * embX c g * h ∈ J} := by
      show h⁻¹ * embX c 1 * h ∈ J
      rw [map_one, mul_one, inv_mul_cancel]
      exact J.one_mem
    refine Filter.mem_of_superset (hV.mem_nhds h1V) ?_
    intro g hg
    refine GlobalTheory.StepData.mem_prX.mpr ⟨1, one_mem _, GlobalTheory.StepData.mem_Cgrp.mpr ⟨?_, ?_⟩⟩
    · rw [one_mul]
      exact Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
    · rw [one_mul]
      exact hg
  have hblk : ∀ {A : GL (n ⊕ Fin c) k → Matrix (n ⊕ Fin c) (n ⊕ Fin c) k}, Continuous A →
      Continuous (fun r => (A r).toBlocks₁₁) :=
    fun hA => continuous_pi fun i => continuous_pi fun j => hA.matrix_elem _ _
  have hΦ : Continuous (fun r : GL (n ⊕ Fin c) k =>
      ((r : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁,
        MulOpposite.op ((r⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁)) :=
    (hblk Units.continuous_val).prodMk (MulOpposite.continuous_op.comp (hblk Units.continuous_coe_inv))
  have himg : Units.embedProduct (Matrix n n k) '' (prX (Cgrp J h) : Set (GL n k)) =
      (fun r : GL (n ⊕ Fin c) k =>
        ((r : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁,
          MulOpposite.op ((r⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁)) ''
        (Cgrp J h : Set (GL (n ⊕ Fin c) k)) := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨u, hu, huC⟩ := GlobalTheory.StepData.mem_prX.mp hg
      refine ⟨u * embX c g, huC, ?_⟩
      have hinv : (u * embX c g)⁻¹ = embX c g⁻¹ * u⁻¹ := by rw [_root_.mul_inv_rev, map_inv]
      simp only [hinv, GlobalTheory.QuotInt.block_right g hu, GlobalTheory.QuotInt.block_left g⁻¹ (inv_mem hu),
        Units.embedProduct_apply]
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨hrR, -⟩ := GlobalTheory.StepData.mem_Cgrp.mp hr
      obtain ⟨x, u, hu, rfl⟩ := GlobalTheory.RootEx.Radical.exists_of_mem_R hrR
      refine ⟨x, GlobalTheory.StepData.mem_prX.mpr ⟨embX c x * u * (embX c x)⁻¹,
        GlobalTheory.RootEx.Radical.conj_mem x hu, by rwa [inv_mul_cancel_right]⟩, ?_⟩
      have hinv : (embX c x * u)⁻¹ = u⁻¹ * embX c x⁻¹ := by rw [_root_.mul_inv_rev, map_inv]
      simp only [hinv, GlobalTheory.QuotInt.block_left x hu, GlobalTheory.QuotInt.block_right x⁻¹ (inv_mem hu),
        Units.embedProduct_apply]
  have hcpt : IsCompact (prX (Cgrp J h) : Set (GL n k)) := by
    rw [Units.isEmbedding_embedProduct.isCompact_iff, himg]
    exact hCc.image hΦ
  refine ⟨⟨hOpen, hcpt⟩, fun g hg => ?_⟩
  have hdet : Continuous (fun g : GL n k => Matrix.GeneralLinearGroup.det g) := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · have e : (Units.val ∘ fun g : GL n k => Matrix.GeneralLinearGroup.det g) =
          fun g : GL n k => (g : Matrix n n k).det := by
        funext g
        exact Matrix.GeneralLinearGroup.val_det_apply g
      rw [e]
      exact Units.continuous_val.matrix_det
    · have e : (fun g : GL n k => ((Matrix.GeneralLinearGroup.det g)⁻¹ : kˣ).val) =
          fun g : GL n k => ((g⁻¹ : GL n k) : Matrix n n k).det := by
        funext g
        rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
      rw [e]
      exact Units.continuous_coe_inv.matrix_det
  have h1 := eq_one_of_isCompact (fun g : GL n k => nabs k (Matrix.GeneralLinearGroup.det g))
    ((GlobalTheory.SplitWeil.isLocallyConstant_nabs k).continuous.comp hdet)
    (fun x y => by
      simp only [map_mul]
      exact GlobalTheory.SplitWeil.nabs_mul k _ _)
    (fun x => GlobalTheory.SplitWeil.nabs_pos k _) hcpt hg
  refine ⟨(GlobalTheory.SplitWeil.nabs_eq_one_iff _).mp h1, ?_⟩
  show nabs k (Matrix.GeneralLinearGroup.det g) ^ ((c : ℤ) - 1) = 1
  rw [h1, _root_.one_zpow]
end GlobalTheory.PrCompactOpen
