-- Prove2me | solution 1 for GlobalTheory.InertZeta.cosetIntegral_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:27:17.955173+00:00
-- url     : https://prove2.me/submissions/e4ff01b8-ba4e-40ef-8028-440c66599ea9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralRightInvariantEqSumOpenSubgroupCosets
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_HasLen_unique
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
import Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid



set_option autoImplicit false
open GlobalTheory.InertZeta
open MeasureTheory Pointwise
open GlobalTheory GlobalTheory.InertZeta
namespace GlobalTheory.InertZeta
theorem _root_.solution : CosetIntegral := by
  intro G _ _ _ _ _ μ _ K hK hμK F Z hF hZ
  classical
  set f : G ⧸ K → ℂ := fun x => F x.out with hf
  let A : G ⧸ K → Set G := fun x => QuotientGroup.mk ⁻¹' {x}
  have hA : ∀ x, A x = x.out • (K : Set G) := by
    intro x; ext g
    simp only [A, Set.mem_preimage, Set.mem_singleton_iff, mem_leftCoset_iff]
    conv_lhs => rw [← QuotientGroup.out_eq' x]
    rw [eq_comm, QuotientGroup.eq]
    rfl
  have hAm : ∀ x, MeasurableSet (A x) := fun x => by
    rw [hA]; exact (hK.smul x.out).measurableSet
  have hAμ : ∀ x, μ (A x) = 1 := fun x => by rw [hA, measure_smul]; exact hμK
  have hconst : ∀ x, ∀ g ∈ A x, F g = f x := by
    intro x g hg
    rw [hA, mem_leftCoset_iff] at hg
    have := hF x.out _ hg
    rwa [mul_inv_cancel_left] at this
  have hself : ∀ g : G, g ∈ A (QuotientGroup.mk g) := fun g => rfl
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro x y hxy
    exact (Set.disjoint_singleton.mpr hxy).preimage _
  set S := Function.support f with hSdef
  have hS : S.Countable := hZ.summable.countable_support
  haveI : Countable S := hS.to_subtype
  let B : S → Set G := fun i => A i.1
  have hBint : ∀ i : S, ∫ g in B i, F g ∂μ = f i.1 := by
    intro i
    rw [setIntegral_congr_fun (hAm i.1) (fun g hg => hconst i.1 g hg), setIntegral_const]
    simp [Measure.real, hAμ]
  have hBnorm : ∀ i : S, ∫ g in B i, ‖F g‖ ∂μ = ‖f i.1‖ := by
    intro i
    rw [setIntegral_congr_fun (g := fun _ => ‖f i.1‖) (hAm i.1) (fun g hg => by simp only [hconst i.1 g hg]), setIntegral_const]
    simp [Measure.real, hAμ]
  have hBon : ∀ i : S, IntegrableOn F (B i) μ := by
    intro i
    have h1 : IntegrableOn (fun _ : G => f i.1) (B i) μ :=
      integrableOn_const (by simp [B, hAμ]) (by simp)
    exact h1.congr_fun (fun g hg => (hconst i.1 g hg).symm) (hAm i.1)
  have hsumm : Summable fun i : S => ∫ g in B i, ‖F g‖ ∂μ := by
    simp only [hBnorm]
    exact (summable_norm_iff.mpr hZ.summable).subtype S
  have hU : IntegrableOn F (Set.iUnion B) μ :=
    integrableOn_iUnion_of_summable_integral_norm hBon hsumm
  have hzero : ∀ g ∉ Set.iUnion B, F g = 0 := by
    intro g hg
    have hnot : (QuotientGroup.mk g : G ⧸ K) ∉ S := by
      intro hm
      exact hg (Set.mem_iUnion.mpr ⟨⟨_, hm⟩, hself g⟩)
    rw [hconst _ g (hself g)]
    simpa [hSdef] using hnot
  have hInt : Integrable F μ := hU.integrable_of_forall_notMem_eq_zero hzero
  refine ⟨hInt, ?_⟩
  have h1 := hasSum_integral_iUnion (fun i : S => hAm i.1) (fun i j hij => hdisj (fun h => hij (Subtype.ext h))) hU
  have hfun : (fun i : S => ∫ g in B i, F g ∂μ) = fun i => f i.1 := funext hBint
  rw [hfun] at h1
  have h2 : HasSum (fun i : S => f i.1) Z :=
    (hasSum_subtype_iff_of_support_subset (s := S) subset_rfl).mpr hZ
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  exact h1.unique h2
end GlobalTheory.InertZeta
