-- Prove2me | solution 1 for GlobalTheory.ExactSeq.sum_neg_one_pow_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:48:16.980852+00:00
-- url     : https://prove2.me/submissions/b641d1b2-e1dd-4092-9a13-d4fcf658e7d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_GlobalTheory_SheafLES_map_id
import Theorems.Thm_GlobalTheory_SheafLES_map_zero_hom
import Theorems.Thm_GlobalTheory_SheafLES_res_id
import Theorems.Thm_GlobalTheory_SheafLES_toAbSheaf_map_hom
import Theorems.Thm_GlobalTheory_SheafLES_toAbSheaf_obj_obj
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
import Theorems.Thm_P2M_GlobalTheory_SheafLES___map_026ec4bafb10
import Theorems.Thm_P2M_GlobalTheory_SheafLES_map___ee3a67e9aebf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SheafLES.map_id
attribute [local simp] GlobalTheory.SheafLES.map_zero_hom
attribute [local simp] GlobalTheory.SheafLES.res_id
attribute [local simp] GlobalTheory.SheafLES.toAbSheaf_map_hom
attribute [local simp] GlobalTheory.SheafLES.toAbSheaf_obj_obj
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply
attribute [local simp] P2M_GlobalTheory_SheafLES___map_026ec4bafb10
attribute [local simp] P2M_GlobalTheory_SheafLES_map___ee3a67e9aebf



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Module
universe t v u
noncomputable section
open GlobalTheory
open GlobalTheory.ExactSeq
variable {k : Type*} [DivisionRing k]
namespace GlobalTheory.ExactSeq
theorem _root_.solution {V : ℕ → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (f : ∀ i, V i →ₗ[k] V (i + 1)) (N : ℕ) (hV : ∀ i < N, Module.Finite k (V i))
    (h : ∀ i < N, Function.Exact (f i) (f (i + 1))) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * finrank k (V i) =
      finrank k (LinearMap.ker (f 0)) - (-1) ^ N * finrank k (LinearMap.ker (f N)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have := hV N N.lt_succ_self
    rw [Finset.sum_range_succ, ih (fun i hi ↦ hV i (by omega)) (fun i hi ↦ h i (by omega)),
      ← (f N).finrank_range_add_finrank_ker, (h N N.lt_succ_self).linearMap_ker_eq]
    push_cast
    ring
end GlobalTheory.ExactSeq
