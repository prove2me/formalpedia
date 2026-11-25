-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.coe_norm_eq_of_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:10:47.847422+00:00
-- url     : https://prove2.me/submissions/7ba1e49a-f71e-4e22-a75f-e245f7f06225

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_NormFormula
import Theorems.Thm_GroundTheory_LocalField_Abstract_coe_norm
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk



set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution {K S Q J : Subgroup G} (hQK : Q ≤ K)
    (hmul : ∀ k ∈ K, ∃ q ∈ Q, q⁻¹ * k ∈ S) (hJ : ∀ q ∈ Q, q ∈ S ↔ q ∈ J)
    [(S.subgroupOf K).FiniteIndex] [(J.subgroupOf Q).FiniteIndex] (a : fixedModule A S)
    (ha : (a : A) ∈ fixedModule A J) :
    (norm A K S a : A) = norm A Q J ⟨a, ha⟩ := by
  let f : Q ⧸ J.subgroupOf Q → K ⧸ S.subgroupOf K :=
    Quotient.map' (fun q : Q => (⟨q, hQK q.2⟩ : K)) fun q q' h => by
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at h ⊢
      have hq : ((q⁻¹ * q' : Q) : G) ∈ Q := (q⁻¹ * q').2
      simpa using (hJ _ hq).2 h
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      induction x using QuotientGroup.induction_on with
      | H q =>
      induction y using QuotientGroup.induction_on with
      | H q' =>
        have h' : ((⟨q, hQK q.2⟩ : K) : K ⧸ S.subgroupOf K) = ((⟨q', hQK q'.2⟩ : K) : K ⧸ _) := hxy
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h'
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have hq : ((q⁻¹ * q' : Q) : G) ∈ Q := (q⁻¹ * q').2
        exact (hJ _ hq).1 (by simpa using h')
    · intro y
      induction y using QuotientGroup.induction_on with
      | H k =>
        obtain ⟨q, hq, hqk⟩ := hmul k k.2
        refine ⟨((⟨q, hq⟩ : Q) : Q ⧸ J.subgroupOf Q), ?_⟩
        show ((⟨q, hQK hq⟩ : K) : K ⧸ S.subgroupOf K) = _
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa using hqk
  rw [coe_norm, coe_norm, ← finprod_comp_equiv (Equiv.ofBijective f hf)]
  congr 1
  funext x
  induction x using QuotientGroup.induction_on with
  | H q => rfl
end GroundTheory.LocalField.Abstract
