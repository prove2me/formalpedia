-- Prove2me | solution 1 for GlobalTheory.SmGL.LeviInt.levi_integral_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:49:45.402207+00:00
-- url     : https://prove2.me/submissions/1b30d42b-192a-48d2-bb31-0c79a23ca8d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviIntegralFacts
import Theorems.Thm_GlobalTheory_SmGL_LeviInt_nabs_det_eq_one
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_exists_iwasawa
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_isLocallyConstant_modulus
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_unip_mul_levi_mem_KO
import Theorems.Thm_GlobalTheory_SmGL_exists_levi_mul_unip
import Theorems.Thm_GlobalTheory_SmGL_mem_unipRad
import Theorems.Thm_GlobalTheory_SmGL_unipRad_le_parab
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open scoped ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.LeviInt
open MeasureTheory Topology
open scoped ENNReal
namespace GlobalTheory.SmGL.LeviInt
namespace _root_.GlobalTheory.SmGL.LeviInt
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n), (∀ (g : _root_.GlobalTheory.SmGL.Levi k m) (u : GL n k), u ∈ _root_.GlobalTheory.SmGL.unipRad k e → (_root_.GlobalTheory.SmGL.leviEmb k e g * u ∈ _root_.GlobalTheory.SplitWeil.KO k n ↔ (∀ a, g a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a)) ∧ u ∈ _root_.GlobalTheory.SplitWeil.KO k n)) ∧ (∀ p : _root_.GlobalTheory.SmGL.parab k e, (p : GL n k) ∈ _root_.GlobalTheory.SplitWeil.KO k n → ∀ a, _root_.GlobalTheory.SmGL.leviProj k e p a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a)) ∧ (∀ g : _root_.GlobalTheory.SmGL.Levi k m, (∀ a, g a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a)) → _root_.GlobalTheory.SmGL.modulus k m g = 1) ∧ (∀ g h : _root_.GlobalTheory.SmGL.Levi k m, _root_.GlobalTheory.SmGL.modulus k m (g * h) = _root_.GlobalTheory.SmGL.modulus k m g * _root_.GlobalTheory.SmGL.modulus k m h) ∧ Continuous (_root_.GlobalTheory.SmGL.modulus k m) ∧ Continuous (_root_.GlobalTheory.SmGL.leviProj k e) ∧ IsClosed (_root_.GlobalTheory.SmGL.parab k e : Set (GL n k)) ∧ IsClosed (_root_.GlobalTheory.SmGL.unipRad k e : Set (GL n k)) ∧ ∀ g : GL n k, ∃ p ∈ _root_.GlobalTheory.SmGL.parab k e, ∃ x ∈ _root_.GlobalTheory.SplitWeil.KO k n, g = p * x := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e
  have hT2 : T2Space k := (_root_.GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)).2
  have hlevi : ∀ (g : _root_.GlobalTheory.SmGL.Levi k m) (u : GL n k), u ∈ _root_.GlobalTheory.SmGL.unipRad k e →
      (_root_.GlobalTheory.SmGL.leviEmb k e g * u ∈ _root_.GlobalTheory.SplitWeil.KO k n ↔
        (∀ a, g a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a)) ∧
          u ∈ _root_.GlobalTheory.SplitWeil.KO k n) := by
    intro g u hu
    rw [← Subgroup.inv_mem_iff, mul_inv_rev, ← map_inv]
    refine (_root_.GlobalTheory.SmGL.UnitInd.unip_mul_levi_mem_KO e ⟨u⁻¹, inv_mem hu⟩ g⁻¹).trans ?_
    have hinv : ∀ a, (g⁻¹) a = (g a)⁻¹ := fun a => rfl
    simp only [hinv, Subgroup.inv_mem_iff]
    exact and_comm
  have hproj : ∀ p : _root_.GlobalTheory.SmGL.parab k e,
      (p : GL n k) ∈ _root_.GlobalTheory.SplitWeil.KO k n →
        ∀ a, _root_.GlobalTheory.SmGL.leviProj k e p a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a) := by
    intro p hp a
    obtain ⟨u, hu, hpu⟩ := _root_.GlobalTheory.SmGL.exists_levi_mul_unip k e p
    rw [hpu] at hp
    exact ((hlevi _ u hu).1 hp).1 a
  have hmod : ∀ g : _root_.GlobalTheory.SmGL.Levi k m,
      (∀ a, g a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a)) → _root_.GlobalTheory.SmGL.modulus k m g = 1 := by
    intro g hg
    unfold _root_.GlobalTheory.SmGL.modulus
    exact Finset.prod_eq_one fun a _ => by
      rw [_root_.GlobalTheory.SmGL.LeviInt.nabs_det_eq_one (hg a), one_zpow]
  have hmul : ∀ g h : _root_.GlobalTheory.SmGL.Levi k m,
      _root_.GlobalTheory.SmGL.modulus k m (g * h) = _root_.GlobalTheory.SmGL.modulus k m g * _root_.GlobalTheory.SmGL.modulus k m h := by
    intro g h
    unfold _root_.GlobalTheory.SmGL.modulus
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← mul_zpow, ← _root_.GlobalTheory.SmGL.nabs_mul', ← map_mul]
    rfl
  have hcont : Continuous (_root_.GlobalTheory.SmGL.leviProj k e) := by
    refine continuous_pi fun a => Units.continuous_iff.2 ⟨?_, ?_⟩
    · refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Function.comp_apply, _root_.GlobalTheory.SmGL.leviProj_apply]
      exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _
    · have hinv : ∀ p : _root_.GlobalTheory.SmGL.parab k e,
          (_root_.GlobalTheory.SmGL.leviProj k e p a)⁻¹ = _root_.GlobalTheory.SmGL.leviProj k e p⁻¹ a := by
        intro p
        rw [map_inv]
        rfl
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [hinv, _root_.GlobalTheory.SmGL.leviProj_apply, Subgroup.coe_inv]
      exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_elem _ _
  have hP : IsClosed (_root_.GlobalTheory.SmGL.parab k e : Set (GL n k)) := by
    have hset : (_root_.GlobalTheory.SmGL.parab k e : Set (GL n k)) =
        ⋂ (a) (b) (i : m a) (j : m b) (_ : b < a),
          {g : GL n k | (g : Matrix n n k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0} := by
      ext g
      rw [SetLike.mem_coe, _root_.GlobalTheory.SmGL.mem_parab_iff]
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rw [hset]
    exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun i =>
      isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_eq (Units.continuous_val.matrix_elem _ _) continuous_const
  have hN : IsClosed (_root_.GlobalTheory.SmGL.unipRad k e : Set (GL n k)) := by
    have hset : (_root_.GlobalTheory.SmGL.unipRad k e : Set (GL n k)) =
        (_root_.GlobalTheory.SmGL.parab k e : Set (GL n k)) ∩
          ⋂ (a) (i : m a) (j : m a), {g : GL n k |
            (g : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) k) i j} := by
      ext g
      rw [SetLike.mem_coe, _root_.GlobalTheory.SmGL.mem_unipRad]
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe]
    rw [hset]
    exact hP.inter (isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (Units.continuous_val.matrix_elem _ _) continuous_const)
  refine ⟨hlevi, hproj, hmod, hmul, _root_.GlobalTheory.SmGL.UnitInd.isLocallyConstant_modulus.continuous, hcont,
    hP, hN, fun g => ?_⟩
  obtain ⟨u, h, w, hw, rfl⟩ := _root_.GlobalTheory.SmGL.UnitInd.exists_iwasawa e g
  exact ⟨_, mul_mem (_root_.GlobalTheory.SmGL.unipRad_le_parab k e u.2)
    (_root_.GlobalTheory.SmGL.leviEmb_mem_parab k e h), w, hw, rfl⟩
end _root_.GlobalTheory.SmGL.LeviInt
end GlobalTheory.SmGL.LeviInt
