-- Prove2me | solution 1 for GlobalTheory.CohenRegular.exists_coefficientField_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:35.1158+00:00
-- url     : https://prove2.me/submissions/7409c089-6da0-4e7d-93c7-9394eba245aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CohenStructureFiniteOverNormalCompleteSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCoefficientFieldOfCharZero
import Theorems.Thm_GlobalTheory_CoeffSubring_dvd_of_forall_sub_mul_mem
import Theorems.Thm_GlobalTheory_CoeffSubring_exists_iInf_sub_mem
import Theorems.Thm_GlobalTheory_CoeffSubring_exists_level_sub_mem
import Theorems.Thm_GlobalTheory_CoeffSubring_exists_sub_mul_mem
import Theorems.Thm_GlobalTheory_PBasis_exists_pBasis
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CohenRegular
namespace GlobalTheory.CohenRegular
theorem _root_.solution (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [IsAdicComplete (maximalIdeal S) S] {p : ℕ} (hp : p.Prime) (hp0 : (p : S) = 0) :
    ∃ Λ : Subring S, IsField Λ ∧ ∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S := by
  have h0 : (p : S) ∈ maximalIdeal S := by rw [hp0]; exact zero_mem _
  obtain ⟨B, hB, hB'⟩ := GlobalTheory.PBasis.exists_pBasis (ResidueField S) p hp
    (by rw [← map_natCast (residue S), residue_eq_zero_iff]; exact h0)
  choose l hl using residue_surjective (R := S)
  have hL : residue S '' (l '' B) = B := by simp [Set.image_image, hl]
  have hinj : Set.InjOn (residue S) (l '' B) := by
    rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ h
    rw [hl, hl] at h
    rw [h]
  rw [← hL] at hB hB'
  have hs := CoeffSubring.exists_level_sub_mem hp h0 hB
  have h1 := CoeffSubring.exists_iInf_sub_mem h0 hs
  set Λ : Subring S := ⨅ n, CoeffSubring.level p (l '' B) n
  have h2 : ∀ a ∈ Λ, a ∈ maximalIdeal S → a = 0 := fun a ha hm => by
    rw [← zero_dvd_iff, ← hp0]
    refine CoeffSubring.dvd_of_forall_sub_mul_mem fun n => ?_
    obtain ⟨t, -, ht⟩ :=
      CoeffSubring.exists_sub_mul_mem hp h0 hinj hB' hs n (Subring.mem_iInf.1 ha n) hm
    exact ⟨t, Ideal.pow_le_pow_right n.le_succ ht⟩
  refine ⟨Λ, ⟨exists_pair_ne _, mul_comm, fun {x} hx => ?_⟩, h1⟩
  have hu : IsUnit (x : S) := by
    by_contra h
    exact hx (Subtype.ext (h2 _ x.2 h))
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  obtain ⟨a, ha, hya⟩ := h1 y
  refine ⟨⟨a, ha⟩, Subtype.ext (sub_eq_zero.1 (h2 _ (Λ.sub_mem (Λ.mul_mem x.2 ha) Λ.one_mem) ?_))⟩
  have : (x : S) * a - 1 = -x * (y - a) := by rw [← hy]; ring
  show (x : S) * a - 1 ∈ _
  rw [this]
  exact Ideal.mul_mem_left _ _ hya
end GlobalTheory.CohenRegular
