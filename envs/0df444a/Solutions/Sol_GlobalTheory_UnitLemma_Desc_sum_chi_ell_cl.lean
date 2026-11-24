-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.sum_chi_ell_cl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:00:09.377466+00:00
-- url     : https://prove2.me/submissions/9e4969d4-7263-4fb8-b6af-4b9b6ee4bc2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartFramePropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartOrthogonalityClasse
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_sum_powerset_neg_one_pow_inter
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_sum_chi_mul_chi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma Polynomial Filter Topology
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι] (e π : ι → B.A)
    (S : Finset ι), IsFrame B e π S → Finite B.Cl → ∀ (ℓ : B.A → ℝ) (h : Finset ι → ℝ),
    (∀ I ⊆ S, ∀ x, B.Plus x → ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ ((∏ j ∈ J, π j) * x) =
      (chi B e I x : ℝ) * h I) →
    ∀ I ⊆ S, ∑ᶠ k : B.Cl, (chi B e I k.rep : ℝ) * ℓ k.rep = (Nat.card B.Cl : ℝ) / 2 ^ S.card * h I := by
  intro K B ι _ _ e π S hF hfin ℓ h hyp I₀ h₀
  haveI := Fintype.ofFinite B.Cl
  have inv : ∀ x, B.Plus x → (2 : ℝ) ^ S.card * ℓ x = ∑ I ∈ S.powerset, (chi B e I x : ℝ) * h I := by
    intro x hx
    calc (2 : ℝ) ^ S.card * ℓ x
        = ∑ J ∈ S.powerset, (∑ I ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card) * ℓ ((∏ j ∈ J, π j) * x) := by
          rw [Finset.sum_eq_single ∅]
          · simp [sum_powerset_neg_one_pow_inter S ∅ (Finset.empty_subset _)]
          · intro J hJ hJe
            rw [sum_powerset_neg_one_pow_inter S J (Finset.mem_powerset.1 hJ), if_neg hJe, zero_mul]
          · intro hn; exact absurd (Finset.empty_mem_powerset S) hn
      _ = ∑ I ∈ S.powerset, ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ ((∏ j ∈ J, π j) * x) := by
          simp_rw [Finset.sum_mul]; exact Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun I hI => hyp I (Finset.mem_powerset.1 hI) x hx
  have hplus : ∀ k : B.Cl, B.Plus k.rep := fun k => ⟨(Quot.out k).1.isUnit, (Quot.out k).2⟩
  have e1 : ∀ k : B.Cl, ℓ k.rep = ((2 : ℝ) ^ S.card)⁻¹ * ∑ I ∈ S.powerset, (chi B e I k.rep : ℝ) * h I := by
    intro k; rw [← inv _ (hplus k), ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have orth : ∀ I ∈ S.powerset, ∑ k : B.Cl, (chi B e I₀ k.rep : ℝ) * (chi B e I k.rep : ℝ) =
      if I = I₀ then (Fintype.card B.Cl : ℝ) else 0 := by
    intro I hI
    have := sum_chi_mul_chi B e π S hF I₀ I h₀ (Finset.mem_powerset.1 hI)
    split_ifs at this ⊢ <;> exact_mod_cast this
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  simp_rw [e1]
  calc ∑ k : B.Cl, (chi B e I₀ k.rep : ℝ) * (((2 : ℝ) ^ S.card)⁻¹ * ∑ I ∈ S.powerset, (chi B e I k.rep : ℝ) * h I)
      = ((2 : ℝ) ^ S.card)⁻¹ * ∑ I ∈ S.powerset, h I * ∑ k : B.Cl, (chi B e I₀ k.rep : ℝ) * (chi B e I k.rep : ℝ) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun k _ => by ring
    _ = ((2 : ℝ) ^ S.card)⁻¹ * ∑ I ∈ S.powerset, h I * (if I = I₀ then (Fintype.card B.Cl : ℝ) else 0) := by
        rw [Finset.sum_congr rfl fun I hI => by rw [orth I hI]]
    _ = (Fintype.card B.Cl : ℝ) / 2 ^ S.card * h I₀ := by
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_powerset.2 h₀, if_true]
        ring
end GlobalTheory.UnitLemma.Desc
