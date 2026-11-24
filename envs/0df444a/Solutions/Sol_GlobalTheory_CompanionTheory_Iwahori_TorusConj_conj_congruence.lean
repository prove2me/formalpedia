-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.TorusConj.conj_congruence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:01:42.091802+00:00
-- url     : https://prove2.me/submissions/7474c0b5-7fa8-4323-a367-9c26c0bf9a03

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusConjugationPreservesCongruence
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_TorusConj_conj_sub_one_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori GlobalTheory.CompanionTheory.Iwahori.TorusConj
namespace GlobalTheory.CompanionTheory.Iwahori.TorusConj
theorem _root_.solution {L E ι : Type} [NormedField L] [Ring E] [Algebra L E] [Fintype ι]
    (wt : ι → ℕ) (P : ι → E) (hP : GlobalTheory.CompanionTheory.Iwahori.IsPieces P) (J : AddSubgroup E)
    (hJ : GlobalTheory.CompanionTheory.Iwahori.IsCongIdeal J P)
    (hc : ∀ c : L, ‖c‖ ≤ 1 → ∀ x ∈ J, c • x ∈ J) (T T' : E) (τ : ι → L)
    (hτ : ∀ i, τ i ≠ 0) (hTT : T * T' = 1) (hTT' : T' * T = 1)
    (hl : ∀ i, T * P i = τ i • P i) (hr : ∀ i, P i * T = τ i • P i)
    (hw : ∀ i j, wt i ≤ wt j → ‖τ i‖ ≤ ‖τ j‖) (a b : E) (ha : a - 1 ∈ J) (hb : b - 1 ∈ J)
    (hU : GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a) (hL : GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b) :
    T * a * T' - 1 ∈ J ∧ T' * b * T - 1 ∈ J := by
  have hl' : ∀ j, T' * P j = (τ j)⁻¹ • P j := by
    intro j
    have e : T' * (T * P j) = T' * (τ j • P j) := by rw [hl]
    rw [← mul_assoc, hTT', one_mul, mul_smul_comm] at e
    rw [eq_inv_smul_iff₀ (hτ j)]
    exact e.symm
  have hr' : ∀ j, P j * T' = (τ j)⁻¹ • P j := by
    intro j
    have e : (P j * T) * T' = (τ j • P j) * T' := by rw [hr]
    rw [mul_assoc, hTT, mul_one, smul_mul_assoc] at e
    rw [eq_inv_smul_iff₀ (hτ j)]
    exact e.symm
  constructor
  · refine conj_sub_one_mem hP hJ hc hr hl' hTT ha fun i j => ?_
    by_cases hij : wt j < wt i
    · exact Or.inr ⟨fun e => by subst e; exact lt_irrefl _ hij, hU i j hij⟩
    · left
      have hn := hw i j (not_lt.mp hij)
      have hpos : 0 < ‖τ j‖ := norm_pos_iff.mpr (hτ j)
      rw [norm_mul, norm_inv, ← div_eq_mul_inv]
      exact (div_le_one hpos).mpr hn
  · refine conj_sub_one_mem hP hJ hc hr' hl hTT' hb fun i j => ?_
    by_cases hij : wt i < wt j
    · exact Or.inr ⟨fun e => by subst e; exact lt_irrefl _ hij, hL i j hij⟩
    · left
      have hn := hw j i (not_lt.mp hij)
      have hpos : 0 < ‖τ i‖ := norm_pos_iff.mpr (hτ i)
      rw [norm_mul, norm_inv, inv_mul_eq_div]
      exact (div_le_one hpos).mpr hn
end GlobalTheory.CompanionTheory.Iwahori.TorusConj
