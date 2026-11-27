-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Orbit.isLocalRing_of_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:35:43.936509+00:00
-- url     : https://prove2.me/submissions/e4389fcc-f21e-407d-8b55-67096665b5fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_exists_idempotent_henselian
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_exists_pow_mem_map_maximalIdeal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_finite_maximal_ideals_of_finite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_isAdicComplete_finite_algebra


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma Polynomial IsLocalRing ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
namespace GlobalTheory.UnitLemma.Orbit
theorem _root_.solution {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (S : Type*) [CommRing S] [Nontrivial S] [Algebra R S]
    [Module.Finite R S] (hid : ∀ e : S, e * e = e → e = 0 ∨ e = 1) : IsLocalRing S := by
  classical
  by_contra hloc
  obtain ⟨M1, hM1⟩ := Ideal.exists_maximal S
  have hex : ∃ M2 : Ideal S, M2.IsMaximal ∧ M2 ≠ M1 := by
    by_contra h
    push Not at h
    exact hloc (IsLocalRing.of_unique_max_ideal ⟨M1, hM1, fun M hM => h M hM⟩)
  obtain ⟨M2, hM2, h12⟩ := hex
  set F := (finite_maximal_ideals_of_finite (R := R) S).toFinset.filter (· ≠ M1) with hF
  have hmemF : ∀ N : Ideal S, N.IsMaximal → N ≠ M1 → N ∈ F := by
    intro N hN hN1
    rw [hF, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨hN, hN1⟩
  have hcop : M1 ⊔ F.inf id = ⊤ := by
    by_contra hne
    have hle : F.inf id ≤ M1 := by
      rw [hM1.eq_of_le hne le_sup_left]; exact le_sup_right
    obtain ⟨N, hN, hNle⟩ := (hM1.isPrime.inf_le').1 hle
    rw [hF, Finset.mem_filter, Set.Finite.mem_toFinset] at hN
    exact hN.2 ((hN.1 : N.IsMaximal).eq_of_le hM1.ne_top hNle)
  have h1 : (1 : S) ∈ M1 ⊔ F.inf id := by rw [hcop]; exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
  have hx1 : ∀ N : Ideal S, N.IsMaximal → N ≠ M1 → x - 1 ∈ N := by
    intro N hN hN1
    have : y ∈ N := Finset.inf_le (f := id) (hmemF N hN hN1) hy
    have : x - 1 = -y := by rw [← hxy]; ring
    rw [this]; exact N.neg_mem (by assumption)
  have hall : ∀ N : Ideal S, N.IsMaximal → x * x - x ∈ N := by
    intro N hN
    by_cases hN1 : N = M1
    · subst hN1; exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hx) hx
    · have := hx1 N hN hN1
      have e : x * x - x = x * (x - 1) := by ring
      rw [e]; exact Ideal.mul_mem_left _ _ this
  obtain ⟨k, hk, hkJ⟩ := exists_pow_mem_map_maximalIdeal (R := R) S _ hall
  have : IsAdicComplete ((maximalIdeal R).map (algebraMap R S)) S := isAdicComplete_finite_algebra S
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  obtain ⟨e, s, hee, hes⟩ := exists_idempotent_henselian ((maximalIdeal R).map (algebraMap R S)) x k' hkJ
  have hxx1 : x * x - x ∈ M1 := hall M1 hM1
  have hxx2 : x * x - x ∈ M2 := hall M2 hM2
  rcases hid e hee with h0 | h0
  · apply hM2.ne_top
    rw [Ideal.eq_top_iff_one]
    have ha : -x ∈ M2 := by
      have : -x = s * (x * x - x) := by rw [← hes, h0]; ring
      rw [this]; exact Ideal.mul_mem_left _ _ hxx2
    have hb := hx1 M2 hM2 h12
    have : (1 : S) = -(x - 1) + -(-x) := by ring
    rw [this]; exact M2.add_mem (M2.neg_mem hb) (M2.neg_mem ha)
  · apply hM1.ne_top
    rw [Ideal.eq_top_iff_one]
    have : (1 : S) = s * (x * x - x) + x := by rw [← hes, h0]; ring
    rw [this]; exact M1.add_mem (Ideal.mul_mem_left _ _ hxx1) hx
end GlobalTheory.UnitLemma.Orbit
