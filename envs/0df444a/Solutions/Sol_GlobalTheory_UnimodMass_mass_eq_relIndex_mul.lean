-- Prove2me | solution 1 for GlobalTheory.UnimodMass.mass_eq_relIndex_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:41:48.658958+00:00
-- url     : https://prove2.me/submissions/c8319aa7-cb87-444e-a3c8-4c7d8fdf64ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteDcOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DoubleCosetMassEqRelIndexMulMass
import Theorems.Thm_GlobalTheory_UnimodMass_dcOfCoset_mk
import Theorems.Thm_GlobalTheory_UnimodMass_fiber_card_mul_stabCard
import Theorems.Thm_GlobalTheory_UnimodMass_dcOfCoset_surj
import Theorems.Thm_GlobalTheory_UnimodMass_dcMapLe_dcOfCoset
import Theorems.Thm_GlobalTheory_UnimodMass_finite_dc_of_le
import Theorems.Thm_GlobalTheory_UnimodMass_stabCard_out
import Theorems.Thm_GlobalTheory_UnimodMass_stabCard_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnimodMass
open scoped BigOperators
namespace GlobalTheory.UnimodMass
theorem _root_.solution {G : Type} [Group G] (Γ W K : Subgroup G) (hWK : W ≤ K)
    (hW : Finite (DC Γ W)) (hfin : ∀ t : G, Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) :
    W.relIndex K ≠ 0 ∧ mass Γ W = (W.relIndex K : ℚ) * mass Γ K := by
  classical
  haveI := hW
  haveI : Finite (DC Γ K) := finite_dc_of_le hWK

  have hfibre : ∀ d : DC Γ W, Finite {x : K ⧸ W.subgroupOf K // dcOfCoset Γ W K 1 x = d} := by
    intro d
    by_cases hne : ∃ x : K ⧸ W.subgroupOf K, dcOfCoset Γ W K 1 x = d
    · obtain ⟨x, rfl⟩ := hne
      induction x using QuotientGroup.induction_on with
      | H k =>
        have h1 := fiber_card_mul_stabCard Γ W K hWK 1 (hfin 1) k
        have h2 := stabCard_pos (Γ := Γ) (K := K) 1 (hfin 1)
        have h3 : 0 < Nat.card {x : K ⧸ W.subgroupOf K //
            dcOfCoset Γ W K 1 x = dcOfCoset Γ W K 1 (k : K ⧸ W.subgroupOf K)} := by
          rcases Nat.eq_zero_or_pos (Nat.card {x : K ⧸ W.subgroupOf K //
            dcOfCoset Γ W K 1 x = dcOfCoset Γ W K 1 (k : K ⧸ W.subgroupOf K)}) with h | h
          · rw [h, zero_mul] at h1; omega
          · exact h
        exact (Nat.card_pos_iff.1 h3).2
    · push_neg at hne
      exact Finite.of_injective (β := Empty) (fun x => (hne x.1 x.2).elim) (fun x => (hne x.1 x.2).elim)
  haveI : Finite (K ⧸ W.subgroupOf K) :=
    Finite.of_equiv _ (Equiv.sigmaFiberEquiv (dcOfCoset Γ W K 1))
  have hidx : W.relIndex K = Nat.card (K ⧸ W.subgroupOf K) := rfl
  have hne0 : W.relIndex K ≠ 0 := by
    rw [hidx]; exact Nat.card_ne_zero.2 ⟨⟨(1 : K)⟩, inferInstance⟩
  refine ⟨hne0, ?_⟩
  haveI := Fintype.ofFinite (DC Γ W)
  haveI := Fintype.ofFinite (DC Γ K)
  haveI := Fintype.ofFinite (K ⧸ W.subgroupOf K)

  have hfib : ∀ c : DC Γ K,
      ∑ d ∈ Finset.univ.filter (fun d => dcMapLe hWK d = c), ((stabCard Γ W d.out : ℕ) : ℚ)⁻¹ =
        (W.relIndex K : ℚ) * ((stabCard Γ K c.out : ℕ) : ℚ)⁻¹ := by
    intro c
    set t := c.out with htdef
    have hct : c = Quotient.mk (dcSetoid Γ K) t := (Quotient.out_eq c).symm
    have hsK : (0 : ℚ) < stabCard Γ K t := by exact_mod_cast stabCard_pos t (hfin t)
    have hcard : (W.relIndex K : ℚ) = ∑ d ∈ Finset.univ.filter (fun d => dcMapLe hWK d = c),
        ((Finset.univ.filter (fun x => dcOfCoset Γ W K t x = d)).card : ℚ) := by
      rw [hidx, Nat.card_eq_fintype_card, ← Finset.card_univ]
      rw [Finset.card_eq_sum_card_fiberwise (f := dcOfCoset Γ W K t)
        (t := Finset.univ.filter (fun d => dcMapLe hWK d = c))]
      · push_cast; rfl
      · intro x _
        simp [dcMapLe_dcOfCoset, hct]
    rw [hcard, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    obtain ⟨k, rfl⟩ := dcOfCoset_surj hWK t _ (hd.trans hct)
    have h1 := fiber_card_mul_stabCard Γ W K hWK t (hfin t) k
    rw [dcOfCoset_mk, stabCard_out]
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, ← dcOfCoset_mk]
    have hsW : (0 : ℚ) < stabCard Γ W (t * k) := by
      have := stabCard_pos t (hfin t)
      rcases Nat.eq_zero_or_pos (stabCard Γ W (t * k)) with h | h
      · rw [h, mul_zero] at h1; omega
      · exact_mod_cast h
    have h1' : (Nat.card {x : K ⧸ W.subgroupOf K // dcOfCoset Γ W K t x =
        dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K)} : ℚ) * stabCard Γ W (t * k) = stabCard Γ K t := by
      exact_mod_cast h1
    field_simp
    linarith [h1']
  unfold mass
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [← Finset.sum_fiberwise Finset.univ (dcMapLe hWK)]
  exact Finset.sum_congr rfl (fun c _ => hfib c)
end GlobalTheory.UnimodMass
