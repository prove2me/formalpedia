-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwistedAverage.mem_twKer_iff_average
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:22:07.946892+00:00
-- url     : https://prove2.me/submissions/211f1b08-5d07-4d49-a777-3da321d9f11b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemTwKerIffAverage
import Theorems.Thm_GlobalTheory_CompanionTheory_TwistedAverage_sum_out_refine
import Theorems.Thm_GlobalTheory_CompanionTheory_TwistedAverage_twOrbit_mul_right
import Theorems.Thm_GlobalTheory_CompanionTheory_TwistedAverage_isOpen_stabKer
import Theorems.Thm_GlobalTheory_CompanionTheory_TwistedAverage_finiteIndex_stabKer
import Theorems.Thm_GlobalTheory_CompanionTheory_TwistedAverage_exists_sum_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TwistedAverage
open GlobalTheory.PRep
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.CompanionTheory.TwistedAverage
theorem _root_.solution (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (L : Subgroup G)
    (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) (v : V) :
    v ∈ twKer ρ L θ ↔ ∃ (K : Subgroup L) (T : Finset L), IsOpen (K : Set L) ∧
      (∀ x ∈ K, ρ (x : G) v = v) ∧ (∀ x ∈ K, θ x = 1) ∧
      (∀ x : L, ∃! t, t ∈ T ∧ t⁻¹ * x ∈ K) ∧
      ∑ t ∈ T, (((θ t)⁻¹ : ℂˣ) : ℂ) • ρ t v = 0 := by
  classical
  constructor
  · intro hv
    obtain ⟨M, hM, hsum⟩ := exists_sum_eq_zero hρ hL θ hθ hv
    haveI hK : (stabKer ρ L θ v).FiniteIndex := finiteIndex_stabKer hρ hL θ hθ v
    haveI : Fintype (L ⧸ stabKer ρ L θ v) := Fintype.ofFinite _
    refine ⟨stabKer ρ L θ v, (Finset.univ : Finset (L ⧸ stabKer ρ L θ v)).image Quotient.out,
      isOpen_stabKer hρ L θ hθ v,
      fun x hx => hx.1, fun x hx => hx.2, ?_, ?_⟩
    · intro x
      refine ⟨(QuotientGroup.mk x : L ⧸ stabKer ρ L θ v).out, ⟨Finset.mem_image_of_mem _
        (Finset.mem_univ _), ?_⟩, ?_⟩
      · exact QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
      · rintro t ⟨ht, hx⟩
        obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ht
        have : q = (QuotientGroup.mk x : L ⧸ stabKer ρ L θ v) := by
          rw [← QuotientGroup.out_eq' q]
          exact QuotientGroup.eq.2 hx
        rw [this]
    · rw [Finset.sum_image (fun a _ b _ h => Quotient.out_injective h)]
      set C : Subgroup L := (M ⊓ stabKer ρ L θ v).normalCore with hC
      haveI : C.Normal := Subgroup.normalCore_normal _
      haveI : C.FiniteIndex := inferInstance
      haveI : Fintype (L ⧸ C) := Fintype.ofFinite _
      have hCM : C ≤ M ⊓ stabKer ρ L θ v := Subgroup.normalCore_le _
      haveI : Finite (stabKer ρ L θ v ⧸ C.subgroupOf (stabKer ρ L θ v)) := inferInstance
      haveI : Fintype (stabKer ρ L θ v ⧸ C.subgroupOf (stabKer ρ L θ v)) := Fintype.ofFinite _
      have h0 := hsum C (hCM.trans inf_le_left)
      rw [sum_out_refine (hCM.trans inf_le_right) (twOrbit ρ L θ v)
        (fun x k hk => twOrbit_mul_right ρ L θ v x k hk)] at h0
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h0
      rcases h0 with h0 | h0
      · exact absurd h0 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
      · exact h0
  · rintro ⟨K, T, -, -, -, hT, hsum⟩
    have hne : T.Nonempty := by
      obtain ⟨t, ⟨ht, -⟩, -⟩ := hT 1
      exact ⟨t, ht⟩
    have hc : (T.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hne.card_pos.ne'
    have hmem : ∀ t : L, v - (((θ t)⁻¹ : ℂˣ) : ℂ) • ρ (t : G) v ∈ twKer ρ L θ := by
      intro t
      have hg : ρ (t : G) v - (θ t : ℂ) • v ∈ twKer ρ L θ := Submodule.subset_span ⟨t, v, rfl⟩
      have := (twKer ρ L θ).smul_mem (-(((θ t)⁻¹ : ℂˣ) : ℂ)) hg
      convert this using 1
      rw [smul_sub, smul_smul, neg_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, neg_smul,
        neg_smul, one_smul]
      abel
    have hs : (T.card : ℂ) • v = ∑ t ∈ T, (v - (((θ t)⁻¹ : ℂˣ) : ℂ) • ρ (t : G) v) := by
      rw [Finset.sum_sub_distrib, hsum, sub_zero, Finset.sum_const, Nat.cast_smul_eq_nsmul]
    have h1 : (T.card : ℂ) • v ∈ twKer ρ L θ := hs ▸ Submodule.sum_mem _ fun t _ => hmem t
    exact ((twKer ρ L θ).smul_mem_iff hc).1 h1
end GlobalTheory.CompanionTheory.TwistedAverage
