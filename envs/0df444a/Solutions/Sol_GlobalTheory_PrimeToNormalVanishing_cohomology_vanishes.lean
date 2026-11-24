-- Prove2me | solution 1 for GlobalTheory.PrimeToNormalVanishing.cohomology_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:46:23.155784+00:00
-- url     : https://prove2.me/submissions/5922f089-c388-4921-941c-4adb0f497a29

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousCohomologyVanishesOfPrimeToLNormalNoIn
import Theorems.Thm_GlobalTheory_PrimeToNormalVanishing_two_variables
import Theorems.Thm_GlobalTheory_PrimeToNormalVanishing_three_variables
import Theorems.Thm_GlobalTheory_PrimeToNormalVanishing_exists_inverse
import Theorems.Thm_GlobalTheory_PrimeToNormalVanishing_card_coprime
import Theorems.Thm_GlobalTheory_PrimeToNormalVanishing_exists_level

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.PrimeToNormalVanishing
namespace GlobalTheory.PrimeToNormalVanishing
theorem _root_.solution : ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousConstSMul R M] (ρ : Representation R Γ M) (l : ℕ) (J : Subgroup Γ), l.Prime → J.Normal → IsClosed (J : Set Γ) → (∀ U : Subgroup Γ, U.Normal → IsOpen (U : Set Γ) → ∀ j ∈ J, ∃ n, Nat.Coprime n l ∧ j ^ n ∈ U) → ContAction ρ → (∀ m : M, ∃ n, l ^ n • m = 0) → (∀ m : M, (∀ j ∈ J, ρ j m = m) → m = 0) → H0 ρ = ⊥ ∧ Subsingleton (H1 ρ) ∧ Subsingleton (H2 ρ) := by
  intro Γ _ _ _ _ _ _ R M _ _ _ _ _ _ ρ l J hl hJ _ hord hρ htor hinv
  classical
  have hcop : ∀ (U : OpenNormalSubgroup Γ) [Fintype (J.map (QuotientGroup.mk' U.toSubgroup))],
      Nat.Coprime (Fintype.card (J.map (QuotientGroup.mk' U.toSubgroup))) l := by
    intro U _
    refine card_coprime _ l hl ?_
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨n, hn, hjn⟩ := hord U.toSubgroup inferInstance U.isOpen j hj
    exact ⟨n, hn, by rw [← map_pow]; exact (QuotientGroup.eq_one_iff _).2 hjn⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (Submodule.eq_bot_iff _).2 fun m hm => hinv m fun j _ => hm j
  · refine Submodule.Quotient.subsingleton_iff.2 (Submodule.eq_top_iff'.2 ?_)
    rintro ⟨f, hf, hfc⟩
    obtain ⟨U, F, hF⟩ := exists_level (fun p : Γ × Γ × Γ => ρ p.1 (f (p.1⁻¹ * p.2.1)))
      (hρ.comp (continuous_fst.prodMk (hf.comp (by fun_prop))))
    haveI : Finite (Γ ⧸ U.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
    haveI := Fintype.ofFinite (J.map (QuotientGroup.mk' U.toSubgroup))
    haveI := hJ.map _ (QuotientGroup.mk'_surjective U.toSubgroup)
    have hF' : ∀ a b : Γ, F a b 1 = ρ a (f (a⁻¹ * b)) := fun a b => hF a b 1
    obtain ⟨m, hm⟩ := two_variables ρ (QuotientGroup.mk' U.toSubgroup) J
      (J.map (QuotientGroup.mk' U.toSubgroup)) (fun j hj => ⟨j, hj, rfl⟩) hinv
      (fun a b => F a b 1) (by
        intro g a b
        induction a using QuotientGroup.induction_on
        induction b using QuotientGroup.induction_on
        simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, hF']
        simp [mul_assoc]) (by
        intro a b c
        induction a using QuotientGroup.induction_on with | H a => ?_
        induction b using QuotientGroup.induction_on with | H b => ?_
        induction c using QuotientGroup.induction_on with | H c => ?_
        have e := hfc (a⁻¹ * b) (b⁻¹ * c)
        have e' : a⁻¹ * b * (b⁻¹ * c) = a⁻¹ * c := by group
        simp only [hF']
        rw [← e', e, map_add, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
        abel)
    obtain ⟨a, ha⟩ := exists_inverse l _ ((hcop U).pow_left 2) htor (fun q => F 1 q 1)
    refine (mem_coboundaries1 ρ _).2 ⟨a • m, fun g => ?_⟩
    have e := ha g
    have e2 := hF 1 g 1
    have e3 := hm g
    simp only [QuotientGroup.mk'_apply] at e3
    rw [e3] at e
    rw [map_zsmul, ← smul_sub, e, ← QuotientGroup.mk_one, e2]
    simp
  · refine Submodule.Quotient.subsingleton_iff.2 (Submodule.eq_top_iff'.2 ?_)
    rintro ⟨f, hf, hfc⟩
    obtain ⟨U, F, hF⟩ := exists_level
      (fun p : Γ × Γ × Γ => ρ p.1 (f (p.1⁻¹ * p.2.1, p.2.1⁻¹ * p.2.2)))
      (hρ.comp (continuous_fst.prodMk (hf.comp (by fun_prop))))
    haveI : Finite (Γ ⧸ U.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
    haveI : DiscreteTopology (Γ ⧸ U.toSubgroup) := QuotientGroup.discreteTopology U.isOpen
    haveI := Fintype.ofFinite (J.map (QuotientGroup.mk' U.toSubgroup))
    haveI := hJ.map _ (QuotientGroup.mk'_surjective U.toSubgroup)
    simp only at hF
    obtain ⟨H, hH⟩ := three_variables ρ (QuotientGroup.mk' U.toSubgroup) J
      (J.map (QuotientGroup.mk' U.toSubgroup)) (fun j hj => ⟨j, hj, rfl⟩) hinv F (by
        intro g a b c
        induction a using QuotientGroup.induction_on
        induction b using QuotientGroup.induction_on
        induction c using QuotientGroup.induction_on
        simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, hF]
        simp [mul_assoc]) (by
        intro a b c d
        induction a using QuotientGroup.induction_on with | H a => ?_
        induction b using QuotientGroup.induction_on with | H b => ?_
        induction c using QuotientGroup.induction_on with | H c => ?_
        induction d using QuotientGroup.induction_on with | H d => ?_
        have e := congrArg (ρ a) (hfc (a⁻¹ * b) (b⁻¹ * c) (c⁻¹ * d))
        have e1 : a⁻¹ * b * (b⁻¹ * c) = a⁻¹ * c := by group
        have e2 : b⁻¹ * c * (c⁻¹ * d) = b⁻¹ * d := by group
        rw [e1, e2, map_sub, map_add, map_sub, ← Module.End.mul_apply, ← map_mul,
          mul_inv_cancel_left, map_zero] at e
        simp only [hF]
        exact e)
    obtain ⟨a, ha⟩ := exists_inverse l _ ((hcop U).pow_left 3) htor
      (fun q : (Γ ⧸ U.toSubgroup) × (Γ ⧸ U.toSubgroup) => F 1 q.1 q.2)
    refine (separated_dvr_second_cohomology_mem ρ _).2 ⟨fun g => a • H g, ?_, ?_⟩
    · exact (continuous_of_discreteTopology (f := fun q => a • H q)).comp QuotientGroup.continuous_mk
    · funext ⟨g, h⟩
      have e := ha ((g : Γ ⧸ U.toSubgroup), ((g * h : Γ) : Γ ⧸ U.toSubgroup))
      have e2 := hF 1 g (g * h)
      have e3 := hH g h
      simp only [QuotientGroup.mk'_apply] at e3
      simp only at e
      rw [e3] at e
      rw [d1_apply, map_zsmul, ← smul_sub, ← smul_add, e, ← QuotientGroup.mk_one, e2]
      simp
end GlobalTheory.PrimeToNormalVanishing
