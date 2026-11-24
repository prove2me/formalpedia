-- Prove2me | solution 1 for GlobalTheory.finsum_doubleCoset_regroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:57:38.552653+00:00
-- url     : https://prove2.me/submissions/b1536ec6-9876-4532-a06c-7f0e90fb8eec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumCompEqFinsumCardFiberMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetCardDivCardInfCommutativeSubgroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardFiberDoubleCosetMapEqCardInfConjStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumDoubleCosetRegroupCommutative
import Theorems.Thm_GlobalTheory_T_card_fiber_doubleCoset_map_eq_card_inf_conj
import Theorems.Thm_GlobalTheory_T_doubleCoset_card_div_card_inf_commutative_subgroup
import Theorems.Thm_GlobalTheory_T_finsum_comp_eq_finsum_card_fiber_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (G : Type) [Group G] (T Γ C K' : Subgroup G) (φ : G → ℂ)
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hCT : C ≤ T)
    (hU : ∀ x : G, T ⊓ K'.map (MulAut.conj x).toMonoidHom ≤ C ∧ (T ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0)
    (hφ : ∀ t ∈ T, ∀ k ∈ K', ∀ x, φ (t * x * k) = φ x) :
    ∑ᶠ q : DoubleCoset.Quotient ((Γ ⊓ T : Subgroup G) : Set G) (K' : Set G), ((Nat.card ((Γ ⊓ T) ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℂ))⁻¹ * φ (Quotient.out q) = (Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (Γ ⊓ C : Subgroup G) : ℂ) * ∑ᶠ q : DoubleCoset.Quotient (T : Set G) (K' : Set G), (((T ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex C : ℕ) : ℂ) * φ (Quotient.out q) := by
  classical
  have hconj : ∀ t ∈ T, ∀ k ∈ K', ∀ x : G,
      T ⊓ K'.map (MulAut.conj (t * x * k)).toMonoidHom = T ⊓ K'.map (MulAut.conj x).toMonoidHom := by
    intro t ht k hk x
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    constructor
    · rintro ⟨hg, hm⟩
      refine ⟨hg, ?_⟩
      have e1 : t⁻¹ * g * t = g := by rw [mul_assoc, hT g hg t ht, inv_mul_cancel_left]
      have e2 : (t * x * k)⁻¹ * g * (t * x * k) = k⁻¹ * (x⁻¹ * (t⁻¹ * g * t) * x) * k := by group
      rw [e1] at e2
      rw [e2] at hm
      have e3 : x⁻¹ * g * x = k * (k⁻¹ * (x⁻¹ * g * x) * k) * k⁻¹ := by group
      rw [e3]
      exact K'.mul_mem (K'.mul_mem hk hm) (K'.inv_mem hk)
    · rintro ⟨hg, hm⟩
      refine ⟨hg, ?_⟩
      have e1 : t⁻¹ * g * t = g := by rw [mul_assoc, hT g hg t ht, inv_mul_cancel_left]
      have e2 : (t * x * k)⁻¹ * g * (t * x * k) = k⁻¹ * (x⁻¹ * (t⁻¹ * g * t) * x) * k := by group
      rw [e1] at e2
      rw [e2]
      exact K'.mul_mem (K'.mul_mem (K'.inv_mem hk) hm) hk
  let π : DoubleCoset.Quotient ((Γ ⊓ T : Subgroup G) : Set G) (K' : Set G) →
      DoubleCoset.Quotient (T : Set G) (K' : Set G) := fun q => DoubleCoset.mk T K' (Quotient.out q)
  let h : DoubleCoset.Quotient (T : Set G) (K' : Set G) → ℂ := fun p =>
    ((Nat.card (Γ ⊓ (T ⊓ K'.map (MulAut.conj (Quotient.out p)).toMonoidHom) : Subgroup G) : ℂ))⁻¹ * φ (Quotient.out p)
  have hLHS : ∀ q : DoubleCoset.Quotient ((Γ ⊓ T : Subgroup G) : Set G) (K' : Set G),
      ((Nat.card ((Γ ⊓ T) ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℂ))⁻¹ * φ (Quotient.out q) = h (π q) := by
    intro q
    obtain ⟨t, k, ht, hk, e⟩ := DoubleCoset.mk_out_eq_mul T K' (Quotient.out q)
    show _ = ((Nat.card (Γ ⊓ (T ⊓ K'.map (MulAut.conj (Quotient.out (DoubleCoset.mk T K' (Quotient.out q)))).toMonoidHom) : Subgroup G) : ℂ))⁻¹ * φ (Quotient.out (DoubleCoset.mk T K' (Quotient.out q)))
    rw [e, hconj t ht k hk, hφ t ht k hk, inf_assoc]
  set a : ℂ := (Nat.card (DoubleCoset.Quotient ((Γ.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (Γ ⊓ C : Subgroup G) : ℂ) with ha_def
  have hfinal : ∀ p, (Nat.card (π ⁻¹' {p}) : ℂ) * h p
      = a * ((((T ⊓ K'.map (MulAut.conj (Quotient.out p)).toMonoidHom).relIndex C : ℕ) : ℂ) * φ (Quotient.out p)) := by
    intro p
    have e1 := GlobalTheory.T.card_fiber_doubleCoset_map_eq_card_inf_conj T Γ K' (Quotient.out p)
    rw [DoubleCoset.out_eq'] at e1
    have e2 := GlobalTheory.T.doubleCoset_card_div_card_inf_commutative_subgroup T Γ (T ⊓ K'.map (MulAut.conj (Quotient.out p)).toMonoidHom) C hT (hU _).1 hCT (hU _).2
    show (Nat.card (π ⁻¹' {p}) : ℂ) * (((Nat.card (Γ ⊓ (T ⊓ K'.map (MulAut.conj (Quotient.out p)).toMonoidHom) : Subgroup G) : ℂ))⁻¹ * φ (Quotient.out p)) = _
    rw [e1, ← mul_assoc, ← div_eq_mul_inv, e2, ha_def]
    ring
  have hmul : ∀ (c : ℂ) (f : DoubleCoset.Quotient (T : Set G) (K' : Set G) → ℂ),
      c * ∑ᶠ p, f p = ∑ᶠ p, c * f p := by
    intro c f
    exact mul_finsum f c
  have hdich : (∀ p, h p ≠ 0 → (π ⁻¹' {p}).Finite) ∨ (∀ p, h p ≠ 0 → Nat.card (π ⁻¹' {p}) = 0) := by
    by_cases ha : a = 0
    · right
      intro p hp
      have hc := hfinal p
      rw [ha, zero_mul] at hc
      rcases mul_eq_zero.mp hc with h1 | h1
      · exact_mod_cast h1
      · exact absurd h1 hp
    · left
      intro p hp
      have hφp : φ (Quotient.out p) ≠ 0 := fun e => hp (by simp [h, e])
      have hne : (Nat.card (π ⁻¹' {p}) : ℂ) * h p ≠ 0 := by
        rw [hfinal p]
        exact mul_ne_zero ha (mul_ne_zero (by exact_mod_cast (hU _).2) hφp)
      have hn : Nat.card (π ⁻¹' {p}) ≠ 0 := by
        intro e; apply hne; simp [e]
      exact Set.finite_coe_iff.mp (Nat.finite_of_card_ne_zero hn)
  calc _ = ∑ᶠ q, h (π q) := finsum_congr hLHS
    _ = ∑ᶠ p, (Nat.card (π ⁻¹' {p}) : ℂ) * h p := GlobalTheory.T.finsum_comp_eq_finsum_card_fiber_mul π h hdich
    _ = ∑ᶠ p, a * ((((T ⊓ K'.map (MulAut.conj (Quotient.out p)).toMonoidHom).relIndex C : ℕ) : ℂ) * φ (Quotient.out p)) := finsum_congr hfinal
    _ = _ := (hmul a _).symm
end GlobalTheory
