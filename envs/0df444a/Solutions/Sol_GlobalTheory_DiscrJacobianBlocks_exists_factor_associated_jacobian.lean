-- Prove2me | solution 1 for GlobalTheory.DiscrJacobianBlocks.exists_factor_associated_jacobian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:03:38.995571+00:00
-- url     : https://prove2.me/submissions/60054a0c-d05c-44bc-a3a9-387eeea09cd7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrEqJacobianOfIntegralPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsFactorAssociatedJacobian
import Theorems.Thm_GlobalTheory_DiscrJacobianBlocks_map_eq_zero_of_mem_span
import Theorems.Thm_GlobalTheory_DiscrJacobianBlocks_det_eq_prod_fibres
import Theorems.Thm_GlobalTheory_DiscrJacobianBlocks_sum_ite_fibre
import Theorems.Thm_GlobalTheory_DiscrJacobian_der_tmul
import Theorems.Thm_GlobalTheory_DiscrJacobian_mu_tmul
import Theorems.Thm_GlobalTheory_DiscrJacobian_pairing_tmul
import Theorems.Thm_GlobalTheory_T_exists_basis_discr_associated_prod_jacobian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DiscrJacobian.der_tmul
attribute [local simp] GlobalTheory.DiscrJacobian.mu_tmul
attribute [local simp] GlobalTheory.DiscrJacobian.pairing_tmul



set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.DiscrJacobianBlocks
namespace GlobalTheory.DiscrJacobianBlocks
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (g d N : ℕ) (Y : Type) (p : Fin d → Y) (F : Y → Fin g → (MvPowerSeries (Fin g) O)) (ρ : Y → Fin N → (MvPowerSeries (Fin g) O)) (e : Fin d → ((MvPowerSeries (Fin g) O) →ₐ[O] O)) (u : Fin d → Oˣ) (ev : Matrix (Fin d) (Fin N) O), (∀ a i, e a (F (p a) i) = 0) → (∀ a i, e a (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal O) → (∀ a k, ev a k = u a * e a (ρ (p a) k)) → (∀ G : Y → (MvPowerSeries (Fin g) O), ∃ v : Fin N → O, ∀ y, G y - ∑ k, v k • ρ y k ∈ Ideal.span (Set.range (F y))) → (∀ v, ev.mulVec v = 0 → ∀ y, ∑ k, v k • ρ y k ∈ Ideal.span (Set.range (F y))) → (∃ c : O, c ≠ 0 ∧ ∀ t, ∃ v, ev.mulVec v = c • t) → ∃ (ev₀ : Matrix (Fin d) (Fin N) O) (Pm : Matrix (Fin d) (Fin d) O), ev = Pm * ev₀ ∧ Pm.det ≠ 0 ∧ Function.Surjective ev₀.mulVec ∧ Associated (Pm.det ^ 2) (∏ a, e a (Matrix.of fun i j => MvPowerSeries.pderiv O j (F (p a) i)).det) := by
  intro O _ _ _ _ g d N Y p F ρ e u ev hF hX hev hsurj hinj hc
  classical
  obtain ⟨c, hc0, hc⟩ := hc
  have hker : ∀ a {G}, G ∈ Ideal.span (Set.range (F (p a))) → e a G = 0 :=
    fun a G hG => map_eq_zero_of_mem_span (e a) _ (hF a) hG
  have hmul : ∀ v a, ev.mulVec v a = u a * e a (∑ k, v k • ρ (p a) k) := by
    intro v a
    simp only [Matrix.mulVec, dotProduct, hev, map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hloc := fun y : Y => GlobalTheory.T.exists_basis_discr_associated_prod_jacobian O g {a // p a = y} (F y) (fun a => e a.1)
    (by rintro ⟨a, rfl⟩ i; exact hF a i) (fun a i => hX a.1 i)
    (by
      intro G hG
      obtain ⟨v, hv⟩ := hsurj (Pi.single y G)
      have h0 : ev.mulVec v = 0 := by
        funext a
        rw [hmul]
        have h1 := hker a (hv (p a))
        rw [map_sub, sub_eq_zero] at h1
        rw [← h1]
        by_cases h : p a = y
        · subst h
          have := hG ⟨a, rfl⟩
          simp only [Pi.single_eq_same, Pi.zero_apply]
          rw [this, mul_zero]
        · simp [Pi.single_eq_of_ne h]
      have h2 := Ideal.add_mem _ (hv y) (hinj v h0 y)
      simpa using h2)
    ⟨c, hc0, by
      intro t
      obtain ⟨v, hv⟩ := hc (fun a => if h : p a = y then u a * t ⟨a, h⟩ else 0)
      refine ⟨∑ k, v k • ρ y k, ?_⟩
      rintro ⟨a, rfl⟩
      have h1 := congrFun hv a
      rw [hmul] at h1
      simp only [Pi.smul_apply, dite_true, smul_eq_mul] at h1
      apply (u a).isUnit.mul_left_cancel
      rw [h1]; ring⟩
  choose β hβ hdet hass using hloc
  choose r hr huniq using hβ
  let γ : Fin d → MvPowerSeries (Fin g) O := fun a => β (p a) ⟨a, rfl⟩
  have hγ : ∀ y (x : {a // p a = y}), γ x.1 = β y x := by
    rintro y ⟨a, rfl⟩; rfl
  let M : Matrix (Fin d) (Fin d) O := Matrix.of fun a a' => if p a = p a' then e a (γ a') else 0
  let ev₀ : Matrix (Fin d) (Fin N) O := Matrix.of fun a k => r (p a) (ρ (p a) k) ⟨a, rfl⟩
  have hev₀ : ∀ y (x : {a // p a = y}) k, ev₀ x.1 k = r y (ρ y k) x := by
    rintro y ⟨a, rfl⟩ k; rfl
  have hMdet : M.det = ∏ y ∈ Finset.univ.image p,
      (Matrix.of fun a a' : {a // p a = y} => e a.1 (β y a')).det := by
    rw [det_eq_prod_fibres p M (fun a a' h => by simp [M, h])]
    refine Finset.prod_congr rfl fun y _ => ?_
    congr 1
    ext a a'
    simp [M, a.2, a'.2, hγ]
  have hU : IsUnit (Matrix.diagonal fun a => (u a : O)).det := by
    rw [Matrix.det_diagonal]
    exact IsUnit.prod_univ_iff.2 fun a => (u a).isUnit
  refine ⟨ev₀, Matrix.diagonal (fun a => (u a : O)) * M, ?_, ?_, ?_, ?_⟩
  · ext a k
    rw [Matrix.mul_assoc, Matrix.diagonal_mul, hev, Matrix.mul_apply]
    congr 1
    have h1 := hker a (hr (p a) (ρ (p a) k))
    rw [map_sub, sub_eq_zero] at h1
    rw [h1]
    simp only [M, Matrix.of_apply, ite_mul, zero_mul]
    rw [sum_ite_fibre p (p a) (fun a' => e a (γ a') * ev₀ a' k), map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hγ, hev₀, map_smul, smul_eq_mul, mul_comm]
  · rw [Matrix.det_mul, hMdet]
    exact mul_ne_zero hU.ne_zero (Finset.prod_ne_zero_iff.2 fun y _ => hdet y)
  · intro t
    obtain ⟨v, hv⟩ := hsurj (fun y => ∑ x : {a // p a = y}, t x.1 • β y x)
    refine ⟨v, ?_⟩
    funext a
    set y := p a with hy
    have h1 : (fun x : {a // p a = y} => t x.1) = r y (∑ x : {a // p a = y}, t x.1 • β y x) :=
      huniq y _ _ (by simp)
    have h2 : (fun x : {a // p a = y} => ∑ k, v k * r y (ρ y k) x)
        = r y (∑ x : {a // p a = y}, t x.1 • β y x) := by
      apply huniq
      have h3 : ∑ k, v k • (ρ y k - ∑ x, r y (ρ y k) x • β y x) ∈ Ideal.span (Set.range (F y)) :=
        Submodule.sum_mem _ fun k _ => Submodule.smul_of_tower_mem _ _ (hr y (ρ y k))
      have h4 := Ideal.add_mem _ (hv y) h3
      convert h4 using 1
      simp only [smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm]
      abel
    have h5 := congrFun (h2.trans h1.symm) ⟨a, hy.symm⟩
    simp only at h5
    rw [← h5]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
    rfl
  · rw [Matrix.det_mul, mul_pow, hMdet, ← Finset.prod_pow,
      ← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image p) (g := p)
        (fun a _ => Finset.mem_image_of_mem p (Finset.mem_univ a))]
    refine (associated_unit_mul_left _ _ (hU.pow 2)).trans ?_
    refine Associated.prod _ _ _ fun y _ => (hass y).trans (Associated.of_eq ?_)
    rw [Finset.prod_subtype (p := fun a => p a = y) (F := inferInstance) _ (fun a => by simp)]
    refine Finset.prod_congr rfl ?_
    rintro ⟨a, rfl⟩ _
    rfl
end GlobalTheory.DiscrJacobianBlocks
