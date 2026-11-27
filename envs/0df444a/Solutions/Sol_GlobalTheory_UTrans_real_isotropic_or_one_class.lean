-- Prove2me | solution 1 for GlobalTheory.UTrans.real_isotropic_or_one_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:35:26.8131+00:00
-- url     : https://prove2.me/submissions/fe6a45c5-282c-475f-aa19-eee455ac907f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RealIsotropicOrOneClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped Matrix
namespace GlobalTheory.UTrans
open GlobalTheory.UTrans.Calc
private theorem sigma_hf_eq_hf_swap {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R)
    (G : Matrix (Fin n) (Fin n) R) (hσ : ∀ a, σ (σ a) = a) (hG : ∀ a b, σ (G a b) = G b a)
    (x y : Fin n → R) : σ (GlobalTheory.UTrans.hf σ G x y) = GlobalTheory.UTrans.hf σ G y x := by
  unfold GlobalTheory.UTrans.hf
  simp only [map_sum, map_mul, hσ, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
private theorem hf_add_smul_self {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R)
    (G : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) (c : R) (hc : σ c = c) :
    GlobalTheory.UTrans.hf σ G (x + c • y) (x + c • y) = GlobalTheory.UTrans.hf σ G x x
      + c * (GlobalTheory.UTrans.hf σ G y x + GlobalTheory.UTrans.hf σ G x y) + c * c * GlobalTheory.UTrans.hf σ G y y := by
  unfold GlobalTheory.UTrans.hf
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, hc, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
private theorem exists_eq_algebraMap_of_fixed' {K L : Type} [Field K] [Field L] [CharZero L] [Algebra K L]
    (σ : L →+* L) (δ : L) (hK : ∀ a : K, σ (algebraMap K L a) = algebraMap K L a)
    (hσδ : σ δ = -δ) (hspan : ∀ x : L, ∃ a b : K, x = algebraMap K L a + algebraMap K L b * δ)
    (z : L) (hz : σ z = z) : ∃ k : K, z = algebraMap K L k := by
  obtain ⟨a, b, rfl⟩ := hspan z
  refine ⟨a, ?_⟩
  rw [map_add, map_mul, hK, hK, hσδ] at hz
  have h2 : (2 : L) * (algebraMap K L b * δ) = 0 := by linear_combination -hz
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h two_ne_zero
  · rw [h, add_zero]
private theorem involutive_of_anti_fixed_generator {K L : Type} [Field K] [Field L] [Algebra K L]
    (σ : L →+* L) (δ : L) (hK : ∀ a : K, σ (algebraMap K L a) = algebraMap K L a)
    (hσδ : σ δ = -δ) (hspan : ∀ x : L, ∃ a b : K, x = algebraMap K L a + algebraMap K L b * δ)
    (x : L) : σ (σ x) = x := by
  obtain ⟨a, b, rfl⟩ := hspan x
  simp only [map_add, map_mul, hK, hσδ, map_neg, neg_neg]
private theorem hf_smul_smul' {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R)
    (G : Matrix (Fin n) (Fin n) R) (y : Fin n → R) (c : R) (hc : σ c = c) :
    GlobalTheory.UTrans.hf σ G (c • y) (c • y) = c * c * GlobalTheory.UTrans.hf σ G y y := by
  unfold GlobalTheory.UTrans.hf
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, hc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end GlobalTheory.UTrans
end

set_option autoImplicit false
open scoped Matrix
open GlobalTheory GlobalTheory.UTrans
open GlobalTheory.UTrans.Calc
namespace GlobalTheory.UTrans
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [CharZero L] [Algebra K L] (σ : L →+* L) (δ : L), (∀ a : K, σ (algebraMap K L a) = algebraMap K L a) → δ ≠ 0 → σ δ = -δ → (∀ x : L, ∃ a b : K, x = algebraMap K L a + algebraMap K L b * δ) → Nonempty (K ≃+* ℝ) → ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) L), (∀ a b, σ (G a b) = G b a) → (∃ z : Fin n → L, z ≠ 0 ∧ GlobalTheory.UTrans.hf σ G z z = 0) ∨ ∀ x y : Fin n → L, GlobalTheory.UTrans.hf σ G x x ≠ 0 → GlobalTheory.UTrans.hf σ G y y ≠ 0 → ∃ a : L, GlobalTheory.UTrans.hf σ G y y = σ a * a * GlobalTheory.UTrans.hf σ G x x := by
  intro K L _ _ _ _ σ δ hK hδ hσδ hspan ⟨e⟩ n G hG
  have hσ : ∀ a : L, σ (σ a) = a := involutive_of_anti_fixed_generator σ δ hK hσδ hspan
  have hfix : ∀ z : L, σ z = z → ∃ k : K, z = algebraMap K L k :=
    exists_eq_algebraMap_of_fixed' σ δ hK hσδ hspan
  by_cases hiso : ∃ z : Fin n → L, z ≠ 0 ∧ GlobalTheory.UTrans.hf σ G z z = 0
  · exact Or.inl hiso
  right
  push_neg at hiso
  intro x y hx hy
  obtain ⟨p, hp⟩ := hfix _ (sigma_hf_eq_hf_swap σ G hσ hG x x)
  obtain ⟨q, hq⟩ := hfix _ (sigma_hf_eq_hf_swap σ G hσ hG y y)
  obtain ⟨m, hm⟩ := hfix (GlobalTheory.UTrans.hf σ G y x + GlobalTheory.UTrans.hf σ G x y)
    (by rw [map_add, sigma_hf_eq_hf_swap σ G hσ hG, sigma_hf_eq_hf_swap σ G hσ hG, add_comm])
  have hp0 : e p ≠ 0 := by
    intro h
    apply hx
    rw [hp, (map_eq_zero_iff e e.injective).mp h, map_zero]
  have hq0 : e q ≠ 0 := by
    intro h
    apply hy
    rw [hq, (map_eq_zero_iff e e.injective).mp h, map_zero]

  have hpos : 0 < e q / e p := by
    by_contra hneg
    push_neg at hneg
    have hlt : e q * e p < 0 := by
      have h1 : e q / e p < 0 := lt_of_le_of_ne hneg (div_ne_zero hq0 hp0)
      have h2 : e q * e p = e q / e p * (e p * e p) := by field_simp
      rw [h2]
      exact mul_neg_of_neg_of_pos h1 (mul_self_pos.mpr hp0)
    have hd : 0 ≤ discrim (e q) (e m) (e p) := by
      unfold discrim
      nlinarith [sq_nonneg (e m)]
    have hs : discrim (e q) (e m) (e p) = Real.sqrt (discrim (e q) (e m) (e p))
        * Real.sqrt (discrim (e q) (e m) (e p)) := (Real.mul_self_sqrt hd).symm
    have ht := (quadratic_eq_zero_iff hq0 hs ((-(e m) + Real.sqrt (discrim (e q) (e m) (e p)))
      / (2 * e q))).mpr (Or.inl rfl)
    set t : ℝ := (-(e m) + Real.sqrt (discrim (e q) (e m) (e p))) / (2 * e q) with ht_def
    have hT : q * (e.symm t * e.symm t) + m * e.symm t + p = 0 := by
      apply e.injective
      simp only [map_add, map_mul, RingEquiv.apply_symm_apply, map_zero]
      linear_combination ht
    have hTK : σ (algebraMap K L (e.symm t)) = algebraMap K L (e.symm t) := hK _
    apply hiso (x + algebraMap K L (e.symm t) • y)
    · intro h0
      have hx' : x = (-(algebraMap K L (e.symm t))) • y := by
        rw [neg_smul]
        exact eq_neg_of_add_eq_zero_left h0
      have hxx := hf_smul_smul' σ G y (-(algebraMap K L (e.symm t))) (by rw [map_neg, hTK])
      rw [← hx', hp, hq, neg_mul_neg, ← map_mul, ← map_mul] at hxx
      have hpk := congrArg e ((algebraMap K L).injective hxx)
      simp only [map_mul, RingEquiv.apply_symm_apply] at hpk
      rw [hpk] at hlt
      nlinarith [mul_self_nonneg (t * e q)]
    · rw [hf_add_smul_self σ G x y _ hTK, hm, hp, hq, ← map_mul, ← map_mul, ← map_mul, ← map_add,
        ← map_add, ← map_zero (algebraMap K L)]
      congr 1
      linear_combination hT

  refine ⟨algebraMap K L (e.symm (Real.sqrt (e q / e p))), ?_⟩
  rw [hK, hp, hq, ← map_mul, ← map_mul]
  congr 1
  apply e.injective
  simp only [map_mul, RingEquiv.apply_symm_apply]
  rw [Real.mul_self_sqrt hpos.le]
  field_simp
end GlobalTheory.UTrans
