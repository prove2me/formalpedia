-- Prove2me | solution 1 for GlobalTheory.Hk.aRay_mul_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:07:04.552859+00:00
-- url     : https://prove2.me/submissions/b984fdc2-620d-474d-9a2e-05f437224f52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiniteIdealsIn
import Theorems.Thm_GlobalTheory_Hk_RayConv_finite_dvd
import Theorems.Thm_GlobalTheory_Hk_RayConv_sum_lamIdeal
import Theorems.Thm_GlobalTheory_Hk_RayConv_finite_idealsIn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk
open RayConv
namespace GlobalTheory.Hk
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (g : D.G) (n : ℕ), aRay D g n * Real.log n = ∑ h : D.G, ∑ p ∈ n.divisorsAntidiagonal, lamRay D h p.1 * aRay D (g / h) p.2 := by
  intro K _ _ M _ D g n
  let F : D.G → ℕ → Finset (Ideal (𝓞 K)) := fun g n => (finite_idealsIn D g n).toFinset
  have hF : ∀ g n I, I ∈ F g n ↔ I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ Ideal.absNorm I = n ∧ D.cls I = g :=
    fun g n I => by simp [F, idealsIn]
  have ha : ∀ g n, aRay D g n = (F g n).card := fun g n => by
    unfold aRay; rw [Set.ncard_eq_toFinset_card _ (finite_idealsIn D g n)]
  have hl : ∀ g n, lamRay D g n = ∑ I ∈ F g n, lamIdeal I := fun g n => by
    unfold lamRay; rw [finsum_mem_eq_finite_toFinset_sum _ (finite_idealsIn D g n)]
  let T : Ideal (𝓞 K) → Finset (Ideal (𝓞 K)) := fun I => if h : I = 0 then ∅ else (finite_dvd h).toFinset
  have hT : ∀ I, I ≠ 0 → ∀ J, J ∈ T I ↔ J ∣ I := fun I hI J => by
    simp only [T]; rw [dif_neg hI]; simp
  have L : aRay D g n * Real.log n = ∑ I ∈ F g n, ∑ J ∈ T I, lamIdeal J := by
    rw [ha, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun I hI => ?_
    have := (hF _ _ _).1 hI
    rw [sum_lamIdeal I this.1 _ (hT I this.1), this.2.2.1]
  have R : ∀ h (p : ℕ × ℕ), lamRay D h p.1 * aRay D (g / h) p.2 =
      ∑ q ∈ F h p.1 ×ˢ F (g / h) p.2, lamIdeal q.1 := fun h p => by
    rw [hl, ha, Finset.sum_product, Finset.sum_mul]
    refine Finset.sum_congr rfl fun I _ => ?_
    simp [mul_comm]
  simp only [R]
  rw [L, Finset.sum_sigma', Finset.sum_sigma', Finset.sum_sigma']
  symm
  refine Finset.sum_bij (fun x _ => ⟨x.2.1 * x.2.2, x.2.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨⟨h, p⟩, I, J⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_product, hF, Nat.mem_divisorsAntidiagonal] at hx ⊢
    obtain ⟨⟨-, hp, -⟩, ⟨a1, a2, a3, a4⟩, b1, b2, b3, b4⟩ := hx
    refine ⟨⟨mul_ne_zero a1 b1, a2.mul_left b2, by rw [map_mul, a3, b3, hp], ?_⟩,
      (hT _ (mul_ne_zero a1 b1) _).2 (dvd_mul_right _ _)⟩
    rw [D.cls_mul I J a2 b2 a1 b1, a4, b4, mul_div_cancel]
  · rintro ⟨⟨h, p, p'⟩, I, J⟩ hx ⟨⟨h', q, q'⟩, I', J'⟩ hy hxy
    simp only [Finset.mem_sigma, Finset.mem_product, hF, Nat.mem_divisorsAntidiagonal] at hx hy
    obtain ⟨⟨-, hp, -⟩, ⟨a1, a2, a3, a4⟩, b1, b2, b3, b4⟩ := hx
    obtain ⟨⟨-, hq, -⟩, ⟨c1, c2, c3, c4⟩, d1, d2, d3, d4⟩ := hy
    simp only [Sigma.mk.injEq, heq_eq_eq] at hxy
    obtain ⟨e1, rfl⟩ := hxy
    obtain rfl : J = J' := mul_left_cancel₀ a1 e1
    subst a3 b3 a4 c3 d3 c4
    rfl
  · rintro ⟨I, J⟩ hx
    simp only [Finset.mem_sigma, hF] at hx
    obtain ⟨⟨a1, a2, a3, a4⟩, hJ⟩ := hx
    obtain ⟨J', rfl⟩ := (hT _ a1 _).1 hJ
    have j1 : J ≠ ⊥ := left_ne_zero_of_mul a1
    have j2 : J' ≠ ⊥ := right_ne_zero_of_mul a1
    refine ⟨⟨⟨D.cls J, Ideal.absNorm J, Ideal.absNorm J'⟩, J, J'⟩, ?_, rfl⟩
    simp only [Finset.mem_sigma, Finset.mem_product, hF, Nat.mem_divisorsAntidiagonal, Finset.mem_univ, true_and, and_true]
    refine ⟨⟨by rw [← map_mul, a3], ?_⟩, ⟨j1, a2.of_mul_left_left⟩, j2, a2.of_mul_left_right, ?_⟩
    · rw [← a3]; exact fun h => a1 (Ideal.absNorm_eq_zero_iff.1 h)
    · rw [← a4, D.cls_mul J J' a2.of_mul_left_left a2.of_mul_left_right j1 j2, mul_div_cancel_left]
  · intro x _; rfl
end GlobalTheory.Hk
