-- Prove2me | solution 1 for GlobalTheory.CubeFace.doubling
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:47:58.604217+00:00
-- url     : https://prove2.me/submissions/49fde301-79d0-4252-bab5-ad728c26159e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeSectionFacesAndDoubling
import Theorems.Thm_GlobalTheory_CubeFace_glue_const
import Theorems.Thm_GlobalTheory_CubeFace_span_triples
import Theorems.Thm_GlobalTheory_CubeFace_differentiableOn_prod
import Theorems.Thm_GlobalTheory_CubeFace_prod_alt_erase
import Theorems.Thm_GlobalTheory_CubeFace_diagChart_self
import Theorems.Thm_GlobalTheory_CubeFace_diag_mem
import Theorems.Thm_GlobalTheory_CubeFace_diag_prod
import Theorems.Thm_GlobalTheory_CubeFace_isOpen_sums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.CubeFace
variable {g : ℕ} {ι : Type} (W : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ)
  (hW : ∀ i, IsOpen (W i)) (hcov : ∀ z, ∃ i, z ∈ W i)
  (hc0 : ∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0)
  (hcc : ∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z)
  (T : (Finset (Fin 3) → ι) → (Fin 3 → Fin g → ℂ) → ℂ)
  (hT : ∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))})
  (hT0 : ∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0)
  (hTT : ∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
    (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) →
    T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) *
      T j' x)
  (Λ : Submodule ℤ (Fin g → ℂ)) (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
  (hWp : ∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i)
  (hTp : ∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x + l) = T j x)
  (i₀ : ι) (h0 : (0 : Fin g → ℂ) ∈ W i₀)
include hW hcov hc0 hcc hT hT0 hTT hΛ hWp hTp h0
namespace GlobalTheory.CubeFace
theorem _root_.solution (x : Fin 3 → Fin g → ℂ)
    (hx : ∀ I : Finset (Fin 3), ∑ b ∈ I, x b ∈ W i₀)
    (hx' : ∀ I : Finset (Fin 3), ∑ b ∈ I, (-x) b ∈ W i₀)
    (hx'' : ∀ I : Finset (Fin 3), ∑ b ∈ I, ((2 : ℂ) • x) b ∈ W i₀) :
    T (fun _ => i₀) ((2 : ℂ) • x) * (∏ I : Finset (Fin 3),
      T (fun _ => i₀) ![∑ a ∈ I, x a, ∑ a ∈ I, x a, -∑ a ∈ I, x a] ^
        ((-1 : ℤ) ^ (3 - I.card))) * T (fun _ => i₀) 0 ^ 3 =
      T (fun _ => i₀) x ^ 3 * T (fun _ => i₀) (-x) := by
  have hone : c i₀ i₀ 0 = 1 :=
    mul_left_cancel₀ (hc0 _ _ _ h0 h0) (by rw [hcc _ _ _ _ h0 h0 h0, mul_one])
  have sneg : ∀ (y : Fin 3 → Fin g → ℂ) (I : Finset (Fin 3)),
      ∑ b ∈ I, (-y) b = -∑ b ∈ I, y b := fun y I => by simp
  have stwo : ∀ (y : Fin 3 → Fin g → ℂ) (I : Finset (Fin 3)),
      ∑ b ∈ I, ((2 : ℂ) • y) b = (2 : ℂ) • ∑ b ∈ I, y b := fun y I => by
    simp [Finset.smul_sum]
  let κ := (Finset (Fin 3) → ι) × (Finset (Fin 3) → ι) × (Finset (Fin 3) → ι)
  let U : κ → Set (Fin 3 → Fin g → ℂ) := fun k =>
    {y | (∀ I : Finset (Fin 3), ∑ b ∈ I, y b ∈ W (k.1 I)) ∧
      (∀ I : Finset (Fin 3), ∑ b ∈ I, (-y) b ∈ W (k.2.1 I)) ∧
      (∀ I : Finset (Fin 3), ∑ b ∈ I, ((2 : ℂ) • y) b ∈ W (k.2.2 I))}
  let D : κ → Finset (Fin 3) → (Fin 3 → Fin g → ℂ) → ℂ := fun k I y =>
    T (diagChart (k.1 I) (k.2.1 I) (k.2.2 I) i₀) ![∑ a ∈ I, y a, ∑ a ∈ I, y a, -∑ a ∈ I, y a]
  let R : κ → (Fin 3 → Fin g → ℂ) → ℂ := fun k y =>
    T k.2.2 ((2 : ℂ) • y) * (∏ I : Finset (Fin 3), D k I y ^ ((-1 : ℤ) ^ (3 - I.card))) /
      (T k.1 y ^ 3 * T k.2.1 (-y))
  have hDm : ∀ k y, y ∈ U k → ∀ I J : Finset (Fin 3),
      ∑ i ∈ J, (![∑ a ∈ I, y a, ∑ a ∈ I, y a, -∑ a ∈ I, y a] : Fin 3 → Fin g → ℂ) i ∈
        W (diagChart (k.1 I) (k.2.1 I) (k.2.2 I) i₀ J) := fun k y hy I =>
    diag_mem W (hy.1 I) (sneg y I ▸ hy.2.1 I) (stwo y I ▸ hy.2.2 I) h0
  have hD0 : ∀ k y, y ∈ U k → ∀ I, D k I y ≠ 0 := fun k y hy I => hT0 _ _ (hDm k y hy I)
  have key := glue_const U R
    (fun k => (isOpen_sums W hW k.1).inter
      (((isOpen_sums W hW k.2.1).preimage continuous_neg).inter
        ((isOpen_sums W hW k.2.2).preimage (continuous_const_smul (2 : ℂ)))))
    (fun y => by
      choose s hs using hcov
      exact ⟨(fun I => s _, fun I => s _, fun I => s _), fun I => hs _, fun I => hs _,
        fun I => hs _⟩)
    (fun k => by
      have h1 : DifferentiableOn ℂ (T k.1) (U k) := (hT _).mono fun y hy => hy.1
      have h2 : DifferentiableOn ℂ (fun y => T k.2.1 (-y)) (U k) :=
        (hT _).comp (f := fun y : Fin 3 → Fin g → ℂ => -y) (by fun_prop) fun y hy => hy.2.1
      have h3 : DifferentiableOn ℂ (fun y => T k.2.2 ((2 : ℂ) • y)) (U k) :=
        (hT _).comp (f := fun y : Fin 3 → Fin g → ℂ => (2 : ℂ) • y) (by fun_prop)
          fun y hy => hy.2.2
      have h4 : ∀ I, DifferentiableOn ℂ (D k I) (U k) := fun I => by
        refine (hT _).comp (f := fun y : Fin 3 → Fin g → ℂ =>
          (![∑ a ∈ I, y a, ∑ a ∈ I, y a, -∑ a ∈ I, y a] : Fin 3 → Fin g → ℂ)) ?_
          fun y hy => hDm k y hy I
        refine Differentiable.differentiableOn (differentiable_pi.2 fun b => ?_)
        fin_cases b <;> simp <;> fun_prop
      have h5 : DifferentiableOn ℂ (fun y => ∏ I : Finset (Fin 3),
          D k I y ^ ((-1 : ℤ) ^ (3 - I.card))) (U k) :=
        differentiableOn_prod _ _ fun I _ => (h4 I).zpow (Or.inl fun y hy => hD0 k y hy I)
      have h6 : DifferentiableOn ℂ (fun y => (T k.1 y ^ 3 * T k.2.1 (-y))⁻¹) (U k) :=
        DifferentiableOn.fun_inv ((h1.fun_pow 3).fun_mul h2) fun y (hy : y ∈ U k) =>
          mul_ne_zero (pow_ne_zero _ (hT0 _ _ hy.1)) (hT0 _ _ hy.2.1)
      exact ((h3.fun_mul h5).fun_mul h6).congr fun y _ => div_eq_mul_inv _ _)
    (fun k k' y hy hy' => by
      have e1 := hTT _ _ _ hy.1 hy'.1
      have e2 := hTT _ _ _ hy.2.1 hy'.2.1
      have e3 := hTT _ _ _ hy.2.2 hy'.2.2
      have e4 : ∀ I, D k I y = c (k.1 I) (k'.1 I) (∑ a ∈ I, y a) ^ 3 *
          c (k.2.1 I) (k'.2.1 I) (∑ a ∈ I, (-y) a) *
          (c (k.2.2 I) (k'.2.2 I) (∑ a ∈ I, ((2 : ℂ) • y) a))⁻¹ * D k' I y := fun I => by
        rw [sneg, stwo, ← diag_prod c _ _ _ _ _ _ i₀ hone]
        exact hTT _ _ _ (hDm k y hy I) (hDm k' y hy' I)
      have n1 : (∏ I : Finset (Fin 3), c (k.1 I) (k'.1 I) (∑ a ∈ I, y a) ^
          ((-1 : ℤ) ^ (3 - I.card))) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ (hc0 _ _ _ (hy.1 I) (hy'.1 I))
      have n2 : (∏ I : Finset (Fin 3), c (k.2.1 I) (k'.2.1 I) (∑ a ∈ I, (-y) a) ^
          ((-1 : ℤ) ^ (3 - I.card))) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ (hc0 _ _ _ (hy.2.1 I) (hy'.2.1 I))
      have n3 : (∏ I : Finset (Fin 3), c (k.2.2 I) (k'.2.2 I) (∑ a ∈ I, ((2 : ℂ) • y) a) ^
          ((-1 : ℤ) ^ (3 - I.card))) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ (hc0 _ _ _ (hy.2.2 I) (hy'.2.2 I))
      have m1 := hT0 _ _ hy'.1
      have m2 := hT0 _ _ hy'.2.1
      have e5 : (∏ I : Finset (Fin 3), D k I y ^ ((-1 : ℤ) ^ (3 - I.card))) =
          (∏ I : Finset (Fin 3), c (k.1 I) (k'.1 I) (∑ a ∈ I, y a) ^
            ((-1 : ℤ) ^ (3 - I.card))) ^ 3 *
          (∏ I : Finset (Fin 3), c (k.2.1 I) (k'.2.1 I) (∑ a ∈ I, (-y) a) ^
            ((-1 : ℤ) ^ (3 - I.card))) *
          (∏ I : Finset (Fin 3), c (k.2.2 I) (k'.2.2 I) (∑ a ∈ I, ((2 : ℂ) • y) a) ^
            ((-1 : ℤ) ^ (3 - I.card)))⁻¹ *
          ∏ I : Finset (Fin 3), D k' I y ^ ((-1 : ℤ) ^ (3 - I.card)) := by
        rw [← Finset.prod_pow, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
          ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun I _ => ?_
        rw [e4 I, mul_zpow, mul_zpow, mul_zpow, _root_.inv_zpow, pow_three, pow_three, mul_zpow,
          mul_zpow]
      change T k.2.2 ((2 : ℂ) • y) * _ / (T k.1 y ^ 3 * T k.2.1 (-y)) =
        T k'.2.2 ((2 : ℂ) • y) * _ / (T k'.1 y ^ 3 * T k'.2.1 (-y))
      rw [e5, e1, e2, e3]
      generalize (∏ I : Finset (Fin 3), c (k.1 I) (k'.1 I) (∑ a ∈ I, y a) ^
          ((-1 : ℤ) ^ (3 - I.card))) = A at n1 ⊢
      generalize (∏ I : Finset (Fin 3), c (k.2.1 I) (k'.2.1 I) (∑ a ∈ I, (-y) a) ^
          ((-1 : ℤ) ^ (3 - I.card))) = B at n2 ⊢
      generalize (∏ I : Finset (Fin 3), c (k.2.2 I) (k'.2.2 I) (∑ a ∈ I, ((2 : ℂ) • y) a) ^
          ((-1 : ℤ) ^ (3 - I.card))) = C at n3 ⊢
      field_simp)
    (span_triples Λ hΛ)
    (fun k y l hl hy => by
      have hl1 : ∀ a, (-l) a ∈ Λ := fun a => Λ.neg_mem (hl a)
      have hl2 : ∀ a, ((2 : ℂ) • l) a ∈ Λ := fun a => by
        rw [Pi.smul_apply, two_smul]; exact Λ.add_mem (hl a) (hl a)
      have hs : ∀ (j : Finset (Fin 3) → ι) (y l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) →
          (∀ I : Finset (Fin 3), ∑ b ∈ I, y b ∈ W (j I)) →
          ∀ I : Finset (Fin 3), ∑ b ∈ I, (y + l) b ∈ W (j I) := fun j y l hl hy I => by
        simp only [Pi.add_apply, Finset.sum_add_distrib]
        exact (hWp _ _ _ (Λ.sum_mem fun b _ => hl b)).2 (hy I)
      have hD : ∀ I, D k I (y + l) = D k I y := fun I => by
        have hm : ∑ a ∈ I, l a ∈ Λ := Λ.sum_mem fun b _ => hl b
        have := hTp (diagChart (k.1 I) (k.2.1 I) (k.2.2 I) i₀)
          ![∑ a ∈ I, y a, ∑ a ∈ I, y a, -∑ a ∈ I, y a]
          ![∑ a ∈ I, l a, ∑ a ∈ I, l a, -∑ a ∈ I, l a] (fun a => by
            fin_cases a
            · exact hm
            · exact hm
            · exact Λ.neg_mem hm)
        refine Eq.trans ?_ this
        refine congrArg (T _) ?_
        funext b
        fin_cases b <;> simp [Finset.sum_add_distrib, add_comm]
      refine ⟨⟨hs _ _ _ hl hy.1, ?_, ?_⟩, ?_⟩
      · rw [neg_add]; exact hs _ _ _ hl1 hy.2.1
      · rw [smul_add]; exact hs _ _ _ hl2 hy.2.2
      · simp only [R, hD]
        rw [neg_add, smul_add, hTp _ _ _ hl, hTp _ _ _ hl1, hTp _ _ _ hl2])
    (fun _ => i₀, fun _ => i₀, fun _ => i₀) (fun _ => i₀, fun _ => i₀, fun _ => i₀) x 0
    ⟨hx, hx', hx''⟩
    ⟨fun I => by simpa using h0, fun I => by simpa using h0, fun I => by simpa using h0⟩
  have m0 : T (fun _ => i₀) 0 ≠ 0 := hT0 _ _ fun I => by simpa using h0
  have m1 := hT0 (fun _ => i₀) _ hx
  have m2 := hT0 (fun _ => i₀) _ hx'
  have hz : (![0, 0, -0] : Fin 3 → Fin g → ℂ) = 0 := by
    funext b; fin_cases b <;> simp
  have hp := prod_alt_erase 0 (fun _ => T (fun _ => i₀) 0) fun _ => m0
  simp only [R, D, diagChart_self, smul_zero, Pi.zero_apply, Finset.sum_const_zero, hz, hp] at key
  rw [neg_zero, div_eq_div_iff (mul_ne_zero (pow_ne_zero _ m1) m2)
    (mul_ne_zero (pow_ne_zero _ m0) m0)] at key
  refine mul_right_cancel₀ m0 ?_
  linear_combination key
end GlobalTheory.CubeFace
