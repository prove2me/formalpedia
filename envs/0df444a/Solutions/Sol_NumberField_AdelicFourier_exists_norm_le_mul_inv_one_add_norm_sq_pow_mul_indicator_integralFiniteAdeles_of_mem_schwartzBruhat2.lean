-- Prove2me | solution 1 for NumberField.AdelicFourier.exists_norm_le_mul_inv_one_add_norm_sq_pow_mul_indicator_integralFiniteAdeles_of_mem_schwartzBruhat2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/db94da61-9f27-5052-a906-680b0502e5b0

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_NumberField_AdelicBox_exists_eq_sum_indicator_pi_image_integralFiniteAdeles
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_exists_norm_le_mul_inv_one_add_norm_sq_pow_mul_indicator_integralFiniteAdeles_of_mem_schwartzBruhat2

set_option autoImplicit false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox IsDedekindDomain MeasureTheory
open scoped SchwartzMap

noncomputable section

namespace SB2Major28

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

theorem mem_integral_iff (z : 𝔸f) :
    z ∈ integralFiniteAdeles (𝓞 F) F ↔ ∀ v : HeightOneSpectrum (𝓞 F), z v ∈ v.adicCompletionIntegers F :=
  Iff.rfl

theorem natCast_eq (n : ℕ) : ((n : ℕ) : 𝔸f) = algebraMap (𝓞 F) 𝔸f (n : 𝓞 F) := by
  rw [map_natCast]

theorem add_mem_integral {a b : 𝔸f} (ha : a ∈ integralFiniteAdeles (𝓞 F) F)
    (hb : b ∈ integralFiniteAdeles (𝓞 F) F) : a + b ∈ integralFiniteAdeles (𝓞 F) F := by
  rw [mem_integral_iff] at ha hb ⊢
  intro v
  exact add_mem (ha v) (hb v)

theorem algebraMap_mul_mem_integral (r : 𝓞 F) {b : 𝔸f} (hb : b ∈ integralFiniteAdeles (𝓞 F) F) :
    algebraMap (𝓞 F) 𝔸f r * b ∈ integralFiniteAdeles (𝓞 F) F := by
  rw [mem_integral_iff] at hb ⊢
  intro v
  exact (algebraMap_mul_apply (𝓞 F) F r b v).symm ▸
    mul_mem (algebraMap_mem_adicCompletionIntegers (𝓞 F) F v r) (hb v)

theorem natCast_mul_mem_integral (m : ℕ) {b : 𝔸f} (hb : b ∈ integralFiniteAdeles (𝓞 F) F) :
    ((m : ℕ) : 𝔸f) * b ∈ integralFiniteAdeles (𝓞 F) F := by
  rw [natCast_eq]
  exact algebraMap_mul_mem_integral F _ hb

theorem algebraMap_mem_integral (r : 𝓞 F) : algebraMap (𝓞 F) 𝔸f r ∈ integralFiniteAdeles (𝓞 F) F := by
  have := algebraMap_mul_mem_integral F r (b := 1) (by
    rw [mem_integral_iff]; intro v
    exact (show (1 : 𝔸f) v = 1 from rfl) ▸ one_mem _)
  rwa [mul_one] at this

theorem exists_nat_mul_mem (y : 𝔸f) :
    ∃ n : ℕ, 0 < n ∧ ((n : ℕ) : 𝔸f) * y ∈ integralFiniteAdeles (𝓞 F) F := by
  obtain ⟨s, hs0, hsy⟩ := exists_mul_mem_integralFiniteAdeles (𝓞 F) F y
  have hI : (Ideal.span {s} : Ideal (𝓞 F)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hs0
  have hn0 : Ideal.absNorm (Ideal.span {s} : Ideal (𝓞 F)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hI
  have hmem : ((Ideal.absNorm (Ideal.span {s} : Ideal (𝓞 F)) : ℕ) : 𝓞 F) ∈ (Ideal.span {s} : Ideal (𝓞 F)) :=
    Ideal.absNorm_mem _
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨Ideal.absNorm (Ideal.span {s} : Ideal (𝓞 F)), Nat.pos_of_ne_zero hn0, ?_⟩
  have : ((Ideal.absNorm (Ideal.span {s} : Ideal (𝓞 F)) : ℕ) : 𝔸f) =
      algebraMap (𝓞 F) 𝔸f r * algebraMap (𝓞 F) 𝔸f s := by
    rw [← map_mul, hr, map_natCast]
  rw [this, mul_assoc]
  exact algebraMap_mul_mem_integral F r hsy

theorem mul_nat_mul_mem {y : 𝔸f} {n : ℕ} (m : ℕ) (h : ((n : ℕ) : 𝔸f) * y ∈ integralFiniteAdeles (𝓞 F) F) :
    ((m * n : ℕ) : 𝔸f) * y ∈ integralFiniteAdeles (𝓞 F) F := by
  rw [Nat.cast_mul, mul_assoc]
  exact natCast_mul_mem_integral F m h

open scoped Classical in

def archFactor (M : ℕ) (x : Fin 2 → AdeleRing (𝓞 F) F) : ℝ :=
  ((1 + ‖fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1‖ ^ 2) ^ M)⁻¹

def finFactor (n : ℕ) (x : Fin 2 → AdeleRing (𝓞 F) F) : ℝ :=
  Set.indicator {x : Fin 2 → AdeleRing (𝓞 F) F |
      ∀ i, ((n : ℕ) : 𝔸f) * (x i).2 ∈ integralFiniteAdeles (𝓞 F) F} (fun _ => (1 : ℝ)) x

def Bound (Ψ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (M : ℕ) : Prop :=
  ∃ (C : ℝ) (n : ℕ), 0 ≤ C ∧ 0 < n ∧ ∀ x : Fin 2 → AdeleRing (𝓞 F) F,
    ‖Ψ x‖ ≤ C * archFactor F M x * finFactor F n x

open scoped Classical in
theorem archFactor_pos (M : ℕ) (x : Fin 2 → AdeleRing (𝓞 F) F) : 0 < archFactor F M x := by
  unfold archFactor; positivity

theorem finFactor_of_mem {n : ℕ} {x : Fin 2 → AdeleRing (𝓞 F) F}
    (h : ∀ i, ((n : ℕ) : 𝔸f) * (x i).2 ∈ integralFiniteAdeles (𝓞 F) F) : finFactor F n x = 1 := by
  unfold finFactor
  exact Set.indicator_of_mem
    (show x ∈ {x : Fin 2 → AdeleRing (𝓞 F) F | ∀ i, ((n : ℕ) : 𝔸f) * (x i).2 ∈ integralFiniteAdeles (𝓞 F) F}
      from h) _

theorem finFactor_of_not_mem {n : ℕ} {x : Fin 2 → AdeleRing (𝓞 F) F}
    (h : ¬ ∀ i, ((n : ℕ) : 𝔸f) * (x i).2 ∈ integralFiniteAdeles (𝓞 F) F) : finFactor F n x = 0 := by
  unfold finFactor
  exact Set.indicator_of_notMem
    (show x ∉ {x : Fin 2 → AdeleRing (𝓞 F) F | ∀ i, ((n : ℕ) : 𝔸f) * (x i).2 ∈ integralFiniteAdeles (𝓞 F) F}
      from h) _

theorem finFactor_nonneg (n : ℕ) (x : Fin 2 → AdeleRing (𝓞 F) F) : 0 ≤ finFactor F n x := by
  unfold finFactor; exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem finFactor_le_one (n : ℕ) (x : Fin 2 → AdeleRing (𝓞 F) F) : finFactor F n x ≤ 1 := by
  unfold finFactor; exact Set.indicator_le_self' (fun _ _ => zero_le_one) _

open scoped Classical in
theorem schwartz_decay (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ)) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Fin 2 → mixedEmbedding.mixedSpace F, ‖g y‖ ≤ C * ((1 + ‖y‖ ^ 2) ^ M)⁻¹ := by
  refine ⟨2 ^ (2 * M) * ((Finset.Iic (2 * M, 0)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) g,
    mul_nonneg (by positivity) (apply_nonneg _ _), fun y => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (2 * M, 0)) (k := 2 * M) (n := 0)
    le_rfl le_rfl g y
  rw [norm_iteratedFDeriv_zero] at h
  have hpos : 0 < (1 + ‖y‖ ^ 2) ^ M := by positivity
  have h1 : (1 + ‖y‖ ^ 2) ^ M ≤ (1 + ‖y‖) ^ (2 * M) := by
    rw [pow_mul]
    have h0 : (0 : ℝ) ≤ 1 + ‖y‖ ^ 2 := by positivity
    have h2 : 1 + ‖y‖ ^ 2 ≤ (1 + ‖y‖) ^ 2 := by nlinarith [norm_nonneg y]
    exact pow_le_pow_left₀ h0 h2 M
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖g y‖ * (1 + ‖y‖ ^ 2) ^ M ≤ ‖g y‖ * (1 + ‖y‖) ^ (2 * M) := by gcongr
    _ = (1 + ‖y‖) ^ (2 * M) * ‖g y‖ := mul_comm _ _
    _ ≤ _ := h

open scoped Classical in
theorem bound_pure (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Φ ∈ pureTensorSet2 F) (M : ℕ) :
    Bound F Φ M := by
  obtain ⟨g, h, hlc, hcs, rfl⟩ := hΦ
  obtain ⟨C, hC0, hg⟩ := schwartz_decay F g M
  obtain ⟨d, hd0, s, c, hh⟩ :=
    NumberField.AdelicBox.exists_eq_sum_indicator_pi_image_integralFiniteAdeles F (Fin 2) hlc hcs
  choose nk hnk0 hnk using fun (p : (Fin 2 → F) × Fin 2) =>
    exists_nat_mul_mem F (algebraMap F 𝔸f (p.1 p.2))
  set n : ℕ := ∏ p ∈ s ×ˢ (Finset.univ : Finset (Fin 2)), nk p with hn
  have hnpos : 0 < n := Finset.prod_pos fun p _ => hnk0 p

  have hbox : ∀ z : Fin 2 → 𝔸f, ∀ k ∈ s,
      z ∈ Set.pi Set.univ (fun i => (fun w : 𝔸f =>
        algebraMap F 𝔸f (k i) + algebraMap F 𝔸f (d : F) * w) '' integralFiniteAdeles (𝓞 F) F) →
      ∀ i, ((n : ℕ) : 𝔸f) * z i ∈ integralFiniteAdeles (𝓞 F) F := by
    intro z k hk hz i
    obtain ⟨w, hw, hzw⟩ := (Set.mem_univ_pi.mp hz) i
    rw [← hzw, mul_add]
    refine add_mem_integral F ?_ ?_
    · have hp : (k, i) ∈ s ×ˢ (Finset.univ : Finset (Fin 2)) := Finset.mem_product.mpr ⟨hk, Finset.mem_univ i⟩
      rw [hn, ← Finset.prod_erase_mul _ _ hp]
      exact mul_nat_mul_mem F _ (hnk (k, i))
    · rw [← mul_assoc, mul_comm ((n : ℕ) : 𝔸f), mul_assoc,
        show algebraMap F 𝔸f (d : F) = algebraMap (𝓞 F) 𝔸f d from rfl]
      exact algebraMap_mul_mem_integral F d (natCast_mul_mem_integral F n hw)

  have hbound : ∀ z : Fin 2 → 𝔸f, ‖h z‖ ≤ ∑ k ∈ s, ‖c k‖ := by
    intro z
    rw [hh, Finset.sum_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [Pi.smul_apply, norm_smul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    rw [Set.indicator_apply]
    split_ifs <;> simp
  have hzero : ∀ z : Fin 2 → 𝔸f, (¬ ∀ i, ((n : ℕ) : 𝔸f) * z i ∈ integralFiniteAdeles (𝓞 F) F) → h z = 0 := by
    intro z hz
    rw [hh, Finset.sum_apply]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Pi.smul_apply, Set.indicator_of_notMem, smul_zero]
    exact fun hmem => hz (hbox z k hk hmem)
  refine ⟨C * ∑ k ∈ s, ‖c k‖, n, mul_nonneg hC0 (Finset.sum_nonneg fun _ _ => norm_nonneg _), hnpos,
    fun x => ?_⟩
  rw [norm_mul]
  by_cases hx : ∀ i, ((n : ℕ) : 𝔸f) * (x i).2 ∈ integralFiniteAdeles (𝓞 F) F
  · rw [finFactor_of_mem F hx, mul_one, mul_assoc, mul_comm (∑ k ∈ s, ‖c k‖), ← mul_assoc]
    exact mul_le_mul (hg _) (hbound _) (norm_nonneg _)
      (mul_nonneg hC0 (le_of_lt (by unfold archFactor; positivity)))
  · rw [finFactor_of_not_mem F hx, mul_zero, hzero _ hx, norm_zero, mul_zero]

theorem bound_zero (M : ℕ) : Bound F 0 M :=
  ⟨0, 1, le_rfl, one_pos, fun x => by simp⟩

theorem bound_add {Φ Ψ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} {M : ℕ} (h₁ : Bound F Φ M) (h₂ : Bound F Ψ M) :
    Bound F (Φ + Ψ) M := by
  obtain ⟨C₁, n₁, hC₁, hn₁, b₁⟩ := h₁
  obtain ⟨C₂, n₂, hC₂, hn₂, b₂⟩ := h₂
  refine ⟨C₁ + C₂, n₁ * n₂, add_nonneg hC₁ hC₂, Nat.mul_pos hn₁ hn₂, fun x => ?_⟩
  have hA := archFactor_pos F M x
  by_cases hx : ∀ i, ((n₁ * n₂ : ℕ) : 𝔸f) * (x i).2 ∈ integralFiniteAdeles (𝓞 F) F
  · rw [finFactor_of_mem F hx, mul_one, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (b₁ x).trans (mul_le_of_le_one_right (mul_nonneg hC₁ hA.le) (finFactor_le_one F _ _))
    · exact (b₂ x).trans (mul_le_of_le_one_right (mul_nonneg hC₂ hA.le) (finFactor_le_one F _ _))
  · rw [finFactor_of_not_mem F hx, mul_zero]
    have h1 : ¬ ∀ i, ((n₁ : ℕ) : 𝔸f) * (x i).2 ∈ integralFiniteAdeles (𝓞 F) F := fun h =>
      hx fun i => by rw [mul_comm n₁ n₂]; exact mul_nat_mul_mem F n₂ (h i)
    have h2 : ¬ ∀ i, ((n₂ : ℕ) : 𝔸f) * (x i).2 ∈ integralFiniteAdeles (𝓞 F) F := fun h =>
      hx fun i => mul_nat_mul_mem F n₁ (h i)
    have e1 := b₁ x; have e2 := b₂ x
    rw [finFactor_of_not_mem F h1, mul_zero] at e1
    rw [finFactor_of_not_mem F h2, mul_zero] at e2
    exact (norm_add_le _ _).trans (by linarith)

theorem bound_smul {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} {M : ℕ} (a : ℂ) (h : Bound F Φ M) :
    Bound F (a • Φ) M := by
  obtain ⟨C, n, hC, hn, b⟩ := h
  refine ⟨‖a‖ * C, n, mul_nonneg (norm_nonneg _) hC, hn, fun x => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left ((b x).trans (le_of_eq (mul_assoc _ _ _))) (norm_nonneg _)

theorem bound_of_mem (Ψ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (hΨ : Ψ ∈ schwartzBruhat2 F) (M : ℕ) :
    Bound F Ψ M := by
  refine schwartzBruhat2_induction (p := fun Φ _ => Bound F Φ M) ?_ ?_ ?_ ?_ hΨ
  · exact fun Φ hΦ => bound_pure F Φ hΦ M
  · exact bound_zero F M
  · exact fun Φ Ψ _ _ h₁ h₂ => bound_add F h₁ h₂
  · exact fun a Φ _ h => bound_smul F a h

end SB2Major28

end

open NumberField NumberField.AdelicFourier NumberField.AdelicBox IsDedekindDomain in
open scoped Classical in

theorem solution
    (F : Type) [Field F] [NumberField F]
    (Ψ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (hΨ : Ψ ∈ schwartzBruhat2 F) (M : ℕ) :
    ∃ (C : ℝ) (n : ℕ), 0 ≤ C ∧ 0 < n ∧ ∀ x : Fin 2 → AdeleRing (𝓞 F) F,
      ‖Ψ x‖ ≤ C * ((1 + ‖fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1‖ ^ 2) ^ M)⁻¹ *
        Set.indicator {x : Fin 2 → AdeleRing (𝓞 F) F |
            ∀ i, ((n : ℕ) : FiniteAdeleRing (𝓞 F) F) * (x i).2 ∈ integralFiniteAdeles (𝓞 F) F}
          (fun _ => (1 : ℝ)) x :=
  SB2Major28.bound_of_mem F Ψ hΨ M

end S_NumberField_AdelicFourier_exists_norm_le_mul_inv_one_add_norm_sq_pow_mul_indicator_integralFiniteAdeles_of_mem_schwartzBruhat2
end P2MW
export P2MW.S_NumberField_AdelicFourier_exists_norm_le_mul_inv_one_add_norm_sq_pow_mul_indicator_integralFiniteAdeles_of_mem_schwartzBruhat2 (solution)
