-- Prove2me | solution 1 for NumberField.InfinitePlace.exists_sum_prod_inv_one_add_mul_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/6a5f419e-07aa-54e1-8710-c9847a7c4afc

import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.Algebra.Module.ZLattice.Summable
import Theorems.Thm_NumberField_Units_exists_forall_abs_sub_mult_mul_log_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfinitePlace_exists_sum_prod_inv_one_add_mul_pow_le

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace M4aP3B
namespace Rows
namespace LatticeSum

variable (F : Type) [Field F] [NumberField F]

theorem apply_le_norm (w : InfinitePlace F) (x : F) : w x ≤ ‖mixedEmbedding F x‖ := by
  rw [← normAtPlace_apply w x, norm_eq_sup'_normAtPlace]
  exact Finset.le_sup' (fun w => normAtPlace w (mixedEmbedding F x)) (Finset.mem_univ w)

theorem exists_apply_eq_norm (x : F) : ∃ w : InfinitePlace F, w x = ‖mixedEmbedding F x‖ := by
  obtain ⟨w, -, hw⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun w : InfinitePlace F => normAtPlace w (mixedEmbedding F x))
  exact ⟨w, by rw [norm_eq_sup'_normAtPlace, hw, normAtPlace_apply]⟩

theorem prod_le_factor {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ)
    (h0 : ∀ i, 0 ≤ f i) (h1 : ∀ i, f i ≤ 1) (i : ι) : ∏ j, f j ≤ f i := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)]
  exact mul_le_of_le_one_right (h0 i) (Finset.prod_le_one (fun j _ => h0 j) fun j _ => h1 j)

def latPt (a : 𝓞 F) : mixedEmbedding.integerLattice F :=
  ⟨mixedEmbedding F (a : F), LinearMap.mem_range.mpr ⟨a, rfl⟩⟩

theorem latPt_injective : Function.Injective (latPt F) := by
  intro a b h
  have h' : mixedEmbedding F (a : F) = mixedEmbedding F (b : F) := congrArg Subtype.val h
  exact RingOfIntegers.coe_injective (mixedEmbedding_injective F h')

theorem core_ineq {yv wu wui ws wa wx Ae S : ℝ} (hS : 0 < S) (hws : ws ≤ S) (hws0 : 0 ≤ ws)
    (hyv : 0 ≤ yv) (hbal : Ae ≤ yv * wu) (hu1 : wu * wui = 1) (hwa : wa = wui * ws * wx)
    (hwx : 0 ≤ wx) (hwui : 0 ≤ wui) : Ae * S⁻¹ * wa ≤ yv * wx := by
  have hq : ws / S ≤ 1 := div_le_one_of_le₀ hws hS.le
  have hq0 : 0 ≤ ws / S := div_nonneg hws0 hS.le
  calc Ae * S⁻¹ * wa = Ae * (wui * (ws / S) * wx) := by rw [hwa]; ring
    _ ≤ (yv * wu) * (wui * (ws / S) * wx) :=
        mul_le_mul_of_nonneg_right hbal (mul_nonneg (mul_nonneg hwui hq0) hwx)
    _ = yv * ((wu * wui) * (ws / S) * wx) := by ring
    _ = yv * ((ws / S) * wx) := by rw [hu1, one_mul]
    _ ≤ yv * (1 * wx) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hq hwx) hyv
    _ = yv * wx := by ring

theorem exists_sum_prod_inv_one_add_mul_pow_le_impl {s : 𝓞 F} (hs : s ≠ 0) (N : ℕ) :
    ∃ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : InfinitePlace F → ℝ, (∀ w, 0 < y w) →
      1 ≤ ∏ w, y w ^ w.mult →
      ∀ T : Finset F, (∀ ξ ∈ T, ξ ≠ 0 ∧ ∃ a : 𝓞 F, (a : F) = (s : F) * ξ) →
        ∑ ξ ∈ T, ∏ w : InfinitePlace F, ((1 + y w * w ξ) ^ M)⁻¹
          ≤ C * ((∏ w : InfinitePlace F, y w ^ w.mult) ^ N)⁻¹ := by
  classical
  obtain ⟨R, hR⟩ := NumberField.Units.exists_forall_abs_sub_mult_mul_log_le F
  set d : ℕ := Module.finrank ℚ F with hd
  have hd0 : 0 < d := Module.finrank_pos
  set M : ℕ := d * (N + 2) with hM
  set L := mixedEmbedding.integerLattice F with hL
  have hrank : Module.finrank ℤ L = d := by rw [hL, ZLattice.rank ℝ, mixedEmbedding.finrank]
  have hsum : Summable fun z : L => ‖(z : mixedSpace F)‖⁻¹ ^ M :=
    ZLattice.summable_norm_pow_inv L M (by rw [hrank, hM]; nlinarith)
  set Z : ℝ := ∑' z : L, ‖(z : mixedSpace F)‖⁻¹ ^ M with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg fun z => by positivity
  set S : ℝ := ‖mixedEmbedding F (s : F)‖ with hS
  have hs' : (s : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hs
  have hS0 : 0 < S := norm_pos_iff.mpr ((map_ne_zero_iff _ (mixedEmbedding_injective F)).mpr hs')
  have hR0 : 0 ≤ R := by
    obtain ⟨u, hu⟩ := hR 0 (by simp)
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    exact (abs_nonneg _).trans (hu w)
  have hC0 : 0 ≤ (Real.exp R * S) ^ M * Z := mul_nonneg (pow_nonneg (mul_nonneg (Real.exp_pos R).le hS0.le) _) hZ0
  refine ⟨M, (Real.exp R * S) ^ M * Z, hC0, fun y hy hY T hT => ?_⟩
  set Y : ℝ := ∏ w, y w ^ w.mult with hYdef
  have hY0 : 0 < Y := Finset.prod_pos fun w _ => pow_pos (hy w) _
  set A : ℝ := Real.exp (Real.log Y / d) with hA
  have hA0 : 0 < A := Real.exp_pos _
  have hAd : A ^ d = Y := by
    rw [hA, ← Real.exp_nat_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hd0.ne'), Real.exp_log hY0]
  have hlogY : Real.log Y = ∑ w, (w.mult : ℝ) * Real.log (y w) := by
    rw [hYdef, Real.log_prod]
    · simp [Real.log_pow]
    · exact fun w _ => pow_ne_zero _ (hy w).ne'
  have hsummult : (∑ w : InfinitePlace F, (w.mult : ℝ)) = d := by
    rw [hd, ← InfinitePlace.sum_mult_eq]; push_cast; rfl
  obtain ⟨u, hu⟩ := hR (fun w => (w.mult : ℝ) * (Real.log Y / d - Real.log (y w))) (by
    have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsummult, ← hlogY]
    field_simp
    ring)
  have hu0 : ((u : 𝓞 F) : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr (Units.ne_zero u)
  have hui0 : (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr (Units.ne_zero _)
  have huu : ((u : 𝓞 F) : F) * (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := by
    simp

  have hbal : ∀ w : InfinitePlace F, A * Real.exp (-R) ≤ y w * w ((u : 𝓞 F) : F) := by
    intro w
    have h1 := (abs_sub_le_iff.1 (hu w)).1
    have hmul : (1 : ℝ) ≤ w.mult := by exact_mod_cast mult_pos (w := w)
    have hwu : 0 < w ((u : 𝓞 F) : F) := pos_iff.mpr hu0
    have h2 : Real.log Y / d - Real.log (y w) - Real.log (w ((u : 𝓞 F) : F)) ≤ R := by
      have h3 : (w.mult : ℝ) * (Real.log Y / d - Real.log (y w) - Real.log (w ((u : 𝓞 F) : F)))
          ≤ R := by linarith [h1]
      by_cases hx : Real.log Y / d - Real.log (y w) - Real.log (w ((u : 𝓞 F) : F)) ≤ 0
      · linarith
      · push Not at hx
        nlinarith
    calc A * Real.exp (-R) = Real.exp (Real.log Y / d - R) := by
          rw [hA, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp (Real.log (y w) + Real.log (w ((u : 𝓞 F) : F))) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = y w * w ((u : 𝓞 F) : F) := by rw [Real.exp_add, Real.exp_log (hy w), Real.exp_log hwu]
  set B : ℝ := A * Real.exp (-R) * S⁻¹ with hB
  have hB0 : 0 < B := mul_pos (mul_pos hA0 (Real.exp_pos _)) (inv_pos.mpr hS0)

  have key : ∀ ξ ∈ T, ∃ a' : 𝓞 F, (a' : F) = (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * (s : F) * ξ ∧
      ∏ w : InfinitePlace F, ((1 + y w * w ξ) ^ M)⁻¹
        ≤ (B ^ M)⁻¹ * ‖mixedEmbedding F (a' : F)‖⁻¹ ^ M := by
    intro ξ hξ
    obtain ⟨hξ0, a, ha⟩ := hT ξ hξ
    refine ⟨(u⁻¹ : (𝓞 F)ˣ) * a, by push_cast [ha]; ring, ?_⟩
    set a' : 𝓞 F := (u⁻¹ : (𝓞 F)ˣ) * a with ha'def
    have ha'F : (a' : F) = (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * (s : F) * ξ := by
      rw [ha'def]; push_cast [ha]; ring
    have ha'0 : (a' : F) ≠ 0 := by rw [ha'F]; exact mul_ne_zero (mul_ne_zero hui0 hs') hξ0
    obtain ⟨w₀, hw₀⟩ := exists_apply_eq_norm F (a' : F)
    have hρ : 0 < ‖mixedEmbedding F (a' : F)‖ := by rw [← hw₀]; exact pos_iff.mpr ha'0
    have hnn : ∀ w : InfinitePlace F, 0 ≤ y w * w ξ := fun w => mul_nonneg (hy w).le (apply_nonneg w ξ)
    have hf0 : ∀ w : InfinitePlace F, 0 ≤ ((1 + y w * w ξ) ^ M)⁻¹ := fun w =>
      inv_nonneg.mpr (pow_nonneg (by linarith [hnn w]) _)
    have hf1 : ∀ w : InfinitePlace F, ((1 + y w * w ξ) ^ M)⁻¹ ≤ 1 := fun w =>
      inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [hnn w]))
    have hcore : B * ‖mixedEmbedding F (a' : F)‖ ≤ 1 + y w₀ * w₀ ξ := by
      rw [← hw₀, hB]
      have h := core_ineq (yv := y w₀) (wu := w₀ ((u : 𝓞 F) : F))
        (wui := w₀ (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)) (ws := w₀ (s : F)) (wa := w₀ (a' : F)) (wx := w₀ ξ)
        (Ae := A * Real.exp (-R)) (S := S) hS0 (apply_le_norm F w₀ (s : F)) (apply_nonneg _ _)
        (hy w₀).le (hbal w₀) (by rw [← map_mul, huu, map_one]) (by rw [ha'F, map_mul, map_mul])
        (apply_nonneg _ _) (apply_nonneg _ _)
      linarith [hnn w₀]
    calc ∏ w : InfinitePlace F, ((1 + y w * w ξ) ^ M)⁻¹ ≤ ((1 + y w₀ * w₀ ξ) ^ M)⁻¹ :=
          prod_le_factor _ hf0 hf1 w₀
      _ ≤ ((B * ‖mixedEmbedding F (a' : F)‖) ^ M)⁻¹ := by
          apply inv_anti₀ (pow_pos (mul_pos hB0 hρ) _)
          exact pow_le_pow_left₀ (mul_pos hB0 hρ).le hcore _
      _ = (B ^ M)⁻¹ * ‖mixedEmbedding F (a' : F)‖⁻¹ ^ M := by
          rw [mul_pow, mul_inv, inv_pow]

  choose! g hg using key
  have hinj : Set.InjOn (fun ξ => latPt F (g ξ)) T := by
    intro ξ₁ h₁ ξ₂ h₂ heq
    have h := congrArg (fun z : L => (z : mixedSpace F)) heq
    simp only [latPt] at h
    have h' : ((g ξ₁ : 𝓞 F) : F) = ((g ξ₂ : 𝓞 F) : F) := mixedEmbedding_injective F h
    rw [(hg ξ₁ h₁).1, (hg ξ₂ h₂).1] at h'
    exact mul_left_cancel₀ (mul_ne_zero hui0 hs') h'
  have hdom : ∑ ξ ∈ T, ‖mixedEmbedding F ((g ξ : 𝓞 F) : F)‖⁻¹ ^ M ≤ Z := by
    have h1 : ∑ ξ ∈ T, ‖mixedEmbedding F ((g ξ : 𝓞 F) : F)‖⁻¹ ^ M
        = ∑ z ∈ T.image (fun ξ => latPt F (g ξ)), ‖(z : mixedSpace F)‖⁻¹ ^ M := by
      rw [Finset.sum_image hinj]; rfl
    rw [h1, hZ]
    exact hsum.sum_le_tsum _ fun z _ => by positivity

  have hBM : (B ^ M)⁻¹ = (Real.exp R * S) ^ M * (A ^ M)⁻¹ := by
    have hE : Real.exp (-R) = (Real.exp R)⁻¹ := Real.exp_neg R
    rw [hB, hE]
    have h1 : A ≠ 0 := hA0.ne'
    have h2 : Real.exp R ≠ 0 := (Real.exp_pos R).ne'
    have h3 : S ≠ 0 := hS0.ne'
    field_simp
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (mul_ne_zero h2 h3))]
  have hAM : (A ^ M)⁻¹ ≤ (Y ^ N)⁻¹ := by
    rw [hM, pow_mul, hAd]
    exact inv_anti₀ (pow_pos hY0 _) (pow_le_pow_right₀ hY (by omega))
  calc ∑ ξ ∈ T, ∏ w : InfinitePlace F, ((1 + y w * w ξ) ^ M)⁻¹
        ≤ ∑ ξ ∈ T, (B ^ M)⁻¹ * ‖mixedEmbedding F ((g ξ : 𝓞 F) : F)‖⁻¹ ^ M :=
          Finset.sum_le_sum fun ξ hξ => (hg ξ hξ).2
    _ = (B ^ M)⁻¹ * ∑ ξ ∈ T, ‖mixedEmbedding F ((g ξ : 𝓞 F) : F)‖⁻¹ ^ M := by rw [Finset.mul_sum]
    _ ≤ (B ^ M)⁻¹ * Z := mul_le_mul_of_nonneg_left hdom (inv_nonneg.mpr (pow_nonneg hB0.le _))
    _ = (Real.exp R * S) ^ M * Z * (A ^ M)⁻¹ := by rw [hBM]; ring
    _ ≤ (Real.exp R * S) ^ M * Z * (Y ^ N)⁻¹ := mul_le_mul_of_nonneg_left hAM hC0

theorem gate_empty (y : InfinitePlace F → ℝ) (M N : ℕ) (C : ℝ) (hC : 0 ≤ C) (hy : ∀ w, 0 < y w) :
    ∑ ξ ∈ (∅ : Finset F), ∏ w : InfinitePlace F, ((1 + y w * w ξ) ^ M)⁻¹
      ≤ C * ((∏ w : InfinitePlace F, y w ^ w.mult) ^ N)⁻¹ := by
  rw [Finset.sum_empty]
  exact mul_nonneg hC (inv_nonneg.mpr (pow_nonneg (Finset.prod_nonneg fun w _ => (pow_pos (hy w) _).le) _))

end M4aP3B.Rows.LatticeSum

end

#print axioms M4aP3B.Rows.LatticeSum.exists_sum_prod_inv_one_add_mul_pow_le_impl
#print axioms M4aP3B.Rows.LatticeSum.gate_empty

theorem solution
    (F : Type) [Field F] [NumberField F] {s : NumberField.RingOfIntegers F} (hs : s ≠ 0) (N : ℕ) :
    ∃ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : NumberField.InfinitePlace F → ℝ, (∀ w, 0 < y w) →
      1 ≤ ∏ w, y w ^ w.mult →
      ∀ T : Finset F,
        (∀ ξ ∈ T, ξ ≠ 0 ∧ ∃ a : NumberField.RingOfIntegers F, (a : F) = (s : F) * ξ) →
        ∑ ξ ∈ T, ∏ w : NumberField.InfinitePlace F, ((1 + y w * w ξ) ^ M)⁻¹
          ≤ C * ((∏ w : NumberField.InfinitePlace F, y w ^ w.mult) ^ N)⁻¹ := by
  first
    | exact M4aP3B.Rows.LatticeSum.exists_sum_prod_inv_one_add_mul_pow_le_impl F hs N
    | (apply M4aP3B.Rows.LatticeSum.exists_sum_prod_inv_one_add_mul_pow_le_impl <;> assumption)

end S_NumberField_InfinitePlace_exists_sum_prod_inv_one_add_mul_pow_le
end P2MW
export P2MW.S_NumberField_InfinitePlace_exists_sum_prod_inv_one_add_mul_pow_le (solution)
