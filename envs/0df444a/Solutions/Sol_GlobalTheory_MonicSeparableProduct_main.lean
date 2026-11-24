-- Prove2me | solution 1 for GlobalTheory.MonicSeparableProduct.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:34:04.509836+00:00
-- url     : https://prove2.me/submissions/4b20ca1f-be19-426c-bc72-5cde7b7623c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MonicEqProd
import Theorems.Thm_GlobalTheory_MonicSeparableProduct_exists_sep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MonicSeparableProduct
open Polynomial
namespace GlobalTheory.MonicSeparableProduct
theorem _root_.solution : ∀ (F : Type) [inst : Field F] [IsAlgClosed F] (W : ValuationSubring F) (p : ↥W), (∀ (a : ↥W), ¬IsUnit a → ∃ (n : ℕ), a ^ n ∈ Ideal.span {p}) → ∀ (A : Type) [inst_2 : CommRing A] [inst_3 : Algebra (↥W) A] [Module.Finite (↥W) A] (aug : A →ₐ[↥W] ↥W), ∃ (s : A), Function.Surjective (⇑(Algebra.algebraMap A (Localization.Away s)) : A → Localization.Away s) ∧ (∃ (m : ℕ), Ideal.map (Algebra.algebraMap A (Localization.Away s)) (RingHom.ker aug) ^ m ≤ Ideal.span {(Algebra.algebraMap (↥W) (Localization.Away s) : ↥W → Localization.Away s) p}) ∧ ∀ (R : Type) [inst_5 : CommRing R] [inst_6 : Algebra (↥W) R] (w : A →ₐ[↥W] R), (∀ t ∈ RingHom.ker aug, IsNilpotent ((w : A → R) t)) → IsUnit ((w : A → R) s) := by
  intro F _ _ W p hp A _ _ _ aug
  classical
  obtain ⟨S, hS⟩ : (⊤ : Submodule W A).FG := Module.Finite.fg_top
  let τ : A → A := fun a => a - algebraMap W A (aug a)
  have hτ : ∀ a, aug (τ a) = 0 := by
    intro a
    simp only [τ]
    rw [map_sub, AlgHom.commutes]; simp
  choose σ β h1 h2 h3 using fun a => exists_sep W p hp A aug (τ a) (hτ a)
  have hker : RingHom.ker aug = Ideal.span ((S.image τ : Finset A) : Set A) := by
    apply le_antisymm
    · intro x hx
      have key : ∀ y ∈ Submodule.span W (S : Set A),
          τ y ∈ Ideal.span ((S.image τ : Finset A) : Set A) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          apply Ideal.subset_span
          simp only [Finset.coe_image]
          exact ⟨y, hy, rfl⟩
        | zero => simp [τ]
        | add y z _ _ hy hz =>
          have : τ (y + z) = τ y + τ z := by simp only [τ, map_add]; ring
          rw [this]; exact add_mem hy hz
        | smul c y _ hy =>
          have : τ (c • y) = algebraMap W A c * τ y := by
            simp only [τ]
            rw [map_smul, smul_eq_mul, map_mul, Algebra.smul_def]; ring
          rw [this]; exact Ideal.mul_mem_left _ _ hy
      have := key x (by rw [hS]; trivial)
      have hx0 : aug x = 0 := hx
      simpa [τ, hx0] using this
    · rw [Ideal.span_le]
      intro x hx
      simp only [Finset.coe_image] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact hτ y
  set s : A := ∏ a ∈ S, σ a with hs
  have hsu : IsUnit (aug s) := by
    rw [hs, map_prod]
    exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun a _ => h1 a)
  have hsb : s = (∏ a ∈ S, β a) * s ^ 2 := by
    rw [hs, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun a _ => h2 a)
  set b : A := ∏ a ∈ S, β a with hb
  have hLu : IsUnit (algebraMap A (Localization.Away s) s) := IsLocalization.Away.algebraMap_isUnit s
  refine ⟨s, ?_, ?_, ?_⟩
  · have hinv : algebraMap A (Localization.Away s) s * algebraMap A (Localization.Away s) b = 1 := by
      apply hLu.mul_left_cancel
      have := congrArg (algebraMap A (Localization.Away s)) hsb
      rw [map_mul, map_pow] at this
      linear_combination -this
    intro z
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj s z
    refine ⟨a * b ^ n, ?_⟩
    rw [map_mul, map_pow, ← ha, mul_assoc, ← mul_pow, hinv, one_pow, mul_one]
  · apply Ideal.exists_pow_le_of_le_radical_of_fg
    · rw [hker, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨x, hx, rfl⟩
      simp only [Finset.coe_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [Ideal.radical_eq_sInf]
      refine Ideal.mem_sInf.2 ?_
      rintro P ⟨hle, hP⟩
      refine h3 y (P.comap (algebraMap A (Localization.Away s))) inferInstance ?_ ?_
      · rw [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
        exact hle (Ideal.mem_span_singleton_self _)
      · intro hmem
        have hsm : s ∈ P.comap (algebraMap A (Localization.Away s)) :=
          Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem σ hy) hmem
        exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hsm hLu)
    · apply Ideal.FG.map
      rw [hker]
      exact ⟨_, rfl⟩
  · intro R _ _ w hw
    have hn := hw (τ s) (hτ s)
    have hu : IsUnit (algebraMap W R (aug s)) := hsu.map _
    have : w s = algebraMap W R (aug s) + w (τ s) := by
      simp only [τ]
      rw [map_sub, AlgHom.commutes]; ring
    rw [this]
    exact hn.isUnit_add_left_of_commute hu (Commute.all _ _)
end GlobalTheory.MonicSeparableProduct
