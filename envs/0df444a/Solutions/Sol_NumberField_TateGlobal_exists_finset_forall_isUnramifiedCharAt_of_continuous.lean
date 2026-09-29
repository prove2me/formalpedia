-- Prove2me | solution 1 for NumberField.TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d3bf98de-25dc-5e79-a411-7e1849991116

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous

set_option autoImplicit false

open NumberField NumberField.TateGlobal NumberField.AdelicLevel IsDedekindDomain
open scoped Topology

namespace UnramAE

theorem norm_eq_one_of_forall_norm_pow_sub_one_lt {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1)
    (h' : ∀ n : ℕ, ‖z⁻¹ ^ n - 1‖ < 1) : ‖z‖ = 1 := by
  have key : ∀ w : ℂ, (∀ n : ℕ, ‖w ^ n - 1‖ < 1) → ‖w‖ ≤ 1 := by
    intro w hw
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn⟩ : ∃ n : ℕ, 3 ≤ ‖w‖ ^ n :=
      ((tendsto_pow_atTop_atTop_of_one_lt hlt).eventually (Filter.eventually_ge_atTop 3)).exists
    have h1 : ‖w ^ n‖ - ‖(1 : ℂ)‖ ≤ ‖w ^ n - 1‖ := norm_sub_norm_le _ _
    rw [norm_pow, norm_one] at h1
    linarith [hw n]
  have hz1 := key z h
  have hz0 : z ≠ 0 := by
    intro hz
    have := h 1
    rw [hz, pow_one, zero_sub, norm_neg, norm_one] at this
    exact lt_irrefl _ this
  have hz2 := key z⁻¹ h'
  rw [norm_inv] at hz2
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have h3 : ‖z‖ * ‖z‖⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  have : 1 ≤ ‖z‖ :=
    calc (1 : ℝ) = ‖z‖ * ‖z‖⁻¹ := h3.symm
      _ ≤ ‖z‖ * 1 := mul_le_mul_of_nonneg_left hz2 hpos.le
      _ = ‖z‖ := mul_one _
  linarith

theorem eq_one_of_forall_norm_pow_sub_one_lt {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1)
    (h' : ∀ n : ℕ, ‖z⁻¹ ^ n - 1‖ < 1) : z = 1 := by
  have hn : ‖z‖ = 1 := norm_eq_one_of_forall_norm_pow_sub_one_lt h h'

  have hre : ∀ u : ℂ, ‖u‖ = 1 → ‖u - 1‖ < 1 → 1 / 2 < u.re := by
    intro u hu hu1
    have hsq : Complex.normSq u = 1 := by rw [Complex.normSq_eq_norm_sq, hu, one_pow]
    have hsq' : Complex.normSq (u - 1) < 1 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (u - 1)]
    rw [Complex.normSq_apply] at hsq hsq'
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at hsq'
    nlinarith

  have hsqre : ∀ u : ℂ, ‖u‖ = 1 → (u ^ 2).re = 2 * u.re ^ 2 - 1 := by
    intro u hu
    have hsq : Complex.normSq u = 1 := by rw [Complex.normSq_eq_norm_sq, hu, one_pow]
    rw [Complex.normSq_apply] at hsq
    rw [pow_two, Complex.mul_re]
    nlinarith

  have hnk : ∀ k : ℕ, ‖z ^ 2 ^ k‖ = 1 := fun k => by rw [norm_pow, hn, one_pow]
  have hak : ∀ k : ℕ, 1 / 2 < (z ^ 2 ^ k).re := fun k => hre _ (hnk k) (h _)
  have hstep : ∀ k : ℕ, (z ^ 2 ^ (k + 1)).re = 2 * (z ^ 2 ^ k).re ^ 2 - 1 := by
    intro k
    rw [pow_succ, pow_mul]
    exact hsqre _ (hnk k)
  have hle1 : ∀ k : ℕ, (z ^ 2 ^ k).re ≤ 1 := fun k => (Complex.re_le_norm _).trans (hnk k).le
  have hz1 : z.re ≤ 1 := by have := hle1 0; simpa using this
  have hgrow : ∀ k : ℕ, 3 ^ k * (1 - z.re) ≤ 1 - (z ^ 2 ^ k).re := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [hstep k, pow_succ]
      have h1 := hak k
      have h2 := hle1 k
      have h0 : 0 ≤ 1 - z.re := by linarith
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) k]
  have hre1 : z.re = 1 := by
    by_contra hne
    have hlt : z.re < 1 := lt_of_le_of_ne hz1 hne
    have hpos : 0 < 1 - z.re := by linarith
    obtain ⟨k, hk⟩ : ∃ k : ℕ, 1 / (1 - z.re) < 3 ^ k := pow_unbounded_of_one_lt _ (by norm_num)
    have h1 : 1 < 3 ^ k * (1 - z.re) := by
      rw [div_lt_iff₀ hpos] at hk
      linarith
    have h2 := hgrow k
    have h3 := hak k
    linarith

  have hsq : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hn, one_pow]
  rw [Complex.normSq_apply, hre1] at hsq
  have him : z.im = 0 := by nlinarith
  exact Complex.ext hre1 him

theorem units_eq_one_of_forall {z : ℂˣ} (h : ∀ n : ℕ, ‖((z ^ n : ℂˣ) : ℂ) - 1‖ < 1)
    (h' : ∀ n : ℕ, ‖((z⁻¹ ^ n : ℂˣ) : ℂ) - 1‖ < 1) : z = 1 := by
  apply Units.ext
  refine eq_one_of_forall_norm_pow_sub_one_lt (fun n => ?_) (fun n => ?_)
  · simpa [Units.val_pow_eq_pow_val] using h n
  · simpa [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val] using h' n

variable (F : Type) [Field F] [NumberField F]

theorem exists_finite_forall_finIncl_localUnit_mem {V : Set (AdeleRing (𝓞 F) F)} (hV : V ∈ 𝓝 (1 : AdeleRing (𝓞 F) F)) :
    ∃ I : Set (HeightOneSpectrum (𝓞 F)), I.Finite ∧ ∀ v ∉ I, ∀ t : (v.adicCompletion F)ˣ,
      (t : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
        finIncl (𝓞 F) F ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) ∈ V := by
  classical
  have hAopen : ∀ v : HeightOneSpectrum (𝓞 F), IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun v => Valued.isOpen_valuationSubring _
  obtain ⟨A, hA, B, hB, hAB⟩ :=
    (mem_nhds_prod_iff (X := InfiniteAdeleRing F) (Y := FiniteAdeleRing (𝓞 F) F) (s := V)
      (x := (1 : InfiniteAdeleRing F)) (y := (1 : FiniteAdeleRing (𝓞 F) F))).mp hV

  let x₁ : (v : HeightOneSpectrum (𝓞 F)) → ↥((v.adicCompletionIntegers F : Set (v.adicCompletion F))) := fun v => ⟨1, one_mem _⟩
  have hx₁ : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite x₁ = (1 : FiniteAdeleRing (𝓞 F) F) :=
    FiniteAdeleRing.ext _ (fun v => rfl)
  rw [← hx₁] at hB
  have hB' : B ∈ Filter.map (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite) (𝓝 x₁) := by
    rw [← RestrictedProduct.nhds_eq_map_structureMap hAopen x₁]
    exact hB
  have hB'' : (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite) ⁻¹' B ∈ 𝓝 x₁ := hB'
  rw [nhds_pi, Filter.mem_pi] at hB''
  obtain ⟨I, hI, tt, htt, hsub⟩ := hB''
  refine ⟨I, hI, fun v hv t ht => ?_⟩
  let y : (w : HeightOneSpectrum (𝓞 F)) → ↥((w.adicCompletionIntegers F : Set (w.adicCompletion F))) := Function.update x₁ v ⟨t, ht⟩
  have hy : y ∈ I.pi tt := by
    intro w hw
    have hwv : w ≠ v := fun h => hv (h ▸ hw)
    show Function.update x₁ v ⟨t, ht⟩ w ∈ tt w
    rw [Function.update_of_ne hwv]
    exact mem_of_mem_nhds (htt w)
  have hyB : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite y ∈ B := hsub hy
  have hyeq : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite y =
      ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) := by
    apply FiniteAdeleRing.ext
    intro w
    by_cases hw : w = v
    · subst hw
      rw [localUnit_apply_self]
      show ((Function.update x₁ w ⟨t, ht⟩ w : ↥((w.adicCompletionIntegers F : Set (w.adicCompletion F)))) : w.adicCompletion F) = t
      rw [Function.update_self]
    · rw [localUnit_apply_of_ne (𝓞 F) F v t hw]
      show ((Function.update x₁ v ⟨t, ht⟩ w : ↥((w.adicCompletionIntegers F : Set (w.adicCompletion F)))) : w.adicCompletion F) = 1
      rw [Function.update_of_ne hw]
  rw [hyeq] at hyB
  exact hAB (Set.mk_mem_prod (mem_of_mem_nhds hA) hyB)

end UnramAE

theorem solution
    (F : Type) [Field F] [NumberField F] (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ : Continuous χ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, IsUnramifiedCharAt χ v := by
  classical

  let U : Set ℂˣ := {z | ‖(z : ℂ) - 1‖ < 1}
  have hUo : IsOpen U := isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const
  have hU1 : (1 : ℂˣ) ∈ U := by simp [U]
  have hW : χ ⁻¹' U ∈ 𝓝 (1 : (AdeleRing (𝓞 F) F)ˣ) :=
    hχ.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hUo.mem_nhds hU1)

  obtain ⟨V₁, hV₁, V₂, hV₂, hVW⟩ : ∃ V₁ ∈ 𝓝 (1 : AdeleRing (𝓞 F) F), ∃ V₂ ∈ 𝓝 (1 : AdeleRing (𝓞 F) F),
      ∀ x : (AdeleRing (𝓞 F) F)ˣ, (x : AdeleRing (𝓞 F) F) ∈ V₁ →
        ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) ∈ V₂ → x ∈ χ ⁻¹' U := by
    rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hW
    obtain ⟨O, hO, hOW⟩ := hW
    rw [Units.embedProduct_apply, inv_one, Units.val_one, MulOpposite.op_one, nhds_prod_eq, Filter.mem_prod_iff] at hO
    obtain ⟨T₁, hT₁, T₂, hT₂, hTO⟩ := hO
    refine ⟨T₁, hT₁, MulOpposite.op ⁻¹' T₂,
      MulOpposite.continuous_op.continuousAt.preimage_mem_nhds (by rwa [MulOpposite.op_one]), fun x hx1 hx2 => hOW ?_⟩
    show Units.embedProduct _ x ∈ O
    rw [Units.embedProduct_apply]
    exact hTO (Set.mk_mem_prod hx1 hx2)
  obtain ⟨I₁, hI₁, hbox₁⟩ := UnramAE.exists_finite_forall_finIncl_localUnit_mem F hV₁
  obtain ⟨I₂, hI₂, hbox₂⟩ := UnramAE.exists_finite_forall_finIncl_localUnit_mem F hV₂
  refine ⟨(hI₁.union hI₂).toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_union, not_or] at hv

  have hmem : ∀ t : (v.adicCompletion F)ˣ, (t : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
      ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
      Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v t) ∈ χ ⁻¹' U := by
    intro t ht ht'
    refine hVW _ (hbox₁ v hv.1 t ht) ?_
    rw [← map_inv, ← map_inv]
    exact hbox₂ v hv.2 t⁻¹ ht'
  intro t ht ht'
  rw [localChar_apply]
  apply UnramAE.units_eq_one_of_forall
  · intro n
    have hn := hmem (t ^ n) (by rw [Units.val_pow_eq_pow_val]; exact pow_mem ht n)
      (by rw [← inv_pow, Units.val_pow_eq_pow_val]; exact pow_mem ht' n)
    simpa only [map_pow, Set.mem_preimage, Set.mem_setOf_eq, U] using hn
  · intro n
    have hn := hmem (t⁻¹ ^ n) (by rw [Units.val_pow_eq_pow_val]; exact pow_mem ht' n)
      (by rw [← inv_pow, inv_inv, Units.val_pow_eq_pow_val]; exact pow_mem ht n)
    simpa only [map_pow, map_inv, Set.mem_preimage, Set.mem_setOf_eq, U] using hn

end S_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous (solution)
