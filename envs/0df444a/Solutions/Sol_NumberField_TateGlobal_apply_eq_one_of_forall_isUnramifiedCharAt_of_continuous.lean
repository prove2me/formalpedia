-- Prove2me | solution 1 for NumberField.TateGlobal.apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/84b922d5-d586-5671-9f9b-2b1c7acc8e8f

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Ws23
namespace HXU

open NumberField NumberField.TateGlobal NumberField.AdelicLevel IsDedekindDomain NumberField.AdeleRing
open scoped Topology

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

theorem fst_mul' (x y : AdeleRing (𝓞 F) F) : (x * y).1 = x.1 * y.1 := rfl
theorem snd_apply_mul' (x y : AdeleRing (𝓞 F) F) (w : HeightOneSpectrum (𝓞 F)) : (x * y).2 w = x.2 w * y.2 w := rfl
theorem fst_one' : (1 : AdeleRing (𝓞 F) F).1 = 1 := rfl
theorem snd_apply_one' (w : HeightOneSpectrum (𝓞 F)) : (1 : AdeleRing (𝓞 F) F).2 w = 1 := rfl
theorem fst_unitsPow' (z : (AdeleRing (𝓞 F) F)ˣ) (n : ℕ) :
    ((z ^ n : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = ((z : AdeleRing (𝓞 F) F).1) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Units.val_one, fst_one']
  | succ n ih => rw [pow_succ, pow_succ, Units.val_mul, fst_mul', ih]
theorem snd_apply_unitsPow' (z : (AdeleRing (𝓞 F) F)ˣ) (n : ℕ) (w : HeightOneSpectrum (𝓞 F)) :
    ((z ^ n : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = ((z : AdeleRing (𝓞 F) F).2 w) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Units.val_one, snd_apply_one']
  | succ n ih => rw [pow_succ, pow_succ, Units.val_mul, snd_apply_mul', ih]
theorem snd_apply_unitsInv_mul' (z : (AdeleRing (𝓞 F) F)ˣ) (w : HeightOneSpectrum (𝓞 F)) :
    ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w * (z : AdeleRing (𝓞 F) F).2 w = 1 := by
  rw [← snd_apply_mul', ← Units.val_mul, inv_mul_cancel, Units.val_one, snd_apply_one']
theorem snd_apply_mul_unitsInv' (z : (AdeleRing (𝓞 F) F)ˣ) (w : HeightOneSpectrum (𝓞 F)) :
    (z : AdeleRing (𝓞 F) F).2 w * ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = 1 := by
  rw [← snd_apply_mul', ← Units.val_mul, mul_inv_cancel, Units.val_one, snd_apply_one']
theorem fst_unitsInv' (z : (AdeleRing (𝓞 F) F)ˣ) (hz : (z : AdeleRing (𝓞 F) F).1 = 1) :
    ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
  have : (z : AdeleRing (𝓞 F) F).1 * ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
    rw [← fst_mul', ← Units.val_mul, mul_inv_cancel, Units.val_one, fst_one']
  rw [hz, one_mul] at this
  exact this

theorem exists_finite_forall_integral_mem {V : Set (AdeleRing (𝓞 F) F)} (hV : V ∈ 𝓝 (1 : AdeleRing (𝓞 F) F)) :
    ∃ I : Set (HeightOneSpectrum (𝓞 F)), I.Finite ∧ ∀ y : FiniteAdeleRing (𝓞 F) F,
      (∀ w, y w ∈ w.adicCompletionIntegers F) → (∀ w ∈ I, y w = 1) →
        (((1 : InfiniteAdeleRing F), y) : AdeleRing (𝓞 F) F) ∈ V := by
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
  refine ⟨I, hI, fun y hy hyI => ?_⟩
  let ys : (w : HeightOneSpectrum (𝓞 F)) → ↥((w.adicCompletionIntegers F : Set (w.adicCompletion F))) :=
    fun w => ⟨y w, hy w⟩
  have hys : ys ∈ I.pi tt := by
    intro w hw
    have : ys w = x₁ w := Subtype.ext (hyI w hw)
    rw [this]
    exact mem_of_mem_nhds (htt w)
  have hyB : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite ys ∈ B := hsub hys
  have hyeq : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite ys = y :=
    FiniteAdeleRing.ext _ (fun w => rfl)
  rw [hyeq] at hyB
  exact hAB (Set.mk_mem_prod (mem_of_mem_nhds hA) hyB)

noncomputable def supportedProd (t : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (T : Finset (HeightOneSpectrum (𝓞 F))) : (AdeleRing (𝓞 F) F)ˣ :=
  ∏ v ∈ T, Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v (t v))

theorem supportedProd_fst (t : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (T : Finset (HeightOneSpectrum (𝓞 F))) :
    ((supportedProd F t T : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
  classical
  induction T using Finset.induction_on with
  | empty => rfl
  | insert v T hv ih =>
    rw [supportedProd, Finset.prod_insert hv, Units.val_mul, fst_mul']
    rw [supportedProd] at ih
    rw [ih, mul_one]
    rfl

open scoped Classical in
theorem supportedProd_snd (t : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F)) :
    ((supportedProd F t T : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = if w ∈ T then (t w : w.adicCompletion F) else 1 := by
  classical
  induction T using Finset.induction_on with
  | empty => rfl
  | insert v T hv ih =>
    rw [supportedProd, Finset.prod_insert hv, Units.val_mul, snd_apply_mul']
    rw [supportedProd] at ih
    have hcomp : (((Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v (t v)) : (AdeleRing (𝓞 F) F)ˣ) :
        AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) w =
          ((localUnit (𝓞 F) F v (t v) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w := rfl
    rw [ih, hcomp]
    by_cases hw : w = v
    · subst hw
      rw [localUnit_apply_self]
      simp [hv]
    · rw [localUnit_apply_of_ne (𝓞 F) F v (t v) hw, one_mul]
      simp [Finset.mem_insert, hw]

end Ws23.HXU

open NumberField NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdeleRing IsDedekindDomain

theorem solution
    (F : Type) [Field F] [NumberField F] (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ : Continuous χ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, IsUnramifiedCharAt χ v) :
    ∀ u : (AdeleRing (𝓞 F) F)ˣ,
      (u : AdeleRing (𝓞 F) F).1 = 1 →
      (∀ v ∈ S, (u : AdeleRing (𝓞 F) F).2 v = 1) →
      finitePartUnits (𝓞 F) F u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F →
      χ u = 1 := by
  classical
  intro u hu1 huS hu3

  let U : Set ℂˣ := {z | ‖(z : ℂ) - 1‖ < 1}
  have hUo : IsOpen U := isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const
  have hU1 : (1 : ℂˣ) ∈ U := by simp [U]
  have hW : χ ⁻¹' U ∈ nhds (1 : (AdeleRing (𝓞 F) F)ˣ) :=
    hχ.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hUo.mem_nhds hU1)
  obtain ⟨V₁, hV₁, V₂, hV₂, hVW⟩ : ∃ V₁ ∈ nhds (1 : AdeleRing (𝓞 F) F), ∃ V₂ ∈ nhds (1 : AdeleRing (𝓞 F) F),
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
  obtain ⟨I₁, hI₁, hbox₁⟩ := Ws23.HXU.exists_finite_forall_integral_mem F hV₁
  obtain ⟨I₂, hI₂, hbox₂⟩ := Ws23.HXU.exists_finite_forall_integral_mem F hV₂

  obtain ⟨hint, hint'⟩ := hu3
  let t : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ := fun v => finiteUnitsComponent (𝓞 F) F v u
  have ht : ∀ v, (t v : v.adicCompletion F) = (u : AdeleRing (𝓞 F) F).2 v := fun v => rfl
  have htinv : ∀ v, (((t v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v := by
    intro v
    show (((finiteUnitsComponent (𝓞 F) F v u)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = _
    rw [← map_inv]
    rfl
  let T : Finset (HeightOneSpectrum (𝓞 F)) := ((hI₁.union hI₂).toFinset) \ S
  let p := Ws23.HXU.supportedProd F t T

  have hp : χ p = 1 := by
    show χ (∏ v ∈ T, Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v (t v))) = 1
    rw [map_prod]
    refine Finset.prod_eq_one fun v hv => ?_
    have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2
    have h := hS v hvS (t v) (by rw [ht]; exact hint v) (by rw [htinv]; exact hint' v)
    rw [localChar_apply] at h
    exact h

  let q : (AdeleRing (𝓞 F) F)ˣ := u * p⁻¹
  have hq1 : (q : AdeleRing (𝓞 F) F).1 = 1 := by
    show ((u * p⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1
    rw [Units.val_mul, Ws23.HXU.fst_mul', hu1, one_mul]
    exact Ws23.HXU.fst_unitsInv' F p (Ws23.HXU.supportedProd_fst F t T)
  have hq2 : ∀ w, (q : AdeleRing (𝓞 F) F).2 w = if w ∈ T then 1 else (u : AdeleRing (𝓞 F) F).2 w := by
    intro w
    have hpw := Ws23.HXU.supportedProd_snd F t T w
    have hpinv := Ws23.HXU.snd_apply_unitsInv_mul' F p w
    show ((u * p⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = _
    rw [Units.val_mul, Ws23.HXU.snd_apply_mul']
    by_cases hw : w ∈ T
    · rw [if_pos hw]
      rw [hpw, if_pos hw, ht] at hpinv
      rw [mul_comm] at hpinv
      exact hpinv
    · rw [if_neg hw]
      rw [hpw, if_neg hw, mul_one] at hpinv
      rw [hpinv, mul_one]

  have hqpow : ∀ z : (AdeleRing (𝓞 F) F)ˣ, (z : AdeleRing (𝓞 F) F).1 = 1 →
      (∀ w, (z : AdeleRing (𝓞 F) F).2 w ∈ w.adicCompletionIntegers F) →
      (∀ w ∈ (hI₁.union hI₂).toFinset, (z : AdeleRing (𝓞 F) F).2 w = 1) →
      (z : AdeleRing (𝓞 F) F) ∈ V₁ ∧ (z : AdeleRing (𝓞 F) F) ∈ V₂ := by
    intro z hz1 hzint hzI
    have heq : (z : AdeleRing (𝓞 F) F) = (((1 : InfiniteAdeleRing F), (z : AdeleRing (𝓞 F) F).2) : AdeleRing (𝓞 F) F) :=
      Prod.ext hz1 rfl
    constructor
    · rw [heq]
      exact hbox₁ _ hzint fun w hw => hzI w (by rw [Set.Finite.mem_toFinset]; exact Or.inl hw)
    · rw [heq]
      exact hbox₂ _ hzint fun w hw => hzI w (by rw [Set.Finite.mem_toFinset]; exact Or.inr hw)

  have hpow1 : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (n : ℕ), ((z ^ n : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = (z : AdeleRing (𝓞 F) F).1 ^ n :=
    fun z n => Ws23.HXU.fst_unitsPow' F z n
  have hpow2 : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (n : ℕ) (w : HeightOneSpectrum (𝓞 F)),
      ((z ^ n : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = ((z : AdeleRing (𝓞 F) F).2 w) ^ n :=
    fun z n w => Ws23.HXU.snd_apply_unitsPow' F z n w

  have hqint : ∀ w, (q : AdeleRing (𝓞 F) F).2 w ∈ w.adicCompletionIntegers F := by
    intro w; rw [hq2]; split_ifs
    · exact one_mem _
    · exact hint w
  have hqinvint : ∀ w, ((q⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w ∈ w.adicCompletionIntegers F := by
    intro w
    have hmul := Ws23.HXU.snd_apply_mul_unitsInv' F q w
    by_cases hw : w ∈ T
    · have h1 : (q : AdeleRing (𝓞 F) F).2 w = 1 := by rw [hq2, if_pos hw]
      rw [h1, one_mul] at hmul
      rw [hmul]; exact one_mem _
    · have h1 : (q : AdeleRing (𝓞 F) F).2 w = (u : AdeleRing (𝓞 F) F).2 w := by rw [hq2, if_neg hw]
      rw [h1] at hmul

      have hmul' := Ws23.HXU.snd_apply_mul_unitsInv' F u w
      have hu0 : (u : AdeleRing (𝓞 F) F).2 w ≠ 0 := fun h0 => by rw [h0, zero_mul] at hmul; exact zero_ne_one hmul
      have : ((q⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w :=
        mul_left_cancel₀ hu0 (hmul.trans hmul'.symm)
      rw [this]; exact hint' w
  have hqI : ∀ w ∈ (hI₁.union hI₂).toFinset, (q : AdeleRing (𝓞 F) F).2 w = 1 := by
    intro w hw
    rw [hq2]
    by_cases hwT : w ∈ T
    · rw [if_pos hwT]
    · rw [if_neg hwT]
      have hwS : w ∈ S := by
        by_contra hwS
        exact hwT (Finset.mem_sdiff.mpr ⟨hw, hwS⟩)
      exact huS w hwS
  have hqinv1 : ((q⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := Ws23.HXU.fst_unitsInv' F q hq1
  have hqinvI : ∀ w ∈ (hI₁.union hI₂).toFinset, ((q⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = 1 := by
    intro w hw
    have hmul := Ws23.HXU.snd_apply_mul_unitsInv' F q w
    rw [hqI w hw, one_mul] at hmul
    exact hmul

  have hmemW : ∀ z : (AdeleRing (𝓞 F) F)ˣ, (z : AdeleRing (𝓞 F) F).1 = 1 →
      ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 →
      (∀ w, (z : AdeleRing (𝓞 F) F).2 w ∈ w.adicCompletionIntegers F) →
      (∀ w, ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w ∈ w.adicCompletionIntegers F) →
      (∀ w ∈ (hI₁.union hI₂).toFinset, (z : AdeleRing (𝓞 F) F).2 w = 1) →
      (∀ w ∈ (hI₁.union hI₂).toFinset, ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = 1) →
      ∀ n : ℕ, z ^ n ∈ χ ⁻¹' U := by
    intro z hz1 hzi1 hzint hziint hzI hziI n
    refine hVW _ (hqpow (z ^ n) (by rw [hpow1, hz1, one_pow]) (fun w => by rw [hpow2]; exact pow_mem (hzint w) n)
      (fun w hw => by rw [hpow2, hzI w hw, one_pow])).1 ?_
    rw [← inv_pow]
    exact (hqpow (z⁻¹ ^ n) (by rw [hpow1, hzi1, one_pow]) (fun w => by rw [hpow2]; exact pow_mem (hziint w) n)
      (fun w hw => by rw [hpow2, hziI w hw, one_pow])).2
  have hq : χ q = 1 := by
    apply Ws23.HXU.units_eq_one_of_forall
    · intro n
      have hn := hmemW q hq1 hqinv1 hqint hqinvint hqI hqinvI n
      simpa only [map_pow, Set.mem_preimage, Set.mem_setOf_eq, U] using hn
    · intro n
      have hn := hmemW q⁻¹ hqinv1 (by rw [inv_inv]; exact hq1) hqinvint (by rw [inv_inv]; exact hqint)
        hqinvI (by rw [inv_inv]; exact hqI) n
      simpa only [map_pow, map_inv, Set.mem_preimage, Set.mem_setOf_eq, U] using hn

  have hu : u = q * p := by
    show u = u * p⁻¹ * p
    rw [inv_mul_cancel_right]
  rw [hu, map_mul, hq, hp, one_mul]

end S_NumberField_TateGlobal_apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous
end P2MW
export P2MW.S_NumberField_TateGlobal_apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous (solution)
