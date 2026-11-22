-- Prove2me | solution 1 for MasulloGRH.localComponent_eq_norm_cpow_of_isUnramifiedAt
-- status  : ACCEPTED   (prove)
-- author  : @WalrusPaul
-- created : 2026-11-22T18:54:21.565975+00:00
-- url     : https://prove2.me/submissions/748673db-54f6-47ec-bd9c-23a565abed51

import Mathlib
import Definitions.Def_MasulloGRH_HeckeLFunction
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

open MasulloGRH

section HK1Helpers

variable {F : Type*} [Field F] [NumberField F]

lemma hk1_ideleSingle_mul (v : HeightOneSpectrum (𝓞 F)) (x y : (v.adicCompletion F)ˣ) :
    ideleSingle v (x * y) = ideleSingle v x * ideleSingle v y := by
  have h1 : finiteIdeleSingle v (x * y) = finiteIdeleSingle v x * finiteIdeleSingle v y := by
    unfold finiteIdeleSingle
    rw [RestrictedProduct.mulSingle_mul]
    exact map_mul _ _ _
  unfold ideleSingle
  rw [h1, show ((1 : (InfiniteAdeleRing F)ˣ), finiteIdeleSingle v x * finiteIdeleSingle v y)
    = (1, finiteIdeleSingle v x) * (1, finiteIdeleSingle v y) by simp]
  exact map_mul _ _ _

lemma hk1_ideleSingle_one (v : HeightOneSpectrum (𝓞 F)) :
    ideleSingle v 1 = 1 := by
  have h1 : finiteIdeleSingle v 1 = 1 := by
    unfold finiteIdeleSingle
    rw [RestrictedProduct.mulSingle_one]
    exact map_one _
  unfold ideleSingle
  rw [h1, show ((1 : (InfiniteAdeleRing F)ˣ), (1 : (FiniteAdeleRing (𝓞 F) F)ˣ)) = 1 from rfl]
  exact map_one _

noncomputable def hk1_ideleSingleHom (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ →* IdeleGroup F where
  toFun := ideleSingle v
  map_one' := hk1_ideleSingle_one v
  map_mul' := hk1_ideleSingle_mul v

noncomputable def hk1_lcHom (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ →* Circle :=
  χ.toMonoidHom.comp ((QuotientGroup.mk' _).comp (hk1_ideleSingleHom v))

lemma hk1_lc_eq (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    χ.localComponent v x = (hk1_lcHom χ v x : ℂ) := rfl

lemma hk1_lc_mul (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (x y : (v.adicCompletion F)ˣ) :
    χ.localComponent v (x * y) = χ.localComponent v x * χ.localComponent v y := by
  simp only [hk1_lc_eq, map_mul, Circle.coe_mul]

lemma hk1_lc_zpow (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (x : (v.adicCompletion F)ˣ) (k : ℤ) :
    χ.localComponent v (x ^ k) = χ.localComponent v x ^ k := by
  simp only [hk1_lc_eq, map_zpow, Circle.coe_zpow]

lemma hk1_lc_norm (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (x : (v.adicCompletion F)ˣ) : ‖χ.localComponent v x‖ = 1 := by
  rw [hk1_lc_eq]; exact Circle.norm_coe _

lemma hk1_norm_eq_zpow (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) (k : ℤ)
    (hx : Valued.v x = WithZero.exp k) :
    ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ k := by
  rw [FinitePlace.norm_def, hx]
  rw [WithZeroMulInt.toNNReal_neg_apply _ (by simp)]
  simp only [WithZero.exp, WithZero.unzero_coe, toAdd_ofAdd]
  push_cast; rfl

lemma hk1_exists_unif (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : (v.adicCompletion F)ˣ, IsUniformizerAt v π := by
  obtain ⟨x, hx⟩ := v.valuedAdicCompletion_surjective F (WithZero.exp (-1 : ℤ))
  have hx0 : x ≠ 0 := by
    intro h; rw [h, map_zero] at hx; exact WithZero.zero_ne_coe hx
  exact ⟨Units.mk0 x hx0, hx⟩

lemma hk1_one_lt_q (v : HeightOneSpectrum (𝓞 F)) : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

lemma hk1_key (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) (hχ : χ.IsUnramifiedAt v)
    (π : (v.adicCompletion F)ˣ) (hπ : IsUniformizerAt v π) (x : (v.adicCompletion F)ˣ) :
    ∃ k : ℤ, ‖(x : v.adicCompletion F)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ k ∧
      χ.localComponent v x = (χ.localComponent v π) ^ (-k) := by
  have hx0 : Valued.v (x : v.adicCompletion F) ≠ 0 := by simp
  set k := WithZero.log (Valued.v (x : v.adicCompletion F)) with hk
  have hxk : Valued.v (x : v.adicCompletion F) = WithZero.exp k := (WithZero.exp_log hx0).symm
  refine ⟨k, hk1_norm_eq_zpow v _ k hxk, ?_⟩
  have hu : Valued.v ((x * π ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hxk]
    unfold IsUniformizerAt at hπ
    rw [hπ, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have h1 := hχ _ hu
  rw [hk1_lc_mul, hk1_lc_zpow] at h1
  have hc : χ.localComponent v π ≠ 0 := by
    intro h; have := hk1_lc_norm χ v π; rw [h, norm_zero] at this; exact zero_ne_one this
  rw [zpow_neg]
  exact eq_inv_of_mul_eq_one_left h1

lemma hk1_ofReal_cpow_eq_exp (a : ℝ) (ha : 0 < a) (w : ℂ) :
    ((a : ℝ) : ℂ) ^ w = Complex.exp ((Real.log a : ℂ) * w) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ha.ne'), Complex.ofReal_log ha.le]

end HK1Helpers

theorem solution
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (hχ : χ.IsUnramifiedAt v) :
    ∃ t : ℝ,
      (∀ x : (v.adicCompletion F)ˣ,
        χ.localComponent v x = ((‖(x : v.adicCompletion F)‖ : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) ∧
      χ.primeValue v = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-((t : ℂ) * Complex.I)) ∧
      ∀ t' : ℝ,
        (∀ x : (v.adicCompletion F)ˣ,
          χ.localComponent v x = ((‖(x : v.adicCompletion F)‖ : ℝ) : ℂ) ^ ((t' : ℂ) * Complex.I)) ↔
        ∃ k : ℤ, t' = t + 2 * Real.pi * k / Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
  classical
  set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hqdef
  have hq1 : 1 < q := hk1_one_lt_q v
  have hq0 : 0 < q := by linarith
  set L := Real.log q with hL
  have hL0 : 0 < L := Real.log_pos hq1
  have hLne : (L : ℂ) ≠ 0 := by exact_mod_cast hL0.ne'
  have hqC : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = ((q : ℝ) : ℂ) := by simp [hqdef]
  obtain ⟨π0, hπ0⟩ := hk1_exists_unif v
  have hex : χ.IsUnramifiedAt v ∧ ∃ x : (v.adicCompletion F)ˣ, IsUniformizerAt v x :=
    ⟨hχ, π0, hπ0⟩
  have hπ : IsUniformizerAt v hex.2.choose := hex.2.choose_spec
  set π := hex.2.choose with hπdef
  have hpv : χ.primeValue v = χ.localComponent v π := by
    unfold HeckeCharacter.primeValue; rw [dif_pos hex]
  set c := χ.localComponent v π with hcdef
  set θ := Complex.arg c with hθ
  have hc : c = Complex.exp ((θ : ℂ) * Complex.I) := by
    have := Complex.norm_mul_exp_arg_mul_I c
    rw [hcdef, hk1_lc_norm] at this
    rw [← hθ] at this
    simpa using this.symm
  have hnπ : ‖(π : v.adicCompletion F)‖ = q ^ (-1 : ℤ) := hk1_norm_eq_zpow v _ (-1) hπ
  have hqpow : ∀ (k : ℤ) (w : ℂ),
      (((q ^ k : ℝ)) : ℂ) ^ w = Complex.exp ((k : ℂ) * ((L : ℂ) * w)) := by
    intro k w
    rw [hk1_ofReal_cpow_eq_exp _ (zpow_pos hq0 k), Real.log_zpow, ← hL]; push_cast; ring_nf
  have equiv : ∀ s : ℝ, (∀ x : (v.adicCompletion F)ˣ,
        χ.localComponent v x = ((‖(x : v.adicCompletion F)‖ : ℝ) : ℂ) ^ ((s : ℂ) * Complex.I)) ↔
        c = Complex.exp ((L : ℂ) * (-((s : ℂ) * Complex.I))) := by
    intro s
    constructor
    · intro h
      have h1 := h π
      rw [hnπ, hqpow] at h1
      rw [hcdef, h1]; congr 1; push_cast; ring
    · intro h x
      obtain ⟨k, hk1, hk2⟩ := hk1_key χ v hχ π hπ x
      rw [hk2, hk1, hqpow, ← hcdef, h, ← Complex.exp_int_mul]
      congr 1; push_cast; ring
  have ht : c = Complex.exp ((L : ℂ) * (-(((-θ / L : ℝ) : ℂ) * Complex.I))) := by
    rw [hc]; congr 1; push_cast; field_simp
  refine ⟨-θ / L, (equiv _).2 ht, ?_, ?_⟩
  · rw [hpv, ht, hqC, hk1_ofReal_cpow_eq_exp _ hq0]
  · intro t'
    rw [equiv t', ht, Complex.exp_eq_exp_iff_exists_int]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have him := congrArg Complex.im hn
      simp at him
      have hθL : L * (-θ / L) = -θ := by field_simp
      rw [hθL] at him
      field_simp
      linarith
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [hk]
      push_cast
      field_simp
      ring
