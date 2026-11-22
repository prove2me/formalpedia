-- Prove2me | solution 1 for MasulloGRH.localComponentInfinite_eq_archParameters
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:22:49.017032+00:00
-- url     : https://prove2.me/submissions/ddc1f14b-991d-4219-897d-b413c34919e7

import Mathlib
import Definitions.Def_MasulloGRH_CompletedL
import Theorems.Thm_LanglandsTunnell_ArchPlace_forall_continuous_exists_eq_realCharFun_and_forall_continuous_exists_eq_complexCharFun

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace Sol_MasulloGRH_localComponentInfinite_eq_archParameters

open MasulloGRH

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

open Classical in
theorem val_ideleSingleInfinite (w : InfinitePlace F) (x : (w.Completion)ˣ) :
    ((ideleSingleInfinite w x : IdeleGroup F) : AdeleRing (𝓞 F) F) =
      ((Pi.mulSingle w (x : w.Completion), 1) :
        InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) := by
  refine Prod.ext ?_ ?_
  · funext v
    show ((Pi.mulSingle (M := fun v : InfinitePlace F => (v.Completion)ˣ) w x v : (v.Completion)ˣ) :
      v.Completion) = Pi.mulSingle (M := fun v : InfinitePlace F => v.Completion) w
        (x : w.Completion) v
    by_cases h : v = w
    · subst h; simp
    · simp [h]
  · rfl

theorem ideleSingleInfinite_mul (w : InfinitePlace F) (x y : (w.Completion)ˣ) :
    ideleSingleInfinite w (x * y) = ideleSingleInfinite w x * ideleSingleInfinite w y := by
  classical
  exact map_mul (MulEquiv.prodUnits.symm.toMonoidHom.comp ((MonoidHom.inl _ _).comp
    (MulEquiv.piUnits.symm.toMonoidHom.comp
      (MonoidHom.mulSingle (fun v : InfinitePlace F => (v.Completion)ˣ) w)))) x y

theorem ideleSingleInfinite_one (w : InfinitePlace F) :
    ideleSingleInfinite w 1 = 1 := by
  classical
  exact map_one (MulEquiv.prodUnits.symm.toMonoidHom.comp ((MonoidHom.inl _ _).comp
    (MulEquiv.piUnits.symm.toMonoidHom.comp
      (MonoidHom.mulSingle (fun v : InfinitePlace F => (v.Completion)ˣ) w))))

theorem ideleSingleInfinite_inv (w : InfinitePlace F) (x : (w.Completion)ˣ) :
    ideleSingleInfinite w x⁻¹ = (ideleSingleInfinite w x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← ideleSingleInfinite_mul, inv_mul_cancel, ideleSingleInfinite_one]

theorem continuous_ideleSingleInfinite (w : InfinitePlace F) :
    Continuous (ideleSingleInfinite w) := by
  classical
  rw [Units.continuous_iff]
  constructor
  · have : (Units.val ∘ ideleSingleInfinite w) = fun x : (w.Completion)ˣ =>
        ((Pi.mulSingle w (x : w.Completion),
          (1 : FiniteAdeleRing (𝓞 F) F)) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) :=
      funext (val_ideleSingleInfinite w)
    rw [this]
    exact Continuous.prodMk ((continuous_mulSingle w).comp Units.continuous_val) continuous_const
  · have : (fun x : (w.Completion)ˣ => (((ideleSingleInfinite w x)⁻¹ : IdeleGroup F) :
        AdeleRing (𝓞 F) F)) = fun x : (w.Completion)ˣ =>
          ((Pi.mulSingle w ((x⁻¹ : (w.Completion)ˣ) : w.Completion),
            (1 : FiniteAdeleRing (𝓞 F) F)) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) := by
      funext x
      rw [← val_ideleSingleInfinite, ideleSingleInfinite_inv]
    rw [this]
    exact Continuous.prodMk ((continuous_mulSingle w).comp
      (Units.continuous_val.comp continuous_inv)) continuous_const

/-- `x ↦ j_w(x)` as a monoid homomorphism. -/
def ideleSingleInfiniteHom (w : InfinitePlace F) : (w.Completion)ˣ →* IdeleGroup F where
  toFun := ideleSingleInfinite w
  map_one' := ideleSingleInfinite_one w
  map_mul' := ideleSingleInfinite_mul w

/-- The local component `χ_w` as a monoid homomorphism to `ℂˣ`. -/
def lc (χ : HeckeCharacter F) (w : InfinitePlace F) : (w.Completion)ˣ →* ℂˣ :=
  Circle.toUnits.comp (χ.toMonoidHom.comp
    ((QuotientGroup.mk' (principalIdeles F)).comp (ideleSingleInfiniteHom w)))

theorem lc_apply (χ : HeckeCharacter F) (w : InfinitePlace F) (x : (w.Completion)ˣ) :
    ((lc χ w x : ℂˣ) : ℂ) = χ.localComponentInfinite w x := rfl

theorem continuous_localComponentInfinite (χ : HeckeCharacter F) (w : InfinitePlace F) :
    Continuous (χ.localComponentInfinite w) := by
  unfold HeckeCharacter.localComponentInfinite
  exact continuous_subtype_val.comp (χ.continuous.comp
    (QuotientGroup.continuous_mk.comp (continuous_ideleSingleInfinite w)))

theorem continuous_lc (χ : HeckeCharacter F) (w : InfinitePlace F) : Continuous (lc χ w) := by
  rw [Units.continuous_iff]
  refine ⟨continuous_localComponentInfinite χ w, ?_⟩
  have : (fun x : (w.Completion)ˣ => (((lc χ w x)⁻¹ : ℂˣ) : ℂ)) =
      fun x => χ.localComponentInfinite w x⁻¹ := by
    funext x; rw [← map_inv]; rfl
  rw [this]
  exact (continuous_localComponentInfinite χ w).comp continuous_inv

theorem norm_localComponentInfinite (χ : HeckeCharacter F) (w : InfinitePlace F)
    (x : (w.Completion)ˣ) : ‖χ.localComponentInfinite w x‖ = 1 :=
  Circle.norm_coe _

theorem norm_eq_norm_extensionEmbedding (w : InfinitePlace F) (x : w.Completion) :
    ‖InfinitePlace.Completion.extensionEmbedding w x‖ = ‖x‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

theorem exists_unit_extensionEmbedding_eq (w : InfinitePlace F) (r : ℝ) (hr : r ≠ 0) :
    ∃ x : (w.Completion)ˣ, InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) =
      (r : ℂ) := by
  rcases w.isReal_or_isComplex with hw | hw
  · obtain ⟨y, hy⟩ := InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal hw r
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy; exact hr (by exact_mod_cast hy.symm)
    refine ⟨Units.mk0 y hy0, ?_⟩
    rw [Units.val_mk0, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, hy]
  · obtain ⟨y, hy⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw
      (r : ℂ)
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy; exact hr (by exact_mod_cast hy.symm)
    exact ⟨Units.mk0 y hy0, hy⟩

/-- `t ↦ (s ↦ s^{it})` is injective on the positive reals, even after composing with `r ↦ r^m`. -/
theorem cpow_I_injective (m : ℕ) (hm : 0 < m) (t t' : ℝ)
    (h : ∀ r : ℝ, 0 < r → ((r ^ m : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) =
      ((r ^ m : ℝ) : ℂ) ^ ((t' : ℂ) * Complex.I)) : t = t' := by
  by_contra hne
  have hd : t - t' ≠ 0 := sub_ne_zero.mpr hne
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  set r : ℝ := Real.exp (Real.pi / (m * (t - t'))) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hlog : Real.log (r ^ m) = Real.pi / (t - t') := by
    rw [Real.log_pow, hr, Real.log_exp]; field_simp
  have hpos : (0 : ℝ) < r ^ m := pow_pos hr0 m
  have h1 := h r hr0
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'),
    ← Complex.ofReal_log hpos.le, hlog, Complex.exp_eq_exp_iff_exists_int] at h1
  obtain ⟨n, hn⟩ := h1
  have h2 : ((Real.pi / (t - t') * t : ℝ) : ℂ) * Complex.I =
      ((Real.pi / (t - t') * t' + n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
    push_cast at hn ⊢; linear_combination hn
  have h3 := mul_right_cancel₀ Complex.I_ne_zero h2
  have h4 : Real.pi / (t - t') * t = Real.pi / (t - t') * t' + n * (2 * Real.pi) :=
    Complex.ofReal_injective h3
  have h5 : Real.pi = n * (2 * Real.pi) := by
    have : Real.pi / (t - t') * t - Real.pi / (t - t') * t' = Real.pi := by
      field_simp
    linarith
  have h6 : (1 : ℝ) = 2 * n := by
    have := Real.pi_pos
    nlinarith
  have h7 : (1 : ℤ) = 2 * n := by exact_mod_cast h6
  omega

/-- `n ↦ (z ↦ z^n)` is injective on the unit circle. -/
theorem zpow_unit_injective (n n' : ℤ) (h : ∀ z : ℂ, ‖z‖ = 1 → z ^ n = z ^ n') : n = n' := by
  by_contra hne
  have hd : n - n' ≠ 0 := sub_ne_zero.mpr hne
  set z : ℂ := Complex.exp ((Real.pi / (n - n' : ℤ) : ℝ) * Complex.I) with hz
  have hz1 : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have h1 : z ^ (n - n') = 1 := by
    rw [zpow_sub₀ hz0, h z hz1, div_self (zpow_ne_zero _ hz0)]
  have h2 : z ^ (n - n') = -1 := by
    rw [hz, ← Complex.exp_int_mul]
    have hd' : ((n - n' : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hd
    have : (((n - n' : ℤ) : ℂ) * (((Real.pi / (n - n' : ℤ) : ℝ) : ℂ) * Complex.I)) =
        (Real.pi : ℂ) * Complex.I := by
      push_cast
      push_cast at hd'
      field_simp
    rw [this, Complex.exp_pi_mul_I]
  rw [h1] at h2
  norm_num at h2

local notation "ι" => InfinitePlace.Completion.extensionEmbedding

theorem archExponent_eq_of (χ : HeckeCharacter F) (w : InfinitePlace F) (t : ℝ)
    (hP : ∀ x : (w.Completion)ˣ, (ι w (x : w.Completion)).im = 0 →
      0 < (ι w (x : w.Completion)).re →
      χ.localComponentInfinite w x =
        ((‖(x : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ (t * Complex.I)) :
    χ.archExponent w = t := by
  classical
  have hex : ∃ t : ℝ, ∀ x : (w.Completion)ˣ,
      (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)).im = 0 →
      0 < (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)).re →
      χ.localComponentInfinite w x =
        ((‖(x : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ (t * Complex.I) := ⟨t, hP⟩
  unfold HeckeCharacter.archExponent
  rw [dif_pos hex]
  have hspec := hex.choose_spec
  apply cpow_I_injective w.mult InfinitePlace.mult_pos
  intro r hr
  obtain ⟨x, hx⟩ := exists_unit_extensionEmbedding_eq w r hr.ne'
  have hnx : ‖(x : w.Completion)‖ = r := by
    rw [← norm_eq_norm_extensionEmbedding, hx, Complex.norm_real, Real.norm_of_nonneg hr.le]
  have him : (ι w (x : w.Completion)).im = 0 := by rw [hx, Complex.ofReal_im]
  have hre : 0 < (ι w (x : w.Completion)).re := by rw [hx, Complex.ofReal_re]; exact hr
  rw [← hnx, ← hspec x him hre, hP x him hre]

theorem archParity_eq_of (χ : HeckeCharacter F) (w : InfinitePlace F) (a : ℕ) (ha : a ≤ 1)
    (h : χ.localComponentInfinite w (-1) = (-1 : ℂ) ^ a) : χ.archParity w = a := by
  classical
  unfold HeckeCharacter.archParity
  interval_cases a
  · simp [h]
  · rw [if_neg]
    rw [h]; norm_num

theorem zpow_eq_of_unit (χ : HeckeCharacter F) (w : InfinitePlace F) (hw : w.IsComplex)
    (n m : ℤ)
    (hn : ∀ x : (w.Completion)ˣ, ‖(x : w.Completion)‖ = 1 →
      χ.localComponentInfinite w x = (ι w (x : w.Completion)) ^ n)
    (hm : ∀ x : (w.Completion)ˣ, ‖(x : w.Completion)‖ = 1 →
      χ.localComponentInfinite w x = (ι w (x : w.Completion)) ^ m) : n = m := by
  apply zpow_unit_injective
  intro z hz
  obtain ⟨y, hy⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw z
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    rw [← hy, norm_zero] at hz
    exact zero_ne_one hz
  have hnx : ‖((Units.mk0 y hy0 : (w.Completion)ˣ) : w.Completion)‖ = 1 := by
    rw [Units.val_mk0, ← norm_eq_norm_extensionEmbedding, hy, hz]
  have h1 := hn (Units.mk0 y hy0) hnx
  have h2 := hm (Units.mk0 y hy0) hnx
  rw [Units.val_mk0, hy] at h1 h2
  rw [← h1, h2]

theorem archWeight_eq_of (χ : HeckeCharacter F) (w : InfinitePlace F) (hw : w.IsComplex)
    (n : ℤ)
    (hn : ∀ x : (w.Completion)ˣ, ‖(x : w.Completion)‖ = 1 →
      χ.localComponentInfinite w x = (ι w (x : w.Completion)) ^ n) :
    χ.archWeight w = n.natAbs := by
  classical
  have hex : ∃ n : ℤ, ∀ x : (w.Completion)ˣ, ‖(x : w.Completion)‖ = 1 →
      χ.localComponentInfinite w x =
        (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)) ^ n := ⟨n, hn⟩
  unfold HeckeCharacter.archWeight
  rw [dif_pos hex]
  rw [zpow_eq_of_unit χ w hw _ n hex.choose_spec hn]

theorem cpow_two_mul (r : ℝ) (hr : 0 < r) (z : ℂ) :
    (r : ℂ) ^ (2 * z) = ((r ^ 2 : ℝ) : ℂ) ^ z := by
  have hr2 : (0 : ℝ) < r ^ 2 := pow_pos hr 2
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hr2.ne'),
    ← Complex.ofReal_log hr.le, ← Complex.ofReal_log hr2.le, Real.log_pow]
  push_cast
  ring_nf

theorem re_eq_zero_of_norm_cpow (r : ℝ) (hr : 1 < r) (u : ℂ) (h : ‖(r : ℂ) ^ u‖ = 1) :
    u.re = 0 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)] at h
  have h1 := congrArg Real.log h
  rw [Real.log_rpow (by linarith), Real.log_one] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact h2
  · exact absurd h2 (Real.log_pos hr).ne'

theorem real_exists (χ : HeckeCharacter F) (w : InfinitePlace F) (hw : w.IsReal) :
    ∃ (a : ℕ) (t : ℝ), a ≤ 1 ∧ ∀ x : (w.Completion)ˣ,
      χ.localComponentInfinite w x =
        (if 0 < (ι w (x : w.Completion)).re then 1 else (-1 : ℂ) ^ a) *
          ((‖(x : w.Completion)‖ : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) := by
  set e : w.Completion ≃+* ℝ := InfinitePlace.Completion.ringEquivRealOfIsReal hw with he
  set ψ : ℝˣ →* ℂˣ := (lc χ w).comp (Units.map e.symm.toRingHom.toMonoidHom) with hψ
  have hec : Continuous (e.symm.toRingHom.toMonoidHom : ℝ → w.Completion) :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous
  have hψc : Continuous ψ := (continuous_lc χ w).comp (Units.continuous_map hec)
  obtain ⟨u, a, hu⟩ :=
    LanglandsTunnell.ArchPlace.forall_continuous_exists_eq_realCharFun_and_forall_continuous_exists_eq_complexCharFun.1
      ψ hψc
  -- the value of `χ_w` in terms of `e x`
  have hval : ∀ x : (w.Completion)ˣ, χ.localComponentInfinite w x =
      ((‖e (x : w.Completion)‖ : ℝ) : ℂ) ^ u *
        (((e (x : w.Completion)) / ‖e (x : w.Completion)‖ : ℝ) : ℂ) ^ a.val := by
    intro x
    have h1 : ψ (Units.map e.toRingHom.toMonoidHom x) = lc χ w x := by
      rw [hψ, MonoidHom.comp_apply]
      congr 1
      ext
      simp
    rw [← lc_apply, ← h1, hu]
    simp [LanglandsTunnell.ArchPlace.realCharFun, LanglandsTunnell.ArchPlace.realSign]
  have hιe : ∀ y : w.Completion, ι w y = ((e y : ℝ) : ℂ) := fun y =>
    (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw y).symm
  have hne : ∀ y : w.Completion, ‖e y‖ = ‖y‖ := fun y =>
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) y
  -- `Re u = 0`
  have hure : u.re = 0 := by
    obtain ⟨x, hx⟩ := exists_unit_extensionEmbedding_eq w 2 two_ne_zero
    have hx' : e (x : w.Completion) = 2 := by
      rw [hιe] at hx; exact_mod_cast hx
    have h1 := norm_localComponentInfinite χ w x
    rw [hval x, hx'] at h1
    norm_num at h1
    exact re_eq_zero_of_norm_cpow 2 one_lt_two u (by exact_mod_cast h1)
  have hu' : u = (u.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hure]
  refine ⟨a.val, u.im, Nat.lt_succ_iff.mp (ZMod.val_lt a), fun x => ?_⟩
  rw [hval x, hιe, Complex.ofReal_re, hne, ← hu']
  have hx0 : e (x : w.Completion) ≠ 0 := by
    rw [map_ne_zero_iff _ e.injective]; exact x.ne_zero
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le)]
    have : e (x : w.Completion) / ‖(x : w.Completion)‖ = -1 := by
      rw [← hne, Real.norm_eq_abs, abs_of_neg hneg, div_neg, div_self hx0]
    rw [this]; push_cast; ring
  · rw [if_pos hpos]
    have : e (x : w.Completion) / ‖(x : w.Completion)‖ = 1 := by
      rw [← hne, Real.norm_eq_abs, abs_of_pos hpos, div_self hx0]
    rw [this]; push_cast; ring

theorem complex_exists (χ : HeckeCharacter F) (w : InfinitePlace F) (hw : w.IsComplex) :
    ∃ (n : ℤ) (t : ℝ), ∀ x : (w.Completion)ˣ,
      χ.localComponentInfinite w x =
        (ι w (x : w.Completion) / ((‖(x : w.Completion)‖ : ℝ) : ℂ)) ^ n *
          ((‖(x : w.Completion)‖ ^ 2 : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) := by
  set e : w.Completion ≃+* ℂ := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw with he
  set ψ : ℂˣ →* ℂˣ := (lc χ w).comp (Units.map e.symm.toRingHom.toMonoidHom) with hψ
  have hec : Continuous (e.symm.toRingHom.toMonoidHom : ℂ → w.Completion) :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.continuous
  have hψc : Continuous ψ := (continuous_lc χ w).comp (Units.continuous_map hec)
  obtain ⟨u, k, hu⟩ :=
    LanglandsTunnell.ArchPlace.forall_continuous_exists_eq_realCharFun_and_forall_continuous_exists_eq_complexCharFun.2
      ψ hψc
  have hne : ∀ y : w.Completion, ‖ι w y‖ = ‖y‖ := norm_eq_norm_extensionEmbedding w
  have hval : ∀ x : (w.Completion)ˣ, χ.localComponentInfinite w x =
      ((‖(x : w.Completion)‖ : ℝ) : ℂ) ^ (2 * u) *
        (ι w (x : w.Completion) / ((‖(x : w.Completion)‖ : ℝ) : ℂ)) ^ k := by
    intro x
    have h1 : ψ (Units.map e.toRingHom.toMonoidHom x) = lc χ w x := by
      rw [hψ, MonoidHom.comp_apply]
      congr 1
      ext
      simp
    rw [← lc_apply, ← h1, hu, LanglandsTunnell.ArchPlace.complexCharFun_apply,
      LanglandsTunnell.ArchPlace.anglePhase]
    have h2 : ((Units.map e.toRingHom.toMonoidHom x : ℂˣ) : ℂ) = ι w (x : w.Completion) := rfl
    rw [h2, hne]
  have hure : u.re = 0 := by
    obtain ⟨x, hx⟩ := exists_unit_extensionEmbedding_eq w 2 two_ne_zero
    have hnx : ‖(x : w.Completion)‖ = 2 := by
      rw [← hne, hx]; norm_num
    have h1 := norm_localComponentInfinite χ w x
    rw [hval x, hx, hnx] at h1
    norm_num at h1
    have h3 := re_eq_zero_of_norm_cpow 2 one_lt_two (2 * u) (by exact_mod_cast h1)
    simpa using h3
  have hu' : u = (u.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hure]
  refine ⟨k, u.im, fun x => ?_⟩
  rw [hval x, mul_comm, ← hu', cpow_two_mul _ (norm_pos_iff.mpr x.ne_zero)]

theorem real_unique (χ : HeckeCharacter F) (w : InfinitePlace F) (hw : w.IsReal) (a : ℕ) (t : ℝ)
    (ha : a ≤ 1) (hf : ∀ x : (w.Completion)ˣ,
      χ.localComponentInfinite w x =
        (if 0 < (ι w (x : w.Completion)).re then 1 else (-1 : ℂ) ^ a) *
          ((‖(x : w.Completion)‖ : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) :
    a = χ.archParity w ∧ t = χ.archExponent w := by
  constructor
  · refine (archParity_eq_of χ w a ha ?_).symm
    rw [hf (-1)]
    simp
  · refine (archExponent_eq_of χ w t ?_).symm
    intro x _ hre
    rw [hf x, if_pos hre, hw.mult_eq_one, pow_one, one_mul]

theorem complex_P (χ : HeckeCharacter F) (w : InfinitePlace F) (hw : w.IsComplex) (n : ℤ) (t : ℝ)
    (hf : ∀ x : (w.Completion)ˣ,
      χ.localComponentInfinite w x =
        (ι w (x : w.Completion) / ((‖(x : w.Completion)‖ : ℝ) : ℂ)) ^ n *
          ((‖(x : w.Completion)‖ ^ 2 : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) :
    χ.archExponent w = t := by
  refine archExponent_eq_of χ w t ?_
  intro x him hre
  have hx : ι w (x : w.Completion) = (((ι w (x : w.Completion)).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hnx : ‖(x : w.Completion)‖ = (ι w (x : w.Completion)).re := by
    rw [← norm_eq_norm_extensionEmbedding]
    conv_lhs => rw [hx]
    rw [Complex.norm_real, Real.norm_of_nonneg hre.le]
  have h1 : ι w (x : w.Completion) / ((‖(x : w.Completion)‖ : ℝ) : ℂ) = 1 := by
    rw [hnx, ← hx]
    apply div_self
    rw [hx]; exact_mod_cast hre.ne'
  rw [hf x, h1, one_zpow, one_mul, hw.mult_eq_two]

theorem complex_Q (χ : HeckeCharacter F) (w : InfinitePlace F) (n : ℤ) (t : ℝ)
    (hf : ∀ x : (w.Completion)ˣ,
      χ.localComponentInfinite w x =
        (ι w (x : w.Completion) / ((‖(x : w.Completion)‖ : ℝ) : ℂ)) ^ n *
          ((‖(x : w.Completion)‖ ^ 2 : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) :
    ∀ x : (w.Completion)ˣ, ‖(x : w.Completion)‖ = 1 →
      χ.localComponentInfinite w x = (ι w (x : w.Completion)) ^ n := by
  intro x hx
  rw [hf x, hx]
  simp

end

end Sol_MasulloGRH_localComponentInfinite_eq_archParameters

open Sol_MasulloGRH_localComponentInfinite_eq_archParameters in
open MasulloGRH in
theorem solution
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) (w : InfinitePlace F) :
    (w.IsReal →
      (∀ x : (w.Completion)ˣ,
        χ.localComponentInfinite w x =
          (if 0 < (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)).re then 1
            else (-1 : ℂ) ^ χ.archParity w) *
          ((‖(x : w.Completion)‖ : ℝ) : ℂ) ^ ((χ.archExponent w : ℂ) * Complex.I)) ∧
      ∀ (a : ℕ) (t : ℝ), a ≤ 1 →
        (∀ x : (w.Completion)ˣ,
          χ.localComponentInfinite w x =
            (if 0 < (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)).re then 1
              else (-1 : ℂ) ^ a) *
            ((‖(x : w.Completion)‖ : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) →
        a = χ.archParity w ∧ t = χ.archExponent w) ∧
    (w.IsComplex →
      ∃ n : ℤ, n.natAbs = χ.archWeight w ∧
        (∀ x : (w.Completion)ˣ,
          χ.localComponentInfinite w x =
            (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) /
                ((‖(x : w.Completion)‖ : ℝ) : ℂ)) ^ n *
              ((‖(x : w.Completion)‖ ^ 2 : ℝ) : ℂ) ^ ((χ.archExponent w : ℂ) * Complex.I)) ∧
        ∀ (m : ℤ) (t : ℝ),
          (∀ x : (w.Completion)ˣ,
            χ.localComponentInfinite w x =
              (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) /
                  ((‖(x : w.Completion)‖ : ℝ) : ℂ)) ^ m *
                ((‖(x : w.Completion)‖ ^ 2 : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) →
          m = n ∧ t = χ.archExponent w) := by
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · obtain ⟨a, t, ha, hf⟩ := real_exists χ w hw
    obtain ⟨h1, h2⟩ := real_unique χ w hw a t ha hf
    refine ⟨?_, fun a' t' ha' hf' => real_unique χ w hw a' t' ha' hf'⟩
    rw [← h1, ← h2]
    exact hf
  · obtain ⟨n, t, hf⟩ := complex_exists χ w hw
    have ht : χ.archExponent w = t := complex_P χ w hw n t hf
    refine ⟨n, (archWeight_eq_of χ w hw n (complex_Q χ w n t hf)).symm, ?_, ?_⟩
    · rw [ht]; exact hf
    · intro m t' hf'
      exact ⟨zpow_eq_of_unit χ w hw m n (complex_Q χ w m t' hf') (complex_Q χ w n t hf),
        (complex_P χ w hw m t' hf').symm⟩
