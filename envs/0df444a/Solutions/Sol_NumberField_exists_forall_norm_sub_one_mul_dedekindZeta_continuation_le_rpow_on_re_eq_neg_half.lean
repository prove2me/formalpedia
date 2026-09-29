-- Prove2me | solution 1 for NumberField.exists_forall_norm_sub_one_mul_dedekindZeta_continuation_le_rpow_on_re_eq_neg_half
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/1577907e-c882-567c-a7cc-10df38bbfece

import Mathlib
import Theorems.Thm_NumberField_exists_completedDedekindZeta_package
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
import Theorems.Thm_EulerProduct_norm_tprod_inv_one_sub_mul_natCast_cpow_neg_le_exp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_forall_norm_sub_one_mul_dedekindZeta_continuation_le_rpow_on_re_eq_neg_half

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Complex Filter Set
open scoped Topology ComplexConjugate

namespace R4Z2b

theorem conj_two : conj (2 : ℂ) = 2 := map_ofNat _ 2

theorem Gammaℝ_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  rw [Gammaℝ_def, Gammaℝ_def, map_mul, ← Complex.Gamma_conj]
  have harg : ((Real.pi : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_ne_zero.symm
  have h1 : -conj s / 2 = conj (-s / 2) := by
    rw [map_div₀, map_neg, conj_two]
  have h2 : conj s / 2 = conj (s / 2) := by
    rw [map_div₀, conj_two]
  rw [h1, h2, Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

theorem Gammaℂ_conj (s : ℂ) : Gammaℂ (conj s) = conj (Gammaℂ s) := by
  rw [Gammaℂ_def, Gammaℂ_def, map_mul, map_mul, ← Complex.Gamma_conj, conj_two]
  have harg : ((2 : ℂ) * (Real.pi : ℝ)).arg ≠ Real.pi := by
    have : (2 : ℂ) * (Real.pi : ℝ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.arg_ofReal_of_nonneg (by positivity)]; exact Real.pi_ne_zero.symm
  have h2 : conj ((2 : ℂ) * (Real.pi : ℝ)) = (2 : ℂ) * (Real.pi : ℝ) := by
    rw [map_mul, conj_two, Complex.conj_ofReal]
  have h3 : -conj s = conj (-s) := by rw [map_neg]
  rw [h3, Complex.cpow_conj _ _ harg, h2]

theorem one_sub_eq_conj (s : ℂ) (hs : s.re = -1 / 2) : 1 - s = conj (s + 2) := by
  apply Complex.ext
  · simp [hs]; norm_num
  · simp

theorem ne_zero_of_re (s : ℂ) (hs : s.re = -1 / 2) : s ≠ 0 := by
  intro h; rw [h] at hs; norm_num at hs

theorem add_one_ne_zero_of_re (s : ℂ) (hs : s.re = -1 / 2) : s + 1 ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [hs] at this; norm_num at this

theorem ne_one_of_re (s : ℂ) (hs : s.re = -1 / 2) : s ≠ 1 := by
  intro h; rw [h] at hs; norm_num at hs

theorem Gammaℝ_ne_zero_of_re (s : ℂ) (hs : s.re = -1 / 2) : Gammaℝ s ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff, not_exists]
  intro n h
  have := congrArg Complex.re h
  simp [hs] at this
  have h2 : (2 : ℝ) * n = 1 / 2 := by linarith
  have h3 : (4 : ℝ) * n = 1 := by linarith
  have h4 : (4 * n : ℕ) = 1 := by exact_mod_cast h3
  omega

theorem Gamma_ne_zero_of_re (s : ℂ) (hs : s.re = -1 / 2) : Gamma s ≠ 0 := by
  refine Complex.Gamma_ne_zero fun m h => ?_
  have := congrArg Complex.re h
  simp [hs] at this
  have h2 : (2 : ℝ) * m = 1 := by linarith
  have h3 : (2 * m : ℕ) = 1 := by exact_mod_cast h2
  omega

theorem Gammaℂ_ne_zero_of_re (s : ℂ) (hs : s.re = -1 / 2) : Gammaℂ s ≠ 0 := by
  rw [Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero_of_re s hs)
  rw [Ne, cpow_eq_zero_iff, not_and_or]
  left
  exact mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)

theorem norm_Gammaℝ_one_sub (s : ℂ) (hs : s.re = -1 / 2) :
    ‖Gammaℝ (1 - s)‖ = ‖Gammaℝ s‖ * ‖s‖ / (2 * Real.pi) := by
  rw [one_sub_eq_conj s hs, Gammaℝ_conj, Complex.norm_conj, Gammaℝ_add_two (ne_zero_of_re s hs)]
  rw [norm_div, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  simp only [Complex.norm_ofNat]
  ring

theorem norm_Gammaℂ_one_sub (s : ℂ) (hs : s.re = -1 / 2) :
    ‖Gammaℂ (1 - s)‖ = ‖Gammaℂ s‖ * ‖s‖ * ‖s + 1‖ / (2 * Real.pi) ^ 2 := by
  rw [one_sub_eq_conj s hs, Gammaℂ_conj, Complex.norm_conj]
  have h1 : s + 2 = (s + 1) + 1 := by ring
  rw [h1, Gammaℂ_add_one (add_one_ne_zero_of_re s hs), Gammaℂ_add_one (ne_zero_of_re s hs)]
  rw [norm_div, norm_div, norm_mul, norm_div, norm_div, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  simp only [Complex.norm_ofNat]
  ring

section zeta
variable (K : Type) [Field K] [NumberField K]

theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

def Mζ : ℝ := Real.exp (2 * ∑' v : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))

theorem Mζ_pos : 0 < Mζ K := Real.exp_pos _

theorem norm_dedekindZeta_le (s : ℂ) (hs : 3 / 2 ≤ s.re) : ‖dedekindZeta K s‖ ≤ Mζ K := by
  have hs1 : 1 < s.re := by linarith
  have hprod := (NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta K s hs1).tprod_eq
  have hsum : Summable fun v : HeightOneSpectrum (𝓞 K) => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s.re) :=
    NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt K hs1
  have h := EulerProduct.norm_tprod_inv_one_sub_mul_natCast_cpow_neg_le_exp
    (fun v : HeightOneSpectrum (𝓞 K) => Ideal.absNorm v.asIdeal) (two_le_absNorm K)
    (fun _ => (1 : ℂ)) (fun _ => by rw [norm_one]) s hs1.le hsum
  simp only [one_mul] at h
  rw [← hprod]
  refine h.trans ?_
  unfold Mζ
  rw [Real.exp_le_exp]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine Summable.tsum_le_tsum (fun v => ?_) hsum
    (NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt K (by norm_num))
  have h1 : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    have := two_le_absNorm K v
    exact_mod_cast (by omega : 1 ≤ Ideal.absNorm v.asIdeal)
  exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)

end zeta

section ident
variable (K : Type) [Field K] [NumberField K]

def D : ℝ := ((|NumberField.discr K| : ℤ) : ℝ)

theorem D_pos : 0 < D K := by
  unfold D
  exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero K)

theorem D_cast : (((|NumberField.discr K| : ℤ)) : ℂ) = ((D K : ℝ) : ℂ) := by
  unfold D; exact (Complex.ofReal_intCast _).symm

theorem one_le_D : 1 ≤ D K := by
  unfold D
  have h := NumberField.discr_ne_zero K
  have : (1 : ℤ) ≤ |NumberField.discr K| := Int.one_le_abs h
  exact_mod_cast this

def invGammaFactor (s : ℂ) : ℂ :=
  (((D K : ℝ) : ℂ) ^ (s / 2))⁻¹ * (Gammaℝ s)⁻¹ ^ NumberField.InfinitePlace.nrRealPlaces K *
    (Gammaℂ s)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K

theorem differentiable_Gammaℂ_inv : Differentiable ℂ (fun s : ℂ => (Gammaℂ s)⁻¹) := by
  have : (fun s : ℂ => (Gammaℂ s)⁻¹) = fun s => (Gammaℝ s)⁻¹ * (Gammaℝ (s + 1))⁻¹ := by
    funext s; rw [← Gammaℝ_mul_Gammaℝ_add_one, mul_inv]
  rw [this]
  exact differentiable_Gammaℝ_inv.mul (differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1))

theorem differentiable_invGammaFactor : Differentiable ℂ (invGammaFactor K) := by
  unfold invGammaFactor
  refine ((Differentiable.inv ?_ ?_).mul (differentiable_Gammaℝ_inv.pow _)).mul
    (differentiable_Gammaℂ_inv.pow _)
  · exact Differentiable.const_cpow (differentiable_id.div_const 2)
      (Or.inl (ofReal_ne_zero.mpr (D_pos K).ne'))
  · intro s
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl (ofReal_ne_zero.mpr (D_pos K).ne')

theorem isOpen_compl01 : IsOpen ({(0 : ℂ), 1}ᶜ : Set ℂ) :=
  (Set.toFinite _).isClosed.isOpen_compl

theorem isPreconnected_compl01 : IsPreconnected ({(0 : ℂ), 1}ᶜ : Set ℂ) := by
  have hc : ({(0 : ℂ), 1} : Set ℂ).Countable := (Set.toFinite _).countable
  have hr : 1 < Module.rank ℝ ℂ := by simp
  exact (hc.isConnected_compl_of_one_lt_rank hr).isPreconnected

theorem R_eq (R : ℂ → ℂ) (hR : Differentiable ℂ R)
    (hRζ : ∀ s : ℂ, 1 < s.re → R s = (s - 1) * NumberField.dedekindZeta K s)
    (Λ : ℂ → ℂ) (hΛd : DifferentiableOn ℂ Λ ({(0 : ℂ), 1}ᶜ))
    (hΛeq : ∀ s : ℂ, 1 < s.re → Λ s =
        (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2)
          * Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K
          * Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K
          * NumberField.dedekindZeta K s) :
    Set.EqOn R (fun s => (s - 1) * Λ s * invGammaFactor K s) ({(0 : ℂ), 1}ᶜ) := by
  set g : ℂ → ℂ := fun s => (s - 1) * Λ s * invGammaFactor K s with hg
  have hRan : AnalyticOnNhd ℂ R ({(0 : ℂ), 1}ᶜ) := (hR.differentiableOn).analyticOnNhd (isOpen_compl01)
  have hgd : DifferentiableOn ℂ g ({(0 : ℂ), 1}ᶜ) :=
    (((differentiable_id.sub_const 1).differentiableOn).mul hΛd).mul
      (differentiable_invGammaFactor K).differentiableOn
  have hgan : AnalyticOnNhd ℂ g ({(0 : ℂ), 1}ᶜ) := hgd.analyticOnNhd isOpen_compl01
  have h2mem : (2 : ℂ) ∈ ({(0 : ℂ), 1}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    norm_num

  have hVopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have hagree : ∀ s : ℂ, 1 < s.re → R s = g s := by
    intro s hs
    have hs0 : 0 < s.re := by linarith
    have hΓℝ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs0
    have hΓℂ : Gammaℂ s ≠ 0 := by
      rw [Gammaℂ_def]
      refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos hs0)
      rw [Ne, cpow_eq_zero_iff, not_and_or]
      exact Or.inl (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero))
    have hD : ((D K : ℝ) : ℂ) ^ (s / 2) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff, not_and_or]
      exact Or.inl (ofReal_ne_zero.mpr (D_pos K).ne')
    rw [hRζ s hs]
    show (s - 1) * dedekindZeta K s = (s - 1) * Λ s * invGammaFactor K s
    rw [hΛeq s hs, D_cast]
    unfold invGammaFactor
    set r₁ : ℕ := NumberField.InfinitePlace.nrRealPlaces K
    set r₂ : ℕ := NumberField.InfinitePlace.nrComplexPlaces K
    have e1 : ((D K : ℝ) : ℂ) ^ (s / 2) * (((D K : ℝ) : ℂ) ^ (s / 2))⁻¹ = 1 := mul_inv_cancel₀ hD
    have e2 : Gammaℝ s ^ r₁ * (Gammaℝ s)⁻¹ ^ r₁ = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hΓℝ, one_pow]
    have e3 : Gammaℂ s ^ r₂ * (Gammaℂ s)⁻¹ ^ r₂ = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hΓℂ, one_pow]
    calc (s - 1) * dedekindZeta K s
        = (s - 1) * dedekindZeta K s * (((D K : ℝ) : ℂ) ^ (s / 2) * (((D K : ℝ) : ℂ) ^ (s / 2))⁻¹) *
            (Gammaℝ s ^ r₁ * (Gammaℝ s)⁻¹ ^ r₁) * (Gammaℂ s ^ r₂ * (Gammaℂ s)⁻¹ ^ r₂) := by
          rw [e1, e2, e3]; ring
      _ = (s - 1) * (((D K : ℝ) : ℂ) ^ (s / 2) * Gammaℝ s ^ r₁ * Gammaℂ s ^ r₂ * dedekindZeta K s) *
            ((((D K : ℝ) : ℂ) ^ (s / 2))⁻¹ * (Gammaℝ s)⁻¹ ^ r₁ * (Gammaℂ s)⁻¹ ^ r₂) := by ring
  have hev : R =ᶠ[𝓝 (2 : ℂ)] g :=
    Filter.eventuallyEq_of_mem (hVopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)) fun z hz => hagree z hz
  exact hRan.eqOn_of_preconnected_of_eventuallyEq hgan (isPreconnected_compl01) h2mem hev

end ident

section main
variable (K : Type) [Field K] [NumberField K]

theorem norm_cpow_D (s : ℂ) : ‖((D K : ℝ) : ℂ) ^ s‖ = (D K) ^ s.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos (D_pos K) s

theorem main :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ (R : ℂ → ℂ), Differentiable ℂ R →
        (∀ s : ℂ, 1 < s.re → R s = (s - 1) * NumberField.dedekindZeta K s) →
      ∀ s : ℂ, s.re = -1 / 2 → ‖R s‖ ≤ C * (2 + |s.im|) ^ A := by
  obtain ⟨Λ, hΛd, hFE, hΛeq, -, -, -⟩ := NumberField.exists_completedDedekindZeta_package K
  obtain ⟨r₁, hr₁⟩ : ∃ r : ℕ, NumberField.InfinitePlace.nrRealPlaces K = r := ⟨_, rfl⟩
  obtain ⟨r₂, hr₂⟩ : ∃ r : ℕ, NumberField.InfinitePlace.nrComplexPlaces K = r := ⟨_, rfl⟩
  have hA0 : (0 : ℝ) < ((1 + r₁ + 2 * r₂ : ℕ) : ℝ) := by positivity
  refine ⟨D K * Mζ K, ((1 + r₁ + 2 * r₂ : ℕ) : ℝ), mul_pos (D_pos K) (Mζ_pos K), hA0, ?_⟩
  intro R hR hRζ s hs
  have hs0 : s ≠ 0 := ne_zero_of_re s hs
  have hs1 : s ≠ 1 := ne_one_of_re s hs
  have hsmem : s ∈ ({(0 : ℂ), 1}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hs0, hs1⟩

  have hReq : R s = (s - 1) * Λ s * invGammaFactor K s := R_eq K R hR hRζ Λ hΛd hΛeq hsmem
  have hΛs : Λ s = Λ (1 - s) := (hFE s hs0 hs1).symm
  have h1s : 1 < (1 - s).re := by rw [sub_re, one_re, hs]; norm_num
  have h1s' : 3 / 2 ≤ (1 - s).re := by rw [sub_re, one_re, hs]; norm_num
  have hΛ1s : Λ (1 - s) = ((D K : ℝ) : ℂ) ^ ((1 - s) / 2) * Gammaℝ (1 - s) ^ r₁ * Gammaℂ (1 - s) ^ r₂ *
      dedekindZeta K (1 - s) := by
    rw [hΛeq (1 - s) h1s, D_cast, hr₁, hr₂]
  have hinv : invGammaFactor K s =
      (((D K : ℝ) : ℂ) ^ (s / 2))⁻¹ * (Gammaℝ s)⁻¹ ^ r₁ * (Gammaℂ s)⁻¹ ^ r₂ := by
    unfold invGammaFactor; rw [hr₁, hr₂]

  set t : ℝ := s.im with ht
  have hsn : ‖s‖ ≤ 2 + |t| := by
    calc ‖s‖ ≤ |s.re| + |s.im| := norm_le_abs_re_add_abs_im s
      _ = 1 / 2 + |t| := by rw [hs, ht]; norm_num
      _ ≤ 2 + |t| := by linarith
  have hs1n : ‖s - 1‖ ≤ 2 + |t| := by
    calc ‖s - 1‖ ≤ |(s - 1).re| + |(s - 1).im| := norm_le_abs_re_add_abs_im _
      _ = 3 / 2 + |t| := by rw [sub_re, one_re, hs, sub_im, one_im, sub_zero, ht]; norm_num
      _ ≤ 2 + |t| := by linarith
  have hsp1n : ‖s + 1‖ ≤ 2 + |t| := by
    calc ‖s + 1‖ ≤ |(s + 1).re| + |(s + 1).im| := norm_le_abs_re_add_abs_im _
      _ = 1 / 2 + |t| := by rw [add_re, one_re, hs, add_im, one_im, add_zero, ht]; norm_num
      _ ≤ 2 + |t| := by linarith
  have h2t : (1 : ℝ) ≤ 2 + |t| := by linarith [abs_nonneg t]
  have h2t0 : (0 : ℝ) ≤ 2 + |t| := by linarith
  have hπ : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]

  have hΓℝ0 : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re s hs
  have hΓℂ0 : Gammaℂ s ≠ 0 := Gammaℂ_ne_zero_of_re s hs
  have hΓℝpos : 0 < ‖Gammaℝ s‖ := norm_pos_iff.mpr hΓℝ0
  have hΓℂpos : 0 < ‖Gammaℂ s‖ := norm_pos_iff.mpr hΓℂ0
  have hratioℝ : ‖Gammaℝ (1 - s)‖ * ‖(Gammaℝ s)⁻¹‖ ≤ 2 + |t| := by
    rw [norm_Gammaℝ_one_sub s hs, norm_inv]
    have : ‖Gammaℝ s‖ * ‖s‖ / (2 * Real.pi) * ‖Gammaℝ s‖⁻¹ = ‖s‖ / (2 * Real.pi) := by
      field_simp
    rw [this]
    calc ‖s‖ / (2 * Real.pi) ≤ ‖s‖ / 1 := div_le_div_of_nonneg_left (norm_nonneg _) one_pos hπ
      _ ≤ 2 + |t| := by rw [div_one]; exact hsn
  have hratioℂ : ‖Gammaℂ (1 - s)‖ * ‖(Gammaℂ s)⁻¹‖ ≤ (2 + |t|) ^ 2 := by
    rw [norm_Gammaℂ_one_sub s hs, norm_inv]
    have : ‖Gammaℂ s‖ * ‖s‖ * ‖s + 1‖ / (2 * Real.pi) ^ 2 * ‖Gammaℂ s‖⁻¹ =
        ‖s‖ * ‖s + 1‖ / (2 * Real.pi) ^ 2 := by
      field_simp
    rw [this]
    have hπ2 : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := one_le_pow₀ hπ
    calc ‖s‖ * ‖s + 1‖ / (2 * Real.pi) ^ 2 ≤ ‖s‖ * ‖s + 1‖ / 1 :=
          div_le_div_of_nonneg_left (by positivity) one_pos hπ2
      _ ≤ (2 + |t|) * (2 + |t|) := by
          rw [div_one]; exact mul_le_mul hsn hsp1n (norm_nonneg _) h2t0
      _ = (2 + |t|) ^ 2 := (sq _).symm

  have hDpow : ‖((D K : ℝ) : ℂ) ^ ((1 - s) / 2)‖ * ‖(((D K : ℝ) : ℂ) ^ (s / 2))⁻¹‖ = D K := by
    rw [norm_inv, norm_cpow_D, norm_cpow_D]
    have h1 : ((1 - s) / 2).re = 3 / 4 := by
      have : ((1 - s) / 2).re = (1 - s).re / 2 := by simp
      rw [this, sub_re, one_re, hs]; norm_num
    have h2 : (s / 2).re = -(1 / 4) := by
      have : (s / 2).re = s.re / 2 := by simp
      rw [this, hs]; norm_num
    rw [h1, h2, ← Real.rpow_neg (D_pos K).le, neg_neg, ← Real.rpow_add (D_pos K)]
    norm_num

  have hζ := norm_dedekindZeta_le K (1 - s) h1s'
  set dA : ℝ := ‖((D K : ℝ) : ℂ) ^ ((1 - s) / 2)‖ with hdA
  set dB : ℝ := ‖(((D K : ℝ) : ℂ) ^ (s / 2))⁻¹‖ with hdB
  set gA : ℝ := ‖Gammaℝ (1 - s)‖ with hgA
  set gB : ℝ := ‖(Gammaℝ s)⁻¹‖ with hgB
  set cA : ℝ := ‖Gammaℂ (1 - s)‖ with hcA
  set cB : ℝ := ‖(Gammaℂ s)⁻¹‖ with hcB
  set z : ℝ := ‖dedekindZeta K (1 - s)‖ with hz
  have hnorm : ‖R s‖ = ‖s - 1‖ * (dA * dB) * (gA * gB) ^ r₁ * (cA * cB) ^ r₂ * z := by
    rw [hReq, hΛs, hΛ1s, hinv]
    simp only [norm_mul, norm_pow]
    rw [mul_pow, mul_pow]
    ring
  rw [hnorm, hDpow]
  calc ‖s - 1‖ * D K * (gA * gB) ^ r₁ * (cA * cB) ^ r₂ * z
      ≤ (2 + |t|) * D K * (2 + |t|) ^ r₁ * ((2 + |t|) ^ 2) ^ r₂ * Mζ K := by
        have h3 : (gA * gB) ^ r₁ ≤ (2 + |t|) ^ r₁ := pow_le_pow_left₀ (by positivity) hratioℝ r₁
        have h4 : (cA * cB) ^ r₂ ≤ ((2 + |t|) ^ 2) ^ r₂ := pow_le_pow_left₀ (by positivity) hratioℂ r₂
        have hDK := (D_pos K).le
        have hMK := (Mζ_pos K).le
        gcongr
    _ = D K * Mζ K * (2 + |t|) ^ (1 + r₁ + 2 * r₂) := by
        rw [← pow_mul]; ring
    _ = D K * Mζ K * (2 + |t|) ^ (((1 + r₁ + 2 * r₂ : ℕ)) : ℝ) := by rw [Real.rpow_natCast]

end main

end R4Z2b

end

theorem solution
    (K : Type) [Field K] [NumberField K] :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ (R : ℂ → ℂ), Differentiable ℂ R →
        (∀ s : ℂ, 1 < s.re → R s = (s - 1) * NumberField.dedekindZeta K s) →
      ∀ s : ℂ, s.re = -1 / 2 → ‖R s‖ ≤ C * (2 + |s.im|) ^ A :=
  R4Z2b.main K

end S_NumberField_exists_forall_norm_sub_one_mul_dedekindZeta_continuation_le_rpow_on_re_eq_neg_half
end P2MW
export P2MW.S_NumberField_exists_forall_norm_sub_one_mul_dedekindZeta_continuation_le_rpow_on_re_eq_neg_half (solution)
