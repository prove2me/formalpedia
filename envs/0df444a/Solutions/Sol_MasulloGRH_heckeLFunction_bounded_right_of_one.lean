-- Prove2me | solution 1 for MasulloGRH.heckeLFunction_bounded_right_of_one
-- status  : ACCEPTED   (prove)
-- author  : @flashonfire
-- created : 2026-11-21T19:22:25.206019+00:00
-- url     : https://prove2.me/submissions/8ea3057a-801d-4944-b6ae-201a133afc75

import Definitions.Def_MasulloGRH_HeckeLFunction

set_option autoImplicit false

open NumberField IsDedekindDomain Filter Finset

namespace RightEdgeAux

variable (K : Type*) [Field K] [NumberField K]

theorem ideal_count_lseries_summable {σ : ℝ} (hσ : 1 < σ) :
    LSeriesSummable (fun n : ℕ => ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) : ℂ))
      (σ : ℂ) := by
  have ht : Tendsto (fun n : ℕ =>
      (∑ k ∈ Icc 1 n, (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)) / n)
      atTop (nhds (dedekindZeta_residue K)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ))
      =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    have h1 := ht.isBigO_one ℝ
    have h2 : (fun n : ℕ => ∑ k ∈ Icc 1 n, (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ))
        =ᶠ[atTop] fun n : ℕ =>
          ((∑ k ∈ Icc 1 n, (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)) / n) * (n : ℝ) := by
      filter_upwards [eventually_ne_atTop 0] with n hn
      rw [div_mul_cancel₀]
      exact_mod_cast hn
    refine (h2.isBigO).trans ?_
    simpa using h1.mul (Asymptotics.isBigO_refl (fun n : ℕ => (n : ℝ)) atTop)
  exact LSeriesSummable_of_sum_norm_bigO_and_nonneg hO (fun _ => Nat.cast_nonneg _) zero_le_one
    (by simpa using hσ)

theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem summable_primeNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun v : HeightOneSpectrum (𝓞 K) =>
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ)) := by
  classical
  set a : ℕ → ℝ := fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) with ha
  have hS := (ideal_count_lseries_summable K hσ).norm
  have hterm : ∀ n : ℕ, n ≠ 0 → ‖LSeries.term (fun n => ((a n : ℝ) : ℂ)) (σ : ℂ) n‖ =
      a n * (n : ℝ) ^ (-σ) := by
    intro n hn
    rw [LSeries.norm_term_eq, if_neg hn, Complex.norm_real, Real.norm_of_nonneg (Nat.cast_nonneg _),
      Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]
  refine summable_of_sum_le (c := ∑' n, ‖LSeries.term (fun n => ((a n : ℝ) : ℂ)) (σ : ℂ) n‖)
    (fun v => Real.rpow_nonneg (Nat.cast_nonneg _) _) fun u => ?_
  set N : HeightOneSpectrum (𝓞 K) → ℕ := fun v => Ideal.absNorm v.asIdeal
  rw [← Finset.sum_fiberwise_of_maps_to (g := N) (t := u.image N)
    (fun v hv => Finset.mem_image_of_mem N hv)]
  refine le_trans (Finset.sum_le_sum fun n hn => ?_)
    (hS.sum_le_tsum (u.image N) (fun _ _ => norm_nonneg _))
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hn
  have hn0 : N w ≠ 0 := by have := two_le_absNorm K w; simp only [N]; omega
  rw [hterm _ hn0]
  have hconst : ∀ v ∈ u.filter (fun v => N v = N w),
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) = ((N w : ℕ) : ℝ) ^ (-σ) := by
    intro v hv; have := (Finset.mem_filter.1 hv).2; simp only [N] at this; rw [this]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hfin : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = N w} :=
    (Ideal.finite_setOfPred_absNorm_eq (N w)).to_subtype
  have hinj : Function.Injective (fun v : ↥(u.filter (fun v => N v = N w)) =>
      (⟨v.1.asIdeal, (Finset.mem_filter.1 v.2).2⟩ : {I : Ideal (𝓞 K) // Ideal.absNorm I = N w})) := by
    intro x y hxy
    apply Subtype.ext
    apply HeightOneSpectrum.ext
    exact congrArg Subtype.val hxy
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at this
  simp only [ha]
  exact_mod_cast this

variable {K}

theorem norm_primeValue_le (χ : MasulloGRH.HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) :
    ‖χ.primeValue v‖ ≤ 1 := by
  unfold MasulloGRH.HeckeCharacter.primeValue
  split_ifs
  · unfold MasulloGRH.HeckeCharacter.localComponent
    rw [Circle.norm_coe]
  · simp

/-- One Euler factor: `‖(1 - x)⁻¹‖ ≤ exp (2 r)` when `‖x‖ ≤ r ≤ 1/2`. -/
theorem norm_inv_one_sub_le_exp {x : ℂ} {r : ℝ} (hx : ‖x‖ ≤ r) (hr : r ≤ 1 / 2) :
    ‖(1 - x)⁻¹‖ ≤ Real.exp (2 * r) := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hx
  have h1 : 1 - r ≤ ‖1 - x‖ := by
    have := norm_sub_norm_le (1 : ℂ) x
    rw [norm_one] at this
    linarith
  have hpos : 0 < 1 - r := by linarith
  rw [norm_inv]
  calc ‖1 - x‖⁻¹ ≤ (1 - r)⁻¹ := inv_anti₀ hpos h1
    _ ≤ 1 + 2 * r := by
        rw [inv_le_iff_one_le_mul₀ hpos]
        nlinarith
    _ ≤ Real.exp (2 * r) := by linarith [Real.add_one_le_exp (2 * r)]

theorem eulerProduct_bounded (χ : MasulloGRH.HeckeCharacter K) {σ : ℝ} (hσ : 1 < σ) :
    ∃ C : ℝ, ∀ s : ℂ, s.re = σ → ‖MasulloGRH.heckeEulerProduct χ s‖ ≤ C := by
  classical
  set r : HeightOneSpectrum (𝓞 K) → ℝ := fun v => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ)
  have hsum : Summable r := summable_primeNorm_rpow K hσ
  have hr0 : ∀ v, 0 ≤ r v := fun v => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hrhalf : ∀ v, r v ≤ 1 / 2 := by
    intro v
    have h2 : (2 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast two_le_absNorm K v
    calc r v ≤ (2 : ℝ) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) h2 (by linarith)
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 / 2 := by norm_num
  refine ⟨Real.exp (2 * ∑' v, r v), fun s hs => ?_⟩
  set g : HeightOneSpectrum (𝓞 K) → ℂ := fun v =>
    (1 - χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹
  have hg : ∀ v, ‖g v‖ ≤ Real.exp (2 * r v) := by
    intro v
    refine norm_inv_one_sub_le_exp ?_ (hrhalf v)
    have hpos : 0 < Ideal.absNorm v.asIdeal := by have := two_le_absNorm K v; omega
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re, hs]
    calc ‖χ.primeValue v‖ * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ)
        ≤ 1 * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right (norm_primeValue_le χ v) (hr0 v)
      _ = r v := one_mul _
  have hfin : ∀ u : Finset (HeightOneSpectrum (𝓞 K)),
      ∏ v ∈ u, ‖g v‖ ≤ Real.exp (2 * ∑' v, r v) := by
    intro u
    calc ∏ v ∈ u, ‖g v‖ ≤ ∏ v ∈ u, Real.exp (2 * r v) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun v _ => hg v)
      _ = Real.exp (2 * ∑ v ∈ u, r v) := by rw [← Real.exp_sum, Finset.mul_sum]
      _ ≤ Real.exp (2 * ∑' v, r v) := by
          gcongr
          exact hsum.sum_le_tsum u (fun v _ => hr0 v)
  unfold MasulloGRH.heckeEulerProduct
  change ‖∏' v, g v‖ ≤ _
  by_cases hm : Multipliable g
  · exact le_of_tendsto' hm.hasProd.norm hfin
  · rw [tprod_eq_one_of_not_multipliable hm, norm_one]
    exact Real.one_le_exp (by positivity)

end RightEdgeAux

open RightEdgeAux in
theorem solution
    (F : Type*) [Field F] [NumberField F] (χ : MasulloGRH.HeckeCharacter F) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ t : ℝ,
      ‖MasulloGRH.heckeLFunction χ (((1 + δ : ℝ) : ℂ) + t * Complex.I)‖ ≤ C := by
  obtain ⟨C, hC⟩ := eulerProduct_bounded χ (σ := 1 + δ) (by linarith)
  refine ⟨max C 0, fun t => ?_⟩
  have hre : (((1 + δ : ℝ) : ℂ) + t * Complex.I).re = 1 + δ := by simp
  unfold MasulloGRH.heckeLFunction
  split_ifs with h
  · rw [h.choose_spec.2 _ (by rw [hre]; linarith)]
    exact (hC _ hre).trans (le_max_left _ _)
  · simp
