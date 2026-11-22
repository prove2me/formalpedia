-- Prove2me | solution 1 for MasulloGRH.heckeGammaRatio_vertical_line_bound
-- status  : ACCEPTED   (prove)
-- author  : @GeorgeCoote
-- created : 2026-11-21T20:18:48.263269+00:00
-- url     : https://prove2.me/submissions/e0b771cc-a565-4ef6-846f-094ce1698e33

import Definitions.Def_MasulloGRH_CompletedL
import Theorems.Thm_Complex_gamma_ratio_fixed_shift_vertical_bound

set_option autoImplicit false

open MasulloGRH NumberField

private theorem localComponentInfinite_inv
    {F : Type*} [Field F] [NumberField F] (χ : HeckeCharacter F) (w : InfinitePlace F)
    (x : (w.Completion)ˣ) :
    (χ⁻¹).localComponentInfinite w x = (χ.localComponentInfinite w x)⁻¹ := by
  rfl

private theorem archParity_inv
    {F : Type*} [Field F] [NumberField F] (χ : HeckeCharacter F) (w : InfinitePlace F) :
    (χ⁻¹).archParity w = χ.archParity w := by
  classical
  simp [HeckeCharacter.archParity, localComponentInfinite_inv]

private theorem unit_circle_zpow_injective {F : Type*} [Field F] [NumberField F]
    {w : InfinitePlace F} (hw : w.IsComplex) {m n : ℤ}
    (h : ∀ x : (w.Completion)ˣ, ‖(x : w.Completion)‖ = 1 →
      InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) ^ m =
        InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) ^ n) : m = n := by
  by_contra hne
  let d : ℤ := m - n
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hne
  let θ : ℂ := ((Real.pi / (d : ℝ) : ℝ) : ℂ) * Complex.I
  let z : ℂ := Complex.exp θ
  have hz : z ≠ 0 := Complex.exp_ne_zero _
  obtain ⟨y, hy⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw z
  have hy0 : y ≠ 0 := by
    intro h0
    exact hz (by simpa [h0] using hy.symm)
  let x := Units.mk0 y hy0
  have hxy : InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) = z := hy
  have hx : ‖(x : w.Completion)‖ = 1 := by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) (x : w.Completion), hxy]
    simp [z, θ, Complex.norm_exp, Complex.mul_re]
  have hpow := h x hx
  rw [hxy] at hpow
  have h₁ : z ^ d = 1 := by
    rw [show d = m - n from rfl, zpow_sub₀ hz, hpow, div_self (zpow_ne_zero _ hz)]
  have h₂ : z ^ d = -1 := by
    rw [show z = Complex.exp θ from rfl, ← Complex.exp_int_mul]
    have hθ : (d : ℂ) * θ = (Real.pi : ℂ) * Complex.I := by
      dsimp [θ]
      push_cast
      field_simp
    rw [hθ, Complex.exp_pi_mul_I]
  rw [h₂] at h₁
  norm_num at h₁

private theorem archWeight_inv
    {F : Type*} [Field F] [NumberField F] (χ : HeckeCharacter F)
    (w : InfinitePlace F) (hw : w.IsComplex) : (χ⁻¹).archWeight w = χ.archWeight w := by
  classical
  let P (ψ : HeckeCharacter F) (n : ℤ) : Prop :=
    ∀ x : (w.Completion)ˣ, ‖(x : w.Completion)‖ = 1 →
      ψ.localComponentInfinite w x =
        InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) ^ n
  have hneg (ψ : HeckeCharacter F) (n : ℤ) (hn : P ψ n) : P ψ⁻¹ (-n) := by
    intro x hx
    rw [localComponentInfinite_inv, hn x hx, zpow_neg]
  change (if h : ∃ n, P χ⁻¹ n then h.choose.natAbs else 0) =
    (if h : ∃ n, P χ n then h.choose.natAbs else 0)
  by_cases h : ∃ n, P χ n
  · have hinv : ∃ n, P χ⁻¹ n := ⟨-h.choose, hneg χ _ h.choose_spec⟩
    rw [dif_pos hinv, dif_pos h]
    have heq : hinv.choose = -h.choose := unit_circle_zpow_injective hw fun x hx =>
      (hinv.choose_spec x hx).symm.trans (hneg χ _ h.choose_spec x hx)
    rw [heq, Int.natAbs_neg]
  · have hinv : ¬ ∃ n, P χ⁻¹ n := by
      rintro ⟨n, hn⟩
      exact h ⟨-n, by simpa only [inv_inv] using hneg χ⁻¹ n hn⟩
    rw [dif_neg hinv, dif_neg h]

private theorem scaledGammaRatio_bound
    (a b u v k B : ℝ) (hk : 0 < k) (hB : 0 < B) :
    ∃ C T : ℝ, 0 ≤ C ∧ 1 ≤ T ∧
      ∀ (t : ℝ) (z w : ℂ), T ≤ |t| →
        z.re = a → w.re = b → z.im = u - k * t → w.im = v + k * t →
        ‖((B : ℂ) ^ (-z) * Complex.Gamma z) /
          ((B : ℂ) ^ (-w) * Complex.Gamma w)‖ ≤ C * |t| ^ (a - b) := by
  obtain ⟨C, T, hC, hT, h⟩ := Complex.gamma_ratio_fixed_shift_vertical_bound a b u v k hk
  refine ⟨(B ^ (-a) / B ^ (-b)) * C, T, by positivity, hT, ?_⟩
  intro t z w ht hzre hwre hzim hwim
  rw [mul_div_mul_comm, norm_mul, norm_div ((B : ℂ) ^ (-z)),
    Complex.norm_cpow_eq_rpow_re_of_pos hB, Complex.norm_cpow_eq_rpow_re_of_pos hB,
    Complex.neg_re, Complex.neg_re, hzre, hwre, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h t z w ht hzre hwre hzim hwim) (by positivity)

private theorem archLFactorRatio_bound
    {F : Type*} [Field F] [NumberField F] (χ : HeckeCharacter F)
    (w : InfinitePlace F) (σ : ℝ) :
    ∃ C T : ℝ, 0 ≤ C ∧ 1 ≤ T ∧
      ∀ s : ℂ, s.re = σ → T ≤ |s.im| →
        ‖(χ⁻¹).archLFactor w (1 - s) / χ.archLFactor w s‖ ≤
          C * |s.im| ^ ((w.mult : ℝ) * (1 / 2 - σ)) := by
  classical
  let u := (χ⁻¹).archExponent w
  let v := χ.archExponent w
  by_cases hw : w.IsReal
  · let j : ℕ := χ.archParity w
    let a : ℝ := (1 - σ + j) / 2
    let b : ℝ := (σ + j) / 2
    obtain ⟨C, T, hC, hT, h⟩ :=
      scaledGammaRatio_bound a b (u / 2) (v / 2) (1 / 2) Real.pi (by norm_num) Real.pi_pos
    refine ⟨C, T, hC, hT, ?_⟩
    intro s hs ht
    rw [HeckeCharacter.archLFactor, HeckeCharacter.archLFactor, if_pos hw, if_pos hw,
      archParity_inv, hw.mult_eq_one]
    let z : ℂ := (1 - s + (u : ℂ) * Complex.I + (j : ℂ)) / 2
    let q : ℂ := (s + (v : ℂ) * Complex.I + (j : ℂ)) / 2
    have hbound := h s.im z q ht
      (by norm_num [z, a, Complex.div_ofNat_re, Complex.mul_re, hs])
      (by norm_num [q, b, Complex.div_ofNat_re, Complex.mul_re, hs])
      (by norm_num [z, Complex.div_ofNat_im, Complex.mul_im]; ring)
      (by norm_num [q, Complex.div_ofNat_im, Complex.mul_im]; ring)
    have hexp : a - b = (1 : ℝ) * (1 / 2 - σ) := by dsimp [a, b]; ring
    simpa only [hexp, Nat.cast_one, z, q, j, u, v] using hbound
  · let j : ℕ := χ.archWeight w
    let a : ℝ := 1 - σ + (j : ℝ) / 2
    let b : ℝ := σ + (j : ℝ) / 2
    have hw' := InfinitePlace.not_isReal_iff_isComplex.mp hw
    obtain ⟨C, T, hC, hT, h⟩ :=
      scaledGammaRatio_bound a b u v 1 (2 * Real.pi) one_pos (by positivity)
    refine ⟨C, T, hC, hT, ?_⟩
    intro s hs ht
    rw [HeckeCharacter.archLFactor, HeckeCharacter.archLFactor, if_neg hw, if_neg hw,
      archWeight_inv χ w hw', hw'.mult_eq_two]
    let z : ℂ := 1 - s + (u : ℂ) * Complex.I + (j : ℂ) / 2
    let q : ℂ := s + (v : ℂ) * Complex.I + (j : ℂ) / 2
    have hbound := h s.im z q ht
      (by norm_num [z, a, Complex.div_ofNat_re, Complex.mul_re, hs])
      (by norm_num [q, b, Complex.div_ofNat_re, Complex.mul_re, hs])
      (by norm_num [z, Complex.div_ofNat_im, Complex.mul_im]; ring)
      (by norm_num [q, Complex.div_ofNat_im, Complex.mul_im]; ring)
    have hexp : a - b = (2 : ℝ) * (1 / 2 - σ) := by dsimp [a, b]; ring
    simpa only [hexp, Nat.cast_ofNat, Complex.ofReal_mul, Complex.ofReal_ofNat,
      z, q, j, u, v] using hbound

theorem solution
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) (σ : ℝ) :
    ∃ (C T : ℝ), 0 ≤ C ∧ 1 ≤ T ∧
      ∀ s : ℂ, s.re = σ → T ≤ |s.im| →
        ‖(χ⁻¹).gammaFactor (1 - s) / χ.gammaFactor s‖ ≤
          C * |s.im| ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - σ)) := by
  classical
  choose C T hC _hT hbound using fun w : InfinitePlace F => archLFactorRatio_bound χ w σ
  let height : ℝ := Finset.univ.fold max 1 T
  have hheight : 1 ≤ height := by
    change 1 ≤ Finset.univ.fold max 1 T
    rw [Finset.le_fold_max]
    exact Or.inl le_rfl
  refine ⟨∏ w, C w, height, Finset.prod_nonneg (fun w _ => hC w), hheight, ?_⟩
  intro s hs ht
  have htpos : 0 < |s.im| := lt_of_lt_of_le zero_lt_one (hheight.trans ht)
  rw [HeckeCharacter.gammaFactor, HeckeCharacter.gammaFactor, ← Finset.prod_div_distrib,
    Complex.norm_prod]
  calc
    _ ≤ ∏ w : InfinitePlace F, C w * |s.im| ^ ((w.mult : ℝ) * (1 / 2 - σ)) := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro w hw
      have hwheight : T w ≤ height := by
        change T w ≤ Finset.univ.fold max 1 T
        rw [Finset.le_fold_max]
        exact Or.inr ⟨w, hw, le_rfl⟩
      exact hbound w s hs (hwheight.trans ht)
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos htpos, ← Finset.sum_mul,
        ← Nat.cast_sum, InfinitePlace.sum_mult_eq]
