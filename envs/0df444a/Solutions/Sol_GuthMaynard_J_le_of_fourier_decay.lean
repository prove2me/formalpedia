-- Prove2me | solution 1 for GuthMaynard.J_le_of_fourier_decay
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T00:14:15.638214+00:00
-- url     : https://prove2.me/submissions/99dc53b6-00af-469c-b99f-b6593d64d895

import Mathlib
import Definitions.Def_GuthMaynard
import Definitions.Def_GuthMaynardAffine
import Theorems.Thm_GuthMaynard_Affine_iteration
section
namespace GuthMaynard.Affine
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal

theorem J_eq (M K : ℝ) (f : ℝ → ℝ) :
    J M K f = ⨆ (M₁ : ℝ) (_ : M₁ ∈ Set.Ioo 0 M) (M₂ : ℝ) (_ : M₂ ∈ Set.Ioo 0 M) (M₃ : ℝ)
      (_ : M₃ ∈ Set.Ioo 0 M), ∫⁻ u : ℝ, ENNReal.ofReal (gsum K M₁ M₂ M₃ f u ^ 2) := rfl


end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartT
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal
/-- The class grows with `T`. -/
theorem Adm.mono {C : ℝ} {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Adm C c T f) (hT : 0 < T)
    {T' : ℝ} (hTT' : T ≤ T') : Adm C (fun j ε => max (c j ε) 0) T' f := by
  refine ⟨hf.smooth, hf.nonneg, hf.supp, fun j ε hε ξ hξ => ?_⟩
  have hS : 0 ≤ ⨆ u, f u := Real.iSup_nonneg hf.nonneg
  refine (hf.decay j ε hε ξ hξ).trans ?_
  have h1 : T ^ ε ≤ T' ^ ε := Real.rpow_le_rpow hT.le hTT' hε.le
  have h2 : (T / |ξ|) ^ j ≤ (T' / |ξ|) ^ j :=
    pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hTT' (abs_nonneg _)) j
  have h3 : c j ε ≤ max (c j ε) 0 := le_max_left _ _
  have h4 : 0 ≤ max (c j ε) 0 := le_max_right _ _
  calc c j ε * T ^ ε * (T / |ξ|) ^ j * ⨆ u, f u
      ≤ max (c j ε) 0 * T ^ ε * (T / |ξ|) ^ j * ⨆ u, f u := by gcongr
    _ ≤ max (c j ε) 0 * T' ^ ε * (T' / |ξ|) ^ j * ⨆ u, f u := by
        gcongr; exact mul_nonneg h4 (Real.rpow_nonneg (hT.le.trans hTT') _)

/-- The radial profile `a` on `[0, R]`, `b / t²` beyond. -/
noncomputable def prof (a b R : ℝ) (t : ℝ) : ℝ := if t ≤ R then a else b / t ^ 2

theorem prof_nonneg {a b R : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (t : ℝ) : 0 ≤ prof a b R t := by
  unfold prof; split_ifs <;> positivity

theorem integrable_prof_abs {a b R : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hR : 0 < R) :
    Integrable (fun ξ : ℝ => prof a b R |ξ|) := by
  have hm : Measurable (fun ξ : ℝ => prof a b R |ξ|) := by
    unfold prof
    exact Measurable.ite (measurableSet_le measurable_abs measurable_const) measurable_const
      (measurable_const.div ((measurable_abs).pow_const 2))
  refine Integrable.mono' ((integrable_inv_one_add_sq.comp_div hR.ne').const_mul
    (2 * (a + b / R ^ 2))) hm.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (prof_nonneg ha hb _)]
  have hq : 0 < 1 + (ξ / R) ^ 2 := by positivity
  unfold prof
  split_ifs with h
  · have : (ξ / R) ^ 2 ≤ 1 := by
      rw [div_pow, div_le_one (by positivity), ← sq_abs ξ]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [← div_eq_mul_inv, le_div_iff₀ hq]
    have : 0 ≤ b / R ^ 2 := by positivity
    nlinarith
  · push Not at h
    have hξ : R ^ 2 < ξ ^ 2 := by rw [← sq_abs ξ]; exact pow_lt_pow_left₀ h hR.le two_ne_zero
    have hξ0 : 0 < ξ ^ 2 := by linarith [sq_nonneg R, pow_pos hR 2]
    rw [sq_abs, ← div_eq_mul_inv, le_div_iff₀ hq, div_pow]
    rw [div_mul_eq_mul_div, div_le_iff₀ hξ0]
    have hR2 : 0 < R ^ 2 := by positivity
    set q := ξ ^ 2 / R ^ 2 with hqdef
    have hxq : ξ ^ 2 = q * R ^ 2 := by rw [hqdef]; field_simp
    have e1 : 2 * (a + b / R ^ 2) * ξ ^ 2 = 2 * a * ξ ^ 2 + 2 * b * q := by
      rw [hxq]; field_simp
    rw [e1]
    have h1 : 1 ≤ q := by rw [hqdef, le_div_iff₀ hR2]; linarith
    have : 0 ≤ 2 * a * ξ ^ 2 := by positivity
    nlinarith

theorem integral_prof_abs {a b R : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hR : 0 < R) :
    ∫ ξ : ℝ, prof a b R |ξ| = 2 * (a * R + b / R) := by
  rw [integral_comp_abs (f := prof a b R)]
  congr 1
  have hI1 : IntegrableOn (prof a b R) (Set.Ioc 0 R) := by
    refine (integrableOn_const (C := a) (by simp)).congr_fun (fun t ht => ?_) measurableSet_Ioc
    simp [prof, ht.2]
  have hrp : Set.EqOn (prof a b R) (fun t => b * t ^ (-2 : ℝ)) (Set.Ioi R) := by
    intro t ht
    have ht' : ¬ t ≤ R := not_le.2 ht
    have tpos : 0 < t := hR.trans ht
    simp only [prof, ht', if_false]
    rw [Real.rpow_neg tpos.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      div_eq_mul_inv]
  have hI2' : IntegrableOn (fun t : ℝ => b * t ^ (-2 : ℝ)) (Set.Ioi R) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR).const_mul b
  have hI2 : IntegrableOn (prof a b R) (Set.Ioi R) :=
    hI2'.congr_fun hrp.symm measurableSet_Ioi
  rw [← Set.Ioc_union_Ioi_eq_Ioi hR.le, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi hI1 hI2]
  rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => a) (fun t ht => by simp [prof, ht.2]),
    setIntegral_congr_fun measurableSet_Ioi hrp, integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR]
  simp only [setIntegral_const, Measure.real, Real.volume_Ioc, sub_zero,
    ENNReal.toReal_ofReal hR.le, smul_eq_mul]
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  field_simp

theorem ae_ne_zero : ∀ᵐ ξ : ℝ ∂volume, ξ ≠ 0 := by
  rw [ae_iff]; simp

theorem cont_hcs {C : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hsupp : Function.support f ⊆ Set.Icc (1 / C) C) : HasCompactSupport f :=
  HasCompactSupport.intro isCompact_Icc fun x hx => by
    by_contra h; exact hx (hsupp h)

theorem le_sup_of {C : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hsupp : Function.support f ⊆ Set.Icc (1 / C) C) (x : ℝ) : f x ≤ ⨆ u, f u :=
  le_ciSup (hf.bddAbove_range_of_hasCompactSupport (cont_hcs hf hsupp)) x

/-- Fourier inversion, pointwise. -/
theorem inversion {F : ℝ → ℂ} (hc : Continuous F) (hi : Integrable F) (hi' : Integrable (𝓕 F))
    (x : ℝ) : F x = ∫ ξ, 𝐞 (ξ * x) • 𝓕 F ξ := by
  have := congrFun (hc.fourierInv_fourier_eq hi hi') x
  rw [← this, Real.fourierInv_eq]
  simp [mul_comm]

theorem norm_le_integral_norm_fourier {F : ℝ → ℂ} (hc : Continuous F) (hi : Integrable F)
    (hi' : Integrable (𝓕 F)) (x : ℝ) : ‖F x‖ ≤ ∫ ξ, ‖𝓕 F ξ‖ := by
  rw [inversion hc hi hi' x]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; ext ξ; rw [Circle.norm_smul]

theorem mem_dyadic {M : ℝ} {m : ℤ} (h : m ∈ dyadic M) : M < m ∧ (m : ℝ) ≤ 2 * M := by
  simp only [dyadic, Finset.mem_Ioc] at h
  exact ⟨Int.floor_lt.1 h.1, Int.le_floor.1 h.2⟩

theorem dyadic_eq_empty {M : ℝ} (h0 : 0 < M) (h : M < 1 / 2) : dyadic M = ∅ := by
  ext m
  simp only [Finset.notMem_empty, iff_false]
  intro hm
  obtain ⟨h1, h2⟩ := mem_dyadic hm
  have : (m : ℝ) < 1 := by linarith
  have : (0 : ℝ) < m := by linarith
  have h3 : m < 1 := by exact_mod_cast ‹(m : ℝ) < 1›
  have h4 : 0 < m := by exact_mod_cast this
  omega

theorem card_dyadic_le {M : ℝ} (h0 : 0 < M) : ((dyadic M).card : ℝ) ≤ 3 * M := by
  by_cases hM : M < 1 / 2
  · rw [dyadic_eq_empty h0 hM]; simp; linarith
  push Not at hM
  simp only [dyadic, Int.card_Ioc]
  have h1 : (⌊2 * M⌋ : ℝ) ≤ 2 * M := Int.floor_le _
  have h2 : M - 1 < (⌊M⌋ : ℝ) := Int.sub_one_lt_floor _
  rcases le_or_gt (⌊2 * M⌋ - ⌊M⌋) 0 with h | h
  · rw [Int.toNat_of_nonpos h]; simp; linarith
  · have : (((⌊2 * M⌋ - ⌊M⌋).toNat : ℤ) : ℝ) = (⌊2 * M⌋ : ℝ) - ⌊M⌋ := by
      rw [Int.toNat_of_nonneg h.le]; push_cast; ring
    rw [← Int.cast_natCast, this]
    linarith

/-- The `m₁` range. -/
noncomputable abbrev A1 (M₁ : ℝ) : Finset ℤ := dyadic M₁ ∪ (dyadic M₁).map (Equiv.neg ℤ).toEmbedding

theorem mem_A1 {M₁ : ℝ} {m : ℤ} (h : m ∈ A1 M₁) : M₁ < |(m : ℝ)| ∧ |(m : ℝ)| ≤ 2 * M₁ := by
  simp only [A1, Finset.mem_union, Finset.mem_map, Equiv.coe_toEmbedding, Equiv.neg_apply] at h
  rcases h with h | ⟨n, hn, rfl⟩
  · obtain ⟨h1, h2⟩ := mem_dyadic h
    have : (0 : ℝ) ≤ m := by
      by_contra hc; push Not at hc
      have := lt_trans h1 hc
      have hM : 0 ≤ M₁ ∨ M₁ < 0 := le_or_gt 0 M₁
      rcases hM with hM | hM <;> linarith
    rw [abs_of_nonneg this]; exact ⟨h1, h2⟩
  · obtain ⟨h1, h2⟩ := mem_dyadic hn
    push_cast
    rw [abs_neg]
    by_cases hn0 : (0 : ℝ) ≤ n
    · rw [abs_of_nonneg hn0]; exact ⟨h1, h2⟩
    · push Not at hn0
      rw [abs_of_neg hn0]; constructor <;> linarith

theorem card_A1_le {M₁ : ℝ} (h0 : 0 < M₁) : ((A1 M₁).card : ℝ) ≤ 6 * M₁ := by
  have := Finset.card_union_le (dyadic M₁) ((dyadic M₁).map (Equiv.neg ℤ).toEmbedding)
  rw [Finset.card_map] at this
  have h2 : ((A1 M₁).card : ℝ) ≤ (dyadic M₁).card + (dyadic M₁).card := by exact_mod_cast this
  linarith [card_dyadic_le h0]

theorem card_Icc_le {K M₃ : ℝ} (hK : 0 < K) (h3 : 0 < M₃) :
    ((Finset.Icc (-⌊K * M₃⌋) ⌊K * M₃⌋).card : ℝ) ≤ 2 * K * M₃ + 1 := by
  have hk : 0 ≤ ⌊K * M₃⌋ := Int.floor_nonneg.2 (by positivity)
  have h1 : (⌊K * M₃⌋ : ℝ) ≤ K * M₃ := Int.floor_le _
  rw [Int.card_Icc, ← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  push_cast
  linarith

/-- `gsum` as one sum over triples. -/
theorem gsum_eq (K M₁ M₂ M₃ : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    gsum K M₁ M₂ M₃ f u = ∑ p ∈ A1 M₁ ×ˢ dyadic M₂ ×ˢ Finset.Icc (-⌊K * M₃⌋) ⌊K * M₃⌋,
      f ((p.1 * u + p.2.2) / p.2.1) := by
  rw [Finset.sum_product, gsum]
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  rw [Finset.sum_product]

/-- Change of variables for one term. -/
theorem integral_term (g : ℝ → ℝ) (m₁ m₂ m₃ : ℝ) (h1 : m₁ ≠ 0) (h2 : m₂ ≠ 0) :
    ∫ u, g ((m₁ * u + m₃) / m₂) = |m₂ / m₁| * ∫ u, g u := by
  have e : (fun u => g ((m₁ * u + m₃) / m₂)) = fun u => (fun y => g (y + m₃ / m₂)) ((m₁ / m₂) * u) := by
    funext u; congr 1; field_simp
  rw [e, Measure.integral_comp_mul_left (fun y => g (y + m₃ / m₂)) (m₁ / m₂),
    integral_add_right_eq_self, smul_eq_mul, inv_div]

theorem integrable_term {g : ℝ → ℝ} (hg : Integrable g) (m₁ m₂ m₃ : ℝ) (h1 : m₁ ≠ 0)
    (h2 : m₂ ≠ 0) : Integrable (fun u => g ((m₁ * u + m₃) / m₂)) := by
  have e : (fun u => g ((m₁ * u + m₃) / m₂)) = fun u => (fun y => g (y + m₃ / m₂)) ((m₁ / m₂) * u) := by
    funext u; congr 1; field_simp
  rw [e]
  exact (hg.comp_add_right (m₃ / m₂)).comp_mul_left' (div_ne_zero h1 h2)

/-- The trivial (Cauchy–Schwarz) bound `J(f) ≪ (1+K)² M⁶ ∫ f²`. -/
theorem lintegral_gsum_sq_le_trivial (C K : ℝ) (hC : 1 ≤ C) (hK : 0 < K) (f : ℝ → ℝ)
    (hf : Continuous f) (hnn : ∀ u, 0 ≤ f u) (hsupp : Function.support f ⊆ Set.Icc (1 / C) C)
    (M M₁ M₂ M₃ : ℝ) (h₁ : M₁ ∈ Set.Ioo 0 M) (h₂ : M₂ ∈ Set.Ioo 0 M) (h₃ : M₃ ∈ Set.Ioo 0 M) :
    ∫⁻ u : ℝ, ENNReal.ofReal (gsum K M₁ M₂ M₃ f u ^ 2) ≤
      ENNReal.ofReal (3000 * (1 + K) ^ 2 * M ^ 6 * ∫ u, f u ^ 2) := by
  obtain ⟨h10, h1M⟩ := h₁
  obtain ⟨h20, h2M⟩ := h₂
  obtain ⟨h30, h3M⟩ := h₃
  by_cases hM : M < 1 / 2
  · have : ∀ u, gsum K M₁ M₂ M₃ f u = 0 := by
      intro u; simp [gsum, dyadic_eq_empty h20 (by linarith : M₂ < 1 / 2)]
    simp [this]
  push Not at hM
  set P := A1 M₁ ×ˢ dyadic M₂ ×ˢ Finset.Icc (-⌊K * M₃⌋) ⌊K * M₃⌋ with hP
  set N : ℝ := (P.card : ℝ) with hN
  have hcs : HasCompactSupport f := cont_hcs hf hsupp
  have hcs2 : HasCompactSupport (fun u => f u ^ 2) :=
    HasCompactSupport.intro isCompact_Icc fun x hx => by
      have : f x = 0 := by by_contra h; exact hx (hsupp h)
      simp [this]
  have hf2 : Integrable (fun u => f u ^ 2) := (hf.pow 2).integrable_of_hasCompactSupport hcs2
  set I := ∫ u, f u ^ 2 with hI
  have hI0 : 0 ≤ I := integral_nonneg fun u => sq_nonneg _
  -- facts on P
  have hPmem : ∀ p ∈ P, (p.1 : ℝ) ≠ 0 ∧ (p.2.1 : ℝ) ≠ 0 ∧ |(p.2.1 : ℝ) / p.1| ≤ 2 * M₂ / M₁ := by
    intro p hp
    simp only [hP, Finset.mem_product] at hp
    obtain ⟨a1, a2⟩ := mem_A1 hp.1
    obtain ⟨b1, b2⟩ := mem_dyadic hp.2.1
    have hp1 : (p.1 : ℝ) ≠ 0 := by intro h; rw [h] at a1; simp at a1; linarith
    refine ⟨hp1, by intro h; rw [h] at b1; linarith, ?_⟩
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < p.2.1), div_le_div_iff₀ (by linarith) h10]
    nlinarith
  have hint : ∀ p ∈ P, Integrable (fun u => f ((p.1 * u + p.2.2) / p.2.1) ^ 2) := by
    intro p hp
    obtain ⟨a, b, -⟩ := hPmem p hp
    exact integrable_term hf2 _ _ _ a b
  have hsum_int : Integrable (fun u => N * ∑ p ∈ P, f ((p.1 * u + p.2.2) / p.2.1) ^ 2) :=
    (integrable_finsetSum P hint).const_mul N
  calc ∫⁻ u : ℝ, ENNReal.ofReal (gsum K M₁ M₂ M₃ f u ^ 2)
      ≤ ∫⁻ u : ℝ, ENNReal.ofReal (N * ∑ p ∈ P, f ((p.1 * u + p.2.2) / p.2.1) ^ 2) := by
        refine lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_
        rw [gsum_eq]
        exact sq_sum_le_card_mul_sum_sq
    _ = ENNReal.ofReal (∫ u, N * ∑ p ∈ P, f ((p.1 * u + p.2.2) / p.2.1) ^ 2) := by
        rw [ofReal_integral_eq_lintegral_ofReal hsum_int
          (Filter.Eventually.of_forall fun u => by positivity)]
    _ ≤ ENNReal.ofReal (3000 * (1 + K) ^ 2 * M ^ 6 * I) := by
        apply ENNReal.ofReal_le_ofReal
        rw [integral_const_mul, integral_finsetSum P hint]
        have hterm : ∀ p ∈ P, ∫ u, f ((p.1 * u + p.2.2) / p.2.1) ^ 2 ≤ 2 * M₂ / M₁ * I := by
          intro p hp
          obtain ⟨a, b, c⟩ := hPmem p hp
          rw [integral_term (fun y => f y ^ 2) _ _ _ a b]
          exact mul_le_mul_of_nonneg_right c hI0
        have hs : ∑ p ∈ P, ∫ u, f ((p.1 * u + p.2.2) / p.2.1) ^ 2 ≤ N * (2 * M₂ / M₁ * I) := by
          refine (Finset.sum_le_sum hterm).trans ?_
          rw [Finset.sum_const, nsmul_eq_mul]
        have hN0 : 0 ≤ N := by positivity
        have hNle : N ≤ 6 * M₁ * (3 * M * ((2 * K + 2) * M)) := by
          rw [hN, hP, Finset.card_product, Finset.card_product]
          push_cast
          have ha := card_A1_le h10
          have hb := card_dyadic_le h20
          have hc := card_Icc_le hK h30
          have hc' : 2 * K * M₃ + 1 ≤ (2 * K + 2) * M := by nlinarith
          have hb' : 3 * M₂ ≤ 3 * M := by linarith
          exact mul_le_mul ha (mul_le_mul (hb.trans hb') (hc.trans hc') (by positivity)
            (by positivity)) (by positivity) (by positivity)
        calc N * ∑ p ∈ P, ∫ u, f ((p.1 * u + p.2.2) / p.2.1) ^ 2
            ≤ N * (N * (2 * M₂ / M₁ * I)) := mul_le_mul_of_nonneg_left hs hN0
          _ = N * N * (2 * M₂ / M₁) * I := by ring
          _ ≤ (6 * M₁ * (3 * M * ((2 * K + 2) * M))) * (6 * M₁ * (3 * M * ((2 * K + 2) * M)))
                * (2 * M / M₁) * I := by
              gcongr
          _ = 2592 * M₁ * M ^ 5 * (1 + K) ^ 2 * I := by field_simp; ring
          _ ≤ 3000 * (1 + K) ^ 2 * M ^ 6 * I := by
              have : M₁ * M ^ 5 ≤ M ^ 6 := by
                have := pow_pos (by linarith : (0 : ℝ) < M) 5
                nlinarith
              have h0 : 0 ≤ (1 + K) ^ 2 * I := by positivity
              have h6 : 0 ≤ M ^ 6 := by positivity
              calc 2592 * M₁ * M ^ 5 * (1 + K) ^ 2 * I = 2592 * (M₁ * M ^ 5) * ((1 + K) ^ 2 * I) := by
                    ring
                _ ≤ 2592 * M ^ 6 * ((1 + K) ^ 2 * I) := by gcongr
                _ ≤ 3000 * M ^ 6 * ((1 + K) ^ 2 * I) := by gcongr; norm_num
                _ = 3000 * (1 + K) ^ 2 * M ^ 6 * I := by ring

end GuthMaynard.Affine.PartT
end

section
namespace GuthMaynard.Affine
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal
alias lintegral_gsum_sq_le_trivial := GuthMaynard.Affine.PartT.lintegral_gsum_sq_le_trivial

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartT
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal
/-- For tiny `T` the class contains only `0`. -/
theorem eq_zero_of_small (C : ℝ) (c : ℕ → ℝ → ℝ) (T : ℝ) (hT : 0 < T) (f : ℝ → ℝ)
    (hf : Adm C c T f) (hsmall : T * (2 * |c 0 1| + 2 * |c 2 1| + 1) < 1) (hT1 : T ≤ 1) :
    ∀ u, f u = 0 := by
  have hcont : Continuous f := hf.smooth.continuous
  set S := ⨆ u, f u with hSdef
  have hS : 0 ≤ S := Real.iSup_nonneg hf.nonneg
  set F : ℝ → ℂ := fun u => (f u : ℂ) with hF
  have hFc : Continuous F := continuous_ofReal.comp hcont
  have hFi : Integrable F :=
    (hcont.integrable_of_hasCompactSupport (cont_hcs hcont hf.supp)).ofReal
  have hFFc : Continuous (𝓕 F) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by fun_prop) hFi
  set a := |c 0 1| * T * S
  set b := |c 2 1| * T * S
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hbound : ∀ᵐ ξ : ℝ ∂volume, ‖𝓕 F ξ‖ ≤ prof a b 1 |ξ| := by
    filter_upwards [ae_ne_zero] with ξ hξ
    unfold prof
    split_ifs with h
    · refine (hf.decay 0 1 one_pos ξ hξ).trans ?_
      simp only [Real.rpow_one, pow_zero, mul_one, a]
      gcongr; exact le_abs_self _
    · refine (hf.decay 2 1 one_pos ξ hξ).trans ?_
      push Not at h
      have hξ2 : 0 < |ξ| ^ 2 := by positivity
      simp only [Real.rpow_one, b, div_pow]
      rw [mul_div_assoc', le_div_iff₀ hξ2]
      have hT2 : T ^ 2 ≤ 1 := pow_le_one₀ hT.le hT1
      calc c 2 1 * T * T ^ 2 / |ξ| ^ 2 * S * |ξ| ^ 2 = c 2 1 * T * S * T ^ 2 := by
            field_simp
        _ ≤ |c 2 1| * T * S * 1 := by
            gcongr
            · exact le_abs_self _
        _ = |c 2 1| * T * S := mul_one _
  have hint : Integrable (𝓕 F) :=
    (integrable_prof_abs ha hb one_pos).mono' hFFc.aestronglyMeasurable hbound
  have key : S ≤ 2 * (a + b) := by
    apply ciSup_le
    intro x
    have h1 := norm_le_integral_norm_fourier hFc hFi hint x
    have h2 : ∫ ξ, ‖𝓕 F ξ‖ ≤ ∫ ξ : ℝ, prof a b 1 |ξ| :=
      integral_mono_ae hint.norm (integrable_prof_abs ha hb one_pos) hbound
    rw [integral_prof_abs ha hb one_pos] at h2
    have h3 : f x ≤ ‖F x‖ := by
      simp only [F, Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
    linarith
  have hS0 : S = 0 := by
    by_contra hne
    have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hne)
    have : 2 * (a + b) = T * (2 * |c 0 1| + 2 * |c 2 1|) * S := by simp only [a, b]; ring
    have h4 : T * (2 * |c 0 1| + 2 * |c 2 1|) < 1 := by nlinarith
    nlinarith
  intro u
  have := le_sup_of hcont hf.supp u
  linarith [hf.nonneg u]

end GuthMaynard.Affine.PartT
end

section
namespace GuthMaynard.Affine
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal
alias eq_zero_of_small := GuthMaynard.Affine.PartT.eq_zero_of_small

alias Adm.mono := GuthMaynard.Affine.PartT.Adm.mono

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartT
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal
theorem decay_le {C : ℝ} {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Adm C c T f) (hT : 0 < T)
    (j : ℕ) (ξ : ℝ) (hξ : ξ ≠ 0) :
    ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ≤ |c j 1| * T ^ (j + 1) * (⨆ u, f u) / |ξ| ^ j := by
  have hS : 0 ≤ ⨆ u, f u := Real.iSup_nonneg hf.nonneg
  refine (hf.decay j 1 one_pos ξ hξ).trans ?_
  calc c j 1 * T ^ (1 : ℝ) * (T / |ξ|) ^ j * (⨆ u, f u)
      = c j 1 * T ^ (j + 1) * (⨆ u, f u) / |ξ| ^ j := by
        rw [Real.rpow_one, div_pow, pow_succ]; field_simp
    _ ≤ |c j 1| * T ^ (j + 1) * (⨆ u, f u) / |ξ| ^ j := by
        gcongr; exact le_abs_self _

theorem fourier_integrable {C : ℝ} {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Adm C c T f)
    (hT : 0 < T) : Integrable (𝓕 (fun u => (f u : ℂ))) := by
  have hcont : Continuous f := hf.smooth.continuous
  have hS : 0 ≤ ⨆ u, f u := Real.iSup_nonneg hf.nonneg
  have hFi : Integrable (fun u => (f u : ℂ)) :=
    (hcont.integrable_of_hasCompactSupport (cont_hcs hcont hf.supp)).ofReal
  have hFFc : Continuous (𝓕 (fun u => (f u : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hFi
  have ha : 0 ≤ |c 0 1| * T * ⨆ u, f u := by positivity
  have hb : 0 ≤ |c 2 1| * T ^ 3 * ⨆ u, f u := by positivity
  refine (integrable_prof_abs ha hb hT).mono' hFFc.aestronglyMeasurable ?_
  filter_upwards [ae_ne_zero] with ξ hξ
  unfold prof
  split_ifs with h
  · have := decay_le hf hT 0 ξ hξ
    simpa using this
  · exact decay_le hf hT 2 ξ hξ

theorem norm_e_sub_le (ξ x y : ℝ) :
    ‖((𝐞 (ξ * x) : ℂ) - 𝐞 (ξ * y))‖ ≤ 2 * Real.pi * (|ξ| * |x - y|) := by
  have e1 : (𝐞 (ξ * x) : ℂ) = 𝐞 (ξ * y) * 𝐞 (ξ * (x - y)) := by
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]; congr 2; ring
  rw [e1, ← mul_sub_one, norm_mul, Circle.norm_coe, one_mul, Real.fourierChar_apply, mul_comm]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans (le_of_eq ?_)
  rw [Real.norm_eq_abs]
  simp only [abs_mul, abs_two, abs_of_pos Real.pi_pos]

/-- The Lipschitz bound `|f x - f y| ≤ 4π(|c 0 1| + |c 3 1|) T³ S |x - y|`. -/
theorem lipschitz {C : ℝ} {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Adm C c T f) (hT : 0 < T)
    (x y : ℝ) : |f x - f y| ≤
      4 * Real.pi * (|c 0 1| + |c 3 1|) * T ^ 3 * (⨆ u, f u) * |x - y| := by
  have hcont : Continuous f := hf.smooth.continuous
  set S := ⨆ u, f u
  have hS : 0 ≤ S := Real.iSup_nonneg hf.nonneg
  set F : ℝ → ℂ := fun u => (f u : ℂ) with hF
  have hFc : Continuous F := continuous_ofReal.comp hcont
  have hFi : Integrable F :=
    (hcont.integrable_of_hasCompactSupport (cont_hcs hcont hf.supp)).ofReal
  have hFFc : Continuous (𝓕 F) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hFi
  have hint := fourier_integrable hf hT
  have hie : ∀ z : ℝ, Integrable (fun ξ : ℝ => 𝐞 (ξ * z) • 𝓕 F ξ) := by
    intro z
    refine hint.norm.mono' (Continuous.aestronglyMeasurable ?_)
      (Filter.Eventually.of_forall fun ξ => by rw [Circle.norm_smul])
    exact (Real.continuous_fourierChar.comp (continuous_id.mul continuous_const)).smul hFFc
  have ha : 0 ≤ |c 0 1| * T ^ 2 * S := by positivity
  have hb : 0 ≤ |c 3 1| * T ^ 4 * S := by positivity
  have hgi := (integrable_prof_abs ha hb hT).const_mul (2 * Real.pi * |x - y|)
  have hdiff : F x - F y = ∫ ξ, (𝐞 (ξ * x) • 𝓕 F ξ - 𝐞 (ξ * y) • 𝓕 F ξ) := by
    rw [integral_sub (hie x) (hie y), ← inversion hFc hFi hint, ← inversion hFc hFi hint]
  have hnorm : ‖F x - F y‖ ≤ ∫ ξ, 2 * Real.pi * |x - y| * prof (|c 0 1| * T ^ 2 * S)
      (|c 3 1| * T ^ 4 * S) T |ξ| := by
    rw [hdiff]
    refine norm_integral_le_of_norm_le hgi ?_
    filter_upwards [ae_ne_zero] with ξ hξ
    rw [Circle.smul_def, Circle.smul_def, ← sub_smul, norm_smul]
    have hbd : |ξ| * ‖𝓕 F ξ‖ ≤ prof (|c 0 1| * T ^ 2 * S) (|c 3 1| * T ^ 4 * S) T |ξ| := by
      unfold prof
      split_ifs with h
      · have := decay_le hf hT 0 ξ hξ
        simp only [zero_add, pow_one, pow_zero, div_one] at this
        calc |ξ| * ‖𝓕 F ξ‖ ≤ T * (|c 0 1| * T * S) := by
              gcongr
          _ = |c 0 1| * T ^ 2 * S := by ring
      · have := decay_le hf hT 3 ξ hξ
        have hξ0 : 0 < |ξ| := abs_pos.2 hξ
        calc |ξ| * ‖𝓕 F ξ‖ ≤ |ξ| * (|c 3 1| * T ^ (3 + 1) * S / |ξ| ^ 3) := by gcongr
          _ = |c 3 1| * T ^ 4 * S / |ξ| ^ 2 := by field_simp; ring
    calc ‖(𝐞 (ξ * x) : ℂ) - 𝐞 (ξ * y)‖ * ‖𝓕 F ξ‖
        ≤ 2 * Real.pi * (|ξ| * |x - y|) * ‖𝓕 F ξ‖ := by gcongr; exact norm_e_sub_le ξ x y
      _ = 2 * Real.pi * |x - y| * (|ξ| * ‖𝓕 F ξ‖) := by ring
      _ ≤ _ := by gcongr
  rw [integral_const_mul, integral_prof_abs ha hb hT] at hnorm
  have hFxy : |f x - f y| = ‖F x - F y‖ := by
    simp only [F, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hFxy]
  refine hnorm.trans (le_of_eq ?_)
  field_simp
  ring

/-- Mass lower bound: `S ≤ 2 Λ ∫ f` given a Lipschitz bound with constant `Λ S`. -/
theorem sup_le_mass {C : ℝ} {f : ℝ → ℝ} (hcont : Continuous f) (hnn : ∀ u, 0 ≤ f u)
    (hsupp : Function.support f ⊆ Set.Icc (1 / C) C) {Λ : ℝ} (hΛ : 0 < Λ)
    (hlip : ∀ x y, |f x - f y| ≤ Λ * (⨆ u, f u) * |x - y|) :
    (⨆ u, f u) ≤ 2 * Λ * ∫ u, f u := by
  set S := ⨆ u, f u
  have hcs := cont_hcs hcont hsupp
  have hint : Integrable f := hcont.integrable_of_hasCompactSupport hcs
  obtain ⟨x₀, hx₀⟩ := hcont.exists_forall_ge_of_hasCompactSupport hcs
  have hSx : S ≤ f x₀ := ciSup_le hx₀
  set r := 1 / (2 * Λ) with hr
  have hr0 : 0 < r := by positivity
  have hlow : ∀ y ∈ Set.Icc (x₀ - r) (x₀ + r), S / 2 ≤ f y := by
    intro y hy
    have h1 := hlip x₀ y
    have h2 : |x₀ - y| ≤ r := by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
    have h3 : Λ * S * |x₀ - y| ≤ Λ * S * r := by
      have : 0 ≤ Λ * S := mul_nonneg hΛ.le (Real.iSup_nonneg hnn)
      gcongr
    have h4 : Λ * S * r = S / 2 := by rw [hr]; field_simp
    have := (abs_le.1 h1).2
    linarith
  have h1 := setIntegral_ge_of_const_le (μ := volume) measurableSet_Icc
    (by simp) hlow hint.integrableOn
  have h2 : ∫ u in Set.Icc (x₀ - r) (x₀ + r), f u ≤ ∫ u, f u :=
    setIntegral_le_integral hint (Filter.Eventually.of_forall hnn)
  rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul] at h1
  have h5 : (x₀ + r - (x₀ - r)) * (S / 2) = S / (2 * Λ) := by rw [hr]; field_simp; ring
  rw [h5] at h1
  have := le_trans h1 h2
  rw [div_le_iff₀ (by positivity)] at this
  linarith

/-- Riemann-sum bound for sample points spaced `1/m₂`. -/
theorem riemann {C : ℝ} (hC : 1 ≤ C) {f : ℝ → ℝ} (hcont : Continuous f) (hnn : ∀ u, 0 ≤ f u)
    (hsupp : Function.support f ⊆ Set.Icc (1 / C) C) {Λ S : ℝ} (hΛS : 0 ≤ Λ * S)
    (hlip : ∀ x y, |f x - f y| ≤ Λ * S * |x - y|) {m₂ : ℝ} (hm₂ : 1 ≤ m₂) (a : ℝ)
    (s : Finset ℤ) :
    ∑ n ∈ s, f ((a + n) / m₂) ≤ m₂ * (∫ u, f u) + (C + 1) * (Λ * S) := by
  have hcs := cont_hcs hcont hsupp
  have hint : Integrable f := hcont.integrable_of_hasCompactSupport hcs
  have hm0 : 0 < m₂ := by linarith
  set h := 1 / m₂ with hh
  have hh0 : 0 < h := by positivity
  set x : ℤ → ℝ := fun n => (a + n) / m₂ with hx
  set I : ℤ → Set ℝ := fun n => Set.Ioc (x n) (x n + h) with hI
  set P : ℤ → Prop := fun n => x n ∈ Set.Icc (1 / C) C with hP
  classical
  -- one term
  have hone : ∀ n, f (x n) ≤ m₂ * (∫ u in I n, f u) + (if P n then Λ * S * h else 0) := by
    intro n
    have hI0 : 0 ≤ ∫ u in I n, f u := setIntegral_nonneg measurableSet_Ioc fun u _ => hnn u
    by_cases hp : P n
    · rw [if_pos hp]
      have hlow : ∀ y ∈ I n, f (x n) - Λ * S * h ≤ f y := by
        intro y hy
        have h1 := hlip (x n) y
        have h2 : |x n - y| ≤ h := by
          rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
        have h3 : Λ * S * |x n - y| ≤ Λ * S * h := mul_le_mul_of_nonneg_left h2 hΛS
        linarith [(abs_le.1 h1).2]
      have h1 := setIntegral_ge_of_const_le (μ := volume) measurableSet_Ioc
        (by simp) hlow hint.integrableOn
      rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul,
        add_sub_cancel_left] at h1
      have : m₂ * h = 1 := by rw [hh]; field_simp
      nlinarith
    · rw [if_neg hp]
      have : f (x n) = 0 := by
        by_contra hne; exact hp (hsupp hne)
      rw [this, add_zero]; exact mul_nonneg hm0.le hI0
  -- sum of the integrals
  have hdisj : Set.Pairwise (↑s) (Function.onFun Disjoint I) := by
    intro n _ n' _ hnn'
    refine Set.disjoint_left.2 fun y hy hy' => hnn' ?_
    simp only [hI, hx, Set.mem_Ioc] at hy hy'
    have k1 : a + n < m₂ * y := by rw [div_lt_iff₀ hm0] at hy; linarith [hy.1]
    have k2 : m₂ * y ≤ a + n + 1 := by
      have := hy.2; rw [hh, ← add_div, le_div_iff₀ hm0] at this; linarith
    have k3 : a + n' < m₂ * y := by rw [div_lt_iff₀ hm0] at hy'; linarith [hy'.1]
    have k4 : m₂ * y ≤ a + n' + 1 := by
      have := hy'.2; rw [hh, ← add_div, le_div_iff₀ hm0] at this; linarith
    have e1 : (n : ℝ) < n' + 1 := by linarith
    have e2 : (n' : ℝ) < n + 1 := by linarith
    have e1' : n < n' + 1 := by exact_mod_cast e1
    have e2' : n' < n + 1 := by exact_mod_cast e2
    omega
  have hsumI : ∑ n ∈ s, ∫ u in I n, f u ≤ ∫ u, f u := by
    rw [← integral_biUnion_finset s (fun n _ => measurableSet_Ioc) hdisj
      (fun n _ => hint.integrableOn)]
    exact setIntegral_le_integral hint (Filter.Eventually.of_forall hnn)
  -- counting
  have hcount : ((s.filter P).card : ℝ) ≤ m₂ * C + 1 := by
    have hsub : s.filter P ⊆ Finset.Icc ⌈m₂ / C - a⌉ ⌊m₂ * C - a⌋ := by
      intro n hn
      simp only [Finset.mem_filter, hP, hx, Set.mem_Icc] at hn
      obtain ⟨-, h1, h2⟩ := hn
      have hC0 : 0 < C := by linarith
      rw [div_le_div_iff₀ hC0 hm0, one_mul] at h1
      rw [div_le_iff₀ hm0] at h2
      simp only [Finset.mem_Icc]
      constructor
      · have : m₂ / C ≤ a + n := by rw [div_le_iff₀ hC0]; linarith
        rw [Int.ceil_le]; linarith
      · rw [Int.le_floor]; linarith
    have hc := Finset.card_le_card hsub
    have hC0 : 0 < C := by linarith
    have hab : m₂ / C - a ≤ m₂ * C - a := by
      have : m₂ / C ≤ m₂ * C := by
        have : 1 ≤ C * C := by nlinarith
        rw [div_le_iff₀ hC0]; nlinarith
      linarith
    have k1 : (⌊m₂ * C - a⌋ : ℝ) ≤ m₂ * C - a := Int.floor_le _
    have k2 : m₂ / C - a ≤ (⌈m₂ / C - a⌉ : ℝ) := Int.le_ceil _
    have hcI : ((Finset.Icc ⌈m₂ / C - a⌉ ⌊m₂ * C - a⌋).card : ℝ) ≤ m₂ * C + 1 := by
      rw [Int.card_Icc]
      rcases le_or_gt (⌊m₂ * C - a⌋ + 1 - ⌈m₂ / C - a⌉) 0 with hle | hlt
      · rw [Int.toNat_of_nonpos hle]; simp; nlinarith
      · rw [← Int.cast_natCast, Int.toNat_of_nonneg hlt.le]; push_cast
        have : 0 ≤ m₂ / C := by positivity
        linarith
    exact (by exact_mod_cast hc : ((s.filter P).card : ℝ) ≤ _).trans hcI
  calc ∑ n ∈ s, f ((a + n) / m₂) = ∑ n ∈ s, f (x n) := rfl
    _ ≤ ∑ n ∈ s, (m₂ * (∫ u in I n, f u) + (if P n then Λ * S * h else 0)) :=
        Finset.sum_le_sum fun n _ => hone n
    _ = m₂ * (∑ n ∈ s, ∫ u in I n, f u) + ((s.filter P).card : ℝ) * (Λ * S * h) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter, Finset.sum_const,
          nsmul_eq_mul]
    _ ≤ m₂ * (∫ u, f u) + (m₂ * C + 1) * (Λ * S * h) := by gcongr
    _ ≤ m₂ * (∫ u, f u) + (C + 1) * (Λ * S) := by
        have e : (m₂ * C + 1) * (Λ * S * h) = (C + h) * (Λ * S) := by rw [hh]; field_simp
        rw [e]
        have : h ≤ 1 := by rw [hh, div_le_one hm0]; exact hm₂
        gcongr

/-- Large `M` (paper p. 30, first paragraph of the proof of Lemma 9.2). -/
theorem lintegral_gsum_sq_le_of_large (C : ℝ) (c : ℕ → ℝ → ℝ) (K : ℝ) (hC : 1 ≤ C) (hK : 0 < K) :
    ∃ A T₁ : ℝ, ∀ T : ℝ, T₁ ≤ T → ∀ f : ℝ → ℝ, Adm C c T f → ∀ M : ℝ, T ^ 6 ≤ M →
      ∀ M₁ M₂ M₃ : ℝ, M₁ ∈ Set.Ioo 0 M → M₂ ∈ Set.Ioo 0 M → M₃ ∈ Set.Ioo 0 M →
      ∫⁻ u : ℝ, ENNReal.ofReal (gsum K M₁ M₂ M₃ f u ^ 2) ≤
        ENNReal.ofReal (A * M ^ 6 * (∫ u, f u) ^ 2) := by
  set κ := 4 * Real.pi * (|c 0 1| + |c 3 1|) + 1 with hκ
  have hκ0 : 0 < κ := by positivity
  set B₀ := 2 + 2 * (C + 1) * κ ^ 2 with hB₀
  have hB₀0 : 0 < B₀ := by positivity
  refine ⟨648 * B₀ ^ 2 * (2 * C + K), 1, ?_⟩
  intro T hT1 f hf M hT6 M₁ M₂ M₃ h₁ h₂ h₃
  obtain ⟨h10, h1M⟩ := h₁
  obtain ⟨h20, h2M⟩ := h₂
  obtain ⟨h30, h3M⟩ := h₃
  have hT : 0 < T := by linarith
  have hC0 : 0 < C := by linarith
  have hcont : Continuous f := hf.smooth.continuous
  have hnn := hf.nonneg
  have hsupp := hf.supp
  set S := ⨆ u, f u with hSdef
  have hS : 0 ≤ S := Real.iSup_nonneg hnn
  set I := ∫ u, f u with hIdef
  have hI0 : 0 ≤ I := integral_nonneg hnn
  set Λ := κ * T ^ 3 with hΛ
  have hΛ0 : 0 < Λ := by positivity
  have hlip : ∀ x y, |f x - f y| ≤ Λ * S * |x - y| := by
    intro x y
    refine (lipschitz hf hT x y).trans ?_
    have : 4 * Real.pi * (|c 0 1| + |c 3 1|) ≤ κ := by rw [hκ]; linarith
    calc 4 * Real.pi * (|c 0 1| + |c 3 1|) * T ^ 3 * S * |x - y|
        = (4 * Real.pi * (|c 0 1| + |c 3 1|)) * (T ^ 3 * S * |x - y|) := by ring
      _ ≤ κ * (T ^ 3 * S * |x - y|) := by gcongr
      _ = Λ * S * |x - y| := by rw [hΛ]; ring
  have hmass : S ≤ 2 * Λ * I := sup_le_mass hcont hnn hsupp hΛ0 hlip
  have hΛ2 : Λ ^ 2 ≤ κ ^ 2 * M := by
    rw [hΛ, mul_pow, ← pow_mul]; gcongr
  -- the inner sum
  have hinner : ∀ m₁ : ℤ, ∀ m₂ ∈ dyadic M₂, ∀ u : ℝ,
      ∑ m₃ ∈ Finset.Icc (-⌊K * M₃⌋) ⌊K * M₃⌋, f ((m₁ * u + m₃) / m₂) ≤ B₀ * M * I := by
    intro m₁ m₂ hm₂ u
    obtain ⟨d1, d2⟩ := mem_dyadic hm₂
    have hm₂pos : (0 : ℤ) < m₂ := by exact_mod_cast (h20.trans d1)
    have hm₂1 : (1 : ℝ) ≤ m₂ := by exact_mod_cast hm₂pos
    have hr := riemann hC hcont hnn hsupp (mul_nonneg hΛ0.le hS) hlip hm₂1 (m₁ * u)
      (Finset.Icc (-⌊K * M₃⌋) ⌊K * M₃⌋)
    refine hr.trans ?_
    have e1 : (m₂ : ℝ) * I ≤ 2 * M * I := by
      gcongr; linarith
    have e2 : (C + 1) * (Λ * S) ≤ 2 * (C + 1) * κ ^ 2 * M * I := by
      calc (C + 1) * (Λ * S) ≤ (C + 1) * (Λ * (2 * Λ * I)) := by gcongr
        _ = 2 * (C + 1) * Λ ^ 2 * I := by ring
        _ ≤ 2 * (C + 1) * (κ ^ 2 * M) * I := by gcongr
        _ = 2 * (C + 1) * κ ^ 2 * M * I := by ring
    calc (m₂ : ℝ) * I + (C + 1) * (Λ * S) ≤ 2 * M * I + 2 * (C + 1) * κ ^ 2 * M * I := by
          linarith
      _ = B₀ * M * I := by rw [hB₀]; ring
  have hgnn : ∀ u, 0 ≤ gsum K M₁ M₂ M₃ f u := by
    intro u; unfold gsum
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => hnn _
  set B := 18 * B₀ * M₁ * M ^ 2 * I with hB
  have hgle : ∀ u, gsum K M₁ M₂ M₃ f u ≤ B := by
    intro u
    unfold gsum
    calc ∑ m₁ ∈ A1 M₁, ∑ m₂ ∈ dyadic M₂, ∑ m₃ ∈ Finset.Icc (-⌊K * M₃⌋) ⌊K * M₃⌋,
          f ((m₁ * u + m₃) / m₂)
        ≤ ∑ m₁ ∈ A1 M₁, ∑ m₂ ∈ dyadic M₂, B₀ * M * I :=
          Finset.sum_le_sum fun m₁ _ => Finset.sum_le_sum fun m₂ hm₂ => hinner m₁ m₂ hm₂ u
      _ = ((A1 M₁).card : ℝ) * (((dyadic M₂).card : ℝ) * (B₀ * M * I)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (6 * M₁) * ((3 * M) * (B₀ * M * I)) := by
          have h3 : ((dyadic M₂).card : ℝ) ≤ 3 * M := (card_dyadic_le h20).trans (by linarith)
          have hM0 : 0 < M := h10.trans h1M
          exact mul_le_mul (card_A1_le h10) (mul_le_mul_of_nonneg_right h3 (by positivity))
            (by positivity) (by positivity)
      _ = B := by rw [hB]; ring
  set R := (2 * C + K) * M / M₁ with hR
  have hR0 : 0 ≤ R := by have : 0 < M := h10.trans h1M; positivity
  have hzero : ∀ u, u ∉ Set.Icc (-R) R → gsum K M₁ M₂ M₃ f u = 0 := by
    intro u hu
    have hu' : R < |u| := by
      by_contra h; push Not at h; exact hu (abs_le.1 h)
    unfold gsum
    refine Finset.sum_eq_zero fun m₁ hm₁ => Finset.sum_eq_zero fun m₂ hm₂ =>
      Finset.sum_eq_zero fun m₃ hm₃ => ?_
    by_contra hne
    obtain ⟨z1, z2⟩ := hsupp hne
    obtain ⟨a1, a2⟩ := mem_A1 hm₁
    obtain ⟨d1, d2⟩ := mem_dyadic hm₂
    have hm₂0 : (0 : ℝ) < m₂ := h20.trans d1
    have hz0 : 0 < 1 / C := by positivity
    have k1 : |(m₁ : ℝ) * u + m₃| ≤ 2 * C * M := by
      have e : (m₁ : ℝ) * u + m₃ = ((m₁ * u + m₃) / m₂) * m₂ := by field_simp
      rw [e, abs_mul, abs_of_pos (hz0.trans_le z1), abs_of_pos hm₂0]
      calc ((m₁ : ℝ) * u + m₃) / m₂ * m₂ ≤ C * (2 * M₂) := by gcongr
        _ ≤ 2 * C * M := by nlinarith
    have k2 : |(m₃ : ℝ)| ≤ K * M := by
      rw [Finset.mem_Icc] at hm₃
      have f1 : (⌊K * M₃⌋ : ℝ) ≤ K * M₃ := Int.floor_le _
      have g1 : (-⌊K * M₃⌋ : ℝ) ≤ m₃ := by exact_mod_cast hm₃.1
      have g2 : (m₃ : ℝ) ≤ ⌊K * M₃⌋ := by exact_mod_cast hm₃.2
      have : K * M₃ ≤ K * M := by gcongr
      rw [abs_le]; constructor <;> linarith
    have k3 : |(m₁ : ℝ)| * |u| ≤ (2 * C + K) * M := by
      rw [← abs_mul]
      have := abs_sub (↑m₁ * u + ↑m₃) (m₃ : ℝ)
      simp only [add_sub_cancel_right] at this
      linarith
    have k4 : M₁ * |u| < |(m₁ : ℝ)| * |u| := by
      have : 0 < |u| := hR0.trans_lt hu'
      gcongr
    have k5 : R * M₁ < |u| * M₁ := by gcongr
    have k6 : R * M₁ = (2 * C + K) * M := by rw [hR]; field_simp
    linarith
  calc ∫⁻ u : ℝ, ENNReal.ofReal (gsum K M₁ M₂ M₃ f u ^ 2)
      ≤ ∫⁻ u : ℝ, (Set.Icc (-R) R).indicator (fun _ => ENNReal.ofReal (B ^ 2)) u := by
        refine lintegral_mono fun u => ?_
        by_cases hu : u ∈ Set.Icc (-R) R
        · rw [Set.indicator_of_mem hu]
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hgnn u) (hgle u) 2)
        · rw [hzero u hu]; simp
    _ = ENNReal.ofReal (B ^ 2) * volume (Set.Icc (-R) R) :=
        lintegral_indicator_const measurableSet_Icc _
    _ = ENNReal.ofReal (B ^ 2 * (2 * R)) := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul (sq_nonneg _)]; congr 1; ring
    _ ≤ ENNReal.ofReal (648 * B₀ ^ 2 * (2 * C + K) * M ^ 6 * I ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        have e : B ^ 2 * (2 * R) = 648 * B₀ ^ 2 * (2 * C + K) * I ^ 2 * M ^ 5 * M₁ := by
          rw [hB, hR]; field_simp; ring
        rw [e]
        have : 0 ≤ 648 * B₀ ^ 2 * (2 * C + K) * I ^ 2 * M ^ 5 := by
          have : 0 < M := h10.trans h1M
          positivity
        calc 648 * B₀ ^ 2 * (2 * C + K) * I ^ 2 * M ^ 5 * M₁
            ≤ 648 * B₀ ^ 2 * (2 * C + K) * I ^ 2 * M ^ 5 * M := by gcongr
          _ = 648 * B₀ ^ 2 * (2 * C + K) * M ^ 6 * I ^ 2 := by ring

end GuthMaynard.Affine.PartT
end

section
namespace GuthMaynard.Affine
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal
alias lintegral_gsum_sq_le_of_large := GuthMaynard.Affine.PartT.lintegral_gsum_sq_le_of_large

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
/-! ## Fixed objects -/


























end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

/-! ### Large `M`: Lipschitz bound, mass lower bound, Riemann sums -/

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartR
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartR
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartZ
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartZ
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartR
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartR
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartR
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartR
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal


end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartZ
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartZ
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartZ
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartZ
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal



end GuthMaynard.Affine
end

namespace GuthMaynard.Affine
end GuthMaynard.Affine

namespace GuthMaynard.Affine.PartA

open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal

/-- Pure algebra of one iteration step. -/
theorem step_alg {A₁ A₂ a t X Y W Z Jg : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (ha : 0 ≤ a)
    (ht : 1 ≤ t) (hX : 0 ≤ X) (hXW : X ≤ W) (hY : 0 ≤ Y) (hXZ : X * Z ≤ W ^ 2)
    (hJ : Jg ≤ A₂ * t ^ 2 * (a ^ 2 * Y + a * Z)) :
    A₁ * t * (Y + Real.sqrt (X * Jg)) ≤
      A₁ * (1 + Real.sqrt A₂ * (a + Real.sqrt a)) * t ^ 2 * (Y + W) := by
  have hW : 0 ≤ W := hX.trans hXW
  have sA := Real.sqrt_nonneg A₂
  have sa := Real.sqrt_nonneg a
  have hsA : Real.sqrt A₂ ^ 2 = A₂ := Real.sq_sqrt hA₂
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have ht0 : 0 ≤ t := by linarith
  have key : Real.sqrt (X * Jg) ≤ t * Real.sqrt A₂ * (a * (X + Y) / 2 + Real.sqrt a * W) := by
    rw [Real.sqrt_le_left]
    · have h1 : X * Jg ≤ X * (A₂ * t ^ 2 * (a ^ 2 * Y + a * Z)) := mul_le_mul_of_nonneg_left hJ hX
      have h2 : (X + Y) ^ 2 / 4 ≥ X * Y := by nlinarith [sq_nonneg (X - Y)]
      have h3 : A₂ * t ^ 2 ≥ 0 := by positivity
      have h4 : a * Real.sqrt a * (X + Y) * W ≥ 0 := by positivity
      calc X * Jg ≤ X * (A₂ * t ^ 2 * (a ^ 2 * Y + a * Z)) := h1
        _ = A₂ * t ^ 2 * (a ^ 2 * (X * Y) + a * (X * Z)) := by ring
        _ ≤ A₂ * t ^ 2 * (a ^ 2 * ((X + Y) ^ 2 / 4) + a * W ^ 2 + a * Real.sqrt a * (X + Y) * W) := by
            apply mul_le_mul_of_nonneg_left _ h3
            nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg a), mul_le_mul_of_nonneg_left hXZ ha]
        _ = (t * Real.sqrt A₂ * (a * (X + Y) / 2 + Real.sqrt a * W)) ^ 2 := by
            linear_combination (-(A₂ * t ^ 2 * W ^ 2)) * hsa -
              (t ^ 2 * (a * (X + Y) / 2 + Real.sqrt a * W) ^ 2) * hsA
    · positivity
  have hYW : 0 ≤ Y + W := by linarith
  have e1 : a * (X + Y) / 2 + Real.sqrt a * W ≤ (a + Real.sqrt a) * (Y + W) := by
    nlinarith [mul_nonneg ha hW, mul_nonneg ha hY, mul_nonneg sa hY, mul_le_mul_of_nonneg_left hXW ha]
  have e2 : Y + Real.sqrt (X * Jg) ≤ t * ((1 + Real.sqrt A₂ * (a + Real.sqrt a)) * (Y + W)) := by
    have := mul_le_mul_of_nonneg_left e1 (mul_nonneg ht0 sA)
    have h5 : Y ≤ t * Y := by nlinarith
    have h6 : 0 ≤ t * W := by positivity
    nlinarith
  calc A₁ * t * (Y + Real.sqrt (X * Jg))
      ≤ A₁ * t * (t * ((1 + Real.sqrt A₂ * (a + Real.sqrt a)) * (Y + W))) :=
        mul_le_mul_of_nonneg_left e2 (by positivity)
    _ = _ := by ring

theorem J_le_of_forall {M K : ℝ} {f : ℝ → ℝ} {x : ℝ≥0∞}
    (h : ∀ M₁ M₂ M₃ : ℝ, M₁ ∈ Set.Ioo 0 M → M₂ ∈ Set.Ioo 0 M → M₃ ∈ Set.Ioo 0 M →
      ∫⁻ u : ℝ, ENNReal.ofReal (gsum K M₁ M₂ M₃ f u ^ 2) ≤ x) : J M K f ≤ x := by
  rw [J_eq]
  exact iSup₂_le fun M₁ h₁ => iSup₂_le fun M₂ h₂ => iSup₂_le fun M₃ h₃ => h M₁ M₂ M₃ h₁ h₂ h₃

theorem rpow_half_sq {M : ℝ} (hM : 0 ≤ M) (r : ℝ) : (M ^ (r / 2)) ^ 2 = M ^ r := by
  rw [← Real.rpow_mul_natCast hM]; norm_num

theorem XZ_le {M F r : ℝ} (hM : 0 ≤ M) :
    (M ^ 4 * F) * (M ^ 4 * (1 + M ^ r) * F) ≤ (M ^ 4 * (1 + M ^ (r / 2)) * F) ^ 2 := by
  have h := rpow_half_sq hM r
  have h0 : 0 ≤ M ^ (r / 2) := Real.rpow_nonneg hM _
  have : (1 + M ^ r) ≤ (1 + M ^ (r / 2)) ^ 2 := by nlinarith
  calc (M ^ 4 * F) * (M ^ 4 * (1 + M ^ r) * F) = (M ^ 4 * F) ^ 2 * (1 + M ^ r) := by ring
    _ ≤ (M ^ 4 * F) ^ 2 * (1 + M ^ (r / 2)) ^ 2 := by gcongr
    _ = _ := by ring

theorem r_succ (i : ℕ) : (2 : ℝ) / 2 ^ (i + 1) = (2 / 2 ^ i) / 2 := by
  rw [pow_succ, div_div]

/-- The induction statement `P(i)`. -/
def Pst (i : ℕ) : Prop :=
  ∀ (C : ℝ) (c : ℕ → ℝ → ℝ) (K : ℝ), 1 ≤ C → 0 < K → ∀ η : ℝ, 0 < η →
    ∃ A T₁ : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T₁ ≤ T → ∀ f : ℝ → ℝ, Adm C c T f → ∀ M : ℝ, 0 < M →
      M ≤ T ^ 6 → J M K f ≤ ENNReal.ofReal (A * T ^ η *
        (M ^ 6 * (∫ u, f u) ^ 2 + M ^ 4 * (1 + M ^ ((2 : ℝ) / 2 ^ i)) * ∫ u, f u ^ 2))

theorem P_zero : Pst 0 := by
  intro C c K hC hK η hη
  refine ⟨3000 * (1 + K) ^ 2, 1, by positivity, ?_⟩
  intro T hT f hf M hM _
  refine J_le_of_forall fun M₁ M₂ M₃ h₁ h₂ h₃ => ?_
  refine (lintegral_gsum_sq_le_trivial C K hC hK f hf.smooth.continuous hf.nonneg hf.supp
    M M₁ M₂ M₃ h₁ h₂ h₃).trans (ENNReal.ofReal_le_ofReal ?_)
  have F1 : 0 ≤ ∫ u, f u := integral_nonneg hf.nonneg
  have F2 : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hTη : 1 ≤ T ^ η := Real.one_le_rpow hT hη.le
  simp only [pow_zero, div_one]
  rw [show M ^ (2 : ℝ) = M ^ 2 from Real.rpow_two M]
  have h0 : 0 ≤ 3000 * (1 + K) ^ 2 := by positivity
  have hV : M ^ 6 * (∫ u, f u ^ 2) ≤ M ^ 6 * (∫ u, f u) ^ 2 + M ^ 4 * (1 + M ^ 2) * ∫ u, f u ^ 2 := by
    nlinarith [mul_nonneg (pow_nonneg hM.le 4) F2, mul_nonneg (pow_nonneg hM.le 6) (sq_nonneg (∫ u, f u))]
  have hV0 : 0 ≤ M ^ 6 * (∫ u, f u) ^ 2 + M ^ 4 * (1 + M ^ 2) * ∫ u, f u ^ 2 := by positivity
  calc 3000 * (1 + K) ^ 2 * M ^ 6 * ∫ u, f u ^ 2
      = 3000 * (1 + K) ^ 2 * (M ^ 6 * ∫ u, f u ^ 2) := by ring
    _ ≤ 3000 * (1 + K) ^ 2 * (M ^ 6 * (∫ u, f u) ^ 2 + M ^ 4 * (1 + M ^ 2) * ∫ u, f u ^ 2) :=
        mul_le_mul_of_nonneg_left hV h0
    _ ≤ 3000 * (1 + K) ^ 2 * T ^ η * (M ^ 6 * (∫ u, f u) ^ 2 + M ^ 4 * (1 + M ^ 2) * ∫ u, f u ^ 2) := by
        rw [mul_assoc _ (T ^ η)]
        exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hV0 hTη) h0

theorem P_succ (i : ℕ) (ih : Pst i) : Pst (i + 1) := by
  intro C c K hC hK η hη
  obtain ⟨A₁, T₁, c', hit⟩ := iteration C c K hC hK (η / 2) (half_pos hη)
  obtain ⟨A₂, T₂, hA₂, hP⟩ := ih (2 * C) c' (8 * C) (by linarith) (by linarith) η hη
  have ha : 0 ≤ max A₁ 0 := le_max_right _ _
  refine ⟨max A₁ 0 * (1 + Real.sqrt A₂ * (max A₁ 0 + Real.sqrt (max A₁ 0))),
    max (max T₁ T₂) 1, by positivity, ?_⟩
  intro T hT f hf M hM hMT
  have hT1 : T₁ ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans hT)
  have hT2 : T₂ ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans hT)
  have hT' : 1 ≤ T := (le_max_right _ _).trans hT
  obtain ⟨g, hg, hg1, hg2, hJ⟩ := hit T hT1 f hf
  have hJg := hP T hT2 g hg M hM hMT
  have F1 : 0 ≤ ∫ u, f u := integral_nonneg hf.nonneg
  have F2 : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have G1 : 0 ≤ ∫ u, g u := integral_nonneg hg.nonneg
  have G2 : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hG1 : ∫ u, g u ≤ max A₁ 0 * ∫ u, f u :=
    hg1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) F1)
  have hG2 : ∫ u, g u ^ 2 ≤ max A₁ 0 * ∫ u, f u ^ 2 :=
    hg2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) F2)
  have hT0 : 0 ≤ T := by linarith
  have hM0 := hM.le
  have hr0 : 0 ≤ M ^ ((2 : ℝ) / 2 ^ i) := Real.rpow_nonneg hM0 _
  have hJr : (J M (8 * C) g).toReal ≤ A₂ * (T ^ (η / 2)) ^ 2 *
      (max A₁ 0 ^ 2 * (M ^ 6 * (∫ u, f u) ^ 2) +
        max A₁ 0 * (M ^ 4 * (1 + M ^ ((2 : ℝ) / 2 ^ i)) * ∫ u, f u ^ 2)) := by
    rw [rpow_half_sq hT0]
    refine (ENNReal.toReal_le_of_le_ofReal (by positivity) hJg).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have e1 : (∫ u, g u) ^ 2 ≤ (max A₁ 0 * ∫ u, f u) ^ 2 := pow_le_pow_left₀ G1 hG1 2
    have e2 : M ^ 4 * (1 + M ^ ((2 : ℝ) / 2 ^ i)) * ∫ u, g u ^ 2 ≤
        M ^ 4 * (1 + M ^ ((2 : ℝ) / 2 ^ i)) * (max A₁ 0 * ∫ u, f u ^ 2) :=
      mul_le_mul_of_nonneg_left hG2 (by positivity)
    have e3 : M ^ 6 * (∫ u, g u) ^ 2 ≤ M ^ 6 * (max A₁ 0 * ∫ u, f u) ^ 2 :=
      mul_le_mul_of_nonneg_left e1 (by positivity)
    nlinarith
  have ht : 1 ≤ T ^ (η / 2) := Real.one_le_rpow hT' (by linarith)
  have key := step_alg (A₁ := max A₁ 0) (A₂ := A₂) (a := max A₁ 0) (t := T ^ (η / 2))
    (X := M ^ 4 * ∫ u, f u ^ 2) (Y := M ^ 6 * (∫ u, f u) ^ 2)
    (W := M ^ 4 * (1 + M ^ ((2 : ℝ) / 2 ^ i / 2)) * ∫ u, f u ^ 2)
    (Z := M ^ 4 * (1 + M ^ ((2 : ℝ) / 2 ^ i)) * ∫ u, f u ^ 2)
    (Jg := (J M (8 * C) g).toReal) ha hA₂ ha ht (by positivity)
    (by
      have : 0 ≤ M ^ ((2 : ℝ) / 2 ^ i / 2) := Real.rpow_nonneg hM0 _
      nlinarith [mul_nonneg (pow_nonneg hM0 4) F2])
    (by positivity) (XZ_le hM0) hJr
  refine J_le_of_forall fun M₁ M₂ M₃ h₁ h₂ h₃ =>
    (hJ M hM hMT M₁ M₂ M₃ h₁ h₂ h₃).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [r_succ i, ← rpow_half_sq hT0 η]
  refine le_trans ?_ key
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

theorem P_all (i : ℕ) : Pst i := by
  induction i with
  | zero => exact P_zero
  | succ i ih => exact P_succ i ih

theorem main (K C : ℝ) (hK : 0 < K) (hC : 1 ≤ C) (c₀ : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B Ts : ℝ, 0 ≤ B ∧ 1 ≤ Ts ∧ ∀ T : ℝ, Ts ≤ T → ∀ f : ℝ → ℝ, Adm C c₀ T f →
      ∀ M : ℝ, 0 < M →
        J M K f ≤ ENNReal.ofReal (B * T ^ δ * (M ^ 6 * (∫ u, f u) ^ 2 + M ^ 4 * ∫ u, f u ^ 2)) := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (24 / δ) (one_lt_two : (1 : ℝ) < 2)
  have hk' : ((6 : ℕ) : ℝ) * ((2 : ℝ) / 2 ^ k) ≤ δ / 2 := by
    have h2 : (0 : ℝ) < 2 ^ k := by positivity
    rw [div_lt_iff₀ hδ] at hk
    rw [mul_div_assoc', div_le_div_iff₀ h2 two_pos]
    push_cast; nlinarith
  obtain ⟨A, T₁, hA, hP⟩ := P_all k C c₀ K hC hK (δ / 2) (half_pos hδ)
  obtain ⟨A', T₁', hL⟩ := lintegral_gsum_sq_le_of_large C c₀ K hC hK
  have ha' : 0 ≤ max A' 0 := le_max_right _ _
  refine ⟨2 * A + max A' 0, max (max T₁ T₁') 1, by positivity, le_max_right _ _, ?_⟩
  intro T hT f hf M hM
  have hT1 : T₁ ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans hT)
  have hT2 : T₁' ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans hT)
  have hT' : 1 ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 ≤ T := by linarith
  have F1 : 0 ≤ ∫ u, f u := integral_nonneg hf.nonneg
  have F2 : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hM0 := hM.le
  have hY : 0 ≤ M ^ 6 * (∫ u, f u) ^ 2 := by positivity
  have hX : 0 ≤ M ^ 4 * ∫ u, f u ^ 2 := by positivity
  have hTd : 1 ≤ T ^ δ := Real.one_le_rpow hT' hδ.le
  have ht : 1 ≤ T ^ (δ / 2) := Real.one_le_rpow hT' (by linarith)
  rcases le_or_gt M (T ^ 6) with hMT | hMT
  · refine (hP T hT1 f hf M hM hMT).trans (ENNReal.ofReal_le_ofReal ?_)
    have hr : M ^ ((2 : ℝ) / 2 ^ k) ≤ T ^ (δ / 2) := by
      calc M ^ ((2 : ℝ) / 2 ^ k) ≤ (T ^ 6) ^ ((2 : ℝ) / 2 ^ k) :=
            Real.rpow_le_rpow hM0 hMT (by positivity)
        _ = T ^ (((6 : ℕ) : ℝ) * ((2 : ℝ) / 2 ^ k)) := (Real.rpow_natCast_mul hT0 6 _).symm
        _ ≤ T ^ (δ / 2) := Real.rpow_le_rpow_of_exponent_le hT' hk'
    have hV : M ^ 6 * (∫ u, f u) ^ 2 + M ^ 4 * (1 + M ^ ((2 : ℝ) / 2 ^ k)) * ∫ u, f u ^ 2 ≤
        2 * T ^ (δ / 2) * (M ^ 6 * (∫ u, f u) ^ 2 + M ^ 4 * ∫ u, f u ^ 2) := by
      have : M ^ 4 * (1 + M ^ ((2 : ℝ) / 2 ^ k)) * ∫ u, f u ^ 2 ≤
          M ^ 4 * (1 + T ^ (δ / 2)) * ∫ u, f u ^ 2 := by gcongr
      nlinarith
    have e : T ^ δ = T ^ (δ / 2) * T ^ (δ / 2) := by rw [← sq, rpow_half_sq hT0]
    calc A * T ^ (δ / 2) * (M ^ 6 * (∫ u, f u) ^ 2 + M ^ 4 * (1 + M ^ ((2 : ℝ) / 2 ^ k)) * ∫ u, f u ^ 2)
        ≤ A * T ^ (δ / 2) * (2 * T ^ (δ / 2) * (M ^ 6 * (∫ u, f u) ^ 2 + M ^ 4 * ∫ u, f u ^ 2)) :=
          mul_le_mul_of_nonneg_left hV (by positivity)
      _ = 2 * A * T ^ δ * (M ^ 6 * (∫ u, f u) ^ 2 + M ^ 4 * ∫ u, f u ^ 2) := by rw [e]; ring
      _ ≤ _ := by gcongr; linarith
  · refine J_le_of_forall fun M₁ M₂ M₃ h₁ h₂ h₃ =>
      (hL T hT2 f hf M hMT.le M₁ M₂ M₃ h₁ h₂ h₃).trans (ENNReal.ofReal_le_ofReal ?_)
    calc A' * M ^ 6 * (∫ u, f u) ^ 2 = A' * (M ^ 6 * (∫ u, f u) ^ 2) := by ring
      _ ≤ max A' 0 * (M ^ 6 * (∫ u, f u) ^ 2) := mul_le_mul_of_nonneg_right (le_max_left _ _) hY
      _ ≤ (2 * A + max A' 0) * T ^ δ * (M ^ 6 * (∫ u, f u) ^ 2 + M ^ 4 * ∫ u, f u ^ 2) := by
        have h1 : max A' 0 ≤ (2 * A + max A' 0) * T ^ δ := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right h1 hY]

/-- Proposition 9.1, as published. -/
theorem J_le_of_fourier_decay_dev (K C : ℝ) (hK : 0 < K) (hC : 1 ≤ C) (c : ℕ → ℝ → ℝ) :
    ∀ δ : ℝ, 0 < δ → ∃ c' : ℝ, ∀ T : ℝ, 0 < T → ∀ M : ℝ, 0 < M → ∀ f : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) f → (∀ u, 0 ≤ f u) → Function.support f ⊆ Set.Icc (1 / C) C →
      (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
        ‖FourierTransform.fourier (fun u => (f u : ℂ)) ξ‖ ≤
          c j ε * T ^ ε * (T / |ξ|) ^ j * ⨆ u, f u) →
      J M K f ≤ ENNReal.ofReal (c' * T ^ δ * (M ^ 6 * (∫ u, f u) ^ 2 + M ^ 4 * ∫ u, f u ^ 2)) := by
  intro δ hδ
  obtain ⟨B, Ts, hB, hTs, hmain⟩ := main K C hK hC (fun j ε => max (c j ε) 0) δ hδ
  set s : ℝ := 2 * |c 0 1| + 2 * |c 2 1| + 1 with hs
  have hs1 : 1 ≤ s := by have := abs_nonneg (c 0 1); have := abs_nonneg (c 2 1); linarith
  have hs0 : 0 < s := by linarith
  have hsT : 1 ≤ (Ts * s) ^ δ := Real.one_le_rpow (by nlinarith) hδ.le
  refine ⟨B * (Ts * s) ^ δ, ?_⟩
  intro T hT M hM f hsm hnn hsupp hdec
  have hf : Adm C c T f := ⟨hsm, hnn, hsupp, hdec⟩
  have F1 : 0 ≤ ∫ u, f u := integral_nonneg hnn
  have F2 : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hV : 0 ≤ M ^ 6 * (∫ u, f u) ^ 2 + M ^ 4 * ∫ u, f u ^ 2 := by positivity
  have hTd : 0 ≤ T ^ δ := Real.rpow_nonneg hT.le _
  rcases lt_or_ge (T * s) 1 with hsm' | hbig
  · -- tiny `T`: `f = 0`
    have hT1 : T ≤ 1 := by nlinarith
    have h0 := eq_zero_of_small C c T hT f hf hsm' hT1
    refine J_le_of_forall fun M₁ M₂ M₃ _ _ _ => ?_
    have : ∀ u, gsum K M₁ M₂ M₃ f u = 0 := fun u => by simp [gsum, h0]
    simp [this]
  rcases lt_or_ge T Ts with hlt | hge
  · have hf' := hf.mono hT hlt.le
    refine (hmain Ts le_rfl f hf' M hM).trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_right _ hV
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hB
    calc Ts ^ δ ≤ (Ts * (T * s)) ^ δ := by
          apply Real.rpow_le_rpow (by linarith) _ hδ.le
          nlinarith
      _ = (Ts * s) ^ δ * T ^ δ := by
          rw [show Ts * (T * s) = (Ts * s) * T by ring, Real.mul_rpow (by nlinarith) hT.le]
  · have hf' := hf.mono hT le_rfl
    refine (hmain T hge f hf' M hM).trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_right _ hV
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hB
    nlinarith

end GuthMaynard.Affine.PartA



theorem solution : type_of% @GuthMaynard.Affine.PartA.J_le_of_fourier_decay_dev := @GuthMaynard.Affine.PartA.J_le_of_fourier_decay_dev
