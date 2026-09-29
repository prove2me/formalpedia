-- Prove2me | solution 1 for LanglandsTunnell.exists_gt_and_hermiteSum_GammaR_mul_mellin_ne_zero_of_shift_ratio_real_of_parity
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/9433e4eb-9e31-5451-ad94-7d851289a870

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_gt_and_hermiteSum_GammaR_mul_mellin_ne_zero_of_shift_ratio_real_of_parity

set_option autoImplicit false

open Filter Topology

namespace K6Dominance

theorem eventually_sum_mul_ne_zero {ι α : Type*} (S : Finset ι) (d : ι → ℂ) (G : ι → α → ℂ) (l : Filter α)
    (T₀ : ι) (hG₀ : ∀ᶠ x in l, G T₀ x ≠ 0) (κ : ι → ℂ)
    (hlim : ∀ T ∈ S, Tendsto (fun x => G T x / G T₀ x) l (𝓝 (κ T)))
    (hL : ∑ T ∈ S, d T * κ T ≠ 0) :
    ∀ᶠ x in l, ∑ T ∈ S, d T * G T x ≠ 0 := by
  have hsum : Tendsto (fun x => ∑ T ∈ S, d T * (G T x / G T₀ x)) l (𝓝 (∑ T ∈ S, d T * κ T)) :=
    tendsto_finset_sum _ fun T hT => (hlim T hT).const_mul (d T)
  have hne : ∀ᶠ x in l, ∑ T ∈ S, d T * (G T x / G T₀ x) ≠ 0 := hsum.eventually_ne hL
  filter_upwards [hne, hG₀] with x h1 h2
  have : ∑ T ∈ S, d T * G T x = G T₀ x * ∑ T ∈ S, d T * (G T x / G T₀ x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    field_simp
  rw [this]
  exact mul_ne_zero h2 h1

theorem sum_ne_zero_of_nonneg_re {ι : Type*} (S : Finset ι) (v : ι → ℂ) (T₀ : ι) (hT₀ : T₀ ∈ S)
    (hre : ∀ T ∈ S, 0 ≤ (v T).re) (him : ∀ T ∈ S, (v T).im = 0) (h0 : 0 < (v T₀).re) :
    ∑ T ∈ S, v T ≠ 0 := by
  intro h
  have hr : (∑ T ∈ S, v T).re = ∑ T ∈ S, (v T).re := by simp [Complex.re_sum]
  have : 0 < ∑ T ∈ S, (v T).re :=
    lt_of_lt_of_le h0 (Finset.single_le_sum (fun T hT => hre T hT) hT₀)
  rw [← hr, h] at this
  simp at this

end K6Dominance

open Complex Filter Topology

theorem solution
    (m : ℕ) (a : ℚ) (ha : a ≠ 0) (u₃ : ℂ) (a₃ c : ZMod 2) (e : ℤ)
    (hne : (((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (m + 1))).filter
          (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧
            ((T.2.1 : ZMod 2) = a₃ + c + (m : ZMod 2)) ∧ ((T.2.2 : ZMod 2) = (e : ZMod 2) + c))).Nonempty)
    (H : ℕ → ℝ → ℂ)
    (hA : ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x : ℝ, R ≤ x →
      mellin (H j) (x : ℂ) ≠ 0 ∧
      ‖mellin (H j) ((x : ℂ) + 2) - (x : ℂ) / (2 * (Real.pi : ℂ) * (a : ℂ) ^ 2) * mellin (H j) (x : ℂ)‖ ≤ ε * x * ‖mellin (H j) (x : ℂ)‖)
    (hC : ∀ (j : ℕ), ∃ C R : ℝ, ∀ x : ℝ, R ≤ x →
      ‖mellin (H (j + 2)) (x : ℂ)‖ ≤ C * ‖mellin (H j) (x : ℂ)‖) :
    ∀ σ₀ : ℝ, ∃ s : ℝ, σ₀ < s ∧
      ∑ T ∈ ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (m + 1))).filter
              (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧
            ((T.2.1 : ZMod 2) = a₃ + c + (m : ZMod 2)) ∧ ((T.2.2 : ZMod 2) = (e : ZMod 2) + c)),
            ((-1 : ℂ) ^ T.1.1 * (m.factorial : ℂ) * (a : ℂ) ^ T.2.2 /
                ((T.1.1.factorial : ℂ) * (T.1.2.factorial : ℂ) * (T.2.1.factorial : ℂ) * (T.2.2.factorial : ℂ) *
                  (4 * (Real.pi : ℂ)) ^ T.1.1)) *
              Complex.Gammaℝ ((s : ℂ) + u₃ + (T.1.2 : ℂ)) * mellin (H T.2.1) ((s : ℂ) + (T.2.2 : ℂ) - 1) ≠ 0 := by
  intro σ₀
  classical
  set Adm := (((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (m + 1))).filter
              (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧
            ((T.2.1 : ZMod 2) = a₃ + c + (m : ZMod 2)) ∧ ((T.2.2 : ZMod 2) = (e : ZMod 2) + c))) with hAdm

  obtain ⟨T₁, hT₁⟩ := hne
  obtain ⟨hT₁s, hT₁j, hT₁l⟩ := (Finset.mem_filter.1 hT₁).2
  set j₀ : ℕ := T₁.2.1 % 2 with hj₀
  have hj₀2 : j₀ < 2 := Nat.mod_lt _ (by norm_num)
  have hj₀le : j₀ ≤ T₁.2.1 := Nat.mod_le _ _
  set K : ℕ := m - j₀ - T₁.2.2 with hK
  have hKdef : K + j₀ + T₁.2.2 = m := by omega
  set iS : ℕ := K % 2 with hiS
  have hiS2 : iS < 2 := Nat.mod_lt _ (by norm_num)
  set lS : ℕ := T₁.2.2 + 2 * (K / 2) with hlS
  have hil : iS + j₀ + lS = m := by omega
  have hj₀par : ((j₀ : ℕ) : ZMod 2) = a₃ + c + (m : ZMod 2) := by
    simp only [hj₀]; rw [ZMod.natCast_mod]; exact hT₁j
  have hlSpar : ((lS : ℕ) : ZMod 2) = (e : ZMod 2) + c := by
    have h2z : (2 : ZMod 2) = 0 := by decide
    simp only [hlS, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, h2z, zero_mul, add_zero]
    exact hT₁l
  set TS : (ℕ × ℕ) × (ℕ × ℕ) := ((0, iS), (j₀, lS)) with hTS
  have hTS_mem : TS ∈ Adm := by
    rw [hAdm, Finset.mem_filter]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [hTS, Finset.mem_product, Finset.mem_range]; omega
    · simp only [hTS]; omega
    · simpa only [hTS] using hj₀par
    · simpa only [hTS] using hlSpar

  set d : (ℕ × ℕ) × (ℕ × ℕ) → ℂ := fun T => ((-1 : ℂ) ^ T.1.1 * (m.factorial : ℂ) * (a : ℂ) ^ T.2.2 /
                ((T.1.1.factorial : ℂ) * (T.1.2.factorial : ℂ) * (T.2.1.factorial : ℂ) * (T.2.2.factorial : ℂ) *
                  (4 * (Real.pi : ℂ)) ^ T.1.1)) with hd
  set G : (ℕ × ℕ) × (ℕ × ℕ) → ℝ → ℂ := fun T s =>
    Complex.Gammaℝ ((s : ℂ) + u₃ + (T.1.2 : ℂ)) * mellin (H T.2.1) ((s : ℂ) + (T.2.2 : ℂ) - 1) with hG

  set κ : (ℕ × ℕ) × (ℕ × ℕ) → ℂ := fun T => if T.1.1 = 0 ∧ T.2.1 = j₀ then ((a : ℂ) ^ 2) ^ ((T.1.2 - iS) / 2) else 0 with hκ

  have hpos : (0 : ℝ) < 2 * Real.pi * (a : ℝ) ^ 2 := by positivity
  set A : ℂ := 2 * (Real.pi : ℂ) * (a : ℂ) ^ 2 with hAdef
  have hA0 : A ≠ 0 := by
    simp only [hAdef]; exact mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) (pow_ne_zero _ (by exact_mod_cast ha))

  have hNZ : ∀ (j : ℕ), ∀ᶠ x : ℝ in atTop, mellin (H j) (x : ℂ) ≠ 0 := by
    intro j
    obtain ⟨R, hR⟩ := hA j 1 one_pos
    filter_upwards [eventually_ge_atTop R] with x hx using (hR x hx).1

  have hAn : 0 < ‖A‖ := norm_pos_iff.2 hA0
  have hρ : ∀ (j : ℕ),
      Tendsto (fun x : ℝ => mellin (H j) ((x : ℂ) + 2) / (((x : ℂ) / A) * mellin (H j) (x : ℂ))) atTop (𝓝 1) := by
    intro j
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨R, hR⟩ := hA j (δ / (2 * ‖A‖)) (by positivity)
    refine ⟨max R 1, fun x hx => ?_⟩
    have hxR : R ≤ x := le_trans (le_max_left _ _) hx
    have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
    have hx0 : (0 : ℝ) < x := by linarith
    obtain ⟨hne0, hbd⟩ := hR x hxR
    have hden : ((x : ℂ) / A) * mellin (H j) (x : ℂ) ≠ 0 :=
      mul_ne_zero (div_ne_zero (by exact_mod_cast hx0.ne') hA0) hne0
    have hnx : ‖(x : ℂ)‖ = x := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    have hM : 0 < ‖mellin (H j) (x : ℂ)‖ := norm_pos_iff.2 hne0
    rw [dist_eq_norm, div_sub_one hden, norm_div, norm_mul, norm_div, hnx, div_lt_iff₀ (by positivity)]
    have hbd' : ‖mellin (H j) ((x : ℂ) + 2) - (x : ℂ) / A * mellin (H j) (x : ℂ)‖ ≤ δ / (2 * ‖A‖) * x * ‖mellin (H j) (x : ℂ)‖ := by
      simpa only [hAdef] using hbd
    have hP : 0 < x / ‖A‖ * ‖mellin (H j) (x : ℂ)‖ := by positivity
    have heq : δ / (2 * ‖A‖) * x * ‖mellin (H j) (x : ℂ)‖ = (1 / 2) * (δ * (x / ‖A‖ * ‖mellin (H j) (x : ℂ)‖)) := by
      field_simp
    rw [heq] at hbd'
    nlinarith

  have hΓ2 : ∀ z : ℂ, z ≠ 0 → Complex.Gammaℝ (z + 2) = z / (2 * (Real.pi : ℂ)) * Complex.Gammaℝ z := by
    intro z hz; rw [Complex.Gammaℝ_add_two hz]; ring

  set bS : ZMod 2 := (e : ZMod 2) + (lS : ZMod 2) with hbS
  have hshift : ∀ (f : ℝ → ℂ) (c : ℝ) (L : ℂ), Tendsto f atTop (𝓝 L) → Tendsto (fun s : ℝ => f (s + c)) atTop (𝓝 L) :=
    fun f c L h => h.comp (tendsto_atTop_add_const_right _ c tendsto_id)
  have hshiftE : ∀ (P : ℝ → Prop) (c : ℝ), (∀ᶠ x : ℝ in atTop, P x) → ∀ᶠ s : ℝ in atTop, P (s + c) :=
    fun P c h => (tendsto_atTop_add_const_right _ c tendsto_id).eventually h

  set Mf : ℕ → ℕ → ℕ → ℝ → ℂ := fun p r q s =>
    mellin (H (j₀ + 2 * q)) (((s + ((lS : ℝ) - 1 - 2 * p - 2 * r - 2 * q)) : ℝ) : ℂ) with hMf
  set Γf : ℕ → ℝ → ℂ := fun p s => Complex.Gammaℝ ((s : ℂ) + u₃ + (iS : ℂ) + 2 * (p : ℂ)) with hΓf
  set Rf : ℕ → ℕ → ℕ → ℝ → ℂ := fun p r j s => (Γf p s * Mf p r j s) / (Γf 0 s * Mf 0 0 0 s) with hRf
  set κf : ℕ → ℕ → ℕ → ℂ := fun p r j => if r = 0 ∧ j = 0 then ((a : ℂ) ^ 2) ^ p else 0 with hκf

  have hMf_ne : ∀ p r j : ℕ, ∀ᶠ s : ℝ in atTop, Mf p r j s ≠ 0 := by
    intro p r j
    simp only [hMf]
    exact hshiftE (fun x => mellin (H (j₀ + 2 * j)) (x : ℂ) ≠ 0) _ (hNZ _)
  have hΓf_ne : ∀ p : ℕ, ∀ᶠ s : ℝ in atTop, Γf p s ≠ 0 ∧ (s : ℂ) + u₃ + (iS : ℂ) + 2 * (p : ℂ) ≠ 0 := by
    intro p
    filter_upwards [eventually_gt_atTop (-u₃.re)] with s hs
    have hre : 0 < ((s : ℂ) + u₃ + (iS : ℂ) + 2 * (p : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero]
      have : (0 : ℝ) ≤ iS := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ p := Nat.cast_nonneg _
      linarith
    exact ⟨Complex.Gammaℝ_ne_zero_of_re_pos hre, fun h => by rw [h, Complex.zero_re] at hre; exact lt_irrefl _ hre⟩

  have hC0 : Tendsto (Rf 0 0 0) atTop (𝓝 (κf 0 0 0)) := by
    have : κf 0 0 0 = 1 := by simp [hκf]
    rw [this]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hMf_ne 0 0 0, hΓf_ne 0] with s h1 h2
    have h3 : Γf 0 s * Mf 0 0 0 s ≠ 0 := mul_ne_zero h2.1 h1
    simp only [hRf, div_self h3]

  have hcst_j : ∀ p r j : ℕ, ((lS : ℝ) - 1 - 2 * p - 2 * r - 2 * ((j + 1 : ℕ) : ℝ)) = ((lS : ℝ) - 1 - 2 * p - 2 * r - 2 * j) - 2 := by
    intro p r j; push_cast; ring
  have hcst_r : ∀ p r j : ℕ, ((lS : ℝ) - 1 - 2 * p - 2 * ((r + 1 : ℕ) : ℝ) - 2 * j) = ((lS : ℝ) - 1 - 2 * p - 2 * r - 2 * j) - 2 := by
    intro p r j; push_cast; ring
  have hcst_p : ∀ p r j : ℕ, ((lS : ℝ) - 1 - 2 * ((p + 1 : ℕ) : ℝ) - 2 * r - 2 * j) = ((lS : ℝ) - 1 - 2 * p - 2 * r - 2 * j) - 2 := by
    intro p r j; push_cast; ring

  have hAdiv : Tendsto (fun y : ℝ => A / (y : ℂ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have : Tendsto (fun y : ℝ => ‖A‖ * y⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul ‖A‖
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy, div_eq_mul_inv]
  have hdown : ∀ (j : ℕ), Tendsto (fun y : ℝ => mellin (H j) (y : ℂ) / mellin (H j) ((y : ℂ) + 2)) atTop (𝓝 0) := by
    intro j
    have h1 := (hρ j).inv₀ one_ne_zero
    have h2 := hAdiv.mul h1
    rw [inv_one, zero_mul] at h2
    refine h2.congr' ?_
    filter_upwards [hNZ j, eventually_gt_atTop (0 : ℝ), (tendsto_atTop_add_const_right _ (2 : ℝ) tendsto_id).eventually (hNZ j)] with y hM hy hM2
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have hM2' : mellin (H j) ((y : ℂ) + 2) ≠ 0 := by push_cast at hM2; exact hM2
    field_simp
  have hTr : ∀ p r j : ℕ, Tendsto (fun s : ℝ => Mf p (r + 1) j s / Mf p r j s) atTop (𝓝 0) := by
    intro p r j
    have h := hshift _ ((lS : ℝ) - 1 - 2 * p - 2 * r - 2 * j - 2) _ (hdown (j₀ + 2 * j))
    refine h.congr' (Eventually.of_forall fun s => ?_)
    simp only [hMf, hcst_r]
    congr 1 <;> (try (congr 1; push_cast; ring)) <;> (try (push_cast; ring))
  have hTp' : ∀ p r j : ℕ, Tendsto (fun s : ℝ => Mf (p + 1) r j s / Mf p r j s) atTop (𝓝 0) := by
    intro p r j
    have h := hshift _ ((lS : ℝ) - 1 - 2 * p - 2 * r - 2 * j - 2) _ (hdown (j₀ + 2 * j))
    refine h.congr' (Eventually.of_forall fun s => ?_)
    simp only [hMf, hcst_p]
    congr 1 <;> (try (congr 1; push_cast; ring)) <;> (try (push_cast; ring))

  have hTj : ∀ p r q : ℕ, Tendsto (fun s : ℝ => Mf p r (q + 1) s / Mf p r q s) atTop (𝓝 0) := by
    intro p r q
    set cc : ℝ := (lS : ℝ) - 1 - 2 * p - 2 * r - 2 * q with hcc
    obtain ⟨C, R, hCR⟩ := hC (j₀ + 2 * q)
    have hg := hshift _ (cc - 2) _ (hdown (j₀ + 2 * q))
    rw [tendsto_zero_iff_norm_tendsto_zero] at hg
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hg' : Tendsto (fun s : ℝ => |C| * ‖mellin (H (j₀ + 2 * q)) (((s + (cc - 2) : ℝ)) : ℂ) / mellin (H (j₀ + 2 * q)) ((((s + (cc - 2) : ℝ)) : ℂ) + 2)‖) atTop (𝓝 0) := by
      simpa using hg.const_mul |C|
    refine squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) ?_ hg'
    filter_upwards [eventually_ge_atTop (R - (cc - 2))] with s hs
    have hx : R ≤ s + (cc - 2) := by linarith
    have hb := hCR _ hx
    have hj2 : j₀ + 2 * (q + 1) = j₀ + 2 * q + 2 := by ring
    have e1 : Mf p r (q + 1) s = mellin (H (j₀ + 2 * q + 2)) (((s + (cc - 2) : ℝ)) : ℂ) := by
      simp only [hMf, hj2, hcc]; congr 1; push_cast; ring
    have e2 : Mf p r q s = mellin (H (j₀ + 2 * q)) ((((s + (cc - 2) : ℝ)) : ℂ) + 2) := by
      simp only [hMf, hcc]; congr 1; push_cast; ring
    rw [e1, e2, norm_div, norm_div, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hb.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))) (norm_nonneg _)

  have hcdiv : ∀ C : ℂ, Tendsto (fun y : ℝ => C / (y : ℂ)) atTop (𝓝 0) := by
    intro C
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have : Tendsto (fun y : ℝ => ‖C‖ * y⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul ‖C‖
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy, div_eq_mul_inv]
  have hlin : ∀ (α : ℂ) (β : ℝ), Tendsto (fun s : ℝ => ((s : ℂ) + α) / (((s + β : ℝ)) : ℂ)) atTop (𝓝 1) := by
    intro α β
    have h := (hshift _ β _ (hcdiv (α - (β : ℂ)))).add_const 1
    rw [zero_add] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (-β)] with s hs
    have : (((s + β : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : s + β ≠ 0)
    field_simp
    push_cast
    ring

  have hTp : ∀ p r j : ℕ, Tendsto (fun s : ℝ => (Γf (p + 1) s / Γf p s) * (Mf (p + 1) r j s / Mf p r j s)) atTop (𝓝 ((a : ℂ) ^ 2)) := by
    intro p r j
    set c : ℝ := (lS : ℝ) - 1 - 2 * p - 2 * r - 2 * j with hc

    have hmodel : Tendsto (fun s : ℝ => (a : ℂ) ^ 2 * ((((s : ℂ) + (u₃ + (iS : ℂ) + 2 * (p : ℂ))) / (((s + (c - 2) : ℝ)) : ℂ)) *
        (mellin (H (j₀ + 2 * j)) ((((s + (c - 2) : ℝ)) : ℂ) + 2) / (((((s + (c - 2) : ℝ)) : ℂ) / A) * mellin (H (j₀ + 2 * j)) (((s + (c - 2) : ℝ)) : ℂ)))⁻¹)) atTop (𝓝 ((a : ℂ) ^ 2)) := by
      have h1 := hlin (u₃ + (iS : ℂ) + 2 * (p : ℂ)) (c - 2)
      have h2 := (hshift _ (c - 2) _ (hρ (j₀ + 2 * j))).inv₀ one_ne_zero
      have := (h1.mul h2).const_mul ((a : ℂ) ^ 2)
      rw [inv_one, mul_one, mul_one] at this
      exact this
    refine hmodel.congr' ?_
    filter_upwards [hΓf_ne p, hshiftE _ (c - 2) (hNZ (j₀ + 2 * j)), hshiftE _ c (hNZ (j₀ + 2 * j)), eventually_gt_atTop (2 - c)] with s hz hM hM0 hs
    have hy0 : (((s + (c - 2) : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : s + (c - 2) ≠ 0)
    have hM2 : mellin (H (j₀ + 2 * j)) ((((s + (c - 2) : ℝ)) : ℂ) + 2) ≠ 0 := by
      have : ((((s + (c - 2) : ℝ)) : ℂ) + 2) = (((s + c : ℝ)) : ℂ) := by push_cast; ring
      rw [this]; exact hM0
    have hΓ : Γf (p + 1) s = ((s : ℂ) + u₃ + (iS : ℂ) + 2 * (p : ℂ)) / (2 * (Real.pi : ℂ)) * Γf p s := by
      have harg : ((s : ℂ) + u₃ + (iS : ℂ) + 2 * ((p + 1 : ℕ) : ℂ)) = ((s : ℂ) + u₃ + (iS : ℂ) + 2 * (p : ℂ)) + 2 := by push_cast; ring
      simp only [hΓf]
      rw [harg, hΓ2 _ hz.2]
    have hMp1 : Mf (p + 1) r j s = mellin (H (j₀ + 2 * j)) (((s + (c - 2) : ℝ)) : ℂ) := by
      simp only [hMf, hc, hcst_p]; try (congr 1; push_cast; ring)
    have hMp : Mf p r j s = mellin (H (j₀ + 2 * j)) ((((s + (c - 2) : ℝ)) : ℂ) + 2) := by
      simp only [hMf, hc]; try (congr 1; push_cast; ring)
    rw [hΓ, hMp1, hMp]
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    have hΓ0 : Γf p s ≠ 0 := hz.1
    simp only [hAdef]
    field_simp
    ring

  have hD_ne : ∀ᶠ s : ℝ in atTop, Γf 0 s * Mf 0 0 0 s ≠ 0 := by
    filter_upwards [hΓf_ne 0, hMf_ne 0 0 0] with s h1 h2 using mul_ne_zero h1.1 h2
  have hEj : ∀ p r j : ℕ, ∀ᶠ s : ℝ in atTop, Rf p r (j + 1) s = Rf p r j s * (Mf p r (j + 1) s / Mf p r j s) := by
    intro p r j
    filter_upwards [hD_ne, hMf_ne p r j] with s hD hM
    simp only [hRf]
    field_simp
  have hEr : ∀ p r j : ℕ, ∀ᶠ s : ℝ in atTop, Rf p (r + 1) j s = Rf p r j s * (Mf p (r + 1) j s / Mf p r j s) := by
    intro p r j
    filter_upwards [hD_ne, hMf_ne p r j] with s hD hM
    simp only [hRf]
    field_simp
  have hEp : ∀ p r j : ℕ, ∀ᶠ s : ℝ in atTop, Rf (p + 1) r j s = Rf p r j s * ((Γf (p + 1) s / Γf p s) * (Mf (p + 1) r j s / Mf p r j s)) := by
    intro p r j
    filter_upwards [hD_ne, hMf_ne p r j, hΓf_ne p] with s hD hM hΓ
    have hΓ' := hΓ.1
    simp only [hRf]
    field_simp

  have hRj : ∀ j : ℕ, Tendsto (Rf 0 0 j) atTop (𝓝 (κf 0 0 j)) := by
    intro j
    induction j with
    | zero => exact hC0
    | succ j ih =>
      have h := ih.mul (hTj 0 0 j)
      rw [mul_zero] at h
      have hk : κf 0 0 (j + 1) = 0 := by simp [hκf]
      rw [hk]
      exact h.congr' ((hEj 0 0 j).mono fun s hs => hs.symm)
  have hRr : ∀ r j : ℕ, Tendsto (Rf 0 r j) atTop (𝓝 (κf 0 r j)) := by
    intro r
    induction r with
    | zero => exact hRj
    | succ r ih =>
      intro j
      have h := (ih j).mul (hTr 0 r j)
      rw [mul_zero] at h
      have hk : κf 0 (r + 1) j = 0 := by simp [hκf]
      rw [hk]
      exact h.congr' ((hEr 0 r j).mono fun s hs => hs.symm)
  have hRp : ∀ p r j : ℕ, Tendsto (Rf p r j) atTop (𝓝 (κf p r j)) := by
    intro p
    induction p with
    | zero => exact hRr
    | succ p ih =>
      intro r j
      have h := (ih r j).mul (hTp p r j)
      have hk : κf (p + 1) r j = κf p r j * (a : ℂ) ^ 2 := by
        simp only [hκf]; split_ifs <;> ring
      rw [hk]
      exact h.congr' ((hEp p r j).mono fun s hs => hs.symm)
  have hG₀ : ∀ᶠ s : ℝ in atTop, G TS s ≠ 0 := by
    filter_upwards [hD_ne] with s hD
    have : G TS s = Γf 0 s * Mf 0 0 0 s := by
      simp only [hG, hΓf, hMf, hTS]
      congr 1
      · congr 1; push_cast; ring
      · congr 1
        · push_cast; ring
    rw [this]; exact hD
  have hlim : ∀ T ∈ Adm, Tendsto (fun s : ℝ => G T s / G TS s) atTop (𝓝 (κ T)) := by
    intro T hT
    obtain ⟨hsum, hparj, hparl⟩ := (Finset.mem_filter.1 hT).2

    have hjmod : T.2.1 % 2 = j₀ := by
      have h1 : ((T.2.1 : ℕ) : ZMod 2) = ((j₀ : ℕ) : ZMod 2) := by rw [hparj, hj₀par]
      have := (ZMod.natCast_eq_natCast_iff' T.2.1 j₀ 2).1 h1
      rw [this]; exact (Nat.mod_eq_of_lt hj₀2)
    obtain ⟨q, hq⟩ : ∃ q, T.2.1 = j₀ + 2 * q := ⟨T.2.1 / 2, by omega⟩

    have hlmod : T.2.2 % 2 = lS % 2 := by
      have h1 : ((T.2.2 : ℕ) : ZMod 2) = ((lS : ℕ) : ZMod 2) := by rw [hparl, hlSpar]
      exact (ZMod.natCast_eq_natCast_iff' T.2.2 lS 2).1 h1
    have hipar : T.1.2 % 2 = iS := by omega
    obtain ⟨p, hp⟩ : ∃ p, T.1.2 = iS + 2 * p := ⟨(T.1.2 - iS) / 2, by omega⟩
    have hl : T.2.2 + 2 * p + 2 * T.1.1 + 2 * q = lS := by omega
    have h2 : (T.1.2 - iS) / 2 = p := by omega
    have hκT : κ T = κf p T.1.1 q := by
      simp only [hκ, hκf]
      by_cases hc0 : T.1.1 = 0 ∧ T.2.1 = j₀
      · rw [if_pos hc0, if_pos ⟨hc0.1, by omega⟩, h2]
      · rw [if_neg hc0, if_neg (fun h => hc0 ⟨h.1, by omega⟩)]
    rw [hκT]
    refine (hRp p T.1.1 q).congr' (Eventually.of_forall fun s => ?_)
    have hlR : ((T.2.2 : ℕ) : ℝ) = (lS : ℝ) - 2 * p - 2 * (T.1.1 : ℝ) - 2 * (q : ℝ) := by
      have hc := congrArg (Nat.cast : ℕ → ℝ) hl
      push_cast at hc
      linarith
    have hiC : ((T.1.2 : ℕ) : ℂ) = (iS : ℂ) + 2 * (p : ℂ) := by rw [hp]; push_cast; ring
    simp only [hG, hRf, hΓf, hMf, hTS] at *
    congr 1
    · rw [hiC, hq]
      congr 1
      · congr 1; ring
      · congr 1
        push_cast
        rw [show ((T.2.2 : ℕ) : ℂ) = ((((T.2.2 : ℕ) : ℝ)) : ℂ) by norm_cast, hlR]
        push_cast; ring
    · congr 1
      · congr 1; push_cast; ring
      · congr 1
        · push_cast; ring
  have hL : ∑ T ∈ Adm, d T * κ T ≠ 0 := by
    have hterm : ∀ T ∈ Adm, d T * κ T =
        ((m.factorial : ℂ) * (a : ℂ) ^ lS / (j₀.factorial : ℂ)) *
          (if T.1.1 = 0 ∧ T.2.1 = j₀ then (1 / ((T.1.2.factorial : ℂ) * (T.2.2.factorial : ℂ))) else 0) := by
      intro T hT
      obtain ⟨hsum, hparj, hparl⟩ := (Finset.mem_filter.1 hT).2
      simp only [hd, hκ]
      split_ifs with h
      · obtain ⟨hr, hj⟩ := h
        have hlmod : T.2.2 % 2 = lS % 2 := by
          have h1 : ((T.2.2 : ℕ) : ZMod 2) = ((lS : ℕ) : ZMod 2) := by rw [hparl, hlSpar]
          exact (ZMod.natCast_eq_natCast_iff' T.2.2 lS 2).1 h1
        have hipar : T.1.2 % 2 = iS := by omega
        obtain ⟨p, hp⟩ : ∃ p, T.1.2 = iS + 2 * p := ⟨(T.1.2 - iS) / 2, by omega⟩
        have hl : T.2.2 + 2 * p = lS := by omega
        have h2 : (T.1.2 - iS) / 2 = p := by omega
        rw [h2, hr, hj]
        have hl' : lS = T.2.2 + 2 * p := hl.symm
        rw [hl']
        simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul, mul_one, pow_add, pow_mul]
        have ha2 : ((a : ℂ) ^ 2) ^ p ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by exact_mod_cast ha))
        have hj0 : (j₀.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
        first
          | (field_simp; ring)
          | field_simp
      · simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    refine mul_ne_zero (div_ne_zero (mul_ne_zero (by exact_mod_cast (Nat.factorial_ne_zero m)) (pow_ne_zero _ (by exact_mod_cast ha))) (by exact_mod_cast Nat.factorial_ne_zero _)) ?_
    apply K6Dominance.sum_ne_zero_of_nonneg_re Adm _ TS hTS_mem
    · intro T _; split_ifs <;> simp <;> positivity
    · intro T _; split_ifs <;> simp
    · simp [hTS]; positivity
  have hev := K6Dominance.eventually_sum_mul_ne_zero Adm d G atTop TS hG₀ κ hlim hL
  obtain ⟨s, hsσ, hs⟩ := ((eventually_gt_atTop σ₀).and hev).exists
  refine ⟨s, hsσ, ?_⟩
  convert hs using 2 with T
  simp only [hd, hG]
  ring

end S_LanglandsTunnell_exists_gt_and_hermiteSum_GammaR_mul_mellin_ne_zero_of_shift_ratio_real_of_parity
end P2MW
export P2MW.S_LanglandsTunnell_exists_gt_and_hermiteSum_GammaR_mul_mellin_ne_zero_of_shift_ratio_real_of_parity (solution)
