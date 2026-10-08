-- Prove2me | solution 1 for OAI.TwoPointCorrelations.halasz_log_dirichlet_block
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:10:00.422635+00:00
-- url     : https://prove2.me/submissions/c7b28353-12eb-410f-b11e-e1dd530c6a6a

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_large_log_polynomial_saving
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_phase_from_polynomial
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_single_log_polynomial_saving

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCubicLaplace
namespace OAI

/-! The cubic Laplace estimate used to pass from the logarithmic
exponential-sum bound to the Vinogradov--Korobov zeta bound (Ford,
Proc. LMS 85 (2002), Section 7). Absolute constants are deliberately
weakened; only the exponents 3/2 and 2/3 matter for the application. -/
namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Set

lemma halasz_cubic_balance {δ x L : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) (hL : 0 < L) :
    δ*x-x^3/(1000*L^2) ≤
      1000*δ^(3/2:ℝ)*L-x^3/(2000*L^2) := by
  have hr : δ^(3/2:ℝ) = δ*Real.sqrt δ := by
    by_cases hz : δ=0
    · simp [hz]
    have hδ0 : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hz)
    rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hδ0,Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hd : Real.sqrt δ^2 = δ := Real.sq_sqrt hδ
  have hl2 : 0 < L^2 := sq_pos_of_pos hL
  have hx3 : 0 ≤ x^3 := pow_nonneg hx _
  have he : x^3/(1000*L^2) = 2*(x^3/(2000*L^2)) := by
    field_simp
    ring
  rw [he,hr]
  by_cases hsmall : x ≤ 1000*Real.sqrt δ*L
  · have hh := mul_le_mul_of_nonneg_left hsmall hδ
    have hn : 0 ≤ x^3/(2000*L^2) := by positivity
    nlinarith only [hh,hn]
  · have hbig : 1000*Real.sqrt δ*L ≤ x := (lt_of_not_ge hsmall).le
    have hs := mul_self_le_mul_self (by positivity : 0 ≤ 1000*Real.sqrt δ*L) hbig
    have hs' : 2000*δ*L^2 ≤ x^2 := by
      have hn : 0 ≤ δ*L^2 := by positivity
      nlinarith only [hs,hd,hn]
    have hc : δ*x ≤ x^3/(2000*L^2) := by
      apply (le_div_iff₀ (by positivity : 0 < 2000*L^2)).mpr
      have hh := mul_le_mul_of_nonneg_right hs' hx
      nlinarith only [hh]
    have hn : 0 ≤ 1000*(δ*Real.sqrt δ)*L := by positivity
    linarith only [hc,hn]




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCubicMaximum
namespace OAI

/-! Cubic logarithmic cancellation absorbs a strip displacement. -/
namespace TwoPointCorrelations

lemma halasz_cubic_maximum {δ y L : ℝ} (hδ : 0≤δ) (hy : 0≤ y) (hL : 0< L) :
    δ*y-y^3/((10^15:ℝ)*L^2)≤(10^9:ℝ)*δ^(3/2:ℝ)*L := by
  have hh := halasz_cubic_balance hδ hy (show 0<(10^6:ℝ)*L by positivity)
  have he : (1000:ℝ)*((10^6:ℝ)*L)^2=(10^15:ℝ)*L^2 := by ring
  rw [he] at hh
  have hn : 0≤ y^3/(2000*((10^6:ℝ)*L)^2) := by positivity
  nlinarith

lemma halasz_log_cubic_identity {N L lam : ℝ} (hL : 0< L)
    (hy : 0< Real.log N) (hLlam : L=lam*Real.log N) :
    (-1/((10^15:ℝ)*lam^2))*Real.log N =
      -(Real.log N)^3/((10^15:ℝ)*L^2) := by
  have hlam : 0< lam := by nlinarith
  rw [hLlam]
  field_simp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovDiagonal
namespace OAI

/-! The diagonal algebra for the complete Vinogradov system: its first
s power sums determine all elementary symmetric functions of s entries.
This is the finite algebraic starting point for the mean-value argument
underlying Ford's logarithmic exponential-sum estimate. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MvPolynomial




@[simp] lemma mem_halaszVinogradovFiber {s N k : ℕ} {x y : Fin s → Fin N} :
    y ∈ halaszVinogradovFiber x k ↔ ∀ j ∈ Icc 1 k,
      (∑ i, ((x i).val+1)^j) = ∑ i, ((y i).val+1)^j := by
  classical
  simp [halaszVinogradovFiber]







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDegreeSaving
namespace OAI

/-! Numerical margins for the degree and shift-length choices in the
logarithmic exponential-sum application. -/
namespace TwoPointCorrelations

lemma halasz_low_height_degree_margin {lam : ℝ}
    (hlo : 49/100≤ lam) (hhi : lam≤9/10) :
    (1:ℝ)/16+(6:ℝ)^2/1024≤ min (1/3:ℝ) (min (1-lam) (lam-1/3)) := by
  apply le_min
  · norm_num
  · apply le_min <;> linarith

lemma halasz_medium_degree_margin {lam : ℝ} (hlo : 9/10≤ lam) (hhi : lam≤48) :
    (1:ℝ)/32≤ lam/2-1/3-(3*lam+6)^2/1024 := by
  have hprod : 0≤(lam-9/10)*(48-lam) := mul_nonneg (by linarith) (by linarith)
  nlinarith





lemma halasz_small_taylor_exponent {lam k : ℝ} (hk : 3*lam+3≤ k) :
    lam-(k+1)/3≤-(4/3:ℝ) := by linarith

lemma halasz_large_taylor_exponent {lam m : ℝ} (hlam : lam≤6*m) :
    lam-(12*m+1)/2≤-(1/2:ℝ) := by linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCircleWindow
namespace OAI

/-! A compact circle window with a lower bound for its small Fourier
coefficients. This supplies the localizer for the double moment estimate. -/
namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Metric _root_.Set
open scoped _root_.ComplexConjugate

local instance : Fact (0<(1:ℝ)) := ⟨by norm_num⟩






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszWeightedPrefix
namespace OAI

/-! A decreasing positive weight preserves the bound for all prefixes.
This is the finite Abel step for the Dirichlet polynomial. -/
namespace TwoPointCorrelations

open _root_.Finset

lemma halasz_telescoping_weights (w : ℕ → ℝ) (H : ℕ) :
    (∑ n∈range H,(w n-w (n+1)))=w 0-w H := by
  induction H with
  | zero => simp
  | succ H ih => rw [sum_range_succ,ih]; ring

theorem halasz_weighted_prefix (f : ℕ → ℂ) (w : ℕ → ℝ) (H : ℕ) (B : ℝ)
    (hw : ∀ n≤ H,0≤ w n) (hdec : ∀ n< H,w (n+1)≤ w n)
    (hB : ∀ n≤ H,‖∑ i∈range n,f i‖≤ B) :
    ‖∑ n∈range H,(w n:ℂ)*f n‖≤ w 0*B := by
  have hB0 : 0≤ B := by simpa only [sum_range_zero,norm_zero] using hB 0 (Nat.zero_le H)
  by_cases hH : H=0
  · subst H
    simpa only [sum_range_zero,norm_zero] using mul_nonneg (hw 0 le_rfl) hB0
  have hlast : H-1≤ H := Nat.sub_le H 1
  have heq := sum_range_by_parts w f H
  simp only [Complex.real_smul,Complex.ofReal_sub] at heq
  rw [heq]
  calc
    _ ≤ ‖(w (H-1):ℂ)*(∑ n∈range H,f n)‖+
        ‖∑ n∈range (H-1),((w (n+1):ℂ)-(w n:ℂ))*(∑ i∈range (n+1),f i)‖ := norm_sub_le _ _
    _ ≤ w (H-1)*B+∑ n∈range (H-1),(w n-w (n+1))*B := by
      apply add_le_add
      · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw _ hlast)]
        exact mul_le_mul_of_nonneg_left (hB H le_rfl) (hw _ hlast)
      · apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro n hn
        have hnH : n< H := by have := mem_range.mp hn; omega
        have hdiff : 0≤ w n-w (n+1) := sub_nonneg.mpr (hdec n hnH)
        rw [← Complex.ofReal_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonpos (sub_nonpos.mpr (hdec n hnH)),neg_sub]
        exact mul_le_mul_of_nonneg_left (hB (n+1) (by omega)) hdiff
    _ = w 0*B := by rw [← sum_mul,halasz_telescoping_weights]; ring

lemma halasz_cpow_real_phase {x : ℝ} (hx : 0< x) (s : ℂ) :
    (x:ℂ)^(-s)=(x^(-s.re):ℝ)*
      Complex.exp (Complex.I*((-s.im*Real.log x:ℝ):ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Real.rpow_def_of_pos hx,Complex.ofReal_exp,← Complex.exp_add,
    ← Complex.ofReal_log hx.le]
  congr 1
  apply Complex.ext <;> simp [mul_comm]

theorem halasz_weighted_log_prefix {x : ℝ} (hx : 0< x) (s : ℂ) (hσ : 0≤ s.re)
    (H : ℕ) (B : ℝ)
    (hB : ∀ n≤ H,‖∑ i∈range n,Complex.exp
      (Complex.I*((-s.im*Real.log (x+i):ℝ):ℂ))‖≤ B) :
    ‖∑ n∈range H,((x+n:ℝ):ℂ)^(-s)‖≤ x^(-s.re)*B := by
  have heq : (∑ n∈range H,((x+n:ℝ):ℂ)^(-s))=
      ∑ n∈range H,((x+n)^(-s.re):ℝ)*Complex.exp
        (Complex.I*((-s.im*Real.log (x+n):ℝ):ℂ)) := by
    apply sum_congr rfl
    intro n _
    exact halasz_cpow_real_phase (by positivity) s
  rw [heq]
  have h := halasz_weighted_prefix
    (fun n => Complex.exp (Complex.I*((-s.im*Real.log (x+n):ℝ):ℂ)))
    (fun n => (x+n)^(-s.re)) H B
    (fun n _ => Real.rpow_nonneg (by positivity) _)
    (fun n _ => Real.rpow_le_rpow_of_nonpos (by positivity)
      (by push_cast; linarith) (neg_nonpos.mpr hσ)) hB
  simpa only [Nat.cast_zero,add_zero] using h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszSelectedDoubleMoment
namespace OAI

/-! The sole selected moment needed for logarithmic exponential sums. -/
namespace TwoPointCorrelations

open _root_.Finset


lemma halasz_selected_moment_pos {k : ℕ} (hk : 2≤ k) : 1≤ halaszSelectedMoment k := by
  unfold halaszSelectedMoment
  nlinarith


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszBoundedDegrees
namespace OAI

/-! Fixed and rounded Taylor degrees cover the bounded height/length ratios. -/
namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma halasz_medium_degree_saving {lam k d : ℝ}
    (hlo : 9/10≤ lam) (hhi : lam≤48) (hk0 : 0≤ k) (hk : k≤3*lam+6)
    (hdlo : 3*lam/2≤ d) (hdhi : d≤3*lam/2+1) :
    (1:ℝ)/32+k^2/1024≤ min (d/3) (min (d-lam) (lam-d/3)) := by
  have hm := halasz_medium_degree_margin hlo hhi
  have hk2 : k^2≤(3*lam+6)^2 := by nlinarith
  apply le_min
  · nlinarith
  · apply le_min <;> nlinarith


lemma halasz_medium_degree_bounds {lam : ℝ} (hlo : 9/10≤ lam) :
    2≤ halaszMediumDegree lam ∧ 1≤ halaszMediumActive lam ∧
    halaszMediumActive lam≤ halaszMediumDegree lam ∧
    3*lam+3≤(halaszMediumDegree lam:ℝ) ∧
    (halaszMediumDegree lam:ℝ)≤3*lam+6 ∧
    3*lam/2≤(halaszMediumActive lam:ℝ) ∧
    (halaszMediumActive lam:ℝ)≤3*lam/2+1 := by
  have hc := Nat.le_ceil lam
  have hc' := Nat.ceil_lt_add_one (by linarith : 0≤ lam)
  have hd := Nat.le_ceil (3*lam/2)
  have hd' := Nat.ceil_lt_add_one (by linarith : 0≤3*lam/2)
  have hklo : 3*lam+3≤(halaszMediumDegree lam:ℝ) := by
    dsimp only [halaszMediumDegree]
    push_cast
    linarith
  have hkhi : (halaszMediumDegree lam:ℝ)≤3*lam+6 := by
    dsimp only [halaszMediumDegree]
    push_cast
    linarith
  have hdlo : 3*lam/2≤(halaszMediumActive lam:ℝ) := hd
  have hdhi : (halaszMediumActive lam:ℝ)≤3*lam/2+1 := hd'.le
  refine ⟨?_,?_,?_,hklo,hkhi,hdlo,hdhi⟩
  · unfold halaszMediumDegree
    omega
  · exact_mod_cast (show (1:ℝ)≤ halaszMediumActive lam by linarith)
  · exact_mod_cast (show (halaszMediumActive lam:ℝ)≤ halaszMediumDegree lam by linarith)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDegreeSelection
namespace OAI

/-! Quantitative degree choices as a function of log|t|/log N. -/
namespace TwoPointCorrelations

lemma halasz_large_degree_selection {lam : ℝ} (hlam : 48≤ lam) :
    8≤⌈lam/6⌉₊ ∧ 6*(⌈lam/6⌉₊:ℝ)-6≤ lam ∧ lam≤6*(⌈lam/6⌉₊:ℝ) ∧
      (12*⌈lam/6⌉₊:ℝ)≤2*lam+12 := by
  have hlo := Nat.le_ceil (lam/6)
  have hhi := Nat.ceil_lt_add_one (by linarith : 0≤ lam/6)
  refine ⟨?_,by linarith,by linarith,?_⟩
  · exact_mod_cast (show (8:ℝ)≤⌈lam/6⌉₊ by linarith)
  · linarith


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszBoundedSaving
namespace OAI

/-! A single absolute saving exponent covers the bounded-degree cases. -/
namespace TwoPointCorrelations

lemma halasz_bounded_root_saving {k : ℕ} (hk : 2≤ k) (hkhi : k≤150)
    {lam : ℝ} (hlam : 49/100≤ lam) :
    1/((10^15:ℝ)*lam^2) ≤
      (1/32:ℝ)/((2*halaszSelectedMoment k*halaszSelectedMoment k:ℕ):ℝ) := by
  have hk0 : 0≤(k:ℝ) := Nat.cast_nonneg _
  have hkR : (k:ℝ)≤150 := by exact_mod_cast hkhi
  have hk2 : (k:ℝ)^2≤150^2 := pow_le_pow_left₀ hk0 hkR 2
  have hr : (halaszSelectedMoment k:ℝ)≤225150 := by
    simp only [halaszSelectedMoment,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    nlinarith
  have hr0 : 0<(halaszSelectedMoment k:ℝ) := by
    exact_mod_cast (show 0< halaszSelectedMoment k from
      lt_of_lt_of_le Nat.zero_lt_one (halasz_selected_moment_pos hk))
  have hr2 := pow_le_pow_left₀ hr0.le hr 2
  have hp : 0<((2*halaszSelectedMoment k*halaszSelectedMoment k:ℕ):ℝ) := by
    push_cast
    positivity
  have hlam0 : 0< lam := by linarith
  have hlam2 : (49/100:ℝ)^2≤ lam^2 := pow_le_pow_left₀ (by norm_num) hlam 2
  apply (div_le_div_iff₀ (by positivity : (0:ℝ)<10^15*lam^2) hp).mpr
  push_cast
  nlinarith

lemma halasz_low_degree_saving {lam : ℝ} (hlo : 49/100≤ lam) (hhi : lam≤9/10) :
    (1:ℝ)/32+(6:ℝ)^2/1024≤ min (1/3:ℝ) (min (1-lam) (lam-1/3)) := by
  have hh := halasz_low_height_degree_margin hlo hhi
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszBoundedLogPolynomial
namespace OAI

/-! Uniform bounded-degree polynomial estimate and Taylor margin. -/
namespace TwoPointCorrelations

open _root_.Finset

theorem halasz_bounded_log_polynomial : ∃ R₀ : ℕ, ∀ lam : ℝ,
    49/100≤ lam → lam≤48 → ∃ k : ℕ, 2≤ k ∧ k≤150 ∧
      lam-((k:ℝ)+1)/3≤-(1/2:ℝ) ∧
      ∀ M : ℕ, 1≤ M → ∀ t z N : ℝ, (M:ℝ)≤ N → N≤ z → z≤2*N →
      |t|=N^lam → N^(1/3:ℝ)≤2*(M:ℝ) →
      ‖∑ b : Fin M,halaszVinogradovPolynomial k M
        (halaszScaledFrequency (halaszLogCoefficient t z)
          (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖/(M:ℝ)^2 ≤
        (R₀+182:ℝ)^6*N^(-1/((10^15:ℝ)*lam^2)) := by
  obtain ⟨R₀,hR⟩ := halasz_single_log_polynomial_saving
  refine ⟨R₀,?_⟩
  intro lam hlo hhi
  have hfinish (k d : ℕ) (hk : 2≤ k) (hkhi : k≤150) (hd : 1≤ d) (hdk : d≤ k)
      (hdeg : (1:ℝ)/32+(k:ℝ)^2/1024≤
        min ((d:ℝ)/3) (min ((d:ℝ)-lam) (lam-(d:ℝ)/3))) :
      ∀ M : ℕ,1≤ M → ∀ t z N : ℝ,(M:ℝ)≤ N → N≤ z → z≤2*N →
      |t|=N^lam → N^(1/3:ℝ)≤2*(M:ℝ) →
      ‖∑ b : Fin M,halaszVinogradovPolynomial k M
        (halaszScaledFrequency (halaszLogCoefficient t z)
          (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖/(M:ℝ)^2 ≤
        (R₀+182:ℝ)^6*N^(-1/((10^15:ℝ)*lam^2)) := by
    intro M hM t z N hMN hz hzhi ht hscale
    have hp := hR k hk M hM d hd hdk t z N lam (1/32) hMN hz hzhi ht hscale hdeg
    have hN : 1≤ N := (show (1:ℝ)≤ M by exact_mod_cast hM).trans hMN
    have he := neg_le_neg (halasz_bounded_root_saving hk hkhi hlo)
    have he' : -(1/32:ℝ)/((2*halaszSelectedMoment k*halaszSelectedMoment k:ℕ):ℝ)≤
        -1/((10^15:ℝ)*lam^2) := by simpa only [neg_div] using he
    apply hp.trans
    apply mul_le_mul
    · apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast (show R₀+k+32≤ R₀+182 by omega)
    · exact Real.rpow_le_rpow_of_exponent_le hN he'
    · exact Real.rpow_nonneg (by linarith) _
    · positivity
  by_cases hlow : lam≤9/10
  · refine ⟨6,by norm_num,by norm_num,by norm_num; linarith,?_⟩
    apply hfinish 6 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa only [Nat.cast_ofNat,Nat.cast_one] using halasz_low_degree_saving hlo hlow
  · have hmed : 9/10≤ lam := by linarith
    obtain ⟨hk,hd,hdk,hkl,hkh,hdl,hdh⟩ := halasz_medium_degree_bounds hmed
    have hk150 : halaszMediumDegree lam≤150 := by
      exact_mod_cast (show (halaszMediumDegree lam:ℝ)≤150 by linarith)
    refine ⟨halaszMediumDegree lam,hk,hk150,?_,?_⟩
    · have ht := halasz_small_taylor_exponent hkl
      linarith
    · apply hfinish (halaszMediumDegree lam) (halaszMediumActive lam) hk hk150 hd hdk
      exact halasz_medium_degree_saving hmed hhi (by positivity) hkh hdl hdh

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszShortScale
namespace OAI

/-! Integer short-variable lengths for the logarithmic bilinear argument. -/
namespace TwoPointCorrelations


lemma halasz_short_scale_bounds {N α : ℝ} (hN : 1≤ N) (hα : 0≤α) :
    1≤ halaszShortScale N α ∧ N^α≤2*(halaszShortScale N α:ℝ) ∧
      (halaszShortScale N α:ℝ)≤ N^α := by
  have hy : 1≤ N^α := Real.one_le_rpow hN hα
  have hy0 : 0≤ N^α := by linarith
  have hp : 1≤ halaszShortScale N α := (Nat.le_floor_iff hy0).mpr (by exact_mod_cast hy)
  have hpR : 1≤(halaszShortScale N α:ℝ) := by exact_mod_cast hp
  refine ⟨hp,?_,Nat.floor_le hy0⟩
  have hh : N^α<(halaszShortScale N α:ℝ)+1 := Nat.lt_floor_add_one _
  linarith


lemma halasz_short_scale_le_base {N α : ℝ} (hN : 1≤ N) (hα : 0≤α) (hα1 : α≤1) :
    (halaszShortScale N α:ℝ)≤ N := by
  apply (halasz_short_scale_bounds hN hα).2.2.trans
  convert (preTransparency := .instances) Real.rpow_le_rpow_of_exponent_le hN hα1 using 1
  exact (Real.rpow_one N).symm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszLogPhase
namespace OAI

/-! An absolute logarithmic phase estimate on every prefix of a dyadic block.
The only size restriction separates off finitely many small blocks. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.Complex

theorem halasz_log_phase_bound : ∃ C : ℝ, 1≤ C ∧ ∀ N H : ℕ,
    1≤ N → H≤ N → ∀ a t lam : ℝ, a∈Set.Icc (0:ℝ) 1 → 49/100≤ lam →
    (N:ℝ)^(2/3:ℝ)≤(N:ℝ)/2 → |t|=(N:ℝ)^lam →
    ‖∑ n∈range H,Complex.exp (Complex.I*((t*Real.log ((N:ℝ)+a+n):ℝ):ℂ))‖≤
      (N:ℝ)*(C*(lam+1)^6*(N:ℝ)^(-1/((10^15:ℝ)*lam^2)))+
        4*(N:ℝ)^(2/3:ℝ) := by
  obtain ⟨R₁,hR₁⟩ := halasz_bounded_log_polynomial
  obtain ⟨R₂,hR₂⟩ := halasz_large_log_polynomial_saving
  let R := max R₁ R₂
  let C : ℝ := (R+200:ℝ)^6
  have hC : 1≤ C := by
    dsimp only [C]
    exact one_le_pow₀ (by have := (Nat.cast_nonneg R : (0:ℝ)≤ R); linarith)
  refine ⟨C,hC,?_⟩
  intro N H hN hH a t lam ha hlam hhalf ht
  have hNR : 1≤(N:ℝ) := by exact_mod_cast hN
  have hN0 : 0<(N:ℝ) := by linarith
  have hlam0 : 0< lam := by linarith
  have hlam1 : 1≤ lam+1 := by linarith
  have hC0 : 0≤ C := by linarith
  have hA0 : 0≤ C*(lam+1)^6*(N:ℝ)^(-1/((10^15:ℝ)*lam^2)) := by positivity
  by_cases hsmall : lam≤48
  · obtain ⟨k,hk,hkhi,htay,hpoly⟩ := hR₁ lam hlam hsmall
    apply halasz_phase_from_polynomial hN hH ha (by norm_num : (0:ℝ)≤1/3)
      (by norm_num : (1/3:ℝ)≤1/3) hA0 hhalf ht
      (by convert (preTransparency := .instances) htay using 1; ring)
    intro z hz
    have hM := halasz_short_scale_bounds hNR (by norm_num : (0:ℝ)≤1/3)
    have hp := hpoly (halaszShortScale N (1/3)) hM.1 t z N
      (halasz_short_scale_le_base hNR (by norm_num) (by norm_num)) hz.1 hz.2 ht hM.2.1
    apply hp.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hN0.le _)
    calc
      (R₁+182:ℝ)^6 ≤ C := by
        apply pow_le_pow_left₀ (by positivity)
        have hR : R₁≤ R := le_max_left _ _
        have hRR : (R₁:ℝ)≤ R := by exact_mod_cast hR
        linarith
      _ ≤ C*(lam+1)^6 := le_mul_of_one_le_right hC0 (one_le_pow₀ hlam1)
  · have hlarge : 48≤ lam := by linarith
    obtain ⟨hm,hlo,hhi,hkbound⟩ := halasz_large_degree_selection hlarge
    let m := ⌈lam/6⌉₊
    apply halasz_phase_from_polynomial (k := 12*m) hN hH ha
      (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)≤1/3) hA0 hhalf ht
    · have hh := halasz_large_taylor_exponent (m := m) hhi
      convert (preTransparency := .instances) hh using 1; push_cast; ring
    · intro z hz
      have hM := halasz_short_scale_bounds hNR (by norm_num : (0:ℝ)≤1/4)
      have hp := hR₂ m hm (halaszShortScale N (1/4)) hM.1 t z N lam
        (halasz_short_scale_le_base hNR (by norm_num) (by norm_num)) hz.1 hz.2
        ht hM.2.1 hlo hhi
      apply hp.trans
      apply mul_le_mul
      · calc
          (R₂+12*m+32:ℝ)^6 ≤ ((R+200:ℝ)*(lam+1))^6 := by
            apply pow_le_pow_left₀ (by positivity)
            have hR : R₂≤ R := le_max_right _ _
            have hRR : (R₂:ℝ)≤ R := by exact_mod_cast hR
            have hR0 : 0≤(R:ℝ) := Nat.cast_nonneg _
            have hRL : 0≤(R:ℝ)*lam := mul_nonneg hR0 hlam0.le
            dsimp only [m]
            nlinarith
          _ = C*(lam+1)^6 := by rw [mul_pow]
      · apply Real.rpow_le_rpow_of_exponent_le hNR
        rw [neg_div,neg_div]
        apply neg_le_neg
        apply one_div_le_one_div_of_le (by positivity : (0:ℝ)<10^8*lam^2)
        nlinarith [sq_nonneg lam]
      · exact Real.rpow_nonneg hN0.le _
      · positivity

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszLogDirichletBlock
namespace OAI

/-! Uniform Dirichlet block bounds in the weak Vinogradov--Korobov strip.
The harmless power of the height replaces all degree-selection constants. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.Complex

theorem halasz_log_dirichlet_block : ∃ C : ℝ, 1≤ C ∧ ∀ N H : ℕ,
    1≤ N → H≤ N → ∀ a : ℝ, a∈Set.Icc (0:ℝ) 1 → ∀ s : ℂ,
    2/3≤ s.re → ∀ L lam : ℝ, 0< L → 1≤ Real.log N →
    L=lam*Real.log N → 49/100≤ lam →
    (N:ℝ)^(2/3:ℝ)≤(N:ℝ)/2 → |s.im|=(N:ℝ)^lam →
    ‖∑ n∈range H,(((N:ℝ)+a+n:ℝ):ℂ)^(-s)‖≤
      C*(L+1)^6*Real.exp ((10^9:ℝ)*(max (1-s.re) 0)^(3/2:ℝ)*L)+4 := by
  obtain ⟨C,hC,hphase⟩ := halasz_log_phase_bound
  refine ⟨C,hC,?_⟩
  intro N H hN hH a ha s hσ L lam hL hy hLy hlam hhalf ht
  have hNR : 1≤(N:ℝ) := by exact_mod_cast hN
  have hN0 : 0<(N:ℝ) := by linarith
  have hx : 0<(N:ℝ)+a := by linarith [ha.1]
  have hlam0 : 0< lam := by linarith
  have hlamL : lam≤ L := by nlinarith
  let δ := max (1-s.re) 0
  let η := 1/((10^15:ℝ)*lam^2)
  let A := C*(lam+1)^6*(N:ℝ)^(-η)
  have hA : 0≤ A := by dsimp only [A]; positivity
  have hw := halasz_weighted_log_prefix hx s (by linarith : 0≤ s.re) H
    ((N:ℝ)*A+4*(N:ℝ)^(2/3:ℝ)) (fun n hn => by
      have hh := hphase N n hN (hn.trans hH) a (-s.im) lam ha hlam hhalf
        (by simpa only [abs_neg] using ht)
      simpa only [A,η,neg_div] using hh)
  have hwbase : ((N:ℝ)+a)^(-s.re)≤(N:ℝ)^(-s.re) :=
    Real.rpow_le_rpow_of_nonpos hN0 (by linarith [ha.1]) (by linarith)
  apply hw.trans
  apply (mul_le_mul_of_nonneg_right hwbase (by positivity)).trans
  have hmain : (N:ℝ)^(-s.re)*((N:ℝ)*A)=
      C*(lam+1)^6*Real.exp ((1-s.re)*Real.log N-
        (Real.log N)^3/((10^15:ℝ)*L^2)) := by
    have hp : (N:ℝ)^(-s.re)*(N:ℝ)*(N:ℝ)^(-η)=
        (N:ℝ)^(1-s.re-η) := by
      calc
        _ = (N:ℝ)^(-s.re+1)*(N:ℝ)^(-η) := by
          rw [Real.rpow_add hN0,Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hN0]; congr 1; ring
    dsimp only [A]
    calc
      _ = C*(lam+1)^6*((N:ℝ)^(-s.re)*(N:ℝ)*(N:ℝ)^(-η)) := by ring
      _ = C*(lam+1)^6*Real.exp ((1-s.re-η)*Real.log N) := by
        rw [hp,Real.rpow_def_of_pos hN0]
        congr 2
        ring
      _ = _ := by
        congr 2
        have he := halasz_log_cubic_identity hL (show 0< Real.log N by linarith) hLy
        dsimp only [η]
        calc
          _ = (1-s.re)*Real.log N+(-1/((10^15:ℝ)*lam^2))*Real.log N := by ring
          _ = _ := by rw [he]; ring
  have htail : (N:ℝ)^(-s.re)*(N:ℝ)^(2/3:ℝ)≤1 := by
    rw [← Real.rpow_add hN0]
    apply Real.rpow_le_one_of_one_le_of_nonpos hNR
    linarith
  have hcubic : (1-s.re)*Real.log N-(Real.log N)^3/((10^15:ℝ)*L^2)≤
      (10^9:ℝ)*δ^(3/2:ℝ)*L := by
    have hh := halasz_cubic_maximum (show 0≤δ from le_max_right _ _)
      (show 0≤ Real.log N by linarith) hL
    have hm := mul_le_mul_of_nonneg_right (show 1-s.re≤δ from le_max_left _ _)
      (show 0≤ Real.log N by linarith)
    linarith
  have hcoef : C*(lam+1)^6≤ C*(L+1)^6 := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith) (by linarith) 6) (by linarith)
  have hresult := mul_le_mul hcoef (Real.exp_le_exp.mpr hcubic)
    (Real.exp_pos _).le (by positivity : 0≤ C*(L+1)^6)
  rw [mul_add,hmain]
  nlinarith only [hresult,htail]

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.halasz_log_dirichlet_block := @OAI.TwoPointCorrelations.halasz_log_dirichlet_block
