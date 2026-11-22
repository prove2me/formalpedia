-- Prove2me | solution 1 for MasulloGRH.completedHeckeLFunction_logDeriv_local_partial_fraction
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:21:49.575533+00:00
-- url     : https://prove2.me/submissions/6ac4463f-ebca-41fe-b68d-e2a5626d8845

import Definitions.Def_MasulloGRH_CompletedL
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_disk_logderiv
import Theorems.Thm_PNTA_ZerosBound
import Theorems.Thm_Complex_exists_forall_norm_digamma_le_mul_log_norm_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re
import Theorems.Thm_MasulloGRH_heckeLFunction_exists_meromorphic_continuation
import Theorems.Thm_MasulloGRH_heckeLFunction_polynomial_growth_on_vertical_strips
import Theorems.Thm_MasulloGRH_completedHeckeLFunction_properties
import Theorems.Thm_MasulloGRH_heckeLFunction_inv_polynomial_growth_on_one_line

set_option autoImplicit false

/-!
Local partial fraction expansion of the logarithmic derivative of a completed Hecke L-function.
Landau's lemma (from `OAI.TwoPointCorrelations.mrt_disk_logderiv` and `PNTA.ZerosBound`) is
applied to the finite L-function on the disk of radius 3 about `1 + it`; the Archimedean factor is
handled with the digamma bound; the zeros lie in the critical strip by the functional equation.
-/

open Complex Metric Filter Topology

namespace Sol_MasulloGRH_completedHeckeLFunction_logDeriv_local_partial_fraction

/-- Analytic orders are invariant under `z ↦ f (a + b z) * c` with `b ≠ 0`, `c ≠ 0`. -/
lemma analyticOrderAt_affine (f : ℂ → ℂ) (a b c z : ℂ) (hb : b ≠ 0) (hc : c ≠ 0)
    (hf : AnalyticAt ℂ f (a + b * z)) :
    analyticOrderAt (fun w => f (a + b * w) * c) z = analyticOrderAt f (a + b * z) := by
  have hφ : AnalyticAt ℂ (fun w : ℂ => a + b * w) z := by fun_prop
  have hcomp : AnalyticAt ℂ (f ∘ fun w : ℂ => a + b * w) z := AnalyticAt.comp (g := f) (f := fun w : ℂ => a + b * w) hf hφ
  have hg : AnalyticAt ℂ (fun w => f (a + b * w) * c) z := hcomp.mul analyticAt_const
  have hderiv : deriv (fun w : ℂ => a + b * w) z ≠ 0 := by
    have : HasDerivAt (fun w : ℂ => a + b * w) b z := by
      simpa using ((hasDerivAt_id z).const_mul b).const_add a
    rw [this.deriv]; exact hb
  have h1 : meromorphicOrderAt (fun w => f (a + b * w) * c) z =
      meromorphicOrderAt f (a + b * z) := by
    have : (fun w => f (a + b * w) * c) = (f ∘ fun w : ℂ => a + b * w) * fun _ => c := by
      ext w; simp
    rw [this, meromorphicOrderAt_mul hcomp.meromorphicAt analyticAt_const.meromorphicAt,
      meromorphicOrderAt_comp_of_deriv_ne_zero hφ hderiv]
    rw [(analyticAt_const (v := c)).meromorphicOrderAt_eq,
      (analyticOrderAt_eq_zero.mpr (Or.inr hc))]
    simp
  rw [hg.meromorphicOrderAt_eq, hf.meromorphicOrderAt_eq] at h1
  exact ENat.map_natCast_injective h1


/-- Landau's lemma on a general disk, from the unit-disk version. -/
theorem landau_disk (f : ℂ → ℂ) (s₀ : ℂ) (R B : ℝ) (hR : 0 < R)
    (hf : ∀ w, ‖w - s₀‖ ≤ 6 / 5 * R → AnalyticAt ℂ f w) (hf0 : f s₀ ≠ 0) (hB : 2 ≤ B)
    (hbound : ∀ w, ‖w - s₀‖ ≤ 15 / 16 * R → ‖f w‖ ≤ B * ‖f s₀‖) :
    ∃ Z : Finset ℂ, (∀ ρ, ρ ∈ Z ↔ (‖ρ - s₀‖ ≤ 7 / 8 * R ∧ f ρ = 0)) ∧
      (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) ≤
        1 / Real.log ((15 / 16) / (7 / 8)) * Real.log B ∧
      ∀ s, ‖s - s₀‖ ≤ 3 / 4 * R → f s ≠ 0 →
        ‖logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ ≤
          OAI.TwoPointCorrelations.mrtCharacterLogDerivativeConstant / R * Real.log B := by
  classical
  set c : ℂ := (f s₀)⁻¹ with hc_def
  have hc : c ≠ 0 := inv_ne_zero hf0
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  set φ : ℂ → ℂ := fun z => s₀ + (R : ℂ) * z with hφ_def
  set g : ℂ → ℂ := fun z => f (s₀ + (R : ℂ) * z) * c with hg_def
  have hnormφ : ∀ z, ‖φ z - s₀‖ = R * ‖z‖ := by
    intro z; simp [φ, norm_mul, abs_of_pos hR]
  have hg_an : ∀ z, ‖z‖ ≤ 6 / 5 → AnalyticAt ℂ g z := by
    intro z hz
    have h1 : AnalyticAt ℂ f (s₀ + (R : ℂ) * z) := hf _ (by
      have := hnormφ z; simp only [φ] at this; rw [this]; nlinarith)
    have hφa : AnalyticAt ℂ (fun w : ℂ => s₀ + (R : ℂ) * w) z := by fun_prop
    exact (AnalyticAt.comp (g := f) (f := fun w : ℂ => s₀ + (R : ℂ) * w) h1 hφa).mul analyticAt_const
  have hg1 : ∀ z ∈ closedBall (0 : ℂ) 1, AnalyticAt ℂ g z := by
    intro z hz; rw [mem_closedBall, dist_zero_right] at hz; exact hg_an z (by linarith)
  have hg0 : g 0 = 1 := by simp [g, c, hf0]
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hgB : ∀ z, ‖z‖ ≤ 15 / 16 → ‖g z‖ ≤ B := by
    intro z hz
    have h1 := hbound (φ z) (by rw [hnormφ]; nlinarith)
    have hpos : 0 < ‖f s₀‖ := norm_pos_iff.mpr hf0
    simp only [g, norm_mul, c, norm_inv]
    rw [mul_inv_le_iff₀ hpos]; exact h1
  -- the unit-disk lemma
  have hmain := fun z (hz : ‖z‖ ≤ 3 / 4) (hgz : g z ≠ 0) =>
    OAI.TwoPointCorrelations.mrt_disk_logderiv g hg1 hg0 hlogB (by
      intro w hw; rw [mem_closedBall, dist_zero_right] at hw
      rw [Real.exp_log (by linarith)]; exact hgB w hw) hz hgz
  set Zg := (OAI.TwoPointCorrelations.mrtDiskZeros_finite g hg1 hg0).toFinset with hZg
  have hmemZg : ∀ ρ', ρ' ∈ Zg ↔ (‖ρ'‖ ≤ 7 / 8 ∧ g ρ' = 0) := by
    intro ρ'
    rw [hZg, Set.Finite.mem_toFinset]
    simp [OAI.TwoPointCorrelations.mrtDiskZeros, Erdos970.zerosetKfR]
  have hφinj : Function.Injective φ := by
    intro x y hxy; simp only [φ, add_right_inj] at hxy
    exact mul_left_cancel₀ hRc hxy
  have hord : ∀ z, ‖z‖ ≤ 6 / 5 → analyticOrderAt g z = analyticOrderAt f (φ z) := by
    intro z hz
    have h1 : AnalyticAt ℂ f (s₀ + (R : ℂ) * z) := hf _ (by
      have := hnormφ z; simp only [φ] at this; rw [this]; nlinarith)
    exact analyticOrderAt_affine f s₀ R c z hRc hc h1
  refine ⟨Zg.image φ, ?_, ?_, ?_⟩
  · intro ρ
    rw [Finset.mem_image]
    constructor
    · rintro ⟨ρ', hρ', rfl⟩
      rw [hmemZg] at hρ'
      refine ⟨by rw [hnormφ]; nlinarith [hρ'.1], ?_⟩
      have := hρ'.2; simp only [g, mul_eq_zero, hc, or_false] at this; exact this
    · rintro ⟨hρ1, hρ2⟩
      refine ⟨(ρ - s₀) / R, ?_, ?_⟩
      · rw [hmemZg]
        constructor
        · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_le_iff₀ hR]
          linarith
        · simp only [g]; rw [mul_div_cancel₀ _ hRc]; simp [hρ2]
      · simp only [φ]; rw [mul_div_cancel₀ _ hRc]; ring
  · -- zero count
    have hgAN : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) 1) := hg1
    set g₂ : ℂ → ℂ := fun z => g (6 / 5 * z) with hg₂
    have hg₂AN : AnalyticOnNhd ℂ g₂ (closedBall (0 : ℂ) 1) := by
      intro z hz; rw [mem_closedBall, dist_zero_right] at hz
      have h1 : AnalyticAt ℂ g (6 / 5 * z) := hg_an _ (by rw [norm_mul]; norm_num; linarith)
      exact AnalyticAt.comp (g := g) (f := fun w : ℂ => 6 / 5 * w) h1 (by fun_prop)
    have hfin2 := Erdos970.lem_Contra_finiteKR (5 / 6) (by norm_num) (by norm_num) g₂ hg₂AN
      ⟨0, by simp, by simp [g₂, hg0]⟩
    have hfin1 : (PNTA.SetOfZeros 1 g).Finite := by
      refine (hfin2.image (fun z : ℂ => 6 / 5 * z)).subset ?_
      intro ρ hρ
      simp only [PNTA.SetOfZeros, Set.mem_ofPred_eq] at hρ
      refine ⟨5 / 6 * ρ, ?_, by ring⟩
      simp only [Erdos970.zerosetKfR, Set.mem_ofPred_eq, mem_closedBall, dist_zero_right, g₂]
      refine ⟨by rw [norm_mul]; norm_num; linarith [hρ.1], ?_⟩
      rw [show (6 / 5 : ℂ) * (5 / 6 * ρ) = ρ by ring]; exact hρ.2
    have hZB := PNTA.ZerosBound (B := B) (r := 7 / 8) (R := 15 / 16) (f := g) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) hgAN hg0 hfin1 hgB
    have hsets : (PNTA.finiteSetOfZeros_mono (r := 7 / 8) (by norm_num) hfin1).toFinset = Zg := by
      ext ρ'; rw [Set.Finite.mem_toFinset, hmemZg]; simp [PNTA.SetOfZeros]
    rw [hsets] at hZB
    rw [Finset.sum_image (fun x _ y _ h => hφinj h)]
    calc (∑ x ∈ Zg, (analyticOrderNatAt f (φ x) : ℝ))
        = ((∑ x ∈ Zg, analyticOrderNatAt g x : ℕ) : ℝ) := by
          push_cast
          refine Finset.sum_congr rfl fun x hx => ?_
          rw [hmemZg] at hx
          simp only [analyticOrderNatAt, hord x (by linarith [hx.1])]
      _ ≤ _ := hZB
  · intro s hs hfs
    set z := (s - s₀) / (R : ℂ) with hz_def
    have hφz : φ z = s := by simp only [φ, z]; rw [mul_div_cancel₀ _ hRc]; ring
    have hz : ‖z‖ ≤ 3 / 4 := by
      rw [hz_def, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_le_iff₀ hR]
      linarith
    have hgz : g z ≠ 0 := by
      simp only [g]; rw [show s₀ + (R : ℂ) * z = s from hφz]; exact mul_ne_zero hfs hc
    have hm := hmain z hz hgz
    have hfs_an : AnalyticAt ℂ f s := hf s (by nlinarith)
    -- derivative of g
    have hdg : deriv g z = deriv f s * R * c := by
      have h1 : HasDerivAt (fun w : ℂ => s₀ + (R : ℂ) * w) (R : ℂ) z := by
        simpa using ((hasDerivAt_id z).const_mul (R : ℂ)).const_add s₀
      have h2 : HasDerivAt f (deriv f s) (s₀ + (R : ℂ) * z) := by
        rw [show s₀ + (R : ℂ) * z = s from hφz]; exact hfs_an.differentiableAt.hasDerivAt
      have h3 := (h2.comp z h1).mul_const c
      exact h3.deriv
    have hgz' : g z = f s * c := by simp only [g]; rw [show s₀ + (R : ℂ) * z = s from hφz]
    have hkey : deriv g z / g z - ∑ ρ ∈ Zg, ((analyticOrderAt g ρ).toNat : ℂ) / (z - ρ) =
        (R : ℂ) * (logDeriv f s - ∑ ρ ∈ Zg.image φ, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)) := by
      rw [Finset.sum_image (fun x _ y _ h => hφinj h), mul_sub, Finset.mul_sum, hdg, hgz',
        logDeriv_apply]
      congr 1
      · field_simp
      · refine Finset.sum_congr rfl fun ρ hρ => ?_
        rw [hmemZg] at hρ
        have hne : z - ρ ≠ 0 := by
          intro h; apply hgz; rw [sub_eq_zero] at h; rw [h]; exact hρ.2
        have hsφ : s - φ ρ = (R : ℂ) * (z - ρ) := by rw [← hφz]; simp only [φ]; ring
        rw [hsφ, hord ρ (by linarith [hρ.1]), analyticOrderNatAt]
        field_simp
    rw [hkey, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] at hm
    rw [div_mul_eq_mul_div, le_div_iff₀ hR, mul_comm]
    exact hm

end Sol_MasulloGRH_completedHeckeLFunction_logDeriv_local_partial_fraction

namespace Sol_MasulloGRH_completedHeckeLFunction_logDeriv_local_partial_fraction

lemma logDeriv_cpow_mul_Gamma (b α β w : ℂ) (hb : b ≠ 0) (hu : ∀ m : ℕ, α * w + β ≠ -m) :
    logDeriv (fun s => b ^ (-(α * s + β)) * Complex.Gamma (α * s + β)) w =
      -(Complex.log b) * α + Complex.digamma (α * w + β) * α := by
  have hd1 : HasDerivAt (fun s => α * s + β) α w := by
    simpa using ((hasDerivAt_id w).const_mul α).add_const β
  have hP : HasDerivAt (fun s => b ^ (-(α * s + β))) (b ^ (-(α * w + β)) * Complex.log b * (-α)) w :=
    (hd1.neg).const_cpow (Or.inl hb)
  have hΓ : DifferentiableAt ℂ Complex.Gamma (α * w + β) := Complex.differentiableAt_Gamma _ hu
  have hPne : b ^ (-(α * w + β)) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hb]; exact Complex.exp_ne_zero _
  have hΓne : Complex.Gamma (α * w + β) ≠ 0 := Complex.Gamma_ne_zero hu
  have hΓc : DifferentiableAt ℂ (fun s => Complex.Gamma (α * s + β)) w :=
    hΓ.comp w hd1.differentiableAt
  rw [logDeriv_mul w hPne hΓne hP.differentiableAt hΓc]
  have h2 : logDeriv (fun s => Complex.Gamma (α * s + β)) w = Complex.digamma (α * w + β) * α := by
    have := logDeriv_comp (f := Complex.Gamma) (g := fun s => α * s + β) hΓ hd1.differentiableAt
    rw [hd1.deriv] at this
    exact this
  rw [h2, logDeriv_apply, hP.deriv]
  field_simp

lemma not_neg_nat_of_im_ne_zero (u : ℂ) (hu : u.im ≠ 0) : ∀ m : ℕ, u ≠ -m := by
  intro m h; apply hu; rw [h]; simp

/-- Digamma bound on `Re ≥ -1`, away from the real axis. -/
lemma digamma_bound : ∃ C : ℝ, 0 < C ∧ ∀ u : ℂ, -1 ≤ u.re → 1 ≤ |u.im| →
    ‖Complex.digamma u‖ ≤ C * Real.log (2 + ‖u + 2‖) + 2 := by
  obtain ⟨C, hC, h⟩ :=
    Complex.exists_forall_norm_digamma_le_mul_log_norm_and_norm_logDeriv_GammaReal_le_and_norm_logDeriv_GammaComplex_le_of_le_re
      1 one_pos
  refine ⟨C, hC, fun u hre him => ?_⟩
  have him0 : u.im ≠ 0 := by intro h0; rw [h0] at him; simp at him; linarith
  have hu0 := not_neg_nat_of_im_ne_zero u him0
  have hu1 := not_neg_nat_of_im_ne_zero (u + 1) (by simpa using him0)
  have e1 := Complex.digamma_apply_add_one u hu0
  have e2 := Complex.digamma_apply_add_one (u + 1) hu1
  have hdig : Complex.digamma u = Complex.digamma (u + 2) - u⁻¹ - (u + 1)⁻¹ := by
    rw [show u + 2 = u + 1 + 1 by ring, e2, e1]; ring
  have hn1 : ‖u⁻¹‖ ≤ 1 := by
    rw [norm_inv]; apply inv_le_one_of_one_le₀
    exact him.trans (Complex.abs_im_le_norm u)
  have hn2 : ‖(u + 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]; apply inv_le_one_of_one_le₀
    have := Complex.abs_im_le_norm (u + 1); simp at this; linarith
  have h3 := (h (u + 2) (by simp; linarith)).1
  rw [hdig]
  calc ‖Complex.digamma (u + 2) - u⁻¹ - (u + 1)⁻¹‖
      ≤ ‖Complex.digamma (u + 2)‖ + ‖u⁻¹‖ + ‖(u + 1)⁻¹‖ := by
        have := norm_sub_le (Complex.digamma (u + 2) - u⁻¹) (u + 1)⁻¹
        have := norm_sub_le (Complex.digamma (u + 2)) u⁻¹
        linarith
    _ ≤ C * Real.log (2 + ‖u + 2‖) + 1 + 1 := by gcongr
    _ = _ := by ring


lemma cpow_mul_Gamma_diff (b α β w : ℂ) (hb : b ≠ 0) (hu : ∀ m : ℕ, α * w + β ≠ -m) :
    DifferentiableAt ℂ (fun s => b ^ (-(α * s + β)) * Complex.Gamma (α * s + β)) w ∧
      b ^ (-(α * w + β)) * Complex.Gamma (α * w + β) ≠ 0 := by
  have hd1 : HasDerivAt (fun s => α * s + β) α w := by
    simpa using ((hasDerivAt_id w).const_mul α).add_const β
  have hP : HasDerivAt (fun s => b ^ (-(α * s + β))) (b ^ (-(α * w + β)) * Complex.log b * (-α)) w :=
    (hd1.neg).const_cpow (Or.inl hb)
  have hΓ : DifferentiableAt ℂ Complex.Gamma (α * w + β) := Complex.differentiableAt_Gamma _ hu
  have hPne : b ^ (-(α * w + β)) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hb]; exact Complex.exp_ne_zero _
  exact ⟨hP.differentiableAt.mul (hΓ.comp w hd1.differentiableAt),
    mul_ne_zero hPne (Complex.Gamma_ne_zero hu)⟩

lemma factor_bound (C : ℝ)
    (hdig : ∀ u : ℂ, -1 ≤ u.re → 1 ≤ |u.im| → ‖Complex.digamma u‖ ≤ C * Real.log (2 + ‖u + 2‖) + 2)
    (b α β w : ℂ) (hb : b ≠ 0) (hα : ‖α‖ ≤ 1) (hre : -1 ≤ (α * w + β).re)
    (him : 1 ≤ |(α * w + β).im|) :
    ‖logDeriv (fun s => b ^ (-(α * s + β)) * Complex.Gamma (α * s + β)) w‖ ≤
      ‖Complex.log b‖ + (C * Real.log (2 + ‖α * w + β + 2‖) + 2) := by
  have him0 : (α * w + β).im ≠ 0 := by intro h0; rw [h0] at him; simp at him; linarith
  rw [logDeriv_cpow_mul_Gamma b α β w hb (not_neg_nat_of_im_ne_zero _ him0)]
  have h1 := hdig _ hre him
  calc ‖-Complex.log b * α + Complex.digamma (α * w + β) * α‖
      ≤ ‖-Complex.log b * α‖ + ‖Complex.digamma (α * w + β) * α‖ := norm_add_le _ _
    _ ≤ ‖Complex.log b‖ + ‖Complex.digamma (α * w + β)‖ := by
        rw [norm_mul, norm_mul, norm_neg]
        gcongr
        · exact mul_le_of_le_one_right (norm_nonneg _) hα
        · exact mul_le_of_le_one_right (norm_nonneg _) hα
    _ ≤ _ := by gcongr

end Sol_MasulloGRH_completedHeckeLFunction_logDeriv_local_partial_fraction

namespace Sol_MasulloGRH_completedHeckeLFunction_logDeriv_local_partial_fraction
open MasulloGRH

variable {F : Type*} [Field F] [NumberField F]

lemma archLFactor_eq_real (χ : HeckeCharacter F) (v : NumberField.InfinitePlace F) (hv : v.IsReal) :
    χ.archLFactor v = fun s => (Real.pi : ℂ) ^ (-((1 / 2 : ℂ) * s +
        ((χ.archExponent v : ℂ) * Complex.I + (χ.archParity v : ℂ)) / 2)) *
      Complex.Gamma ((1 / 2 : ℂ) * s + ((χ.archExponent v : ℂ) * Complex.I + (χ.archParity v : ℂ)) / 2) := by
  funext s
  simp only [HeckeCharacter.archLFactor, if_pos hv]
  rw [show (s + (χ.archExponent v : ℂ) * Complex.I + (χ.archParity v : ℂ)) / 2 =
    (1 / 2 : ℂ) * s + ((χ.archExponent v : ℂ) * Complex.I + (χ.archParity v : ℂ)) / 2 by ring]

lemma archLFactor_eq_complex (χ : HeckeCharacter F) (v : NumberField.InfinitePlace F)
    (hv : ¬ v.IsReal) :
    χ.archLFactor v = fun s => (2 * Real.pi : ℂ) ^ (-((1 : ℂ) * s +
        ((χ.archExponent v : ℂ) * Complex.I + (χ.archWeight v : ℂ) / 2))) *
      Complex.Gamma ((1 : ℂ) * s + ((χ.archExponent v : ℂ) * Complex.I + (χ.archWeight v : ℂ) / 2)) := by
  funext s
  simp only [HeckeCharacter.archLFactor, if_neg hv]
  rw [show s + (χ.archExponent v : ℂ) * Complex.I + (χ.archWeight v : ℂ) / 2 =
    (1 : ℂ) * s + ((χ.archExponent v : ℂ) * Complex.I + (χ.archWeight v : ℂ) / 2) by ring]


lemma archParity_le_one (χ : HeckeCharacter F) (v : NumberField.InfinitePlace F) :
    χ.archParity v ≤ 1 := by
  unfold HeckeCharacter.archParity; split_ifs <;> norm_num

lemma norm_le_re_im (z : ℂ) : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z

lemma log_pi_le : ‖Complex.log (Real.pi : ℂ)‖ ≤ Real.log (2 * Real.pi) := by
  rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
  exact Real.log_le_log Real.pi_pos (by linarith [Real.pi_pos])

lemma log_two_pi_le : ‖Complex.log (2 * Real.pi : ℂ)‖ ≤ Real.log (2 * Real.pi) := by
  rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_log (by positivity), Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]

lemma archLFactor_local (χ : HeckeCharacter F) (v : NumberField.InfinitePlace F) (w : ℂ)
    (hw : w.im + χ.archExponent v ≠ 0) :
    DifferentiableAt ℂ (χ.archLFactor v) w ∧ χ.archLFactor v w ≠ 0 := by
  by_cases hv : v.IsReal
  · rw [archLFactor_eq_real χ v hv]
    refine cpow_mul_Gamma_diff _ _ _ w (by exact_mod_cast Real.pi_pos.ne') ?_
    apply not_neg_nat_of_im_ne_zero
    simp
    intro h; apply hw; linarith
  · rw [archLFactor_eq_complex χ v hv]
    refine cpow_mul_Gamma_diff _ _ _ w (by
      have := Real.pi_pos; exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)) ?_
    apply not_neg_nat_of_im_ne_zero
    simpa using hw

lemma archLFactor_logDeriv_le (χ : HeckeCharacter F) (v : NumberField.InfinitePlace F) (C : ℝ)
    (hC : 0 ≤ C)
    (hdig : ∀ u : ℂ, -1 ≤ u.re → 1 ≤ |u.im| → ‖Complex.digamma u‖ ≤ C * Real.log (2 + ‖u + 2‖) + 2)
    (w : ℂ) (hre1 : -1 ≤ w.re) (hre2 : w.re ≤ 2) (hw : 2 ≤ |w.im + χ.archExponent v|) :
    ‖logDeriv (χ.archLFactor v) w‖ ≤ Real.log (2 * Real.pi) +
      (C * Real.log (2 + (|w.im| + |χ.archExponent v| + χ.archWeight v + 5)) + 2) := by
  have hn : (0:ℝ) ≤ (χ.archWeight v : ℝ) := Nat.cast_nonneg _
  have habs := abs_add_le w.im (χ.archExponent v)
  have h0w := abs_nonneg w.im
  have h0t := abs_nonneg (χ.archExponent v)
  by_cases hv : v.IsReal
  · rw [archLFactor_eq_real χ v hv]
    have ha' : ((χ.archParity v : ℕ) : ℝ) ≤ 1 := by exact_mod_cast archParity_le_one χ v
    have ha0 : (0:ℝ) ≤ (χ.archParity v : ℝ) := Nat.cast_nonneg _
    set u := (1 / 2 : ℂ) * w + ((χ.archExponent v : ℂ) * Complex.I + (χ.archParity v : ℂ)) / 2
      with hu
    have hure : u.re = w.re / 2 + (χ.archParity v : ℝ) / 2 := by rw [hu]; simp; ring
    have huim : u.im = (w.im + χ.archExponent v) / 2 := by rw [hu]; simp; ring
    have hu2re : (u + 2).re = u.re + 2 := by simp
    have hu2im : (u + 2).im = u.im := by simp
    refine (factor_bound C hdig _ _ _ w (by exact_mod_cast Real.pi_pos.ne') (by norm_num) ?_ ?_).trans ?_
    · rw [hure]; linarith
    · rw [huim, abs_div, abs_two]; linarith
    · gcongr
      · exact log_pi_le
      · have h1 := norm_le_re_im (u + 2)
        rw [hu2re, hu2im, hure, huim] at h1
        have hre : |w.re / 2 + (χ.archParity v : ℝ) / 2 + 2| ≤ 4 := by
          rw [abs_le]; constructor <;> linarith
        have him : |(w.im + χ.archExponent v) / 2| ≤ |w.im| + |χ.archExponent v| := by
          rw [abs_div, abs_two]; linarith
        linarith
  · rw [archLFactor_eq_complex χ v hv]
    set u := (1 : ℂ) * w + ((χ.archExponent v : ℂ) * Complex.I + (χ.archWeight v : ℂ) / 2)
      with hu
    have hure : u.re = w.re + (χ.archWeight v : ℝ) / 2 := by rw [hu]; simp
    have huim : u.im = w.im + χ.archExponent v := by rw [hu]; simp
    have hu2re : (u + 2).re = u.re + 2 := by simp
    have hu2im : (u + 2).im = u.im := by simp
    refine (factor_bound C hdig _ _ _ w (by
      have := Real.pi_pos; exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0))
      (by norm_num) ?_ ?_).trans ?_
    · rw [hure]; linarith
    · rw [huim]; linarith
    · gcongr
      · exact log_two_pi_le
      · have h1 := norm_le_re_im (u + 2)
        rw [hu2re, hu2im, hure, huim] at h1
        have hre : |w.re + (χ.archWeight v : ℝ) / 2 + 2| ≤ 4 + χ.archWeight v := by
          rw [abs_le]; constructor <;> linarith
        linarith


lemma gamma_props (χ : HeckeCharacter F) : ∃ TG KG : ℝ, 2 ≤ TG ∧
    (∀ w : ℂ, TG ≤ |w.im| → AnalyticAt ℂ χ.gammaFactor w ∧ χ.gammaFactor w ≠ 0) ∧
    ∀ w : ℂ, -1 ≤ w.re → w.re ≤ 2 → TG ≤ |w.im| →
      ‖logDeriv χ.gammaFactor w‖ ≤ KG * Real.log |w.im| := by
  classical
  obtain ⟨C, hC, hdig⟩ := digamma_bound
  set Kt : ℝ := ∑ v : NumberField.InfinitePlace F, (|χ.archExponent v| + (χ.archWeight v : ℝ))
    with hKt_def
  have hKt : ∀ v, |χ.archExponent v| + (χ.archWeight v : ℝ) ≤ Kt := by
    intro v
    exact Finset.single_le_sum (f := fun v => |χ.archExponent v| + (χ.archWeight v : ℝ))
      (fun v _ => by positivity) (Finset.mem_univ v)
  have hKt0 : 0 ≤ Kt := Finset.sum_nonneg (fun v _ => by positivity)
  have hG : χ.gammaFactor = fun s => ∏ v ∈ Finset.univ, χ.archLFactor v s := by
    funext s; rfl
  have hloc : ∀ w : ℂ, Kt + 6 < |w.im| → ∀ v, 6 ≤ |w.im + χ.archExponent v| := by
    intro w hw v
    have h1 := hKt v
    have h2 : (0:ℝ) ≤ (χ.archWeight v : ℝ) := Nat.cast_nonneg _
    have h3 := abs_sub_abs_le_abs_add w.im (χ.archExponent v)
    have h4 : |w.im| - |χ.archExponent v| ≤ |w.im + χ.archExponent v| := by
      have := abs_add_le (w.im + χ.archExponent v) (-χ.archExponent v)
      rw [add_neg_cancel_right, abs_neg] at this; linarith
    linarith
  have hdiff : ∀ w : ℂ, Kt + 6 < |w.im| →
      DifferentiableAt ℂ χ.gammaFactor w ∧ χ.gammaFactor w ≠ 0 := by
    intro w hw
    have hv : ∀ v, w.im + χ.archExponent v ≠ 0 := by
      intro v h; have := hloc w hw v; rw [h, abs_zero] at this; linarith
    rw [hG]
    refine ⟨DifferentiableAt.fun_finsetProd (fun v _ => (archLFactor_local χ v w (hv v)).1), ?_⟩
    exact Finset.prod_ne_zero_iff.mpr (fun v _ => (archLFactor_local χ v w (hv v)).2)
  set card : ℝ := (Fintype.card (NumberField.InfinitePlace F) : ℝ)
  refine ⟨Kt + 7, card * ((Real.log (2 * Real.pi) + 2) / Real.log 2 + 2 * C), by linarith, ?_, ?_⟩
  · intro w hw
    have hU : IsOpen {y : ℂ | Kt + 6 < |y.im|} :=
      isOpen_lt continuous_const (continuous_abs.comp Complex.continuous_im)
    have hwU : w ∈ {y : ℂ | Kt + 6 < |y.im|} := by simp only [Set.mem_ofPred_eq]; linarith
    refine ⟨?_, (hdiff w (by linarith)).2⟩
    apply DifferentiableOn.analyticAt (s := {y : ℂ | Kt + 6 < |y.im|})
    · intro y hy; exact (hdiff y hy).1.differentiableWithinAt
    · exact hU.mem_nhds hwU
  · intro w hre1 hre2 hw
    have hv : ∀ v, w.im + χ.archExponent v ≠ 0 := by
      intro v h; have := hloc w (by linarith) v; rw [h, abs_zero] at this; linarith
    have hx2 : 2 ≤ |w.im| := by linarith
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogx : Real.log 2 ≤ Real.log |w.im| := Real.log_le_log (by norm_num) hx2
    have hsum : logDeriv χ.gammaFactor w = ∑ v ∈ Finset.univ, logDeriv (χ.archLFactor v) w := by
      rw [hG]
      exact logDeriv_prod (fun v _ => (archLFactor_local χ v w (hv v)).2)
        (fun v _ => (archLFactor_local χ v w (hv v)).1)
    rw [hsum]
    have hterm : ∀ v, ‖logDeriv (χ.archLFactor v) w‖ ≤
        ((Real.log (2 * Real.pi) + 2) / Real.log 2 + 2 * C) * Real.log |w.im| := by
      intro v
      have h1 := archLFactor_logDeriv_le χ v C hC.le hdig w hre1 hre2
        (by have := hloc w (by linarith) v; linarith)
      have h2 : Real.log (2 + (|w.im| + |χ.archExponent v| + χ.archWeight v + 5)) ≤
          2 * Real.log |w.im| := by
        rw [show (2:ℝ) * Real.log |w.im| = ((2:ℕ):ℝ) * Real.log |w.im| by norm_num,
          ← Real.log_pow]
        apply Real.log_le_log (by positivity)
        have := hKt v
        nlinarith
      have h3 : Real.log (2 * Real.pi) + 2 ≤
          (Real.log (2 * Real.pi) + 2) / Real.log 2 * Real.log |w.im| := by
        have hpos : 0 ≤ Real.log (2 * Real.pi) + 2 := by
          have := Real.log_nonneg (show (1:ℝ) ≤ 2 * Real.pi by linarith [Real.pi_gt_three])
          linarith
        rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
        exact mul_le_mul_of_nonneg_left hlogx hpos
      calc ‖logDeriv (χ.archLFactor v) w‖
          ≤ Real.log (2 * Real.pi) + (C * Real.log (2 + (|w.im| + |χ.archExponent v| +
              χ.archWeight v + 5)) + 2) := h1
        _ ≤ Real.log (2 * Real.pi) + 2 + C * (2 * Real.log |w.im|) := by
          have := mul_le_mul_of_nonneg_left h2 hC.le
          linarith
        _ ≤ _ := by nlinarith
    calc ‖∑ v ∈ Finset.univ, logDeriv (χ.archLFactor v) w‖
        ≤ ∑ v ∈ Finset.univ, ‖logDeriv (χ.archLFactor v) w‖ := norm_sum_le _ _
      _ ≤ ∑ v ∈ (Finset.univ : Finset (NumberField.InfinitePlace F)),
            ((Real.log (2 * Real.pi) + 2) / Real.log 2 + 2 * C) * Real.log |w.im| :=
          Finset.sum_le_sum (fun v _ => hterm v)
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Sol_MasulloGRH_completedHeckeLFunction_logDeriv_local_partial_fraction

namespace Sol_MasulloGRH_completedHeckeLFunction_logDeriv_local_partial_fraction
open MasulloGRH

variable {F : Type*} [Field F] [NumberField F]

lemma heckeL_nf (χ : HeckeCharacter F) : MeromorphicNFOn (heckeLFunction χ) Set.univ := by
  have h := heckeLFunction_exists_meromorphic_continuation F χ
  unfold heckeLFunction
  rw [dif_pos h]
  exact (Classical.choose_spec h).1

lemma analyticAt_of_bdd_nf {f : ℂ → ℂ} {x : ℂ} (hnf : MeromorphicNFAt f x) (K : ℝ)
    (hb : ∀ᶠ y in 𝓝[≠] x, ‖f y‖ ≤ K) : AnalyticAt ℂ f x := by
  rw [← hnf.meromorphicOrderAt_nonneg_iff_analyticAt]
  by_contra h
  push Not at h
  have h1 := tendsto_cobounded_of_meromorphicOrderAt_neg h
  rw [← tendsto_norm_atTop_iff_cobounded] at h1
  have h2 := h1.eventually (eventually_gt_atTop K)
  obtain ⟨y, hy1, hy2⟩ := (h2.and hb).exists
  linarith

lemma heckeL_analytic (χ : HeckeCharacter F) : ∃ T₁ : ℝ, ∀ w : ℂ, -3 < w.re → w.re < 5 →
    T₁ < |w.im| → AnalyticAt ℂ (heckeLFunction χ) w := by
  obtain ⟨M, hM, C, T, hb⟩ := heckeLFunction_polynomial_growth_on_vertical_strips F χ (-4) 6
    (by norm_num)
  refine ⟨|T| + 1, fun w hre1 hre2 him => ?_⟩
  apply analyticAt_of_bdd_nf (heckeL_nf χ (Set.mem_univ w)) (|C| * (|w.im| + 1) ^ M)
  apply eventually_nhdsWithin_of_eventually_nhds
  rw [Metric.eventually_nhds_iff]
  refine ⟨1 / 2, by norm_num, fun y hy => ?_⟩
  rw [dist_eq_norm] at hy
  have h1 := Complex.abs_re_le_norm (y - w)
  have h2 := Complex.abs_im_le_norm (y - w)
  rw [Complex.sub_re] at h1; rw [Complex.sub_im] at h2
  have h3 : |y.im| ≤ |w.im| + 1 := by
    have := abs_add_le (y.im - w.im) w.im; rw [sub_add_cancel] at this; linarith
  have h4 : |w.im| - 1 ≤ |y.im| := by
    have := abs_add_le (w.im - y.im) y.im; rw [sub_add_cancel] at this
    rw [abs_sub_comm] at this; linarith
  have hT := le_abs_self T
  have h1' := abs_le.mp (h1.trans hy.le)
  have hyb := hb y (by linarith [h1'.1]) (by linarith [h1'.2]) (by linarith)
  calc ‖heckeLFunction χ y‖ ≤ C * |y.im| ^ M := hyb
    _ ≤ |C| * |y.im| ^ M := by
        have := Real.rpow_nonneg (abs_nonneg y.im) M
        exact mul_le_mul_of_nonneg_right (le_abs_self C) this
    _ ≤ |C| * (|w.im| + 1) ^ M := by
        gcongr

/-- All zeros of the completed L-function lie in the open critical strip. -/
lemma zeros_strip (χ : HeckeCharacter F) (ρ : ℂ)
    (h : 0 < meromorphicOrderAt (completedHeckeLFunction χ) ρ) : 0 < ρ.re ∧ ρ.re < 1 := by
  obtain ⟨⟨hNF, -⟩, -, -, -, hstrip⟩ := completedHeckeLFunction_properties F χ
  by_cases hre : 0 < ρ.re
  · exact ⟨hre, hstrip ρ hre h⟩
  · exfalso
    push Not at hre
    obtain ⟨-, -, -, ⟨ε, hεd, hε0, hFE⟩, -⟩ := completedHeckeLFunction_properties F χ
    obtain ⟨-, -, -, -, hstrip'⟩ := completedHeckeLFunction_properties F χ⁻¹
    have hg : AnalyticAt ℂ (fun s : ℂ => 1 - s) ρ := by fun_prop
    have hg' : deriv (fun s : ℂ => 1 - s) ρ ≠ 0 := by
      have : HasDerivAt (fun s : ℂ => 1 - s) (-1) ρ := by
        simpa using (hasDerivAt_id ρ).const_sub 1
      rw [this.deriv]; norm_num
    have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero
      (f := completedHeckeLFunction χ⁻¹) hg hg'
    have hfun : (completedHeckeLFunction χ⁻¹ ∘ fun s : ℂ => 1 - s) =
        (fun s => ε s) * completedHeckeLFunction χ := by
      funext s; simp [hFE s]
    have hεa : AnalyticAt ℂ ε ρ := hεd.analyticAt ρ
    rw [hfun, meromorphicOrderAt_mul hεa.meromorphicAt (hNF.meromorphicOn ρ (Set.mem_univ ρ)),
      hεa.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr (hε0 ρ))] at hcomp
    simp only [ENat.map_zero, Nat.cast_zero, WithTop.coe_zero, zero_add] at hcomp
    have h1 := hstrip' (1 - ρ) (by simp; linarith) (by rw [← hcomp]; exact h)
    simp at h1; linarith

end Sol_MasulloGRH_completedHeckeLFunction_logDeriv_local_partial_fraction

open MasulloGRH

lemma Sol_MasulloGRH_completedHeckeLFunction_logDeriv_local_partial_fraction.untop₀_map (n : ℕ∞) : ((n.map (Nat.cast : ℕ → ℤ)).untop₀ : ℤ) = (n.toNat : ℤ) := by
  induction n using ENat.recTopCoe <;> simp

lemma Sol_MasulloGRH_completedHeckeLFunction_logDeriv_local_partial_fraction.map_pos (n : ℕ∞) : (0 : WithTop ℤ) < n.map (Nat.cast : ℕ → ℤ) ↔ n ≠ 0 := by
  induction n using ENat.recTopCoe
  · simp
  · rename_i k
    simp only [ENat.map_natCast, ne_eq, Nat.cast_eq_zero]
    constructor
    · intro h hk; subst hk; simp at h
    · intro hk; exact_mod_cast Nat.pos_of_ne_zero hk

set_option maxHeartbeats 1600000 in
theorem solution (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) :
    ∃ C T₀ : ℝ, 2 ≤ T₀ ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → T₀ ≤ |s.im| →
      completedHeckeLFunction χ s ≠ 0 →
      ‖logDeriv (completedHeckeLFunction χ) s -
          ∑ᶠ ρ ∈ {ρ : ℂ | 0 < meromorphicOrderAt (completedHeckeLFunction χ) ρ ∧
              |ρ.im - s.im| ≤ 1},
            (((meromorphicOrderAt (completedHeckeLFunction χ) ρ).untop₀ : ℤ) : ℂ) / (s - ρ)‖
        ≤ C * Real.log |s.im| := by
  classical
  by_cases hmer : MeromorphicOn (fun s => χ.gammaFactor s * heckeLFunction χ s) Set.univ
  swap
  · refine ⟨0, 2, le_refl _, fun s _ _ _ hs => absurd ?_ hs⟩
    simp only [completedHeckeLFunction]
    rw [toMeromorphicNFOn_of_not_meromorphicOn hmer]; rfl
  obtain ⟨T₁, hT₁⟩ := Sol_MasulloGRH_completedHeckeLFunction_logDeriv_local_partial_fraction.heckeL_analytic χ
  obtain ⟨M, hM, C₁, T₂, hgrowth⟩ :=
    heckeLFunction_polynomial_growth_on_vertical_strips F χ (-2) 4 (by norm_num)
  obtain ⟨N, hN, C₂, T₃, hinv⟩ := heckeLFunction_inv_polynomial_growth_on_one_line F χ
  obtain ⟨TG, KG, hTG, hGan, hGlog⟩ := Sol_MasulloGRH_completedHeckeLFunction_logDeriv_local_partial_fraction.gamma_props χ
  set L := heckeLFunction χ with hL
  set G := χ.gammaFactor with hGdef
  set Λ := completedHeckeLFunction χ with hΛ
  set T₄ := |T₁| + |TG| + 1 with hT₄
  have hT₁abs := le_abs_self T₁
  have hTGabs := le_abs_self TG
  have hT₁0 := abs_nonneg T₁
  have hTG0 := abs_nonneg TG
  -- local identification of Λ with G * L
  have hΛloc : ∀ w : ℂ, -3 < w.re → w.re < 5 → T₄ < |w.im| →
      Λ =ᶠ[𝓝 w] fun s => G s * L s := by
    intro w h1 h2 h3
    have hV : IsOpen {y : ℂ | -3 < y.re ∧ y.re < 5 ∧ T₄ < |y.im|} := by
      apply IsOpen.inter (isOpen_lt continuous_const Complex.continuous_re)
      apply IsOpen.inter (isOpen_lt Complex.continuous_re continuous_const)
      exact isOpen_lt continuous_const (continuous_abs.comp Complex.continuous_im)
    filter_upwards [hV.mem_nhds ⟨h1, h2, h3⟩] with y hy
    obtain ⟨hy1, hy2, hy3⟩ := hy
    have hLa : AnalyticAt ℂ L y := hT₁ y hy1 hy2 (by linarith)
    have hGa : AnalyticAt ℂ G y := (hGan y (by linarith)).1
    have hGLa : AnalyticAt ℂ (fun s => G s * L s) y := hGa.mul hLa
    rw [hΛ]
    simp only [completedHeckeLFunction]
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hmer (Set.mem_univ y),
      toMeromorphicNFAt_eq_self.mpr hGLa.meromorphicNFAt]
  -- order of Λ in terms of L
  have hord : ∀ w : ℂ, -3 < w.re → w.re < 5 → T₄ < |w.im| →
      meromorphicOrderAt Λ w = (analyticOrderAt L w).map (Nat.cast : ℕ → ℤ) := by
    intro w h1 h2 h3
    have hLa : AnalyticAt ℂ L w := hT₁ w h1 h2 (by linarith)
    have hGa := hGan w (by linarith)
    rw [meromorphicOrderAt_congr ((hΛloc w h1 h2 h3).filter_mono nhdsWithin_le_nhds)]
    have : (fun s => G s * L s) = G * L := rfl
    rw [this, meromorphicOrderAt_mul hGa.1.meromorphicAt hLa.meromorphicAt,
      hGa.1.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr hGa.2),
      hLa.meromorphicOrderAt_eq]
    simp
  -- constants
  have hT₂0 := abs_nonneg T₂
  have hT₃0 := abs_nonneg T₃
  have hT₂abs := le_abs_self T₂
  have hT₃abs := le_abs_self T₃
  set A : ℝ := |C₁| * (2 : ℝ) ^ M * |C₂| with hA
  have hA0 : 0 ≤ A := by positivity
  set P : ℝ := M + N with hP
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hP1 : 1 ≤ P := by linarith
  set KB : ℝ := Real.log (2 + A) / Real.log 2 + P with hKB
  set KL : ℝ := OAI.TwoPointCorrelations.mrtCharacterLogDerivativeConstant with hKL
  set KZ : ℝ := 1 / Real.log ((15 / 16) / (7 / 8)) with hKZ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2A : 0 ≤ Real.log (2 + A) := Real.log_nonneg (by linarith)
  have hKB0 : 0 ≤ KB := by positivity
  refine ⟨KG + (|KL| / 3 + |KZ|) * KB, |T₁| + |T₂| + |T₃| + |TG| + 10, by linarith, ?_⟩
  intro s hs1 hs2 hsT hΛs
  set t := s.im with ht
  have ht2 : 2 ≤ |t| := by linarith
  have htpos : 0 < |t| := by linarith
  have hlogt : Real.log 2 ≤ Real.log |t| := Real.log_le_log (by norm_num) ht2
  set s₀ : ℂ := 1 + (t : ℂ) * Complex.I with hs₀
  have hs₀re : s₀.re = 1 := by simp [s₀]
  have hs₀im : s₀.im = t := by simp [s₀]
  -- lower bound at s₀
  obtain ⟨hL0, hLinv⟩ := hinv t (by linarith)
  have hL0' : L s₀ ≠ 0 := hL0
  have hLs₀pos : 0 < ‖L s₀‖ := norm_pos_iff.mpr hL0'
  have h1le : 1 ≤ C₂ * |t| ^ N * ‖L s₀‖ := by
    have := hLinv
    rw [norm_inv] at this
    have h := (inv_le_iff_one_le_mul₀ hLs₀pos).mp this
    linarith [mul_comm (C₂ * |t| ^ N) ‖L s₀‖]
  -- the number B
  set B : ℝ := (2 + A) * |t| ^ P with hB
  have htP : 1 ≤ |t| ^ P := Real.one_le_rpow (by linarith) (by linarith)
  have hB2 : 2 ≤ B := by
    have : (2 + A) * 1 ≤ (2 + A) * |t| ^ P := mul_le_mul_of_nonneg_left htP (by linarith)
    linarith
  have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  have hlogB : Real.log B ≤ KB * Real.log |t| := by
    rw [hB, Real.log_mul (by linarith) (by positivity), Real.log_rpow htpos, hKB, add_mul]
    have : Real.log (2 + A) ≤ Real.log (2 + A) / Real.log 2 * Real.log |t| := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      exact mul_le_mul_of_nonneg_left hlogt hlog2A
    linarith
  -- re/im control near s₀
  have hreim : ∀ w : ℂ, |w.re - 1| ≤ ‖w - s₀‖ ∧ |w.im - t| ≤ ‖w - s₀‖ := by
    intro w
    have h1 := Complex.abs_re_le_norm (w - s₀)
    have h2 := Complex.abs_im_le_norm (w - s₀)
    rw [Complex.sub_re, hs₀re] at h1; rw [Complex.sub_im, hs₀im] at h2
    exact ⟨h1, h2⟩
  have himlow : ∀ w : ℂ, |w.im - t| ≤ 4 → |t| - 4 ≤ |w.im| := by
    intro w hw
    have := abs_add_le (t - w.im) w.im
    rw [sub_add_cancel, abs_sub_comm] at this; linarith
  have himup : ∀ w : ℂ, |w.im - t| ≤ 4 → |w.im| ≤ |t| + 4 := by
    intro w hw
    have := abs_add_le (w.im - t) t
    rw [sub_add_cancel] at this; linarith
  -- analyticity of L on the big disk
  have hAn : ∀ w, ‖w - s₀‖ ≤ 6 / 5 * 3 → AnalyticAt ℂ L w := by
    intro w hw
    obtain ⟨h1, h2⟩ := hreim w
    have h1' := abs_le.mp (h1.trans hw)
    have := himlow w (by linarith)
    exact hT₁ w (by linarith [h1'.1]) (by linarith [h1'.2]) (by linarith)
  -- growth bound on the disk
  have hbound : ∀ w, ‖w - s₀‖ ≤ 15 / 16 * 3 → ‖L w‖ ≤ B * ‖L s₀‖ := by
    intro w hw
    obtain ⟨h1, h2⟩ := hreim w
    have h1' := abs_le.mp (h1.trans hw)
    have hlow := himlow w (by linarith)
    have hup := himup w (by linarith)
    have hg := hgrowth w (by linarith [h1'.1]) (by linarith [h1'.2]) (by linarith)
    have hwim0 : 0 ≤ |w.im| := abs_nonneg _
    have hM0 : 0 ≤ M := hM.le
    have e1 : |w.im| ^ M ≤ (2 * |t|) ^ M := Real.rpow_le_rpow hwim0 (by linarith) hM0
    have e2 : (2 * |t|) ^ M = (2 : ℝ) ^ M * |t| ^ M := Real.mul_rpow (by norm_num) htpos.le
    have e3 : |t| ^ M * (|t| ^ N : ℝ) = |t| ^ P := by
      rw [hP, Real.rpow_add htpos, Real.rpow_natCast]
    have hC₂ : C₂ * |t| ^ N ≤ |C₂| * |t| ^ N :=
      mul_le_mul_of_nonneg_right (le_abs_self C₂) (by positivity)
    have step1 : ‖L w‖ ≤ |C₁| * ((2 : ℝ) ^ M * |t| ^ M) := by
      calc ‖L w‖ ≤ C₁ * |w.im| ^ M := hg
        _ ≤ |C₁| * |w.im| ^ M :=
            mul_le_mul_of_nonneg_right (le_abs_self C₁) (Real.rpow_nonneg hwim0 M)
        _ ≤ |C₁| * (2 * |t|) ^ M := mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
        _ = _ := by rw [e2]
    have hX0 : 0 ≤ |C₁| * ((2 : ℝ) ^ M * |t| ^ M) := by positivity
    calc ‖L w‖ ≤ |C₁| * ((2 : ℝ) ^ M * |t| ^ M) * 1 := by linarith
      _ ≤ |C₁| * ((2 : ℝ) ^ M * |t| ^ M) * (C₂ * |t| ^ N * ‖L s₀‖) :=
          mul_le_mul_of_nonneg_left h1le hX0
      _ ≤ |C₁| * ((2 : ℝ) ^ M * |t| ^ M) * (|C₂| * |t| ^ N * ‖L s₀‖) := by
          apply mul_le_mul_of_nonneg_left _ hX0
          exact mul_le_mul_of_nonneg_right hC₂ (norm_nonneg _)
      _ = A * (|t| ^ M * (|t| ^ N : ℝ)) * ‖L s₀‖ := by rw [hA]; ring
      _ = A * |t| ^ P * ‖L s₀‖ := by rw [e3]
      _ ≤ B * ‖L s₀‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [hB]
          have : 0 ≤ |t| ^ P := by positivity
          nlinarith
  obtain ⟨Z, hZmem, hZcount, hZlog⟩ :=
    Sol_MasulloGRH_completedHeckeLFunction_logDeriv_local_partial_fraction.landau_disk L s₀ 3 B (by norm_num) hAn hL0' hB2 hbound
  -- the point s
  have hs_near : ‖s - s₀‖ ≤ 3 / 4 * 3 := by
    have h := Sol_MasulloGRH_completedHeckeLFunction_logDeriv_local_partial_fraction.norm_le_re_im (s - s₀)
    rw [Complex.sub_re, Complex.sub_im, hs₀re, hs₀im, ← ht, sub_self, abs_zero] at h
    have : |s.re - 1| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    linarith
  have hsT₄ : T₄ < |s.im| := by rw [← ht]; linarith
  have hΛs_eq : Λ s = G s * L s := (hΛloc s (by linarith) (by linarith) hsT₄).eq_of_nhds
  have hLs0 : L s ≠ 0 := by intro h; apply hΛs; rw [hΛs_eq, h, mul_zero]
  have hGs0 : G s ≠ 0 := by intro h; apply hΛs; rw [hΛs_eq, h, zero_mul]
  have hLsa : AnalyticAt ℂ L s := hT₁ s (by linarith) (by linarith) (by linarith)
  have hGsa : AnalyticAt ℂ G s := (hGan s (by rw [← ht]; linarith)).1
  have hlogΛ : logDeriv Λ s = logDeriv G s + logDeriv L s := by
    rw [(logDeriv_congr_nhds (hΛloc s (by linarith) (by linarith) hsT₄)).eq_of_nhds]
    exact logDeriv_mul s hGs0 hLs0 hGsa.differentiableAt hLsa.differentiableAt
  have hLlog := hZlog s hs_near hLs0
  have hGb := hGlog s hs1 hs2 (by rw [← ht]; linarith)
  -- the window
  set Zw := Z.filter (fun ρ => |ρ.im - t| ≤ 1) with hZw
  have hW : {ρ : ℂ | 0 < meromorphicOrderAt Λ ρ ∧ |ρ.im - s.im| ≤ 1} = (↑Zw : Set ℂ) := by
    ext ρ
    simp only [Set.mem_ofPred_eq, hZw, Finset.coe_filter, hZmem, ← ht]
    constructor
    · rintro ⟨hpos, hp⟩
      obtain ⟨hre0, hre1⟩ := Sol_MasulloGRH_completedHeckeLFunction_logDeriv_local_partial_fraction.zeros_strip χ ρ hpos
      have hlow := himlow ρ (by linarith)
      have hρ := hord ρ (by linarith) (by linarith) (by linarith)
      rw [hρ, Sol_MasulloGRH_completedHeckeLFunction_logDeriv_local_partial_fraction.map_pos] at hpos
      have hLρ : L ρ = 0 := by
        by_contra hne
        exact hpos (analyticOrderAt_eq_zero.mpr (Or.inr hne))
      refine ⟨⟨?_, hLρ⟩, hp⟩
      have h := Sol_MasulloGRH_completedHeckeLFunction_logDeriv_local_partial_fraction.norm_le_re_im (ρ - s₀)
      rw [Complex.sub_re, Complex.sub_im, hs₀re, hs₀im] at h
      have : |ρ.re - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      linarith
    · rintro ⟨⟨hnorm, hLρ⟩, hp⟩
      obtain ⟨h1, h2⟩ := hreim ρ
      have h1' := abs_le.mp (h1.trans hnorm)
      have hlow := himlow ρ (by linarith)
      have hρ := hord ρ (by linarith [h1'.1]) (by linarith [h1'.2]) (by linarith)
      have hLa : AnalyticAt ℂ L ρ := hT₁ ρ (by linarith [h1'.1]) (by linarith [h1'.2]) (by linarith)
      refine ⟨?_, hp⟩
      rw [hρ, Sol_MasulloGRH_completedHeckeLFunction_logDeriv_local_partial_fraction.map_pos]
      intro h0
      rcases analyticOrderAt_eq_zero.mp h0 with h | h
      · exact h hLa
      · exact h hLρ
  have hsummand : ∀ ρ ∈ Zw, (((meromorphicOrderAt Λ ρ).untop₀ : ℤ) : ℂ) / (s - ρ) =
      (analyticOrderNatAt L ρ : ℂ) / (s - ρ) := by
    intro ρ hρ
    rw [hZw, Finset.mem_filter, hZmem] at hρ
    obtain ⟨⟨hnorm, -⟩, hp⟩ := hρ
    obtain ⟨h1, h2⟩ := hreim ρ
    have h1' := abs_le.mp (h1.trans hnorm)
    have hlow := himlow ρ (by linarith)
    rw [hord ρ (by linarith [h1'.1]) (by linarith [h1'.2]) (by linarith), Sol_MasulloGRH_completedHeckeLFunction_logDeriv_local_partial_fraction.untop₀_map,
      analyticOrderNatAt]
    push_cast; rfl
  have hfin : ∑ᶠ ρ ∈ {ρ : ℂ | 0 < meromorphicOrderAt Λ ρ ∧ |ρ.im - s.im| ≤ 1},
      (((meromorphicOrderAt Λ ρ).untop₀ : ℤ) : ℂ) / (s - ρ) =
      ∑ ρ ∈ Zw, (analyticOrderNatAt L ρ : ℂ) / (s - ρ) := by
    rw [hW, finsum_mem_coe_finset]
    exact Finset.sum_congr rfl hsummand
  rw [hfin, hlogΛ]
  -- split the Landau sum
  have hsplit := Finset.sum_filter_add_sum_filter_not Z (fun ρ => |ρ.im - t| ≤ 1)
    (fun ρ => (analyticOrderNatAt L ρ : ℂ) / (s - ρ))
  set Zo := Z.filter (fun ρ => ¬ |ρ.im - t| ≤ 1) with hZo
  have hrest : ‖∑ ρ ∈ Zo, (analyticOrderNatAt L ρ : ℂ) / (s - ρ)‖ ≤ KZ * Real.log B := by
    calc ‖∑ ρ ∈ Zo, (analyticOrderNatAt L ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ Zo, ‖(analyticOrderNatAt L ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Zo, (analyticOrderNatAt L ρ : ℝ) := by
          apply Finset.sum_le_sum
          intro ρ hρ
          rw [hZo, Finset.mem_filter] at hρ
          have hfar : 1 < ‖s - ρ‖ := by
            have h := Complex.abs_im_le_norm (s - ρ)
            rw [Complex.sub_im, ← ht, abs_sub_comm] at h
            linarith [not_le.mp hρ.2]
          rw [norm_div, Complex.norm_natCast]
          rw [div_le_iff₀ (by linarith)]
          have : (0 : ℝ) ≤ (analyticOrderNatAt L ρ : ℝ) := Nat.cast_nonneg _
          nlinarith
      _ ≤ ∑ ρ ∈ Z, (analyticOrderNatAt L ρ : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ KZ * Real.log B := hZcount
  have hdecomp : logDeriv G s + logDeriv L s - ∑ ρ ∈ Zw, (analyticOrderNatAt L ρ : ℂ) / (s - ρ) =
      logDeriv G s + (logDeriv L s - ∑ ρ ∈ Z, (analyticOrderNatAt L ρ : ℂ) / (s - ρ)) +
        ∑ ρ ∈ Zo, (analyticOrderNatAt L ρ : ℂ) / (s - ρ) := by
    rw [← hsplit]; ring
  rw [hdecomp]
  have hKL : KL / 3 * Real.log B ≤ |KL| / 3 * (KB * Real.log |t|) := by
    have : KL / 3 ≤ |KL| / 3 := by have := le_abs_self KL; linarith
    calc KL / 3 * Real.log B ≤ |KL| / 3 * Real.log B :=
          mul_le_mul_of_nonneg_right this hlogB0
      _ ≤ |KL| / 3 * (KB * Real.log |t|) :=
          mul_le_mul_of_nonneg_left hlogB (by positivity)
  have hKZ : KZ * Real.log B ≤ |KZ| * (KB * Real.log |t|) := by
    calc KZ * Real.log B ≤ |KZ| * Real.log B :=
          mul_le_mul_of_nonneg_right (le_abs_self KZ) hlogB0
      _ ≤ |KZ| * (KB * Real.log |t|) := mul_le_mul_of_nonneg_left hlogB (abs_nonneg _)
  calc ‖logDeriv G s + (logDeriv L s - ∑ ρ ∈ Z, (analyticOrderNatAt L ρ : ℂ) / (s - ρ)) +
        ∑ ρ ∈ Zo, (analyticOrderNatAt L ρ : ℂ) / (s - ρ)‖
      ≤ ‖logDeriv G s‖ + ‖logDeriv L s - ∑ ρ ∈ Z, (analyticOrderNatAt L ρ : ℂ) / (s - ρ)‖ +
        ‖∑ ρ ∈ Zo, (analyticOrderNatAt L ρ : ℂ) / (s - ρ)‖ := norm_add₃_le
    _ ≤ KG * Real.log |t| + KL / 3 * Real.log B + KZ * Real.log B := by
        exact add_le_add (add_le_add hGb hLlog) hrest
    _ ≤ KG * Real.log |t| + |KL| / 3 * (KB * Real.log |t|) + |KZ| * (KB * Real.log |t|) := by
        linarith
    _ = (KG + (|KL| / 3 + |KZ|) * KB) * Real.log |t| := by ring
