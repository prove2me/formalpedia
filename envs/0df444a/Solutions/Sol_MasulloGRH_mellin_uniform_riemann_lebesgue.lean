-- Prove2me | solution 1 for MasulloGRH.mellin_uniform_riemann_lebesgue
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T04:32:02.860684+00:00
-- url     : https://prove2.me/submissions/14158155-233a-44ab-b678-6684500204b2

import Definitions.Def_MasulloGRH_MellinRpos
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.MellinInversion
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter Topology Asymptotics

namespace MasulloGRH

private theorem nf_log_mellin (f : ℝ → ℂ) (s : ℂ) :
    mellin f s = ∫ x : ℝ, Complex.exp (s * x) * f (Real.exp x) := by
  rw [mellin, ← Real.range_exp, ← Set.image_univ,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
    setIntegral_univ]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [abs_of_pos (Real.exp_pos _), Complex.real_smul, smul_eq_mul, ← mul_assoc,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  ring

private theorem nf_strip_analytic (a b : ℝ) (hab : a < b) (ϕ : ℝ → ℂ)
    (hϕ : IsSchwartzRpos ϕ)
    (h : ∀ σ : ℝ, a ≤ σ → σ ≤ b → IsSchwartzRpos (powMul σ ϕ)) :
    ContinuousOn (mellin ϕ) (closedStrip a b) ∧
    DifferentiableOn ℂ (mellin ϕ) (openStrip a b) ∧
    ∃ D : ℝ, ∀ z ∈ closedStrip a b, ‖mellin ϕ z‖ ≤ D := by
  obtain ⟨F, hF⟩ := hϕ
  obtain ⟨A, hA⟩ := h a le_rfl hab.le
  obtain ⟨B, hB⟩ := h b hab.le le_rfl
  let I (s : ℂ) (x : ℝ) := Complex.exp (s * x) * F x
  have hI (s : ℂ) : mellin ϕ s = ∫ x, I s x := by
    simp only [nf_log_mellin, I, hF]
  have weight (u : ℝ) (G : SchwartzMap ℝ ℂ) (hG : ∀ x : ℝ, G x = powMul u ϕ (Real.exp x)) (x : ℝ) :
      ‖G x‖ = Real.exp (u*x)*‖F x‖ := by
    rw [hG, powMul, hF, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos (Real.exp_pos _) _), Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm x u]
  have major (s : ℂ) (hs : s ∈ closedStrip a b) (x : ℝ) :
      ‖I s x‖ ≤ ‖A x‖ + ‖B x‖ := by
    rw [show ‖I s x‖ = Real.exp (s.re*x)*‖F x‖ by simp [I, Complex.norm_exp, Complex.mul_re],
      weight a A hA, weight b B hB]
    obtain hx | hx := le_total x 0
    · exact le_add_of_le_of_nonneg (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hs.1 hx)) (norm_nonneg _)) (by positivity)
    · apply le_add_of_nonneg_of_le (by positivity)
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs.2 hx)) (norm_nonneg _)
  have hmajor : Integrable (fun x : ℝ => ‖A x‖ + ‖B x‖) := A.integrable.norm.add B.integrable.norm
  have measurable (s : ℂ) : AEStronglyMeasurable (I s) volume :=
    ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul F.continuous).aestronglyMeasurable
  have hc : ContinuousOn (fun s => ∫ x, I s x) (closedStrip a b) :=
    continuousOn_of_dominated (fun s _ => measurable s)
      (fun s hs => .of_forall (major s hs)) hmajor
      (.of_forall (fun x => ((Complex.continuous_exp.comp (continuous_id.mul continuous_const)).mul continuous_const).continuousOn))
  refine ⟨hc.congr (fun z _ => hI z), ?_, ?_⟩
  · have hf : ContinuousOn ϕ (Ioi 0) := by
      apply (F.continuous.comp_continuousOn (Real.continuousOn_log.mono (by
        intro t ht
        exact (show 0 < t from ht).ne'))).congr
      intro t ht
      simp [hF, Real.exp_log (show 0 < t from ht)]
    have point (u : ℝ) (G : SchwartzMap ℝ ℂ) (hG : ∀ x : ℝ, G x = powMul u ϕ (Real.exp x)) (t : ℝ) (ht : 0 < t) :
        ‖ϕ t‖ ≤ (SchwartzMap.seminorm ℝ 0 0 G) * ‖t ^ (-u)‖ := by
      have hsup := G.norm_le_seminorm ℝ (Real.log t)
      rw [hG, Real.exp_log ht, powMul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos ht _)] at hsup
      rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht _), Real.rpow_neg ht.le, ← div_eq_mul_inv,
        le_div_iff₀ (Real.rpow_pos_of_pos ht _)]
      simpa only [mul_comm] using hsup
    intro z hz
    exact (mellin_differentiableAt_of_isBigO_rpow (hf.locallyIntegrableOn measurableSet_Ioi)
      (isBigO_iff.mpr ⟨_, (eventually_gt_atTop (0:ℝ)).mono (fun t ht => point b B hB t ht)⟩)
      hz.2 (isBigO_iff.mpr ⟨_, eventually_mem_nhdsWithin.mono (fun t ht => point a A hA t ht)⟩) hz.1).differentiableWithinAt
  · refine ⟨∫ x : ℝ, ‖A x‖ + ‖B x‖, ?_⟩
    intro z hz
    rw [hI z]
    exact norm_integral_le_of_norm_le hmajor (.of_forall (major z hz))

end MasulloGRH
namespace MasulloGRH

open Complex FourierTransform

private theorem nf_mellin_slice (ϕ : ℝ → ℂ) (σ : ℝ)
    (hσ : IsSchwartzRpos (powMul σ ϕ)) :
    ∃ g : SchwartzMap ℝ ℂ, ∀ y : ℝ, g y = mellin ϕ (σ + y * Complex.I) := by
  obtain ⟨ψ,hψ⟩ := hσ
  let negEquiv : ℝ ≃L[ℝ] ℝ := (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv
  let reflected : SchwartzMap ℝ ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ negEquiv ψ
  let dilation := ContinuousLinearEquiv.unitsEquivAut ℝ
    (Units.mk0 (2 * Real.pi)⁻¹ (by positivity))
  let F : SchwartzMap ℝ ℂ := 𝓕 reflected
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ dilation F, ?_⟩
  intro y
  have hfun : (reflected : ℝ → ℂ) =
      (fun u : ℝ => Real.exp (-σ * u) • ϕ (Real.exp (-u))) := by
    funext u
    change ψ (-u) = _
    rw [hψ, powMul, Complex.real_smul, ← Real.exp_mul]
    rw [show -u * σ = -σ * u by ring]
  change F (y * (2 * Real.pi)⁻¹) = _
  rw [mellin_eq_fourier]
  change (𝓕 (reflected : ℝ → ℂ)) (y * (2 * Real.pi)⁻¹) = _
  rw [hfun]
  simp [div_eq_mul_inv]
end MasulloGRH

open Set Filter Complex Asymptotics
open scoped Topology

private theorem nf_uniform_boundary (F : ℂ → ℂ) (x : ℝ) (g : SchwartzMap ℝ ℂ)
    (hg : ∀ y : ℝ, g y = F (x + y * Complex.I)) (N : ℕ) :
    ∃ B : ℝ, ∀ z : ℂ, z.re = x → ‖z ^ N * F z‖ ≤ B := by
  let A : ℝ := |x| + 1
  let S : ℝ := 2 ^ N * (Finset.Iic (N, (0 : ℕ))).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g
  refine ⟨A ^ N * S, ?_⟩
  intro z hz
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hnorm : ‖z‖ ≤ A * (1 + |z.im|) := by
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ A * (1 + |z.im|) := by
        rw [hz]
        dsimp [A]
        nlinarith [mul_nonneg (abs_nonneg x) (abs_nonneg z.im)]
  have hgz : F z = g z.im := by
    rw [hg, ← hz, z.re_add_im]
  have hS : (1 + |z.im|)^N * ‖g z.im‖ ≤ S := by
    simpa [S, Real.norm_eq_abs] using
      (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0)) (k := N) (n := 0)
        le_rfl le_rfl g z.im)
  calc
    ‖z ^ N * F z‖ = ‖z‖ ^ N * ‖g z.im‖ := by rw [norm_mul, norm_pow, hgz]
    _ ≤ (A * (1 + |z.im|)) ^ N * ‖g z.im‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hnorm _) (norm_nonneg _)
    _ = A ^ N * ((1 + |z.im|)^N * ‖g z.im‖) := by rw [mul_pow, mul_assoc]
    _ ≤ A ^ N * S := mul_le_mul_of_nonneg_left hS (pow_nonneg hA _)

private theorem nf_uniform_strip {a b : ℝ} (hab : a < b) (F : ℂ → ℂ)
    (hd : DifferentiableOn ℂ F (Complex.re ⁻¹' Ioo a b))
    (hc : ContinuousOn F (Complex.re ⁻¹' Icc a b))
    (hbounded : ∃ M : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖F z‖ ≤ M)
    (ha : ∃ g : SchwartzMap ℝ ℂ, ∀ y : ℝ, g y = F (a + y * Complex.I))
    (hb : ∃ g : SchwartzMap ℝ ℂ, ∀ y : ℝ, g y = F (b + y * Complex.I)) :
    ∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, 0 < C ∧ ∃ Y : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      Y ≤ |z.im| → ‖F z‖ ≤ C / |z.im| ^ N := by
  rintro N -
  obtain ⟨M,hM⟩ := hbounded
  obtain ⟨ga,hga⟩ := ha
  obtain ⟨gb,hgb⟩ := hb
  obtain ⟨Ba,ha'⟩ := nf_uniform_boundary F a ga hga N
  obtain ⟨Bb,hb'⟩ := nf_uniform_boundary F b gb hgb N
  let C := max 1 (max Ba Bb)
  have hdcl : DiffContOnCl ℂ F (Complex.re ⁻¹' Ioo a b) := by
    refine ⟨hd, ?_⟩
    rwa [Complex.closure_preimage_re, closure_Ioo hab.ne]
  let G : ℂ → ℂ := fun z => z^N * F z
  have hdG : DiffContOnCl ℂ G (Complex.re ⁻¹' Ioo a b) :=
    ⟨(differentiableOn_id.pow N).mul hd, (continuousOn_id.pow N).mul hdcl.2⟩
  let c := (Real.pi / (b - a)) / 2
  have hpi : 0 < Real.pi / (b-a) := div_pos Real.pi_pos (sub_pos.mpr hab)
  have hc0 : 0 < c := half_pos hpi
  let H := |a| + |b|
  have growth :
      G =O[comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo a b)]
        fun z => Real.exp (c⁻¹ * Real.exp (c * |z.im|)) := by
    apply Asymptotics.IsBigO.of_bound ((N.factorial : ℝ) * Real.exp H * |M|)
    filter_upwards [Filter.Eventually.filter_mono inf_le_right
      (Filter.eventually_principal.mpr (Set.Subset.rfl (s := Complex.re ⁻¹' Ioo a b)))] with z hz
    have h' : a < z.re ∧ z.re < b := hz
    have hreal : |z.re| ≤ H := by
      apply abs_le.mpr
      dsimp [H]
      constructor <;> linarith [neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b]
    have hyn : |z.im| ≤ c⁻¹ * Real.exp (c * |z.im|) := by
      have he := Real.add_one_le_exp (c * |z.im|)
      calc
        |z.im| = c⁻¹ * (c * |z.im|) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hc0.le)
    have hfactor : ‖z‖ ^ N ≤ Real.exp ‖z‖ * (N.factorial : ℝ) :=
      (div_le_iff₀ (by positivity)).mp (Real.pow_div_factorial_le_exp ‖z‖ (norm_nonneg z) N)
    have hez : Real.exp ‖z‖ ≤ Real.exp H * Real.exp (c⁻¹ * Real.exp (c * |z.im|)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr ((Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add hreal hyn))
    simp only [G, norm_mul, norm_pow, Real.norm_eq_abs, Real.abs_exp]
    calc
      ‖z‖ ^ N * ‖F z‖ ≤ (Real.exp ‖z‖ * (N.factorial : ℝ)) * |M| :=
        mul_le_mul hfactor ((hM z h'.1.le h'.2.le).trans (le_abs_self _)) (norm_nonneg _) (by positivity)
      _ ≤ (Real.exp H * Real.exp (c⁻¹ * Real.exp (c * |z.im|)) * (N.factorial : ℝ)) * |M| := by gcongr
      _ = _ := by ring
  refine ⟨C, lt_of_lt_of_le zero_lt_one (le_max_left ..), 1, ?_⟩
  intro z hza hzb hy
  have hpos : 0 < |z.im| := lt_of_lt_of_le zero_lt_one hy
  have hest := PhragmenLindelof.vertical_strip hdG ⟨c, half_lt_self hpi, c⁻¹, growth⟩
    (C := C) (fun z h => (ha' z h).trans ((le_max_left ..).trans (le_max_right ..)))
    (fun z h => (hb' z h).trans ((le_max_right ..).trans (le_max_right ..))) hza hzb
  apply (le_div_iff₀ (pow_pos hpos _)).mpr
  rw [mul_comm]
  calc
    |z.im| ^ N * ‖F z‖ ≤ ‖z‖ ^ N * ‖F z‖ := by gcongr; exact Complex.abs_im_le_norm z
    _ = ‖G z‖ := by simp [G]
    _ ≤ C := hest
open MasulloGRH

theorem solution (a b : ℝ) (hab : a < b) (ϕ : ℝ → ℂ)
    (hϕ : IsSchwartzRpos ϕ) (h : ∀ σ : ℝ, a ≤ σ → σ ≤ b → IsSchwartzRpos (powMul σ ϕ)) :
    ContinuousOn (mellin ϕ) (closedStrip a b) ∧
    (∀ σ : ℝ, a ≤ σ → σ ≤ b →
      ∃ g : SchwartzMap ℝ ℂ, ∀ y : ℝ, g y = mellin ϕ (σ + y * Complex.I)) ∧
    DifferentiableOn ℂ (mellin ϕ) (openStrip a b) ∧
    (∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, 0 < C ∧ ∃ Y : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → Y ≤ |s.im| →
      ‖mellin ϕ s‖ ≤ C / |s.im| ^ N) := by
  obtain ⟨hc, hd, M, hM⟩ := nf_strip_analytic a b hab ϕ hϕ h
  have H σ (h₁ : a ≤ σ) (h₂ : σ ≤ b) := nf_mellin_slice ϕ σ (h σ h₁ h₂)
  exact ⟨hc,H,hd,nf_uniform_strip hab (mellin ϕ) hd hc
    ⟨M,fun z hz₁ hz₂ => hM z ⟨hz₁,hz₂⟩⟩ (H a le_rfl hab.le) (H b hab.le le_rfl)⟩