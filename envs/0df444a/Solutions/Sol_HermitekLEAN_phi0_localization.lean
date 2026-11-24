-- Prove2me | solution 1 for HermitekLEAN.phi0_localization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:41.516076+00:00
-- url     : https://prove2.me/submissions/cc58320b-8c41-4a30-b95b-d96ab3fc5593

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LaplaceFactorial
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_MissingMathlib
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_BasisLocalization
public import Theorems.Thm_HermiteLEAN_polynomial_times_gaussian_le_gaussian
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_phi_polar
public import Theorems.Thm_HermitekLEAN_qkn_explicit
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open Complex MeasureTheory Real Finset
noncomputable section
namespace HermitekLEAN
private theorem hermiteSeries_single (k n : ℕ) :
    hermiteSeries k (fun m : ℕ => if m = n then (1 : ℂ) else 0) = Phi k n := by
  funext z
  unfold hermiteSeries
  simp only [ite_mul, one_mul, zero_mul, tsum_ite_eq]
private theorem qkn_zero (k : ℕ) {r : ℝ} (hr : 0 < r) : qkn k 0 r = 1 := by simp [qkn_explicit hr]
private lemma fourier_mk_eq_exp
    (n : ℤ)
    (θ : ℝ) :
    (fourier n (QuotientAddGroup.mk θ : Circle) : ℂ) =
      Complex.exp (Complex.I * (n : ℂ) * θ) := by
  rw [fourier_coe_apply]
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * θ / (HermiteLEAN.T : ℂ) =
        Complex.I * (n : ℂ) * θ := by
    simp [HermiteLEAN.T, mul_assoc]
    field_simp [Real.pi_ne_zero]
  rw [harg]
private lemma circlePoint_mk_eq_polarCoord_symm
    (r θ : ℝ) :
    circlePoint r (QuotientAddGroup.mk θ : Circle) = Complex.polarCoord.symm (r, θ) := by
  change ((r : ℂ) * (fourier (1 : ℤ) (QuotientAddGroup.mk θ : Circle) : ℂ)) = _
  rw [fourier_mk_eq_exp]
  have hexp :
      Complex.exp (Complex.I * (((1 : ℤ) : ℂ)) * (θ : ℂ)) =
        Complex.exp ((θ : ℂ) * Complex.I) := by
    congr 1
    ring
  rw [hexp, Complex.polarCoord_symm_apply, Complex.exp_mul_I]
  simp [mul_comm]
private lemma setIntegral_radialStrip_eq_intervalIntegral (j : ℕ) (f : ℝ → ℝ) :
    (∫ r in Set.Ioi (0 : ℝ) ∩ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ)), f r)
      = ∫ r in (j : ℝ)..(((j + 1 : ℕ) : ℝ)), f r := by
  set strip : Set ℝ := Set.Ioi (0 : ℝ) ∩ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ)) with hstrip
  have hIoiIco_ae : strip =ᵐ[volume] Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ)) := by
    filter_upwards [Ioi_ae_eq_Ici (a := (0 : ℝ)) (μ := volume)] with x hx
    apply propext
    constructor
    · intro h
      exact h.2
    · intro h
      refine ⟨hx.mpr ?_, h⟩
      exact le_trans (show (0 : ℝ) ≤ (j : ℝ) by exact_mod_cast Nat.zero_le j) h.1
  rw [MeasureTheory.setIntegral_congr_set hIoiIco_ae,
    intervalIntegral.integral_of_le
      (show (j : ℝ) ≤ (((j + 1 : ℕ) : ℝ)) by exact_mod_cast Nat.le_succ j)]
  exact
    (MeasureTheory.setIntegral_congr_set
      (f := f) (μ := volume)
      (Ico_ae_eq_Ioc (a := (j : ℝ)) (b := (((j + 1 : ℕ) : ℝ)))))
private theorem phi0_support_zero (k : ℕ) :
    ∃ g : ℕ → ℂ,
      phi0 k = hermiteSeries k g ∧
      (∀ n : ℕ, 0 < n → g n = 0) ∧
      (∀ r : ℝ, 0 < r → ∀ t : Circle,
        phi0 k (circlePoint r t) = circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ) * g 0) := by
  let g : ℕ → ℂ := fun n => if n = 0 then 1 else 0
  refine ⟨g, ?_, ?_, ?_⟩
  · exact (hermiteSeries_single k 0).symm
  · intro n hn
    simp [g, Nat.ne_of_gt hn]
  · intro r hr t
    rw [phi0, phi_polar (k := k) (n := 0) hr t, qkn_zero k hr]
    simp [g]
private theorem phi0_polar_norm_formula
    (k : ℕ)
    {g : ℕ → ℂ}
    (hpolar : ∀ r : ℝ, 0 < r → ∀ t : Circle,
      phi0 k (circlePoint r t) = circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ) * g 0)
    {r θ : ℝ}
    (hr : 0 < r) :
    ‖phi0 k (Complex.polarCoord.symm (r, θ))‖ ^ 2 *
        Real.exp (-‖Complex.polarCoord.symm (r, θ)‖ ^ 2) =
      (((r ^ k / Real.sqrt (Nat.factorial k : ℝ)) ^ 2) * ‖g 0‖ ^ 2) * Real.exp (-r ^ 2) := by
  have hcircle : circlePoint r (QuotientAddGroup.mk θ : Circle) = Complex.polarCoord.symm (r, θ) :=
    circlePoint_mk_eq_polarCoord_symm r θ
  rw [← hcircle, hpolar r hr (QuotientAddGroup.mk θ : Circle)]
  unfold circleLeadingFactor
  rw [norm_mul, norm_mul]
  have hsqrt_nonneg : 0 ≤ Real.sqrt (Nat.factorial k : ℝ) := Real.sqrt_nonneg _
  have hnorm : ‖circlePoint r (QuotientAddGroup.mk θ : Circle)‖ = r := by
    rw [hcircle, Complex.norm_polarCoord_symm, abs_of_pos hr]
  rw [hnorm]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsqrt_nonneg, abs_of_pos hr,
    fourier_apply, Circle.norm_coe]
  ring
private theorem continuous_phi0AnnulusIntegrand (k : ℕ) (g0normsq : ℝ) :
    Continuous (phi0AnnulusIntegrand k g0normsq) := by
  unfold phi0AnnulusIntegrand
  continuity
private theorem integrableOn_annulus_polar_phi0
    (k j : ℕ)
    (g0normsq : ℝ) :
    IntegrableOn
      (fun p : ℝ × ℝ => phi0AnnulusIntegrand k g0normsq p.1)
      ((Set.Ioi (0 : ℝ) ∩ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ))) ×ˢ Set.Ioo (-Real.pi) Real.pi)
      volume := by
  let sclosed : Set (ℝ × ℝ) :=
    Set.Icc (0 : ℝ) (((j + 1 : ℕ) : ℝ)) ×ˢ Set.Icc (-Real.pi) Real.pi
  have hcompact : IsCompact sclosed := isCompact_Icc.prod isCompact_Icc
  have hbase :
      IntegrableOn (fun p : ℝ × ℝ => phi0AnnulusIntegrand k g0normsq p.1) sclosed volume := by
    have hcont : Continuous (fun p : ℝ × ℝ => phi0AnnulusIntegrand k g0normsq p.1) :=
      (continuous_phi0AnnulusIntegrand k g0normsq).comp continuous_fst
    exact hcont.continuousOn.integrableOn_compact hcompact
  refine hbase.mono_set ?_
  intro p hp
  rcases hp with ⟨⟨hp0, hpj⟩, hpθ⟩
  refine ⟨?_, ?_⟩
  · refine ⟨le_of_lt hp0, hpj.2.le⟩
  · exact ⟨le_of_lt hpθ.1, le_of_lt hpθ.2⟩
private theorem annulusIntegralSq_phi0_eq
    (k j : ℕ)
    {g : ℕ → ℂ}
    (hpolar : ∀ r : ℝ, 0 < r → ∀ t : Circle,
      phi0 k (circlePoint r t) = circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ) * g 0) :
    annulusIntegralSq (phi0 k) j =
      2 * ∫ r in (j : ℝ)..(((j + 1 : ℕ) : ℝ)), phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r := by
  let F : ℂ → ℝ := fun z => ‖phi0 k z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
  have hannulus_meas : MeasurableSet (annulus j) := by
    refine (measurableSet_le measurable_const measurable_norm).inter ?_
    exact measurableSet_lt measurable_norm measurable_const
  unfold HermitekLEAN.annulusIntegralSq HermiteLEAN.annulusIntegralSq
  rw [show (∫ z in annulus j, F z ∂(volume : Measure ℂ)) =
      ∫ z : ℂ, Set.indicator (annulus j) F z ∂(volume : Measure ℂ) by
      symm
      rw [MeasureTheory.integral_indicator hannulus_meas]]
  rw [← Complex.integral_comp_polarCoord_symm (fun z : ℂ => Set.indicator (annulus j) F z)]
  have hpolar_rw :
      (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        p.1 • Set.indicator (annulus j) F (Complex.polarCoord.symm p))
        =
      ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        Set.indicator
          ((Set.Ioi (0 : ℝ) ∩ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ))) ×ˢ
            Set.Ioo (-Real.pi) Real.pi)
          (fun p : ℝ × ℝ => phi0AnnulusIntegrand k (‖g 0‖ ^ 2) p.1) p := by
    apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    rcases p with ⟨r, θ⟩
    rcases hp with ⟨hrpos, hθ⟩
    have hrpos' : 0 < r := by simpa only [Set.mem_Ioi] using hrpos
    by_cases hrj : r ∈ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ))
    · have hann :
          Complex.polarCoord.symm (r, θ) ∈ annulus j := by
        change (j : ℝ) ≤ ‖Complex.polarCoord.symm (r, θ)‖ ∧
            ‖Complex.polarCoord.symm (r, θ)‖ < (((j + 1 : ℕ) : ℝ))
        rw [Complex.norm_polarCoord_symm, abs_of_pos hrpos']
        exact hrj
      change
        r * Set.indicator (annulus j) F (Complex.polarCoord.symm (r, θ)) = _
      rw [Set.indicator_of_mem hann,
        Set.indicator_of_mem (show
          (r, θ) ∈
            (Set.Ioi (0 : ℝ) ∩ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ))) ×ˢ
              Set.Ioo (-Real.pi) Real.pi from by
            exact ⟨⟨hrpos, hrj⟩, hθ⟩)]
      have hFpolar :
          F (Complex.polarCoord.symm (r, θ))
            =
          (((r ^ k / Real.sqrt (Nat.factorial k : ℝ)) ^ 2) * ‖g 0‖ ^ 2) * Real.exp (-r ^ 2) := by
        dsimp [F]
        exact phi0_polar_norm_formula k hpolar hrpos'
      rw [hFpolar]
      simp [phi0AnnulusIntegrand, mul_left_comm, mul_comm]
    · have hann :
          Complex.polarCoord.symm (r, θ) ∉ annulus j := by
        intro hz
        apply hrj
        change (j : ℝ) ≤ ‖Complex.polarCoord.symm (r, θ)‖ ∧
            ‖Complex.polarCoord.symm (r, θ)‖ < (((j + 1 : ℕ) : ℝ)) at hz
        rw [Complex.norm_polarCoord_symm, abs_of_pos hrpos'] at hz
        exact hz
      simp_all only [fourier_apply, neg_smul, natCast_zsmul, Set.mem_Ioi, Set.mem_Ioo, Nat.cast_add,
        Nat.cast_one, Set.mem_Ico, not_and, not_lt, Complex.polarCoord_symm_apply, ofReal_cos,
        ofReal_sin, not_false_eq_true, Set.indicator_of_notMem, smul_eq_mul, mul_zero, Set.mem_prod,
        Set.mem_inter_iff, true_and, and_self, and_true, implies_true]
  change
    (1 / Real.pi) *
        ∫ p in Complex.polarCoord.target,
          p.1 • Set.indicator (annulus j) F (Complex.polarCoord.symm p)
      =
      2 * ∫ r in (j : ℝ)..(((j + 1 : ℕ) : ℝ)), phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r
  rw [Complex.polarCoord_target, hpolar_rw]
  rw [MeasureTheory.integral_indicator
    ((measurableSet_Ioi.inter measurableSet_Ico).prod measurableSet_Ioo)]
  rw [Measure.restrict_restrict
    ((measurableSet_Ioi.inter measurableSet_Ico).prod measurableSet_Ioo)]
  have hstrip :
      ((Set.Ioi (0 : ℝ) ∩ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ))) ×ˢ
          Set.Ioo (-Real.pi) Real.pi) ∩
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi)
        =
      (Set.Ioi (0 : ℝ) ∩ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ))) ×ˢ
        Set.Ioo (-Real.pi) Real.pi := by
    ext p
    simp_all only [fourier_apply, neg_smul, natCast_zsmul, Complex.polarCoord_symm_apply,
      ofReal_cos, ofReal_sin, smul_eq_mul, Nat.cast_add, Nat.cast_one, Set.mem_inter_iff,
      Set.mem_prod, Set.mem_Ioi, Set.mem_Ico, Set.mem_Ioo, and_iff_left_iff_imp, and_self,
      implies_true]
  rw [hstrip,
    show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ,
    setIntegral_prod _ (integrableOn_annulus_polar_phi0 k j (‖g 0‖ ^ 2))]
  have inner_eq :
      ∀ r : ℝ,
        (∫ θ in Set.Ioo (-Real.pi) Real.pi, phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r)
          =
        T * phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r := by
    intro r
    have hvol : volume (Set.Ioo (-Real.pi) Real.pi) = ENNReal.ofReal (2 * Real.pi) := by
      rw [Real.volume_Ioo]
      congr 1
      ring
    have hμ :
        (volume.restrict (Set.Ioo (-Real.pi) Real.pi)).real Set.univ = 2 * Real.pi := by
      rw [MeasureTheory.measureReal_restrict_apply_univ,
        MeasureTheory.Measure.real, hvol, ENNReal.toReal_ofReal]
      positivity
    rw [MeasureTheory.integral_const, hμ, smul_eq_mul]
    have hT : T = 2 * Real.pi := by rfl
    rw [hT]
  simp_rw [inner_eq]
  rw [MeasureTheory.integral_const_mul]
  have hT_eq : (1 / Real.pi) * T = 2 := by
    rw [show T = 2 * Real.pi by rfl]
    field_simp
  let srad : Set ℝ := Set.Ioi (0 : ℝ) ∩ Set.Ico (j : ℝ) (((j + 1 : ℕ) : ℝ))
  have hset_eq :=
    setIntegral_radialStrip_eq_intervalIntegral j (phi0AnnulusIntegrand k (‖g 0‖ ^ 2))
  calc
    (1 / Real.pi) *
        (T *
          ∫ r in srad,
            phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r)
      =
    ((1 / Real.pi) * T) *
        ∫ r in srad,
          phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r := by ring
    _ =
      2 *
        ∫ r in srad,
          phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r := by rw [hT_eq]
    _ =
      2 *
      ∫ r in (j : ℝ)..(((j + 1 : ℕ) : ℝ)),
          phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r := by rw [hset_eq]
private theorem phi0AnnulusIntegrand_le_shell
    (k j : ℕ)
    (g0normsq : ℝ)
    {r : ℝ}
    (hr : r ∈ Set.Icc (j : ℝ) (((j + 1 : ℕ) : ℝ)))
    (hg0 : 0 ≤ g0normsq) :
    phi0AnnulusIntegrand k g0normsq r
      ≤ (g0normsq / (Nat.factorial k : ℝ)) *
          ((((j + 1 : ℕ) : ℝ) ^ (2 * k + 1))) * Real.exp (-(j : ℝ) ^ 2) := by
  have hr_nonneg : 0 ≤ r := by exact le_trans (by exact_mod_cast Nat.zero_le j) hr.1
  have hsqrt_sq : (Real.sqrt (Nat.factorial k : ℝ)) ^ 2 = (Nat.factorial k : ℝ) := by
    simp_all
  have hpow : r ^ (2 * k + 1) ≤ (((j + 1 : ℕ) : ℝ) ^ (2 * k + 1)) := by
    gcongr
    exact hr.2
  have hexp : Real.exp (-r ^ 2) ≤ Real.exp (-(j : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hr.1, hr.2]
  unfold phi0AnnulusIntegrand
  have hsqrt_nonzero : Real.sqrt (Nat.factorial k : ℝ) ≠ 0 := by positivity
  calc
    r * (((r ^ k / Real.sqrt (Nat.factorial k : ℝ)) ^ 2) * g0normsq) * Real.exp (-r ^ 2)
      = (g0normsq / (Nat.factorial k : ℝ)) * (r ^ (2 * k + 1)) * Real.exp (-r ^ 2) := by
          field_simp [hsqrt_nonzero]
          rw [hsqrt_sq]
          ring
    _ ≤ (g0normsq / (Nat.factorial k : ℝ)) *
          ((((j + 1 : ℕ) : ℝ) ^ (2 * k + 1))) * Real.exp (-(j : ℝ) ^ 2) := by
          have hcoeff_nonneg : 0 ≤ g0normsq / (Nat.factorial k : ℝ) := by positivity
          have hprod :
              r ^ (2 * k + 1) * Real.exp (-r ^ 2)
                ≤
              (((j + 1 : ℕ) : ℝ) ^ (2 * k + 1)) * Real.exp (-(j : ℝ) ^ 2) := by gcongr
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (mul_le_mul_of_nonneg_left hprod hcoeff_nonneg)
private theorem annulusIntegralSq_phi0_shell_bound
    (k j : ℕ)
    {g : ℕ → ℂ}
    (hpolar : ∀ r : ℝ, 0 < r → ∀ t : Circle,
      phi0 k (circlePoint r t) = circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ) * g 0) :
    annulusIntegralSq (phi0 k) j ≤
      (2 * (‖g 0‖ ^ 2 / (Nat.factorial k : ℝ))) *
        ((((j + 1 : ℕ) : ℝ) ^ (2 * k + 1))) * Real.exp (-(j : ℝ) ^ 2) := by
  rw [annulusIntegralSq_phi0_eq k j hpolar]
  have hint :
      IntervalIntegrable (phi0AnnulusIntegrand k (‖g 0‖ ^ 2))
        volume (j : ℝ) (((j + 1 : ℕ) : ℝ)) :=
    (continuous_phi0AnnulusIntegrand k (‖g 0‖ ^ 2)).intervalIntegrable _ _
  have hbound :
      ∫ r in (j : ℝ)..(((j + 1 : ℕ) : ℝ)), phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r
        ≤
      ∫ r in (j : ℝ)..(((j + 1 : ℕ) : ℝ)),
        (‖g 0‖ ^ 2 / (Nat.factorial k : ℝ)) *
          ((((j + 1 : ℕ) : ℝ) ^ (2 * k + 1))) * Real.exp (-(j : ℝ) ^ 2) := by
    refine intervalIntegral.integral_mono_on
      (show (j : ℝ) ≤ (((j + 1 : ℕ) : ℝ)) by exact_mod_cast Nat.le_succ j)
      hint
      intervalIntegrable_const
      ?_
    intro r hr
    exact phi0AnnulusIntegrand_le_shell k j (‖g 0‖ ^ 2) hr (by positivity)
  have hconst :
      ∫ r in (j : ℝ)..(((j + 1 : ℕ) : ℝ)),
        (‖g 0‖ ^ 2 / (Nat.factorial k : ℝ)) *
          ((((j + 1 : ℕ) : ℝ) ^ (2 * k + 1))) * Real.exp (-(j : ℝ) ^ 2)
        =
      (‖g 0‖ ^ 2 / (Nat.factorial k : ℝ)) *
        ((((j + 1 : ℕ) : ℝ) ^ (2 * k + 1))) * Real.exp (-(j : ℝ) ^ 2) := by
    simp_all only [fourier_apply, neg_smul, natCast_zsmul, Nat.cast_add, Nat.cast_one,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, add_sub_cancel_left,
      smul_eq_mul, one_mul]
  calc
    2 * ∫ r in (j : ℝ)..(((j + 1 : ℕ) : ℝ)), phi0AnnulusIntegrand k (‖g 0‖ ^ 2) r
      ≤
    2 * ∫ r in (j : ℝ)..(((j + 1 : ℕ) : ℝ)),
      (‖g 0‖ ^ 2 / (Nat.factorial k : ℝ)) *
        ((((j + 1 : ℕ) : ℝ) ^ (2 * k + 1))) * Real.exp (-(j : ℝ) ^ 2) := by gcongr
    _ =
      (2 * (‖g 0‖ ^ 2 / (Nat.factorial k : ℝ))) *
        ((((j + 1 : ℕ) : ℝ) ^ (2 * k + 1))) * Real.exp (-(j : ℝ) ^ 2) := by
          rw [hconst]
          ring
end HermitekLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution :
    ∀ k : ℕ,
      ∃ C c : ℝ,
        0 < C ∧ 0 < c ∧
          ∀ j : ℕ,
            annulusIntegralSq (phi0 k) j ≤
              C * Real.exp (-c * (posPart ((j : ℝ) - ((k + 5 : ℕ) : ℝ))) ^ 2) := by
  intro k
  obtain ⟨g, _, _, hpolar⟩ := phi0_support_zero k
  let m : ℕ := 2 * k + 1
  obtain ⟨Cpoly, hCpoly_pos, hCpoly⟩ :=
    HermiteLEAN.polynomial_times_gaussian_le_gaussian (a := 1) (by norm_num) m
  let A : ℝ :=
    (2 * (‖g 0‖ ^ 2 / (Nat.factorial k : ℝ))) * ((((k + 6 : ℕ) : ℝ) ^ m)) * (2 ^ (m - 1))
  let C : ℝ := A * Cpoly + 1
  refine ⟨C, (1 : ℝ) / 2, by positivity, by norm_num, ?_⟩
  intro j
  let x : ℝ := posPart ((j : ℝ) - ((k + 5 : ℕ) : ℝ))
  have hx_nonneg : 0 ≤ x := by
    dsimp [x, posPart]
    exact le_max_right _ _
  have hx_le_j : x ≤ (j : ℝ) := by
    dsimp [x, posPart]
    refine max_le ?_ ?_
    · exact sub_le_self _ (Nat.cast_nonneg _)
    · exact_mod_cast Nat.zero_le j
  have hj1_le : (((j + 1 : ℕ) : ℝ)) ≤ (((k + 6 : ℕ) : ℝ)) * (x + 1) := by
    have hx_lb : (j : ℝ) - ((k + 5 : ℕ) : ℝ) ≤ x := by
      dsimp [x, posPart]
      exact le_max_left _ _
    have hkcast : (((k + 6 : ℕ) : ℝ)) = ((k + 5 : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    have hsum' : (j : ℝ) + 1 ≤ x + (((k + 6 : ℕ) : ℝ)) := by
      rw [hkcast]
      linarith only [hx_lb]
    have hsum : (((j + 1 : ℕ) : ℝ)) ≤ x + (((k + 6 : ℕ) : ℝ)) := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hsum'
    have hk6_ge1_nat : 1 ≤ k + 6 := by omega
    have hk6_ge1 : (1 : ℝ) ≤ (((k + 6 : ℕ) : ℝ)) := by exact_mod_cast hk6_ge1_nat
    have hmul : x + (((k + 6 : ℕ) : ℝ)) ≤ (((k + 6 : ℕ) : ℝ)) * (x + 1) := by
      nlinarith only [
        hx_nonneg, hkcast
      ]
    exact le_trans hsum hmul
  have hpoly1 : (((j + 1 : ℕ) : ℝ) ^ m) ≤ ((((k + 6 : ℕ) : ℝ) ^ m)) * ((x + 1) ^ m) := by
    calc
      (((j + 1 : ℕ) : ℝ) ^ m) ≤ ((((k + 6 : ℕ) : ℝ) * (x + 1)) ^ m) := by gcongr
      _ = ((((k + 6 : ℕ) : ℝ) ^ m)) * ((x + 1) ^ m) := by rw [mul_pow]
  have hpoly2 : (x + 1) ^ m ≤ 2 ^ (m - 1) * (x ^ m + 1) := by
    simpa only [one_pow, add_comm, add_left_comm, add_assoc] using
      add_pow_le hx_nonneg (show (0 : ℝ) ≤ 1 by norm_num) m
  have hpoly :
      (((j + 1 : ℕ) : ℝ) ^ m) ≤ ((((k + 6 : ℕ) : ℝ) ^ m)) * (2 ^ (m - 1)) * (1 + x ^ m) := by
    calc
      (((j + 1 : ℕ) : ℝ) ^ m) ≤ ((((k + 6 : ℕ) : ℝ) ^ m)) * ((x + 1) ^ m) := hpoly1
      _ ≤ ((((k + 6 : ℕ) : ℝ) ^ m)) * (2 ^ (m - 1) * (x ^ m + 1)) := by gcongr
      _ = ((((k + 6 : ℕ) : ℝ) ^ m)) * (2 ^ (m - 1)) * (1 + x ^ m) := by ring
  have hexp : Real.exp (-(j : ℝ) ^ 2) ≤ Real.exp (-x ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hx_nonneg, hx_le_j]
  have hshell := annulusIntegralSq_phi0_shell_bound k j hpolar
  have hmain :
      annulusIntegralSq (phi0 k) j ≤ A * (1 + x ^ m) * Real.exp (-x ^ 2) := by
    calc
      annulusIntegralSq (phi0 k) j
        ≤ (2 * (‖g 0‖ ^ 2 / (Nat.factorial k : ℝ))) * ((((j + 1 : ℕ) : ℝ) ^ m)) *
            Real.exp (-(j : ℝ) ^ 2) := by simpa only [Nat.cast_add, Nat.cast_one, m] using hshell
      _ ≤ (2 * (‖g 0‖ ^ 2 / (Nat.factorial k : ℝ))) *
            ((((k + 6 : ℕ) : ℝ) ^ m) * (2 ^ (m - 1)) * (1 + x ^ m)) * Real.exp (-x ^ 2) := by gcongr
      _ = A * (1 + x ^ m) * Real.exp (-x ^ 2) := by
              dsimp [A]
              ring
  have hgauss : (1 + x ^ m) * Real.exp (-x ^ 2) ≤ Cpoly * Real.exp (-((1 : ℝ) / 2) * x ^ 2) := by
    simpa only [one_div, neg_mul, one_mul] using hCpoly x hx_nonneg
  have hA_nonneg : 0 ≤ A := by positivity
  calc
    annulusIntegralSq (phi0 k) j
      ≤ A * (1 + x ^ m) * Real.exp (-x ^ 2) := hmain
    _ ≤ A * (Cpoly * Real.exp (-((1 : ℝ) / 2) * x ^ 2)) := by
          simpa only [mul_assoc, one_div, neg_mul] using mul_le_mul_of_nonneg_left hgauss hA_nonneg
    _ ≤ (A * Cpoly + 1) * Real.exp (-((1 : ℝ) / 2) * x ^ 2) := by
          have hexp_nonneg : 0 ≤ Real.exp (-((1 : ℝ) / 2) * x ^ 2) := (Real.exp_pos _).le
          have hcoeff : A * Cpoly ≤ A * Cpoly + 1 := le_add_of_nonneg_right zero_le_one
          simpa only [one_div, neg_mul, ge_iff_le, mul_assoc] using
            mul_le_mul_of_nonneg_right hcoeff hexp_nonneg
    _ = C * Real.exp (-((1 : ℝ) / 2) * x ^ 2) := by rfl
    _ = C * Real.exp (-((1 : ℝ) / 2) * (posPart ((j : ℝ) - ((k + 5 : ℕ) : ℝ))) ^ 2) := by rfl
end HermitekLEAN
