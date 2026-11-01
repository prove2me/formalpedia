-- Prove2me | solution 1 for MechanismDesign.Dynamic.optimal_sequential_screening
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T20:16:23.461336+00:00
-- url     : https://prove2.me/submissions/9740c0c9-0fca-4259-85d8-e6869cb9dc11

import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model
import Definitions.Def_MechanismDesign_Dynamic_OptimalScreening

set_option autoImplicit false
set_option linter.unusedVariables false

open MeasureTheory Set
open scoped Interval

namespace MechanismDesign.Dynamic.SSAux

variable {τlo τhi θlo θhi : ℝ}

lemma F_lo (E : SeqEnv τlo τhi θlo θhi) {τ : ℝ} (hτ : τ ∈ Icc τlo τhi) : E.F θlo τ = 0 := by
  rw [E.F_eq τ hτ θlo ⟨le_rfl, E.θlo_lt_θhi.le⟩]; simp

lemma F_hi (E : SeqEnv τlo τhi θlo θhi) {τ : ℝ} (hτ : τ ∈ Icc τlo τhi) : E.F θhi τ = 1 := by
  rw [E.F_eq τ hτ θhi ⟨E.θlo_lt_θhi.le, le_rfl⟩]; exact E.f_total τ hτ

lemma dFdτ_eq_zero_of_const (E : SeqEnv τlo τhi θlo θhi) {θ : ℝ} (hθ : θ ∈ Icc θlo θhi) (c : ℝ)
    (hc : ∀ s ∈ Icc τlo τhi, E.F θ s = c) {τ : ℝ} (hτ : τ ∈ Icc τlo τhi) : E.dFdτ θ τ = 0 := by
  have h1 := E.hasDerivWithinAt_F θ hθ τ hτ
  have h2 : HasDerivWithinAt (fun s => E.F θ s) 0 (Icc τlo τhi) τ :=
    (hasDerivWithinAt_const τ _ c).congr (fun s hs => hc s hs) (hc τ hτ)
  exact (uniqueDiffOn_Icc E.τlo_lt_τhi τ hτ).eq_deriv _ h1 h2

lemma dFdτ_lo (E : SeqEnv τlo τhi θlo θhi) {τ : ℝ} (hτ : τ ∈ Icc τlo τhi) : E.dFdτ θlo τ = 0 :=
  dFdτ_eq_zero_of_const E ⟨le_rfl, E.θlo_lt_θhi.le⟩ 0 (fun s hs => F_lo E hs) hτ

lemma dFdτ_hi (E : SeqEnv τlo τhi θlo θhi) {τ : ℝ} (hτ : τ ∈ Icc τlo τhi) : E.dFdτ θhi τ = 0 :=
  dFdτ_eq_zero_of_const E ⟨E.θlo_lt_θhi.le, le_rfl⟩ 1 (fun s hs => F_hi E hs) hτ

lemma dFdτ_nonpos (E : SeqEnv τlo τhi θlo θhi) {θ τ : ℝ} (hθ : θ ∈ Icc θlo θhi)
    (hτ : τ ∈ Icc τlo τhi) : E.dFdτ θ τ ≤ 0 := by
  rcases eq_or_lt_of_le hθ.1 with h | h
  · subst h; rw [dFdτ_lo E hτ]
  rcases eq_or_lt_of_le hθ.2 with h' | h'
  · subst h'; rw [dFdτ_hi E hτ]
  exact (E.fosd θ ⟨h, h'⟩ τ hτ).le

lemma F_lip (E : SeqEnv τlo τhi θlo θhi) {θ : ℝ} (hθ : θ ∈ Icc θlo θhi) {τ τ' : ℝ}
    (hτ : τ ∈ Icc τlo τhi) (hτ' : τ' ∈ Icc τlo τhi) :
    |E.F θ τ' - E.F θ τ| ≤ E.K * |τ' - τ| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun s => E.F θ s)
    (f' := fun s => E.dFdτ θ s) (C := E.K) (s := Icc τlo τhi)
    (fun x hx => E.hasDerivWithinAt_F θ hθ x hx)
    (fun x hx => (E.abs_dFdτ_lt θ hθ x hx).le) (convex_Icc _ _) hτ hτ'
  simpa [Real.norm_eq_abs] using this

/-- ψ ≥ θlo ≥ 0 on the rectangle under Assumption 11.1. -/
lemma psi_lo (E : SeqEnv τlo τhi θlo θhi) {τ : ℝ} (hτ : τ ∈ Icc τlo τhi) : E.ψ τ θlo = θlo := by
  simp [SeqEnv.ψ, dFdτ_lo E hτ]

lemma psi_ge (E : SeqEnv τlo τhi θlo θhi) (hA : E.Assumption11_1) {τ θ : ℝ}
    (hτ : τ ∈ Icc τlo τhi) (hθ : θ ∈ Icc θlo θhi) : θlo ≤ E.ψ τ θ := by
  have := hA.2 τ hτ ⟨le_rfl, E.θlo_lt_θhi.le⟩ hθ hθ.1
  simpa [psi_lo E hτ] using this

lemma p_eq (E : SeqEnv τlo τhi θlo θhi) (hA : E.Assumption11_1) {τ : ℝ}
    (hτ : τ ∈ Icc τlo τhi) : E.p τ = θlo := by
  unfold SeqEnv.p
  apply le_antisymm
  · apply csInf_le (⟨θlo, fun x hx => hx.1.1⟩ : BddBelow _)
    exact ⟨⟨le_rfl, E.θlo_lt_θhi.le⟩, by rw [psi_lo E hτ]; exact E.θlo_nonneg⟩
  · refine le_csInf ?_ ?_
    · exact ⟨θlo, ⟨le_rfl, E.θlo_lt_θhi.le⟩, by rw [psi_lo E hτ]; exact E.θlo_nonneg⟩
    · exact fun x hx => hx.1.1

lemma optQ_eq (E : SeqEnv τlo τhi θlo θhi) (hA : E.Assumption11_1) {τ θ : ℝ}
    (hτ : τ ∈ Icc τlo τhi) (hθ : θ ∈ Icc θlo θhi) : E.optQ τ θ = 1 := by
  simp [SeqEnv.optQ, p_eq E hA hτ, hθ.1]

/-! ### Ex-post incentive compatibility -/

lemma sandwich (m : DirectMechanism τlo τhi θlo θhi) (h : m.IsExPostIC) {τ θ θ' : ℝ}
    (hτ : τ ∈ Icc τlo τhi) (hθ : θ ∈ Icc θlo θhi) (hθ' : θ' ∈ Icc θlo θhi) :
    (θ - θ') * m.q τ θ' ≤ m.u τ θ - m.u τ θ' := by
  have := h τ hτ θ hθ θ' hθ'
  simp only [DirectMechanism.u] at *
  linarith

lemma u_lip (m : DirectMechanism τlo τhi θlo θhi) (hadm : m.Admissible) (h : m.IsExPostIC)
    {τ θ θ' : ℝ} (hτ : τ ∈ Icc τlo τhi) (hθ : θ ∈ Icc θlo θhi) (hθ' : θ' ∈ Icc θlo θhi) :
    |m.u τ θ - m.u τ θ'| ≤ |θ - θ'| := by
  have h1 := sandwich m h hτ hθ hθ'
  have h2 := sandwich m h hτ hθ' hθ
  have q1 := hadm.1 τ hτ θ hθ
  have q2 := hadm.1 τ hτ θ' hθ'
  rw [abs_le]
  rcases le_total θ θ' with hl | hl
  · rw [abs_of_nonpos (by linarith)]
    constructor <;> nlinarith [q1.1, q1.2, q2.1, q2.2]
  · rw [abs_of_nonneg (by linarith)]
    constructor <;> nlinarith [q1.1, q1.2, q2.1, q2.2]

lemma u_lipOn (m : DirectMechanism τlo τhi θlo θhi) (hadm : m.Admissible) (h : m.IsExPostIC)
    {τ : ℝ} (hτ : τ ∈ Icc τlo τhi) (hle : θlo ≤ θhi) :
    LipschitzOnWith 1 (fun θ => m.u τ θ) (uIcc θlo θhi) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [uIcc_of_le hle] at hx hy
  simpa [Real.dist_eq] using u_lip m hadm h hτ hx hy

lemma deriv_u (m : DirectMechanism τlo τhi θlo θhi) (h : m.IsExPostIC) {τ θ d : ℝ}
    (hτ : τ ∈ Icc τlo τhi) (hθ : θ ∈ Ioo θlo θhi) (hd : HasDerivAt (fun x => m.u τ x) d θ) :
    d = m.q τ θ := by
  have hw : HasDerivAt (fun x => m.u τ x - m.q τ θ * x) (d - m.q τ θ * 1) θ :=
    hd.sub ((hasDerivAt_id' θ).const_mul _)
  have hmin : IsLocalMin (fun x => m.u τ x - m.q τ θ * x) θ := by
    filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with x hx
    have := sandwich m h hτ ⟨hx.1.le, hx.2.le⟩ ⟨hθ.1.le, hθ.2.le⟩
    linarith [show (x - θ) * m.q τ θ = m.q τ θ * x - m.q τ θ * θ by ring]
  have := hmin.hasDerivAt_eq_zero hw
  linarith

/-- **K1**: the closed form of `Û(τ|σ)`. -/
lemma uhat_eq (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hadm : m.Admissible) (h : m.IsExPostIC) {τ σ : ℝ} (hτ : τ ∈ Icc τlo τhi)
    (hσ : σ ∈ Icc τlo τhi) :
    m.Uhat E τ σ = m.u τ θhi - ∫ θ in θlo..θhi, m.q τ θ * E.F θ σ := by
  have hle := E.θlo_lt_θhi.le
  set Fs : ℝ → ℝ := fun x => ∫ t in θlo..x, E.f t σ with hFs
  have hfi := E.f_integrable σ hσ
  have hFac : AbsolutelyContinuousOnInterval Fs θlo θhi :=
    hfi.absolutelyContinuousOnInterval_intervalIntegral (c := θlo) (by simp)
  have huac : AbsolutelyContinuousOnInterval (fun θ => m.u τ θ) θlo θhi :=
    (u_lipOn m hadm h hτ hle).absolutelyContinuousOnInterval
  have ibp := huac.integral_mul_deriv_eq_deriv_mul hFac
  have e1 : ∫ x in θlo..θhi, m.u τ x * deriv Fs x = m.Uhat E τ σ := by
    unfold DirectMechanism.Uhat
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hfi.ae_hasDerivAt_integral] with x hx hx'
    rw [(hx (uIoc_subset_uIcc hx') θlo (by simp)).deriv]
  have e2 : ∫ x in θlo..θhi, deriv (fun θ => m.u τ θ) x * Fs x =
      ∫ x in θlo..θhi, m.q τ x * E.F x σ := by
    apply intervalIntegral.integral_congr_ae
    have hne : ∀ᵐ x ∂volume, x ≠ θhi := by rw [ae_iff]; simp
    filter_upwards [huac.ae_differentiableAt, hne] with x hx hxne hx'
    rw [uIoc_of_le hle] at hx'
    have hxI : x ∈ Ioo θlo θhi := ⟨hx'.1, lt_of_le_of_ne hx'.2 hxne⟩
    have hxd := (hx (by rw [uIcc_of_le hle]; exact Ioo_subset_Icc_self hxI)).hasDerivAt
    rw [deriv_u m h hτ hxI hxd, hFs]
    simp only
    rw [E.F_eq σ hσ x ⟨hxI.1.le, hxI.2.le⟩]
  have h1 : Fs θhi = 1 := E.f_total σ hσ
  have h0 : Fs θlo = 0 := by simp [hFs]
  rw [← e1, ibp, e2, h1, h0]
  ring


lemma q_mono (m : DirectMechanism τlo τhi θlo θhi) (h : m.IsExPostIC) {τ : ℝ}
    (hτ : τ ∈ Icc τlo τhi) : MonotoneOn (fun θ => m.q τ θ) (Icc θlo θhi) := by
  intro x hx y hy hxy
  have h1 := sandwich m h hτ hy hx
  have h2 := sandwich m h hτ hx hy
  rcases eq_or_lt_of_le hxy with e | lt
  · subst e; exact le_rfl
  · by_contra hc
    rw [not_le] at hc
    nlinarith [mul_pos (sub_pos.2 lt) (sub_pos.2 hc)]

lemma q_aesm (m : DirectMechanism τlo τhi θlo θhi) (h : m.IsExPostIC) {τ : ℝ}
    (hτ : τ ∈ Icc τlo τhi) (hle : θlo ≤ θhi) :
    AEStronglyMeasurable (fun θ => m.q τ θ) (volume.restrict (Ι θlo θhi)) :=
  ((aemeasurable_restrict_of_monotoneOn measurableSet_Icc (q_mono m h hτ)).mono_set
    (by rw [uIoc_of_le hle]; exact Ioc_subset_Icc_self)).aestronglyMeasurable

lemma F_cont (E : SeqEnv τlo τhi θlo θhi) {σ : ℝ} (hσ : σ ∈ Icc τlo τhi) :
    ContinuousOn (fun θ => E.F θ σ) (uIcc θlo θhi) := by
  have hle := E.θlo_lt_θhi.le
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hle).1 (E.f_integrable σ hσ)
  rw [← uIcc_of_le hle] at hi
  exact (intervalIntegral.continuousOn_primitive_interval hi).congr
    (fun x hx => E.F_eq σ hσ x (by rwa [uIcc_of_le hle] at hx))

lemma int_of_bdd {φ ψ : ℝ → ℝ} {a b C : ℝ} (hφ : AEStronglyMeasurable φ (volume.restrict (Ι a b)))
    (hb : ∀ x ∈ Ι a b, |φ x| ≤ C) (hψ : IntervalIntegrable ψ volume a b) :
    IntervalIntegrable (fun x => φ x * ψ x) volume a b := by
  rw [intervalIntegrable_iff] at *
  exact hψ.bdd_mul hφ ((ae_restrict_iff' measurableSet_uIoc).2
    (Filter.Eventually.of_forall fun x hx => by simpa [Real.norm_eq_abs] using hb x hx))

lemma q_abs_le (m : DirectMechanism τlo τhi θlo θhi) (hadm : m.Admissible) {τ θ : ℝ}
    (hτ : τ ∈ Icc τlo τhi) (hθ : θ ∈ Icc θlo θhi) : |m.q τ θ| ≤ 1 := by
  have := hadm.1 τ hτ θ hθ
  rw [abs_le]; constructor <;> linarith [this.1, this.2]

lemma mem_I_of_uIoc {θ : ℝ} (hle : θlo ≤ θhi) (h : θ ∈ Ι θlo θhi) : θ ∈ Icc θlo θhi := by
  rw [uIoc_of_le hle] at h; exact Ioc_subset_Icc_self h

lemma qF_int (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hadm : m.Admissible) (h : m.IsExPostIC) {τ σ : ℝ} (hτ : τ ∈ Icc τlo τhi)
    (hσ : σ ∈ Icc τlo τhi) :
    IntervalIntegrable (fun θ => m.q τ θ * E.F θ σ) volume θlo θhi :=
  int_of_bdd (q_aesm m h hτ E.θlo_lt_θhi.le)
    (fun x hx => q_abs_le m hadm hτ (mem_I_of_uIoc E.θlo_lt_θhi.le hx))
    (F_cont E hσ).intervalIntegrable

lemma U_ge (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hadm : m.Admissible) (hIC : m.IsIC E) {τ τ' : ℝ} (hτ : τ ∈ Icc τlo τhi)
    (hτ' : τ' ∈ Icc τlo τhi) :
    ∫ θ in θlo..θhi, m.q τ' θ * (E.F θ τ' - E.F θ τ) ≤ m.U E τ - m.U E τ' := by
  have h1 := hIC.2 τ hτ τ' hτ' id measurable_id (fun θ hθ => hθ)
  have e : (∫ θ in θlo..θhi, (θ * m.q τ' (id θ) - m.t τ' (id θ)) * E.f θ τ) = m.Uhat E τ' τ := rfl
  rw [e, uhat_eq E m hadm hIC.1 hτ' hτ] at h1
  have h2 : m.U E τ' = m.u τ' θhi - ∫ θ in θlo..θhi, m.q τ' θ * E.F θ τ' :=
    uhat_eq E m hadm hIC.1 hτ' hτ'
  rw [h2]
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub (qF_int E m hadm hIC.1 hτ' hτ') (qF_int E m hadm hIC.1 hτ' hτ)]
  linarith

lemma U_lip (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hadm : m.Admissible) (hIC : m.IsIC E) {τ τ' : ℝ} (hτ : τ ∈ Icc τlo τhi)
    (hτ' : τ' ∈ Icc τlo τhi) :
    |m.U E τ - m.U E τ'| ≤ E.K * (θhi - θlo) * |τ - τ'| := by
  have hle := E.θlo_lt_θhi.le
  have bnd : ∀ a b : ℝ, a ∈ Icc τlo τhi → b ∈ Icc τlo τhi →
      |∫ θ in θlo..θhi, m.q a θ * (E.F θ a - E.F θ b)| ≤ E.K * (θhi - θlo) * |τ - τ'| ∨
        |a - b| ≠ |τ - τ'| := by
    intro a b ha hb
    by_cases hab : |a - b| = |τ - τ'|
    · left
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := θlo) (b := θhi)
        (C := E.K * |τ - τ'|) (f := fun θ => m.q a θ * (E.F θ a - E.F θ b)) (fun x hx => by
          have hxI := mem_I_of_uIoc hle hx
          rw [Real.norm_eq_abs, abs_mul]
          have h1 := q_abs_le m hadm ha hxI
          have h2 := F_lip E hxI hb ha
          rw [← hab]
          calc |m.q a x| * |E.F x a - E.F x b| ≤ 1 * (E.K * |a - b|) := by
                apply mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
            _ = E.K * |a - b| := one_mul _)
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hle)] at this
      linarith
    · right; exact hab
  have g1 := U_ge E m hadm hIC hτ hτ'
  have g2 := U_ge E m hadm hIC hτ' hτ
  have b1 := (bnd τ' τ hτ' hτ).resolve_right (by rw [abs_sub_comm]; exact not_not.2 rfl)
  have b2 := (bnd τ τ' hτ hτ').resolve_right (not_not.2 rfl)
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (∫ θ in θlo..θhi, m.q τ' θ * (E.F θ τ' - E.F θ τ))]
  · linarith [neg_abs_le (∫ θ in θlo..θhi, m.q τ θ * (E.F θ τ - E.F θ τ'))]

/-- The envelope derivative `U'(s) = −∫ q(s,θ) ∂F(θ|s)/∂τ dθ`. -/
noncomputable def phi (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi) (s : ℝ) :
    ℝ :=
  -(∫ θ in θlo..θhi, m.q s θ * E.dFdτ θ s)

lemma dF_aesm (E : SeqEnv τlo τhi θlo θhi) (s : ℝ) (μ : Measure ℝ) :
    AEStronglyMeasurable (fun θ => E.dFdτ θ s) μ :=
  (E.dFdτ_measurable.comp measurable_prodMk_left).aestronglyMeasurable

lemma deriv_U (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hadm : m.Admissible) (hIC : m.IsIC E) {τ d : ℝ} (hτ : τ ∈ Ioo τlo τhi)
    (hd : HasDerivAt (fun s => m.U E s) d τ) : d = phi E m τ := by
  have hle := E.θlo_lt_θhi.le
  have hτJ : τ ∈ Icc τlo τhi := Ioo_subset_Icc_self hτ
  set L : ℝ → ℝ := fun x => ∫ θ in θlo..θhi, m.q τ θ * (E.F θ τ - E.F θ x) with hL
  have hLd : HasDerivAt L (∫ θ in θlo..θhi, m.q τ θ * -E.dFdτ θ τ) τ := by
    refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun x θ => m.q τ θ * (E.F θ τ - E.F θ x))
      (F' := fun x θ => m.q τ θ * -E.dFdτ θ x) (bound := fun _ => E.K)
      (Ioo_mem_nhds hτ.1 hτ.2) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_).2
    · filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with x hx
      exact (q_aesm m hIC.1 hτJ hle).mul
        (((F_cont E hτJ).sub (F_cont E (Ioo_subset_Icc_self hx))).mono uIoc_subset_uIcc
          |>.aestronglyMeasurable measurableSet_uIoc)
    · exact int_of_bdd (q_aesm m hIC.1 hτJ hle)
        (fun x hx => q_abs_le m hadm hτJ (mem_I_of_uIoc hle hx))
        ((F_cont E hτJ).sub (F_cont E hτJ)).intervalIntegrable
    · exact (q_aesm m hIC.1 hτJ hle).mul (dF_aesm E τ _).neg
    · refine Filter.Eventually.of_forall fun θ hθ x hx => ?_
      have hθI := mem_I_of_uIoc hle hθ
      rw [Real.norm_eq_abs, abs_mul, abs_neg]
      have h1 := q_abs_le m hadm hτJ hθI
      have h2 := (E.abs_dFdτ_lt θ hθI x (Ioo_subset_Icc_self hx)).le
      nlinarith [abs_nonneg (m.q τ θ), abs_nonneg (E.dFdτ θ x)]
    · refine Filter.Eventually.of_forall fun θ hθ x hx => ?_
      have hθI := mem_I_of_uIoc hle hθ
      have := (E.hasDerivWithinAt_F θ hθI x (Ioo_subset_Icc_self hx)).hasDerivAt
        (Icc_mem_nhds hx.1 hx.2)
      simpa using ((hasDerivAt_const x (E.F θ τ)).sub this).const_mul (m.q τ θ)
  have hmin : IsLocalMin (fun x => m.U E x - L x) τ := by
    filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with x hx
    have := U_ge E m hadm hIC (Ioo_subset_Icc_self hx) hτJ
    have hL0 : L τ = 0 := by simp [hL]
    simp only [hL0]
    simp only [hL] at this ⊢
    linarith
  have := hmin.hasDerivAt_eq_zero (hd.sub hLd)
  have e : (∫ θ in θlo..θhi, m.q τ θ * -E.dFdτ θ τ) = phi E m τ := by
    simp [phi, mul_neg, intervalIntegral.integral_neg]
  linarith

lemma U_ac (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hadm : m.Admissible) (hIC : m.IsIC E) {τ : ℝ} (hτ : τ ∈ Icc τlo τhi) :
    AbsolutelyContinuousOnInterval (fun s => m.U E s) τlo τ := by
  have hle := E.θlo_lt_θhi.le
  have hsub : uIcc τlo τ ⊆ Icc τlo τhi := by
    rw [uIcc_of_le hτ.1]; exact Icc_subset_Icc le_rfl hτ.2
  have hC : 0 ≤ E.K * (θhi - θlo) := mul_nonneg E.K_pos.le (sub_nonneg.2 hle)
  have hlip : LipschitzOnWith (E.K * (θhi - θlo)).toNNReal (fun s => m.U E s) (uIcc τlo τ) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [Real.coe_toNNReal _ hC, Real.dist_eq, Real.dist_eq]
    exact U_lip E m hadm hIC (hsub hx) (hsub hy)
  exact hlip.absolutelyContinuousOnInterval

lemma dU_ae (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hadm : m.Admissible) (hIC : m.IsIC E) {τ : ℝ} (hτ : τ ∈ Icc τlo τhi) :
    ∀ᵐ x ∂volume, x ∈ Ι τlo τ → deriv (fun s => m.U E s) x = phi E m x := by
  have hac := U_ac E m hadm hIC hτ
  have hne : ∀ᵐ x ∂volume, x ≠ τ := by rw [ae_iff]; simp
  filter_upwards [hac.ae_differentiableAt, hne] with x hx hxne hx'
  rw [uIoc_of_le hτ.1] at hx'
  have hxI : x ∈ Ioo τlo τhi := ⟨hx'.1, lt_of_lt_of_le (lt_of_le_of_ne hx'.2 hxne) hτ.2⟩
  have hxd := (hx (by rw [uIcc_of_le hτ.1]; exact ⟨hx'.1.le, hx'.2⟩)).hasDerivAt
  exact deriv_U E m hadm hIC hxI hxd

/-- **K2** (envelope formula). -/
lemma envelope (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hadm : m.Admissible) (hIC : m.IsIC E) {τ : ℝ} (hτ : τ ∈ Icc τlo τhi) :
    m.U E τ = m.U E τlo + ∫ s in τlo..τ, phi E m s := by
  have hft := (U_ac E m hadm hIC hτ).integral_deriv_eq_sub
  rw [intervalIntegral.integral_congr_ae (dU_ae E m hadm hIC hτ)] at hft
  linarith

lemma phi_int (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hadm : m.Admissible) (hIC : m.IsIC E) :
    IntervalIntegrable (phi E m) volume τlo τhi := by
  have hhi : τhi ∈ Icc τlo τhi := ⟨E.τlo_lt_τhi.le, le_rfl⟩
  exact intervalIntegrable_iff.2 (Integrable.congr
    (intervalIntegrable_iff.1 (U_ac E m hadm hIC hhi).intervalIntegrable_deriv)
    ((ae_restrict_iff' measurableSet_uIoc).2 (dU_ae E m hadm hIC hhi)))

/-- `G̃(τ) = ∫_{τ̲}^{τ} g`. -/
noncomputable def Gt (E : SeqEnv τlo τhi θlo θhi) (τ : ℝ) : ℝ := ∫ x in τlo..τ, E.g x

lemma Gt_cont (E : SeqEnv τlo τhi θlo θhi) : ContinuousOn (Gt E) (uIcc τlo τhi) := by
  have hle := E.τlo_lt_τhi.le
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hle).1 E.g_integrable
  rw [← uIcc_of_le hle] at hi
  exact intervalIntegral.continuousOn_primitive_interval hi

/-- Integration by parts in `τ`: `∫ g U = U(τ̲) + ∫ (1 − G̃) U'`. -/
lemma gU (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hadm : m.Admissible) (hIC : m.IsIC E) :
    ∫ τ in τlo..τhi, E.g τ * m.U E τ =
      m.U E τlo + ∫ τ in τlo..τhi, (1 - Gt E τ) * phi E m τ := by
  have hhi : τhi ∈ Icc τlo τhi := ⟨E.τlo_lt_τhi.le, le_rfl⟩
  have hGac : AbsolutelyContinuousOnInterval (Gt E) τlo τhi :=
    E.g_integrable.absolutelyContinuousOnInterval_intervalIntegral (c := τlo) (by simp)
  have hUac := U_ac E m hadm hIC hhi
  have ibp := hUac.integral_mul_deriv_eq_deriv_mul hGac
  have e1 : ∫ τ in τlo..τhi, E.g τ * m.U E τ = ∫ τ in τlo..τhi, m.U E τ * deriv (Gt E) τ := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [E.g_integrable.ae_hasDerivAt_integral] with x hx hx'
    rw [show Gt E = fun x => ∫ t in τlo..x, E.g t from rfl,
      (hx (uIoc_subset_uIcc hx') τlo (by simp)).deriv, mul_comm]
  have e2 : ∫ τ in τlo..τhi, deriv (fun s => m.U E s) τ * Gt E τ =
      ∫ τ in τlo..τhi, phi E m τ * Gt E τ := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [dU_ae E m hadm hIC hhi] with x hx hx'
    rw [hx hx']
  have h1 : Gt E τhi = 1 := E.g_total
  have h0 : Gt E τlo = 0 := by simp [Gt]
  have env := envelope E m hadm hIC hhi
  have hphi := phi_int E m hadm hIC
  have hsplit : ∫ τ in τlo..τhi, (1 - Gt E τ) * phi E m τ =
      (∫ τ in τlo..τhi, phi E m τ) - ∫ τ in τlo..τhi, phi E m τ * Gt E τ := by
    rw [← intervalIntegral.integral_sub hphi (hphi.mul_continuousOn (Gt_cont E))]
    congr 1; funext τ; ring
  rw [e1, ibp, e2, h1, h0, hsplit, env]
  ring

lemma F_mem (E : SeqEnv τlo τhi θlo θhi) {θ τ : ℝ} (hθ : θ ∈ Icc θlo θhi)
    (hτ : τ ∈ Icc τlo τhi) : E.F θ τ ∈ Icc (0 : ℝ) 1 := by
  have hfi := E.f_integrable τ hτ
  rw [E.F_eq τ hτ θ hθ]
  have hpos : ∀ x ∈ Icc θlo θhi, 0 ≤ E.f x τ := fun x hx => (E.f_pos x hx τ hτ).le
  constructor
  · apply intervalIntegral.integral_nonneg hθ.1
    intro x hx; exact hpos x ⟨hx.1, hx.2.trans hθ.2⟩
  · have s1 : uIcc θlo θ ⊆ uIcc θlo θhi := by
      rw [uIcc_of_le hθ.1, uIcc_of_le (hθ.1.trans hθ.2)]
      exact Icc_subset_Icc le_rfl hθ.2
    have s2 : uIcc θ θhi ⊆ uIcc θlo θhi := by
      rw [uIcc_of_le hθ.2, uIcc_of_le (hθ.1.trans hθ.2)]
      exact Icc_subset_Icc hθ.1 le_rfl
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hfi.mono_set s1)
      (hfi.mono_set s2)
    rw [E.f_total τ hτ] at hsplit
    have : 0 ≤ ∫ x in θ..θhi, E.f x τ := by
      apply intervalIntegral.integral_nonneg hθ.2
      intro x hx; exact hpos x ⟨hθ.1.trans hx.1, hx.2⟩
    linarith

/-- Fubini for the joint law. -/
lemma fub (E : SeqEnv τlo τhi θlo θhi) {h : ℝ → ℝ → ℝ}
    (hint : Integrable (fun p : ℝ × ℝ => E.g p.1 * E.f p.2 p.1 * h p.1 p.2)
      ((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi)))) :
    ∫ p, h p.1 p.2 ∂E.jointLaw =
      ∫ τ in τlo..τhi, ∫ θ in θlo..θhi, E.g τ * E.f θ τ * h τ θ := by
  have hmeas : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (E.g p.1 * E.f p.2 p.1) :=
    ENNReal.measurable_ofReal.comp ((E.g_measurable.comp measurable_fst).mul E.f_measurable)
  unfold SeqEnv.jointLaw
  rw [integral_withDensity_eq_integral_toReal_smul hmeas
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hR : MeasurableSet (typeRect τlo τhi θlo θhi) := measurableSet_Icc.prod measurableSet_Icc
  rw [setIntegral_congr_fun hR (g := fun p : ℝ × ℝ => E.g p.1 * E.f p.2 p.1 * h p.1 p.2)
    (fun p hp => by
      have h1 := E.g_pos p.1 hp.1
      have h2 := E.f_pos p.2 hp.2 p.1 hp.1
      simp only [smul_eq_mul]
      rw [ENNReal.toReal_ofReal (by positivity)])]
  rw [typeRect, Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hint,
    intervalIntegral.integral_of_le E.τlo_lt_τhi.le, ← integral_Icc_eq_integral_Ioc]
  congr 1; funext τ
  rw [intervalIntegral.integral_of_le E.θlo_lt_θhi.le, ← integral_Icc_eq_integral_Ioc]

lemma P_eq : ((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi)) : Measure (ℝ × ℝ)) =
    volume.restrict (Icc τlo τhi ×ˢ Icc θlo θhi) := by
  rw [Measure.prod_restrict, Measure.volume_eq_prod]

lemma aesm_rect {φ : ℝ → ℝ → ℝ}
    (hφ : Measurable (fun p : Icc τlo τhi × Icc θlo θhi => φ p.1 p.2)) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => φ p.1 p.2)
      ((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi))) := by
  rw [P_eq]
  apply AEMeasurable.aestronglyMeasurable
  apply aemeasurable_restrict_of_measurable_subtype (measurableSet_Icc.prod measurableSet_Icc)
  exact hφ.comp (MeasurableEquiv.Set.prod _ _).measurable

lemma gf_int0 (E : SeqEnv τlo τhi θlo θhi) :
    Integrable (fun p : ℝ × ℝ => E.g p.1 * E.f p.2 p.1)
      ((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi))) := by
  have hle := E.θlo_lt_θhi.le
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => E.g p.1 * E.f p.2 p.1)
      ((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi))) :=
    ((E.g_measurable.comp measurable_fst).mul E.f_measurable).aestronglyMeasurable
  rw [integrable_prod_iff hm]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hle).1 (E.f_integrable x hx)).const_mul _
  · have hg := (intervalIntegrable_iff_integrableOn_Icc_of_le E.τlo_lt_τhi.le).1 E.g_integrable
    refine hg.congr ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun x hx => ?_))
    have : ∫ y in Icc θlo θhi, ‖E.g x * E.f y x‖ = ∫ y in Icc θlo θhi, E.g x * E.f y x :=
      setIntegral_congr_fun measurableSet_Icc (fun y hy => by
        rw [Real.norm_eq_abs, abs_of_pos (mul_pos (E.g_pos x hx) (E.f_pos y hy x hx))])
    simp only
    rw [this, integral_const_mul, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
      E.f_total x hx, mul_one]

lemma gf_int (E : SeqEnv τlo τhi θlo θhi) {h : ℝ → ℝ → ℝ} {C : ℝ}
    (hm : AEStronglyMeasurable (fun p : ℝ × ℝ => h p.1 p.2)
      ((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi))))
    (hb : ∀ τ ∈ Icc τlo τhi, ∀ θ ∈ Icc θlo θhi, |h τ θ| ≤ C) :
    Integrable (fun p : ℝ × ℝ => E.g p.1 * E.f p.2 p.1 * h p.1 p.2)
      ((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi))) := by
  have := (gf_int0 E).bdd_mul hm (c := C) (by
    rw [P_eq]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    rw [Real.norm_eq_abs]; exact hb p.1 hp.1 p.2 hp.2)
  refine this.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only; ring

lemma t_bdd (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hadm : m.Admissible) (hIC : m.IsIC E) :
    ∃ C, ∀ τ ∈ Icc τlo τhi, ∀ θ ∈ Icc θlo θhi, |m.t τ θ| ≤ C := by
  have hle := E.θlo_lt_θhi.le
  have hlo : τlo ∈ Icc τlo τhi := ⟨le_rfl, E.τlo_lt_τhi.le⟩
  have hhiI : θhi ∈ Icc θlo θhi := ⟨hle, le_rfl⟩
  refine ⟨θhi + |m.U E τlo| + E.K * (θhi - θlo) * (τhi - τlo) + 2 * (θhi - θlo), ?_⟩
  intro τ hτ θ hθ
  have e1 : |m.u τ θ - m.u τ θhi| ≤ θhi - θlo :=
    calc _ ≤ |θ - θhi| := u_lip m hadm hIC.1 hτ hθ hhiI
      _ = θhi - θ := by rw [abs_sub_comm, abs_of_nonneg (by linarith [hθ.2])]
      _ ≤ θhi - θlo := by linarith [hθ.1]
  have e2 : |∫ x in θlo..θhi, m.q τ x * E.F x τ| ≤ 1 * |θhi - θlo| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := θlo) (b := θhi) (C := 1)
      (f := fun x => m.q τ x * E.F x τ) (fun x hx => by
        have hxI := mem_I_of_uIoc hle hx
        rw [Real.norm_eq_abs, abs_mul]
        have h1 := q_abs_le m hadm hτ hxI
        have h2 := F_mem E hxI hτ
        rw [abs_of_nonneg h2.1]
        nlinarith [abs_nonneg (m.q τ x), h2.1, h2.2])
    simpa [Real.norm_eq_abs] using this
  rw [one_mul, abs_of_nonneg (sub_nonneg.2 hle)] at e2
  have e3 := U_lip E m hadm hIC hτ hlo
  rw [abs_of_nonneg (sub_nonneg.2 hτ.1)] at e3
  have e3' : E.K * (θhi - θlo) * (τ - τlo) ≤ E.K * (θhi - θlo) * (τhi - τlo) :=
    mul_le_mul_of_nonneg_left (by linarith [hτ.2]) (mul_nonneg E.K_pos.le (sub_nonneg.2 hle))
  have e4 : m.U E τ = m.u τ θhi - ∫ x in θlo..θhi, m.q τ x * E.F x τ :=
    uhat_eq E m hadm hIC.1 hτ hτ
  have hq := hadm.1 τ hτ θ hθ
  have e5 : 0 ≤ θ * m.q τ θ := mul_nonneg (E.θlo_nonneg.trans hθ.1) hq.1
  have e6 : θ * m.q τ θ ≤ θhi := by nlinarith [hq.1, hq.2, hθ.1, hθ.2, E.θlo_nonneg]
  have ht : m.t τ θ = θ * m.q τ θ - m.u τ θ := by simp [DirectMechanism.u]
  rw [ht]
  rw [abs_le] at e1 e2 e3 ⊢
  have := abs_le.1 (le_refl |m.U E τlo|)
  constructor <;> linarith [neg_abs_le (m.U E τlo), le_abs_self (m.U E τlo)]

/-- `W = ψ g f` on the rectangle, written without division. -/
noncomputable def W (E : SeqEnv τlo τhi θlo θhi) (τ θ : ℝ) : ℝ :=
  θ * E.g τ * E.f θ τ + (1 - Gt E τ) * E.dFdτ θ τ

lemma Wq_inner (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hadm : m.Admissible) (hIC : m.IsIC E) {τ : ℝ} (hτ : τ ∈ Icc τlo τhi) :
    ∫ θ in θlo..θhi, W E τ θ * m.q τ θ =
      E.g τ * (∫ θ in θlo..θhi, θ * m.q τ θ * E.f θ τ) - (1 - Gt E τ) * phi E m τ := by
  have hle := E.θlo_lt_θhi.le
  have i1 : IntervalIntegrable (fun θ => θ * m.q τ θ * E.f θ τ) volume θlo θhi :=
    int_of_bdd (C := θhi) ((measurable_id.aestronglyMeasurable).mul (q_aesm m hIC.1 hτ hle))
      (fun x hx => by
        have hxI := mem_I_of_uIoc hle hx
        have hq := hadm.1 τ hτ x hxI
        rw [abs_of_nonneg (mul_nonneg (E.θlo_nonneg.trans hxI.1) hq.1)]
        nlinarith [hq.1, hq.2, hxI.1, hxI.2, E.θlo_nonneg]) (E.f_integrable τ hτ)
  have i2 : IntervalIntegrable (fun θ => m.q τ θ * E.dFdτ θ τ) volume θlo θhi := by
    have := int_of_bdd (C := E.K) (ψ := fun _ => (1 : ℝ))
      ((q_aesm m hIC.1 hτ hle).mul (dF_aesm E τ _)) (fun x hx => by
        have hxI := mem_I_of_uIoc hle hx
        show |m.q τ x * E.dFdτ x τ| ≤ E.K
        rw [abs_mul]
        have h1 := q_abs_le m hadm hτ hxI
        have h2 := (E.abs_dFdτ_lt x hxI τ hτ).le
        nlinarith [abs_nonneg (m.q τ x), abs_nonneg (E.dFdτ x τ)]) intervalIntegrable_const
    simpa using this
  have e : (fun θ => W E τ θ * m.q τ θ) =
      fun θ => E.g τ * (θ * m.q τ θ * E.f θ τ) + (1 - Gt E τ) * (m.q τ θ * E.dFdτ θ τ) := by
    funext θ; simp only [W]; ring
  rw [e, intervalIntegral.integral_add (i1.const_mul _) (i2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp only [phi]; ring

lemma gQU_inner (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hadm : m.Admissible) (hIC : m.IsIC E) {τ : ℝ} (hτ : τ ∈ Icc τlo τhi) :
    ∫ θ in θlo..θhi, E.g τ * E.f θ τ * m.t τ θ =
      E.g τ * (∫ θ in θlo..θhi, θ * m.q τ θ * E.f θ τ) - E.g τ * m.U E τ := by
  have hle := E.θlo_lt_θhi.le
  have i1 : IntervalIntegrable (fun θ => θ * m.q τ θ * E.f θ τ) volume θlo θhi :=
    int_of_bdd (C := θhi) ((measurable_id.aestronglyMeasurable).mul (q_aesm m hIC.1 hτ hle))
      (fun x hx => by
        have hxI := mem_I_of_uIoc hle hx
        have hq := hadm.1 τ hτ x hxI
        rw [abs_of_nonneg (mul_nonneg (E.θlo_nonneg.trans hxI.1) hq.1)]
        nlinarith [hq.1, hq.2, hxI.1, hxI.2, E.θlo_nonneg]) (E.f_integrable τ hτ)
  have i2 : IntervalIntegrable (fun θ => m.u τ θ * E.f θ τ) volume θlo θhi :=
    (E.f_integrable τ hτ).continuousOn_mul (u_lipOn m hadm hIC.1 hτ hle).continuousOn
  have e : (fun θ => E.g τ * E.f θ τ * m.t τ θ) =
      fun θ => E.g τ * (θ * m.q τ θ * E.f θ τ - m.u τ θ * E.f θ τ) := by
    funext θ; simp only [DirectMechanism.u]; ring
  rw [e, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub i1 i2]
  simp only [DirectMechanism.U, DirectMechanism.Uhat]; ring

lemma Wq_int (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hadm : m.Admissible) :
    Integrable (fun p : ℝ × ℝ => W E p.1 p.2 * m.q p.1 p.2)
      ((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi))) := by
  have hq := aesm_rect (φ := m.q) hadm.2.1
  have i1 := gf_int E (h := fun τ θ => θ * m.q τ θ) (C := θhi)
    (measurable_snd.aestronglyMeasurable.mul hq) (fun τ hτ θ hθ => by
      have hqq := hadm.1 τ hτ θ hθ
      rw [abs_of_nonneg (mul_nonneg (E.θlo_nonneg.trans hθ.1) hqq.1)]
      nlinarith [hqq.1, hqq.2, hθ.1, hθ.2, E.θlo_nonneg])
  have hG : Integrable (fun τ => 1 - Gt E τ) (volume.restrict (Icc τlo τhi)) := by
    have : ContinuousOn (fun τ => (1 : ℝ) - Gt E τ) (uIcc τlo τhi) :=
      continuousOn_const.sub (Gt_cont E)
    rw [uIcc_of_le E.τlo_lt_τhi.le] at this
    exact this.integrableOn_Icc
  have h1 : Integrable (fun p : ℝ × ℝ => (1 - Gt E p.1) * (1 : ℝ))
      ((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi))) :=
    hG.mul_prod (integrable_const (1 : ℝ))
  have i2 := h1.bdd_mul (c := E.K) (E.dFdτ_measurable.aestronglyMeasurable.mul hq) (by
    rw [P_eq]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    rw [Real.norm_eq_abs]
    show |E.dFdτ p.2 p.1 * m.q p.1 p.2| ≤ E.K
    rw [abs_mul]
    have a1 := q_abs_le m hadm hp.1 hp.2
    have a2 := (E.abs_dFdτ_lt p.2 hp.2 p.1 hp.1).le
    nlinarith [abs_nonneg (m.q p.1 p.2), abs_nonneg (E.dFdτ p.2 p.1)])
  refine (i1.add i2).congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [W, Pi.add_apply, Pi.mul_apply]; ring

lemma inner_int {φ : ℝ → ℝ → ℝ}
    (h : Integrable (fun p : ℝ × ℝ => φ p.1 p.2)
      ((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi))))
    (hτ : τlo ≤ τhi) (hθ : θlo ≤ θhi) :
    IntervalIntegrable (fun τ => ∫ θ in θlo..θhi, φ τ θ) volume τlo τhi := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ]
  refine h.integral_prod_left.congr (Filter.Eventually.of_forall fun τ => ?_)
  simp only
  rw [intervalIntegral.integral_of_le hθ, integral_Icc_eq_integral_Ioc]

/-- **K3** (revenue identity). -/
lemma revenue_eq (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hadm : m.Admissible) (hIC : m.IsIC E) :
    m.revenue E = (∫ τ in τlo..τhi, ∫ θ in θlo..θhi, W E τ θ * m.q τ θ) - m.U E τlo := by
  have hle := E.θlo_lt_θhi.le
  have hτle := E.τlo_lt_τhi.le
  have hhi : τhi ∈ Icc τlo τhi := ⟨hτle, le_rfl⟩
  obtain ⟨C, hC⟩ := t_bdd E m hadm hIC
  have hint := gf_int E (h := m.t) (aesm_rect hadm.2.2) hC
  have hA := inner_int (φ := fun τ θ => E.g τ * E.f θ τ * m.t τ θ) hint hτle hle
  have hB := inner_int (φ := fun τ θ => W E τ θ * m.q τ θ) (Wq_int E m hadm) hτle hle
  have hgU : IntervalIntegrable (fun τ => E.g τ * m.U E τ) volume τlo τhi :=
    E.g_integrable.mul_continuousOn (U_ac E m hadm hIC hhi).continuousOn
  have hGp : IntervalIntegrable (fun τ => (1 - Gt E τ) * phi E m τ) volume τlo τhi :=
    (phi_int E m hadm hIC).continuousOn_mul (continuousOn_const.sub (Gt_cont E))
  rw [DirectMechanism.revenue, fub E hint]
  have hdiff : (∫ τ in τlo..τhi, ∫ θ in θlo..θhi, E.g τ * E.f θ τ * m.t τ θ) -
      (∫ τ in τlo..τhi, ∫ θ in θlo..θhi, W E τ θ * m.q τ θ) =
      ∫ τ in τlo..τhi, ((1 - Gt E τ) * phi E m τ - E.g τ * m.U E τ) := by
    rw [← intervalIntegral.integral_sub hA hB]
    apply intervalIntegral.integral_congr
    intro τ hτ
    rw [uIcc_of_le hτle] at hτ
    simp only
    rw [gQU_inner E m hadm hIC hτ, Wq_inner E m hadm hIC hτ]
    ring
  rw [intervalIntegral.integral_sub hGp hgU, gU E m hadm hIC] at hdiff
  linarith

/-! ### Constant mechanisms and the closed forms of the optimal mechanism -/

/-- `M(τ) = ∫ θ f(θ|τ) dθ`. -/
noncomputable def M (E : SeqEnv τlo τhi θlo θhi) (τ : ℝ) : ℝ := ∫ θ in θlo..θhi, θ * E.f θ τ

/-- The constant mechanism `q ≡ 1`, `t ≡ c`. -/
def cmech (c : ℝ) : DirectMechanism τlo τhi θlo θhi := ⟨fun _ _ => 1, fun _ _ => c⟩

lemma cmech_adm (c : ℝ) : (cmech c : DirectMechanism τlo τhi θlo θhi).Admissible :=
  ⟨fun _ _ _ _ => ⟨zero_le_one, le_rfl⟩, measurable_const, measurable_const⟩

lemma cmech_IC (E : SeqEnv τlo τhi θlo θhi) (c : ℝ) :
    (cmech c : DirectMechanism τlo τhi θlo θhi).IsIC E :=
  ⟨fun _ _ _ _ _ _ => le_rfl, fun _ _ _ _ _ _ _ => le_rfl⟩

lemma fθ_int (E : SeqEnv τlo τhi θlo θhi) {τ : ℝ} (hτ : τ ∈ Icc τlo τhi) (a : ℝ) :
    IntervalIntegrable (fun θ => (θ - a) * E.f θ τ) volume θlo θhi :=
  (E.f_integrable τ hτ).continuousOn_mul (by fun_prop)

lemma Mθ (E : SeqEnv τlo τhi θlo θhi) {τ : ℝ} (hτ : τ ∈ Icc τlo τhi) (a : ℝ) :
    ∫ θ in θlo..θhi, (θ - a) * E.f θ τ = M E τ - a := by
  have h1 : IntervalIntegrable (fun θ => θ * E.f θ τ) volume θlo θhi :=
    (E.f_integrable τ hτ).continuousOn_mul (by fun_prop)
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub h1 ((E.f_integrable τ hτ).const_mul a),
    intervalIntegral.integral_const_mul, E.f_total τ hτ, mul_one]
  rfl

lemma cmech_U (E : SeqEnv τlo τhi θlo θhi) {c τ : ℝ} (hτ : τ ∈ Icc τlo τhi) :
    (cmech c : DirectMechanism τlo τhi θlo θhi).U E τ = M E τ - c := by
  show ∫ θ in θlo..θhi, (θ * 1 - c) * E.f θ τ = _
  simp only [mul_one]
  exact Mθ E hτ c

lemma Mdiff (E : SeqEnv τlo τhi θlo θhi) {τ : ℝ} (hτ : τ ∈ Icc τlo τhi) :
    M E τ - M E τlo = ∫ s in τlo..τ, -(∫ θ in θlo..θhi, E.dFdτ θ s) := by
  have hlo : τlo ∈ Icc τlo τhi := ⟨le_rfl, E.τlo_lt_τhi.le⟩
  have h := envelope E (cmech 0) (cmech_adm 0) (cmech_IC E 0) hτ
  rw [cmech_U E hτ, cmech_U E hlo] at h
  simp only [phi, cmech, one_mul] at h
  linarith

lemma M_mono (E : SeqEnv τlo τhi θlo θhi) {τ : ℝ} (hτ : τ ∈ Icc τlo τhi) :
    M E τlo ≤ M E τ := by
  have h := Mdiff E hτ
  have : 0 ≤ ∫ s in τlo..τ, -(∫ θ in θlo..θhi, E.dFdτ θ s) := by
    apply intervalIntegral.integral_nonneg hτ.1
    intro s hs
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_nonneg E.θlo_lt_θhi.le
    intro θ hθ
    exact neg_nonneg.2 (dFdτ_nonpos E hθ ⟨hs.1, hs.2.trans hτ.2⟩)
  linarith

lemma R1 (E : SeqEnv τlo τhi θlo θhi) :
    ∫ τ in τlo..τhi, ∫ θ in θlo..θhi, W E τ θ = M E τlo := by
  have hlo : τlo ∈ Icc τlo τhi := ⟨le_rfl, E.τlo_lt_τhi.le⟩
  have h := revenue_eq E (cmech 0) (cmech_adm 0) (cmech_IC E 0)
  have hr : (cmech 0 : DirectMechanism τlo τhi θlo θhi).revenue E = 0 := by
    simp [DirectMechanism.revenue, cmech]
  rw [hr, cmech_U E hlo] at h
  simp only [cmech, mul_one] at h
  linarith

lemma optTlo_eq (E : SeqEnv τlo τhi θlo θhi) (hA : E.Assumption11_1) :
    E.optTlo = M E τlo := by
  have hlo : τlo ∈ Icc τlo τhi := ⟨le_rfl, E.τlo_lt_τhi.le⟩
  unfold SeqEnv.optTlo
  rw [p_eq E hA hlo, F_lo E hlo, optQ_eq E hA hlo ⟨le_rfl, E.θlo_lt_θhi.le⟩]
  simp only [M]; ring

lemma optT0_eq (E : SeqEnv τlo τhi θlo θhi) (hA : E.Assumption11_1) {τ : ℝ}
    (hτ : τ ∈ Icc τlo τhi) : E.optT0 τ = M E τlo - θlo := by
  have hle := E.θlo_lt_θhi.le
  have hlo : τlo ∈ Icc τlo τhi := ⟨le_rfl, E.τlo_lt_τhi.le⟩
  unfold SeqEnv.optT0 SeqEnv.t0
  rw [optTlo_eq E hA, optQ_eq E hA hlo ⟨le_rfl, hle⟩]
  have h2 : (∫ τ' in τlo..τ, ∫ θ' in θlo..θhi, E.optQ τ' θ' * E.dFdτ θ' τ') =
      M E τlo - M E τ := by
    rw [intervalIntegral.integral_congr (g := fun τ' => ∫ θ' in θlo..θhi, E.dFdτ θ' τ') ?_]
    · have := Mdiff E hτ
      rw [intervalIntegral.integral_neg] at this
      linarith
    intro τ' hτ'
    rw [uIcc_of_le hτ.1] at hτ'
    have hτ'J : τ' ∈ Icc τlo τhi := ⟨hτ'.1, hτ'.2.trans hτ.2⟩
    apply intervalIntegral.integral_congr
    intro θ' hθ'
    rw [uIcc_of_le hle] at hθ'
    simp only [optQ_eq E hA hτ'J hθ', one_mul]
  have h3 : (∫ θ' in θlo..θhi, ∫ x in θlo..θ',
      (E.optQ τ x * E.f θ' τ - E.optQ τlo x * E.f θ' τlo)) = M E τ - M E τlo := by
    rw [intervalIntegral.integral_congr
      (g := fun θ' => (θ' - θlo) * E.f θ' τ - (θ' - θlo) * E.f θ' τlo) ?_]
    · rw [intervalIntegral.integral_sub (fθ_int E hτ θlo) (fθ_int E hlo θlo), Mθ E hτ, Mθ E hlo]
      ring
    intro θ' hθ'
    rw [uIcc_of_le hle] at hθ'
    simp only
    rw [intervalIntegral.integral_congr (g := fun _ => E.f θ' τ - E.f θ' τlo) ?_]
    · rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    intro x hx
    rw [uIcc_of_le hθ'.1] at hx
    have hxI : x ∈ Icc θlo θhi := ⟨hx.1, hx.2.trans hθ'.2⟩
    simp only [optQ_eq E hA hτ hxI, optQ_eq E hA hlo hxI, one_mul]
  rw [h2, h3]; ring

lemma optT_eq (E : SeqEnv τlo τhi θlo θhi) (hA : E.Assumption11_1) {τ θ : ℝ}
    (hτ : τ ∈ Icc τlo τhi) (hθ : θ ∈ Icc θlo θhi) : E.optT τ θ = M E τlo := by
  unfold SeqEnv.optT
  rw [p_eq E hA hτ, if_pos hθ.1, optT0_eq E hA hτ]; ring

lemma W_eq (E : SeqEnv τlo τhi θlo θhi) {τ θ : ℝ} (hτ : τ ∈ Icc τlo τhi)
    (hθ : θ ∈ Icc θlo θhi) : W E τ θ = E.g τ * E.f θ τ * E.ψ τ θ := by
  have hg := (E.g_pos τ hτ).ne'
  have hf := (E.f_pos θ hθ τ hτ).ne'
  simp only [W, SeqEnv.ψ]
  rw [show Gt E τ = E.G τ from (E.G_eq τ hτ).symm]
  field_simp

lemma W_nonneg (E : SeqEnv τlo τhi θlo θhi) (hA : E.Assumption11_1) {τ θ : ℝ}
    (hτ : τ ∈ Icc τlo τhi) (hθ : θ ∈ Icc θlo θhi) : 0 ≤ W E τ θ := by
  rw [W_eq E hτ hθ]
  exact mul_nonneg (mul_pos (E.g_pos τ hτ) (E.f_pos θ hθ τ hτ)).le
    (E.θlo_nonneg.trans (psi_ge E hA hτ hθ))

lemma Wq_iint (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hadm : m.Admissible) (hIC : m.IsIC E) {τ : ℝ} (hτ : τ ∈ Icc τlo τhi) :
    IntervalIntegrable (fun θ => W E τ θ * m.q τ θ) volume θlo θhi := by
  have hle := E.θlo_lt_θhi.le
  have i1 : IntervalIntegrable (fun θ => θ * m.q τ θ * E.f θ τ) volume θlo θhi :=
    int_of_bdd (C := θhi) ((measurable_id.aestronglyMeasurable).mul (q_aesm m hIC.1 hτ hle))
      (fun x hx => by
        have hxI := mem_I_of_uIoc hle hx
        have hq := hadm.1 τ hτ x hxI
        rw [abs_of_nonneg (mul_nonneg (E.θlo_nonneg.trans hxI.1) hq.1)]
        nlinarith [hq.1, hq.2, hxI.1, hxI.2, E.θlo_nonneg]) (E.f_integrable τ hτ)
  have i2 : IntervalIntegrable (fun θ => m.q τ θ * E.dFdτ θ τ) volume θlo θhi := by
    have := int_of_bdd (C := E.K) (ψ := fun _ => (1 : ℝ))
      ((q_aesm m hIC.1 hτ hle).mul (dF_aesm E τ _)) (fun x hx => by
        have hxI := mem_I_of_uIoc hle hx
        show |m.q τ x * E.dFdτ x τ| ≤ E.K
        rw [abs_mul]
        have h1 := q_abs_le m hadm hτ hxI
        have h2 := (E.abs_dFdτ_lt x hxI τ hτ).le
        nlinarith [abs_nonneg (m.q τ x), abs_nonneg (E.dFdτ x τ)]) intervalIntegrable_const
    simpa using this
  have e : (fun θ => W E τ θ * m.q τ θ) =
      fun θ => E.g τ * (θ * m.q τ θ * E.f θ τ) + (1 - Gt E τ) * (m.q τ θ * E.dFdτ θ τ) := by
    funext θ; simp only [W]; ring
  rw [e]
  exact (i1.const_mul _).add (i2.const_mul _)

lemma W_iint (E : SeqEnv τlo τhi θlo θhi) {τ : ℝ} (hτ : τ ∈ Icc τlo τhi) :
    IntervalIntegrable (fun θ => W E τ θ) volume θlo θhi := by
  simpa [cmech] using Wq_iint E (cmech 0) (cmech_adm 0) (cmech_IC E 0) hτ

lemma W_int (E : SeqEnv τlo τhi θlo θhi) :
    Integrable (fun p : ℝ × ℝ => W E p.1 p.2)
      ((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi))) := by
  simpa [cmech] using Wq_int E (cmech 0 : DirectMechanism τlo τhi θlo θhi) (cmech_adm 0)

lemma R_le (E : SeqEnv τlo τhi θlo θhi) (hA : E.Assumption11_1)
    (m : DirectMechanism τlo τhi θlo θhi) (hadm : m.Admissible) (hIC : m.IsIC E) :
    ∫ τ in τlo..τhi, ∫ θ in θlo..θhi, W E τ θ * m.q τ θ ≤ M E τlo := by
  have hle := E.θlo_lt_θhi.le
  have hτle := E.τlo_lt_τhi.le
  rw [← R1 E]
  apply intervalIntegral.integral_mono_on hτle
    (inner_int (φ := fun τ θ => W E τ θ * m.q τ θ) (Wq_int E m hadm) hτle hle)
    (inner_int (φ := fun τ θ => W E τ θ) (W_int E) hτle hle)
  intro τ hτ
  apply intervalIntegral.integral_mono_on hle (Wq_iint E m hadm hIC hτ) (W_iint E hτ)
  intro θ hθ
  exact mul_le_of_le_one_right (W_nonneg E hA hτ hθ) (hadm.1 τ hτ θ hθ).2

/-- Item 2 core: a mechanism equal to `(q*, t*)` on the rectangle. -/
lemma opt_of_eq (E : SeqEnv τlo τhi θlo θhi) (hA : E.Assumption11_1)
    (m : DirectMechanism τlo τhi θlo θhi) (hadm : m.Admissible)
    (hrect : ∀ τ ∈ Icc τlo τhi, ∀ θ ∈ Icc θlo θhi,
      m.q τ θ = E.optQ τ θ ∧ m.t τ θ = E.optT τ θ) :
    m.IsIC E ∧ m.IsIR E ∧ m.IsOptimal E ∧ m.revenue E = M E τlo := by
  have hle := E.θlo_lt_θhi.le
  have hlo : τlo ∈ Icc τlo τhi := ⟨le_rfl, E.τlo_lt_τhi.le⟩
  have hq : ∀ τ ∈ Icc τlo τhi, ∀ θ ∈ Icc θlo θhi, m.q τ θ = 1 := fun τ hτ θ hθ =>
    (hrect τ hτ θ hθ).1.trans (optQ_eq E hA hτ hθ)
  have ht : ∀ τ ∈ Icc τlo τhi, ∀ θ ∈ Icc θlo θhi, m.t τ θ = M E τlo := fun τ hτ θ hθ =>
    (hrect τ hτ θ hθ).2.trans (optT_eq E hA hτ hθ)
  have hU : ∀ τ ∈ Icc τlo τhi, m.U E τ = M E τ - M E τlo := by
    intro τ hτ
    show ∫ θ in θlo..θhi, (θ * m.q τ θ - m.t τ θ) * E.f θ τ = _
    rw [intervalIntegral.integral_congr (g := fun θ => (θ - M E τlo) * E.f θ τ) ?_, Mθ E hτ]
    intro θ hθ
    rw [uIcc_of_le hle] at hθ
    simp only [hq τ hτ θ hθ, ht τ hτ θ hθ, mul_one]
  have hIC : m.IsIC E := by
    refine ⟨fun τ hτ θ hθ θ' hθ' => ?_, fun τ hτ τ' hτ' θr _ hθr => ?_⟩
    · simp only [DirectMechanism.u, hq τ hτ θ hθ, hq τ hτ θ' hθ', ht τ hτ θ hθ, ht τ hτ θ' hθ',
        le_refl]
    · rw [hU τ hτ, intervalIntegral.integral_congr (g := fun θ => (θ - M E τlo) * E.f θ τ) ?_,
        Mθ E hτ]
      intro θ hθ
      rw [uIcc_of_le hle] at hθ
      simp only [hq τ' hτ' _ (hθr θ hθ), ht τ' hτ' _ (hθr θ hθ), mul_one]
  have hIR : m.IsIR E := fun τ hτ => by rw [hU τ hτ]; linarith [M_mono E hτ]
  have hWq : ∫ τ in τlo..τhi, ∫ θ in θlo..θhi, W E τ θ * m.q τ θ =
      ∫ τ in τlo..τhi, ∫ θ in θlo..θhi, W E τ θ := by
    apply intervalIntegral.integral_congr
    intro τ hτ
    rw [uIcc_of_le E.τlo_lt_τhi.le] at hτ
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le hle] at hθ
    simp only [hq τ hτ θ hθ, mul_one]
  have hrev : m.revenue E = M E τlo := by
    rw [revenue_eq E m hadm hIC, hU τlo hlo, hWq, R1 E]; ring
  refine ⟨hIC, hIR, ⟨hadm, hIC, hIR, fun m' ha' hi' hr' => ?_⟩, hrev⟩
  rw [hrev, revenue_eq E m' ha' hi']
  have := R_le E hA m' ha' hi'
  have := hr' τlo hlo
  linarith

lemma exists_opt (E : SeqEnv τlo τhi θlo θhi) (hA : E.Assumption11_1) :
    ∃ m : DirectMechanism τlo τhi θlo θhi, m.Admissible ∧
      ∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi,
        m.q τ θ = E.optQ τ θ ∧ m.t τ θ = E.optT τ θ :=
  ⟨cmech (M E τlo), cmech_adm _, fun τ hτ θ hθ =>
    ⟨(optQ_eq E hA hτ hθ).symm, (optT_eq E hA hτ hθ).symm⟩⟩

/-! ### Almost-everywhere characterisations (items 3 and 4) -/

lemma iter {φ : ℝ → ℝ → ℝ}
    (h : Integrable (fun p : ℝ × ℝ => φ p.1 p.2)
      ((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi))))
    (hτ : τlo ≤ τhi) (hθ : θlo ≤ θhi) :
    ∫ p, φ p.1 p.2 ∂((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi))) =
      ∫ τ in τlo..τhi, ∫ θ in θlo..θhi, φ τ θ := by
  rw [integral_prod _ h, intervalIntegral.integral_of_le hτ, ← integral_Icc_eq_integral_Ioc]
  congr 1; funext τ
  rw [intervalIntegral.integral_of_le hθ, ← integral_Icc_eq_integral_Ioc]

lemma aeP_rect :
    ∀ᵐ p ∂((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi))),
      p ∈ Icc τlo τhi ×ˢ Icc θlo θhi := by
  rw [P_eq]; exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)

lemma J_ac (E : SeqEnv τlo τhi θlo θhi) :
    E.jointLaw ≪ (volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi)) := by
  rw [P_eq]; unfold SeqEnv.jointLaw typeRect; exact withDensity_absolutelyContinuous _ _

lemma P_ac (E : SeqEnv τlo τhi θlo θhi) :
    (volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi)) ≪ E.jointLaw := by
  rw [P_eq]; unfold SeqEnv.jointLaw typeRect
  apply withDensity_absolutelyContinuous'
  · exact (ENNReal.measurable_ofReal.comp
      ((E.g_measurable.comp measurable_fst).mul E.f_measurable)).aemeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    exact (ENNReal.ofReal_pos.2 (mul_pos (E.g_pos p.1 hp.1) (E.f_pos p.2 hp.2 p.1 hp.1))).ne'

lemma gap (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hadm : m.Admissible) :
    Integrable (fun p : ℝ × ℝ => W E p.1 p.2 * (1 - m.q p.1 p.2))
      ((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi))) ∧
    ∫ p, W E p.1 p.2 * (1 - m.q p.1 p.2)
        ∂((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi))) =
      M E τlo - ∫ τ in τlo..τhi, ∫ θ in θlo..θhi, W E τ θ * m.q τ θ := by
  have hle := E.θlo_lt_θhi.le
  have hτle := E.τlo_lt_τhi.le
  refine ⟨((W_int E).sub (Wq_int E m hadm)).congr (Filter.Eventually.of_forall fun p => by
    simp only [Pi.sub_apply]; ring), ?_⟩
  have e1 : (∫ p, W E p.1 p.2
      ∂((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi)))) =
      ∫ τ in τlo..τhi, ∫ θ in θlo..θhi, W E τ θ :=
    iter (φ := fun τ θ => W E τ θ) (W_int E) hτle hle
  have e2 : (∫ p, W E p.1 p.2 * m.q p.1 p.2
      ∂((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi)))) =
      ∫ τ in τlo..τhi, ∫ θ in θlo..θhi, W E τ θ * m.q τ θ :=
    iter (φ := fun τ θ => W E τ θ * m.q τ θ) (Wq_int E m hadm) hτle hle
  have e3 : ∫ p, W E p.1 p.2 * (1 - m.q p.1 p.2)
        ∂((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi))) =
      (∫ p, W E p.1 p.2
        ∂((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi)))) -
      ∫ p, W E p.1 p.2 * m.q p.1 p.2
        ∂((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi))) := by
    rw [← integral_sub (W_int E) (Wq_int E m hadm)]
    congr 1; funext p; ring
  rw [e3, e1, e2, R1 E]

/-- **Item 3**. -/
lemma opt_iff (E : SeqEnv τlo τhi θlo θhi) (hA : E.Assumption11_1)
    (m : DirectMechanism τlo τhi θlo θhi) (hadm : m.Admissible) (hIC : m.IsIC E)
    (hIR : m.IsIR E) :
    m.IsOptimal E ↔
      (∀ᵐ p ∂E.jointLaw, E.ψ p.1 p.2 ≠ 0 → m.q p.1 p.2 = E.optQ p.1 p.2) ∧
        m.U E τlo = 0 := by
  have hlo : τlo ∈ Icc τlo τhi := ⟨le_rfl, E.τlo_lt_τhi.le⟩
  obtain ⟨hi, hgap⟩ := gap E m hadm
  have hrev : m.revenue E = M E τlo - (∫ p, W E p.1 p.2 * (1 - m.q p.1 p.2)
      ∂((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi)))) - m.U E τlo := by
    rw [revenue_eq E m hadm hIC, hgap]; ring
  have hnn : 0 ≤ᵐ[(volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi))]
      fun p : ℝ × ℝ => W E p.1 p.2 * (1 - m.q p.1 p.2) := by
    filter_upwards [aeP_rect] with p hp
    show 0 ≤ W E p.1 p.2 * (1 - m.q p.1 p.2)
    exact mul_nonneg (W_nonneg E hA hp.1 hp.2) (sub_nonneg.2 (hadm.1 p.1 hp.1 p.2 hp.2).2)
  have hU0 := hIR τlo hlo
  obtain ⟨ms, hsa, hsr⟩ := exists_opt E hA
  obtain ⟨hsIC, hsIR, -, hsrev⟩ := opt_of_eq E hA ms hsa hsr
  constructor
  · intro hopt
    have h1 := hopt.2.2.2 ms hsa hsIC hsIR
    rw [hsrev, hrev] at h1
    have hG0 : 0 ≤ ∫ p, W E p.1 p.2 * (1 - m.q p.1 p.2)
        ∂((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi))) :=
      integral_nonneg_of_ae hnn
    have hG : ∫ p, W E p.1 p.2 * (1 - m.q p.1 p.2)
        ∂((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi))) = 0 := by
      linarith
    refine ⟨?_, by linarith⟩
    have h0 := (integral_eq_zero_iff_of_nonneg_ae hnn hi).1 hG
    filter_upwards [(J_ac E).ae_le h0, (J_ac E).ae_le aeP_rect] with p h1 h2 hψ
    have h1' : W E p.1 p.2 * (1 - m.q p.1 p.2) = 0 := h1
    rw [W_eq E h2.1 h2.2] at h1'
    rw [optQ_eq E hA h2.1 h2.2]
    rcases mul_eq_zero.1 h1' with h | h
    · exact absurd h (mul_ne_zero (mul_ne_zero (E.g_pos p.1 h2.1).ne'
        (E.f_pos p.2 h2.2 p.1 h2.1).ne') hψ)
    · linarith
  · rintro ⟨hae, hU⟩
    have hG : ∫ p, W E p.1 p.2 * (1 - m.q p.1 p.2)
        ∂((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi))) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [(P_ac E).ae_le hae, aeP_rect] with p h1 h2
      show W E p.1 p.2 * (1 - m.q p.1 p.2) = 0
      by_cases hψ : E.ψ p.1 p.2 = 0
      · rw [W_eq E h2.1 h2.2, hψ]; ring
      · rw [h1 hψ, optQ_eq E hA h2.1 h2.2]; ring
    refine ⟨hadm, hIC, hIR, fun m' ha' hi' hr' => ?_⟩
    rw [hrev, hG, hU, revenue_eq E m' ha' hi']
    have := R_le E hA m' ha' hi'
    have := hr' τlo hlo
    linarith

lemma t_of_good (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hadm : m.Admissible) (hIC : m.IsIC E)
    (hg2 : ∀ᵐ s ∂volume, s ∈ Icc τlo τhi →
      ∀ᵐ θ ∂(volume.restrict (Icc θlo θhi)), m.q s θ = 1)
    {τ : ℝ} (hτ : τ ∈ Icc τlo τhi)
    (hτg : ∀ᵐ θ ∂(volume.restrict (Icc θlo θhi)), m.q τ θ = 1)
    {θ : ℝ} (hθ : θ ∈ Icc θlo θhi) (hq : m.q τ θ = 1) :
    m.t τ θ = M E τlo - m.U E τlo := by
  have hle := E.θlo_lt_θhi.le
  have hlo : τlo ∈ Icc τlo τhi := ⟨le_rfl, E.τlo_lt_τhi.le⟩
  have qI : ∀ s, (∀ᵐ θ ∂(volume.restrict (Icc θlo θhi)), m.q s θ = 1) →
      ∀ᵐ θ ∂volume, θ ∈ Ι θlo θhi → m.q s θ = 1 := by
    intro s hs
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 hs] with x h hx
    exact h (mem_I_of_uIoc hle hx)
  have hqF : ∫ x in θlo..θhi, m.q τ x * E.F x τ = θhi - M E τ := by
    have h0 : M E τ - 0 = θhi * 1 - 0 - ∫ x in θlo..θhi, 1 * E.F x τ := by
      rw [← cmech_U E hτ]
      exact uhat_eq E (cmech 0) (cmech_adm 0) (cmech_IC E 0).1 hτ hτ
    rw [intervalIntegral.integral_congr_ae (g := fun x => 1 * E.F x τ)
      ((qI τ hτg).mono fun x h hx => by rw [h hx])]
    linarith
  have hUd : m.U E τ - m.U E τlo = M E τ - M E τlo := by
    have e1 := envelope E m hadm hIC hτ
    have e2 := envelope E (cmech 0) (cmech_adm 0) (cmech_IC E 0) hτ
    rw [cmech_U E hτ, cmech_U E hlo] at e2
    have e3 : ∫ s in τlo..τ, phi E m s = ∫ s in τlo..τ, phi E (cmech 0) s := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hg2] with s h hs
      rw [uIoc_of_le hτ.1] at hs
      have hsJ : s ∈ Icc τlo τhi := ⟨hs.1.le, hs.2.trans hτ.2⟩
      simp only [phi]
      congr 1
      apply intervalIntegral.integral_congr_ae
      filter_upwards [qI s (h hsJ)] with x hx hx'
      simp only [hx hx', cmech]
    linarith
  have hθhi : θhi ∈ Icc θlo θhi := ⟨hle, le_rfl⟩
  have hu : m.u τ θ = m.u τ θhi - (θhi - θ) := by
    have hac : AbsolutelyContinuousOnInterval (fun x => m.u τ x) θ θhi :=
      ((u_lipOn m hadm hIC.1 hτ hle).mono (uIcc_subset_uIcc
        (by rw [uIcc_of_le hle]; exact hθ)
        (by rw [uIcc_of_le hle]; exact hθhi))).absolutelyContinuousOnInterval
    have hft := hac.integral_deriv_eq_sub
    have hne : ∀ᵐ x ∂volume, x ≠ θhi := by rw [ae_iff]; simp
    have e : ∫ x in θ..θhi, deriv (fun x => m.u τ x) x = ∫ x in θ..θhi, (1 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hac.ae_differentiableAt, hne, qI τ hτg] with x hx hxne hq1 hx'
      rw [uIoc_of_le hθ.2] at hx'
      have hxI : x ∈ Ioo θlo θhi := ⟨lt_of_le_of_lt hθ.1 hx'.1, lt_of_le_of_ne hx'.2 hxne⟩
      have hxd := (hx (by rw [uIcc_of_le hθ.2]; exact ⟨hx'.1.le, hx'.2⟩)).hasDerivAt
      rw [deriv_u m hIC.1 hτ hxI hxd]
      exact hq1 (by rw [uIoc_of_le hle]; exact ⟨hxI.1, hxI.2.le⟩)
    rw [e, intervalIntegral.integral_const, smul_eq_mul, mul_one] at hft
    linarith
  have hUτ : m.U E τ = m.u τ θhi - ∫ x in θlo..θhi, m.q τ x * E.F x τ :=
    uhat_eq E m hadm hIC.1 hτ hτ
  have ht : m.t τ θ = θ * m.q τ θ - m.u τ θ := by simp [DirectMechanism.u]
  rw [ht, hu, hq]
  rw [hqF] at hUτ
  linarith

lemma t_ae (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hadm : m.Admissible) (hIC : m.IsIC E)
    (hq1 : ∀ᵐ p ∂((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi))),
      m.q p.1 p.2 = 1) :
    ∀ᵐ p ∂((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi))),
      m.t p.1 p.2 = M E τlo - m.U E τlo := by
  have hgood := Measure.ae_ae_of_ae_prod hq1
  have hg2 := (ae_restrict_iff' measurableSet_Icc).1 hgood
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Icc τlo τhi))
    (ν := volume.restrict (Icc θlo θhi))).ae hgood, aeP_rect, hq1] with p hp hr hq
  exact t_of_good E m hadm hIC hg2 hr.1 hp hr.2 hq

lemma P_ne (E : SeqEnv τlo τhi θlo θhi) :
    (volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi)) ≠
      (0 : Measure (ℝ × ℝ)) := by
  intro h0
  have := congrArg (fun μ : Measure (ℝ × ℝ) => μ univ) h0
  simp only [Measure.coe_zero, Pi.zero_apply] at this
  rw [← Set.univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ,
    Measure.restrict_apply_univ, Real.volume_Icc, Real.volume_Icc] at this
  exact mul_ne_zero (ENNReal.ofReal_pos.2 (sub_pos.2 E.τlo_lt_τhi)).ne'
    (ENNReal.ofReal_pos.2 (sub_pos.2 E.θlo_lt_θhi)).ne' this

/-- **Item 4**. -/
lemma opt_iff4 (E : SeqEnv τlo τhi θlo θhi) (hA : E.Assumption11_1)
    (hnull : E.jointLaw {p | E.ψ p.1 p.2 = 0} = 0)
    (m : DirectMechanism τlo τhi θlo θhi) (hadm : m.Admissible) (hIC : m.IsIC E)
    (hIR : m.IsIR E) :
    m.IsOptimal E ↔ (∀ᵐ p ∂E.jointLaw, m.q p.1 p.2 = E.optQ p.1 p.2) ∧
      ∀ᵐ p ∂E.jointLaw, m.t p.1 p.2 = E.optT p.1 p.2 := by
  have hψ : ∀ᵐ p ∂E.jointLaw, E.ψ p.1 p.2 ≠ 0 := by
    rw [ae_iff]; simpa only [ne_eq, not_not] using hnull
  have hq1 : (∀ᵐ p ∂E.jointLaw, m.q p.1 p.2 = E.optQ p.1 p.2) →
      ∀ᵐ p ∂((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi))),
        m.q p.1 p.2 = 1 := fun h => by
    filter_upwards [(P_ac E).ae_le h, aeP_rect] with p h1 h2
    rw [h1, optQ_eq E hA h2.1 h2.2]
  rw [opt_iff E hA m hadm hIC hIR]
  constructor
  · rintro ⟨hae, hU⟩
    have hq : ∀ᵐ p ∂E.jointLaw, m.q p.1 p.2 = E.optQ p.1 p.2 := by
      filter_upwards [hae, hψ] with p h1 h2 using h1 h2
    refine ⟨hq, ?_⟩
    filter_upwards [(J_ac E).ae_le (t_ae E m hadm hIC (hq1 hq)), (J_ac E).ae_le aeP_rect]
      with p h1 h2
    rw [h1, hU, optT_eq E hA h2.1 h2.2]; ring
  · rintro ⟨hq, ht⟩
    refine ⟨by filter_upwards [hq] with p h _ using h, ?_⟩
    have := ae_neBot.2 (P_ne E)
    have ht' : ∀ᵐ p ∂((volume.restrict (Icc τlo τhi)).prod (volume.restrict (Icc θlo θhi))),
        m.t p.1 p.2 = E.optT p.1 p.2 := (P_ac E).ae_le ht
    obtain ⟨p, h1, h2, h3⟩ :=
      ((t_ae E m hadm hIC (hq1 hq)).and (ht'.and aeP_rect)).exists
    rw [h2, optT_eq E hA h3.1 h3.2] at h1
    linarith

end MechanismDesign.Dynamic.SSAux

open MechanismDesign.Dynamic in
theorem solution {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (hA : E.Assumption11_1) :
    (∃ m : DirectMechanism τlo τhi θlo θhi, m.Admissible ∧
      ∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi,
        m.q τ θ = E.optQ τ θ ∧ m.t τ θ = E.optT τ θ) ∧
    (∀ m : DirectMechanism τlo τhi θlo θhi, m.Admissible →
      (∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi,
        m.q τ θ = E.optQ τ θ ∧ m.t τ θ = E.optT τ θ) →
      m.IsIC E ∧ m.IsIR E ∧ m.IsOptimal E) ∧
    (∀ m : DirectMechanism τlo τhi θlo θhi, m.Admissible → m.IsIC E → m.IsIR E →
      (m.IsOptimal E ↔
        (∀ᵐ p ∂E.jointLaw, E.ψ p.1 p.2 ≠ 0 → m.q p.1 p.2 = E.optQ p.1 p.2) ∧
          m.U E τlo = 0)) ∧
    (E.jointLaw {p | E.ψ p.1 p.2 = 0} = 0 →
      ∀ m : DirectMechanism τlo τhi θlo θhi, m.Admissible → m.IsIC E → m.IsIR E →
        (m.IsOptimal E ↔
          (∀ᵐ p ∂E.jointLaw, m.q p.1 p.2 = E.optQ p.1 p.2) ∧
            ∀ᵐ p ∂E.jointLaw, m.t p.1 p.2 = E.optT p.1 p.2)) := by
  refine ⟨SSAux.exists_opt E hA, fun m hadm hrect => ?_,
    fun m hadm hIC hIR => SSAux.opt_iff E hA m hadm hIC hIR,
    fun hnull m hadm hIC hIR => SSAux.opt_iff4 E hA hnull m hadm hIC hIR⟩
  obtain ⟨h1, h2, h3, -⟩ := SSAux.opt_of_eq E hA m hadm hrect
  exact ⟨h1, h2, h3⟩
