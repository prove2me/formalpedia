-- Prove2me | solution 1 for OAI.CrouzeixHilbert.Conformal.riemann_biholomorphic_bounded
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:42:58.761615+00:00
-- url     : https://prove2.me/submissions/7eeb4897-8c10-4d7b-b265-35d352e18fe4

import Mathlib
import Definitions.Def_OAIQWCH000
import Theorems.Thm_MilnorDynamics_locally_bounded_holomorphic_subseq_locally_uniform
import Theorems.Thm_OAI_CrouzeixHilbert_Conformal_injOn_of_tendstoLocallyUniformlyOn

section
-- module Solutions.OAIQW_CrouzeixHilbert.DiskAutomorphism
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disk Automorphism. -/

noncomputable section

open Set Filter Metric Topology Function

open scoped ComplexConjugate

namespace CrouzeixHilbert.Conformal

theorem diskShift_den_ne {w z : ℂ} (hw : ‖w‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - conj w * z ≠ 0 := by
  intro h
  have he : conj w * z = 1 := (sub_eq_zero.mp h).symm
  have hn : ‖conj w * z‖ < 1 := by
    calc
      ‖conj w * z‖ = ‖w‖ * ‖z‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ < 1 := by simpa using hw
  simp [he] at hn

theorem diskShift_norm_identity (w z : ℂ) :
    ‖1 - conj w * z‖ ^ 2 - ‖z - w‖ ^ 2 = (1 - ‖w‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem diskShift_into_disk {w z : ℂ} (hw : ‖w‖ < 1) (hz : ‖z‖ < 1) :
    ‖diskShift w z‖ < 1 := by
  have hpos : 0 < (1 - ‖w‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
    apply mul_pos <;> nlinarith [norm_nonneg w, norm_nonneg z]
  rw [diskShift, norm_div, div_lt_one₀ (norm_pos_iff.mpr (diskShift_den_ne hw hz.le))]
  have := diskShift_norm_identity w z
  nlinarith [norm_nonneg (1 - conj w * z), norm_nonneg (z - w)]

theorem diskShift_eq_zero_iff {w z : ℂ} (hw : ‖w‖ < 1) (hz : ‖z‖ ≤ 1) :
    diskShift w z = 0 ↔ z = w := by
  simp [diskShift, div_eq_zero_iff, diskShift_den_ne hw hz, sub_eq_zero]

theorem diskShift_injOn {w : ℂ} (hw : ‖w‖ < 1) :
    InjOn (diskShift w) (closedBall 0 1) := by
  intro z hz v hv he
  have hz' : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
  have hv' : ‖v‖ ≤ 1 := mem_closedBall_zero_iff.mp hv
  have hm : w * conj w ≠ 1 := by
    intro he'
    have hh := congrArg norm he'
    rw [norm_mul, Complex.norm_conj, norm_one] at hh
    nlinarith [norm_nonneg w]
  have he' := (div_eq_div_iff (diskShift_den_ne hw hz') (diskShift_den_ne hw hv')).mp he
  have hh : (z - v) * (1 - w * conj w) = 0 := by linear_combination he'
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hm.symm))

theorem hasDerivAt_diskShift {w z : ℂ} (hw : ‖w‖ < 1) (hz : ‖z‖ ≤ 1) :
    HasDerivAt (diskShift w) ((1 - conj w * w) / (1 - conj w * z) ^ 2) z := by
  convert! ((hasDerivAt_id z).sub_const w).div
    ((hasDerivAt_const z 1).sub ((hasDerivAt_id z).const_mul (conj w)))
    (diskShift_den_ne hw hz) using 1
  congr 1
  dsimp
  ring

theorem norm_deriv_diskShift_zero {w : ℂ} (hw : ‖w‖ < 1) :
    ‖deriv (diskShift w) 0‖ = 1 - ‖w‖ ^ 2 := by
  rw [(hasDerivAt_diskShift hw (by simp : ‖(0 : ℂ)‖ ≤ 1)).deriv]
  simp only [mul_zero, sub_zero, one_pow, div_one]
  rw [mul_comm (conj w) w, Complex.mul_conj, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Complex.normSq_eq_norm_sq, abs_of_pos]
  nlinarith [norm_nonneg w]

theorem norm_deriv_diskShift_self {w : ℂ} (hw : ‖w‖ < 1) :
    ‖deriv (diskShift w) w‖ = (1 - ‖w‖ ^ 2)⁻¹ := by
  rw [(hasDerivAt_diskShift hw hw.le).deriv]
  have he : (1 - conj w * w) / (1 - conj w * w) ^ 2 = (1 - conj w * w)⁻¹ := by
    field_simp
  rw [he, norm_inv]
  congr 1
  rw [mul_comm (conj w) w, Complex.mul_conj, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Complex.normSq_eq_norm_sq, abs_of_pos]
  nlinarith [norm_nonneg w]

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Montel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Montel. -/

noncomputable section

open Set Filter Metric Topology Function

namespace CrouzeixHilbert.Conformal

theorem norm_deriv_le_on_half_ball {f : ℂ → ℂ} {U : Set ℂ}
    (_hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hb : ∀ z ∈ U, ‖f z‖ ≤ 1) {x : ℂ} {R : ℝ} (hR : 0 < R)
    (hRU : ball x R ⊆ U) {y : ℂ} (hy : y ∈ ball x (R / 2)) :
    ‖deriv f y‖ ≤ 1 / (R / 2) := by
  have hsub : closedBall y (R / 2) ⊆ U := by
    intro z hz
    apply hRU
    have hy' : dist y x < R / 2 := hy
    have hz' : dist z y ≤ R / 2 := hz
    exact (dist_triangle z y x).trans_lt (by linarith)
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
  · exact (hf.mono (by simpa [closure_ball _ (by positivity : R / 2 ≠ 0)] using hsub)).diffContOnCl
  · exact fun z hz => hb z (hsub (sphere_subset_closedBall hz))

theorem montel {U : Set ℂ} (hU : IsOpen U) (F : ℕ → ℂ → ℂ)
    (hd : ∀ n, DifferentiableOn ℂ (F n) U)
    (hb : ∀ n z, z ∈ U → ‖F n z‖ ≤ 1) :
    ∃ (f : ℂ → ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (F ∘ φ) f atTop U ∧
      DifferentiableOn ℂ f U ∧ ∀ z ∈ U, ‖f z‖ ≤ 1 := by
  obtain ⟨φ, hφ, g, -, hconv⟩ :=
    MilnorDynamics.locally_bounded_holomorphic_subseq_locally_uniform U hU F hd
      (fun K hK _ => ⟨1, fun n z hz => hb n z (hK hz)⟩)
  refine ⟨g, φ, hφ, hconv, hconv.differentiableOn (Eventually.of_forall (fun n => hd (φ n))) hU, ?_⟩
  intro z hz
  exact le_of_tendsto' (hconv.tendsto_at hz).norm (fun n => hb (φ n) z hz)

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Riemann
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Riemann. -/

noncomputable section

open Set Filter Metric Topology Function

namespace CrouzeixHilbert.Conformal

theorem derivative_values_bddAbove {U : Set ℂ} {a : ℂ} (hU : IsOpen U) (ha : a ∈ U) :
    BddAbove {v : ℝ | ∃ f, DiskEmbedding U a f ∧ ‖deriv f a‖ = v} := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU a ha
  refine ⟨1 / (r / 2), ?_⟩
  rintro v ⟨f, hf, rfl⟩
  exact norm_deriv_le_on_half_ball hU hf.holomorphic
    (fun z hz => (hf.into_disk z hz).le) hr hsub (mem_ball_self (by positivity))

theorem exists_extremal {U : Set ℂ} {a : ℂ} (hU : IsOpen U)
    (hc : IsPreconnected U) (ha : a ∈ U) {g : ℂ → ℂ}
    (hg : DiskEmbedding U a g) (hgd : deriv g a ≠ 0) :
    ∃ f, DiskEmbedding U a f ∧ deriv f a ≠ 0 ∧
      ∀ q, DiskEmbedding U a q → ‖deriv q a‖ ≤ ‖deriv f a‖ := by
  classical
  let S : Set ℝ := {v | ∃ f, DiskEmbedding U a f ∧ ‖deriv f a‖ = v}
  have hS : S.Nonempty := ⟨‖deriv g a‖, g, hg, rfl⟩
  have hSb : BddAbove S := derivative_values_bddAbove hU ha
  have hα : 0 < sSup S := (norm_pos_iff.mpr hgd).trans_le (le_csSup hSb ⟨g, hg, rfl⟩)
  obtain ⟨v, _, hv, hvS⟩ := exists_seq_tendsto_sSup hS hSb
  choose F hF hFv using hvS
  obtain ⟨f, φ, hφ, hl, hd, hnorm⟩ := montel hU F (fun n => (hF n).holomorphic)
    (fun n z hz => ((hF n).into_disk z hz).le)
  have hderiv : ‖deriv f a‖ = sSup S := by
    have hlim := ((hl.deriv (Eventually.of_forall (fun n => (hF (φ n)).holomorphic)) hU).tendsto_at ha).norm
    have heq : (fun n => ‖deriv ((F ∘ φ) n) a‖) = v ∘ φ := by
      funext n
      exact hFv (φ n)
    change Tendsto (fun n => ‖deriv ((F ∘ φ) n) a‖) atTop (𝓝 ‖deriv f a‖) at hlim
    rw [heq] at hlim
    exact tendsto_nhds_unique hlim (hv.comp hφ.tendsto_atTop)
  have hfd : deriv f a ≠ 0 := norm_pos_iff.mp (hderiv ▸ hα)
  have hnc : ¬ ∃ c, EqOn f (fun _ => c) U := by
    rintro ⟨c, he⟩
    apply hfd
    have hfe : f =ᶠ[𝓝 a] fun _ => c := he.eventuallyEq_of_mem (hU.mem_nhds ha)
    exact hfe.deriv_eq.trans (deriv_const _ _)
  have hinto : ∀ z ∈ U, ‖f z‖ < 1 := by
    intro z hz
    apply lt_of_le_of_ne (hnorm z hz)
    intro he
    apply hnc
    refine ⟨f z, Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hc hU hd hz ?_⟩
    intro w hw
    exact (hnorm w hw).trans he.ge
  have hzero : f a = 0 := by
    apply tendsto_nhds_unique (hl.tendsto_at ha)
    have he : (fun n => (F ∘ φ) n a) = fun _ => (0 : ℂ) := by
      funext n
      exact (hF (φ n)).normalized
    rw [he]
    exact tendsto_const_nhds
  refine ⟨f, ⟨hd, injOn_of_tendstoLocallyUniformlyOn hU hc hl
    (fun n => (hF (φ n)).holomorphic) (fun n => (hF (φ n)).injective) hnc, hinto, hzero⟩,
    hfd, ?_⟩
  intro q hq
  rw [hderiv]
  exact le_csSup hSb ⟨q, hq, rfl⟩

theorem exists_holomorphic_square_root {U : Set ℂ} (hU : IsOpen U)
    (hc : IsSimplyConnected U) {q : ℂ → ℂ} (hq : DifferentiableOn ℂ q U)
    (hz : ∀ z ∈ U, q z ≠ 0) :
    ∃ h : ℂ → ℂ, (∀ z, h z ^ 2 = q z) ∧
      (∀ z ∈ U, h z ≠ 0) ∧
      ∀ z ∈ U, HasDerivAt h (deriv q z / (2 * h z)) z := by
  have hnot : 0 ∉ q '' U := by
    rintro ⟨z, hzu, he⟩
    exact hz z hzu he
  obtain ⟨h, hh, he⟩ := Complex.exists_continuousOn_pow_eq hc hU hq.continuousOn hnot two_ne_zero
  have hn : ∀ z ∈ U, h z ≠ 0 := by
    intro z hzu he'
    apply hz z hzu
    rw [← he, he', zero_pow two_ne_zero]
  refine ⟨h, he, hn, ?_⟩
  intro z hzu
  have hp : HasDerivAt (fun x : ℂ => x ^ 2) (2 * h z) (h z) := by
    simpa using hasDerivAt_pow 2 (h z)
  exact HasDerivAt.of_comp_left (hh.continuousAt (hU.mem_nhds hzu)) hp
    ((hq z hzu).differentiableAt (hU.mem_nhds hzu)).hasDerivAt
    (mul_ne_zero two_ne_zero (hn z hzu)) (Eventually.of_forall he)

theorem exists_improved_of_omitted {U : Set ℂ} {a : ℂ} (hU : IsOpen U)
    (hc : IsSimplyConnected U) (ha : a ∈ U) {f : ℂ → ℂ}
    (hf : DiskEmbedding U a f) (hfd : deriv f a ≠ 0)
    {w : ℂ} (hw : ‖w‖ < 1) (hwo : w ∉ f '' U) :
    ∃ ψ, DiskEmbedding U a ψ ∧ ‖deriv f a‖ < ‖deriv ψ a‖ := by
  let q := diskShift w ∘ f
  have hqnorm : ∀ z ∈ U, ‖q z‖ < 1 := fun z hz => diskShift_into_disk hw (hf.into_disk z hz)
  have hqhol : DifferentiableOn ℂ q U := by
    intro z hz
    exact ((hasDerivAt_diskShift hw (hf.into_disk z hz).le).comp z
      ((hf.holomorphic z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt).differentiableAt.differentiableWithinAt
  have hqinj : InjOn q U := (diskShift_injOn hw).comp hf.injective
    (fun z hz => mem_closedBall_zero_iff.mpr (hf.into_disk z hz).le)
  have hqzero : ∀ z ∈ U, q z ≠ 0 := by
    intro z hz he
    exact hwo ⟨z, hz, (diskShift_eq_zero_iff hw (hf.into_disk z hz).le).mp he⟩
  obtain ⟨h, hsq, hhn, hhd⟩ := exists_holomorphic_square_root hU hc hqhol hqzero
  have hhnorm : ∀ z ∈ U, ‖h z‖ < 1 := by
    intro z hz
    have hn : ‖h z‖ ^ 2 < 1 := by rw [← norm_pow, hsq]; exact hqnorm z hz
    nlinarith [norm_nonneg (h z)]
  have hhinj : InjOn h U := by
    intro z hz v hv he
    apply hqinj hz hv
    rw [← hsq, ← hsq, he]
  let ψ := diskShift (h a) ∘ h
  have hψder : HasDerivAt ψ
      (deriv (diskShift (h a)) (h a) * (deriv q a / (2 * h a))) a :=
    (hasDerivAt_diskShift (hhnorm a ha) (hhnorm a ha).le).differentiableAt.hasDerivAt.comp a (hhd a ha)
  have hψ : DiskEmbedding U a ψ := by
    constructor
    · intro z hz
      exact ((hasDerivAt_diskShift (hhnorm a ha) (hhnorm z hz).le).comp z
        (hhd z hz)).differentiableAt.differentiableWithinAt
    · exact (diskShift_injOn (hhnorm a ha)).comp hhinj
        (fun z hz => mem_closedBall_zero_iff.mpr (hhnorm z hz).le)
    · exact fun z hz => diskShift_into_disk (hhnorm a ha) (hhnorm z hz)
    · exact diskShift_self _
  refine ⟨ψ, hψ, ?_⟩
  have hqa : q a = -w := by simp [q, hf.normalized]
  have hsqa : ‖h a‖ ^ 2 = ‖w‖ := by rw [← norm_pow, hsq, hqa, norm_neg]
  have hqd : ‖deriv q a‖ = (1 - ‖w‖ ^ 2) * ‖deriv f a‖ := by
    rw [deriv_comp a (hasDerivAt_diskShift hw (hf.into_disk a ha).le).differentiableAt
      ((hf.holomorphic a ha).differentiableAt (hU.mem_nhds ha)), norm_mul,
      hf.normalized, norm_deriv_diskShift_zero hw]
  have hψnorm : ‖deriv ψ a‖ = (1 - ‖h a‖ ^ 2)⁻¹ *
      ((1 - ‖w‖ ^ 2) * ‖deriv f a‖ / (2 * ‖h a‖)) := by
    rw [hψder.deriv, norm_mul, norm_deriv_diskShift_self (hhnorm a ha),
      norm_div, hqd, norm_mul]
    norm_num
  have hr0 : 0 < ‖h a‖ := norm_pos_iff.mpr (hhn a ha)
  have hr1 : ‖h a‖ < 1 := hhnorm a ha
  have ha0 : 0 < ‖deriv f a‖ := norm_pos_iff.mpr hfd
  have hden : 0 < 1 - ‖h a‖ ^ 2 := by nlinarith
  rw [hψnorm, ← hsqa]
  have he : (1 - ‖h a‖ ^ 2)⁻¹ *
      ((1 - (‖h a‖ ^ 2) ^ 2) * ‖deriv f a‖ / (2 * ‖h a‖)) =
      (1 + ‖h a‖ ^ 2) * ‖deriv f a‖ / (2 * ‖h a‖) := by
    field_simp
    ring
  rw [he, lt_div_iff₀ (by positivity)]
  have hgain : 0 < (1 - ‖h a‖) ^ 2 * ‖deriv f a‖ :=
    mul_pos (sq_pos_of_pos (sub_pos.mpr hr1)) ha0
  nlinarith

theorem exists_diskEmbedding_of_bounded {U : Set ℂ} (hb : Bornology.IsBounded U) (a : ℂ) :
    ∃ f, DiskEmbedding U a f ∧ deriv f a ≠ 0 := by
  obtain ⟨r, hr, hsub⟩ := hb.subset_ball_lt 0 a
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  let f : ℂ → ℂ := fun z => (z - a) / r
  have hd : ∀ z, HasDerivAt f (1 / r) z := fun z => ((hasDerivAt_id z).sub_const a).div_const (r : ℂ)
  refine ⟨f, ⟨fun z _ => (hd z).differentiableAt.differentiableWithinAt, ?_, ?_, ?_⟩, ?_⟩
  · intro z _ w _ he
    have he' : z - a = w - a := (div_left_inj' hrC).mp he
    exact sub_left_injective he'
  · intro z hz
    change ‖(z - a) / (r : ℂ)‖ < 1
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le, div_lt_one₀ hr]
    exact (dist_eq_norm z a) ▸ hsub hz
  · simp [f]
  · rw [(hd a).deriv]
    exact div_ne_zero one_ne_zero hrC

theorem riemann_mapping_bounded {U : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) (hc : IsSimplyConnected U) {a : ℂ} (ha : a ∈ U) :
    ∃ f, DiskEmbedding U a f ∧ deriv f a ≠ 0 ∧ BijOn f U (ball 0 1) := by
  obtain ⟨g, hg, hgd⟩ := exists_diskEmbedding_of_bounded hb a
  obtain ⟨f, hf, hfd, hext⟩ := exists_extremal hU hc.isPathConnected.isConnected.isPreconnected ha hg hgd
  refine ⟨f, hf, hfd, ⟨fun z hz => mem_ball_zero_iff.mpr (hf.into_disk z hz), hf.injective, ?_⟩⟩
  intro w hw
  by_contra hwo
  obtain ⟨ψ, hψ, hh⟩ := exists_improved_of_omitted hU hc ha hf hfd
    (mem_ball_zero_iff.mp hw) hwo
  exact (hext ψ hψ).not_gt hh

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Univalent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Univalent. -/

noncomputable section

open Set Filter Metric Topology Function

namespace CrouzeixHilbert.Conformal

theorem hasStrictDerivAt_invFunOn {U V : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U V) {w : ℂ} (hw : w ∈ V) :
    HasStrictDerivAt (invFunOn f U) (deriv f (invFunOn f U w))⁻¹ w := by
  obtain ⟨z, hz, rfl⟩ := hbij.surjOn hw
  have hinv := hbij.invOn_invFunOn
  have he : ∀ᶠ v in 𝓝 z, invFunOn f U (f v) = v := by
    filter_upwards [hU.mem_nhds hz] with v hv
    exact hinv.1 hv
  rw [hinv.1 hz]
  exact ((hf.analyticOnNhd hU z hz).hasStrictDerivAt).to_local_left_inverse
    (deriv_ne_zero_of_injOn hU hf hbij.injOn hz) he

theorem riemann_biholomorphic_bounded_oai {U : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) (hc : IsSimplyConnected U) {a : ℂ} (ha : a ∈ U) :
    ∃ f g : ℂ → ℂ,
      DifferentiableOn ℂ f U ∧ DifferentiableOn ℂ g (ball 0 1) ∧
      BijOn f U (ball 0 1) ∧ BijOn g (ball 0 1) U ∧
      InvOn g f U (ball 0 1) ∧ f a = 0 ∧
      (∀ z ∈ U, deriv f z ≠ 0) ∧ (∀ w ∈ ball 0 1, deriv g w ≠ 0) := by
  obtain ⟨f, hf, _, hbij⟩ := riemann_mapping_bounded hU hb hc ha
  let g := invFunOn f U
  have hd : DifferentiableOn ℂ g (ball 0 1) := fun w hw =>
    (hasStrictDerivAt_invFunOn hU hf.holomorphic hbij hw).hasDerivAt.differentiableAt.differentiableWithinAt
  have hinv : InvOn g f U (ball 0 1) := hbij.invOn_invFunOn
  have hg : BijOn g (ball 0 1) U := hbij.symm hinv.symm
  exact ⟨f, g, hf.holomorphic, hd, hbij, hg, hinv, hf.normalized,
    fun z hz => deriv_ne_zero_of_injOn hU hf.holomorphic hf.injective hz,
    fun w hw => deriv_ne_zero_of_injOn isOpen_ball hd hg.injOn hw⟩

end CrouzeixHilbert.Conformal

end

end OAI
end

theorem solution : type_of% @OAI.CrouzeixHilbert.Conformal.riemann_biholomorphic_bounded_oai := @OAI.CrouzeixHilbert.Conformal.riemann_biholomorphic_bounded_oai
