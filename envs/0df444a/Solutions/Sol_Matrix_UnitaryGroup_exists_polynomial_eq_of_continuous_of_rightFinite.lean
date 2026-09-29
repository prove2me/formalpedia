-- Prove2me | solution 1 for Matrix.UnitaryGroup.exists_polynomial_eq_of_continuous_of_rightFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/1df22b47-a5c6-533a-a580-c97a71f7be45

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite

noncomputable section

namespace M4aP3C
namespace TensorSplit

variable {G : Type*}

theorem exists_eval_combination (W : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ W]
    (φ : Module.Dual ℂ W) :
    ∃ (m : ℕ) (e : Fin m → ℂ) (x : Fin m → G), ∀ w : W, φ w = ∑ l, e l * (w : G → ℂ) (x l) := by
  classical
  let ev : G → Module.Dual ℂ W := fun x => (LinearMap.proj x).comp W.subtype
  have hev : ∀ x (w : W), ev x w = (w : G → ℂ) x := fun x w => rfl
  let Φ : Submodule ℂ (Module.Dual ℂ W) := Submodule.span ℂ (Set.range ev)
  have hco : Φ.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_dualCoannihilator] at hw
    rw [Submodule.mem_bot]
    apply Subtype.ext
    funext x
    have := hw (ev x) (Submodule.subset_span ⟨x, rfl⟩)
    rw [hev] at this
    simpa using this
  have hΦ : Φ = ⊤ := by
    have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Φ)
    rw [hco, Submodule.dualAnnihilator_bot] at h
    exact h.symm
  have hφ : φ ∈ Φ := by rw [hΦ]; exact Submodule.mem_top
  rw [Submodule.mem_span_set'] at hφ
  obtain ⟨m, e, g, hg⟩ := hφ
  have hg' : ∀ l, ∃ x, ev x = ((g l : Set.range ev) : Module.Dual ℂ W) := fun l => (g l).2
  choose x hx using hg'
  refine ⟨m, e, x, fun w => ?_⟩
  rw [← hg]
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [LinearMap.smul_apply, ← hx l, hev, smul_eq_mul]

end M4aP3C.TensorSplit

end

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace M4aP3C
namespace SU2Finite

abbrev U2 : Type := ↥(Matrix.unitaryGroup (Fin 2) ℂ)

def polyFun : Submodule ℂ (Matrix (Fin 2) (Fin 2) ℂ → ℂ) :=
  Submodule.span ℂ
    {F | ∃ l : List (Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ), F = fun m => (l.map (fun φ => φ m)).prod}

theorem isCompact_unitaryGroup :
    IsCompact ((Matrix.unitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ))) := by

  have hclosed : IsClosed ((Matrix.unitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ))) :=
    isClosed_unitary
  letI : NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℂ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.normedSpace
  haveI : ProperSpace (Matrix (Fin 2) (Fin 2) ℂ) :=
    FiniteDimensional.proper ℂ (Matrix (Fin 2) (Fin 2) ℂ)
  have hsub : (Matrix.unitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ))
      ⊆ Metric.closedBall 0 1 := by
    intro m hm
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (Matrix.norm_le_iff zero_le_one).2 fun i j => entry_norm_bound_of_unitary hm i j
  exact Metric.isCompact_of_isClosed_isBounded hclosed
    (Metric.isBounded_closedBall.subset hsub)

scoped instance : CompactSpace U2 := isCompact_iff_compactSpace.mp isCompact_unitaryGroup

scoped instance : MeasurableSpace U2 := borel U2

scoped instance : BorelSpace U2 := ⟨rfl⟩

scoped instance : MeasurableMul U2 :=
  ⟨fun g => (continuous_const_mul g).measurable, fun g => (continuous_mul_const g).measurable⟩

def K0 : TopologicalSpace.PositiveCompacts U2 :=
  ⟨⟨Set.univ, isCompact_univ⟩, by rw [interior_univ]; exact Set.univ_nonempty⟩

def haarU2 : Measure U2 := Measure.haarMeasure K0

scoped instance : Measure.IsHaarMeasure haarU2 := Measure.isHaarMeasure_haarMeasure K0

theorem haarU2_univ : haarU2 Set.univ = 1 := Measure.haarMeasure_self

scoped instance : IsProbabilityMeasure haarU2 := ⟨haarU2_univ⟩

theorem integral_translate (g : U2) (f : U2 → ℂ) :
    ∫ h, f (g * h) ∂haarU2 = ∫ h, f h ∂haarU2 :=
  integral_mul_left_eq_self f g

theorem integral_translate_real (g : U2) (f : U2 → ℝ) :
    ∫ h, f (g * h) ∂haarU2 = ∫ h, f h ∂haarU2 :=
  integral_mul_left_eq_self f g

theorem integrable_of_continuous {E : Type} [NormedAddCommGroup E] {f : U2 → E}
    (hf : Continuous f) : Integrable f haarU2 :=
  hf.integrable_of_hasCompactSupport (isClosed_tsupport f).isCompact

theorem integral_pos_of_continuous {χ : U2 → ℝ} (hc : Continuous χ) (h0 : 0 ≤ χ)
    (h1 : 0 < χ 1) : 0 < ∫ h, χ h ∂haarU2 := by
  rw [integral_pos_iff_support_of_nonneg h0 (integrable_of_continuous hc)]
  have hopen : IsOpen (Function.support χ) := by
    rw [Function.support_eq_preimage]
    exact isClosed_singleton.isOpen_compl.preimage hc
  exact hopen.measure_pos haarU2 ⟨1, Function.mem_support.mpr (ne_of_gt h1)⟩

def qker (k : U2) : ℝ := (2 + (Matrix.trace (k : Matrix (Fin 2) (Fin 2) ℂ)).re) / 4

theorem continuous_qker : Continuous qker := by
  have htr : Continuous fun k : U2 => Matrix.trace (k : Matrix (Fin 2) (Fin 2) ℂ) :=
    Continuous.matrix_trace continuous_subtype_val
  exact (continuous_const.add (Complex.continuous_re.comp htr)).div_const 4

theorem entry_re_le (k : U2) (i j : Fin 2) : ((k : Matrix (Fin 2) (Fin 2) ℂ) i j).re ≤ 1 :=
  le_trans (Complex.re_le_norm _) (entry_norm_bound_of_unitary k.2 i j)

theorem entry_abs_re_le (k : U2) (i j : Fin 2) :
    |((k : Matrix (Fin 2) (Fin 2) ℂ) i j).re| ≤ 1 :=
  le_trans (Complex.abs_re_le_norm _) (entry_norm_bound_of_unitary k.2 i j)

theorem qker_nonneg (k : U2) : 0 ≤ qker k := by
  have h0 := abs_le.mp (entry_abs_re_le k 0 0)
  have h1 := abs_le.mp (entry_abs_re_le k 1 1)
  unfold qker
  rw [Matrix.trace_fin_two, Complex.add_re]
  linarith [h0.1, h1.1]

theorem qker_le_one (k : U2) : qker k ≤ 1 := by
  have h0 := entry_re_le k 0 0
  have h1 := entry_re_le k 1 1
  unfold qker
  rw [Matrix.trace_fin_two, Complex.add_re]
  linarith

theorem qker_one : qker 1 = 1 := by
  have h : ((1 : U2) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := rfl
  unfold qker
  rw [h, Matrix.trace_one]
  norm_num

theorem qker_eq_one_iff {k : U2} : qker k = 1 ↔ k = 1 := by
  constructor
  · intro hq
    have hre : ((k : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re = 1 ∧
        ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1).re = 1 := by
      have e0 := entry_re_le k 0 0
      have e1 := entry_re_le k 1 1
      unfold qker at hq
      rw [Matrix.trace_fin_two, Complex.add_re] at hq
      constructor <;> linarith
    have hdiag : ∀ i : Fin 2, ((k : Matrix (Fin 2) (Fin 2) ℂ) i i).re = 1 →
        (k : Matrix (Fin 2) (Fin 2) ℂ) i i = 1 := by
      intro i hi
      have hn : ‖(k : Matrix (Fin 2) (Fin 2) ℂ) i i‖ ≤ 1 := entry_norm_bound_of_unitary k.2 i i
      have hns : Complex.normSq ((k : Matrix (Fin 2) (Fin 2) ℂ) i i) ≤ 1 := by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [norm_nonneg ((k : Matrix (Fin 2) (Fin 2) ℂ) i i)]
      have hsq := Complex.normSq_apply ((k : Matrix (Fin 2) (Fin 2) ℂ) i i)
      have h2 : ((k : Matrix (Fin 2) (Fin 2) ℂ) i i).im *
          ((k : Matrix (Fin 2) (Fin 2) ℂ) i i).im ≤ 0 := by
        nlinarith [hi]
      have him : ((k : Matrix (Fin 2) (Fin 2) ℂ) i i).im = 0 :=
        mul_self_eq_zero.mp (le_antisymm h2 (mul_self_nonneg _))
      exact Complex.ext (by rw [hi, Complex.one_re]) (by rw [him, Complex.one_im])
    have h00 : (k : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 1 := hdiag 0 hre.1
    have h11 : (k : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 1 := hdiag 1 hre.2
    have hu : (k : Matrix (Fin 2) (Fin 2) ℂ) * star (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp k.2
    have row : ∀ i : Fin 2, Complex.normSq ((k : Matrix (Fin 2) (Fin 2) ℂ) i 0) +
        Complex.normSq ((k : Matrix (Fin 2) (Fin 2) ℂ) i 1) = 1 := by
      intro i
      have r := congrArg (fun M => M i i) hu
      simp only [Matrix.mul_apply, Matrix.one_apply_eq] at r
      rw [Fin.sum_univ_two] at r
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        Matrix.conjTranspose_apply] at r
      simp only [Complex.star_def] at r
      rw [Complex.mul_conj, Complex.mul_conj] at r
      have := congrArg Complex.re r
      simpa using this
    have h01 : (k : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by
      have h := row 0
      rw [h00, Complex.normSq_one] at h
      exact Complex.normSq_eq_zero.mp (by linarith)
    have h10 : (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by
      have h := row 1
      rw [h11, Complex.normSq_one] at h
      exact Complex.normSq_eq_zero.mp (by linarith)
    have hAone : (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
      rw [Matrix.eta_fin_two (k : Matrix (Fin 2) (Fin 2) ℂ), h00, h01, h10, h11,
        Matrix.one_fin_two]
    exact Subtype.ext hAone
  · rintro rfl
    exact qker_one

theorem exists_lt_one_bound {U : Set U2} (hU : U ∈ nhds (1 : U2)) :
    ∃ δ : ℝ, δ < 1 ∧ ∀ k : U2, k ∉ U → qker k ≤ δ := by
  rcases Set.eq_empty_or_nonempty ((interior U)ᶜ : Set U2) with hS | hS
  · refine ⟨0, by norm_num, fun k hk => ?_⟩
    exfalso
    have hkS : k ∈ ((interior U)ᶜ : Set U2) := fun hin => hk (interior_subset hin)
    rw [hS] at hkS
    simp at hkS
  · obtain ⟨m₀, hm₀, hmax⟩ :=
      (isOpen_interior.isClosed_compl.isCompact).exists_isMaxOn hS continuous_qker.continuousOn
    refine ⟨qker m₀, ?_, fun k hk => hmax (fun hin => hk (interior_subset hin))⟩
    rcases lt_or_eq_of_le (qker_le_one m₀) with h | h
    · exact h
    · exfalso
      have h1 : m₀ = 1 := qker_eq_one_iff.mp h
      rw [h1] at hm₀
      exact hm₀ (mem_interior_iff_mem_nhds.mpr hU)

def fejerNorm (n : ℕ) : ℝ := ∫ h, qker h ^ n ∂haarU2

theorem fejerNorm_pos (n : ℕ) : 0 < fejerNorm n := by
  refine integral_pos_of_continuous (continuous_qker.pow n)
    (fun h => pow_nonneg (qker_nonneg h) n) ?_
  rw [qker_one, one_pow]
  norm_num

def fejerConv (n : ℕ) (Φ : U2 → ℂ) (k : U2) : ℂ :=
  (fejerNorm n)⁻¹ • ∫ h, Φ (k * h) * ((qker h ^ n : ℝ) : ℂ) ∂haarU2

theorem integrable_conv_kernel {Φ : U2 → ℂ} (hc : Continuous Φ) (n : ℕ) (k : U2) :
    Integrable (fun h => Φ (k * h) * ((qker h ^ n : ℝ) : ℂ)) haarU2 :=
  integrable_of_continuous ((hc.comp (continuous_const_mul k)).mul
    (Complex.continuous_ofReal.comp (continuous_qker.pow n)))

theorem fejerConv_sub {Φ : U2 → ℂ} (hc : Continuous Φ) (n : ℕ) (k : U2) :
    fejerConv n Φ k - Φ k
      = (fejerNorm n)⁻¹ • ∫ h, (Φ (k * h) - Φ k) * ((qker h ^ n : ℝ) : ℂ) ∂haarU2 := by
  have hint1 := integrable_conv_kernel hc n k
  have hint2 : Integrable (fun h : U2 => Φ k * ((qker h ^ n : ℝ) : ℂ)) haarU2 :=
    integrable_of_continuous (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_qker.pow n)))
  have hq2c : (∫ h, ((qker h ^ n : ℝ) : ℂ) ∂haarU2) = ((fejerNorm n : ℝ) : ℂ) := by
    unfold fejerNorm
    exact integral_ofReal
  have hpt : ∀ h : U2, (Φ (k * h) - Φ k) * ((qker h ^ n : ℝ) : ℂ)
      = Φ (k * h) * ((qker h ^ n : ℝ) : ℂ) - Φ k * ((qker h ^ n : ℝ) : ℂ) := by
    intro h; ring
  have hsplit : ∫ h, (Φ (k * h) - Φ k) * ((qker h ^ n : ℝ) : ℂ) ∂haarU2
      = (∫ h, Φ (k * h) * ((qker h ^ n : ℝ) : ℂ) ∂haarU2)
        - Φ k * ((fejerNorm n : ℝ) : ℂ) := by
    simp only [hpt]
    rw [integral_sub hint1 hint2, integral_const_mul, hq2c]
  unfold fejerConv
  rw [hsplit, smul_sub]
  congr 1
  have hne : ((fejerNorm n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (fejerNorm_pos n))
  rw [Complex.real_smul, Complex.ofReal_inv]
  field_simp

private theorem aux_ratio (x d e b : ℝ) (n : ℕ) (he : e ≠ 0) (hb : b ≠ 0) :
    (e^n * b)⁻¹ * (2*x*d^n) = (2*x/b) * (d/e)^n := by
  rw [div_pow]
  field_simp

theorem fejerConv_tendsto {Φ : U2 → ℂ} (hc : Continuous Φ) (k : U2) :
    Filter.Tendsto (fun n => fejerConv n Φ k) Filter.atTop (nhds (Φ k)) := by

  obtain ⟨xm, -, hxm⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.norm.continuousOn
  have hCb : ∀ x : U2, ‖Φ x‖ ≤ ‖Φ xm‖ := fun x => hxm (Set.mem_univ x)
  set C : ℝ := ‖Φ xm‖ with hCdef
  have hC0 : 0 ≤ C := norm_nonneg _
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : 0 < ε/4 := by linarith

  have hg : Continuous fun h : U2 => Φ (k * h) := hc.comp (continuous_const_mul k)
  set U : Set U2 := (fun h : U2 => Φ (k * h)) ⁻¹' Metric.ball (Φ k) (ε/4) with hUdef
  have hUopen : IsOpen U := Metric.isOpen_ball.preimage hg
  have hU1 : (1 : U2) ∈ U := by
    simp only [hUdef, Set.mem_preimage, Metric.mem_ball, mul_one, dist_self]
    exact hε4

  obtain ⟨δ₀, hδ₀1, hδ₀b⟩ := exists_lt_one_bound (hUopen.mem_nhds hU1)
  set δ : ℝ := max δ₀ 0 with hδdef
  have hδ1 : δ < 1 := max_lt hδ₀1 one_pos
  have hδ0 : 0 ≤ δ := le_max_right _ _
  have hδb : ∀ h : U2, h ∉ U → qker h ≤ δ := fun h hh => (hδ₀b h hh).trans (le_max_left _ _)
  set η : ℝ := (1 + δ)/2 with hηdef
  have hδη : δ < η := by rw [hηdef]; linarith
  have hη1 : η < 1 := by rw [hηdef]; linarith
  have hη0 : 0 < η := by rw [hηdef]; linarith
  set V : Set U2 := {h : U2 | η < qker h} with hVdef
  have hVopen : IsOpen V := isOpen_lt continuous_const continuous_qker
  have hV1 : (1 : U2) ∈ V := by
    simp only [hVdef, Set.mem_setOf_eq, qker_one]
    exact hη1
  have hβpos : 0 < haarU2.real V := by
    rw [Measure.real]
    exact ENNReal.toReal_pos (ne_of_gt (hVopen.measure_pos haarU2 ⟨1, hV1⟩)) (measure_ne_top _ _)
  set β : ℝ := haarU2.real V with hβdef
  have hβne : β ≠ 0 := ne_of_gt hβpos

  have hlow : ∀ n : ℕ, η ^ n * β ≤ fejerNorm n := by
    intro n
    have hqn : Integrable (fun h : U2 => qker h ^ n) haarU2 :=
      integrable_of_continuous (continuous_qker.pow n)
    have h1 : ∫ _ in V, (η ^ n : ℝ) ∂haarU2 ≤ ∫ h in V, qker h ^ n ∂haarU2 := by
      refine setIntegral_mono_on integrableOn_const hqn.integrableOn
        hVopen.measurableSet fun h hh => ?_
      exact pow_le_pow_left₀ (le_of_lt hη0) (le_of_lt hh) n
    have h2 : ∫ h in V, qker h ^ n ∂haarU2 ≤ fejerNorm n := by
      unfold fejerNorm
      exact setIntegral_le_integral hqn
        (Filter.Eventually.of_forall fun h => pow_nonneg (qker_nonneg h) n)
    rw [setIntegral_const, smul_eq_mul] at h1
    calc η ^ n * β = β * η ^ n := mul_comm _ _
      _ ≤ ∫ h in V, qker h ^ n ∂haarU2 := h1
      _ ≤ fejerNorm n := h2

  have hkey : ∀ n : ℕ, dist (fejerConv n Φ k) (Φ k) ≤ ε/4 + (2*C/β) * (δ/η) ^ n := by
    intro n
    have hnpos := fejerNorm_pos n
    have hDint : Integrable (fun h : U2 => ‖Φ (k * h) - Φ k‖ * qker h ^ n) haarU2 :=
      integrable_of_continuous ((hg.sub continuous_const).norm.mul (continuous_qker.pow n))
    rw [dist_eq_norm, fejerConv_sub hc n k, norm_smul]
    have hinv0 : (0:ℝ) ≤ (fejerNorm n)⁻¹ := le_of_lt (inv_pos.mpr hnpos)
    have hnn : ‖(fejerNorm n)⁻¹‖ = (fejerNorm n)⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hinv0]
    rw [hnn]
    have hstep1 : ‖∫ h, (Φ (k * h) - Φ k) * ((qker h ^ n : ℝ) : ℂ) ∂haarU2‖
        ≤ ∫ h, ‖Φ (k * h) - Φ k‖ * qker h ^ n ∂haarU2 := by
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
      show ‖(Φ (k * h) - Φ k) * ((qker h ^ n : ℝ) : ℂ)‖ = ‖Φ (k * h) - Φ k‖ * qker h ^ n
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (qker_nonneg h) n)]
    have hsplit : ∫ h, ‖Φ (k * h) - Φ k‖ * qker h ^ n ∂haarU2
        = (∫ h in U, ‖Φ (k * h) - Φ k‖ * qker h ^ n ∂haarU2)
          + ∫ h in Uᶜ, ‖Φ (k * h) - Φ k‖ * qker h ^ n ∂haarU2 :=
      (integral_add_compl hUopen.measurableSet hDint).symm
    have hqn : Integrable (fun h : U2 => qker h ^ n) haarU2 :=
      integrable_of_continuous (continuous_qker.pow n)
    have hUb : ∫ h in U, ‖Φ (k * h) - Φ k‖ * qker h ^ n ∂haarU2 ≤ (ε/4) * fejerNorm n := by
      have hmono : ∫ h in U, ‖Φ (k * h) - Φ k‖ * qker h ^ n ∂haarU2
          ≤ ∫ h in U, (ε/4) * qker h ^ n ∂haarU2 := by
        refine setIntegral_mono_on hDint.integrableOn
          (integrable_of_continuous (continuous_const.mul (continuous_qker.pow n))).integrableOn
          hUopen.measurableSet fun h hh => ?_
        have hdist : dist (Φ (k * h)) (Φ k) < ε/4 := by
          simpa [hUdef, Metric.mem_ball] using hh
        rw [dist_eq_norm] at hdist
        exact mul_le_mul_of_nonneg_right (le_of_lt hdist) (pow_nonneg (qker_nonneg h) n)
      refine hmono.trans ?_
      rw [MeasureTheory.integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hε4)
      exact setIntegral_le_integral hqn
        (Filter.Eventually.of_forall fun h => pow_nonneg (qker_nonneg h) n)
    have hUcb : ∫ h in Uᶜ, ‖Φ (k * h) - Φ k‖ * qker h ^ n ∂haarU2 ≤ 2*C*δ^n := by
      have hmono : ∫ h in Uᶜ, ‖Φ (k * h) - Φ k‖ * qker h ^ n ∂haarU2
          ≤ ∫ _ in Uᶜ, (2*C*δ^n : ℝ) ∂haarU2 := by
        refine setIntegral_mono_on hDint.integrableOn integrableOn_const
          hUopen.measurableSet.compl fun h hh => ?_
        have h1 : ‖Φ (k * h) - Φ k‖ ≤ 2*C := by
          have hx := hCb (k*h)
          have hy := hCb k
          calc ‖Φ (k * h) - Φ k‖ ≤ ‖Φ (k * h)‖ + ‖Φ k‖ := norm_sub_le _ _
            _ ≤ 2*C := by rw [hCdef] at hx hy ⊢; linarith
        have h2 : qker h ^ n ≤ δ ^ n := pow_le_pow_left₀ (qker_nonneg h) (hδb h hh) n
        exact mul_le_mul h1 h2 (pow_nonneg (qker_nonneg h) n) (by positivity)
      refine hmono.trans ?_
      rw [setIntegral_const, smul_eq_mul]
      have hle1 : haarU2.real Uᶜ ≤ 1 := by
        have h1 : haarU2 Uᶜ ≤ 1 := by
          rw [← haarU2_univ]
          exact measure_mono (Set.subset_univ _)
        rw [Measure.real]
        calc (haarU2 Uᶜ).toReal ≤ (1 : ENNReal).toReal :=
          ENNReal.toReal_mono ENNReal.one_ne_top h1
          _ = 1 := ENNReal.toReal_one
      exact mul_le_of_le_one_left (by positivity) hle1
    have htotal : ∫ h, ‖Φ (k * h) - Φ k‖ * qker h ^ n ∂haarU2
        ≤ (ε/4) * fejerNorm n + 2*C*δ^n := by
      rw [hsplit]
      exact add_le_add hUb hUcb
    have hmain : (fejerNorm n)⁻¹ * ‖∫ h, (Φ (k*h) - Φ k) * ((qker h ^ n : ℝ):ℂ) ∂haarU2‖
        ≤ (fejerNorm n)⁻¹ * ((ε/4) * fejerNorm n + 2*C*δ^n) :=
      mul_le_mul_of_nonneg_left (hstep1.trans htotal) hinv0
    refine hmain.trans ?_
    rw [mul_add]
    have e1 : (fejerNorm n)⁻¹ * ((ε/4) * fejerNorm n) = ε/4 := by
      field_simp
    have hinvle : (fejerNorm n)⁻¹ ≤ ((η:ℝ)^n*β)⁻¹ :=
      inv_anti₀ (mul_pos (pow_pos hη0 n) hβpos) (hlow n)
    have e2 : (fejerNorm n)⁻¹ * (2*C*δ^n) ≤ ((η:ℝ)^n*β)⁻¹ * (2*C*δ^n) :=
      mul_le_mul_of_nonneg_right hinvle
        (mul_nonneg (mul_nonneg (by norm_num) hC0) (pow_nonneg hδ0 n))
    have e3 : ((η:ℝ)^n*β)⁻¹ * (2*C*δ^n) = (2*C/β) * (δ/η)^n :=
      aux_ratio C δ η β n (ne_of_gt hη0) hβne
    rw [e1]
    have := e2.trans_eq e3
    linarith

  have htail : Filter.Tendsto (fun n => (2*C/β) * (δ/η)^n) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n => ((δ/η) : ℝ)^n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hδ0 (le_of_lt hη0))
        ((div_lt_one hη0).mpr hδη)
    simpa using h1.const_mul (2*C/β)
  have hev : ∀ᶠ n in Filter.atTop, (2*C/β) * (δ/η)^n < ε/4 := htail.eventually (gt_mem_nhds hε4)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  calc dist (fejerConv n Φ k) (Φ k) ≤ ε/4 + (2*C/β)*(δ/η)^n := hkey n
    _ < ε/4 + ε/4 := by linarith [hN n hn]
    _ < ε := by linarith

theorem fejerConv_mem_span {Φ : U2 → ℂ} (hc : Continuous Φ) {s : Finset (U2 → ℂ)}
    (hfin : ∀ k : U2, (fun x => Φ (x * k)) ∈ Submodule.span ℂ (s : Set (U2 → ℂ)))
    (n : ℕ) : fejerConv n Φ ∈ Submodule.span ℂ (s : Set (U2 → ℂ)) := by
  classical
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (s : Set (U2 → ℂ))) :=
    FiniteDimensional.span_of_finite ℂ s.finite_toSet
  set V : Submodule ℂ (U2 → ℂ) := Submodule.span ℂ (s : Set (U2 → ℂ)) with hVdef
  set T : U2 → V := fun h => ⟨fun x => Φ (x * h), hfin h⟩ with hTdef
  set b := Module.finBasis ℂ V with hbdef
  have hev : ∀ j, ∃ (m : ℕ) (e : Fin m → ℂ) (x : Fin m → U2),
      ∀ w : V, b.coord j w = ∑ l, e l * (w : U2 → ℂ) (x l) := fun j =>
    M4aP3C.TensorSplit.exists_eval_combination V (b.coord j)
  choose m e xs hev using hev
  have hcont : ∀ j, Continuous fun h : U2 => (b.coord j) (T h) := by
    intro j
    have heq : (fun h : U2 => (b.coord j) (T h))
        = fun h : U2 => ∑ l, e j l * Φ (xs j l * h) := by
      funext h
      rw [hev j (T h)]
    rw [heq]
    exact continuous_finsetSum _ fun l _ =>
      continuous_const.mul (hc.comp (continuous_const_mul (xs j l)))
  have hexp : ∀ k h : U2, Φ (k * h) = ∑ j, (b.coord j) (T h) * ((b j : U2 → ℂ) k) := by
    intro k h
    have h0 : Φ (k * h) = (T h : U2 → ℂ) k := rfl
    have h1 : ((T h : U2 → ℂ)) k = ((∑ j, (b.repr (T h)) j • b j : V) : U2 → ℂ) k := by
      rw [b.sum_repr (T h)]
    rw [h0, h1, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Module.Basis.coord_apply]
  have hrepr : fejerConv n Φ = ∑ j,
      (((fejerNorm n)⁻¹ • ∫ h, (b.coord j) (T h) * ((qker h ^ n : ℝ) : ℂ) ∂haarU2 : ℂ)) •
        ((b j : U2 → ℂ)) := by
    funext k
    rw [Finset.sum_apply]
    unfold fejerConv
    have h1 : (fun h : U2 => Φ (k * h) * ((qker h ^ n : ℝ) : ℂ))
        = fun h : U2 => ∑ j, ((b j : U2 → ℂ) k) *
            ((b.coord j) (T h) * ((qker h ^ n : ℝ) : ℂ)) := by
      funext h
      rw [hexp k h, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h1]
    have hswap := integral_finsetSum (μ := haarU2) Finset.univ
      (f := fun j (h : U2) => ((b j : U2 → ℂ) k) *
        ((b.coord j) (T h) * ((qker h ^ n : ℝ) : ℂ)))
      (fun j _ => integrable_of_continuous (continuous_const.mul ((hcont j).mul
        (Complex.continuous_ofReal.comp (continuous_qker.pow n)))))
    rw [hswap]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    ring
  rw [hrepr]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (b j).2

def entryCLM (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ :=
  ((ContinuousLinearMap.proj j : (Fin 2 → ℂ) →L[ℝ] ℂ).comp
    (ContinuousLinearMap.proj i : (Fin 2 → Fin 2 → ℂ) →L[ℝ] (Fin 2 → ℂ)))

theorem entryCLM_apply (i j : Fin 2) (m : Matrix (Fin 2) (Fin 2) ℂ) : entryCLM i j m = m i j := rfl

def conjEntryCLM (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ :=
  Complex.conjCLE.toContinuousLinearMap.comp (entryCLM i j)

theorem conjEntryCLM_apply (i j : Fin 2) (m : Matrix (Fin 2) (Fin 2) ℂ) :
    conjEntryCLM i j m = (starRingEnd ℂ) (m i j) := rfl

def coordFns : Fin 8 → (Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ) :=
  ![entryCLM 0 0, entryCLM 0 1, entryCLM 1 0, entryCLM 1 1,
    conjEntryCLM 0 0, conjEntryCLM 0 1, conjEntryCLM 1 0, conjEntryCLM 1 1]

def monom (β : Fin 8 → ℕ) : Matrix (Fin 2) (Fin 2) ℂ → ℂ :=
  fun M => ∏ α, (coordFns α M) ^ (β α)

def Pdeg (n : ℕ) : Submodule ℂ (Matrix (Fin 2) (Fin 2) ℂ → ℂ) :=
  Submodule.span ℂ (Set.range fun β : {β : Fin 8 → ℕ // ∀ α, β α ≤ n} => monom ↑β)

scoped instance finite_expIndex (n : ℕ) : Finite {β : Fin 8 → ℕ // ∀ α, β α ≤ n} := by
  refine Finite.of_injective
    (fun β => (fun α => (⟨β.1 α, Nat.lt_succ_of_le (β.2 α)⟩ : Fin (n+1)))) ?_
  intro β γ hβγ
  apply Subtype.ext
  funext α
  exact congrArg Fin.val (congrFun hβγ α)

theorem finiteDimensional_Pdeg (n : ℕ) : FiniteDimensional ℂ (Pdeg n) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

theorem one_mem_polyFun : (fun _ : Matrix (Fin 2) (Fin 2) ℂ => (1 : ℂ)) ∈ polyFun := by
  refine Submodule.subset_span ⟨[], ?_⟩
  funext m
  simp

theorem polyFun_mul_mem {f g : Matrix (Fin 2) (Fin 2) ℂ → ℂ}
    (hf : f ∈ polyFun) (hg : g ∈ polyFun) : f * g ∈ polyFun := by
  have hSS : polyFun * polyFun ≤ polyFun := by
    unfold polyFun
    rw [Submodule.span_mul_span]
    refine Submodule.span_le.mpr ?_
    rintro F ⟨F₁, ⟨l₁, rfl⟩, F₂, ⟨l₂, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨l₁ ++ l₂, ?_⟩
    funext M
    simp [List.map_append, List.prod_append]
  exact hSS (Submodule.mul_mem_mul hf hg)

theorem Pdeg_le_polyFun (n : ℕ) : Pdeg n ≤ polyFun := by
  refine Submodule.span_le.mpr ?_
  rintro F ⟨β, rfl⟩
  have hpow : ∀ (α : Fin 8) (m : ℕ), (fun M => (coordFns α M) ^ m) ∈ polyFun := by
    intro α m
    refine Submodule.subset_span ⟨List.replicate m (coordFns α), ?_⟩
    funext M
    simp [List.map_replicate, List.prod_replicate]
  have hmono : monom ↑β = ∏ α, (fun M => (coordFns α M) ^ ((β : Fin 8 → ℕ) α)) := by
    funext M
    rw [Finset.prod_apply]
    rfl
  show monom ↑β ∈ polyFun
  rw [hmono]
  refine Finset.prod_induction _ (· ∈ polyFun) (fun a b ha hb => polyFun_mul_mem ha hb)
    one_mem_polyFun (fun α _ => hpow α _)

theorem Pdeg_mul_mem {a b : ℕ} {f g : Matrix (Fin 2) (Fin 2) ℂ → ℂ}
    (hf : f ∈ Pdeg a) (hg : g ∈ Pdeg b) : f * g ∈ Pdeg (a + b) := by
  have hle : Pdeg a * Pdeg b ≤ Pdeg (a + b) := by
    unfold Pdeg
    rw [Submodule.span_mul_span]
    refine Submodule.span_le.mpr ?_
    rintro F ⟨F₁, ⟨β₁, rfl⟩, F₂, ⟨β₂, rfl⟩, rfl⟩
    refine Submodule.subset_span
      ⟨⟨(β₁ : Fin 8 → ℕ) + (β₂ : Fin 8 → ℕ), fun α => add_le_add (β₁.2 α) (β₂.2 α)⟩, ?_⟩
    funext M
    simp [monom, Pi.mul_apply, ← Finset.prod_mul_distrib, pow_add]
  exact hle (Submodule.mul_mem_mul hf hg)

theorem pow_mem_Pdeg {f : Matrix (Fin 2) (Fin 2) ℂ → ℂ} (hf : f ∈ Pdeg 1) :
    ∀ n : ℕ, f ^ n ∈ Pdeg n
  | 0 => by
    rw [pow_zero]
    refine Submodule.subset_span ⟨⟨0, fun α => le_refl 0⟩, ?_⟩
    funext M
    simp [monom]
  | n + 1 => by
    rw [pow_succ]
    exact Pdeg_mul_mem (pow_mem_Pdeg hf n) hf

theorem coordFn_mem_Pdeg_one (α : Fin 8) : (fun M => coordFns α M) ∈ Pdeg 1 := by
  refine Submodule.subset_span
    ⟨⟨Pi.single α 1, fun γ => ?_⟩, ?_⟩
  · by_cases hγ : γ = α
    · subst hγ; simp
    · simp [Pi.single_eq_of_ne hγ]
  · funext M
    show monom (Pi.single α 1) M = coordFns α M
    unfold monom
    rw [Fintype.prod_eq_single α (fun γ hγ => by simp [Pi.single_eq_of_ne hγ])]
    simp

theorem const_mem_Pdeg_one (c : ℂ) :
    (fun _ : Matrix (Fin 2) (Fin 2) ℂ => c) ∈ Pdeg 1 := by
  have h1 : (fun _ : Matrix (Fin 2) (Fin 2) ℂ => (1 : ℂ)) ∈ Pdeg 1 := by
    refine Submodule.subset_span ⟨⟨0, fun α => Nat.zero_le 1⟩, ?_⟩
    funext M
    simp [monom]
  have heq : (fun _ : Matrix (Fin 2) (Fin 2) ℂ => c)
      = c • (fun _ : Matrix (Fin 2) (Fin 2) ℂ => (1 : ℂ)) := by
    funext M
    simp
  rw [heq]
  exact Submodule.smul_mem (Pdeg 1) c h1

def aker (h : U2) : Matrix (Fin 2) (Fin 2) ℂ → ℝ :=
  fun M => (2 + (Matrix.trace (star M * (h : Matrix (Fin 2) (Fin 2) ℂ))).re) / 4

theorem aker_coe (h k : U2) : aker h (k : Matrix (Fin 2) (Fin 2) ℂ) = qker (k⁻¹ * h) := by
  unfold aker qker
  congr 2

theorem continuous_aker (x : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous fun h : U2 => aker h x := by
  have hmul : Continuous fun h : U2 => star x * (h : Matrix (Fin 2) (Fin 2) ℂ) :=
    Continuous.matrix_mul continuous_const continuous_subtype_val
  have htr : Continuous fun h : U2 =>
      Matrix.trace (star x * (h : Matrix (Fin 2) (Fin 2) ℂ)) :=
    Continuous.matrix_trace hmul
  exact (continuous_const.add (Complex.continuous_re.comp htr)).div_const 4

theorem akerC_mem_Pdeg_one (h : U2) :
    (fun M : Matrix (Fin 2) (Fin 2) ℂ => ((aker h M : ℝ) : ℂ)) ∈ Pdeg 1 := by
  set H : Matrix (Fin 2) (Fin 2) ℂ := (h : Matrix (Fin 2) (Fin 2) ℂ) with hH
  have hre : ∀ w : ℂ, ((w.re : ℝ) : ℂ) = (w + (starRingEnd ℂ) w) / 2 := by
    intro w
    have h2 := Complex.add_conj w
    rw [h2]
    push_cast
    ring
  have hexp : (fun M : Matrix (Fin 2) (Fin 2) ℂ => ((aker h M : ℝ) : ℂ))
      = (fun _ => (1/2 : ℂ))
        + ((H 0 0 / 8) • fun M : Matrix (Fin 2) (Fin 2) ℂ => (starRingEnd ℂ) (M 0 0))
        + (((starRingEnd ℂ) (H 0 0) / 8) • fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0)
        + ((H 1 0 / 8) • fun M : Matrix (Fin 2) (Fin 2) ℂ => (starRingEnd ℂ) (M 1 0))
        + (((starRingEnd ℂ) (H 1 0) / 8) • fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0)
        + ((H 0 1 / 8) • fun M : Matrix (Fin 2) (Fin 2) ℂ => (starRingEnd ℂ) (M 0 1))
        + (((starRingEnd ℂ) (H 0 1) / 8) • fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1)
        + ((H 1 1 / 8) • fun M : Matrix (Fin 2) (Fin 2) ℂ => (starRingEnd ℂ) (M 1 1))
        + (((starRingEnd ℂ) (H 1 1) / 8) • fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) := by
    funext M
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    unfold aker
    rw [← hH, Matrix.trace_fin_two]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Complex.star_def]
    push_cast
    rw [hre]
    simp only [map_add, map_mul, Complex.conj_conj]
    ring
  rw [hexp]
  have m00 : (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) ∈ Pdeg 1 := coordFn_mem_Pdeg_one 0
  have m01 : (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) ∈ Pdeg 1 := coordFn_mem_Pdeg_one 1
  have m10 : (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) ∈ Pdeg 1 := coordFn_mem_Pdeg_one 2
  have m11 : (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) ∈ Pdeg 1 := coordFn_mem_Pdeg_one 3
  have c00 : (fun M : Matrix (Fin 2) (Fin 2) ℂ => (starRingEnd ℂ) (M 0 0)) ∈ Pdeg 1 :=
    coordFn_mem_Pdeg_one 4
  have c01 : (fun M : Matrix (Fin 2) (Fin 2) ℂ => (starRingEnd ℂ) (M 0 1)) ∈ Pdeg 1 :=
    coordFn_mem_Pdeg_one 5
  have c10 : (fun M : Matrix (Fin 2) (Fin 2) ℂ => (starRingEnd ℂ) (M 1 0)) ∈ Pdeg 1 :=
    coordFn_mem_Pdeg_one 6
  have c11 : (fun M : Matrix (Fin 2) (Fin 2) ℂ => (starRingEnd ℂ) (M 1 1)) ∈ Pdeg 1 :=
    coordFn_mem_Pdeg_one 7
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (const_mem_Pdeg_one _) (Submodule.smul_mem _ _ c00)) (Submodule.smul_mem _ _ m00))
      (Submodule.smul_mem _ _ c10)) (Submodule.smul_mem _ _ m10))
      (Submodule.smul_mem _ _ c01)) (Submodule.smul_mem _ _ m01))
      (Submodule.smul_mem _ _ c11)) (Submodule.smul_mem _ _ m11)

def restrictU2 : (Matrix (Fin 2) (Fin 2) ℂ → ℂ) →ₗ[ℂ] (U2 → ℂ) where
  toFun F := fun k => F (k : Matrix (Fin 2) (Fin 2) ℂ)
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

theorem exists_polyFun_fejerConv {Φ : U2 → ℂ} (hc : Continuous Φ) (n : ℕ) :
    ∃ F ∈ polyFun, ∀ k : U2, fejerConv n Φ k = F (k : Matrix (Fin 2) (Fin 2) ℂ) := by
  classical

  have hsub : ∀ k : U2, (∫ h, Φ (k * h) * ((qker h ^ n : ℝ) : ℂ) ∂haarU2)
      = ∫ h, Φ h * ((aker h (k : Matrix (Fin 2) (Fin 2) ℂ) ^ n : ℝ) : ℂ) ∂haarU2 := by
    intro k
    calc ∫ h, Φ (k * h) * ((qker h ^ n : ℝ) : ℂ) ∂haarU2
        = ∫ h, Φ (k * h) * ((qker (k⁻¹ * (k * h)) ^ n : ℝ) : ℂ) ∂haarU2 := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
          show Φ (k * h) * ((qker h ^ n : ℝ) : ℂ)
            = Φ (k * h) * ((qker (k⁻¹ * (k * h)) ^ n : ℝ) : ℂ)
          rw [inv_mul_cancel_left]
      _ = ∫ h, Φ h * ((qker (k⁻¹ * h) ^ n : ℝ) : ℂ) ∂haarU2 :=
          integral_translate k (fun h => Φ h * ((qker (k⁻¹ * h) ^ n : ℝ) : ℂ))
      _ = ∫ h, Φ h * ((aker h (k : Matrix (Fin 2) (Fin 2) ℂ) ^ n : ℝ) : ℂ) ∂haarU2 := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
          show Φ h * ((qker (k⁻¹ * h) ^ n : ℝ) : ℂ)
            = Φ h * ((aker h (k : Matrix (Fin 2) (Fin 2) ℂ) ^ n : ℝ) : ℂ)
          rw [aker_coe]
  haveI : FiniteDimensional ℂ (Pdeg n) := finiteDimensional_Pdeg n

  have hmemW : ∀ h : U2,
      (fun M : Matrix (Fin 2) (Fin 2) ℂ => ((aker h M ^ n : ℝ) : ℂ)) ∈ Pdeg n := by
    intro h
    have h1 : (fun M : Matrix (Fin 2) (Fin 2) ℂ => ((aker h M : ℝ) : ℂ)) ^ n ∈ Pdeg n :=
      pow_mem_Pdeg (akerC_mem_Pdeg_one h) n
    have heq : (fun M : Matrix (Fin 2) (Fin 2) ℂ => ((aker h M ^ n : ℝ) : ℂ))
        = (fun M : Matrix (Fin 2) (Fin 2) ℂ => ((aker h M : ℝ) : ℂ)) ^ n := by
      funext M
      simp only [Pi.pow_apply]
      push_cast
      ring
    rw [heq]
    exact h1
  set T : U2 → (Pdeg n) :=
    fun h => ⟨fun M => ((aker h M ^ n : ℝ) : ℂ), hmemW h⟩ with hTdef
  set b := Module.finBasis ℂ (Pdeg n) with hbdef
  have hev : ∀ j, ∃ (m : ℕ) (e : Fin m → ℂ) (x : Fin m → Matrix (Fin 2) (Fin 2) ℂ),
      ∀ w : (Pdeg n), b.coord j w = ∑ l, e l * (w : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (x l) :=
    fun j => M4aP3C.TensorSplit.exists_eval_combination (Pdeg n) (b.coord j)
  choose m e xs hev using hev
  have hcont : ∀ j, Continuous fun h : U2 => (b.coord j) (T h) := by
    intro j
    have heq : (fun h : U2 => (b.coord j) (T h))
        = fun h : U2 => ∑ l, e j l * ((aker h (xs j l) ^ n : ℝ) : ℂ) := by
      funext h
      rw [hev j (T h)]
    rw [heq]
    exact continuous_finsetSum _ fun l _ => continuous_const.mul
      (Complex.continuous_ofReal.comp ((continuous_aker (xs j l)).pow n))
  refine ⟨∑ j, (((fejerNorm n)⁻¹ • ∫ h, Φ h * (b.coord j) (T h) ∂haarU2 : ℂ)) •
    ((b j : Matrix (Fin 2) (Fin 2) ℂ → ℂ)), ?_, ?_⟩
  · exact Pdeg_le_polyFun n (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (b j).2)
  · intro k
    unfold fejerConv
    rw [hsub k]
    have hexp : ∀ h : U2, Φ h * ((aker h (k : Matrix (Fin 2) (Fin 2) ℂ) ^ n : ℝ) : ℂ)
        = ∑ j, ((b j : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ)) *
            (Φ h * (b.coord j) (T h)) := by
      intro h
      have h0 : ((aker h ((k : Matrix (Fin 2) (Fin 2) ℂ)) ^ n : ℝ) : ℂ)
          = (T h : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ) := rfl
      have h1 : ((T h : Matrix (Fin 2) (Fin 2) ℂ → ℂ)) (k : Matrix (Fin 2) (Fin 2) ℂ)
          = ((∑ j, (b.repr (T h)) j • b j : (Pdeg n)) :
              Matrix (Fin 2) (Fin 2) ℂ → ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ) := by
        rw [b.sum_repr (T h)]
      rw [h0, h1, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Module.Basis.coord_apply]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hexp)]
    have hswap := integral_finsetSum (μ := haarU2) Finset.univ
      (f := fun j (h : U2) =>
        ((b j : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ)) *
          (Φ h * (b.coord j) (T h)))
      (fun j _ => integrable_of_continuous (continuous_const.mul (hc.mul (hcont j))))
    rw [hswap, Finset.smul_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    ring

theorem exists_polyFun_eq_of_continuous_of_rightFinite
    (Φ : U2 → ℂ) (hc : Continuous Φ)
    (hfin : ∃ s : Finset (U2 → ℂ), ∀ k : U2,
      (fun x => Φ (x * k)) ∈ Submodule.span ℂ (s : Set (U2 → ℂ))) :
    ∃ F ∈ polyFun, ∀ k : U2, Φ k = F (k : Matrix (Fin 2) (Fin 2) ℂ) := by
  obtain ⟨s, hfin⟩ := hfin
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (s : Set (U2 → ℂ))) :=
    FiniteDimensional.span_of_finite ℂ s.finite_toSet
  set V : Submodule ℂ (U2 → ℂ) := Submodule.span ℂ (s : Set (U2 → ℂ)) with hVdef
  set R : Submodule ℂ (U2 → ℂ) := polyFun.map restrictU2 with hRdef
  have hmem : ∀ n : ℕ, fejerConv n Φ ∈ V ⊓ R := by
    intro n
    refine Submodule.mem_inf.mpr ⟨fejerConv_mem_span hc hfin n, ?_⟩
    obtain ⟨F, hF, hFeq⟩ := exists_polyFun_fejerConv hc n
    exact Submodule.mem_map.mpr ⟨F, hF, by funext k; exact (hFeq k).symm⟩
  haveI : FiniteDimensional ℂ (V ⊓ R : Submodule ℂ (U2 → ℂ)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have hclosed : IsClosed ((V ⊓ R : Submodule ℂ (U2 → ℂ)) : Set (U2 → ℂ)) :=
    Submodule.closed_of_finiteDimensional _
  have htend : Filter.Tendsto (fun n => fejerConv n Φ) Filter.atTop (nhds Φ) := by
    rw [tendsto_pi_nhds]
    exact fun k => fejerConv_tendsto hc k
  have hΦ : Φ ∈ V ⊓ R :=
    hclosed.mem_of_tendsto htend (Filter.Eventually.of_forall hmem)
  obtain ⟨F, hF, hFΦ⟩ := Submodule.mem_map.mp (Submodule.mem_inf.mp hΦ).2
  exact ⟨F, hF, fun k => by rw [← hFΦ]; rfl⟩

end M4aP3C.SU2Finite
p2m_reactivate "P2MW.S_Matrix_UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite.M4aP3C P2MW.S_Matrix_UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite.M4aP3C.SU2Finite"
p2m_reactivate "P2MW.S_Matrix_UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite.M4aP3C"

end
p2m_reactivate "P2MW.S_Matrix_UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite.M4aP3C P2MW.S_Matrix_UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite.M4aP3C.SU2Finite"

noncomputable section

theorem solution
    (Φ : ↥(Matrix.unitaryGroup (Fin 2) ℂ) → ℂ) (hc : Continuous Φ)
    (hfin : ∃ s : Finset (↥(Matrix.unitaryGroup (Fin 2) ℂ) → ℂ),
      ∀ k : ↥(Matrix.unitaryGroup (Fin 2) ℂ),
        (fun x => Φ (x * k)) ∈ Submodule.span ℂ (s : Set (↥(Matrix.unitaryGroup (Fin 2) ℂ) → ℂ))) :
    ∃ F ∈ Submodule.span ℂ
        {F : Matrix (Fin 2) (Fin 2) ℂ → ℂ |
          ∃ l : List (Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ), F = fun m => (l.map (fun φ => φ m)).prod},
      ∀ k : ↥(Matrix.unitaryGroup (Fin 2) ℂ), Φ k = F (k : Matrix (Fin 2) (Fin 2) ℂ) :=
  M4aP3C.SU2Finite.exists_polyFun_eq_of_continuous_of_rightFinite Φ hc hfin

end
p2m_reactivate "P2MW.S_Matrix_UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite.M4aP3C P2MW.S_Matrix_UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite.M4aP3C.SU2Finite"

#print axioms solution

end S_Matrix_UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite
end P2MW
export P2MW.S_Matrix_UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite (solution)
