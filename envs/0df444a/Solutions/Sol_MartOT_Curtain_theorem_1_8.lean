-- Prove2me | solution 1 for MartOT.Curtain.theorem_1_8
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:47:29.934469+00:00
-- url     : https://prove2.me/submissions/07a4a20b-3926-4c92-a273-8cf4d5e4cdfb

import Mathlib
import Definitions.Def_MartOT_Var_Setting

set_option autoImplicit false
open MeasureTheory Filter Topology

namespace MCJ

/-- right derivative of `φ` -/
noncomputable def dd (φ : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin φ (Set.Ioi x) x

lemma dd_tangent {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) (x y : ℝ) :
    φ x + dd φ x * (y - x) ≤ φ y := by
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have h := hφ.rightDeriv_le_slope_of_mem_interior (x := x) (y := y)
      (by simp) (Set.mem_univ _) hxy
    rw [slope_def_field] at h
    have h2 : dd φ x ≤ (φ y - φ x) / (y - x) := h
    rw [le_div_iff₀ (sub_pos.mpr hxy)] at h2
    linarith
  · simp
  · have h1 := hφ.slope_le_leftDeriv_of_mem_interior (x := y) (y := x) (Set.mem_univ _)
      (by simp) hyx
    have h2 := hφ.leftDeriv_le_rightDeriv_of_mem_interior (x := x) (by simp)
    rw [slope_def_field] at h1
    have h3 : (φ x - φ y) / (x - y) ≤ dd φ x := h1.trans h2
    rw [div_le_iff₀ (sub_pos.mpr hyx)] at h3
    linarith

lemma dd_measurable (φ : ℝ → ℝ) : Measurable (dd φ) :=
  measurable_derivWithin_Ioi φ

lemma dd_bound {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) (n : ℝ) :
    ∃ C : ℝ, ∀ x, x ∈ Set.Icc (-n) n → |dd φ x| ≤ C := by
  refine ⟨|dd φ (-n)| + |dd φ n|, fun x hx => ?_⟩
  have h1 : dd φ (-n) ≤ dd φ x := hφ.monotoneOn_rightDeriv (by simp) (by simp) hx.1
  have h2 : dd φ x ≤ dd φ n := hφ.monotoneOn_rightDeriv (by simp) (by simp) hx.2
  rw [abs_le]
  constructor
  · have := neg_abs_le (dd φ (-n)); have := abs_nonneg (dd φ n); linarith
  · have := le_abs_self (dd φ n); have := abs_nonneg (dd φ (-n)); linarith

lemma integralE_map_eq {X : Type*} [MeasurableSpace X] (α : Measure X) (f : X → ℝ)
    (hf : Measurable f) (φ : ℝ → ℝ) (hφ : Measurable φ) :
    MartOT.Var.integralE (α.map f) φ =
      ((∫⁻ p, ENNReal.ofReal (φ (f p)) ∂α : ENNReal) : EReal) -
        ((∫⁻ p, ENNReal.ofReal (-φ (f p)) ∂α : ENNReal) : EReal) := by
  unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  have e1 : ∀ x : ℝ, ((φ x : ℝ) : EReal).toENNReal = ENNReal.ofReal (φ x) := fun x => rfl
  have e2 : ∀ x : ℝ, (-((φ x : ℝ) : EReal)).toENNReal = ENNReal.ofReal (-φ x) := by
    intro x; rw [← EReal.coe_neg]; rfl
  simp only [e1, e2]
  rw [lintegral_map (by fun_prop) hf, lintegral_map (by fun_prop) hf]

lemma integrable_of_lintegral_fin {X : Type*} [MeasurableSpace X] {α : Measure X} {g : X → ℝ}
    (hg : Measurable g) (h1 : ∫⁻ p, ENNReal.ofReal (g p) ∂α < ⊤)
    (h2 : ∫⁻ p, ENNReal.ofReal (-g p) ∂α < ⊤) : Integrable g α := by
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  have : ∀ p, ‖g p‖ₑ ≤ ENNReal.ofReal (g p) + ENNReal.ofReal (-g p) := by
    intro p
    rw [Real.enorm_eq_ofReal_abs]
    rcases le_total 0 (g p) with h | h
    · rw [abs_of_nonneg h]; simp
    · rw [abs_of_nonpos h]; simp
  calc ∫⁻ p, ‖g p‖ₑ ∂α ≤ ∫⁻ p, (ENNReal.ofReal (g p) + ENNReal.ofReal (-g p)) ∂α :=
        lintegral_mono this
    _ = _ := lintegral_add_left (by fun_prop) _
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨h1, h2⟩

end MCJ
namespace MCJ

lemma neg_part_fin {α : Measure (ℝ × ℝ)} [IsFiniteMeasure α] {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) (h : ℝ × ℝ → ℝ) (hi : Integrable h α) :
    ∫⁻ p, ENNReal.ofReal (-φ (h p)) ∂α < ⊤ := by
  have hint : Integrable (fun p => |φ 0| + |dd φ 0| * |h p|) α :=
    (integrable_const _).add (hi.abs.const_mul _)
  refine lt_of_le_of_lt (lintegral_mono fun p => ENNReal.ofReal_le_ofReal ?_) hint.lintegral_lt_top
  have h1 := dd_tangent hφ 0 (h p)
  have a1 := neg_abs_le (φ 0)
  have a2 : -(dd φ 0 * h p) ≤ |dd φ 0| * |h p| := by rw [← abs_mul]; exact neg_le_abs _
  simp only [sub_zero] at h1
  linarith

lemma jensen_core {α : Measure (ℝ × ℝ)} [IsFiniteMeasure α]
    (hX : Integrable (fun p : ℝ × ℝ => p.1) α)
    (hY : Integrable (fun p : ℝ × ℝ => p.2) α)
    (hM : ∀ ρ : ℝ → ℝ, Measurable ρ → (∃ C, ∀ x, |ρ x| ≤ C) →
      ∫ p, ρ p.1 * (p.2 - p.1) ∂α = 0)
    {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ)
    (hfin : ∫⁻ p, ENNReal.ofReal (φ p.2) ∂α < ⊤) :
    ∫⁻ p, ENNReal.ofReal (φ p.1) ∂α < ⊤ ∧
    (∫⁻ p, ENNReal.ofReal (φ p.1) ∂α).toReal - (∫⁻ p, ENNReal.ofReal (-φ p.1) ∂α).toReal ≤
    (∫⁻ p, ENNReal.ofReal (φ p.2) ∂α).toReal - (∫⁻ p, ENNReal.ofReal (-φ p.2) ∂α).toReal := by
  have hφc : Continuous φ := continuousOn_univ.mp (hφ.continuousOn isOpen_univ)
  have hφm : Measurable φ := hφc.measurable
  have hBx := neg_part_fin hφ (fun p : ℝ × ℝ => p.1) hX
  have hBy := neg_part_fin hφ (fun p : ℝ × ℝ => p.2) hY
  have hgi : Integrable (fun p : ℝ × ℝ => φ p.2) α :=
    integrable_of_lintegral_fin (hφm.comp measurable_snd) hfin hBy
  have hJ : ∫ p, φ p.2 ∂α = (∫⁻ p, ENNReal.ofReal (φ p.2) ∂α).toReal -
      (∫⁻ p, ENNReal.ofReal (-φ p.2) ∂α).toReal :=
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hgi
  set Bx := ∫⁻ p, ENNReal.ofReal (-φ p.1) ∂α with hBxdef
  set Ax := ∫⁻ p, ENNReal.ofReal (φ p.1) ∂α with hAxdef
  set J := ∫ p, φ p.2 ∂α with hJdef
  let K : ℕ → Set (ℝ × ℝ) := fun n => {p | |p.1| ≤ (n : ℝ)}
  have hKm : ∀ n, MeasurableSet (K n) := fun n =>
    measurableSet_le (measurable_fst.abs) measurable_const
  have hKmono : Monotone K := by
    intro m n hmn p hp
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact le_trans hp this
  have hU : (⋃ n, K n) = Set.univ := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_ge |p.1|
    exact ⟨n, hn⟩
  have key : ∀ n : ℕ, (∫⁻ p in K n, ENNReal.ofReal (φ p.1) ∂α) ≠ ⊤ ∧
      (∫⁻ p in K n, ENNReal.ofReal (φ p.1) ∂α).toReal ≤
        (∫ p in K n, φ p.2 ∂α) + Bx.toReal := by
    intro n
    obtain ⟨Cf, hCf⟩ : ∃ C, ∀ x ∈ Set.Icc (-(n : ℝ)) n, ‖φ x‖ ≤ C :=
      isCompact_Icc.exists_bound_of_continuousOn hφc.continuousOn
    have hfi : Integrable (fun p : ℝ × ℝ => φ p.1) (α.restrict (K n)) := by
      refine Integrable.of_bound ((hφm.comp measurable_fst).aestronglyMeasurable) Cf ?_
      refine (ae_restrict_iff' (hKm n)).mpr (Filter.Eventually.of_forall fun p hp => ?_)
      exact hCf _ (abs_le.mp hp)
    obtain ⟨Cd, hCd⟩ := dd_bound hφ n
    set ρ : ℝ → ℝ := (Set.Icc (-(n : ℝ)) n).indicator (dd φ) with hρdef
    have hρm : Measurable ρ := (dd_measurable φ).indicator measurableSet_Icc
    have hρb : ∀ x, |ρ x| ≤ max Cd 0 := by
      intro x
      by_cases hx : x ∈ Set.Icc (-(n : ℝ)) n
      · simp only [hρdef, Set.indicator_of_mem hx]; exact (hCd x hx).trans (le_max_left _ _)
      · simp only [hρdef, Set.indicator_of_notMem hx]; simp
    have hρ0 := hM ρ hρm ⟨max Cd 0, hρb⟩
    have hti : Integrable (fun p : ℝ × ℝ => ρ p.1 * (p.2 - p.1)) α :=
      (hY.sub hX).bdd_mul (hρm.comp measurable_fst).aestronglyMeasurable
        (c := max Cd 0) (Filter.Eventually.of_forall fun p => by
          rw [Real.norm_eq_abs]; exact hρb p.1)
    have h0' : ∫ p in K n, ρ p.1 * (p.2 - p.1) ∂α = 0 := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      · exact hρ0
      · intro p hp
        have : p.1 ∉ Set.Icc (-(n : ℝ)) n := fun h => hp (abs_le.mpr h)
        simp [hρdef, Set.indicator_of_notMem this]
    have hineq : ∫ p in K n, (φ p.1 + ρ p.1 * (p.2 - p.1)) ∂α ≤ ∫ p in K n, φ p.2 ∂α := by
      refine setIntegral_mono_on (hfi.add hti.integrableOn) hgi.integrableOn (hKm n) ?_
      intro p hp
      have hp' : p.1 ∈ Set.Icc (-(n : ℝ)) n := abs_le.mp hp
      simp only [hρdef, Set.indicator_of_mem hp']
      have := dd_tangent hφ p.1 p.2
      linarith
    rw [integral_add hfi hti.integrableOn, h0', add_zero] at hineq
    have hlt := hfi.lintegral_lt_top
    have hnn := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi
    refine ⟨hlt.ne, ?_⟩
    have hb : (∫⁻ p in K n, ENNReal.ofReal (-φ p.1) ∂α).toReal ≤ Bx.toReal :=
      ENNReal.toReal_mono hBx.ne (setLIntegral_le_lintegral _ _)
    linarith
  have hgint : Tendsto (fun n : ℕ => ∫ p in K n, φ p.2 ∂α) atTop (𝓝 J) := by
    have := tendsto_setIntegral_of_monotone hKm hKmono (f := fun p : ℝ × ℝ => φ p.2) (μ := α)
      (by rw [hU]; exact hgi.integrableOn)
    simpa [hU] using this
  have hAxsup : Ax = ⨆ n, ∫⁻ p in K n, ENNReal.ofReal (φ p.1) ∂α := by
    rw [← setLIntegral_iUnion_of_directed _ hKmono.directed_le, hU, Measure.restrict_univ]
  have hnonneg : 0 ≤ J + Bx.toReal := by
    refine ge_of_tendsto' (hgint.add_const _) (fun n => ?_)
    exact (ENNReal.toReal_nonneg).trans (key n).2
  have hAxle : Ax ≤ ENNReal.ofReal (J + Bx.toReal) := by
    rw [hAxsup]
    refine iSup_le fun m => ?_
    refine ge_of_tendsto (ENNReal.tendsto_ofReal (hgint.add_const Bx.toReal)) ?_
    filter_upwards [Filter.eventually_ge_atTop m] with n hn
    calc (∫⁻ p in K m, ENNReal.ofReal (φ p.1) ∂α)
        ≤ ∫⁻ p in K n, ENNReal.ofReal (φ p.1) ∂α := lintegral_mono_set (hKmono hn)
      _ = ENNReal.ofReal ((∫⁻ p in K n, ENNReal.ofReal (φ p.1) ∂α).toReal) :=
          (ENNReal.ofReal_toReal (key n).1).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (key n).2
  have hAxlt : Ax < ⊤ := lt_of_le_of_lt hAxle ENNReal.ofReal_lt_top
  refine ⟨hAxlt, ?_⟩
  have h1 : Ax.toReal ≤ J + Bx.toReal := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hAxle
    rwa [ENNReal.toReal_ofReal hnonneg] at this
  rw [← hJ]
  linarith

lemma convexLE_of_martingale {α : Measure (ℝ × ℝ)} [IsFiniteMeasure α]
    (hX : Integrable (fun p : ℝ × ℝ => p.1) α)
    (hY : Integrable (fun p : ℝ × ℝ => p.2) α)
    (hM : ∀ ρ : ℝ → ℝ, Measurable ρ → (∃ C, ∀ x, |ρ x| ≤ C) →
      ∫ p, ρ p.1 * (p.2 - p.1) ∂α = 0) :
    MartOT.Var.ConvexLE (α.map Prod.fst) (α.map Prod.snd) := by
  refine ⟨⟨inferInstance, ?_⟩, ⟨inferInstance, ?_⟩, ?_⟩
  · exact (integrable_map_measure (by fun_prop) measurable_fst.aemeasurable).mpr hX
  · exact (integrable_map_measure (by fun_prop) measurable_snd.aemeasurable).mpr hY
  · intro φ hφ
    have hφc : Continuous φ := continuousOn_univ.mp (hφ.continuousOn isOpen_univ)
    have hφm : Measurable φ := hφc.measurable
    rw [integralE_map_eq α Prod.fst measurable_fst φ hφm,
      integralE_map_eq α Prod.snd measurable_snd φ hφm]
    have hBx := neg_part_fin hφ (fun p : ℝ × ℝ => p.1) hX
    have hBy := neg_part_fin hφ (fun p : ℝ × ℝ => p.2) hY
    by_cases hAy : ∫⁻ p, ENNReal.ofReal (φ p.2) ∂α = ⊤
    · rw [hAy, EReal.coe_ennreal_top, ← EReal.coe_ennreal_toReal hBy.ne]
      rw [EReal.top_sub_coe]
      exact le_top
    · have hAy' := lt_top_iff_ne_top.mpr hAy
      obtain ⟨hAx, hle⟩ := jensen_core hX hY hM hφ hAy'
      rw [← EReal.coe_ennreal_toReal hAx.ne, ← EReal.coe_ennreal_toReal hBx.ne,
        ← EReal.coe_ennreal_toReal hAy, ← EReal.coe_ennreal_toReal hBy.ne,
        ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      exact hle

end MCJ

namespace MCJ

lemma restrict_martingale {μ ν : Measure ℝ} {π : Measure (ℝ × ℝ)}
    (hμν : MartOT.Var.ConvexLE μ ν) (hπ : MartOT.Var.IsMartingalePlan μ ν π) (t : ℝ) :
    MartOT.Var.ConvexLE (μ.restrict (Set.Iic t)) (MartOT.Var.targetUpTo π t) := by
  obtain ⟨⟨hp1, hp2⟩, hint, hmart⟩ := hπ
  have hfin : IsFiniteMeasure π := by
    refine ⟨?_⟩
    have h := congrArg (fun m : Measure ℝ => m Set.univ) hp1
    simp only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] at h
    rw [h]
    haveI := hμν.1.1
    exact measure_lt_top _ _
  set S : Set (ℝ × ℝ) := Set.Iic t ×ˢ Set.univ with hS
  have hSm : MeasurableSet S := measurableSet_Iic.prod MeasurableSet.univ
  haveI : IsFiniteMeasure (π.restrict S) := inferInstance
  have hXπ : Integrable (fun p : ℝ × ℝ => p.1) π := by
    have := hμν.1.2
    rw [← hp1] at this
    exact (integrable_map_measure (by fun_prop) measurable_fst.aemeasurable).mp this
  have hYπ : Integrable (fun p : ℝ × ℝ => p.2) π := by
    have := hμν.2.1.2
    rw [← hp2] at this
    exact (integrable_map_measure (by fun_prop) measurable_snd.aemeasurable).mp this
  have hmapfst : (π.restrict S).map Prod.fst = μ.restrict (Set.Iic t) := by
    rw [← hp1, Measure.restrict_map measurable_fst measurableSet_Iic]
    congr 2
    ext p; simp [hS]
  have key := convexLE_of_martingale (α := π.restrict S) hXπ.restrict hYπ.restrict (by
    intro ρ hρ ⟨C, hC⟩
    rw [← integral_indicator hSm]
    have : S.indicator (fun p : ℝ × ℝ => ρ p.1 * (p.2 - p.1)) =
        fun p => ((Set.Iic t).indicator ρ) p.1 * (p.2 - p.1) := by
      ext p
      by_cases hp : p.1 ≤ t
      · have : p ∈ S := ⟨hp, Set.mem_univ _⟩
        simp [Set.indicator_of_mem this, Set.indicator_of_mem (show p.1 ∈ Set.Iic t from hp)]
      · have : p ∉ S := fun h => hp h.1
        simp [Set.indicator_of_notMem this,
          Set.indicator_of_notMem (show p.1 ∉ Set.Iic t from hp)]
    rw [this]
    refine hmart _ (hρ.indicator measurableSet_Iic) ⟨C, fun x => ?_⟩
    by_cases hx : x ∈ Set.Iic t
    · rw [Set.indicator_of_mem hx]; exact hC x
    · rw [Set.indicator_of_notMem hx]
      simpa using (abs_nonneg _).trans (hC 0))
  rw [hmapfst] at key
  exact key

lemma targetUpTo_le {ν : Measure ℝ} {π : Measure (ℝ × ℝ)} (hp2 : π.map Prod.snd = ν) (t : ℝ) :
    MartOT.Var.targetUpTo π t ≤ ν := by
  rw [← hp2]
  unfold MartOT.Var.targetUpTo
  exact Measure.map_mono Measure.restrict_le_self measurable_snd

end MCJ

theorem solution (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (πlc : Measure (ℝ × ℝ)) (hlc : MartOT.Var.IsLeftCurtain μ ν πlc) (t : ℝ) :
    ∀ π : Measure (ℝ × ℝ), MartOT.Var.IsMartingalePlan μ ν π →
      MartOT.Var.ConvexLE (MartOT.Var.targetUpTo πlc t) (MartOT.Var.targetUpTo π t) := by
  intro π hπ
  exact ((hlc.2 t).2).2.2 _ (MCJ.targetUpTo_le hπ.1.2 t) (MCJ.restrict_martingale hμν hπ t)
