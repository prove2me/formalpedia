-- Prove2me | solution 1 for MartOT.Opt.theorem_1_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T10:42:48.908841+00:00
-- url     : https://prove2.me/submissions/cd14d6d3-97d6-4c09-aee3-76115c525625

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Theorems.Thm_MartOT_Opt_optimizer_exists
import Theorems.Thm_MartOT_Opt_optimizer_monotone
import Theorems.Thm_MartOT_Opt_theorem_5_3

set_option autoImplicit false

open MeasureTheory MeasurableSpace

namespace MartOT.Lib17

/-- `integralE` of an integrable real function is the coercion of its Bochner integral. -/
lemma integralE_eq_coe {X : Type*} [MeasurableSpace X] (m : Measure X) (f : X → ℝ)
    (hf : Integrable f m) : MartOT.Var.integralE m f = ((∫ x, f x ∂m : ℝ) : EReal) := by
  unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  have e1 : ∀ x, ((f x : ℝ) : EReal).toENNReal = ENNReal.ofReal (max (f x) 0) := fun x => by
    rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
    rcases le_total 0 (f x) with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  have e2 : ∀ x, (-((f x : ℝ) : EReal)).toENNReal = ENNReal.ofReal (max (-f x) 0) := fun x => by
    rw [← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
    rcases le_total 0 (-f x) with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  simp_rw [e1, e2]
  rw [← ofReal_integral_eq_lintegral_ofReal hf.pos_part (Filter.Eventually.of_forall
      (fun x => le_max_right _ _)),
    ← ofReal_integral_eq_lintegral_ofReal (show Integrable (fun x => max (-f x) 0) m from hf.neg.pos_part) (Filter.Eventually.of_forall
      (fun x => le_max_right _ _)),
    EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal,
    max_eq_left (integral_nonneg (fun x => le_max_right (f x) 0)),
    max_eq_left (integral_nonneg (fun x => le_max_right (-f x) 0)), ← EReal.coe_sub]
  congr 1
  rw [← integral_sub hf.pos_part (show Integrable (fun x => max (-f x) 0) m from hf.neg.pos_part)]
  congr 1
  ext x
  rcases le_total 0 (f x) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

lemma hinge_convex (k : ℝ) : ConvexOn ℝ Set.univ (fun y : ℝ => max (y - k) 0) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have h1 : a * x + b * y - k = a * (x - k) + b * (y - k) := by
    have : k = a * k + b * k := by rw [← add_mul, hab, one_mul]
    linarith
  apply max_le
  · rw [h1]
    exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
  · positivity

lemma inM_integrable_hinge (η : Measure ℝ) (hη : MartOT.Var.InM η) (k : ℝ) :
    Integrable (fun y : ℝ => max (y - k) 0) η := by
  have := hη.1
  exact (hη.2.sub (integrable_const k)).pos_part

/-- Equal convex integrals in both directions give equal hinge integrals. -/
lemma cx_eq_integral (η η' : Measure ℝ) (h : MartOT.Var.ConvexLE η η')
    (h' : MartOT.Var.ConvexLE η' η) (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ)
    (hi : Integrable φ η) (hi' : Integrable φ η') : ∫ y, φ y ∂η = ∫ y, φ y ∂η' := by
  have a := h.2.2 φ hφ
  have b := h'.2.2 φ hφ
  rw [integralE_eq_coe η φ hi, integralE_eq_coe η' φ hi'] at a b
  exact le_antisymm (EReal.coe_le_coe_iff.1 a) (EReal.coe_le_coe_iff.1 b)

/-- Antisymmetry of the convex order. -/
lemma cx_antisymm (η η' : Measure ℝ) (h : MartOT.Var.ConvexLE η η')
    (h' : MartOT.Var.ConvexLE η' η) : η = η' := by
  have := h.1.1
  have := h.2.1.1
  have hc : ∫ y, (1 : ℝ) ∂η = ∫ y, (1 : ℝ) ∂η' :=
    cx_eq_integral η η' h h' (fun _ => 1) (convexOn_const 1 convex_univ)
      (integrable_const _) (integrable_const _)
  have hh : ∀ k : ℝ, ∫ y, max (y - k) 0 ∂η = ∫ y, max (y - k) 0 ∂η' := fun k =>
    cx_eq_integral η η' h h' _ (hinge_convex k) (inM_integrable_hinge η h.1 k)
      (inM_integrable_hinge η' h.2.1 k)
  -- the approximants g n = 1 - (n+1) (y-k)^+ + (n+1) (y-k-1/(n+1))^+
  have key : ∀ k : ℝ, η (Set.Iic k) = η' (Set.Iic k) := by
    intro k
    let g : ℕ → ℝ → ℝ := fun n y => 1 - ((n : ℝ) + 1) * max (y - k) 0
      + ((n : ℝ) + 1) * max (y - (k + 1 / ((n : ℝ) + 1))) 0
    have gint : ∀ (m : Measure ℝ), MartOT.Var.InM m → ∀ n, Integrable (g n) m := by
      intro m hm n
      have := hm.1
      exact ((integrable_const 1).sub ((inM_integrable_hinge m hm k).const_mul _)).add
        ((inM_integrable_hinge m hm _).const_mul _)
    have geq : ∀ n, ∫ y, g n y ∂η = ∫ y, g n y ∂η' := by
      intro n
      have e : ∀ (m : Measure ℝ), MartOT.Var.InM m → ∫ y, g n y ∂m =
          ∫ y, (1 : ℝ) ∂m - ((n : ℝ) + 1) * ∫ y, max (y - k) 0 ∂m
            + ((n : ℝ) + 1) * ∫ y, max (y - (k + 1 / ((n : ℝ) + 1))) 0 ∂m := by
        intro m hm
        have := hm.1
        simp only [g]
        rw [integral_add, integral_sub, integral_const_mul, integral_const_mul]
        · exact integrable_const 1
        · exact (inM_integrable_hinge m hm k).const_mul _
        · exact (integrable_const 1).sub ((inM_integrable_hinge m hm k).const_mul _)
        · exact (inM_integrable_hinge m hm _).const_mul _
      rw [e η h.1, e η' h.2.1, hc, hh k, hh (k + 1 / ((n : ℝ) + 1))]
    have gbound : ∀ n y, ‖g n y‖ ≤ 1 := by
      intro n y
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hd : ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) = 1 := by field_simp
      simp only [g, Real.norm_eq_abs]
      rcases le_total y k with hy | hy
      · rw [max_eq_right (by linarith), max_eq_right (by
          have : 0 < 1 / ((n : ℝ) + 1) := by positivity
          linarith)]
        simp
      · rcases le_total y (k + 1 / ((n : ℝ) + 1)) with hy2 | hy2
        · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
          have : ((n : ℝ) + 1) * (y - k) ≤ 1 := by
            have := mul_le_mul_of_nonneg_left (show y - k ≤ 1 / ((n : ℝ) + 1) by linarith)
              hn.le
            linarith
          have : 0 ≤ ((n : ℝ) + 1) * (y - k) := mul_nonneg hn.le (by linarith)
          rw [abs_le]; constructor <;> linarith
        · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
          have : 1 - ((n : ℝ) + 1) * (y - k) + ((n : ℝ) + 1) * (y - (k + 1 / ((n : ℝ) + 1)))
              = 0 := by linarith [hd]
          rw [this]; simp
    have glim : ∀ y, Filter.Tendsto (fun n => g n y) Filter.atTop
        (nhds ((Set.Iic k).indicator (fun _ => (1 : ℝ)) y)) := by
      intro y
      rcases le_or_gt y k with hy | hy
      · rw [Set.indicator_of_mem (show y ∈ Set.Iic k from hy)]
        apply tendsto_const_nhds.congr
        intro n
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        simp only [g]
        rw [max_eq_right (by linarith), max_eq_right (by linarith)]
        ring
      · rw [Set.indicator_of_notMem (show y ∉ Set.Iic k from not_le.2 hy)]
        obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.2 hy)
        apply tendsto_const_nhds.congr'
        filter_upwards [Filter.eventually_ge_atTop N] with n hn
        have hn' : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast Nat.add_le_add_right hn 1
        have hd : ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) = 1 := by field_simp
        simp only [g]
        rw [max_eq_left (by linarith), max_eq_left (by linarith)]
        linarith
    have lim : ∀ (m : Measure ℝ), MartOT.Var.InM m → Filter.Tendsto
        (fun n => ∫ y, g n y ∂m) Filter.atTop (nhds (m.real (Set.Iic k))) := by
      intro m hm
      have := hm.1
      have := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
        (fun n => (gint m hm n).aestronglyMeasurable) (integrable_const 1)
        (fun n => Filter.Eventually.of_forall (gbound n))
        (Filter.Eventually.of_forall glim)
      rwa [integral_indicator_const _ measurableSet_Iic, smul_eq_mul, mul_one] at this
    have hr : η.real (Set.Iic k) = η'.real (Set.Iic k) := by
      refine tendsto_nhds_unique (lim η h.1) ?_
      simp_rw [geq]
      exact lim η' h.2.1
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 hr
  exact Measure.ext_of_Iic η η' key

/-- The shadow is unique. -/
lemma shadow_unique (ν m η η' : Measure ℝ) (h : MartOT.Var.IsShadow ν m η)
    (h' : MartOT.Var.IsShadow ν m η') : η = η' :=
  cx_antisymm η η' (h.2.2 η' h'.1 h'.2.1) (h'.2.2 η h.1 h.2.1)

/-- A finite measure on `ℝ × ℝ` is determined by its targets `targetUpTo π t` and its mass. -/
lemma plan_eq_of_targets (π π' : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (huniv : π Set.univ = π' Set.univ)
    (h : ∀ t, MartOT.Var.targetUpTo π t = MartOT.Var.targetUpTo π' t) : π = π' := by
  have hrect : ∀ (m : Measure (ℝ × ℝ)) (t : ℝ) (B : Set ℝ), MeasurableSet B →
      m (Set.Iic t ×ˢ B) = MartOT.Var.targetUpTo m t B := by
    intro m t B hB
    unfold MartOT.Var.targetUpTo
    rw [Measure.map_apply measurable_snd hB, Measure.restrict_apply (measurable_snd hB)]
    congr 1
    ext p
    simp [and_comm]
  have hgen : generateFrom (Set.image2 (· ×ˢ ·) (Set.range (Set.Iic : ℝ → Set ℝ))
      {s : Set ℝ | MeasurableSet s}) = (inferInstance : MeasurableSpace (ℝ × ℝ)) := by
    refine generateFrom_eq_prod ?_ generateFrom_measurableSet ?_ isCountablySpanning_measurableSet
    · exact (borel_eq_generateFrom_Iic ℝ).symm.trans BorelSpace.measurable_eq.symm
    · refine ⟨fun n : ℕ => Set.Iic (n : ℝ), fun n => ⟨n, rfl⟩, ?_⟩
      ext x
      simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]
      exact (exists_nat_ge x)
  refine ext_of_generate_finite _ hgen.symm (isPiSystem_Iic.prod isPiSystem_measurableSet)
    ?_ huniv
  rintro s ⟨A, ⟨t, rfl⟩, B, hB, rfl⟩
  rw [hrect π t B hB, hrect π' t B hB, h t]

/-- Two left-curtain plans with the same first marginal coincide. -/
lemma curtain_unique (μ ν : Measure ℝ) (π π' : Measure (ℝ × ℝ))
    (h1 : MartOT.Var.IsLeftCurtain μ ν π) (h2 : MartOT.Var.IsLeftCurtain μ ν π')
    (hm1 : π.map Prod.fst = μ) (hm2 : π'.map Prod.fst = μ) : π = π' := by
  have := h1.1
  have huniv : π Set.univ = π' Set.univ := by
    have a := congrArg (fun m : Measure ℝ => m Set.univ) hm1
    have b := congrArg (fun m : Measure ℝ => m Set.univ) hm2
    simp only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] at a b
    rw [a, b]
  exact plan_eq_of_targets π π' huniv (fun t => shadow_unique ν _ _ _ (h1.2 t).2 (h2.2 t).2)

end MartOT.Lib17

open MeasureTheory in
theorem solution (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (h : ℝ → ℝ) (hd : Differentiable ℝ h)
    (hconv : StrictConvexOn ℝ Set.univ (deriv h))
    (hint : MartOT.Var.SuffIntegrable μ ν (fun x y => h (y - x)))
    (hfin : MartOT.Var.CM (fun x y => h (y - x)) μ ν < ⊤) :
    ∃ π : Measure (ℝ × ℝ), MartOT.Var.IsLeftCurtain μ ν π ∧ MartOT.Var.IsOptimal (fun x y => h (y - x)) μ ν π ∧
      ∀ π' : Measure (ℝ × ℝ), MartOT.Var.IsOptimal (fun x y => h (y - x)) μ ν π' → π' = π := by
  obtain ⟨π0, hπ0, hπ0fin⟩ : ∃ π0 : Measure (ℝ × ℝ), MartOT.Var.IsMartingalePlan μ ν π0 ∧
      MartOT.Var.cost (fun x y => h (y - x)) π0 < ⊤ := by
    unfold MartOT.Var.CM at hfin
    obtain ⟨π0, h1⟩ := iInf_lt_iff.1 hfin
    obtain ⟨hp, h2⟩ := iInf_lt_iff.1 h1
    exact ⟨π0, hp, h2⟩
  have hlsc : LowerSemicontinuous (Function.uncurry (fun x y : ℝ => h (y - x))) := by
    have : Continuous (Function.uncurry (fun x y : ℝ => h (y - x))) := by
      show Continuous (fun p : ℝ × ℝ => h (p.2 - p.1))
      exact hd.continuous.comp (continuous_snd.sub continuous_fst)
    exact this.lowerSemicontinuous
  obtain ⟨π, hπ⟩ := MartOT.Opt.optimizer_exists μ ν hμν.1 hμν.2.1 (fun x y => h (y - x)) hlsc
    hint ⟨π0, hπ0⟩
  have key : ∀ π' : Measure (ℝ × ℝ), MartOT.Var.IsOptimal (fun x y => h (y - x)) μ ν π' →
      MartOT.Var.IsLeftCurtain μ ν π' := by
    intro π' hπ'
    have hfin' : MartOT.Var.cost (fun x y => h (y - x)) π' < ⊤ :=
      lt_of_le_of_lt (hπ'.2 π0 hπ0) hπ0fin
    have hmono := MartOT.Opt.optimizer_monotone μ ν hμν h hd hconv hint π' hπ' hfin'
    have hfst : π'.map Prod.fst = μ := hπ'.1.1.1
    have hsnd : π'.map Prod.snd = ν := hπ'.1.1.2
    have hfm : IsFiniteMeasure π' := by
      refine ⟨?_⟩
      have a := congrArg (fun m : Measure ℝ => m Set.univ) hfst
      simp only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] at a
      rw [a]
      exact measure_lt_top μ Set.univ
    have := MartOT.Opt.theorem_5_3 π' (by rw [hfst]; exact hμν.1) (by rw [hsnd]; exact hμν.2.1)
      (by rw [hfst, hsnd]; exact hπ'.1) hmono
    rwa [hfst, hsnd] at this
  refine ⟨π, key π hπ, hπ, fun π' hπ' => ?_⟩
  exact MartOT.Lib17.curtain_unique μ ν π' π (key π' hπ') (key π hπ) hπ'.1.1.1 hπ.1.1.1
