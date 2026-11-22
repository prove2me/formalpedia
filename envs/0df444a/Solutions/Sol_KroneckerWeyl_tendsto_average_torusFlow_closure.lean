-- Prove2me | solution 1 for KroneckerWeyl.tendsto_average_torusFlow_closure
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:47:52.994903+00:00
-- url     : https://prove2.me/submissions/68229caa-ebfb-414f-9b37-f8b4e847fb2c

import Mathlib

open MeasureTheory Filter Topology

set_option autoImplicit false

namespace Sol_KroneckerWeyl_tendsto_average_torusFlow_closure

noncomputable section

open Filter Function MeasureTheory Set Real UnitAddTorus
open scoped Topology

variable {ι : Type*}

/-- The linear flow on the torus with frequency vector `τ`. -/
def flow (τ : ι → ℝ) (t : ℝ) : UnitAddTorus ι := fun k => ((t * τ k : ℝ) : UnitAddCircle)

theorem continuous_flow (τ : ι → ℝ) : Continuous (flow τ) := by
  unfold flow
  fun_prop

theorem range_flow_neg (τ : ι → ℝ) : range (flow (-τ)) = range (flow τ) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨-t, ?_⟩
    funext k
    simp only [flow, Pi.neg_apply]
    congr 1
    ring
  · rintro ⟨t, rfl⟩
    refine ⟨-t, ?_⟩
    funext k
    simp only [flow, Pi.neg_apply]
    congr 1
    ring

variable [Fintype ι]

/-- Each exponential monomial is a character of the torus. -/
theorem mFourier_add_apply (n : ι → ℤ) (x y : UnitAddTorus ι) :
    mFourier n (x + y) = mFourier n x * mFourier n y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, smul_add,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

/-- Along the flow, an exponential monomial is the exponential of the paired frequency. -/
theorem mFourier_flow (τ : ι → ℝ) (n : ι → ℤ) (t : ℝ) :
    mFourier n (flow τ t) =
      Complex.exp (2 * π * Complex.I * ((∑ i, (n i : ℝ) * τ i : ℝ) : ℂ) * t) := by
  have h (i : ι) : (flow τ t) i = ((t * τ i : ℝ) : AddCircle (1 : ℝ)) := rfl
  simp only [mFourier, ContinuousMap.coe_mk, h, fourier_coe_apply, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

theorem exp_half_period {c : ℝ} (hc : c ≠ 0) :
    Complex.exp (2 * π * Complex.I * (c : ℂ) * ((1 / (2 * c) : ℝ) : ℂ)) = -1 := by
  rw [show 2 * (π : ℂ) * Complex.I * (c : ℂ) * ((1 / (2 * c) : ℝ) : ℂ) =
      π * Complex.I by
    push_cast; field_simp [hc]]
  exact Complex.exp_pi_mul_I

/-- The time averages of a nonconstant imaginary exponential tend to zero. -/
theorem tendsto_average_exp {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun T : ℝ ↦ (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, Complex.exp (2 * π * Complex.I * c * t))
      atTop (𝓝 0) := by
  have ha : (2 * π * Complex.I * c : ℂ) ≠ 0 := by
    simp [hc, Real.pi_ne_zero, Complex.I_ne_zero]
  have hint (T : ℝ) : ∫ t in (0 : ℝ)..T, Complex.exp (2 * π * Complex.I * c * t) =
      (Complex.exp (2 * π * Complex.I * c * T) - 1) / (2 * π * Complex.I * c) := by
    rw [integral_exp_mul_complex ha]; simp
  have hb (T : ℝ) : ‖Complex.exp (2 * π * Complex.I * c * T) - 1‖ ≤ 2 := by
    calc _ ≤ ‖Complex.exp (2 * π * Complex.I * c * T)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [show (2 * π * Complex.I * c * T : ℂ) = ((2 * π * c * T : ℝ) : ℂ) * Complex.I by
          push_cast; ring, Complex.norm_exp_ofReal_mul_I]
        norm_num
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (by simpa using tendsto_inv_atTop_zero.const_mul (2 / ‖(2 * π * Complex.I * c : ℂ)‖))
  refine (eventually_gt_atTop 0).mono fun T hT ↦ ?_
  rw [hint, norm_mul, norm_div, norm_inv, Complex.norm_real, Real.norm_of_nonneg hT.le,
    mul_comm]
  gcongr
  all_goals first
    | exact hb T
    | simp [abs_of_pos Real.pi_pos]

/-- The integral of an exponential monomial over the orbit closure: it is `1` if the monomial is
trivial along the flow and `0` otherwise. -/
theorem integral_mFourier_closure (τ : ι → ℝ) (G : AddSubgroup (UnitAddTorus ι))
    (hG : (G : Set (UnitAddTorus ι)) = closure (range (flow τ)))
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ] (n : ι → ℤ) :
    ∫ g : G, mFourier n (g : UnitAddTorus ι) ∂μ =
      if (∑ i, (n i : ℝ) * τ i) = 0 then 1 else 0 := by
  split_ifs with hc
  · have hone : ∀ x ∈ closure (range (flow τ)), mFourier n x = 1 := by
      have hsub : range (flow τ) ⊆ {x | mFourier n x = 1} := by
        rintro _ ⟨t, rfl⟩
        simp only [mem_ofPred_eq, mFourier_flow, hc]
        simp
      have hcl : IsClosed {x : UnitAddTorus ι | mFourier n x = 1} :=
        isClosed_eq (mFourier n).continuous continuous_const
      exact fun x hx ↦ closure_minimal hsub hcl hx
    have h1 : (fun g : G ↦ mFourier n (g : UnitAddTorus ι)) = fun _ ↦ (1 : ℂ) := by
      funext g
      exact hone g (hG ▸ g.2)
    rw [h1]
    simp
  · set c := ∑ i, (n i : ℝ) * τ i
    have hmem : flow τ (1 / (2 * c)) ∈ G := by
      rw [← SetLike.mem_coe, hG]
      exact subset_closure ⟨_, rfl⟩
    let g₀ : G := ⟨flow τ (1 / (2 * c)), hmem⟩
    have hw : mFourier n (g₀ : UnitAddTorus ι) = -1 := by
      change mFourier n (flow τ (1 / (2 * c))) = -1
      rw [mFourier_flow]
      exact exp_half_period hc
    have h1 := integral_add_left_eq_self (μ := μ) (fun g : G ↦ mFourier n (g : UnitAddTorus ι))
      g₀
    simp only [AddSubgroup.coe_add, mFourier_add_apply, hw, integral_const_mul] at h1
    linear_combination (-1 / 2 : ℂ) * h1

/-- Weyl's argument: the forward time averages of every continuous function converge to its
integral over the orbit closure. -/
theorem tendsto_forward_average (τ : ι → ℝ) (G : AddSubgroup (UnitAddTorus ι))
    (hG : (G : Set (UnitAddTorus ι)) = closure (range (flow τ)))
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (u : C(UnitAddTorus ι, ℂ)) :
    Tendsto (fun T : ℝ ↦ (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, u (flow τ t)) atTop
      (𝓝 (∫ g : G, u (g : UnitAddTorus ι) ∂μ)) := by
  classical
  have hGc : IsClosed (G : Set (UnitAddTorus ι)) := hG ▸ isClosed_closure
  have : CompactSpace G := isCompact_iff_compactSpace.mp hGc.isCompact
  let A : ℝ → C(UnitAddTorus ι, ℂ) → ℂ :=
    fun T φ ↦ (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, φ (flow τ t)
  let I : C(UnitAddTorus ι, ℂ) → ℂ := fun φ ↦ ∫ g : G, φ (g : UnitAddTorus ι) ∂μ
  have hII (φ : C(UnitAddTorus ι, ℂ)) (T : ℝ) :
      IntervalIntegrable (fun t ↦ φ (flow τ t)) volume 0 T :=
    (φ.continuous.comp (continuous_flow τ)).intervalIntegrable _ _
  have hInt (φ : C(UnitAddTorus ι, ℂ)) : Integrable (fun g : G ↦ φ (g : UnitAddTorus ι)) μ :=
    (φ.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  -- Averages of the monomials converge to their integrals.
  have hF (n : ι → ℤ) : Tendsto (fun T ↦ A T (mFourier n)) atTop (𝓝 (I (mFourier n))) := by
    simp only [I]
    rw [integral_mFourier_closure τ G hG μ n]
    split_ifs with hc
    · refine tendsto_const_nhds.congr' ((eventually_ne_atTop 0).mono fun T hT ↦ ?_)
      simp [A, mFourier_flow, hc, hT]
    · simp only [A, mFourier_flow]
      exact tendsto_average_exp hc
  -- Linearity of the averages.
  have hAsub (T : ℝ) (φ ψ : C(UnitAddTorus ι, ℂ)) : A T φ - A T ψ = A T (φ - ψ) := by
    simp only [A, ContinuousMap.sub_apply, intervalIntegral.integral_sub (hII φ T) (hII ψ T),
      mul_sub]
  have hAadd (T : ℝ) (φ ψ : C(UnitAddTorus ι, ℂ)) : A T (φ + ψ) = A T φ + A T ψ := by
    simp only [A, ContinuousMap.add_apply, intervalIntegral.integral_add (hII φ T) (hII ψ T),
      mul_add]
  have hAsmul (T : ℝ) (a : ℂ) (φ : C(UnitAddTorus ι, ℂ)) : A T (a • φ) = a * A T φ := by
    simp only [A, ContinuousMap.smul_apply, smul_eq_mul, intervalIntegral.integral_const_mul]
    ring
  -- The averages are uniformly 1-Lipschitz.
  have hAnorm (T : ℝ) (φ : C(UnitAddTorus ι, ℂ)) : ‖A T φ‖ ≤ ‖φ‖ := by
    rcases eq_or_ne T 0 with rfl | hT
    · simp [A]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    calc |T|⁻¹ * ‖∫ t in (0 : ℝ)..T, φ (flow τ t)‖ ≤ |T|⁻¹ * (‖φ‖ * |T - 0|) := by
          gcongr
          exact intervalIntegral.norm_integral_le_of_norm_le_const fun t _ ↦ φ.norm_coe_le_norm _
      _ = ‖φ‖ := by rw [sub_zero]; field_simp [abs_ne_zero.mpr hT]
  have hLip (T : ℝ) : LipschitzWith 1 (A T) := LipschitzWith.of_dist_le_mul fun φ ψ ↦ by
    rw [dist_eq_norm, dist_eq_norm, hAsub, NNReal.coe_one, one_mul]
    exact hAnorm T _
  have hIcont : Continuous I := by
    refine (LipschitzWith.of_dist_le_mul fun φ ψ ↦ ?_ : LipschitzWith 1 _).continuous
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    simp only [I]
    rw [← integral_sub (hInt φ) (hInt ψ)]
    calc ‖∫ g : G, (φ (g : UnitAddTorus ι) - ψ (g : UnitAddTorus ι)) ∂μ‖
          ≤ ‖φ - ψ‖ * (μ (univ : Set G)).toReal :=
          norm_integral_le_of_norm_le_const (Eventually.of_forall fun x ↦
            (φ - ψ).norm_coe_le_norm (x : UnitAddTorus ι))
      _ = ‖φ - ψ‖ := by simp
  let V : Set C(UnitAddTorus ι, ℂ) :=
    {φ | Tendsto (fun T ↦ A T φ) atTop (𝓝 (I φ))}
  have hVclosed : IsClosed V :=
    ((LipschitzWith.uniformEquicontinuous A 1 hLip).equicontinuous).isClosed_setOfPred_tendsto
      hIcont
  have hspan : ((Submodule.span ℂ (range (mFourier (d := ι))) :
      Set C(UnitAddTorus ι, ℂ))) ⊆ V := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => obtain ⟨n, rfl⟩ := hx; exact hF n
    | zero => simp [V, A, I]
    | add φ ψ _ _ hφ hψ =>
      change Tendsto _ _ _
      simp only [hAadd, I, ContinuousMap.add_apply, integral_add (hInt φ) (hInt ψ)]
      exact hφ.add hψ
    | smul a φ _ hφ =>
      change Tendsto _ _ _
      simp only [hAsmul, I, ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul]
      exact hφ.const_mul a
  have hall (φ : C(UnitAddTorus ι, ℂ)) : φ ∈ V := by
    have hmem : φ ∈ (Submodule.span ℂ (range (mFourier (d := ι)))).topologicalClosure := by
      rw [span_mFourier_closure_eq_top]; trivial
    exact closure_minimal hspan hVclosed hmem
  exact hall u

end

end Sol_KroneckerWeyl_tendsto_average_torusFlow_closure

open Sol_KroneckerWeyl_tendsto_average_torusFlow_closure in
theorem solution {ι : Type*} [Finite ι] (τ : ι → ℝ)
    (G : AddSubgroup (UnitAddTorus ι))
    (hG : (G : Set (UnitAddTorus ι)) =
      closure (Set.range fun t : ℝ => fun k : ι => ((t * τ k : ℝ) : UnitAddCircle)))
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (u : C(UnitAddTorus ι, ℂ)) :
    Tendsto (fun T : ℝ => T⁻¹ • ∫ t in (0 : ℝ)..T, u fun k => ((t * τ k : ℝ) : UnitAddCircle))
        atTop (𝓝 (∫ g : G, u (g : UnitAddTorus ι) ∂μ)) ∧
      Tendsto
        (fun T : ℝ => (2 * T)⁻¹ • ∫ t in (-T)..T, u fun k => ((t * τ k : ℝ) : UnitAddCircle))
        atTop (𝓝 (∫ g : G, u (g : UnitAddTorus ι) ∂μ)) := by
  have := Fintype.ofFinite ι
  have hG' : (G : Set (UnitAddTorus ι)) = closure (Set.range (flow τ)) := hG
  have hGneg : (G : Set (UnitAddTorus ι)) = closure (Set.range (flow (-τ))) := by
    rw [range_flow_neg]; exact hG'
  have hF := tendsto_forward_average τ G hG' μ u
  have hB := tendsto_forward_average (-τ) G hGneg μ u
  have hflow (t : ℝ) : (fun k => ((t * τ k : ℝ) : UnitAddCircle)) = flow τ t := rfl
  have hneg (t : ℝ) : flow τ (-t) = flow (-τ) t := by
    funext k
    simp only [flow, Pi.neg_apply]
    congr 1
    ring
  have hII (a b : ℝ) : IntervalIntegrable (fun t ↦ u (flow τ t)) volume a b :=
    (u.continuous.comp (continuous_flow τ)).intervalIntegrable _ _
  refine ⟨?_, ?_⟩
  · simp only [hflow, Complex.real_smul, Complex.ofReal_inv]
    exact hF
  · have heq (T : ℝ) : (2 * T)⁻¹ • ∫ t in (-T)..T, u (flow τ t) =
        (1 / 2 : ℂ) * (((T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, u (flow (-τ) t)) +
          ((T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, u (flow τ t))) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hII (-T) 0) (hII 0 T)]
      have h1 : ∫ t in (-T)..0, u (flow τ t) = ∫ t in (0 : ℝ)..T, u (flow (-τ) t) := by
        rw [← neg_zero, ← intervalIntegral.integral_comp_neg]
        simp only [neg_zero, hneg]
      rw [h1, Complex.real_smul]
      push_cast
      ring
    simp only [hflow, heq]
    have := (hB.add hF).const_mul (1 / 2 : ℂ)
    convert this using 2
    ring
