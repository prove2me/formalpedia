-- Prove2me | solution 1 for KroneckerWeyl.closure_range_torusFlow
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:39:28.007192+00:00
-- url     : https://prove2.me/submissions/570c6528-084a-42bd-b9dc-9cbf7637ac26

import Mathlib

set_option autoImplicit false

open Filter Function MeasureTheory Set
open scoped Topology

namespace Sol_KroneckerWeyl_closure_range_torusFlow

open Real UnitAddTorus

/-- The linear flow on the torus. -/
noncomputable def flow {d : Type*} (β : d → ℝ) (t : ℝ) : UnitAddTorus d :=
  fun k => ((t * β k : ℝ) : UnitAddCircle)

theorem continuous_flow {d : Type*} (β : d → ℝ) : Continuous (flow β) :=
  continuous_pi fun _ => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_id.mul continuous_const)

theorem mFourier_add_apply {d : Type*} [Fintype d] (n : d → ℤ) (x y : UnitAddTorus d) :
    mFourier n (x + y) = mFourier n x * mFourier n y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, smul_add,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

theorem mFourier_flow {d : Type*} [Fintype d] (β : d → ℝ) (n : d → ℤ) (t : ℝ) :
    mFourier n (flow β t) =
      Complex.exp (2 * π * Complex.I * ((∑ i, (n i : ℝ) * β i : ℝ) : ℂ) * t) := by
  have h (i : d) : (flow β t) i = ((t * β i : ℝ) : AddCircle (1 : ℝ)) := rfl
  simp only [mFourier, ContinuousMap.coe_mk, h, fourier_coe_apply, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

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

/-- Kronecker: rationally independent frequencies give a dense line in the torus. -/
theorem denseRange_flow {d : Type*} [Fintype d] {τ : d → ℝ}
    (hτ : LinearIndependent ℚ τ) : DenseRange (flow τ) := by
  classical
  have : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨UnitAddCircle.measure_univ⟩
  let A : ℝ → C(UnitAddTorus d, ℂ) → ℂ :=
    fun T φ ↦ (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, φ (flow τ t)
  have hII (φ : C(UnitAddTorus d, ℂ)) (T : ℝ) :
      IntervalIntegrable (fun t ↦ φ (flow τ t)) volume 0 T :=
    (φ.continuous.comp (continuous_flow τ)).intervalIntegrable _ _
  have hInt (φ : C(UnitAddTorus d, ℂ)) : Integrable φ :=
    integrableOn_univ.mp (φ.continuous.continuousOn.integrableOn_compact isCompact_univ)
  have hc (n : d → ℤ) (hn : n ≠ 0) : (∑ i, (n i : ℝ) * τ i) ≠ 0 := by
    intro h
    apply hn
    have h0 := Fintype.linearIndependent_iff.mp hτ (fun i ↦ (n i : ℚ)) (by
      simpa [Rat.smul_def] using h)
    funext i
    exact_mod_cast h0 i
  have hint (n : d → ℤ) : ∫ x, mFourier n x = if n = 0 then 1 else 0 := by
    split_ifs with hn
    · subst hn; simp [mFourier_zero]
    · set c := ∑ i, (n i : ℝ) * τ i
      have hw : mFourier n (flow τ (1 / (2 * c))) = -1 := by
        rw [mFourier_flow, show 2 * (π : ℂ) * Complex.I * (c : ℂ) * ((1 / (2 * c) : ℝ) : ℂ) =
          π * Complex.I by
          push_cast; field_simp [hc n hn]; exact div_self (Complex.ofReal_ne_zero.mpr (hc n hn))]
        exact Complex.exp_pi_mul_I
      have h1 := integral_add_right_eq_self (μ := volume) (fun x ↦ mFourier n x)
        (flow τ (1 / (2 * c)))
      simp only [mFourier_add_apply, hw, integral_mul_const] at h1
      linear_combination (-1 / 2 : ℂ) * h1
  have hF (n : d → ℤ) : Tendsto (fun T ↦ A T (mFourier n)) atTop (𝓝 (∫ x, mFourier n x)) := by
    rw [hint]
    split_ifs with hn
    · subst hn
      refine tendsto_const_nhds.congr' ((eventually_ne_atTop 0).mono fun T hT ↦ ?_)
      simp [A, mFourier_zero, hT]
    · simp only [A, mFourier_flow]
      exact tendsto_average_exp (hc n hn)
  have hAsub (T : ℝ) (φ ψ : C(UnitAddTorus d, ℂ)) : A T φ - A T ψ = A T (φ - ψ) := by
    simp only [A, ContinuousMap.sub_apply, intervalIntegral.integral_sub (hII φ T) (hII ψ T),
      mul_sub]
  have hAadd (T : ℝ) (φ ψ : C(UnitAddTorus d, ℂ)) : A T (φ + ψ) = A T φ + A T ψ := by
    simp only [A, ContinuousMap.add_apply, intervalIntegral.integral_add (hII φ T) (hII ψ T),
      mul_add]
  have hAsmul (T : ℝ) (a : ℂ) (φ : C(UnitAddTorus d, ℂ)) : A T (a • φ) = a * A T φ := by
    simp only [A, ContinuousMap.smul_apply, smul_eq_mul, intervalIntegral.integral_const_mul]
    ring
  have hAnorm (T : ℝ) (φ : C(UnitAddTorus d, ℂ)) : ‖A T φ‖ ≤ ‖φ‖ := by
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
  have hIcont : Continuous fun φ : C(UnitAddTorus d, ℂ) ↦ ∫ x, φ x := by
    refine (LipschitzWith.of_dist_le_mul fun φ ψ ↦ ?_ : LipschitzWith 1 _).continuous
    rw [dist_eq_norm, dist_eq_norm, ← integral_sub (hInt φ) (hInt ψ), NNReal.coe_one, one_mul]
    calc ‖∫ x, (φ x - ψ x)‖ ≤ ‖φ - ψ‖ * volume.real (univ : Set (UnitAddTorus d)) :=
          norm_integral_le_of_norm_le_const (Eventually.of_forall fun x ↦
            (φ - ψ).norm_coe_le_norm x)
      _ = ‖φ - ψ‖ := by simp
  let V : Set C(UnitAddTorus d, ℂ) :=
    {φ | Tendsto (fun T ↦ A T φ) atTop (𝓝 (∫ x, φ x))}
  have hVclosed : IsClosed V :=
    ((LipschitzWith.uniformEquicontinuous A 1 hLip).equicontinuous).isClosed_setOfPred_tendsto
      hIcont
  have hspan : ((Submodule.span ℂ (range (mFourier (d := d))) :
      Set C(UnitAddTorus d, ℂ))) ⊆ V := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => obtain ⟨n, rfl⟩ := hx; exact hF n
    | zero => simp [V, A]
    | add φ ψ _ _ hφ hψ =>
      change Tendsto _ _ _
      simp only [hAadd, ContinuousMap.add_apply, integral_add (hInt φ) (hInt ψ)]
      exact hφ.add hψ
    | smul a φ _ hφ =>
      change Tendsto _ _ _
      simp only [hAsmul, ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul]
      exact hφ.const_mul a
  have hall (φ : C(UnitAddTorus d, ℂ)) : φ ∈ V := by
    have hmem : φ ∈ (Submodule.span ℂ (range (mFourier (d := d)))).topologicalClosure := by
      rw [span_mFourier_closure_eq_top]; trivial
    exact closure_minimal hspan hVclosed hmem
  by_contra hd
  obtain ⟨p, hp⟩ : ∃ p, p ∉ closure (range (flow τ)) :=
    not_forall.mp fun h ↦ hd (dense_iff_closure_eq.mpr (eq_univ_of_forall h))
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed isClosed_closure
    isClosed_singleton (disjoint_singleton_right.mpr hp)
  let φ : C(UnitAddTorus d, ℂ) := ⟨fun x ↦ (f x : ℂ), by fun_prop⟩
  have hA (T : ℝ) : A T φ = 0 := by
    have : ∀ t, φ (flow τ t) = 0 := fun t ↦ by
      change ((f (flow τ t) : ℝ) : ℂ) = 0
      rw [hf0 (subset_closure (mem_range_self t))]
      simp
    simp [A, this]
  have hzero : ∫ x, φ x = 0 :=
    tendsto_nhds_unique (hall φ) (by simp only [hA]; exact tendsto_const_nhds)
  have hpos : 0 < ∫ x, f x :=
    f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace _) (fun x ↦ (hf01 x).1) (x := p)
      (by rw [hf1 rfl]; norm_num)
  have : ∫ x, φ x = ((∫ x, f x : ℝ) : ℂ) := integral_ofReal
  rw [this] at hzero
  exact hpos.ne' (Complex.ofReal_eq_zero.mp hzero)


theorem coe_zsmul_eq (n : ℤ) (x : ℝ) :
    n • (x : UnitAddCircle) = (((n : ℝ) * x : ℝ) : UnitAddCircle) := by
  rw [← zsmul_eq_mul]
  exact (QuotientAddGroup.mk_zsmul _ x n).symm

theorem coe_sum_eq {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ s, (f i : UnitAddCircle) = ((∑ i ∈ s, f i : ℝ) : UnitAddCircle) :=
  (map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) f s).symm

theorem isClosed_relations {ι : Type*} [Fintype ι] (τ : ι → ℝ) :
    IsClosed {ξ : UnitAddTorus ι | ∀ a : ι → ℤ, ∑ k, (a k : ℝ) * τ k = 0 →
      ∑ k, a k • ξ k = 0} := by
  rw [Set.ofPred_forall]
  refine isClosed_iInter fun a => ?_
  refine isClosed_imp isOpen_const ?_
  exact isClosed_eq (continuous_finsetSum _ fun k _ => (continuous_apply k).zsmul (a k))
    continuous_const

end Sol_KroneckerWeyl_closure_range_torusFlow

open Sol_KroneckerWeyl_closure_range_torusFlow in
theorem solution {ι : Type*} [Fintype ι] (τ : ι → ℝ) :
    closure (Set.range fun t : ℝ => fun k : ι => ((t * τ k : ℝ) : UnitAddCircle)) =
      {ξ : UnitAddTorus ι | ∀ a : ι → ℤ, ∑ k, (a k : ℝ) * τ k = 0 → ∑ k, a k • ξ k = 0} := by
  classical
  change closure (Set.range (flow τ)) = _
  refine Set.Subset.antisymm (closure_minimal ?_ (isClosed_relations τ)) ?_
  · rintro _ ⟨t, rfl⟩ a ha
    change ∑ k, a k • ((t * τ k : ℝ) : UnitAddCircle) = 0
    simp_rw [coe_zsmul_eq]
    rw [coe_sum_eq]
    have : ∑ k, (a k : ℝ) * (t * τ k) = t * ∑ k, (a k : ℝ) * τ k := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, ha, mul_zero, AddCircle.coe_zero]
  · intro ξ hξ
    -- An integer basis `β` of the group generated by the frequencies.
    let M : Submodule ℤ ℝ := Submodule.span ℤ (Set.range τ)
    have : Module.Finite ℤ M := Module.Finite.span_of_finite ℤ (Set.finite_range τ)
    let b : Module.Basis (Fin (Module.finrank ℤ M)) ℤ M := Module.finBasis ℤ M
    let β : Fin (Module.finrank ℤ M) → ℝ := fun j ↦ (b j : ℝ)
    have hτM (i : ι) : τ i ∈ M := Submodule.subset_span ⟨i, rfl⟩
    let A : ι → Fin (Module.finrank ℤ M) → ℤ := fun i j ↦ b.repr ⟨τ i, hτM i⟩ j
    have hτ (i : ι) : τ i = ∑ j, A i j • β j := by
      have h := congrArg Subtype.val (b.sum_repr ⟨τ i, hτM i⟩)
      rw [Submodule.coe_sum] at h
      simp_rw [Submodule.coe_smul] at h
      exact h.symm
    have hβZ : LinearIndependent ℤ β := b.linearIndependent.map' M.subtype M.ker_subtype
    have hβQ : LinearIndependent ℚ β := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hβZ
    choose C hC using fun j ↦ (Submodule.mem_span_range_iff_exists_fun ℤ).mp (b j).2
    -- the integer maps between the two tori
    let φ : UnitAddTorus (Fin (Module.finrank ℤ M)) → UnitAddTorus ι :=
      fun y i => ∑ j, A i j • y j
    have hφc : Continuous φ :=
      continuous_pi fun i => continuous_finsetSum _ fun j _ => (continuous_apply j).zsmul _
    let y : UnitAddTorus (Fin (Module.finrank ℤ M)) := fun j => ∑ i, C j i • ξ i
    have hφy : φ y = ξ := by
      funext i
      let n : ι → ℤ := fun k => (if k = i then 1 else 0) - ∑ j, A i j * C j k
      have hn : ∑ k, (n k : ℝ) * τ k = 0 := by
        have h1 : ∑ k, (n k : ℝ) * τ k =
            τ i - ∑ j, (A i j : ℝ) * ∑ k, (C j k : ℝ) * τ k := by
          simp only [n, Int.cast_sub, Int.cast_sum, Int.cast_mul, sub_mul, Finset.sum_sub_distrib,
            Finset.sum_mul, Finset.mul_sum]
          congr 1
          · simp
          · rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
              push_cast; ring
        have h2 (j : Fin (Module.finrank ℤ M)) : ∑ k, (C j k : ℝ) * τ k = β j := by
          have := hC j
          simpa [zsmul_eq_mul] using this
        rw [h1]
        simp_rw [h2]
        rw [hτ i]
        simp [zsmul_eq_mul]
      have h := hξ n hn
      simp only [n, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_smul] at h
      change ∑ j, A i j • ∑ k, C j k • ξ k = ξ i
      rw [sub_eq_zero] at h
      rw [h, Finset.sum_comm]
      simp_rw [Finset.smul_sum, smul_smul]
    have hflow (t : ℝ) : φ (flow β t) = flow τ t := by
      funext i
      change ∑ j, A i j • ((t * β j : ℝ) : UnitAddCircle) = ((t * τ i : ℝ) : UnitAddCircle)
      simp_rw [coe_zsmul_eq]
      rw [coe_sum_eq, hτ i, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [zsmul_eq_mul]; ring
    rw [← hφy]
    refine map_mem_closure hφc (denseRange_flow hβQ y) ?_
    rintro _ ⟨t, rfl⟩
    exact ⟨t, (hflow t).symm⟩
