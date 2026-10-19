-- Prove2me | solution 1 for HunterPDE.Parabolic.weak_solution_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T10:52:17.23904+00:00
-- url     : https://prove2.me/submissions/c4ea874b-577d-4976-b75b-429d0fe21210

import Mathlib
import Definitions.Def_HunterPDE_Parabolic_H10
import Definitions.Def_HunterPDE_Parabolic_WeakTimeDeriv
import Definitions.Def_HunterPDE_Parabolic_WeakSolution
import Definitions.Def_HunterPDE_Parabolic_HilbertTriple
import Theorems.Thm_HunterPDE_Parabolic_galerkin_exists_unique
import Theorems.Thm_HunterPDE_Parabolic_galerkin_limit
import Theorems.Thm_AsymptoticOperator_exists_hilbertBasis_eigenvectors_of_isCompactOperator
import Theorems.Thm_HunterPDE_Parabolic_h10_l2_dense_embeddings
import Theorems.Thm_HunterPDE_Parabolic_rellich_h10_l2_compact
import Theorems.Thm_HunterPDE_Parabolic_weak_solution_unique

/-! Reduction of `HunterPDE.Parabolic.weak_solution_exists_unique` (Hunter, Thm 6.3) to
`galerkin_exists_unique` (Galerkin approximations, (6.15)-(6.16)), `galerkin_limit` (Prop. 6.7),
`h10_l2_dense_embeddings` (the Hilbert triple `H¹₀ ⊂ L² ⊂ H⁻¹`), `rellich_h10_l2_compact`
(Rellich: `H¹₀(Ω) ↪ L²(Ω)` is compact), `weak_solution_unique` (uniqueness of weak solutions) and the
spectral theorem `AsymptoticOperator.exists_hilbertBasis_eigenvectors_of_isCompactOperator`.
Proved here: the degenerate cases `n = 0 ∨ Ω = ∅` and the Dirichlet eigenbasis. -/

set_option linter.all false

section Q4517_I
/-! Shortcut instances for `H¹₀(Ω)` and `H⁻¹(Ω)`: each one is exactly the instance that type-class
search finds anyway (`inferInstance`), declared once with high priority so that later searches stop at
it instead of re-deriving it through the submodule / continuous-linear-map hierarchy every time.
They are `scoped` (opened in each block below, not at the final `theorem solution`), so the
statement of `solution` is elaborated with the standard instances, exactly like the target's. -/
open MeasureTheory
namespace HunterPDE.Parabolic.Q4517Fast
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
noncomputable scoped instance (priority := high) q4517EMS : MeasureSpace (EuclideanSpace ℝ (Fin n)) := inferInstance
noncomputable scoped instance (priority := high) q4517H10NACG : NormedAddCommGroup (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q4517H10SACG : SeminormedAddCommGroup (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q4517H10IPS : InnerProductSpace ℝ (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q4517H10NS : NormedSpace ℝ (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q4517H10Mod : Module ℝ (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q4517Hm1NACG : NormedAddCommGroup (Hm1 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q4517Hm1SACG : SeminormedAddCommGroup (Hm1 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q4517Hm1NS : NormedSpace ℝ (Hm1 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q4517Hm1Mod : Module ℝ (Hm1 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q4517Hm1CS : CompleteSpace (Hm1 n Ω) := inferInstance
end HunterPDE.Parabolic.Q4517Fast
end Q4517_I


section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q4517Fast

abbrev E0 : Type := EuclideanSpace ℝ (Fin 0)

instance e0_subsingleton : Subsingleton E0 := ⟨fun a b => by ext i; exact i.elim0⟩

lemma vol_e0 : (volume : Measure E0) = Measure.dirac 0 := volume_euclideanSpace_eq_dirac (Fin 0)

lemma vol_e0_univ : (volume : Measure E0) univ = 1 := by
  rw [vol_e0]; simp

instance : IsFiniteMeasure (volume.restrict (univ : Set E0)) := by
  rw [Measure.restrict_univ]; exact ⟨by rw [vol_e0_univ]; simp⟩

lemma mu_univ : (volume.restrict (univ : Set E0)) univ = 1 := by
  rw [Measure.restrict_univ, vol_e0_univ]

/-- (T1) a.e. statements hold at every point. -/
lemma ae_point {P : E0 → Prop} (h : ∀ᵐ x ∂(volume.restrict (univ : Set E0)), P x) (x : E0) : P x := by
  by_contra hx
  have hs : {y | ¬ P y} = univ := by
    ext y; simp only [mem_setOf_eq, mem_univ, iff_true]
    rwa [Subsingleton.elim y x]
  have := ae_iff.mp h
  rw [hs, mu_univ] at this
  exact one_ne_zero this

/-- (T2) Lp elements are determined by their value at one point. -/
lemma lp_ext0 {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞}
    (a b : Lp F p (volume.restrict (univ : Set E0))) (h : (a : E0 → F) 0 = (b : E0 → F) 0) :
    a = b := by
  apply Lp.ext
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Subsingleton.elim x 0]; exact h

/-- (T3) integrals are point evaluations. -/
lemma int_pt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (f : E0 → F) :
    ∫ x, f x ∂(volume.restrict (univ : Set E0)) = f 0 := by
  have : f = fun _ => f 0 := funext fun x => by rw [Subsingleton.elim x 0]
  rw [this, integral_const]
  simp [Measure.real, vol_e0_univ]

/-- The unit jet `(1, 0)`. -/
noncomputable def j1 : Jet 0 := WithLp.toLp 2 ((1 : ℝ), (0 : E0))

/-- The constant jet function. -/
noncomputable def e1 : JetL2 0 (univ : Set E0) := Lp.const 2 (volume.restrict univ) j1

lemma e1_mem : e1 ∈ H10 0 (univ : Set E0) := by
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  refine ⟨fun _ => 1, contDiff_const, ?_, subset_univ _, ?_⟩
  · exact (Set.toFinite _).isCompact
  · have := Lp.coeFn_const (p := 2) (μ := volume.restrict (univ : Set E0)) j1
    simp only [e1]
    filter_upwards [this] with x hx
    rw [hx]
    simp [j1, Subsingleton.elim (gradient (fun _ : E0 => (1:ℝ)) x) 0]

noncomputable def E1 : H10 0 (univ : Set E0) := ⟨e1, e1_mem⟩

lemma val_E1 (x : E0) : val E1 x = 1 := by
  have := Lp.coeFn_const (p := 2) (μ := volume.restrict (univ : Set E0)) j1
  have h := ae_point this x
  simp only [val, E1, e1]
  rw [h]; simp [j1]

lemma val_smul (a : ℝ) (v : H10 0 (univ : Set E0)) (x : E0) : val (a • v) x = a * val v x := by
  have := Lp.coeFn_smul (E := Jet 0) (p := 2) (μ := volume.restrict (univ : Set E0)) a
    (v : JetL2 0 univ)
  have h := ae_point this x
  simp only [val]
  rw [Submodule.coe_smul, h]
  simp

/-- Every element of `H10 0 univ` is a multiple of `E1`. -/
lemma h10_eq (v : H10 0 (univ : Set E0)) : v = val v 0 • E1 := by
  apply Subtype.ext
  apply lp_ext0
  have := Lp.coeFn_smul (E := Jet 0) (p := 2) (μ := volume.restrict (univ : Set E0)) (val v 0)
    (E1 : JetL2 0 univ)
  rw [Submodule.coe_smul, ae_point this 0]
  have hE := ae_point (Lp.coeFn_const (p := 2) (μ := volume.restrict (univ : Set E0)) j1) 0
  simp only [Pi.smul_apply, E1, e1]
  rw [hE]
  apply WithLp.ofLp_injective
  refine Prod.ext ?_ (Subsingleton.elim _ _)
  simp [j1, val]



lemma exp_lip_Icc (M : ℝ) :
    LipschitzOnWith (Real.exp M).toNNReal Real.exp (Icc (-M) M) := by
  refine (convex_Icc _ _).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) ?_
  intro x hx
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x),
    Real.coe_toNNReal _ (Real.exp_pos M).le]
  exact Real.exp_le_exp.mpr hx.2

lemma prim_lip {T K : ℝ} {c : ℝ → ℝ} (hc : IntervalIntegrable c volume 0 T)
    (hcb : ∀ t, |c t| ≤ K) :
    ∀ s ∈ uIcc 0 T, ∀ t ∈ uIcc 0 T,
      |(∫ r in (0:ℝ)..t, c r) - ∫ r in (0:ℝ)..s, c r| ≤ K * |t - s| := by
  intro s hs t ht
  rw [intervalIntegral.integral_interval_sub_left (hc.mono_set (uIcc_subset_uIcc_left ht))
    (hc.mono_set (uIcc_subset_uIcc_left hs))]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t) (f := c)
    (C := K) (fun x _ => by rw [Real.norm_eq_abs]; exact hcb x)
  simpa [Real.norm_eq_abs] using this

/-- Scalar linear ODE `y' + c y = F`, `y 0 = g0`, by the integrating factor. -/
lemma scalar_ode {T K g0 : ℝ} (hT : 0 < T) (hK : 0 ≤ K) {c F : ℝ → ℝ}
    (hc : IntervalIntegrable c volume 0 T) (hcb : ∀ t, |c t| ≤ K)
    (hF : IntervalIntegrable F volume 0 T) :
    ∃ y : ℝ → ℝ, ContinuousOn y (Icc 0 T) ∧ y 0 = g0 ∧ AbsolutelyContinuousOnInterval y 0 T ∧
      (∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt y (F t - c t * y t) t) ∧
      ∀ t ∈ Icc 0 T, |y t| ≤ Real.exp (2 * K * T) * (|g0| + ∫ s in (0:ℝ)..T, |F s|) := by
  set C : ℝ → ℝ := fun t => ∫ r in (0:ℝ)..t, c r with hCdef
  have hu : uIcc (0:ℝ) T = Icc 0 T := uIcc_of_le hT.le
  have hcI : IntegrableOn c (uIcc 0 T) := by
    rw [hu]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mp hc
  have hCc : ContinuousOn C (uIcc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) hcI
    simpa [hCdef] using this
  have hCb : ∀ t ∈ uIcc 0 T, |C t| ≤ K * T := by
    intro t ht
    have h := prim_lip hc hcb 0 (by simp [hu, hT.le]) t ht
    rw [hu] at ht
    simp only [intervalIntegral.integral_same, sub_zero] at h
    calc |C t| ≤ K * |t| := h
      _ ≤ K * T := by rw [abs_of_nonneg ht.1]; exact mul_le_mul_of_nonneg_left ht.2 hK
  have hEi : IntervalIntegrable (fun s => Real.exp (C s) * F s) volume 0 T :=
    hF.continuousOn_mul (Real.continuous_exp.comp_continuousOn hCc)
  set Z : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, Real.exp (C s) * F s with hZdef
  refine ⟨fun t => Real.exp (-C t) * (g0 + Z t), ?_, ?_, ?_, ?_, ?_⟩
  · have hEI : IntegrableOn (fun s => Real.exp (C s) * F s) (uIcc 0 T) := by
      rw [hu]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mp hEi
    have hZc : ContinuousOn Z (uIcc 0 T) := by
      have := intervalIntegral.continuousOn_primitive_interval (μ := volume) hEI
      simpa [hZdef] using this
    rw [← hu]
    exact (Real.continuous_exp.comp_continuousOn hCc.neg).mul (continuousOn_const.add hZc)
  · simp [hCdef, hZdef]
  · have hL : LipschitzOnWith ((Real.exp (K * T)).toNNReal * K.toNNReal)
        (fun t => Real.exp (-C t)) (uIcc 0 T) := by
      have h1 : LipschitzOnWith K.toNNReal (fun t => -C t) (uIcc 0 T) := by
        refine LipschitzOnWith.of_dist_le_mul fun s hs t ht => ?_
        rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK]
        have := prim_lip hc hcb t ht s hs
        calc |-C s - -C t| = |C s - C t| := by
              rw [show -C s - -C t = -(C s - C t) by ring, abs_neg]
          _ ≤ K * |s - t| := this
      have h2 := (exp_lip_Icc (K * T)).comp h1 (fun t ht => by
        have := hCb t ht
        rw [abs_le] at this
        exact ⟨by linarith, by linarith⟩)
      exact h2
    have hZac : AbsolutelyContinuousOnInterval Z 0 T :=
      hEi.absolutelyContinuousOnInterval_intervalIntegral (by simp [hu, hT.le])
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => g0) 0 T :=
      ((LipschitzWith.const (α := ℝ) g0).lipschitzOnWith (s := uIcc (0:ℝ) T)).absolutelyContinuousOnInterval
    exact hL.absolutelyContinuousOnInterval.fun_mul (hconst.add hZac)
  · have h1 := hc.ae_hasDerivAt_integral
    have h2 := hEi.ae_hasDerivAt_integral
    filter_upwards [h1, h2] with t ht1 ht2 ht
    have htI : t ∈ uIcc 0 T := by rw [hu]; exact Ioo_subset_Icc_self ht
    have h0 : (0:ℝ) ∈ uIcc 0 T := by simp [hu, hT.le]
    have dC : HasDerivAt C (c t) t := ht1 htI 0 h0
    have dZ : HasDerivAt Z (Real.exp (C t) * F t) t := ht2 htI 0 h0
    have dE : HasDerivAt (fun x => Real.exp (-C x)) (Real.exp (-C t) * (-c t)) t := dC.neg.exp
    have dP : HasDerivAt (fun x => Real.exp (-C x) * (g0 + Z x))
        (Real.exp (-C t) * (-c t) * (g0 + Z t) + Real.exp (-C t) * (Real.exp (C t) * F t)) t :=
      dE.mul (dZ.const_add g0)
    refine dP.congr_deriv ?_
    have e : Real.exp (-C t) * Real.exp (C t) = 1 := by
      rw [← Real.exp_add]; simp
    have e' : Real.exp (-C t) * (Real.exp (C t) * F t) = F t := by rw [← mul_assoc, e, one_mul]
    rw [e']
    ring
  · intro t ht
    have htu : t ∈ uIcc 0 T := by rw [hu]; exact ht
    have hC := hCb t htu
    have hE1 : Real.exp (-C t) ≤ Real.exp (K * T) := Real.exp_le_exp.mpr (by
      rw [abs_le] at hC; linarith)
    have hZb : |Z t| ≤ Real.exp (K * T) * ∫ s in (0:ℝ)..T, |F s| := by
      have hmono : ∫ s in (0:ℝ)..t, |F s| ≤ ∫ s in (0:ℝ)..T, |F s| := by
        apply intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        · exact Filter.Eventually.of_forall fun _ => abs_nonneg _
        · exact hF.abs
      calc |Z t| ≤ ∫ s in (0:ℝ)..t, |Real.exp (C s) * F s| :=
            intervalIntegral.abs_integral_le_integral_abs ht.1
        _ ≤ ∫ s in (0:ℝ)..t, Real.exp (K * T) * |F s| := by
            apply intervalIntegral.integral_mono_on ht.1
            · exact (hEi.mono_set (uIcc_subset_uIcc_left htu)).abs
            · exact ((hF.mono_set (uIcc_subset_uIcc_left htu)).abs).const_mul _
            · intro s hs
              have hsu : s ∈ uIcc 0 T := by
                rw [hu]; exact ⟨hs.1, hs.2.trans ht.2⟩
              have := hCb s hsu
              rw [abs_mul, abs_of_pos (Real.exp_pos _)]
              apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
              exact Real.exp_le_exp.mpr ((le_abs_self _).trans this)
        _ = Real.exp (K * T) * ∫ s in (0:ℝ)..t, |F s| := intervalIntegral.integral_const_mul _ _
        _ ≤ Real.exp (K * T) * ∫ s in (0:ℝ)..T, |F s| :=
            mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le
    have hIF : 0 ≤ ∫ s in (0:ℝ)..T, |F s| :=
      intervalIntegral.integral_nonneg hT.le fun _ _ => abs_nonneg _
    have hKT : 0 ≤ K * T := mul_nonneg hK hT.le
    have e2 : Real.exp (2 * K * T) = Real.exp (K * T) * Real.exp (K * T) := by
      rw [← Real.exp_add]; ring_nf
    have hone : 1 ≤ Real.exp (K * T) := Real.one_le_exp hKT
    calc |Real.exp (-C t) * (g0 + Z t)| = Real.exp (-C t) * |g0 + Z t| := by
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (K * T) * (|g0| + Real.exp (K * T) * ∫ s in (0:ℝ)..T, |F s|) := by
          apply mul_le_mul hE1 ((abs_add_le _ _).trans (by linarith)) (abs_nonneg _)
            (Real.exp_pos _).le
      _ ≤ Real.exp (2 * K * T) * (|g0| + ∫ s in (0:ℝ)..T, |F s|) := by
          rw [e2]
          nlinarith [abs_nonneg g0, mul_nonneg (Real.exp_pos (K*T)).le hIF,
            mul_le_mul_of_nonneg_right hone (abs_nonneg g0)]

/-- Weak derivative of an absolutely continuous function, against a test function on `(0,T)`. -/
lemma weak_deriv_of_ac {T : ℝ} (hT : 0 ≤ T) {y y' : ℝ → ℝ}
    (hac : AbsolutelyContinuousOnInterval y 0 T)
    (hd : ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt y (y' t) t) (φ : ℝ → ℝ)
    (hφ : IsTestFunctionOn T φ) :
    ∫ t in Ioo 0 T, deriv φ t * y t = -∫ t in Ioo 0 T, φ t * y' t := by
  obtain ⟨hφs, -, hφt⟩ := hφ
  have hφac : AbsolutelyContinuousOnInterval φ 0 T :=
    (hφs.contDiffOn.of_le (by simp)).absolutelyContinuousOnInterval
  have key := hac.integral_mul_deriv_eq_deriv_mul hφac
  have h0 : φ 0 = 0 := image_eq_zero_of_notMem_tsupport (fun h => by
    have := hφt h; simp at this)
  have hTT : φ T = 0 := image_eq_zero_of_notMem_tsupport (fun h => by
    have := hφt h; simp at this)
  rw [h0, hTT] at key
  simp only [mul_zero, sub_zero] at key
  rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at key
  have hcongr : ∫ t in Ioo 0 T, deriv y t * φ t = ∫ t in Ioo 0 T, φ t * y' t := by
    refine setIntegral_congr_ae measurableSet_Ioo ?_
    filter_upwards [hd] with t ht htI
    rw [(ht htI).deriv, mul_comm]
  rw [← hcongr]
  simp_rw [mul_comm (deriv φ _) (y _)]
  rw [key]
  ring


/-! ## generic norm helpers (SeminormedAddCommGroup, to dodge Submodule instance paths) -/

lemma el_norm {E : Type*} [SeminormedAddCommGroup E] (f : ℝ → E) (p : ℝ≥0∞) (μ : Measure ℝ) :
    eLpNorm f p μ = eLpNorm (fun t => ‖f t‖) p μ :=
  eLpNorm_congr_enorm_ae (Filter.Eventually.of_forall fun x => by simp [enorm_eq_nnnorm])

lemma el_le {E : Type*} [SeminormedAddCommGroup E] {f : ℝ → E} {g : ℝ → ℝ} {p : ℝ≥0∞}
    {μ : Measure ℝ} (h : ∀ᵐ t ∂μ, ‖f t‖ ≤ g t) : eLpNorm f p μ ≤ eLpNorm g p μ := by
  rw [el_norm]; exact eLpNorm_mono_ae_real (by filter_upwards [h] with t ht; simpa using ht)

lemma el_bound {E : Type*} [SeminormedAddCommGroup E] {f : ℝ → E} {p : ℝ≥0∞} {μ : Measure ℝ}
    {C : ℝ} (h : ∀ᵐ t ∂μ, ‖f t‖ ≤ C) : eLpNorm f p μ ≤ μ univ ^ p.toReal⁻¹ * ENNReal.ofReal C := by
  rw [el_norm]; exact eLpNorm_le_of_ae_bound (by filter_upwards [h] with t ht; simpa using ht)

lemma memLp_bound {E : Type*} [SeminormedAddCommGroup E] {f : ℝ → E} {p : ℝ≥0∞} {μ : Measure ℝ}
    [IsFiniteMeasure μ] (hm : AEStronglyMeasurable f μ) {C : ℝ} (h : ∀ᵐ t ∂μ, ‖f t‖ ≤ C) :
    MemLp f p μ :=
  ⟨hm, (el_bound h).trans_lt (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (measure_ne_top μ univ))
    ENNReal.ofReal_lt_top)⟩

/-! ## the one-point case `n = 0`, `Ω = univ` -/

lemma toL2L_at (u : H10 0 (univ : Set E0)) : (toL2L 0 univ u : E0 → ℝ) 0 = val u 0 := by
  have := ContinuousLinearMap.coeFn_compLp (WithLp.fstL 2 ℝ ℝ E0) (u : JetL2 0 univ)
  have h := ae_point this 0
  exact h

lemma toL2_eq (u : H10 0 (univ : Set E0)) : toL2 u = toL2L 0 univ u := rfl

lemma l2Embed_n0 (u v : H10 0 (univ : Set E0)) : l2Embed 0 univ u v = val u 0 * val v 0 := by
  have h1 : l2Embed 0 univ u v = inner ℝ (toL2L 0 univ u) (toL2L 0 univ v) := rfl
  rw [h1, MeasureTheory.L2.inner_def, int_pt, toL2L_at, toL2L_at]
  simp [mul_comm]

lemma form_n0 (P : Coeffs 0) (t : ℝ) (u v : H10 0 (univ : Set E0)) :
    form P t u v = P.c 0 t * val u 0 * val v 0 := by
  simp only [form, Finset.univ_eq_empty, Finset.sum_empty, zero_add]
  rw [int_pt]

lemma dual_n0 (φ : Hm1 0 (univ : Set E0)) (v : H10 0 (univ : Set E0)) : φ v = val v 0 * φ E1 := by
  conv_lhs => rw [h10_eq v]
  rw [map_smul, smul_eq_mul]


lemma g_norm_n0 (g : Lp ℝ 2 (volume.restrict (univ : Set E0))) : |(g : E0 → ℝ) 0| = ‖g‖ := by
  have h : ‖g‖ ^ 2 = ((g : E0 → ℝ) 0) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def, int_pt]
    simp [sq]
  exact (sq_eq_sq₀ (abs_nonneg _) (norm_nonneg _)).mp (by rw [sq_abs, h])

lemma el_cmul_norm {E : Type*} [SeminormedAddCommGroup E] (f : ℝ → E) {a : ℝ} (ha : 0 ≤ a)
    (p : ℝ≥0∞) (μ : Measure ℝ) :
    eLpNorm (fun t => a * ‖f t‖) p μ = ENNReal.ofReal a * eLpNorm f p μ := by
  have : (fun t => a * ‖f t‖) = a • (fun t => ‖f t‖) := by funext t; simp
  rw [this, eLpNorm_const_smul, ← el_norm, Real.enorm_eq_ofReal ha]


lemma comp_memLp_semi {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {f : ℝ → E} {p : ℝ≥0∞}
    {μ : Measure ℝ} (hf : MemLp f p μ) : MemLp (fun t => L (f t)) p μ := by
  refine ⟨L.continuous.comp_aestronglyMeasurable hf.1, ?_⟩
  refine (el_le (g := fun t => ‖L‖ * ‖f t‖)
    (Filter.Eventually.of_forall fun t => L.le_opNorm _)).trans_lt ?_
  rw [el_cmul_norm f (norm_nonneg L)]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.2

lemma memLp_smul_semi {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {a : ℝ → ℝ}
    {p : ℝ≥0∞} {μ : Measure ℝ} (ha : MemLp a p μ) (w : E) : MemLp (fun t => a t • w) p μ := by
  refine ⟨ha.1.smul_const w, ?_⟩
  refine (el_le (g := fun t => ‖w‖ * ‖a t‖)
    (Filter.Eventually.of_forall fun t => by rw [norm_smul, mul_comm])).trans_lt ?_
  rw [el_cmul_norm a (norm_nonneg w)]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ha.2

lemma aesm_norm_semi {E : Type*} [SeminormedAddCommGroup E] {f : ℝ → E} {p : ℝ≥0∞}
    {μ : Measure ℝ} (hf : MemLp f p μ) : AEStronglyMeasurable (fun t => ‖f t‖) μ := hf.1.norm

lemma norm_smul_semi {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] (a : ℝ) (w : E) :
    ‖a • w‖ = |a| * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs]

lemma hasWeakTimeDeriv_smul {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] (ι : X →L[ℝ] Y) {T : ℝ}
    (hT : 0 ≤ T) {y y' : ℝ → ℝ} (hac : AbsolutelyContinuousOnInterval y 0 T)
    (hd : ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAt y (y' t) t) (x0 : X) :
    HasWeakTimeDeriv ι T (fun t => y t • x0) (fun t => y' t • ι x0) := by
  intro φ hφ
  have key := weak_deriv_of_ac hT hac hd φ hφ
  simp_rw [map_smul, smul_smul]
  rw [integral_smul_const, integral_smul_const, key, neg_smul]

set_option maxHeartbeats 1600000 in
theorem weak_solution_exists_n0 (T : ℝ) (hT : 0 < T) (P : Coeffs 0)
    (hP : P.Assumption61 (univ : Set E0) T) :
    ∃ C : ℝ≥0, ∀ f : ℝ → Hm1 0 (univ : Set E0), MemLp f 2 (timeMeasure T) →
      ∀ g : Lp ℝ 2 (volume.restrict (univ : Set E0)),
        ∃ (u : ℝ → H10 0 (univ : Set E0)) (ut : ℝ → Hm1 0 (univ : Set E0)),
          IsWeakSolution (univ : Set E0) T P f g u ut ∧
          eLpNorm (fun t => toL2 (u t)) ∞ (timeMeasure T) + eLpNorm u 2 (timeMeasure T) +
              eLpNorm ut 2 (timeMeasure T) ≤
            (C : ℝ≥0∞) * (eLpNorm f 2 (timeMeasure T) + ‖g‖ₑ) := by
  have hc := hP.2.2.1
  have hcyl : cylMeasure (univ : Set E0) T = Measure.map (Prod.mk (0 : E0)) (timeMeasure T) := by
    simp only [cylMeasure, Measure.restrict_univ, vol_e0]
    exact Measure.dirac_prod 0
  rw [hcyl] at hc
  have hc0 : MemLp (fun t => P.c 0 t) ⊤ (timeMeasure T) :=
    hc.comp_of_map measurable_prodMk_left.aemeasurable
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = (eLpNorm (fun t => P.c 0 t) ⊤ (timeMeasure T)).toReal := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hKdef]; exact ENNReal.toReal_nonneg
  have hKb : ∀ᵐ t ∂(timeMeasure T), |P.c 0 t| ≤ K := by
    have := ae_le_eLpNormEssSup (f := fun t => P.c 0 t) (μ := timeMeasure T)
    filter_upwards [this] with t ht
    have h2 := ENNReal.toReal_mono hc0.eLpNorm_ne_top (ht.trans_eq (eLpNorm_exponent_top).symm)
    rw [hKdef, eLpNorm_exponent_top]
    simpa [Real.norm_eq_abs] using h2
  have : IsFiniteMeasure (timeMeasure T) := ⟨by simp [timeMeasure]⟩
  have hμ : (timeMeasure T) univ = ENNReal.ofReal T := by simp [timeMeasure]
  obtain ⟨sT, hsTdef⟩ : ∃ sT : ℝ, sT = T ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  have hsT0 : 0 ≤ sT := by rw [hsTdef]; exact Real.rpow_nonneg hT.le _
  have hsT : (timeMeasure T) univ ^ (2 : ℝ≥0∞).toReal⁻¹ = ENNReal.ofReal sT := by
    rw [hμ, ENNReal.ofReal_rpow_of_nonneg hT.le (by norm_num), hsTdef]; norm_num
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = ‖E1‖ := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L, L = l2Embed 0 univ E1 := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = ‖L‖ := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = ‖toL2 E1‖ := ⟨_, rfl⟩
  have hA : 0 ≤ A := by rw [hAdef]; exact norm_nonneg _
  have hB : 0 ≤ B := by rw [hBdef]; exact norm_nonneg L
  have hD : 0 ≤ D := by rw [hDdef]; exact norm_nonneg _
  obtain ⟨K1, hK1def⟩ : ∃ K1 : ℝ, K1 = Real.exp (2 * K * T) * (1 + sT * A) := ⟨_, rfl⟩
  obtain ⟨Cr, hCrdef⟩ : ∃ Cr : ℝ, Cr = K1 * (D + sT * A + sT * (B * K)) + A * B := ⟨_, rfl⟩
  refine ⟨Cr.toNNReal, fun f hf g => ?_⟩
  obtain ⟨cl, hcldef⟩ : ∃ cl : ℝ → ℝ, cl = fun t => max (-K) (min K (P.c 0 t)) := ⟨_, rfl⟩
  have hclb : ∀ t, |cl t| ≤ K := fun t => by
    rw [hcldef]; exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hcl_ae : ∀ᵐ t ∂(timeMeasure T), cl t = P.c 0 t := by
    filter_upwards [hKb] with t ht
    rw [abs_le] at ht
    rw [hcldef]; simp only [min_eq_right ht.2, max_eq_right ht.1]
  have hcl_m : AEStronglyMeasurable cl (timeMeasure T) := by
    rw [hcldef]; exact (by fun_prop : Continuous fun x : ℝ => max (-K) (min K x)).comp_aestronglyMeasurable hc0.1
  have hcl_i : IntervalIntegrable cl volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le]
    exact memLp_one_iff_integrable.mp (memLp_bound hcl_m
      (Filter.Eventually.of_forall fun t => (by rw [Real.norm_eq_abs]; exact hclb t)))
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ → ℝ, F = fun t => f t E1 := ⟨_, rfl⟩
  have hF2 : MemLp F 2 (timeMeasure T) := by
    rw [hFdef]; exact comp_memLp_semi (ContinuousLinearMap.apply ℝ ℝ E1) hf
  have hFi : IntervalIntegrable F volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le]
    exact memLp_one_iff_integrable.mp (hF2.mono_exponent (by norm_num))
  obtain ⟨y, hyc, hy0, hyac, hyd, hyb⟩ := scalar_ode (g0 := (g : E0 → ℝ) 0) hT hK hcl_i hclb hFi
  obtain ⟨M0, hM0def⟩ : ∃ M0 : ℝ, M0 = Real.exp (2 * K * T) * (|(g : E0 → ℝ) 0| + ∫ s in (0:ℝ)..T, |F s|) := ⟨_, rfl⟩
  have hyb' : ∀ᵐ t ∂(timeMeasure T), |y t| ≤ M0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [hM0def]; exact hyb t (Ioo_subset_Icc_self ht)
  have hym : AEStronglyMeasurable y (timeMeasure T) :=
    (hyc.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  refine ⟨fun t => y t • E1, fun t => (F t - cl t * y t) • L, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact memLp_bound (hym.smul_const E1) (C := M0 * A) (by
      filter_upwards [hyb'] with t ht
      rw [norm_smul, Real.norm_eq_abs, ← hAdef]
      exact mul_le_mul_of_nonneg_right ht hA)
  · have hcy : MemLp (fun t => cl t * y t) 2 (timeMeasure T) :=
      memLp_bound (hcl_m.mul hym) (C := K * M0) (by
        filter_upwards [hyb'] with t ht
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hclb t) ht (abs_nonneg _) hK)
    exact memLp_smul_semi (hF2.sub hcy) L
  · rw [hLdef]
    exact hasWeakTimeDeriv_smul (X := H10 0 (univ : Set E0)) (Y := Hm1 0 (univ : Set E0))
      (l2Embed 0 univ) hT.le hyac hyd E1
  · intro v
    filter_upwards [hcl_ae] with t ht
    rw [ContinuousLinearMap.smul_apply, hLdef, l2Embed_n0, form_n0, dual_n0 (f t) v, val_smul,
      val_E1, ht, smul_eq_mul]
    simp only [hFdef]
    ring
  · refine ⟨fun t => y t • toL2 E1, hyc.smul continuousOn_const,
      Filter.Eventually.of_forall fun t => ?_, ?_⟩
    · show y t • toL2 E1 = toL2 (y t • E1)
      rw [toL2_eq, toL2_eq, map_smul]
    · apply lp_ext0
      have := Lp.coeFn_smul (y 0) (toL2 E1)
      rw [ae_point this 0, Pi.smul_apply, toL2_eq, toL2L_at, val_E1, hy0, smul_eq_mul, mul_one]
  · -- the energy estimate
    obtain ⟨Nf, hNfdef⟩ : ∃ Nf : ℝ, Nf = (eLpNorm f 2 (timeMeasure T)).toReal := ⟨_, rfl⟩
    obtain ⟨Ng, hNgdef⟩ : ∃ Ng : ℝ, Ng = ‖g‖ := ⟨_, rfl⟩
    have hNf : 0 ≤ Nf := by rw [hNfdef]; exact ENNReal.toReal_nonneg
    have hNg : 0 ≤ Ng := by rw [hNgdef]; exact norm_nonneg _
    have h3 : eLpNorm F 2 (timeMeasure T) ≤ ENNReal.ofReal A * eLpNorm f 2 (timeMeasure T) := by
      refine (el_le (g := fun t => A * ‖f t‖) (Filter.Eventually.of_forall fun t => ?_)).trans
        (le_of_eq (el_cmul_norm f hA 2 _))
      have := (f t).le_opNorm E1
      rw [hFdef, hAdef, mul_comm]; exact this
    have hFint : ∫ s in (0:ℝ)..T, |F s| ≤ sT * (A * Nf) := by
      rw [intervalIntegral.integral_of_le hT.le, integral_Ioc_eq_integral_Ioo]
      have h1 : ∫ s in Ioo 0 T, |F s| = (eLpNorm F 1 (timeMeasure T)).toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm hF2.1]
        simp [Real.norm_eq_abs]
      have h2 : eLpNorm F 1 (timeMeasure T) ≤ eLpNorm F 2 (timeMeasure T) * ENNReal.ofReal sT := by
        have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hF2.1
          (μ := timeMeasure T)
        convert this using 2
        rw [hμ, ENNReal.ofReal_rpow_of_nonneg hT.le (by norm_num), hsTdef]
        norm_num
      have h4 : eLpNorm F 1 (timeMeasure T) ≤
          ENNReal.ofReal A * ENNReal.ofReal Nf * ENNReal.ofReal sT := by
        refine h2.trans (mul_le_mul_left ?_ _)
        rw [hNfdef, ENNReal.ofReal_toReal hf.eLpNorm_ne_top]; exact h3
      rw [h1]
      calc (eLpNorm F 1 (timeMeasure T)).toReal
          ≤ (ENNReal.ofReal A * ENNReal.ofReal Nf * ENNReal.ofReal sT).toReal :=
            ENNReal.toReal_mono (by finiteness) h4
        _ = sT * (A * Nf) := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA,
              ENNReal.toReal_ofReal hNf, ENNReal.toReal_ofReal hsT0]; ring
    have hM0 : M0 ≤ K1 * (Nf + Ng) := by
      rw [hM0def, hK1def, g_norm_n0, ← hNgdef]
      have h0 : 0 ≤ sT * A * Nf := by positivity
      have h5 : Ng + ∫ s in (0:ℝ)..T, |F s| ≤ (1 + sT * A) * (Nf + Ng) := by
        nlinarith [mul_nonneg (mul_nonneg hsT0 hA) hNg]
      calc Real.exp (2 * K * T) * (Ng + ∫ s in (0:ℝ)..T, |F s|)
          ≤ Real.exp (2 * K * T) * ((1 + sT * A) * (Nf + Ng)) :=
            mul_le_mul_of_nonneg_left h5 (Real.exp_pos _).le
        _ = Real.exp (2 * K * T) * (1 + sT * A) * (Nf + Ng) := by ring
    have hM0' : 0 ≤ M0 := by rw [hM0def]; exact le_trans (abs_nonneg _) (hyb 0 ⟨le_rfl, hT.le⟩)
    have b1 : eLpNorm (fun t => toL2 (y t • E1)) ∞ (timeMeasure T) ≤ ENNReal.ofReal (M0 * D) := by
      refine (el_bound (C := M0 * D) ?_).trans (by simp)
      filter_upwards [hyb'] with t ht
      rw [toL2_eq, map_smul, norm_smul, Real.norm_eq_abs, ← toL2_eq, ← hDdef]
      exact mul_le_mul_of_nonneg_right ht hD
    have b2 : eLpNorm (fun t => y t • E1) 2 (timeMeasure T) ≤ ENNReal.ofReal (sT * (M0 * A)) := by
      refine (el_bound (C := M0 * A) ?_).trans (le_of_eq ?_)
      · filter_upwards [hyb'] with t ht
        rw [norm_smul, Real.norm_eq_abs, ← hAdef]
        exact mul_le_mul_of_nonneg_right ht hA
      · rw [hsT, ← ENNReal.ofReal_mul hsT0]
    have b3 : eLpNorm (fun t => (F t - cl t * y t) • L) 2 (timeMeasure T) ≤
        ENNReal.ofReal (A * B) * eLpNorm f 2 (timeMeasure T) +
          ENNReal.ofReal (sT * (B * (K * M0))) := by
      have hpt : ∀ᵐ t ∂(timeMeasure T),
          ‖(F t - cl t * y t) • L‖ ≤ (fun t => (A * B) * ‖f t‖) t + (fun _ => B * (K * M0)) t := by
        filter_upwards [hyb'] with t ht
        refine le_trans (le_of_eq (norm_smul_semi (F t - cl t * y t) L)) ?_
        rw [← hBdef]
        have h1 : |F t| ≤ ‖f t‖ * A := by
          have := (f t).le_opNorm E1
          rw [hFdef, hAdef]
          simpa [Real.norm_eq_abs] using this
        have h2 : |cl t * y t| ≤ K * M0 := by
          rw [abs_mul]; exact mul_le_mul (hclb t) ht (abs_nonneg _) hK
        calc |F t - cl t * y t| * B ≤ (|F t| + |cl t * y t|) * B :=
              mul_le_mul_of_nonneg_right (abs_sub _ _) hB
          _ ≤ (‖f t‖ * A + K * M0) * B := by gcongr
          _ = (A * B) * ‖f t‖ + B * (K * M0) := by ring
      refine (el_le hpt).trans ((eLpNorm_add_le ?_ aestronglyMeasurable_const (by norm_num)).trans ?_)
      · exact (aesm_norm_semi hf).const_mul _
      · gcongr
        · exact le_of_eq (el_cmul_norm f (mul_nonneg hA hB) 2 _)
        · refine (el_bound (C := B * (K * M0)) (Filter.Eventually.of_forall fun t => ?_)).trans
            (le_of_eq ?_)
          · rw [Real.norm_of_nonneg (by positivity)]
          · rw [hsT, ← ENNReal.ofReal_mul hsT0]
    have hfe : eLpNorm f 2 (timeMeasure T) = ENNReal.ofReal Nf := by
      rw [hNfdef]; exact (ENNReal.ofReal_toReal hf.eLpNorm_ne_top).symm
    have hge : ‖g‖ₑ = ENNReal.ofReal Ng := by rw [hNgdef]; exact (ofReal_norm_eq_enorm g).symm
    calc _ ≤ ENNReal.ofReal (M0 * D) + ENNReal.ofReal (sT * (M0 * A)) +
          (ENNReal.ofReal (A * B) * eLpNorm f 2 (timeMeasure T) +
            ENNReal.ofReal (sT * (B * (K * M0)))) := add_le_add (add_le_add b1 b2) b3
      _ = ENNReal.ofReal (M0 * (D + sT * A + sT * (B * K)) + A * B * Nf) := by
          have n1 : 0 ≤ M0 * D := mul_nonneg hM0' hD
          have n2 : 0 ≤ sT * (M0 * A) := mul_nonneg hsT0 (mul_nonneg hM0' hA)
          have n3 : 0 ≤ A * B * Nf := mul_nonneg (mul_nonneg hA hB) hNf
          have n4 : 0 ≤ sT * (B * (K * M0)) := mul_nonneg hsT0 (mul_nonneg hB (mul_nonneg hK hM0'))
          rw [hfe, ← ENNReal.ofReal_mul (mul_nonneg hA hB), ← ENNReal.ofReal_add n3 n4,
            ← ENNReal.ofReal_add n1 n2, ← ENNReal.ofReal_add (add_nonneg n1 n2) (add_nonneg n3 n4)]
          congr 1; ring
      _ ≤ ENNReal.ofReal (Cr * (Nf + Ng)) := by
          apply ENNReal.ofReal_le_ofReal
          have hX : 0 ≤ D + sT * A + sT * (B * K) := by positivity
          have := mul_le_mul_of_nonneg_right hM0 hX
          rw [hCrdef]
          nlinarith [mul_nonneg (mul_nonneg hA hB) hNg]
      _ = (Cr.toNNReal : ℝ≥0∞) * (eLpNorm f 2 (timeMeasure T) + ‖g‖ₑ) := by
          have hCr0 : 0 ≤ Cr := by
            rw [hCrdef, hK1def]; positivity
          rw [hfe, hge, ← ENNReal.ofReal_add hNf hNg, ENNReal.ofReal_mul hCr0]
          rfl



lemma lp_sub_zero {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] (p : ℝ≥0∞) :
    Subsingleton (Lp E p (0 : Measure α)) := by
  refine ⟨fun a b => ?_⟩
  apply Lp.ext
  simp [Filter.EventuallyEq, ae_zero]

lemma el0 {E : Type*} [SeminormedAddCommGroup E] (p : ℝ≥0∞) (μ : Measure ℝ) :
    eLpNorm (fun _ : ℝ => (0 : E)) p μ = 0 := by
  have h1 : eLpNorm (fun _ : ℝ => (0 : E)) p μ = eLpNorm (fun _ : ℝ => (0 : ℝ)) p μ :=
    eLpNorm_congr_enorm_ae (Filter.Eventually.of_forall fun x => by simp [enorm_eq_nnnorm])
  rw [h1]; simp

lemma mem0 {E : Type*} [SeminormedAddCommGroup E] [Subsingleton E] (h : ℝ → E)
    (p : ℝ≥0∞) (μ : Measure ℝ) : MemLp h p μ := by
  have : h = fun _ => 0 := funext fun _ => Subsingleton.elim _ _
  subst this
  exact ⟨aestronglyMeasurable_const, by rw [el0]; exact ENNReal.zero_lt_top⟩

/-- HP-0 part (a): Ω = ∅ makes every space trivial. -/
theorem weak_solution_exists_empty {n : ℕ} (T : ℝ) (P : Coeffs n) :
    ∃ C : ℝ≥0, ∀ f : ℝ → Hm1 n (∅ : Set (EuclideanSpace ℝ (Fin n))), MemLp f 2 (timeMeasure T) →
      ∀ g : Lp ℝ 2 (volume.restrict (∅ : Set (EuclideanSpace ℝ (Fin n)))),
        ∃ (u : ℝ → H10 n (∅ : Set (EuclideanSpace ℝ (Fin n))))
          (ut : ℝ → Hm1 n (∅ : Set (EuclideanSpace ℝ (Fin n)))),
          IsWeakSolution (∅ : Set (EuclideanSpace ℝ (Fin n))) T P f g u ut ∧
          eLpNorm (fun t => toL2 (u t)) ∞ (timeMeasure T) + eLpNorm u 2 (timeMeasure T) +
              eLpNorm ut 2 (timeMeasure T) ≤
            (C : ℝ≥0∞) * (eLpNorm f 2 (timeMeasure T) + ‖g‖ₑ) := by
  have hL : Subsingleton (Lp ℝ 2 (volume.restrict (∅ : Set (EuclideanSpace ℝ (Fin n))))) := by
    rw [Measure.restrict_empty]; exact lp_sub_zero _
  have hJ : Subsingleton (JetL2 n (∅ : Set (EuclideanSpace ℝ (Fin n)))) := by
    unfold JetL2; rw [Measure.restrict_empty]; exact lp_sub_zero _
  have hH : Subsingleton (H10 n (∅ : Set (EuclideanSpace ℝ (Fin n)))) := by
    refine ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  have hM : Subsingleton (Hm1 n (∅ : Set (EuclideanSpace ℝ (Fin n)))) := by
    refine ⟨fun a b => ?_⟩
    ext v
    have hv : v = 0 := Subsingleton.elim _ _
    subst hv
    simp
  refine ⟨0, fun f hf g => ⟨fun _ => 0, fun _ => 0, ?_, ?_⟩⟩
  · refine ⟨mem0 _ _ _, ?_, ?_, ?_, ⟨fun _ => 0, continuousOn_const, ?_, ?_⟩⟩
    · convert mem0 (E := Hm1 n ∅) (fun _ => 0) 2 (timeMeasure T)
    · intro φ _
      simp
    · intro v
      refine Filter.Eventually.of_forall fun t => ?_
      have hv : v = 0 := Subsingleton.elim _ _
      subst hv
      simp [form]
    · exact Filter.Eventually.of_forall fun t => hL.elim _ _
    · exact hL.elim _ _
  · have e1 : eLpNorm (fun t => toL2 ((fun _ => (0 : H10 n ∅)) t)) ∞ (timeMeasure T) = 0 :=
      el0 _ _
    have e2 : eLpNorm (fun _ => (0 : H10 n ∅)) 2 (timeMeasure T) = 0 := el0 _ _
    have e3 : eLpNorm (fun _ => (0 : Hm1 n ∅)) 2 (timeMeasure T) = 0 := by
      convert el0 (E := Hm1 n ∅) 2 (timeMeasure T)
    rw [e1, e2, e3]; simp


/-- HP-0: the degenerate cases `n = 0` or `Ω = ∅` (existence with the estimate). -/
theorem weak_solution_exists_degenerate {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hdeg : n = 0 ∨ Ω = ∅) (T : ℝ) (hT : 0 < T)
    (P : Coeffs n) (hP : P.Assumption61 Ω T) :
    ∃ C : ℝ≥0, ∀ f : ℝ → Hm1 n Ω, MemLp f 2 (timeMeasure T) →
      ∀ g : Lp ℝ 2 (volume.restrict Ω),
        ∃ (u : ℝ → H10 n Ω) (ut : ℝ → Hm1 n Ω), IsWeakSolution Ω T P f g u ut ∧
          eLpNorm (fun t => toL2 (u t)) ∞ (timeMeasure T) + eLpNorm u 2 (timeMeasure T) +
              eLpNorm ut 2 (timeMeasure T) ≤
            (C : ℝ≥0∞) * (eLpNorm f 2 (timeMeasure T) + ‖g‖ₑ) := by
  rcases hdeg with rfl | rfl
  · rcases Ω.eq_empty_or_nonempty with rfl | hne
    · exact weak_solution_exists_empty T P
    · have hU : Ω = univ := hne.eq_univ
      subst hU
      exact weak_solution_exists_n0 T hT P hP
  · exact weak_solution_exists_empty T P

end HunterPDE.Parabolic

end


section

open MeasureTheory Set
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q4517Fast

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

/-- The embedding `L²(Ω) → H⁻¹(Ω)`, `f ↦ (v ↦ (f, v)_{L²})`. -/
noncomputable def l2Dual (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    Lp ℝ 2 (volume.restrict Ω) →L[ℝ] Hm1 n Ω :=
  (ContinuousLinearMap.precomp ℝ (toL2L n Ω) : _).comp (innerSL ℝ)

lemma toL2L_injective (hΩ : IsOpen Ω) : Function.Injective (toL2L n Ω) :=
  (h10_l2_dense_embeddings hΩ).1

lemma toL2L_denseRange (hΩ : IsOpen Ω) : DenseRange (toL2L n Ω) :=
  (h10_l2_dense_embeddings hΩ).2.1

lemma l2Dual_injective (hΩ : IsOpen Ω) : Function.Injective (l2Dual n Ω) :=
  (h10_l2_dense_embeddings hΩ).2.2.1

lemma l2Dual_denseRange (hΩ : IsOpen Ω) : DenseRange (l2Dual n Ω) :=
  (h10_l2_dense_embeddings hΩ).2.2.2

instance fact_two_ne_top : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

lemma separable_L2 : TopologicalSpace.SeparableSpace (Lp ℝ 2 (volume.restrict Ω)) := by
  infer_instance

instance : TopologicalSpace.SeparableSpace (Jet n) := by
  haveI : ProperSpace (Jet n) := FiniteDimensional.proper ℝ _
  infer_instance

lemma separable_H10 : TopologicalSpace.SeparableSpace (H10 n Ω) := by
  have : SecondCountableTopology (JetL2 n Ω) := inferInstance
  infer_instance

/-- The Hilbert triple `H¹₀(Ω) ⊂ L²(Ω) ⊂ H⁻¹(Ω)`. -/
noncomputable def h10Triple (hΩ : IsOpen Ω) : HilbertTriple (H10 n Ω) (Lp ℝ 2 (volume.restrict Ω)) where
  toH := toL2L n Ω
  toDual := l2Dual n Ω
  injective_toH := toL2L_injective hΩ
  injective_toDual := l2Dual_injective hΩ
  denseRange_toH := toL2L_denseRange hΩ
  denseRange_toDual := l2Dual_denseRange hΩ
  separable_V := separable_H10
  separable_H := separable_L2
  pairing := fun f v => rfl

lemma h10Triple_toDualV (hΩ : IsOpen Ω) : (h10Triple (n := n) hΩ).toDualV = l2Embed n Ω := rfl

end HunterPDE.Parabolic

end


section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q4517Fast

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

lemma val_ae' (u : H10 n Ω) :
    (toL2L n Ω u : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume.restrict Ω] val u := by
  have := (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).coeFn_compLp
    (μ := volume.restrict Ω) (p := 2) (u : JetL2 n Ω)
  filter_upwards [this] with x hx
  exact hx

lemma l2inner_eq (u v : H10 n Ω) : l2inner u v = inner ℝ (toL2L n Ω u) (toL2L n Ω v) := by
  rw [L2.inner_def, l2inner]
  refine integral_congr_ae ?_
  filter_upwards [val_ae' u, val_ae' v] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

lemma inner_H10 (u v : H10 n Ω) :
    inner ℝ u v = l2inner u v + ∫ x in Ω, inner ℝ (grad u x) (grad v x) := by
  have hpt : ∀ x, inner ℝ ((u : JetL2 n Ω) x) ((v : JetL2 n Ω) x) =
      val u x * val v x + inner ℝ (grad u x) (grad v x) := fun x => by
    rw [WithLp.prod_inner_apply]
    simp [val, grad, mul_comm]
  have htot := L2.integrable_inner (𝕜 := ℝ) (u : JetL2 n Ω) (v : JetL2 n Ω)
  have hv : Integrable (fun x => val u x * val v x) (volume.restrict Ω) := by
    have h := L2.integrable_inner (𝕜 := ℝ) (toL2L n Ω u) (toL2L n Ω v)
    refine h.congr ?_
    filter_upwards [val_ae' u, val_ae' v] with x h1 h2
    rw [h1, h2]
    simp [mul_comm]
  have hg : Integrable (fun x => inner ℝ (grad u x) (grad v x)) (volume.restrict Ω) := by
    refine (htot.sub hv).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    rw [hpt x]
    ring
  rw [Submodule.coe_inner, L2.inner_def, l2inner, ← integral_add hv hg]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

/-- `L²(Ω)` is infinite-dimensional when `Ω` is a nonempty open set and `n > 0`. -/
lemma not_finite_L2 (hn : 0 < n) (hΩo : IsOpen Ω) (hΩne : Ω.Nonempty) :
    ¬ Module.Finite ℝ (Lp ℝ 2 (volume.restrict Ω)) := by
  intro hfin
  obtain ⟨x0, hx0⟩ := hΩne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩo x0 hx0
  let A : ℕ → Set (EuclideanSpace ℝ (Fin n)) := fun k =>
    {x | r / 2 ^ (k + 1) < dist x x0 ∧ dist x x0 < r / 2 ^ k}
  have hAo : ∀ k, IsOpen (A k) := fun k =>
    (isOpen_lt continuous_const (continuous_id.dist continuous_const)).inter
      (isOpen_lt (continuous_id.dist continuous_const) continuous_const)
  have hAball : ∀ k, A k ⊆ Metric.ball x0 r := fun k x hx => by
    have h2 : r / 2 ^ k ≤ r := div_le_self hr.le (one_le_pow₀ (by norm_num))
    exact Metric.mem_ball.2 (lt_of_lt_of_le hx.2 h2)
  have hAsub : ∀ k, A k ⊆ Ω := fun k => (hAball k).trans hball
  have hAfin : ∀ k, (volume.restrict Ω) (A k) ≠ ⊤ := fun k =>
    ((Measure.restrict_le_self (A k)).trans_lt
      ((measure_mono (hAball k)).trans_lt measure_ball_lt_top)).ne
  -- a point of `A k`
  have hne : ∀ k, (A k).Nonempty := by
    intro k
    obtain ⟨i⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have e1 : (2 : ℝ) ^ (k + 2) = 4 * 2 ^ k := by ring
    have e2 : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    have hnorm : dist (x0 + (3 * r / 2 ^ (k + 2)) • EuclideanSpace.single i (1 : ℝ)) x0 =
        3 * r / (4 * 2 ^ k) := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, EuclideanSpace.norm_single, norm_one,
        mul_one, Real.norm_eq_abs, abs_of_pos (by positivity), e1]
    refine ⟨x0 + (3 * r / 2 ^ (k + 2)) • EuclideanSpace.single i (1 : ℝ), ?_, ?_⟩
    · show r / 2 ^ (k + 1) < dist _ x0
      rw [hnorm, e2, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    · show dist _ x0 < r / 2 ^ k
      rw [hnorm, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  have hpos : ∀ k, 0 < (volume.restrict Ω) (A k) := by
    intro k
    rw [Measure.restrict_apply (hAo k).measurableSet, inter_eq_left.2 (hAsub k)]
    exact (hAo k).measure_pos volume (hne k)
  have hdisj : ∀ j k, j ≠ k → Disjoint (A j) (A k) := by
    intro j k hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · refine Set.disjoint_left.2 fun x hxj hxk => ?_
      have : r / 2 ^ k ≤ r / 2 ^ (j + 1) :=
        div_le_div_of_nonneg_left hr.le (by positivity) (pow_le_pow_right₀ (by norm_num) h)
      linarith [hxj.1, hxk.2]
    · refine Set.disjoint_left.2 fun x hxj hxk => ?_
      have : r / 2 ^ j ≤ r / 2 ^ (k + 1) :=
        div_le_div_of_nonneg_left hr.le (by positivity) (pow_le_pow_right₀ (by norm_num) h)
      linarith [hxj.2, hxk.1]
  let e : ℕ → Lp ℝ 2 (volume.restrict Ω) := fun k =>
    indicatorConstLp 2 (hAo k).measurableSet (hAfin k) (1 : ℝ)
  have hinner : ∀ j k, inner ℝ (e j) (e k) =
      ∫ x in A j, (A k).indicator (fun _ => (1 : ℝ)) x ∂(volume.restrict Ω) := by
    intro j k
    rw [L2.inner_indicatorConstLp_one]
    refine integral_congr_ae ?_
    exact ae_restrict_of_ae (indicatorConstLp_coeFn (p := 2) (hs := (hAo k).measurableSet)
      (hμs := hAfin k) (c := (1 : ℝ)))
  have horth : Pairwise fun j k => inner ℝ (e j) (e k) = 0 := by
    intro j k hjk
    rw [hinner]
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    exact Set.indicator_of_notMem (Set.disjoint_left.1 (hdisj j k hjk) hx) _
  have hnz : ∀ k, e k ≠ 0 := by
    intro k h
    have h1 := hinner k k
    rw [h, inner_zero_left] at h1
    have h2 : ∫ x in A k, (A k).indicator (fun _ => (1 : ℝ)) x ∂(volume.restrict Ω) =
        ((volume.restrict Ω) (A k)).toReal := by
      rw [setIntegral_indicator (hAo k).measurableSet, Set.inter_self, setIntegral_const,
        smul_eq_mul, mul_one, Measure.real]
    rw [h2] at h1
    exact (ENNReal.toReal_pos (hpos k).ne' (hAfin k)).ne h1
  have hli : LinearIndependent ℝ e := linearIndependent_of_ne_zero_of_inner_eq_zero hnz horth
  have := hli.finite
  exact not_finite ℕ

theorem exists_dirichlet_eigenbasis_of (hn : 0 < n) (hΩo : IsOpen Ω) (hΩne : Ω.Nonempty)
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 (volume.restrict Ω))]
    (hdense : DenseRange (toL2L n Ω)) (hcomp : IsCompactOperator (toL2L n Ω))
    (hspec : ∀ T : Lp ℝ 2 (volume.restrict Ω) →L[ℝ] Lp ℝ 2 (volume.restrict Ω),
      IsCompactOperator T → (T : Lp ℝ 2 (volume.restrict Ω) →ₗ[ℝ] Lp ℝ 2 (volume.restrict Ω)).IsSymmetric →
      Function.Injective T →
      ∃ (ι : Type) (b : HilbertBasis ι ℝ (Lp ℝ 2 (volume.restrict Ω))) (ν : ι → ℝ),
        (∀ i, T (b i) = ν i • b i) ∧ (∀ i, ν i ≠ 0) ∧ Tendsto ν cofinite (𝓝 0)) :
    ∃ (w : ℕ → H10 n Ω) (eig : ℕ → ℝ), IsDirichletEigenbasis Ω w eig := by
  obtain ⟨S, hS⟩ : ∃ S, S = ContinuousLinearMap.adjoint (toL2L n Ω) := ⟨_, rfl⟩
  have hSl : ∀ (x : H10 n Ω) (y : Lp ℝ 2 (volume.restrict Ω)),
      inner ℝ (S y) x = inner ℝ y (toL2L n Ω x) := by
    rw [hS]; exact ContinuousLinearMap.adjoint_inner_left _
  have hSr : ∀ (x : H10 n Ω) (y : Lp ℝ 2 (volume.restrict Ω)),
      inner ℝ x (S y) = inner ℝ (toL2L n Ω x) y := by
    rw [hS]; exact ContinuousLinearMap.adjoint_inner_right _
  have hsym : (((toL2L n Ω).comp S : Lp ℝ 2 (volume.restrict Ω) →L[ℝ] Lp ℝ 2 (volume.restrict Ω)) :
      Lp ℝ 2 (volume.restrict Ω) →ₗ[ℝ] Lp ℝ 2 (volume.restrict Ω)).IsSymmetric := by
    intro f g
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
    rw [← hSr, hSl]
  have hinj : Function.Injective ((toL2L n Ω).comp S) := by
    refine (injective_iff_map_eq_zero ((toL2L n Ω).comp S)).2 fun f hf => ?_
    rw [ContinuousLinearMap.comp_apply] at hf
    have h1 : inner ℝ (S f) (S f) = 0 := by rw [hSl, hf, inner_zero_right]
    have hSf : S f = 0 := inner_self_eq_zero.1 h1
    have h2 : (fun y => inner ℝ f y) ∘ (toL2L n Ω) = (fun _ => (0 : ℝ)) ∘ (toL2L n Ω) := by
      funext v
      simp only [Function.comp_apply]
      rw [← hSl, hSf, inner_zero_left]
    have h3 := hdense.equalizer (continuous_const.inner continuous_id) continuous_const h2
    exact inner_self_eq_zero.1 (congrFun h3 f)
  obtain ⟨ι, b, ν, hb, hν, -⟩ :=
    hspec ((toL2L n Ω).comp S) (hcomp.comp_clm S) hsym hinj
  -- `ι` is countable
  have hcount : (univ : Set ι).Countable := by
    refine Set.PairwiseDisjoint.countable_of_isOpen (s := fun i => Metric.ball (b i) (1 / 2))
      ?_ (fun i _ => Metric.isOpen_ball) (fun i _ => Metric.nonempty_ball.2 (by norm_num))
    intro i _ j _ hij
    refine Metric.ball_disjoint_ball ?_
    rw [dist_eq_norm]
    have h2 : ‖b i - b j‖ ^ 2 = 2 := by
      rw [norm_sub_sq_real, b.orthonormal.norm_eq_one, b.orthonormal.norm_eq_one,
        b.orthonormal.inner_eq_zero hij]
      norm_num
    nlinarith [norm_nonneg (b i - b j)]
  have : Countable ι := Set.countable_univ_iff.1 hcount
  have : Infinite ι := by
    by_contra hinf
    rw [not_infinite_iff_finite] at hinf
    have : Fintype ι := Fintype.ofFinite ι
    exact not_finite_L2 hn hΩo hΩne (Module.Finite.of_basis b.toOrthonormalBasis.toBasis)
  have : Encodable ι := Encodable.ofCountable ι
  have : Denumerable ι := Denumerable.ofEncodableOfInfinite ι
  obtain ⟨e, he⟩ : ∃ e : ℕ ≃ ι, e = (Denumerable.eqv ι).symm := ⟨_, rfl⟩
  have hK : ∀ i, toL2L n Ω (S (b i)) = ν i • b i := fun i => hb i
  refine ⟨fun k => (ν (e k))⁻¹ • S (b (e k)), fun k => (ν (e k))⁻¹ - 1, ?_, ?_, ?_⟩
  · intro k v
    have hw : toL2L n Ω ((ν (e k))⁻¹ • S (b (e k))) = b (e k) := by
      rw [map_smul, hK, inv_smul_smul₀ (hν _)]
    have h1 := inner_H10 ((ν (e k))⁻¹ • S (b (e k))) v
    have hA : inner ℝ ((ν (e k))⁻¹ • S (b (e k))) v =
        (ν (e k))⁻¹ * inner ℝ (b (e k)) (toL2L n Ω v) := by
      rw [Submodule.coe_inner, Submodule.coe_smul, real_inner_smul_left, ← Submodule.coe_inner, hSl]
    have hB : l2inner ((ν (e k))⁻¹ • S (b (e k))) v = inner ℝ (b (e k)) (toL2L n Ω v) := by
      rw [l2inner_eq, hw]
    rw [hB] at h1 ⊢
    linear_combination hA - h1
  · intro j k
    have hw : ∀ k, toL2L n Ω ((ν (e k))⁻¹ • S (b (e k))) = b (e k) := fun k => by
      rw [map_smul, hK, inv_smul_smul₀ (hν _)]
    rw [l2inner_eq, hw, hw]
    classical
    by_cases hjk : j = k
    · subst hjk
      simp [b.orthonormal.norm_eq_one]
    · rw [if_neg hjk, b.orthonormal.inner_eq_zero (fun h => hjk (e.injective h))]
  · have hw : (fun k => toL2 ((ν (e k))⁻¹ • S (b (e k)))) = b ∘ e := by
      funext k
      show toL2L n Ω ((ν (e k))⁻¹ • S (b (e k))) = b (e k)
      rw [map_smul, hK, inv_smul_smul₀ (hν _)]
    rw [hw, e.surjective.range_comp]
    exact b.dense_span

end HunterPDE.Parabolic

end


open MeasureTheory HunterPDE.Parabolic in
open scoped ENNReal NNReal in
theorem solution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (T : ℝ) (hT : 0 < T) (P : Coeffs n)
    (hP : P.Assumption61 Ω T) :
    ∃ C : ℝ≥0, ∀ f : ℝ → Hm1 n Ω, MemLp f 2 (timeMeasure T) →
      ∀ g : Lp ℝ 2 (volume.restrict Ω),
        (∃ (u : ℝ → H10 n Ω) (ut : ℝ → Hm1 n Ω), IsWeakSolution Ω T P f g u ut ∧
          eLpNorm (fun t => toL2 (u t)) ∞ (timeMeasure T) + eLpNorm u 2 (timeMeasure T) +
              eLpNorm ut 2 (timeMeasure T) ≤
            (C : ℝ≥0∞) * (eLpNorm f 2 (timeMeasure T) + ‖g‖ₑ)) ∧
        ∀ (u₁ u₂ : ℝ → H10 n Ω) (ut₁ ut₂ : ℝ → Hm1 n Ω),
          IsWeakSolution Ω T P f g u₁ ut₁ → IsWeakSolution Ω T P f g u₂ ut₂ →
            u₁ =ᵐ[timeMeasure T] u₂ := by
  have huniq : ∀ (f : ℝ → Hm1 n Ω) (g : Lp ℝ 2 (volume.restrict Ω))
      (u₁ u₂ : ℝ → H10 n Ω) (ut₁ ut₂ : ℝ → Hm1 n Ω),
      IsWeakSolution Ω T P f g u₁ ut₁ → IsWeakSolution Ω T P f g u₂ ut₂ →
        u₁ =ᵐ[timeMeasure T] u₂ := by
    intro f g u₁ u₂ ut₁ ut₂ h₁ h₂
    exact weak_solution_unique Ω hΩo hΩb T hT P hP f g u₁ u₂ ut₁ ut₂ h₁ h₂
  by_cases hdeg : n = 0 ∨ Ω = ∅
  · obtain ⟨C, hC⟩ := weak_solution_exists_degenerate Ω hΩo hΩb hdeg T hT P hP
    exact ⟨C, fun f hf g => ⟨hC f hf g, fun u₁ u₂ ut₁ ut₂ h₁ h₂ =>
      huniq f g u₁ u₂ ut₁ ut₂ h₁ h₂⟩⟩
  · push_neg at hdeg
    have hn : 0 < n := Nat.pos_of_ne_zero hdeg.1
    have hne : Ω.Nonempty := hdeg.2
    obtain ⟨w, eig, hw⟩ := exists_dirichlet_eigenbasis_of hn hΩo hne (toL2L_denseRange hΩo)
      (rellich_h10_l2_compact Ω hΩo hΩb)
      (fun T' hc hs hi => AsymptoticOperator.exists_hilbertBasis_eigenvectors_of_isCompactOperator
        T' hc hs hi)
    obtain ⟨C, hC⟩ := galerkin_limit Ω hΩo hΩb T hT P hP
    refine ⟨C, fun f hf g => ⟨?_, fun u₁ u₂ ut₁ ut₂ h₁ h₂ => huniq f g u₁ u₂ ut₁ ut₂ h₁ h₂⟩⟩
    choose uN uNt hN _ using fun N => galerkin_exists_unique Ω hΩo hΩb T hT P hP w eig hw f hf g N
    obtain ⟨φ, -, u, ut, hsol, -, -, hest⟩ := hC w eig hw f hf g uN uNt hN
    exact ⟨u, ut, hsol, hest⟩


