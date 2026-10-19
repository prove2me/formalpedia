-- Prove2me | solution 1 for HunterPDE.Parabolic.h10_l2_dense_embeddings
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T05:00:46.466962+00:00
-- url     : https://prove2.me/submissions/95819e56-ad3a-4926-9132-e7bd0ba61e48

import Mathlib
import Definitions.Def_HunterPDE_Parabolic_H10
import Definitions.Def_HunterPDE_Parabolic_WeakSolution

/-! Child of the reduction of `HunterPDE.Parabolic.galerkin_limit` (Hunter, *Notes on PDEs*, §6.A,
Definition 6.40): for open `Ω`, the embeddings `H¹₀(Ω) → L²(Ω)`, `u ↦ u`, and `L²(Ω) → H⁻¹(Ω)`,
`f ↦ (f, ·)_{L²}`, are injective with dense range (the Hilbert triple `H¹₀ ⊂ L² ⊂ H⁻¹`). -/

set_option autoImplicit false
set_option linter.all false

section Q0ffd_I
/-! Shortcut instances for `H¹₀(Ω)` and `H⁻¹(Ω)`: each one is exactly the instance that type-class
search finds anyway (`inferInstance`), declared once with high priority so that later searches stop at
it instead of re-deriving it through the submodule / continuous-linear-map hierarchy every time.
They are `scoped` (opened in each block below, not at the final `theorem solution`), so the
statement of `solution` is elaborated with the standard instances, exactly like the target's. -/
open MeasureTheory
namespace HunterPDE.Parabolic.Q0ffdFast
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
noncomputable scoped instance (priority := high) q0ffdEMS : MeasureSpace (EuclideanSpace ℝ (Fin n)) :=
  inferInstance
noncomputable scoped instance (priority := high) q0ffdH10NACG : NormedAddCommGroup (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdH10SACG : SeminormedAddCommGroup (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdH10IPS : InnerProductSpace ℝ (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdH10NS : NormedSpace ℝ (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdH10Mod : Module ℝ (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdHm1NACG : NormedAddCommGroup (Hm1 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdHm1SACG : SeminormedAddCommGroup (Hm1 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdHm1NS : NormedSpace ℝ (Hm1 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdHm1Mod : Module ℝ (Hm1 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdHm1CS : CompleteSpace (Hm1 n Ω) := inferInstance
end HunterPDE.Parabolic.Q0ffdFast
end Q0ffd_I

section Q0ffd_L0
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section ht
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}



/-- The embedding `L²(Ω) → H⁻¹(Ω)`, `f ↦ (v ↦ (f, v)_{L²})`. -/
noncomputable def l2Dual (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    Lp ℝ 2 (volume.restrict Ω) →L[ℝ] Hm1 n Ω :=
  (ContinuousLinearMap.precomp ℝ (toL2L n Ω) : _).comp (innerSL ℝ)

lemma l2Dual_apply (f : Lp ℝ 2 (volume.restrict Ω)) (v : H10 n Ω) :
    l2Dual n Ω f v = inner ℝ f (toL2L n Ω v) := rfl

/-- The unit vector `e_i`. -/
noncomputable def ei (n : ℕ) (i : Fin n) : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1

lemma inner_grad_ei (φ : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    inner ℝ (gradient φ x) (ei n i) = fderiv ℝ φ x (ei n i) := by
  simp only [gradient, InnerProductSpace.toDual_symm_apply]

/-- The jet `(∂_i ψ, ψ e_i)` used to test the weak derivative identity. -/
noncomputable def psiFun (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n) :
    EuclideanSpace ℝ (Fin n) → Jet n :=
  fun x => WithLp.toLp 2 (fderiv ℝ ψ x (ei n i), ψ x • ei n i)

lemma psiFun_memLp {ψ : EuclideanSpace ℝ (Fin n) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (i : Fin n) : MemLp (psiFun ψ i) 2 (volume.restrict Ω) := by
  have hcont : Continuous (psiFun ψ i) := by
    unfold psiFun
    exact (WithLp.prod_continuous_toLp 2 ℝ (EuclideanSpace ℝ (Fin n))).comp
      (((hψ.continuous_fderiv (by simp only [ne_eq, WithTop.coe_eq_zero, ENat.top_ne_zero, not_false_eq_true])).clm_apply continuous_const).prodMk
        (hψ.continuous.smul continuous_const))
  have hsupp : HasCompactSupport (psiFun ψ i) := by
    refine hc.mono' ?_
    intro x hx
    by_contra h
    apply hx
    simp only [psiFun, fderiv_of_notMem_tsupport ℝ h, zero_apply, image_eq_zero_of_notMem_tsupport h, zero_smul, WithLp.toLp_eq_zero, Prod.mk_eq_zero, and_self]
  exact (hcont.memLp_of_hasCompactSupport hsupp).restrict _

lemma integral_ibp_zero {φ ψ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (v : EuclideanSpace ℝ (Fin n)) :
    ∫ x, (φ x * fderiv ℝ ψ x v + ψ x * fderiv ℝ φ x v) = 0 := by
  have c1 : Continuous fun x => fderiv ℝ φ x v :=
    (hφ.continuous_fderiv (by simp only [ne_eq, WithTop.coe_eq_zero, ENat.top_ne_zero, not_false_eq_true])).clm_apply continuous_const
  have c2 : Continuous fun x => fderiv ℝ ψ x v :=
    (hψ.continuous_fderiv (by simp only [ne_eq, WithTop.coe_eq_zero, ENat.top_ne_zero, not_false_eq_true])).clm_apply continuous_const
  have i1 : Integrable (fun x => fderiv ℝ φ x v * ψ x) :=
    (c1.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
  have i2 : Integrable (fun x => φ x * fderiv ℝ ψ x v) :=
    (hφ.continuous.mul c2).integrable_of_hasCompactSupport hφc.mul_right
  have i3 : Integrable (fun x => φ x * ψ x) :=
    (hφ.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hφc.mul_right
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) i1 i2 i3
    (fun x _ => (hφ.differentiable (by simp only [ne_eq, WithTop.coe_eq_zero, ENat.top_ne_zero, not_false_eq_true])).differentiableAt)
    (fun x _ => (hψ.differentiable (by simp only [ne_eq, WithTop.coe_eq_zero, ENat.top_ne_zero, not_false_eq_true])).differentiableAt)
  have i4 : Integrable (fun x => ψ x * fderiv ℝ φ x v) := by
    simpa only [mul_comm] using i1
  rw [integral_add i2 i4, hibp]
  simp only [mul_comm (fderiv ℝ φ _ v)]
  ring

/-- Test jets are orthogonal to `Ψ = (∂_i ψ, ψ e_i)`. -/
lemma inner_testJet_psi {ψ : EuclideanSpace ℝ (Fin n) → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψt : tsupport ψ ⊆ Ω) (i : Fin n)
    (F : JetL2 n Ω) (hF : F ∈ testJets n Ω) :
    inner ℝ F ((psiFun_memLp (Ω := Ω) hψ hψc i).toLp) = 0 := by
  obtain ⟨φ, hφ, hφc, hφt, hFφ⟩ := hF
  rw [MeasureTheory.L2.inner_def]
  have hΨ := (psiFun_memLp (Ω := Ω) hψ hψc i).coeFn_toLp
  have h1 : ∫ x, inner ℝ ((F : _ → Jet n) x)
      (((psiFun_memLp (Ω := Ω) hψ hψc i).toLp : _ → Jet n) x) ∂(volume.restrict Ω) =
      ∫ x in Ω, (φ x * fderiv ℝ ψ x (ei n i) + ψ x * fderiv ℝ φ x (ei n i)) := by
    refine integral_congr_ae ?_
    filter_upwards [hFφ, hΨ] with x h1 h2
    rw [h1, h2, WithLp.prod_inner_apply]
    simp only [psiFun, WithLp.ofLp_toLp, inner_smul_right, inner_grad_ei]
    simp only [RCLike.inner_apply, Real.ringHom_apply, mul_comm]
  rw [h1, setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_ibp_zero hφ hφc hψ hψc (ei n i)
  · intro x hx
    have hxψ : x ∉ tsupport ψ := fun h => hx (hψt h)
    simp only [fderiv_of_notMem_tsupport ℝ hxψ, zero_apply, mul_zero, image_eq_zero_of_notMem_tsupport hxψ, zero_mul, add_zero]

lemma inner_H10_psi {ψ : EuclideanSpace ℝ (Fin n) → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψt : tsupport ψ ⊆ Ω) (i : Fin n) (u : H10 n Ω) :
    inner ℝ (u : JetL2 n Ω) ((psiFun_memLp (Ω := Ω) hψ hψc i).toLp) = 0 := by
  set Ψ := (psiFun_memLp (Ω := Ω) hψ hψc i).toLp
  have hle : Submodule.span ℝ (testJets n Ω) ≤ LinearMap.ker ((innerSL ℝ Ψ : JetL2 n Ω →L[ℝ] ℝ) : JetL2 n Ω →ₗ[ℝ] ℝ) := by
    rw [Submodule.span_le]
    intro F hF
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply]
    rw [real_inner_comm]
    exact inner_testJet_psi hψ hψc hψt i F hF
  have hcl : H10 n Ω ≤ LinearMap.ker ((innerSL ℝ Ψ : JetL2 n Ω →L[ℝ] ℝ) : JetL2 n Ω →ₗ[ℝ] ℝ) :=
    Submodule.topologicalClosure_minimal _ hle (ContinuousLinearMap.isClosed_ker _)
  have := hcl u.2
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply] at this
  rw [real_inner_comm]; exact this

/-- (H1) `toL2` is injective on `H¹₀`: the weak gradient of `0` is `0`. -/
lemma toL2L_injective (hΩ : IsOpen Ω) : Function.Injective (toL2L n Ω) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  -- the value is 0 a.e.
  have hval : ∀ᵐ x ∂(volume.restrict Ω), (WithLp.ofLp ((u : JetL2 n Ω) x)).1 = 0 := by
    have h1 := ContinuousLinearMap.coeFn_compLp (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n)))
      (u : JetL2 n Ω)
    have h2 : (toL2L n Ω u : _ → ℝ) =ᵐ[volume.restrict Ω] 0 := by
      rw [hu]; exact Lp.coeFn_zero _ _ _
    filter_upwards [h1, h2] with x hx1 hx2
    have : (toL2L n Ω u : _ → ℝ) x = (WithLp.ofLp ((u : JetL2 n Ω) x)).1 := hx1
    rw [← this, hx2]; rfl
  -- each partial derivative is 0 a.e.
  have hgrad : ∀ i : Fin n, ∀ᵐ x ∂(volume.restrict Ω), (WithLp.ofLp ((u : JetL2 n Ω) x)).2 i = 0 := by
    intro i
    let g : EuclideanSpace ℝ (Fin n) → ℝ := fun x => (WithLp.ofLp ((u : JetL2 n Ω) x)).2 i
    have hgL : MemLp g 2 (volume.restrict Ω) := by
      have := ((EuclideanSpace.proj i).comp
        (WithLp.sndL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n)))).comp_memLp' (Lp.memLp (u : JetL2 n Ω))
      exact this
    have hloc : LocallyIntegrableOn g Ω (volume.restrict Ω) :=
      (hgL.locallyIntegrable (by norm_num)).locallyIntegrableOn _
    have key := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun ψ hψ hψc hψt => by
      have h0 := inner_H10_psi hψ hψc hψt i u
      rw [MeasureTheory.L2.inner_def] at h0
      rw [← h0]
      refine integral_congr_ae ?_
      filter_upwards [(psiFun_memLp (Ω := Ω) hψ hψc i).coeFn_toLp, hval] with x h1 h2
      rw [h1, WithLp.prod_inner_apply]
      simp only [psiFun, WithLp.ofLp_toLp, h2, zero_mul, zero_add, inner_smul_right, smul_eq_mul]
      simp only [WithLp.ofLp_snd, ei, RCLike.inner_apply, Real.ringHom_apply, mul_zero, EuclideanSpace.inner_single_right, one_mul, zero_add, g])
    filter_upwards [key, ae_restrict_mem₀ hΩ.measurableSet.nullMeasurableSet] with x hx hxΩ
    exact hx hxΩ
  have hall := ae_all_iff.mpr hgrad
  apply Subtype.ext
  show (u : JetL2 n Ω) = 0
  apply Lp.ext
  filter_upwards [hval, hall, Lp.coeFn_zero (Jet n) 2 (volume.restrict Ω)] with x h1 h2 h3
  rw [h3]
  apply WithLp.ofLp_injective
  refine Prod.ext ?_ ?_
  · simpa only [WithLp.ofLp_fst, Pi.zero_apply, WithLp.ofLp_zero, Prod.fst_zero] using h1
  · ext i; simpa only [WithLp.ofLp_snd, Pi.zero_apply, WithLp.ofLp_zero, Prod.snd_zero, PiLp.zero_apply] using h2 i

/-- Smooth approximation of a continuous compactly supported function, keeping the support. -/
lemma smooth_approx_supp {g : EuclideanSpace ℝ (Fin n) → ℝ} (hgc : HasCompactSupport g)
    (hg : Continuous g) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧
      tsupport h ⊆ tsupport g ∧ eLpNorm (g - h) 2 volume ≤ ENNReal.ofReal ε := by
  have hfin : volume (tsupport g) ≠ ⊤ := hgc.measure_lt_top.ne
  set m : ℝ := (volume (tsupport g)).toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  set c : ℝ := ε / (m ^ (1 / 2 : ℝ) + 1) with hc
  have hsq : 0 ≤ m ^ (1 / 2 : ℝ) := Real.rpow_nonneg hm0 _
  have hc0 : 0 < c := div_pos hε (by linarith)
  have hob1 := hg.exists_contDiff_approx ⊤ (ε := fun _ => c) (by fun_prop)
    (fun _ => hc0)
  obtain ⟨h, hh1, hh2, hh3⟩ := hob1
  have hts : tsupport h ⊆ tsupport g :=
    closure_minimal (hh3.trans (subset_tsupport g)) (isClosed_tsupport g)
  refine ⟨h, hh1, hgc.mono hh3, hts, ?_⟩
  have key := eLpNorm_sub_le_of_dist_bdd volume (p := 2) (by norm_num)
    (isClosed_tsupport g).measurableSet hc0.le (f := g) (g := h)
    (fun x => by rw [dist_comm]; exact (hh2 x).le) (subset_tsupport g)
    (hh3.trans (subset_tsupport g))
  refine key.trans ?_
  rw [← ENNReal.ofReal_toReal hfin, ← hm, ENNReal.ofReal_rpow_of_nonneg hm0 (by norm_num),
    ← ENNReal.ofReal_mul hc0.le]
  apply ENNReal.ofReal_le_ofReal
  norm_num only [ENNReal.toReal_ofNat]
  rw [hc, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith

/-- Dominated convergence for cutoffs: `‖F (1 - d_k)‖_{L²} → 0`. -/
lemma tendsto_eLpNorm_cutoff {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : MemLp F 2 volume)
    {c : ℕ → EuclideanSpace ℝ (Fin n) → ℝ} (hcc : ∀ k, Continuous (c k))
    (hc1 : ∀ k x, |c k x| ≤ 1) (hlim : ∀ x, ∀ᶠ k in Filter.atTop, F x * c k x = 0) :
    Filter.Tendsto (fun k => eLpNorm (fun x => F x * c k x) 2 volume) Filter.atTop (nhds 0) := by
  have e : ∀ k, eLpNorm (fun x => F x * c k x) 2 volume =
      (∫⁻ x, ‖F x * c k x‖ₑ ^ ((2 : ℝ≥0∞).toReal)) ^ (1 / (2 : ℝ≥0∞).toReal) := fun k =>
    eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)
  simp_rw [e]
  have hbound : ∫⁻ x, ‖F x‖ₑ ^ ((2 : ℝ≥0∞).toReal) ≠ ⊤ :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num) (by norm_num) hF.2).ne
  have hT : Filter.Tendsto (fun k => ∫⁻ x, ‖F x * c k x‖ₑ ^ ((2 : ℝ≥0∞).toReal)) Filter.atTop
      (nhds (∫⁻ (_x : EuclideanSpace ℝ (Fin n)), (0 : ℝ≥0∞))) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun x => ‖F x‖ₑ ^ ((2 : ℝ≥0∞).toReal))
      (fun k => ?_) (fun k => ?_) hbound ?_
    · exact ((hF.1.mul (hcc k).aestronglyMeasurable).enorm.pow_const _)
    · refine Filter.Eventually.of_forall fun x => ?_
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      rw [enorm_mul]
      calc ‖F x‖ₑ * ‖c k x‖ₑ ≤ ‖F x‖ₑ * 1 := by
            gcongr
            rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
            exact ENNReal.ofReal_le_one.mpr (hc1 k x)
        _ = ‖F x‖ₑ := mul_one _
    · refine Filter.Eventually.of_forall fun x => ?_
      apply tendsto_const_nhds.congr'
      filter_upwards [hlim x] with k hk
      rw [hk]; simp only [enorm_zero, ENNReal.toReal_ofNat, ENNReal.rpow_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  rw [lintegral_zero] at hT
  have := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ≥0∞).toReal)).tendsto 0 |>.comp hT
  simpa only [enorm_mul, ENNReal.toReal_ofNat, ENNReal.rpow_ofNat, one_div, Function.comp_def, inv_pos, Nat.ofNat_pos, ENNReal.zero_rpow_of_pos] using this

/-- Continuous compactly supported functions with support inside `Ω` are dense in `L²(Ω)`
(stated for the zero extension `F` of `f`). -/
lemma exists_cont_approx (hΩ : IsOpen Ω) {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : MemLp F 2 volume)
    (hF0 : ∀ x, x ∉ Ω → F x = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ Ω ∧
      eLpNorm (F - g) 2 volume ≤ ENNReal.ofReal ε := by
  have hε2 : 0 < ε / 2 := by linarith
  have hob2 := hF.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num)
    (ε := ENNReal.ofReal (ε / 2)) (by simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le, Nat.ofNat_pos, div_pos_iff_of_pos_right] using hε2)
  obtain ⟨g, hgc, hgF, hgcont, -⟩ := hob2
  by_cases hU : Ω = univ
  · refine ⟨g, hgcont, hgc, by rw [hU]; exact subset_univ _, hgF.trans ?_⟩
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hne : (Ωᶜ).Nonempty := by
    rw [nonempty_compl]; exact hU
  let d : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun k x =>
    min 1 (max 0 (Metric.infDist x Ωᶜ * (k + 1) - 1))
  have hdc : ∀ k, Continuous (d k) := fun k => by
    have := Metric.continuous_infDist_pt (Ωᶜ : Set (EuclideanSpace ℝ (Fin n)))
    fun_prop
  have hd01 : ∀ k x, 0 ≤ d k x ∧ d k x ≤ 1 := fun k x =>
    ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
  have hdsupp : ∀ k, tsupport (d k) ⊆ Ω := by
    intro k
    have hsub : Function.support (d k) ⊆ {x | 1 / ((k:ℝ) + 1) ≤ Metric.infDist x Ωᶜ} := by
      intro x hx
      simp only [mem_setOf_eq]
      by_contra hlt
      push_neg at hlt
      apply hx
      have : Metric.infDist x Ωᶜ * (k + 1) - 1 ≤ 0 := by
        rw [lt_div_iff₀ (by positivity)] at hlt
        linarith
      simp only [max_eq_left this, zero_le_one, inf_of_le_right, d]
    have hcl : IsClosed {x : EuclideanSpace ℝ (Fin n) | 1 / ((k:ℝ) + 1) ≤ Metric.infDist x Ωᶜ} :=
      isClosed_le continuous_const (Metric.continuous_infDist_pt _)
    refine (closure_minimal hsub hcl).trans ?_
    intro x hx
    by_contra hxΩ
    have h0 : Metric.infDist x Ωᶜ = 0 := Metric.infDist_zero_of_mem hxΩ
    simp only [mem_setOf_eq, h0] at hx
    have : (0:ℝ) < 1 / ((k:ℝ) + 1) := by positivity
    linarith
  have hlim : ∀ x, ∀ᶠ k in Filter.atTop, F x * (1 - d k x) = 0 := by
    intro x
    by_cases hx : x ∈ Ω
    · have hpos : 0 < Metric.infDist x Ωᶜ := by
        refine (Metric.infDist_pos_iff_notMem_closure hne).mp ?_
        rw [hΩ.isClosed_compl.closure_eq]
        simpa only [mem_compl_iff, not_not] using hx
      have hob3 := exists_nat_gt (2 / Metric.infDist x Ωᶜ)
      obtain ⟨N, hN⟩ := hob3
      filter_upwards [Filter.eventually_ge_atTop N] with k hk
      have hk' : (2 / Metric.infDist x Ωᶜ) < (k:ℝ) + 1 := by
        have : (N:ℝ) ≤ k := by exact_mod_cast hk
        linarith
      have h2 : 1 ≤ Metric.infDist x Ωᶜ * (k + 1) - 1 := by
        rw [div_lt_iff₀ hpos] at hk'; nlinarith
      have : d k x = 1 := by
        simp only [d]
        rw [max_eq_right (by linarith), min_eq_left h2]
      rw [this]; ring
    · exact Filter.Eventually.of_forall fun k => by rw [hF0 x hx, zero_mul]
  have hT := tendsto_eLpNorm_cutoff hF (c := fun k x => 1 - d k x)
    (fun k => continuous_const.sub (hdc k))
    (fun k x => by rw [abs_le]; constructor <;> linarith [hd01 k x]) hlim
  have hob4 := (hT.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε2))).exists
  obtain ⟨k, hk⟩ := hob4
  refine ⟨fun x => g x * d k x, hgcont.mul (hdc k), hgc.mul_right, ?_, ?_⟩
  · exact (tsupport_mul_subset_right).trans (hdsupp k)
  · have hsplit : (F - fun x => g x * d k x) =
        (fun x => F x * (1 - d k x)) + (fun x => (F x - g x) * d k x) := by
      funext x; simp only [Pi.sub_apply, Pi.add_apply]; ring
    rw [hsplit]
    refine (eLpNorm_add_le ?_ ?_ (by norm_num)).trans ?_
    · exact hF.1.mul (continuous_const.sub (hdc k)).aestronglyMeasurable
    · exact (hF.1.sub hgcont.aestronglyMeasurable).mul (hdc k).aestronglyMeasurable
    · have h2 : eLpNorm (fun x => (F x - g x) * d k x) 2 volume ≤ eLpNorm (F - g) 2 volume := by
        refine eLpNorm_mono fun x => ?_
        rw [norm_mul, Pi.sub_apply]
        calc ‖F x - g x‖ * ‖d k x‖ ≤ ‖F x - g x‖ * 1 := by
              gcongr
              rw [Real.norm_eq_abs, abs_of_nonneg (hd01 k x).1]; exact (hd01 k x).2
          _ = ‖F x - g x‖ := mul_one _
      calc eLpNorm (fun x => F x * (1 - d k x)) 2 volume + eLpNorm (fun x => (F x - g x) * d k x) 2 volume
          ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hk.le (h2.trans hgF)
        _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add hε2.le hε2.le]; ring_nf

/-- The jet of a test function, as an element of `H¹₀`. -/
lemma jet_mem {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφt : tsupport φ ⊆ Ω) :
    ∃ u : H10 n Ω, (toL2L n Ω u : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume.restrict Ω] φ := by
  have hcont : Continuous (fun x => WithLp.toLp 2 (φ x, gradient φ x) : _ → Jet n) := by
    have hg : Continuous (gradient φ) := by
      have := hφ.continuous_fderiv (by simp only [ne_eq, WithTop.coe_eq_zero, ENat.top_ne_zero, not_false_eq_true])
      exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp this
    exact (WithLp.prod_continuous_toLp 2 ℝ (EuclideanSpace ℝ (Fin n))).comp (hφ.continuous.prodMk hg)
  have hsupp : HasCompactSupport (fun x => WithLp.toLp 2 (φ x, gradient φ x) : _ → Jet n) := by
    refine hφc.mono' ?_
    intro x hx
    by_contra h
    apply hx
    have h1 : φ x = 0 := image_eq_zero_of_notMem_tsupport h
    have h2 : gradient φ x = 0 := by simp only [gradient, fderiv_of_notMem_tsupport ℝ h, map_zero]
    simp only [h1, h2, WithLp.toLp_eq_zero, Prod.mk_eq_zero, and_self]
  have hm : MemLp (fun x => WithLp.toLp 2 (φ x, gradient φ x) : _ → Jet n) 2 (volume.restrict Ω) :=
    (hcont.memLp_of_hasCompactSupport hsupp).restrict _
  have hJ : hm.toLp ∈ H10 n Ω :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨φ, hφ, hφc, hφt, hm.coeFn_toLp⟩)
  refine ⟨⟨hm.toLp, hJ⟩, ?_⟩
  have h1 := ContinuousLinearMap.coeFn_compLp (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n)))
    (hm.toLp)
  filter_upwards [h1, hm.coeFn_toLp] with x hx1 hx2
  have : (toL2L n Ω ⟨hm.toLp, hJ⟩ : _ → ℝ) x = (WithLp.ofLp ((hm.toLp : _ → Jet n) x)).1 := hx1
  rw [this, hx2]

/-- (H3) `C_c^∞(Ω)` (hence `H¹₀`) is dense in `L²(Ω)`. -/
lemma toL2L_denseRange (hΩ : IsOpen Ω) : DenseRange (toL2L n Ω) := by
  rw [Metric.denseRange_iff]
  intro f r hr
  set F : EuclideanSpace ℝ (Fin n) → ℝ := Ω.indicator (f : _ → ℝ) with hFdef
  have hF : MemLp F 2 volume :=
    (memLp_indicator_iff_restrict hΩ.measurableSet).mpr (Lp.memLp f)
  have hF0 : ∀ x, x ∉ Ω → F x = 0 := fun x hx => indicator_of_notMem hx _
  have hr3 : 0 < r / 3 := by linarith
  have hob5 := exists_cont_approx hΩ hF hF0 hr3
  obtain ⟨g, hgcont, hgc, hgt, hFg⟩ := hob5
  have hob6 := smooth_approx_supp hgc hgcont hr3
  obtain ⟨φ, hφ, hφc, hφt, hgφ⟩ := hob6
  have hob7 := jet_mem hφ hφc (hφt.trans hgt)
  obtain ⟨u, hu⟩ := hob7
  refine ⟨u, ?_⟩
  rw [Lp.dist_def]
  have hfF : (f : _ → ℝ) =ᵐ[volume.restrict Ω] F := by
    rw [hFdef]; exact (indicator_ae_eq_restrict hΩ.measurableSet).symm
  have h1 : eLpNorm (⇑f - ⇑(toL2L n Ω u)) 2 (volume.restrict Ω) ≤ eLpNorm (F - φ) 2 volume := by
    have : (⇑f - ⇑(toL2L n Ω u)) =ᵐ[volume.restrict Ω] (F - φ) := by
      filter_upwards [hfF, hu] with x h1 h2
      simp only [Pi.sub_apply, h1, h2]
    rw [eLpNorm_congr_ae this]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have h2 : eLpNorm (F - φ) 2 volume ≤ ENNReal.ofReal (2 * (r / 3)) := by
    have hs : F - φ = (F - g) + (g - φ) := by funext x; simp only [Pi.sub_apply, Pi.add_apply, sub_add_sub_cancel]
    rw [hs]
    refine (eLpNorm_add_le (hF.1.sub hgcont.aestronglyMeasurable)
      (hgcont.aestronglyMeasurable.sub hφ.continuous.aestronglyMeasurable) (by norm_num)).trans ?_
    rw [two_mul, ENNReal.ofReal_add hr3.le hr3.le]
    exact add_le_add hFg hgφ
  calc (eLpNorm (⇑f - ⇑(toL2L n Ω u)) 2 (volume.restrict Ω)).toReal
      ≤ (ENNReal.ofReal (2 * (r / 3))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (h1.trans h2)
    _ < r := by rw [ENNReal.toReal_ofReal (by positivity)]; linarith

lemma l2Dual_injective (hΩ : IsOpen Ω) : Function.Injective (l2Dual n Ω) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have h : ∀ v : H10 n Ω, inner ℝ f (toL2L n Ω v) = 0 := fun v => by
    rw [← l2Dual_apply, hf]; rfl
  have hc : ∀ g ∈ closure (range (toL2L n Ω)), inner ℝ f g = 0 := by
    intro g hg
    have hcl : IsClosed {g : Lp ℝ 2 (volume.restrict Ω) | inner ℝ f g = 0} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    exact hcl.closure_subset_iff.mpr (by rintro _ ⟨v, rfl⟩; exact h v) hg
  have := hc f (by rw [(toL2L_denseRange hΩ).closure_range]; trivial)
  exact inner_self_eq_zero.mp this

/-- (H4) `L²(Ω)` is dense in `H⁻¹(Ω)` (via the Riesz isomorphism of `H¹₀`). -/
lemma l2Dual_denseRange (hΩ : IsOpen Ω) : DenseRange (l2Dual n Ω) := by
  set R := InnerProductSpace.toDual ℝ (H10 n Ω) with hR
  let Kp : Submodule ℝ (H10 n Ω) :=
    { carrier := range (fun f => R.symm (l2Dual n Ω f))
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a + b, by simp only [map_add]⟩
      zero_mem' := ⟨0, by simp only [map_zero]⟩
      smul_mem' := by
        rintro c _ ⟨a, rfl⟩
        refine ⟨c • a, ?_⟩
        simp only [map_smul, map_smulₛₗ, starRingEnd_apply, star_trivial] }
  have hperp : Kpᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    have h1 := (Submodule.mem_orthogonal _ _).mp hw (R.symm (l2Dual n Ω (toL2L n Ω w))) ⟨_, rfl⟩
    rw [InnerProductSpace.toDual_symm_apply, l2Dual_apply, real_inner_self_eq_norm_sq] at h1
    have h2 : toL2L n Ω w = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
      exact norm_eq_zero.mp this
    exact toL2L_injective hΩ (by rw [h2, map_zero])
  have hd : DenseRange (fun f => R.symm (l2Dual n Ω f)) := by
    have := (Submodule.topologicalClosure_eq_top_iff (K := Kp)).mpr hperp
    exact (Submodule.dense_iff_topologicalClosure_eq_top (s := Kp)).mpr this
  have hfun : (l2Dual n Ω : Lp ℝ 2 (volume.restrict Ω) → Hm1 n Ω) =
      R ∘ (fun f => R.symm (l2Dual n Ω f)) := by
    funext f; simp only [Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [DenseRange, hfun]
  exact (R.surjective.denseRange).comp hd R.continuous

instance fact_two_ne_top : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

instance : TopologicalSpace.SeparableSpace (Jet n) := by
  haveI : ProperSpace (Jet n) := FiniteDimensional.proper ℝ _
  infer_instance

end ht

section b1
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}



/-! ## Components of `H¹₀` elements as `L²` functions -/

/-! ## Time sections of coefficients on the cylinder -/

/-! ## The form at a good time -/

section good
variable {P : Coeffs n} {θ M t : ℝ}

end good

/-! ## Measurability of the form in time -/

end b1

section b2
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}


/-! ## `L²` inner product, coordinates and the Galerkin space -/

section orth
variable {w : ℕ → H10 n Ω}

end orth


end b2

end HunterPDE.Parabolic
end Q0ffd_L0

section Q0ffd_W
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section weak
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

end weak

section linf
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

end linf

section lpfun
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {μ : Measure ℝ}

end lpfun
end HunterPDE.Parabolic
end Q0ffd_W

section Q0ffd_R
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section riesz
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

variable {V}

end riesz

section eval
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

end eval

section wtd
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

end wtd

end HunterPDE.Parabolic
end Q0ffd_R

section Q0ffd_R2
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section r2

end r2
end HunterPDE.Parabolic
end Q0ffd_R2

section Q0ffd_F
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section F
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

section lam
variable {T : ℝ} {P : Coeffs n} {θ M : ℝ}

end lam

end F
end HunterPDE.Parabolic
end Q0ffd_F

section Q0ffd_D
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section D
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

end D
end HunterPDE.Parabolic
end Q0ffd_D

section Q0ffd_D2
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section D2
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

end D2
end HunterPDE.Parabolic
end Q0ffd_D2

section Q0ffd_P1
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section limit
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {T : ℝ}

end limit
end HunterPDE.Parabolic
end Q0ffd_P1

section Q0ffd_P2
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section eqn
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {T : ℝ}

end eqn
end HunterPDE.Parabolic
end Q0ffd_P2

section Q0ffd_P3
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section ibp
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {T : ℝ}

end ibp
end HunterPDE.Parabolic
end Q0ffd_P3

section Q0ffd_P4
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section init
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {T : ℝ}

end init
end HunterPDE.Parabolic
end Q0ffd_P4

section Q0ffd_P5
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section est

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {T : ℝ}

end est
end HunterPDE.Parabolic
end Q0ffd_P5

section Q0ffd_A
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff
namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast
section asm

end asm
end HunterPDE.Parabolic
end Q0ffd_A


open MeasureTheory HunterPDE.Parabolic in
theorem solution {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) :
    Function.Injective (toL2L n Ω) ∧ DenseRange (toL2L n Ω) ∧
      Function.Injective (fun f : Lp ℝ 2 (volume.restrict Ω) => (innerSL ℝ f).comp (toL2L n Ω)) ∧
      DenseRange (fun f : Lp ℝ 2 (volume.restrict Ω) => (innerSL ℝ f).comp (toL2L n Ω)) :=
  ⟨toL2L_injective hΩ, toL2L_denseRange hΩ, l2Dual_injective hΩ, l2Dual_denseRange hΩ⟩
