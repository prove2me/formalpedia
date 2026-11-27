-- Prove2me | solution 1 for MasulloRH.rational_frequency_modulations_span_a_nonvanishing_L2_weight
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T04:02:43.818671+00:00
-- url     : https://prove2.me/submissions/eae7e98d-624e-419d-9cd3-2b40cb3cb7c2

import Definitions.Def_MasulloRH_VerticalThetaApproximation
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap ComplexConjugate
open MasulloRH.RationalThetaGrid MasulloRH.VerticalThetaApproximation

private theorem fourierUniqueness {u : ℝ → ℂ} (hu : Integrable u) (hzero : 𝓕 u = 0) :
    ∀ᵐ x : ℝ, u x = 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hu.locallyIntegrable
  intro g hgd hgc
  let φ := (hgc.comp_left (show Complex.ofRealCLM 0 = 0 from rfl)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hgd)
  let ψ : 𝓢(ℝ,ℂ) := 𝓕⁻ φ
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner (ψ.integrable (μ := volume)) hu
  have hi : (∫ x : ℝ, (𝓕 ψ) x • u x) = ∫ x : ℝ, ψ x • 𝓕 u x := by
    simpa only [SchwartzMap.fourier_coe, flip_innerₗ] using! h
  have hp : 𝓕 ψ = φ := FourierTransform.fourier_fourierInv_eq φ
  rw [hp,hzero] at hi
  simpa [φ,Complex.real_smul] using hi

private theorem rationalComplexDense : DenseRange asComplex := by
  let e := Complex.equivRealProdCLM.symm
  have h := e.surjective.denseRange.comp
    ((Rat.denseRange_cast (𝕜:=ℝ)).prodMap (Rat.denseRange_cast (𝕜:=ℝ))) e.continuous
  convert h using 1
  funext z
  simp [asComplex,e,Complex.equivRealProdCLM_symm_apply]

private theorem squaredNorm (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∫ t : ℝ, ‖f t‖^2 = ‖f‖^2 := by
  have h := congrArg (RCLike.re (K:=ℂ)) (L2.inner_def (𝕜:=ℂ) f f)
  rw [← integral_re (L2.integrable_inner (𝕜:=ℂ) f f)] at h
  simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using h.symm

theorem solution (c : ℝ) (A H : ℝ → ℂ) (hA : MemLp A 2) (hH : MemLp H 2)
    (hn : ∀ᵐ t : ℝ, H t ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      (∫ t : ℝ, ‖A t - H t * ∑ i, asComplex (a i) * Complex.exp (pointAt c t * (y i : ℝ))‖^2) < ε := by
  classical
  let E := Lp ℂ 2 (volume : Measure ℝ)
  let phase := fun (y : ℚ) (t : ℝ) => Complex.exp (((t*(y:ℝ):ℝ):ℂ)*Complex.I)
  have hnPhase (y : ℚ) (t : ℝ) : ‖phase y t‖=1 := by simp [phase, Complex.norm_exp]
  have hP (y : ℚ) : MemLp (fun t : ℝ => phase y t * H t) 2 := by
    apply hH.of_le_mul (c:=1)
    · exact (show Continuous (phase y) by dsimp [phase]; fun_prop).aestronglyMeasurable.mul hH.1
    · exact Eventually.of_forall fun t => by rw [norm_mul,hnPhase]
  let V := fun y : ℚ => (hP y).toLp (fun t => phase y t * H t)
  let M := Submodule.span ℂ (Set.range V)
  have denseM : M.topologicalClosure = ⊤ := by
    apply M.topologicalClosure_eq_top_iff.mpr
    apply le_antisymm _ bot_le
    intro g hg
    let u := fun t : ℝ => conj (H t) * g t
    have hu : Integrable u := by
      apply (L2.integrable_inner (𝕜:=ℂ) (hH.toLp H) g).congr
      filter_upwards [hH.coeFn_toLp] with t ht
      rw [RCLike.inner_apply',ht]
    have hq (y : ℚ) : 𝓕 u ((y:ℝ)/(2*Real.pi)) = 0 := by
      have innerzero := (Submodule.mem_orthogonal M g).mp hg (V y)
        (Submodule.subset_span (Set.mem_range_self _))
      rw [L2.inner_def] at innerzero
      rw [Real.fourier_real_eq_integral_exp_smul]
      refine Eq.trans (integral_congr_ae ?_) innerzero
      filter_upwards [(hP y).coeFn_toLp] with t ht
      change (V y) t = _ at ht
      rw [RCLike.inner_apply',ht]
      simp only [u, phase, smul_eq_mul, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
        Complex.conj_I]
      rw [show -2*Real.pi*t*((y:ℝ)/(2*Real.pi)) = -(t*(y:ℝ)) by field_simp]
      push_cast
      ring
    have hcont : Continuous (𝓕 u) := VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (innerSL ℝ).continuous₂ hu
    have hall : (fun x : ℝ => 𝓕 u (x/(2*Real.pi))) = 0 :=
      (Rat.denseRange_cast (𝕜:=ℝ)).equalizer (hcont.comp (continuous_id.div_const _))
        continuous_const (funext hq)
    have hf : 𝓕 u = 0 := by
      funext t
      have h := congrFun hall (t*(2*Real.pi))
      simpa [(Real.pi_pos).ne'] using h
    change g = 0
    apply Lp.ext
    filter_upwards [fourierUniqueness hu hf, hn, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with t h hne h0
    rw [h0]
    exact (mul_eq_zero.mp h).resolve_left (by simpa using hne)
  let v := hA.toLp A
  have hv : v ∈ M.topologicalClosure := by rw [denseM]; trivial
  rw [← SetLike.mem_coe,Submodule.topologicalClosure_coe,Metric.mem_closure_iff] at hv
  obtain ⟨w,hw,hnear⟩ := hv (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  obtain ⟨m,b,z,he⟩ := (Submodule.mem_span_set' (R:=ℂ)).mp hw
  choose y hy using fun i : Fin m => (z i).prop
  have e (i : Fin m) : V (y i) = (z i).val := hy i
  let B := fun i => (Real.exp (c*(y i:ℝ)) : ℂ)
  let f := fun b' : Fin m → ℂ => ∑ i, (b' i * B i) • V (y i)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hnon : ∃ b' : Fin m → ℂ, dist v (f b') < Real.sqrt ε := by
    refine ⟨fun i => b i / B i,?_⟩
    have hB (i : Fin m) : B i ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
    simpa only [f,div_mul_cancel₀ _ (hB _),e,he] using hnear
  have hdense : DenseRange (fun a : Fin m → ℚ×ℚ => fun i => asComplex (a i)) :=
    DenseRange.piMap (fun _ => rationalComplexDense)
  obtain ⟨a,ha⟩ := hdense.exists_mem_open (isOpen_lt (continuous_const.dist hf) continuous_const) hnon
  let v' := f (fun i => asComplex (a i))
  change dist v v' < Real.sqrt ε at ha
  refine ⟨m,a,y,?_⟩
  have hc (i : Fin m) : ∀ᵐ t : ℝ,
      (((asComplex (a i)*B i) • V (y i) : E) t) =
        (asComplex (a i)*B i) * (phase (y i) t * H t) := by
    filter_upwards [Lp.coeFn_smul (asComplex (a i)*B i) (V (y i)),(hP (y i)).coeFn_toLp] with t h h'
    change (V (y i)) t = _ at h'
    simpa only [Pi.smul_apply,smul_eq_mul,h'] using h
  have hz : ∀ᵐ t : ℝ, (v-v') t = A t - H t*∑ i, asComplex (a i)*Complex.exp (pointAt c t*(y i:ℝ)) := by
    filter_upwards [Lp.coeFn_sub v v', hA.coeFn_toLp, Lp.coeFn_finsetSum Finset.univ
      (fun i => (asComplex (a i)*B i) • V (y i)),eventually_all.mpr hc] with t h hv' hsum hh
    change v t = _ at hv'
    change v' t = _ at hsum
    simp only [Pi.sub_apply] at h
    rw [h,hv',hsum,Finset.sum_apply,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hh i]
    have et : Complex.exp (pointAt c t*(y i:ℝ)) = B i*phase (y i) t := by
      simp only [pointAt,B,phase,Complex.ofReal_exp,Complex.ofReal_mul,← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [et]
    ring
  calc
    _ = ∫ t : ℝ, ‖(v-v') t‖^2 := integral_congr_ae (hz.mono fun t h => congrArg (fun z : ℂ => ‖z‖^2) h.symm)
    _ = ‖v-v'‖^2 := squaredNorm _
    _ < ε := by have := Real.sq_sqrt hε.le; rw [dist_eq_norm] at ha; nlinarith [norm_nonneg (v-v'),Real.sqrt_nonneg ε]
