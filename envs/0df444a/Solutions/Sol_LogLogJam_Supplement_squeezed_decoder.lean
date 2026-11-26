-- Prove2me | solution 1 for LogLogJam.Supplement.squeezed_decoder
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T19:14:42.275655+00:00
-- url     : https://prove2.me/submissions/ae71200d-69f2-49c9-a2e3-79b9485b7e61

import Theorems.Thm_LogLogJam_Supplement_squeezed_fock_realization
import Theorems.Thm_LogLogJam_Supplement_squeezed_trace_distance
import Definitions.Def_LogLogJam_Supplement_phaseCountReadouts
import Theorems.Thm_BosonicLearn_state_ext_characteristic
import Theorems.Thm_BosonicLearn_traceDist_triangle

open Matrix MeasureTheory Filter LogLogJam LogLogJam.Supplement BosonicLearn
open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ComplexOrder ENNReal Topology Matrix

private theorem disk_norm {K : Matrix (Fin 1) (Fin 1) ℂ} (hK : InSiegelDisk K) : ‖K 0 0‖ < 1 := by
  have h := (Complex.pos_iff.mp (hK.2.diag_pos (i:=0))).1
  simp [Matrix.mul_apply, Complex.mul_conj, ← Complex.sq_norm, ← Complex.ofReal_pow] at h
  nlinarith [norm_nonneg (K 0 0)]

private theorem disk_coords {K : Matrix (Fin 1) (Fin 1) ℂ} (hK : InSiegelDisk K) :
    ∃ r θ : ℝ, 0 ≤ r ∧ K = Matrix.of (fun _ _ : Fin 1 => (Real.tanh r : ℂ) * Complex.exp ((2*θ : ℝ)*Complex.I)) := by
  let z := K 0 0
  have hz : ‖z‖ < 1 := disk_norm hK
  refine ⟨Real.artanh ‖z‖, z.arg/2, Real.artanh_nonneg (norm_nonneg _), ?_⟩
  ext a b; fin_cases a; fin_cases b
  change z = (Real.tanh (Real.artanh ‖z‖) : ℂ) * Complex.exp ((2*(z.arg/2) : ℝ)*Complex.I)
  rw [Real.tanh_artanh ⟨by linarith [norm_nonneg z],hz⟩, show 2*(z.arg/2) = z.arg by ring]
  exact (Complex.norm_mul_exp_arg_mul_I _).symm

private theorem coords_disk (r θ : ℝ) : InSiegelDisk (Matrix.of (fun _ _ : Fin 1 =>
    (Real.tanh r : ℂ) * Complex.exp ((2*θ : ℝ)*Complex.I))) := by
  let z := (Real.tanh r : ℂ) * Complex.exp ((2*θ : ℝ)*Complex.I)
  let K : Matrix (Fin 1) (Fin 1) ℂ := Matrix.of (fun _ _ => z)
  change Kᵀ = K ∧ (1-K*Kᴴ).PosDef
  have hn : ‖z‖ < 1 := by
    dsimp [z]; rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact abs_lt.mpr ⟨Real.neg_one_lt_tanh _,Real.tanh_lt_one _⟩
  have h : 1 - K * Kᴴ = diagonal (fun _ => (((1:ℝ) - ‖z‖^2 : ℝ) : ℂ)) := by
    ext i j; fin_cases i; fin_cases j
    simp [K,Matrix.mul_apply,Complex.mul_conj,Complex.sq_norm,← Complex.ofReal_pow]
  refine ⟨rfl,h ▸ Matrix.PosDef.diagonal ?_⟩
  intro i; apply Complex.pos_iff.mpr
  constructor <;> simp [← Complex.ofReal_pow]
  nlinarith [norm_nonneg z]

private theorem covered (ρ : State (Occupation (Fin 1))) (hρ : IsPureCentGauss ρ) : ∃ r θ : ℝ, squeezedAt ρ r θ := by
  obtain ⟨K,hK,hg⟩ := hρ
  obtain ⟨r, θ, hr, rfl⟩ := disk_coords hK
  exact ⟨r,θ,hr,hg⟩

private theorem unique {ρ σ : State (Occupation (Fin 1))} {r θ : ℝ} (hρ : squeezedAt ρ r θ)
    (hσ : squeezedAt σ r θ) : ρ = σ := by
  have h := state_ext_characteristic ρ σ (fun ξ => (hρ.2.2 ξ).trans (hσ.2.2 ξ).symm)
  cases ρ; cases σ; congr
private theorem rot_det (θ : ℝ) : (rot θ).det = 1 := by
  simp [rot,det_fin_two, ← sq, Real.cos_sq_add_sin_sq]

private theorem covariance_pos (r θ : ℝ) : (Vsq (Real.exp (2*r)) θ).PosDef := by
  have hrot : IsUnit (rot θ) := (isUnit_iff_isUnit_det _).mpr (by simp [rot_det])
  have hdiag : (diagonal ![Real.exp (2*r),(Real.exp (2*r))⁻¹]).PosDef := by
    apply PosDef.diagonal; intro i; fin_cases i <;> simp <;> positivity
  have he : diagonal ![Real.exp (2*r),(Real.exp (2*r))⁻¹] = !![Real.exp (2*r),0;0,(Real.exp (2*r))⁻¹] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  simpa [Vsq, he, conjTranspose_eq_transpose_of_trivial] using
    (hdiag.mul_mul_conjTranspose_same (B := rot θ) (vecMul_injective_of_isUnit hrot))

private noncomputable def vdist (x y : ℝ × ℝ) := Real.sqrt (1-2/Real.sqrt
    (Vsq (Real.exp (2*x.1)) x.2 + Vsq (Real.exp (2*y.1)) y.2).det)

private theorem diag_sum (r s θ : ℝ) :
    (Vsq (Real.exp (2*r)) θ + Vsq (Real.exp (2*s)) θ).det = 4 * Real.cosh (s-r)^2 := by
  have e : Vsq (Real.exp (2*r)) θ + Vsq (Real.exp (2*s)) θ =
      rot θ * (!![Real.exp (2*r),0;0,(Real.exp (2*r))⁻¹] + !![Real.exp (2*s),0;0,(Real.exp (2*s))⁻¹]) * (rot θ)ᵀ := by simp only [Vsq,mul_add,add_mul]
  rw [e,det_mul,det_mul,det_transpose,rot_det,one_mul,mul_one,det_fin_two]
  simp [Real.cosh_eq, Real.exp_sub,Real.exp_neg,show 2*r=r+r by ring,show 2*s=s+s by ring,Real.exp_add]
  field_simp; ring

private theorem rad (r s θ : ℝ) : vdist (r,θ) (s,θ) = Real.sqrt (1 - 1/Real.cosh (s-r)) := by
  simp only [vdist,diag_sum,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),Real.sqrt_sq (Real.cosh_pos _).le]
  congr 2; norm_num; field_simp

private theorem vdist_self (x : ℝ × ℝ) : vdist x x = 0 := by
  rcases x with ⟨r,θ⟩; simp [rad]

private theorem vcont (y : ℝ × ℝ) : Continuous (fun x : ℝ × ℝ => vdist x y) := by
  have hc : Continuous fun x : ℝ × ℝ => Vsq (Real.exp (2*x.1)) x.2 := by
    apply continuous_pi; intro i;apply continuous_pi; intro j
    fin_cases i <;> fin_cases j <;> simp [Vsq,rot,vecMul,dotProduct,Fin.sum_univ_two,← Real.exp_neg] <;> fun_prop
  have hp (x : ℝ × ℝ) : 0 < (Vsq (Real.exp (2*x.1)) x.2 + Vsq (Real.exp (2*y.1)) y.2).det :=
    ((covariance_pos _ _).add (covariance_pos _ _)).det_pos
  exact Real.continuous_sqrt.comp (continuous_const.sub (continuous_const.div
    (Real.continuous_sqrt.comp (hc.add continuous_const).matrix_det) (fun x => (Real.sqrt_pos.mpr (hp x)).ne')))

private theorem decoder_cont (D : ℝ × ℝ → State (Occupation (Fin 1))) (f : ℝ × ℝ → ℝ × ℝ)
    (hf : Continuous f) (hd : ∀ x y, traceDist (D x).coefficients (D y).coefficients = ENNReal.ofReal (vdist (f x) (f y))) :
    Continuous D := by
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨σ,ε,hε,rfl⟩
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  change traceSize ((D x).coefficients - σ.coefficients) < ENNReal.ofReal ε at hx
  let distance (y) := traceDist (D y).coefficients σ.coefficients
  have hm (y) : distance y * 2 = traceSize ((D y).coefficients - σ.coefficients) := by
    unfold distance traceDist; exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)
  rw [← hm] at hx
  have hlim : Tendsto (fun y => (ENNReal.ofReal (vdist (f y) (f x)) + distance x)*2) (𝓝 x) (𝓝 ((0 + distance x)*2)) := by
    have h0 := (ENNReal.continuous_ofReal.comp ((vcont (f x)).comp hf)).continuousAt (x := x)
    have h0' : Tendsto (fun y => ENNReal.ofReal (vdist (f y) (f x))) (𝓝 x) (𝓝 0) := by simpa [Function.comp_def,vdist_self] using h0.tendsto
    exact (ENNReal.continuous_mul_const (a:=2) (by norm_num)).continuousAt.tendsto.comp (h0'.add (tendsto_const_nhds (x:=distance x)))
  filter_upwards [hlim.eventually_lt_const (by simpa using hx)] with y hy
  change traceSize ((D y).coefficients - σ.coefficients) < _
  rw [← hm]; apply lt_of_le_of_lt _ hy
  apply mul_le_mul' _ le_rfl
  rw [← hd]; exact traceDist_triangle _ _ _

theorem solution :
    ∃ D : ℝ × ℝ → State (Occupation (Fin 1)), Measurable D ∧
    (∀ r θ : ℝ, 0 ≤ r → squeezedAt (D (r, θ)) r θ ∧ IsPureCentGauss (D (r, θ))) ∧
    (∀ ρ : State (Occupation (Fin 1)), IsPureCentGauss ρ → ∃ r θ : ℝ, 0 ≤ r ∧ D (r, θ) = ρ) ∧
    (∀ r θ φ : ℝ, 0 ≤ r → BosonicLearn.traceDist (D (r, θ)).coefficients (D (r, φ)).coefficients =
      ENNReal.ofReal (LogLogJam.trDist (Real.exp (2 * r)) θ φ)) ∧
    (∀ r s θ : ℝ, 0 ≤ r → 0 ≤ s →
      BosonicLearn.traceDist (D (r, θ)).coefficients (D (s, θ)).coefficients =
        ENNReal.ofReal (Real.sqrt (1 - 1 / Real.cosh (s - r)))) := by
  let f (x : ℝ × ℝ) : ℝ × ℝ := (max x.1 0,x.2)
  have hf : Continuous f := (continuous_fst.max continuous_const).prodMk continuous_snd
  have hex (x : ℝ × ℝ) : ∃ ρ : State (Occupation (Fin 1)), squeezedAt ρ (f x).1 (f x).2 := by
    obtain ⟨ρ,hρ,_⟩ := squeezed_fock_realization _ x.2 (le_max_right x.1 0)
    exact ⟨ρ,hρ⟩
  let D := fun x => (hex x).choose
  have hD (x) : squeezedAt (D x) (f x).1 (f x).2 := (hex x).choose_spec
  have hd (x y) : traceDist (D x).coefficients (D y).coefficients = ENNReal.ofReal (vdist (f x) (f y)) :=
    squeezed_trace_distance _ _ _ _ _ _ (hD x) (hD y)
  refine ⟨D,(decoder_cont D f hf hd).measurable,?_,?_,?_,?_⟩
  · intro r θ hr
    have h : squeezedAt (D (r,θ)) r θ := by simpa [f,max_eq_left hr] using hD (r,θ)
    exact ⟨h,_,coords_disk _ _,h.2⟩
  · intro ρ hρ; obtain ⟨r,θ,h⟩ := covered ρ hρ
    refine ⟨r,θ,h.1,unique ?_ h⟩; simpa [f,max_eq_left h.1] using hD (r,θ)
  · intro r θ φ hr; simpa [f,max_eq_left hr,vdist,trDist] using hd (r,θ) (r,φ)
  · intro r s θ hr hs; simpa [f,max_eq_left hr,max_eq_left hs,rad] using hd (r,θ) (s,θ)
