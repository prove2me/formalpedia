-- Prove2me | solution 1 for NoHair.TwoCentre.Model.closed_causal_diamonds
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T23:14:42.565992+00:00
-- url     : https://prove2.me/submissions/7d2ea42f-627d-4e8f-a861-69b5074ef399

import Definitions.Def_NoHair_PseudoRiemannianNormalCoordinates
import Definitions.Def_NoHair_TwoCentreIsotropic
import Definitions.Def_NoHair_kerrNewman
import Theorems.Thm_NoHair_TwoCentre_optical_confinement
import Theorems.Thm_NoHair_TwoCentre_Cartesian_exterior_and_frontier
import Theorems.Thm_NoHair_TwoCentre_Model_stationary_geometry
/-! The local normal-coordinate and causal-curve arguments adapt the verified Kerr–Newman exterior proofs
https://prove2.me/submissions/9d1adb05-dffe-4969-a064-d9b960def90e ,
https://prove2.me/submissions/48ff4c37-9c26-46c2-afe7-dd0e96ce0729 and
https://prove2.me/theorems/46e8d6cc-84d5-4d89-a5cb-f8bb00226bd7 to the two-centre isotropic metric. -/

open NoHair NoHair.TwoCentre Set Filter
open OAI.WeakMTWGlobalSupport OAI.WeakMTWGlobalSupport.CoordinateGeometry
open OAI.WeakMTWGlobalSupport.NormalNeighborhood NoHair.PseudoNormal
open scoped ContDiff Manifold BigOperators Topology
namespace NoHair.TwoCentre.StaticCausality
noncomputable section

theorem openS : IsOpen exterior := by
  have h (c : ℝ) : Continuous (squaredDistance c) := by unfold squaredDistance;fun_prop
  exact (isOpen_lt continuous_const (h (-1))).inter (isOpen_lt continuous_const (h 1))
def U : TopologicalSpace.Opens E4 := ⟨exterior,openS⟩
abbrev D := (Subtype.val : U → E4) ⁻¹' exterior
abbrev S := exterior
abbrev I4 := 𝓘(ℝ,E4)
abbrev F (z : E4) := matrixBilin (isotropicMetric z)
abbrev G : BilinField U := fun z => F z.val
def timeComponent (v:E4) := v 0
theorem inU {z:E4} (h:z∈S) : z∈U := h
theorem metric_formula (x : U) (v w : E4) : G x v w =
    -(v 0*w 0)/harmonicPotential x.val^2 + harmonicPotential x.val^2*(v 1*w 1+v 2*w 2+v 3*w 3) := by
  change Matrix.toLinearMap₂' ℝ (isotropicMetric x.val) (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp (config := {decide := true}) [Matrix.toLinearMap₂'_apply,smul_eq_mul,isotropicMetric,Matrix.diagonal,Fin.sum_univ_four]
  ring
theorem U_ge (y:E4) : 1 ≤ harmonicPotential y := by
  unfold harmonicPotential inverseDistance
  linarith [one_div_nonneg.mpr (Real.sqrt_nonneg (squaredDistance (-1) y)),one_div_nonneg.mpr (Real.sqrt_nonneg (squaredDistance 1 y))]
theorem exterior_profile (x : U) (_ : x∈D) : 1≤harmonicPotential x.val := U_ge x.val
theorem spatial_squares (x:U) (hf:1≤harmonicPotential x.val)
    (v:E4) (h:G x v v≤0) : (v 1)^2+(v 2)^2+(v 3)^2≤(v 0)^2 := by
  rw [metric_formula] at h
  have hu : 0<harmonicPotential x.val := by linarith
  have he : 1≤harmonicPotential x.val^4 := one_le_pow₀ hf
  have hn : 0≤(v 1)^2+(v 2)^2+(v 3)^2 := by positivity
  have hmult := mul_le_mul_of_nonneg_right he hn
  have hh := mul_nonpos_of_nonpos_of_nonneg h (sq_nonneg (harmonicPotential x.val))
  field_simp [hu.ne'] at hh
  nlinarith only [hh,hmult]
theorem spatial_kernel (x:U) (_ : 1≤harmonicPotential x.val) (v:E4) (h0:v 0=0) : 0≤ G x v v := by
  rw [metric_formula,h0]
  simp only [zero_mul,neg_zero,zero_div,zero_add]
  exact mul_nonneg (sq_nonneg _) (by nlinarith [sq_nonneg (v 1),sq_nonneg (v 2),sq_nonneg (v 3)])
theorem cone_estimates  (x : U) (hf : 1 ≤ harmonicPotential x.val)
    (v w : E4) (hv : v ≠ 0) (hvv : G x v v ≤ 0) (hvw : G x v w < 0)
    (hww : G x w w < 0) :
    (∀ i, |v i| ≤ |v 0|) ∧ 0 < (v 0)*(w 0) := by
  have hs := spatial_squares x hf v hvv
  have hb (i : Fin 4) : |v i| ≤ |v 0| := by
    apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
    rw [sq_abs, sq_abs]
    fin_cases i <;> simp <;> nlinarith only [hs, sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
  have hv0 : v 0 ≠ 0 := by
    intro h
    apply hv
    ext i
    exact abs_nonpos_iff.mp (by simpa only [h, abs_zero] using hb i)
  refine ⟨hb, ?_⟩
  by_contra! hprod
  have hkernel := spatial_kernel x hf ((w 0) • v - (v 0) • w)
    (by simp [smul_eq_mul, mul_comm])
  have hsym : G x w v = G x v w := by rw [metric_formula, metric_formula]; ring
  let A := matrixBilin (isotropicMetric x.val)
  change 0 ≤ A ((w 0) • v - (v 0) • w) ((w 0) • v - (v 0) • w) at hkernel
  change A w v = A v w at hsym
  change A w w < 0 at hww
  change A v v ≤ 0 at hvv
  change A v w < 0 at hvw
  simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, hsym] at hkernel
  nlinarith only [hkernel, mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (w 0)) hvv,
    mul_neg_of_pos_of_neg (sq_pos_iff.mpr hv0) hww, mul_nonneg_of_nonpos_of_nonpos hprod hvw.le]

theorem matrix_eval (A : Matrix (Fin 4) (Fin 4) ℝ) (v w : E4) :
    matrixBilin A v w = ∑ i, ∑ j, v i * (w j * A i j) := by
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul]

theorem ambient_velocity  (γ : ℝ → U) (hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ)
    (s : ℝ) (v : E4) (hd : HasDerivAt (fun t => (γ t).val) v s) : (velocity γ s : E4) = v := by
  have hval : ContMDiff I4 I4 1 (Subtype.val : U → E4) := contMDiff_subtype_val
  have hcomp := mfderiv_comp s (hval.mdifferentiableAt (by simp) (x := γ s)) (hγ.mdifferentiableAt (by simp))
  have hinc : (mfderiv I4 I4 (Subtype.val : U → E4) (γ s) : E4 →L[ℝ] E4) =
      ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := γ s)
  rw [hinc] at hcomp
  have h : fderiv ℝ (fun t => (γ t).val) s = (mfderiv 𝓘(ℝ,ℝ) I4 γ s : ℝ →L[ℝ] E4) := by
    rw [← mfderiv_eq_fderiv]
    exact hcomp
  exact (congrArg (fun A : ℝ →L[ℝ] E4 => A 1) h).symm.trans hd.deriv

abbrev J := Icc (0:ℝ) 1

noncomputable def W (T : VecField U) : E4 → E4 :=
  Function.extend (Subtype.val : U → E4) (fun x : U => (T x : E4)) (fun _ => 0)

theorem W_on (T : VecField U) (x : U) : W T x.val = (T x : E4) :=
  Subtype.val_injective.extend_apply _ _ _
  
theorem W_cont  (T : VecField (U)) (hT : IsTimeOrientation (G) T)
    (x : U) : ContinuousAt (W T) x.val := by
  apply (U).isOpen.isOpenEmbedding_subtypeVal.continuousAt_iff.mp
  have h := hT.1.continuousAt (x := x)
  rw [FiberBundle.continuousAt_section] at h
  have htr (y : U) : (trivializationAt E4 (TangentSpace I4) x ⟨y,T y⟩).2 = (T y : E4) := by
    change tangentCoordChange I4 y y y (T y) = _
    exact tangentCoordChange_self (mem_extChartAt_source y)
  change ContinuousAt (fun y : U => W T y.val) x
  rw [show (fun y : U => W T y.val) = (fun y : U => (T y : E4)) from funext (W_on T)]
  simpa only [htr] using h

private theorem smooth_scalar_multiple {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → ℝ} {x : X} (hf : ContDiffAt ℝ ∞ f x) (v : Y) :
    ContDiffAt ℝ ∞ (fun z => f z • v) x := hf.smul_const v

set_option backward.defeqAttrib.useBackward true in
theorem field_smooth   :
    ContDiffOn ℝ ∞ (F) (S) := by
  let P (i : Fin 4) := EuclideanSpace.proj (𝕜:=ℝ) i
  have heP (i : Fin 4) (v : E4) : P i v = v i := rfl
  let B (i j : Fin 4) := (P i).smulRight (P j)
  have he (y : E4) : F y = ∑ i, ∑ j, (isotropicMetric y i j) • B i j := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    simp only [F,matrix_eval,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
      smul_eq_mul,B,ContinuousLinearMap.smulRight_apply,heP]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  intro y hy
  apply ContDiffAt.contDiffWithinAt
  rw [show F = fun z => ∑ i, ∑ j, (isotropicMetric z i j) • B i j from funext he]
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  have hcoeff : ContDiffAt ℝ ∞ (fun z : E4 => isotropicMetric z i j) y := by
    have hc (b:ℝ) : ContDiffAt ℝ ∞ (squaredDistance b) y := by unfold squaredDistance;fun_prop
    have hi (b:ℝ) (h : 0<squaredDistance b y) : ContDiffAt ℝ ∞ (inverseDistance b) y :=
      (contDiffAt_const (c := (1:ℝ))).div ((hc b).sqrt h.ne') (Real.sqrt_pos.mpr h).ne'
    have hu : 0<harmonicPotential y := lt_of_lt_of_le zero_lt_one (U_ge y)
    have hs : ContDiffAt ℝ ∞ harmonicPotential y := ((contDiffAt_const (c := (1:ℝ))).add (hi (-1) hy.1)).add (hi 1 hy.2)
    by_cases eq : i=j
    · subst j;simp only [isotropicMetric,Matrix.diagonal_apply_eq]
      by_cases hz : i=0
      · simp only [hz,if_true];exact ((contDiffAt_const (c := (1:ℝ))).div (hs.pow 2) (pow_ne_zero _ hu.ne')).neg
      · simp only [hz,if_false];exact hs.pow 2
    · simp only [isotropicMetric,Matrix.diagonal_apply_ne _ eq];exact contDiffAt_const
  first
  | exact smooth_scalar_multiple (Y:=MetricTensor E4) hcoeff (B i j)
  | convert! smooth_scalar_multiple (Y:=MetricTensor E4) hcoeff (B i j) using 1
  | let L : ℝ →L[ℝ] MetricTensor E4 := ContinuousLinearMap.toSpanSingleton ℝ (B i j)
    have hL := ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=ℝ) (F:=MetricTensor E4) (n:=∞) L
    exact hL.contDiffAt.comp (f:=fun z : E4 => isotropicMetric z i j) y hcoeff

theorem field_sym   {z : E4}
    (hz : z∈S) (v w : E4) : F z v w=F z w v := by
  let x : U := ⟨z,inU hz⟩
  change G x v w=G x w v
  rw [metric_formula,metric_formula]; ring

theorem field_inv {z:E4} (hz:z∈S) : (F z).IsInvertible := by
  let x : U := ⟨z,hz⟩
  let M := F z
  have hu : 0<harmonicPotential z := lt_of_lt_of_le zero_lt_one (U_ge z)
  have hi : Function.Injective M := by
    apply (injective_iff_map_eq_zero M).mpr
    intro v hv
    have h (j:Fin 4) : G x v (coordBasis j)=0 := congrArg (fun L:E4 →L[ℝ] ℝ => L (coordBasis j)) hv
    ext i
    have he := h i
    rw [metric_formula] at he
    fin_cases i <;> simp (config:={decide:=true}) [coordBasis,x,hu.ne'] at he <;> simpa using he
  have hdim : Module.finrank ℝ E4=Module.finrank ℝ (E4→L[ℝ]ℝ) := (InnerProductSpace.toDual ℝ E4).toLinearEquiv.finrank_eq
  have hs : Function.Surjective M := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi
  exact ⟨ContinuousLinearEquiv.ofBijective M (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs),rfl⟩
theorem nonzero_time   {z v : E4}
    (hz : z∈S) (hn : v≠0) (h : F z v v ≤ 0) : v 0≠0 := by
  let x : U := ⟨z,inU hz⟩
  have hs := spatial_squares x (exterior_profile x hz) v h
  intro h0
  rw [h0] at hs
  apply hn
  ext i
  fin_cases i
  · exact h0
  · change v 1=0
    apply sq_eq_zero_iff.mp
    nlinarith only [hs,sq_nonneg (v 1),sq_nonneg (v 2),sq_nonneg (v 3)]
  · change v 2=0
    apply sq_eq_zero_iff.mp
    nlinarith only [hs,sq_nonneg (v 1),sq_nonneg (v 2),sq_nonneg (v 3)]
  · change v 3=0
    apply sq_eq_zero_iff.mp
    nlinarith only [hs,sq_nonneg (v 1),sq_nonneg (v 2),sq_nonneg (v 3)]

theorem cone_pair_negative  
    {z v w : E4} (hz : z∈S) (hvv : F z v v ≤ 0) (hww : F z w w < 0)
    (hvw : 0 < v 0*w 0) : F z v w < 0 := by
  let x : U := ⟨z,inU hz⟩
  have hk := spatial_kernel x (exterior_profile x hz) ((w 0) • v - (v 0) • w)
    (by simp [smul_eq_mul,mul_comm])
  let A := F z
  change 0 ≤ A ((w 0) • v - (v 0) • w) ((w 0) • v - (v 0) • w) at hk
  have he : A w v = A v w := field_sym hz w v
  simp only [map_sub,map_smul,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,he] at hk
  by_contra! h
  change 0 ≤ A v w at h
  have hn := (mul_ne_zero_iff.mp hvw.ne').1
  nlinarith only [hk,mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (w 0)) hvv,
    mul_neg_of_pos_of_neg (sq_pos_iff.mpr hn) hww, mul_nonneg hvw.le h]

theorem sign_prop {L : ℝ} {f : ℝ→ℝ} (hc : ContinuousOn f (Icc 0 L))
    (hne : ∀ s∈Icc 0 L, f s≠0) {u : ℝ} (hu : u∈Icc 0 L) (hpos : 0 < f u) :
    ∀ t∈Icc 0 L, 0 < f t := by
  intro t ht
  by_contra! h
  obtain ⟨r,hr,he⟩ := isPreconnected_Icc.intermediate_value ht hu hc (show (0:ℝ)∈Icc (f t) (f u) from ⟨h,hpos.le⟩)
  exact hne _ hr he

theorem time_deriv {c : ℝ→E4} {v : E4} {t : ℝ} (h : HasDerivAt c v t) :
    HasDerivAt (fun s => c s 0) (v 0) t := by
  let P : E4 →L[ℝ] ℝ := EuclideanSpace.proj 0
  have hh : HasDerivAt (P ∘ c) (P v) t := P.hasFDerivAt.comp_hasDerivAt t h
  exact hh

theorem clock_positive {L o : ℝ} (hL : 0 < L) (c v : ℝ→E4)
    (hc : ∀ t∈Icc 0 L, HasDerivAt c (v t) t) (hv : ContinuousOn v (Icc 0 L))
    (hne : ∀ t∈Icc 0 L, v t 0≠0) (hdisp : 0 < o*(c L 0-c 0 0)) :
    ∀ t∈Icc 0 L, 0 < o*v t 0 := by
  let d (t : ℝ) := o*(c t 0)
  have hd (t : ℝ) (ht : t∈Icc 0 L) : HasDerivAt d (o*v t 0) t :=
    (time_deriv (hc t ht)).const_mul o
  have hco : ContinuousOn d (Icc 0 L) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope d (fun s => o*v s 0) hL hco (fun s hs => hd s (Ioo_subset_Icc_self hs))
  have htd : 0 < o*v t 0 := by
    rw [he]
    exact div_pos (by dsimp [d]; linarith only [hdisp]) (sub_pos.mpr hL)
  have ho := (mul_ne_zero_iff.mp hdisp.ne').1
  exact sign_prop (continuousOn_const.mul ((EuclideanSpace.proj (𝕜:=ℝ) 0).continuous.comp_continuousOn hv))
    (fun s hs => mul_ne_zero ho (hne s hs)) (Ioo_subset_Icc_self ht) htd

theorem common_sign {o u v : ℝ} (h1 : 0 < o*u) (h2 : 0 < o*v) : 0 < u*v := by
  rcases mul_pos_iff.mp h1 with h|h <;> rcases mul_pos_iff.mp h2 with k|k
  · exact mul_pos h.2 k.2
  · linarith [h.1,k.1]
  · linarith [h.1,k.1]
  · exact mul_pos_of_neg_of_neg h.2 k.2

theorem fit_clock {A : Set ℝ} (hA : IsOpen A) {L : ℝ} (hL : 0 < L) (hS : Icc 0 L⊆A) :
    ∃ f : ℝ→ℝ, ContDiff ℝ 1 f ∧ (∀ t, f t∈A) ∧ ∀ t∈Icc 0 L, f=ᶠ[𝓝 t] id := by
  obtain ⟨r₁,hr₁,h₁⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds (hS (left_mem_Icc.mpr hL.le)))
  obtain ⟨r₂,hr₂,h₂⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds (hS (right_mem_Icc.mpr hL.le)))
  let r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  let m := L/2
  let b : ContDiffBump m := ⟨m+r/2,m+r,by dsimp [m]; linarith,by linarith⟩
  let f (t : ℝ) := m+b t*(t-m)
  refine ⟨f,?_,?_,?_⟩
  · exact contDiff_const.add (b.contDiff.mul (contDiff_id.sub contDiff_const))
  · intro t
    have hb : |f t-m| < m+r := by
      by_cases h : b t=0
      · simp [f,h]; dsimp [m]; linarith
      · have hh : t∈Function.support b := h
        rw [b.support_eq,Metric.mem_ball,Real.dist_eq] at hh
        have he : f t-m=b t*(t-m) := by dsimp [f]; ring
        rw [he,abs_mul,abs_of_nonneg b.nonneg]
        exact (mul_le_mul_of_nonneg_right b.le_one (abs_nonneg _)).trans_lt (by simpa using hh)
    have hl := (abs_lt.mp hb).1
    have hu := (abs_lt.mp hb).2
    by_cases h0 : f t < 0
    · apply h₁
      rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_neg h0]
      dsimp [m] at hl; linarith only [hl,min_le_left r₁ r₂]
    · by_cases h1 : L < f t
      · apply h₂
        rw [Metric.mem_ball,Real.dist_eq,abs_of_pos (sub_pos.mpr h1)]
        dsimp [m] at hu; linarith only [hu,min_le_right r₁ r₂]
      · exact hS ⟨le_of_not_gt h0,le_of_not_gt h1⟩
  · intro t ht
    have hh : t∈Metric.ball m b.rIn := by
      rw [Metric.mem_ball,Real.dist_eq,abs_lt]
      change -(L/2+r/2) < t-L/2 ∧ t-L/2 < L/2+r/2
      constructor <;> linarith [ht.1,ht.2]
    filter_upwards [b.eventuallyEq_one_of_mem_ball hh] with z hz
    change b z=1 at hz
    simp [f,hz]

abbrev NF  (x₀ : E4) := NormalFlow (F) (S) x₀
abbrev span  {x₀ : E4} (N : NF x₀) := Icc (0:ℝ) N.time
abbrev Z  {x₀ : E4} (N : NF x₀) (p v : E4) (t : ℝ) := (N.flow (t,(p,v))).1
abbrev Velo  {x₀ : E4} (N : NF x₀) (p v : E4) (t : ℝ) := (N.flow (t,(p,v))).2

theorem radial_data  {x₀ : E4} (N : NF x₀) {p v : E4}
    (hv : (p,v)∈N.normal.source) :
    (∀ t∈span N, Z N p v t∈S ∧ HasDerivAt (Z N p v) (Velo N p v t) t) ∧
    ContinuousOn (Velo N p v) (span N) ∧ Z N p v 0=p ∧ Velo N p v 0=v := by
  have h0 := N.initial (p,v) (N.source_stays (p,v) hv 0 ⟨le_rfl,N.time_pos.le⟩)
  refine ⟨fun t ht => ⟨(N.ode _ (N.source_stays _ hv t ht)).1,?_⟩,?_,congrArg Prod.fst h0,congrArg Prod.snd h0⟩
  · exact (N.ode _ (N.source_stays _ hv t ht)).2.fst
  · exact (N.flow_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (N.source_stays (p,v) hv)).snd

private theorem radial_nonzero   {x₀ : E4}
    (N : NF x₀) {p v : E4} (hv : (p,v)∈N.normal.source) (hn : v≠0) {t : ℝ} (ht : t∈span N) :
    Velo N p v t≠0 := by
  intro hbad
  let f := geodesicSpray (F)
  let u (s : ℝ) := N.flow (t-s,(p,v))
  let y := N.flow (t,(p,v))
  have htime {s : ℝ} (hs : s∈Icc 0 t) : t-s∈span N := ⟨sub_nonneg.mpr hs.2,by linarith [ht.2,hs.1]⟩
  have hdu (s : ℝ) (hs : s∈Icc 0 t) : HasDerivAt u (-f (u s)) s := by
    simpa [u,f,Function.comp_def] using ((N.ode _ (N.source_stays (p,v) hv _ (htime hs))).2.scomp s ((hasDerivAt_id s).const_sub t))
  have hy : f y=0 := by
    change (y.2,-OAI.WeakMTWGlobalSupport.CoordinateGeometry.christoffel (F) y.1 y.2 y.2) = 0
    change y.2=0 at hbad
    simp [hbad]
  have hsmooth := contDiffOn_geodesicSpray_of_invertible (openS) (field_smooth) (fun z hz => field_inv hz)
  have hz : EqOn u (fun _=>y) (Icc 0 t) := by
    apply FlowLinearization.unique_Icc (f:=fun z => -f z) (fun s hs => (hdu s hs).continuousAt.continuousWithinAt) continuousOn_const
    · intro z hz
      have hz' : z∈(S) ×ˢ (univ : Set E4) := by
        rcases hz with ⟨s,hs,rfl⟩|⟨_,_,rfl⟩
        · exact ⟨(N.ode _ (N.source_stays (p,v) hv _ (htime hs))).1,mem_univ _⟩
        · exact ⟨(N.ode _ (N.source_stays (p,v) hv t ht)).1,mem_univ _⟩
      exact (((hsmooth z hz').contDiffAt (((openS).prod isOpen_univ).mem_nhds hz')).of_le (by simp)).neg
    · exact fun s hs => (hdu s hs).hasDerivWithinAt
    · intro s _
      simpa only [hy,neg_zero] using hasDerivWithinAt_const s (Icc (0:ℝ) t) y
    · simp [u,y]
  have h := congrArg Prod.snd (hz (right_mem_Icc.mpr ht.1))
  have h0 := (radial_data N hv).2.2.2
  apply hn
  calc
    v = Velo N p v 0 := h0.symm
    _ = Velo N p v t := by simpa only [u,y,sub_self] using h
    _ = 0 := hbad

theorem radial_future  
    (T : VecField (U)) (hT : IsTimeOrientation (G) T) {x₀ : E4} (N : NF x₀)
    (p q : U) (htarget : (p.val,q.val)∈N.normal.target)
    (hE : initialEnergy N p.val q.val ≤ 0)
    (ho : 0 ≤ (q.val 0-p.val 0)*timeComponent (T p)) : q∈causalFuture (G) T (D) p := by
  by_cases hdiag : q=p
  · exact Or.inl (mem_singleton_iff.mpr hdiag)
  let v := logVec N p.val q.val
  let R := Z N p.val v
  let d := Velo N p.val v
  let o := timeComponent (T p)
  have hv : (p.val,v)∈N.normal.source := (N.normalAt p.val).map_target htarget
  have hlast : R N.time = q.val := by
    simpa only [N.normalAt_apply,R,Z,v,logVec] using (N.normalAt p.val).right_inv htarget
  have hvne : v≠0 := by
    intro hv0
    have hh : (p.val,(0:E4))∈N.normal.source := hv0 ▸ hv
    have he := normalAt_zero_of_invertible N (openS) (field_smooth)
      (fun z hz => field_inv hz) hh
    apply hdiag
    apply Subtype.ext
    calc
      q.val = N.normalAt p.val v := ((N.normalAt p.val).right_inv htarget).symm
      _ = p.val := hv0 ▸ he
  obtain ⟨hR,hdc,hfirst,_⟩ := radial_data N hv
  have henergy (t : ℝ) (ht : t∈span N) : F (R t) (d t) (d t) ≤ 0 :=
    (flow_energy N (openS) (field_smooth) (fun _ hz => field_sym hz)
      (fun _ hz => field_inv hz) hv ht).trans_le hE
  have hdn (t : ℝ) (ht : t∈span N) := radial_nonzero N hv hvne ht
  have hdt (t : ℝ) (ht : t∈span N) : d t 0≠0 := nonzero_time (hR _ ht).1 (hdn t ht) (henergy t ht)
  have h₀ : (0:ℝ)∈span N := ⟨le_rfl,N.time_pos.le⟩
  have hpS := N.base_mem hv
  have hor : o≠0 := by
    apply nonzero_time hpS _ (hT.2 p).le
    intro h
    have hh := hT.2 p
    change (T p : E4)=0 at h
    change F p.val (T p : E4) (T p : E4) < 0 at hh
    rw [h] at hh
    have e : F p.val (0:E4) (0:E4)=0 := by rw [map_zero]
    exact (lt_irrefl _) (e ▸ hh)
  have hdiff (s : ℝ) (hs : s∈span N) : HasDerivAt (fun t => R t 0) (d s 0) s :=
    time_deriv (hR s hs).2
  have hstrict : 0 < o*(R N.time 0-R 0 0) := by
    have h0' : R 0=p.val := hfirst
    have hs := exists_hasDerivAt_eq_slope (fun t => R t 0) (fun t => d t 0) N.time_pos
      (fun t ht => (hdiff t ht).continuousAt.continuousWithinAt) (fun t ht => hdiff t (Ioo_subset_Icc_self ht))
    obtain ⟨t,ht,he⟩ := hs
    have hdne : R N.time 0 - R 0 0 ≠ 0 := fun hh => hdt t (Ioo_subset_Icc_self ht) (by simpa [hh] using he)
    apply lt_of_le_of_ne _ ((mul_ne_zero hor hdne).symm)
    rw [hlast,h0',mul_comm]
    exact ho
  have hsign := clock_positive N.time_pos R d (fun s hs => (hR s hs).2) hdc hdt hstrict
  have horient (s : ℝ) (hs : s∈span N) : 0 < o*(W T (R s)) 0 := by
    have hc : ContinuousOn (fun t => o*(W T (R t)) 0) (span N) := by
      intro t ht
      let z : U := ⟨R t,inU (hR t ht).1⟩
      have hz : ContinuousAt (W T) (R t) := W_cont T hT z
      have hr : ContinuousAt R t := (hR t ht).2.continuousAt
      have ht' : ContinuousAt (fun s => W T (R s)) t := hz.comp (f:=R) hr
      let proj : E4 →L[ℝ] ℝ := EuclideanSpace.proj 0
      have hh : ContinuousAt (fun s => proj (W T (R s))) t :=
        proj.continuous.continuousAt.comp (f:=fun s => W T (R s)) ht'
      exact (continuousAt_const.mul hh).continuousWithinAt
    have hn (t : ℝ) (ht : t∈span N) : o*(W T (R t)) 0≠0 := by
      let z : U := ⟨R t,inU (hR t ht).1⟩
      have hg := hT.2 z
      change F (R t) (T z : E4) (T z : E4) < 0 at hg
      have he : W T (R t)=(T z:E4) := W_on T z
      rw [he]
      exact mul_ne_zero hor (nonzero_time (hR t ht).1 (fun hh => by simp [hh] at hg) hg.le)
    apply sign_prop hc hn h₀ _ s hs
    change 0 < o*(W T (R 0)) 0
    rw [show R 0=p.val from hfirst,W_on]
    exact mul_self_pos.mpr hor
  let A : Set ℝ := {s | (s,(p.val,v))∈N.domain}
  have hA : IsOpen A := N.domain_open.preimage (continuous_id.prodMk continuous_const)
  obtain ⟨f,hf,hfA,hfe⟩ := fit_clock hA N.time_pos (N.source_stays (p.val,v) hv)
  let γ (t : ℝ) : U := ⟨R (f (N.time*t)),inU (N.ode _ (hfA _)).1⟩
  have hc : ContDiff ℝ 1 (Subtype.val ∘ γ) := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    let param (u : ℝ) : ℝ×(E4×E4) := (f (N.time*u),(p.val,v))
    have hparam : ContDiff ℝ 1 param := (hf.comp (contDiff_const.mul contDiff_id)).prodMk contDiff_const
    have hh : ContDiffAt ℝ 1 N.flow (param t) :=
      ((N.flow_smooth _ (hfA (N.time*t))).contDiffAt (N.domain_open.mem_nhds (hfA (N.time*t)))).of_le
        (show (1:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    have hh' : ContDiffAt ℝ 1 (N.flow ∘ param) t := hh.comp (f:=param) t hparam.contDiffAt
    exact hh'.fst
  have hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ := fun s =>
    (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff γ univ s).mp (hc.contMDiff s)
  have eqF (s : ℝ) (hs : s∈span N) : f s=s := (hfe s hs).eq_of_nhds
  refine Or.inr ⟨γ,⟨hγ,?_⟩,Subtype.ext ?_,Subtype.ext ?_⟩
  · intro s hs
    have hts : N.time*s∈span N := ⟨mul_nonneg N.time_pos.le hs.1,by simpa using mul_le_mul_of_nonneg_left hs.2 N.time_pos.le⟩
    let t := N.time*s
    have hz : (γ s).val=R t := by change R (f t)=R t; rw [eqF t hts]
    have hb : HasDerivAt (fun u => f (N.time*u)) N.time s := by
      have hclock : HasDerivAt (fun u : ℝ => N.time*u) N.time s := by
        simpa only [id_eq,mul_one] using (hasDerivAt_id s).const_mul N.time
      have hequal : (fun u : ℝ => f (N.time*u)) =ᶠ[𝓝 s] (fun u : ℝ => N.time*u) :=
        (hfe t hts).comp_tendsto hclock.continuousAt.tendsto
      exact hclock.congr_of_eventuallyEq hequal
    have hr : HasDerivAt R (d t) (f t) := by rw [eqF t hts]; exact (hR t hts).2
    have hder : HasDerivAt (fun u => (γ u).val) (N.time • d t) s := by
      change HasDerivAt (R ∘ fun u => f (N.time*u)) (N.time • d t) s
      exact hr.scomp s hb
    have hv' := ambient_velocity γ hγ s _ hder
    have htim := hT.2 (γ s)
    have heW : W T (R t)=(T (γ s):E4) := hz ▸ W_on T (γ s)
    have hpair := cone_pair_negative (hR t hts).1 (henergy t hts)
      (w:=W T (R t)) (by
        change F (R t) (W T (R t)) (W T (R t)) < 0
        rw [heW,←hz]
        exact htim) (common_sign (hsign t hts) (horient t hts))
    refine ⟨show (γ s).val∈S by rw [hz]; exact (hR t hts).1,?_,?_,?_⟩
    · change (velocity γ s:E4)≠0
      rw [hv']
      exact smul_ne_zero N.time_pos.ne' (hdn t hts)
    · change F (γ s).val (velocity γ s:E4) (velocity γ s:E4) ≤ 0
      rw [hv',hz]
      simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos N.time_pos.le (mul_nonpos_of_nonneg_of_nonpos N.time_pos.le (henergy t hts))
    · change F (γ s).val (velocity γ s:E4) (T (γ s):E4) < 0
      rw [hv',hz,←heW]
      simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
      exact mul_neg_of_pos_of_neg N.time_pos hpair
  · simpa only [γ,mul_zero,eqF 0 h₀] using hfirst
  · simpa only [γ,mul_one,eqF _ (right_mem_Icc.mpr N.time_pos.le)] using hlast

theorem energy_cont   {x₀ : E4}
    (N : NF x₀) {p q : E4} (hpS : p∈S) (ht : (p,q)∈N.normal.target) :
    ContinuousAt (fun k : E4×E4 => initialEnergy N k.1 k.2) (p,q) := by
  have hF := ((field_smooth p hpS).continuousWithinAt.continuousAt ((openS).mem_nhds hpS)).comp
    (continuous_fst.continuousAt (x:=(p,q)))
  exact (hF.clm_apply (logVec_continuousAt N ht)).clm_apply (logVec_continuousAt N ht)


end
end NoHair.TwoCentre.StaticCausality


open NoHair NoHair.TwoCentre Set Filter
open OAI.WeakMTWGlobalSupport OAI.WeakMTWGlobalSupport.CoordinateGeometry
open OAI.WeakMTWGlobalSupport.NormalNeighborhood NoHair.PseudoNormal
open scoped ContDiff Manifold BigOperators Topology
namespace NoHair.TwoCentre.StaticCausality
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 330000
private theorem energy_barrier  
    {x₀ : E4} (N : NF x₀) (base : E4) (c v : ℝ→E4) (o : ℝ)
    (hd : ∀ t, HasDerivAt c (v t) t) (hmemS : ∀ t∈J, c t∈S)
    (htarget : ∀ t∈J, (base,c t)∈N.normal.target)
    (hcone : ∀ t∈J, F (c t) (v t) (v t) ≤ 0)
    (hsign : ∀ t∈J, 0 < o*v t 0) (htime : ∀ t∈J, 0 < o*(c t 0-base 0))
    (hseed : initialEnergy N base (c 0) < 0) : initialEnergy N base (c 1) ≤ initialEnergy N base (c 0) := by
  have sG := field_smooth
  have invG (z : E4) (hz : z∈S) := field_inv hz
  have symG (z : E4) (hz : z∈S) := field_sym hz
  let d (t : ℝ) := (2/N.time)*F (c t) (terminalVelocity N base (c t)) (v t)
  have HE (t : ℝ) (ht : t∈J) : HasDerivAt (fun t => initialEnergy N base (c t)) (d t) t :=
    initialEnergy_deriv N (openS) sG symG invG (htarget t ht) (hd t)
  have H := image_le_of_deriv_right_lt_deriv_boundary (f:=fun t => initialEnergy N base (c t))
    (f':=d) (B:=fun _ => initialEnergy N base (c 0)) (B':=fun _ => 0) (a:=(0:ℝ)) (b:=1)
    (fun t ht => (HE t ht).continuousAt.continuousWithinAt) (fun t ht => (HE t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    le_rfl (fun t => hasDerivAt_const t _) (by
      intro t hti ha
      have ht := Ico_subset_Icc_self hti
      let u := logVec N base (c t)
      have htar' := htarget t ht
      have hu : (base,u)∈N.normal.source := (N.normalAt base).map_target htar'
      obtain ⟨hR,hC,hfirst,_⟩ := radial_data N hu
      have hlast : Z N base u N.time=c t := by simpa only [N.normalAt_apply,Z,u,logVec] using (N.normalAt base).right_inv htar'
      have htim (r : ℝ) (hr : r∈span N) :
          F (Z N base u r) (Velo N base u r) (Velo N base u r) < 0 :=
        (flow_energy N (openS) sG symG invG hu hr).trans_lt (ha.trans_lt hseed)
      have hdt (r : ℝ) (hr : r∈span N) : Velo N base u r 0≠0 := by
        have hh := htim r hr
        exact nonzero_time (hR r hr).1 (fun h => by simp [h] at hh) hh.le
      have hforward : 0 < o*(Z N base u N.time 0-Z N base u 0 0) := by
        rw [hlast,hfirst]
        exact htime t ht
      have hfin : N.time∈span N := right_mem_Icc.mpr N.time_pos.le
      have hsg := clock_positive N.time_pos (Z N base u) (Velo N base u) (fun r hr => (hR r hr).2) hC hdt hforward N.time hfin
      have hh := htim N.time hfin
      rw [hlast] at hh
      have hm := cone_pair_negative (hmemS t ht) (hcone t ht) hh (common_sign (hsign t ht) hsg)
      dsimp only [d]
      apply mul_neg_of_pos_of_neg (div_pos (by norm_num) N.time_pos)
      rw [symG (c t) (hmemS t ht)]
      exact hm)
  exact H (right_mem_Icc.mpr zero_le_one)

private theorem past_shift_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (p w : E) :
    Tendsto (fun t : ℝ => p-t • w) (𝓝[>] (0:ℝ)) (𝓝 p) := by
  have h : Continuous (fun t : ℝ => p-t • w) := continuous_const.sub (continuous_id.smul continuous_const)
  have hh := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  simpa only [zero_smul,sub_zero] using hh

private theorem derivative_quotient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ→E) (v : E) (hf : HasDerivAt f v 0) (h0 : f 0=0) :
    Tendsto (fun s : ℝ => s⁻¹ • f s) (𝓝[>] (0:ℝ)) (𝓝 v) := by
  have h := (hasDerivAt_iff_tendsto_slope_left_right.mp hf).2
  have he : slope f 0 = (fun s : ℝ => s⁻¹ • f s) := by
    funext s
    rw [slope_def_module,h0,sub_zero,sub_zero]
  rwa [he] at h

private theorem scaled_norm_negative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (g₀ : E →L[ℝ] E →L[ℝ] ℝ) (f : ℝ→E) (v : E)
    (hg : Tendsto g (𝓝[>] (0:ℝ)) (𝓝 g₀)) (hf : Tendsto (fun s : ℝ => s⁻¹ • f s) (𝓝[>] 0) (𝓝 v))
    (hneg : g₀ v v < 0) : ∀ᶠ s in 𝓝[>] (0:ℝ), g s (f s) (f s) < 0 := by
  have he : Continuous (fun k : (E →L[ℝ] E →L[ℝ] ℝ) × (E×E) => k.1 k.2.1 k.2.2) :=
    (continuous_fst.clm_apply (continuous_fst.comp continuous_snd)).clm_apply (continuous_snd.comp continuous_snd)
  have hlim : Tendsto (fun s : ℝ => g s (s⁻¹ • f s) (s⁻¹ • f s)) (𝓝[>] 0) (𝓝 (g₀ v v)) :=
    (he.tendsto (g₀,v,v)).comp (hg.prodMk_nhds (hf.prodMk_nhds hf))
  have hspos : ∀ᶠ s in 𝓝[>] (0:ℝ), 0<s := self_mem_nhdsWithin
  filter_upwards [hlim.eventually_lt_const hneg,hspos] with s hs hp
  change g s (s⁻¹ • f s) (s⁻¹ • f s) < 0 at hs
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul] at hs
  exact neg_of_mul_neg_right (neg_of_mul_neg_right hs (inv_pos.mpr hp).le) (inv_pos.mpr hp).le

private theorem scale_timelike {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E →L[ℝ] E →L[ℝ] ℝ) (v : E) (t : ℝ) (ht : 0 < t) (hv : G v v < 0) :
    G (t⁻¹ • v) (t⁻¹ • v) < 0 := by
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
  exact mul_neg_of_pos_of_neg (inv_pos.mpr ht) (mul_neg_of_pos_of_neg (inv_pos.mpr ht) hv)

private theorem past_seed   {x₀ : E4} (N : NF x₀)
    {p : E4} (hpS : p∈S) (hsrc : (p,(0:E4))∈N.normal.source)
    (hlog : logVec N p p = 0) (w : E4) (hw : F p w w < 0) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), initialEnergy N (p-s • w) p < 0 := by
  let f (s : ℝ) := logVec N (p-s • w) p
  let g (s : ℝ) := F (p-s • w)
  have sm := field_smooth
  have hG : ContinuousAt (F) p := (sm p hpS).continuousWithinAt.continuousAt ((openS).mem_nhds hpS)
  have gL : Tendsto g (𝓝[>] (0:ℝ)) (𝓝 (F p)) := hG.tendsto.comp (past_shift_limit p w)
  have hd : HasDerivAt f (N.time⁻¹ • w) 0 := logVec_base_deriv N (openS) sm
    (fun z hz => field_inv hz) hsrc w
  have f0 : f 0 = 0 := by simpa only [f,zero_smul,sub_zero] using hlog
  exact scaled_norm_negative g (F p) f (N.time⁻¹ • w) gL
    (derivative_quotient f _ hd f0) (scale_timelike _ w N.time N.time_pos hw)

private theorem positive_shift {a p o s : ℝ} (h : 0 ≤ o*(a-p)) (ho : o≠0) (hs : 0<s) :
    0 < o*(a-(p-s*o)) := by
  nlinarith only [h,mul_pos hs (sq_pos_iff.mpr ho)]

private theorem past_energy_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : E×E→ℝ) (p q w : E) (hc : ContinuousAt k (p,q))
    (hh : ∀ᶠ s in 𝓝[>] (0:ℝ), k (p-s • w,q) ≤ 0) : k (p,q) ≤ 0 := by
  have hpair : Tendsto (fun s : ℝ => (p-s • w,q)) (𝓝[>] 0) (𝓝 (p,q)) :=
    (past_shift_limit p w).prodMk_nhds tendsto_const_nhds
  exact le_of_tendsto (hc.tendsto.comp hpair) hh

private theorem clock_along (c v : ℝ→E4) (o : ℝ) (hd : ∀ t, HasDerivAt c (v t) t)
    (hc : Continuous v) (hn : ∀ t∈J, v t 0≠0) (hstart : 0 < o*v 0 0) :
    (∀ t∈J, 0 < o*v t 0) ∧ ∀ t∈J, 0 ≤ o*(c t 0-c 0 0) := by
  have h₀ : (0:ℝ)∈J := left_mem_Icc.mpr zero_le_one
  have hone := (mul_ne_zero_iff.mp hstart.ne').1
  have hsign : ∀ t∈J, 0 < o*v t 0 := sign_prop
    (continuous_const.mul ((EuclideanSpace.proj (𝕜:=ℝ) 0).continuous.comp hc)).continuousOn
    (fun t ht => mul_ne_zero hone (hn t ht)) h₀ hstart
  have hclock (t : ℝ) : HasDerivAt (fun s => o*c s 0) (o*v t 0) t :=
    (time_deriv (hd t)).const_mul o
  have hdiff : Differentiable ℝ (fun s => o*c s 0) := fun t => (hclock t).differentiableAt
  have hmono : MonotoneOn (fun s => o*c s 0) J := monotoneOn_of_deriv_nonneg (convex_Icc (0:ℝ) 1)
    hdiff.continuous.continuousOn hdiff.differentiableOn (fun t ht => (hclock t).deriv.symm ▸ (hsign t (interior_subset ht)).le)
  refine ⟨hsign,?_⟩
  intro t ht
  rw [mul_sub]
  exact sub_nonneg.mpr (hmono h₀ ht ht.1)

private theorem energy_of_arc  
    {x₀ : E4} (N : NF x₀) (V : Set E4) (hV : IsOpen V) (hVS : V⊆S)
    (htar : ∀ p∈V, ∀ q∈V, (p,q)∈N.normal.target) (p q w : E4)
    (hpV : p∈V) (hqV : q∈V) (hsrc : (p,(0:E4))∈N.normal.source)
    (hlog : logVec N p p = 0) (hw : F p w w < 0)
    (c v : ℝ→E4) (hd : ∀ t, HasDerivAt c (v t) t)
    (hmem : ∀ t∈J, c t∈V) (he0 : c 0=p) (he1 : c 1=q)
    (hcone : ∀ t∈J, F (c t) (v t) (v t) ≤ 0)
    (hsign : ∀ t∈J, 0 < w 0*v t 0) (hdisp : ∀ t∈J, 0 ≤ w 0*(c t 0-p 0)) :
    initialEnergy N p q ≤ 0 := by
  let o := w 0
  have h₀ : (0:ℝ)∈J := left_mem_Icc.mpr zero_le_one
  have hone : o≠0 := (mul_ne_zero_iff.mp (hsign 0 h₀).ne').1
  let b (s : ℝ) := p-s • w
  have bL : Tendsto b (𝓝[>] (0:ℝ)) (𝓝 p) := past_shift_limit p w
  have bV : ∀ᶠ s in 𝓝[>] (0:ℝ), b s∈V := bL (hV.mem_nhds hpV)
  have spos : ∀ᶠ s in 𝓝[>] (0:ℝ), 0<s := self_mem_nhdsWithin
  have hbase : ∀ᶠ s in 𝓝[>] (0:ℝ), initialEnergy N (b s) p < 0 :=
    past_seed N (hVS hpV) hsrc hlog w hw
  have hbound : ∀ᶠ s in 𝓝[>] (0:ℝ), initialEnergy N (b s) q ≤ 0 := by
    filter_upwards [hbase,bV,spos] with s hseed hsV hspos
    have htime (t : ℝ) (ht : t∈J) : 0 < o*(c t 0-b s 0) := by
      change 0 < o*(c t 0-(p 0-s*o))
      exact positive_shift (hdisp t ht) hone hspos
    have h := energy_barrier N (b s) c v o hd (fun t ht => hVS (hmem t ht))
      (fun t ht => htar _ hsV _ (hmem t ht)) hcone hsign htime (by rwa [he0])
    rw [he0,he1] at h
    exact h.trans hseed.le
  exact past_energy_limit (fun k : E4×E4 => initialEnergy N k.1 k.2) p q w
    (energy_cont N (hVS hpV) (htar _ hpV _ hqV)) hbound


private theorem curve_necessary  
    (T : VecField (U)) (hT : IsTimeOrientation (G) T) {x₀ : E4} (N : NF x₀)
    (V : Set E4) (hV : IsOpen V) (hVS : V⊆S) (hsrc : ∀ x∈V, (x,(0:E4))∈N.normal.source)
    (htar : ∀ p∈V, ∀ q∈V, (p,q)∈N.normal.target)
    (p q : U) (hpV : p.val∈V) (hqV : q.val∈V)
    (hJ : q∈causalFuture (G) T ((Subtype.val : U → E4) ⁻¹' V) p) :
    initialEnergy N p.val q.val ≤ 0 ∧ 0 ≤ (q.val 0-p.val 0)*timeComponent (T p) := by
  have sG := field_smooth
  have invG (z : E4) (hz : z∈S) := field_inv hz
  have hxsrc := hsrc p.val hpV
  have hlog0 : logVec N p.val p.val = 0 := by
    have he := normalAt_zero_of_invertible N (openS) sG invG hxsrc
    simpa only [logVec,he] using (N.normalAt p.val).left_inv hxsrc
  rcases hJ with he|⟨γ,hγ,h0,h1⟩
  · have heq : q = p := mem_singleton_iff.mp he
    subst q
    constructor
    · change F p.val (logVec N p.val p.val) (logVec N p.val p.val) ≤ 0
      simp only [hlog0,map_zero,ContinuousLinearMap.zero_apply,le_refl]
    · simp only [sub_self,zero_mul,le_refl]
  let c (t : ℝ) := (γ t).val
  let v := deriv c
  let w : E4 := T p
  let o := w 0
  have hval : ContMDiff I4 I4 1 (Subtype.val : U→E4) := contMDiff_subtype_val
  have hc : ContDiff ℝ 1 c := (hval.comp hγ.1).contDiff
  have hd (t : ℝ) : HasDerivAt c (v t) t := (hc.differentiable (by simp) t).hasDerivAt
  have hvel (t : ℝ) := ambient_velocity γ hγ.1 t (v t) (hd t)
  have hmem (t : ℝ) (ht : t∈J) : c t∈V := (hγ.2 t ht).1
  have he0 : c 0=p.val := congrArg Subtype.val h0
  have he1 : c 1=q.val := congrArg Subtype.val h1
  have hcone (t : ℝ) (ht : t∈J) : v t≠0 ∧ F (c t) (v t) (v t) ≤ 0 ∧ 0 < (v t 0)*timeComponent (T (γ t)) := by
    obtain ⟨hx,hn,hv,hf⟩ := hγ.2 t ht
    have hh := (cone_estimates (γ t) (exterior_profile _ (hVS hx)) _ _ hn hv hf (hT.2 _)).2
    change 0 < timeComponent (velocity γ t) * timeComponent (T (γ t)) at hh
    rw [hvel] at hh
    change (velocity γ t:E4)≠0 at hn
    change F (c t) (velocity γ t:E4) (velocity γ t:E4) ≤ 0 at hv
    rw [hvel] at hn hv
    exact ⟨hn,hv,hh⟩
  have h₀ : (0:ℝ)∈J := left_mem_Icc.mpr zero_le_one
  have h₁ : (1:ℝ)∈J := right_mem_Icc.mpr zero_le_one
  have hstart : 0 < o*v 0 0 := by
    have h := (hcone 0 h₀).2.2
    rw [h0,mul_comm] at h
    exact h
  have hn (t : ℝ) (ht : t∈J) : v t 0≠0 :=
    nonzero_time (hVS (hmem t ht)) (hcone t ht).1 (hcone t ht).2.1
  obtain ⟨hsign,hdisp₀⟩ := clock_along c v o hd (hc.continuous_deriv le_rfl) hn hstart
  have hdisp (t : ℝ) (ht : t∈J) : 0 ≤ o*(c t 0-p.val 0) := by
    simpa only [he0] using hdisp₀ t ht
  refine ⟨energy_of_arc N V hV hVS htar p.val q.val w hpV hqV hxsrc hlog0
    (hT.2 p) c v hd hmem he0 he1 (fun t ht => (hcone t ht).2.1) hsign hdisp,?_⟩
  rw [← he1,mul_comm]
  exact hdisp 1 h₁

theorem local_closure (T : VecField U) (hT : IsTimeOrientation G T) :
    ∀ x ∈ D, ∃ V : Set U, IsOpen V ∧ x ∈ V ∧ V ⊆ D ∧
      ∀ z : U × U, z.1 ∈ V → z.2 ∈ V →
        z ∈ closure {y : U × U | y.1 ∈ V ∧ y.2 ∈ V ∧ y.2 ∈ causalFuture G T V y.1} →
          z.2 ∈ causalFuture G T D z.1 := by
  intro x hx
  obtain ⟨N⟩ := exists_normalFlow_of_invertible (openS) (field_smooth)
    (fun z hz => field_inv hz) (x₀:=x.val) hx
  have hdiag := normal_center N (openS) (field_smooth) (fun z hz => field_inv hz) N.center_mem
  have htar : (x.val,x.val)∈N.normal.target := hdiag ▸ N.normal.map_source N.center_mem
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (N.normal.open_target.mem_nhds htar)
  let V := Metric.ball x.val r ∩ (S ∩ {p | (p,(0:E4))∈N.normal.source})
  have hV : IsOpen V := Metric.isOpen_ball.inter ((openS).inter
    (N.normal.open_source.preimage (continuous_id.prodMk continuous_const)))
  have hVS {z : E4} (hz : z∈V) := hz.2.1
  have htr (p : E4) (hp : p∈V) (q : E4) (hq : q∈V) : (p,q)∈N.normal.target := by
    apply hball
    rw [Metric.mem_ball,Prod.dist_eq]
    exact max_lt (Metric.mem_ball.mp hp.1) (Metric.mem_ball.mp hq.1)
  refine ⟨(Subtype.val : U→E4) ⁻¹' V,hV.preimage continuous_subtype_val,
    ⟨Metric.mem_ball_self hr,hx,N.center_mem⟩,fun _ hz => hVS hz,?_⟩
  intro z hpV hqV hcl
  obtain ⟨seq,hseq,hlim⟩ := mem_closure_iff_seq_limit.mp hcl
  have hnec (n : ℕ) := curve_necessary T hT N V hV (fun _ hz => hVS hz)
    (fun _ hz => hz.2.2) htr (seq n).1 (seq n).2 (hseq n).1 (hseq n).2.1 (hseq n).2.2
  have hP : Tendsto (fun n => (seq n).1.val) atTop (𝓝 z.1.val) :=
    (continuous_subtype_val.tendsto z.1).comp ((continuous_fst.tendsto z).comp hlim)
  have hQ : Tendsto (fun n => (seq n).2.val) atTop (𝓝 z.2.val) :=
    (continuous_subtype_val.tendsto z.2).comp ((continuous_snd.tendsto z).comp hlim)
  apply radial_future T hT N z.1 z.2 (htr _ hpV _ hqV)
  · exact le_of_tendsto ((energy_cont N (hVS hpV) (htr _ hpV _ hqV)).tendsto.comp
      (hP.prodMk_nhds hQ)) (Eventually.of_forall fun n => (hnec n).1)
  · have hTlim : Tendsto (fun n => W T (seq n).1.val) atTop (𝓝 (W T z.1.val)) :=
      (W_cont T hT z.1).tendsto.comp hP
    have hproj : Continuous timeComponent := (EuclideanSpace.proj (𝕜:=ℝ) (0 : Fin 4)).continuous
    have hQ0 : Tendsto (fun n => timeComponent (seq n).2.val) atTop (𝓝 (timeComponent z.2.val)) :=
      (hproj.tendsto _).comp hQ
    have hP0 : Tendsto (fun n => timeComponent (seq n).1.val) atTop (𝓝 (timeComponent z.1.val)) :=
      (hproj.tendsto _).comp hP
    have ht0 : Tendsto (fun n => timeComponent (W T (seq n).1.val)) atTop (𝓝 (timeComponent (W T z.1.val))) :=
      (hproj.tendsto _).comp hTlim
    have hT0 : Tendsto (fun n => timeComponent (T (seq n).1)) atTop (𝓝 (timeComponent (T z.1))) := by
      simpa only [W_on] using ht0
    exact ge_of_tendsto ((hQ0.sub hP0).mul hT0) (Eventually.of_forall fun n => (hnec n).2)

end
end NoHair.TwoCentre.StaticCausality

open NoHair NoHair.TwoCentre Set Filter
open OAI.WeakMTWGlobalSupport OAI.WeakMTWGlobalSupport.CoordinateGeometry
open OAI.WeakMTWGlobalSupport.NormalNeighborhood NoHair.PseudoNormal
open scoped ContDiff Manifold BigOperators Topology
namespace NoHair.TwoCentre.StaticCausality
noncomputable section
set_option maxHeartbeats 400000
theorem eval_smooth (z v w : E4) (hz : z∈exterior) :
    ContDiffAt ℝ 1 (fun k : E4 × E4 × E4 => F k.1 k.2.1 k.2.2) (z,v,w) := by
  have h := ((field_smooth z hz).contDiffAt (openS.mem_nhds hz)).of_le (show (1:ℕ∞ω) ≤ ∞ by simp)
  exact ((h.comp (z,v,w) contDiffAt_fst).clm_apply (contDiffAt_fst.comp (z,v,w) contDiffAt_snd)).clm_apply (contDiffAt_snd.comp (z,v,w) contDiffAt_snd)
def Good  (T : VecField (U)) (z v : E4) : Prop :=
  z ∈ exterior ∧ F z v v ≤ 0 ∧ F z v (W T z) < 0

private theorem good_scale  (T : VecField (U)) {z v : E4} (h : Good T z v)
    {c : ℝ} (hc : 0<c) : Good T z (c • v) := by
  obtain ⟨hz,hv,hw⟩ := h
  refine ⟨hz, ?_, ?_⟩
  · simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos hc.le (mul_nonpos_of_nonneg_of_nonpos hc.le hv)
  · simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hc hw

theorem directions   (T : VecField (U))
    (hT : IsTimeOrientation (G) T) (x : U) (v w : E4)
    (hv : Good T x.val v) (hw : Good T x.val w) :
    (∃ c : ℝ, 0<c ∧ v=c • w) ∨ F x.val v w < 0 := by
  have hf := exterior_profile x hv.1
  have vn (h : E4) (hh : Good T x.val h) : h ≠ 0 := by
    intro he
    have hh' := hh.2.2
    simp [he] at hh'
  have ht (h : E4) (hh : Good T x.val h) : 0 < h 0 * timeComponent (T x) := by
    apply (cone_estimates x hf h (T x) (vn h hh) hh.2.1 _ (hT.2 x)).2
    exact (show F x.val h (T x : E4)<0 by simpa only [W_on] using hh.2.2)
  have hprod : 0 < v 0*w 0 := by
    rcases mul_pos_iff.mp (ht v hv) with h₁|h₁ <;> rcases mul_pos_iff.mp (ht w hw) with h₂|h₂
    · exact mul_pos h₁.1 h₂.1
    · linarith [h₁.2,h₂.2]
    · linarith [h₁.2,h₂.2]
    · exact mul_pos_of_neg_of_neg h₁.1 h₂.1
  let u : E4 := (w 0) • v - (v 0) • w
  by_cases h : u=0
  · left
    have hw0 := (mul_ne_zero_iff.mp hprod.ne').2
    refine ⟨v 0/w 0, (div_pos_iff.mpr (mul_pos_iff.mp hprod)), ?_⟩
    have hh : (w 0) • v = (v 0) • w := sub_eq_zero.mp h
    ext i
    have ee := congrArg (fun k : E4 => k i) hh
    change w 0*v i = v 0*w i at ee
    change v i = v 0/w 0*w i
    field_simp [hw0]
    linarith
  · right
    have hu0 : u 0 = 0 := by simp [u, smul_eq_mul, mul_comm]
    have hpos : 0 < F x.val u u := by
      by_contra! hle
      have hsq := spatial_squares x hf u hle
      rw [hu0] at hsq
      apply h
      ext i
      fin_cases i
      · exact hu0
      · change u 1=0
        apply sq_eq_zero_iff.mp
        nlinarith only [hsq, sq_nonneg (u 1), sq_nonneg (u 2), sq_nonneg (u 3)]
      · change u 2=0
        apply sq_eq_zero_iff.mp
        nlinarith only [hsq, sq_nonneg (u 1), sq_nonneg (u 2), sq_nonneg (u 3)]
      · change u 3=0
        apply sq_eq_zero_iff.mp
        nlinarith only [hsq, sq_nonneg (u 1), sq_nonneg (u 2), sq_nonneg (u 3)]
    let A := F x.val
    have hsym : A w v = A v w := by
      change G x w v = G x v w
      rw [metric_formula, metric_formula]; ring
    change 0 < A ((w 0) • v - (v 0) • w) ((w 0) • v - (v 0) • w) at hpos
    simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, hsym] at hpos
    by_contra! hn
    change 0 ≤ A v w at hn
    nlinarith only [hpos, mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (w 0)) hv.2.1,
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (v 0)) hw.2.1, mul_nonneg hprod.le hn]

structure Arc where
  pos : ℝ → E4
  vel : ℝ → E4
  hasDeriv : ∀ s, HasDerivAt pos (vel s) s
  continuous_vel : Continuous vel

theorem Arc.smooth (P : Arc) : ContDiff ℝ 1 P.pos := by
  have he : deriv P.pos = P.vel := funext fun s => (P.hasDeriv s).deriv
  exact contDiff_one_iff_deriv.mpr ⟨fun s => (P.hasDeriv s).differentiableAt,he ▸ P.continuous_vel⟩

private def Arc.reparam (P : Arc) (f d : ℝ → ℝ) (hd : ∀ s, HasDerivAt f (d s) s)
    (hc : Continuous d) : Arc where
  pos := fun t => P.pos (f t)
  vel := fun t => d t • P.vel (f t)
  hasDeriv s := (P.hasDeriv (f s)).scomp s (hd s)
  continuous_vel := hc.smul (P.continuous_vel.comp (continuous_iff_continuousAt.mpr fun s => (hd s).continuousAt))

private def Arc.affine (P : Arc) (c b : ℝ) : Arc :=
  P.reparam (fun s => c*(s-b)) (fun _ => c) (fun s => by
    simpa using (((hasDerivAt_id s).sub_const b).const_mul c)) continuous_const

def join (c : ℝ) (P Q : Arc) (hp : P.pos c=Q.pos c) (hv : P.vel c=Q.vel c) : Arc where
  pos := fun s => if s ≤ c then P.pos s else Q.pos s
  vel := fun s => if s ≤ c then P.vel s else Q.vel s
  continuous_vel := continuous_if_le continuous_id continuous_const P.continuous_vel.continuousOn
    Q.continuous_vel.continuousOn (fun _ he => he ▸ hv)
  hasDeriv s := by
    rcases lt_trichotomy s c with h|rfl|h
    · rw [if_pos h.le]
      apply (P.hasDeriv s).congr_of_eventuallyEq
      filter_upwards [eventually_lt_nhds h] with t ht using if_pos ht.le
    · rw [if_pos le_rfl]
      apply hasDerivWithinAt_univ.mp
      rw [← Iic_union_Ici (a := s)]
      apply HasDerivWithinAt.union
      · exact (P.hasDeriv s).hasDerivWithinAt.congr_of_mem (fun t ht => if_pos ht) (Set.mem_Iic.mpr (le_refl s))
      · rw [hv]
        apply (Q.hasDeriv s).hasDerivWithinAt.congr_of_mem _ (Set.mem_Ici.mpr (le_refl s))
        intro t ht
        by_cases hs : t ≤ s
        · have he : t=s := le_antisymm hs ht
          simpa [he] using hp
        · exact if_neg hs
    · rw [if_neg h.not_ge]
      apply (Q.hasDeriv s).congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds h] with t ht using if_neg ht.not_ge

def fromCurve  (γ : ℝ → U) (hc : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ) : Arc :=
  let hval : ContMDiff I4 I4 1 (Subtype.val : U → E4) := contMDiff_subtype_val
  let h : ContDiff ℝ 1 (Subtype.val ∘ γ) := (hval.comp hc).contDiff
  ⟨Subtype.val ∘ γ,deriv (Subtype.val ∘ γ),fun s => (h.differentiable (by simp) s).hasDerivAt,
    h.continuous_deriv le_rfl⟩

theorem fromCurve_good  (T : VecField (U)) (γ : ℝ → U)
    (hγ : IsFutureCausalCurveIn (G) T (D) γ) (s : ℝ) (hs : s∈J) :
    Good T ((fromCurve γ hγ.1).pos s) ((fromCurve γ hγ.1).vel s) := by
  let P := fromCurve γ hγ.1
  have he := ambient_velocity γ hγ.1 s (P.vel s) (P.hasDeriv s)
  change Good T (γ s).val (P.vel s)
  rw [← he]
  obtain ⟨hx,_,hv,ht⟩ := hγ.2 s hs
  change F (γ s).val (velocity γ s:E4) (T (γ s):E4)<0 at ht
  exact ⟨hx,hv,by rw [W_on]; exact ht⟩

private theorem realize  (T : VecField (U)) (P : Arc) (L : ℝ) (hL : 0<L)
    (p q : U) (h0 : P.pos 0=p.val) (h1 : P.pos L=q.val) (hU : ∀ s, P.pos s∈U)
    (hg : ∀ s ∈ Icc (0:ℝ) L, Good T (P.pos s) (P.vel s)) :
    q∈causalFuture (G) T (D) p := by
  let γ (s : ℝ) : U := ⟨P.pos (L*s),hU _⟩
  have hc : ContDiff ℝ 1 (Subtype.val ∘ γ) := P.smooth.comp (contDiff_const.mul contDiff_id)
  have hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ := by
    intro s
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff γ univ s).mp (hc.contMDiff s)
  refine Or.inr ⟨γ,⟨hγ,?_⟩,Subtype.ext (by simpa [γ] using h0),Subtype.ext (by simpa [γ] using h1)⟩
  intro s hs
  have hls : L*s∈Icc (0:ℝ) L := ⟨mul_nonneg hL.le hs.1,by simpa using mul_le_mul_of_nonneg_left hs.2 hL.le⟩
  have h := good_scale T (hg _ hls) hL
  have hd : HasDerivAt (fun t => (γ t).val) (L • P.vel (L*s)) s :=
    (P.hasDeriv (L*s)).scomp s (by simpa using (hasDerivAt_id s).const_mul L)
  have he := ambient_velocity γ hγ s _ hd
  have htg : G (γ s) (velocity γ s) (T (γ s)) < 0 := by
    change F (γ s).val (velocity γ s : E4) (T (γ s) : E4) < 0
    rw [he, ← W_on T (γ s)]
    exact h.2.2
  refine ⟨h.1,?_,?_,htg⟩
  · intro hh
    simp [hh] at htg
  · change F (γ s).val (velocity γ s : E4) (velocity γ s : E4) ≤ 0
    rw [he]
    exact h.2.1

def middleTime (d s : ℝ) := (s-(1-d))/(2*d)
def middle (d : ℝ) (hd : 0<d) (P Q : Arc) (y : E4) : Arc where
  pos s := let u := middleTime d s; P.pos (1-d*(1-u)^2)+Q.pos (d*u^2)-y
  vel s := let u := middleTime d s; (1-u) • P.vel (1-d*(1-u)^2) + u • Q.vel (d*u^2)
  continuous_vel := by
    have h := P.continuous_vel
    have h' := Q.continuous_vel
    unfold middleTime
    fun_prop
  hasDeriv s := by
    let u := middleTime d
    have hu : HasDerivAt u (1/(2*d)) s := by
      change HasDerivAt (fun t : ℝ => (t-(1-d))/(2*d)) (1/(2*d)) s
      exact ((hasDerivAt_id s).sub_const (1-d)).div_const (2*d)
    have hα : HasDerivAt (fun t => 1-d*(1-u t)^2) (1-u s) s := by
      have h := (((hu.const_sub 1).pow 2).const_mul d).const_sub 1
      apply h.congr_deriv
      field_simp [hd.ne'] <;> ring
    have hβ : HasDerivAt (fun t => d*(u t)^2) (u s) s := by
      have h := (hu.pow 2).const_mul d
      apply h.congr_deriv
      field_simp [hd.ne'] <;> ring
    exact (((P.hasDeriv _).scomp s hα).add ((Q.hasDeriv _).scomp s hβ)).sub_const y

private theorem use_join (c : ℝ) (P Q : Arc) (h : P.pos c=Q.pos c) (h' : P.vel c=Q.vel c)
    (s : ℝ) (R : E4→E4→Prop) (hL : s ≤ c → R (P.pos s) (P.vel s))
    (hR : c ≤ s → R (Q.pos s) (Q.vel s)) :
    R ((join c P Q h h').pos s) ((join c P Q h h').vel s) := by
  by_cases hs : s ≤ c
  · simpa [join,hs] using hL hs
  · simpa [join,hs] using hR (le_of_not_ge hs)

theorem combine_parallel  (T : VecField (U)) (P Q : Arc) (p x q : U)
    (h0 : P.pos 0=p.val) (h1 : P.pos 1=x.val) (g0 : Q.pos 0=x.val) (g1 : Q.pos 1=q.val)
    (pU : ∀ s, P.pos s∈U) (qU : ∀ s, Q.pos s∈U)
    (pG : ∀ s∈J, Good T (P.pos s) (P.vel s)) (qG : ∀ s∈J, Good T (Q.pos s) (Q.vel s))
    (c : ℝ) (hc : 0<c) (he : P.vel 1=c • Q.vel 0) : q∈causalFuture (G) T (D) p := by
  let B := Q.affine c 1
  have hj : P.pos 1=B.pos 1 := by simpa [B,Arc.affine,Arc.reparam,g0] using h1
  have hv : P.vel 1=B.vel 1 := by simpa [B,Arc.affine,Arc.reparam] using he
  let A := join 1 P B hj hv
  let L := 1+1/c
  have hL : 1<L := by dsimp [L]; linarith [one_div_pos.mpr hc]
  have hlast : c*(L-1)=1 := by dsimp [L]; field_simp [hc.ne'] <;> ring
  apply realize T A L (by linarith) p q
  · simpa [A,join] using h0
  · simpa [A,join,hL.not_ge,B,Arc.affine,Arc.reparam,hlast] using g1
  · intro s
    apply use_join 1 P B hj hv s (fun z _ => z∈U) (fun _ => pU s) (fun _ => qU _)
  · intro s hs
    apply use_join 1 P B hj hv s (Good T) (fun ht => pG s ⟨hs.1,ht⟩)
    intro ht
    apply good_scale T _ hc
    apply qG _ ⟨mul_nonneg hc.le (sub_nonneg.mpr ht),?_⟩
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hs.2 1) hc.le).trans_eq hlast

theorem combine_round  
    (T : VecField (U)) (P Q : Arc) (p x q : U)
    (h0 : P.pos 0=p.val) (h1 : P.pos 1=x.val) (g0 : Q.pos 0=x.val) (g1 : Q.pos 1=q.val)
    (pU : ∀ s, P.pos s∈U) (qU : ∀ s, Q.pos s∈U)
    (pG : ∀ s∈J, Good T (P.pos s) (P.vel s)) (qG : ∀ s∈J, Good T (Q.pos s) (Q.vel s))
    (d : ℝ) (hd : 0<d) (hd1 : d<1)
    (hmid : ∀ u∈J,
      let s := 1-d*(1-u)^2
      let t := d*u^2
      Good T (P.pos s+Q.pos t-x.val) ((1-u) • P.vel s + u • Q.vel t)) :
    q∈causalFuture (G) T (D) p := by
  let M := middle d hd P Q x.val
  let B := Q.affine 1 1
  have hleft : middleTime d (1-d)=0 := by simp [middleTime]
  have hright : middleTime d (1+d)=1 := by unfold middleTime; field_simp [hd.ne']; ring
  have hj : P.pos (1-d)=M.pos (1-d) := by
    change P.pos (1-d) = P.pos (1-d*(1-middleTime d (1-d))^2)+Q.pos (d*middleTime d (1-d)^2)-x.val
    rw [hleft]
    simp [g0]
  have hv : P.vel (1-d)=M.vel (1-d) := by simp [M,middle,hleft]
  let A := join (1-d) P M hj hv
  have hlt : 1-d < 1+d := by linarith
  have hj' : A.pos (1+d)=B.pos (1+d) := by simp [A,join,hlt.not_ge,M,middle,hright,h1,B,Arc.affine,Arc.reparam]
  have hv' : A.vel (1+d)=B.vel (1+d) := by simp [A,join,hlt.not_ge,M,middle,hright,B,Arc.affine,Arc.reparam]
  let path := join (1+d) A B hj' hv'
  have hmg (s : ℝ) (hl : 1-d ≤ s) (hr : s ≤ 1+d) : Good T (M.pos s) (M.vel s) := by
    apply hmid (middleTime d s)
    constructor
    · exact div_nonneg (sub_nonneg.mpr hl) (by positivity)
    · apply (div_le_iff₀ (by positivity : 0<2*d)).mpr
      linarith
  have hdu {z : E4} (h : z∈exterior) : z∈U := h
  apply realize T path 2 (by norm_num) p q
  · simpa [path,A,join,show (0:ℝ) ≤ 1+d by linarith,show (0:ℝ) ≤ 1-d by linarith] using h0
  · simpa [path,join,show ¬ (2:ℝ) ≤ 1+d by linarith,B,Arc.affine,Arc.reparam,show (2:ℝ)-1=1 by norm_num] using g1
  · intro s
    apply use_join _ A B hj' hv' s (fun z _ => z∈U) _ (fun _ => qU _)
    intro hr
    exact use_join _ P M hj hv s (fun z _ => z∈U) (fun _ => pU _) (fun hl => hdu (hmg s hl hr).1)
  · intro s hs
    apply use_join _ A B hj' hv' s (Good T)
    · intro hr
      apply use_join _ P M hj hv s (Good T) _ (fun hl => hmg s hl hr)
      intro hl
      exact pG s ⟨hs.1,by linarith⟩
    · intro hl
      have hJ : s-1∈J := ⟨by linarith,by linarith [hs.2]⟩
      simpa [B,Arc.affine,Arc.reparam] using qG (s-1) hJ



private def patch (P Q : Arc) (y : E4) (k : ℝ×ℝ) : E4 := P.pos k.1 + Q.pos k.2-y
private abbrev corner := ((1:ℝ),(0:ℝ))

private abbrev CornerBilin := E4 → E4 →L[ℝ] E4 →L[ℝ] ℝ
private def Okay (S : Set E4) (g : CornerBilin) (O : E4→E4) (z v : E4) :=
  z∈S ∧ g z v v ≤ 0 ∧ g z v (O z) < 0
private def SmoothAt (g : CornerBilin) (y : E4) := ∀ v w : E4,
  ContDiffAt ℝ 1 (fun k : E4×E4×E4 => g k.1 k.2.1 k.2.2) (y,v,w)

private def OrientedNear (S : Set E4) (g : CornerBilin) (O : E4→E4) (P Q : Arc) (y : E4) (c : ℝ) (k : ℝ×ℝ) :=
  let z := patch P Q y k
  z∈S ∧
    g z (P.vel k.1) (O z) < 0 ∧ g z (Q.vel k.2) (O z) < 0 ∧
    g z (P.vel k.1) (Q.vel k.2) ≤ -c

private def MetricError (g : CornerBilin) (P Q : Arc) (y : E4) (C : ℝ) (k : ℝ×ℝ) :=
  let z := patch P Q y k
  let v := P.vel k.1
  let w := Q.vel k.2
  g z v v - g (P.pos k.1) v v ≤ C*|k.2| ∧
    g z w w - g (Q.pos k.2) w w ≤ C*|k.1-1|

private theorem orientation_near (S : Set E4) (g : CornerBilin) (O : E4→E4) (y : E4) (hdoc : IsOpen S) (hg : SmoothAt g y) (hw : ContinuousAt O y) (P Q : Arc) (hp : P.pos 1=y) (hq : Q.pos 0=y)
    (hP : ∀ s∈J, Okay S g O (P.pos s) (P.vel s)) (hQ : ∀ s∈J, Okay S g O (Q.pos s) (Q.vel s))
    (hcross : g y (P.vel 1) (Q.vel 0) < 0) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ k in 𝓝 corner, OrientedNear S g O P Q y c k := by
  let A := P.vel 1
  let B := Q.vel 0
  let c := -(g y A B)/2
  have hc : 0<c := by dsimp [c,A,B]; linarith only [hcross]
  have ha := hP 1 (right_mem_Icc.mpr zero_le_one)
  have hb := hQ 0 (left_mem_Icc.mpr zero_le_one)
  rw [hp] at ha
  rw [hq] at hb
  let l : Filter (ℝ×ℝ) := 𝓝 ((1:ℝ),(0:ℝ))
  let Z := patch P Q y
  let v (k : ℝ×ℝ) := P.vel k.1
  let w (k : ℝ×ℝ) := Q.vel k.2
  have pL : Tendsto (fun k : ℝ×ℝ => P.pos k.1) l (𝓝 y) := by
    simpa only [l,←hp,Function.comp_apply,Function.comp_def] using (P.smooth.continuous.comp continuous_fst).tendsto ((1:ℝ),(0:ℝ))
  have qL : Tendsto (fun k : ℝ×ℝ => Q.pos k.2) l (𝓝 y) := by
    simpa only [l,←hq,Function.comp_apply,Function.comp_def] using (Q.smooth.continuous.comp continuous_snd).tendsto ((1:ℝ),(0:ℝ))
  have zL : Tendsto Z l (𝓝 y) := by
    have hz : Z = (fun k : ℝ×ℝ => P.pos k.1 + Q.pos k.2 - y) := funext (fun _ => rfl)
    rw [hz]
    simpa only [add_sub_cancel_right,add_sub_cancel_left] using (pL.add qL).sub (tendsto_const_nhds (x:=y) (f:=l))
  have vL : Tendsto v l (𝓝 A) := (P.continuous_vel.comp continuous_fst).tendsto ((1:ℝ),(0:ℝ))
  have wL : Tendsto w l (𝓝 B) := (Q.continuous_vel.comp continuous_snd).tendsto ((1:ℝ),(0:ℝ))
  have tL : Tendsto (fun k => O (Z k)) l (𝓝 (O y)) := hw.tendsto.comp zL
  have ev {V V' : (ℝ×ℝ)→E4} {b b' : E4} (h : Tendsto V l (𝓝 b)) (h' : Tendsto V' l (𝓝 b')) :
      Tendsto (fun k => g (Z k) (V k) (V' k)) l (𝓝 (g y b b')) :=
    (hg b b').continuousAt.tendsto.comp (zL.prodMk_nhds (h.prodMk_nhds h'))
  have hcx : g y A B < -c := by dsimp [c,A,B]; linarith only [hcross]
  have hd : ∀ᶠ k in l, Z k∈S := zL (hdoc.mem_nhds ha.1)
  have h1 : ∀ᶠ k in l, g (Z k) (v k) (O (Z k))<0 := (ev vL tL).eventually_lt_const ha.2.2
  have h2 : ∀ᶠ k in l, g (Z k) (w k) (O (Z k))<0 := (ev wL tL).eventually_lt_const hb.2.2
  have h3 : ∀ᶠ k in l, g (Z k) (v k) (w k) < -c := (ev vL wL).eventually_lt_const hcx
  refine ⟨c,hc,?_⟩
  filter_upwards [hd,h1,h2,h3] with k hk h1 h2 h3 using ⟨hk,h1,h2,h3.le⟩

private theorem metric_error_near (g : CornerBilin) (y : E4) (hg : SmoothAt g y) (P Q : Arc) (hp : P.pos 1=y) (hq : Q.pos 0=y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in 𝓝 corner, MetricError g P Q y C k := by
  let A := P.vel 1
  let B := Q.vel 0
  let l : Filter (ℝ×ℝ) := 𝓝 ((1:ℝ),(0:ℝ))
  let Z := patch P Q y
  let v (k : ℝ×ℝ) := P.vel k.1
  let w (k : ℝ×ℝ) := Q.vel k.2
  have pL : Tendsto (fun k : ℝ×ℝ => P.pos k.1) l (𝓝 y) := by
    simpa only [l,←hp,Function.comp_apply,Function.comp_def] using (P.smooth.continuous.comp continuous_fst).tendsto ((1:ℝ),(0:ℝ))
  have qL : Tendsto (fun k : ℝ×ℝ => Q.pos k.2) l (𝓝 y) := by
    simpa only [l,←hq,Function.comp_apply,Function.comp_def] using (Q.smooth.continuous.comp continuous_snd).tendsto ((1:ℝ),(0:ℝ))
  have zL : Tendsto Z l (𝓝 y) := by
    have hz : Z = (fun k : ℝ×ℝ => P.pos k.1 + Q.pos k.2 - y) := funext (fun _ => rfl)
    rw [hz]
    simpa only [add_sub_cancel_right,add_sub_cancel_left] using (pL.add qL).sub (tendsto_const_nhds (x:=y) (f:=l))
  have vL : Tendsto v l (𝓝 A) := (P.continuous_vel.comp continuous_fst).tendsto ((1:ℝ),(0:ℝ))
  have wL : Tendsto w l (𝓝 B) := (Q.continuous_vel.comp continuous_snd).tendsto ((1:ℝ),(0:ℝ))
  let H (p : E4×E4) := g p.1 p.2 p.2
  have qsm (b : E4) : ContDiffAt ℝ 1 H (y,b) :=
    (hg b b).comp (f:=fun k : E4×E4 => (k.1,k.2,k.2)) (y,b) (contDiffAt_fst.prodMk (contDiffAt_snd.prodMk contDiffAt_snd))
  obtain ⟨K₁,S₁,hS₁,hK₁⟩ := (qsm A).exists_lipschitzOnWith
  obtain ⟨K₂,S₂,hS₂,hK₂⟩ := (qsm B).exists_lipschitzOnWith
  obtain ⟨L₁,V₁,hV₁,hL₁⟩ := (P.smooth.contDiffAt (x:=1)).exists_lipschitzOnWith
  obtain ⟨L₂,V₂,hV₂,hL₂⟩ := (Q.smooth.contDiffAt (x:=0)).exists_lipschitzOnWith
  let C : ℝ := max ((K₁:ℝ)*L₂) ((K₂:ℝ)*L₁)
  have hC : 0 ≤ C := (mul_nonneg K₁.2 L₂.2).trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  filter_upwards [(zL.prodMk_nhds vL) hS₁,(pL.prodMk_nhds vL) hS₁,(zL.prodMk_nhds wL) hS₂,
    (qL.prodMk_nhds wL) hS₂,(continuous_fst.tendsto corner) hV₁,
    (continuous_snd.tendsto corner) hV₂] with k h1 h2 h3 h4 h5 h6
  constructor
  · have hx := hK₁.dist_le_mul _ h1 _ h2
    have hh := hL₂.dist_le_mul _ h6 0 (mem_of_mem_nhds hV₂)
    rw [dist_prod_same_right, Real.dist_eq] at hx
    rw [Real.dist_eq,sub_zero,hq] at hh
    have he : dist (Z k) (P.pos k.1) = dist (Q.pos k.2) y := by
      simp only [Z,patch,dist_eq_norm]
      congr 1
      abel
    rw [he] at hx
    calc
      _ ≤ |H (Z k,v k)-H (P.pos k.1,v k)| := le_abs_self _
      _ ≤ _ := hx
      _ ≤ (K₁:ℝ)*((L₂:ℝ)*|k.2|) := mul_le_mul_of_nonneg_left hh K₁.2
      _ ≤ C*|k.2| := by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
  · have hx := hK₂.dist_le_mul _ h3 _ h4
    have hh := hL₁.dist_le_mul _ h5 1 (mem_of_mem_nhds hV₁)
    rw [dist_prod_same_right, Real.dist_eq] at hx
    rw [Real.dist_eq,hp] at hh
    have he : dist (Z k) (Q.pos k.2) = dist (P.pos k.1) y := by
      simp only [Z,patch,dist_eq_norm]
      congr 1
      abel
    rw [he] at hx
    calc
      _ ≤ |H (Z k,w k)-H (Q.pos k.2,w k)| := le_abs_self _
      _ ≤ _ := hx
      _ ≤ (K₂:ℝ)*((L₁:ℝ)*|k.1-1|) := mul_le_mul_of_nonneg_left hh K₂.2
      _ ≤ C*|k.1-1| := by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)

private theorem round_window (S : Set E4) (g : CornerBilin) (O : E4→E4) (y : E4) (hdoc : IsOpen S) (hg : SmoothAt g y) (hw : ContinuousAt O y)
    (symm : ∀ z v w, g z v w = g z w v) (P Q : Arc) (hp : P.pos 1=y) (hq : Q.pos 0=y)
    (hP : ∀ s∈J, Okay S g O (P.pos s) (P.vel s)) (hQ : ∀ s∈J, Okay S g O (Q.pos s) (Q.vel s))
    (hcross : g y (P.vel 1) (Q.vel 0) < 0) :
    ∃ d : ℝ, 0 < d ∧ d<1 ∧ ∀ u∈J,
      let s := 1-d*(1-u)^2
      let t := d*u^2
      Okay S g O (P.pos s+Q.pos t-y) ((1-u) • P.vel s + u • Q.vel t) := by
  let Z := patch P Q y
  obtain ⟨c,hc,ho⟩ := orientation_near S g O y hdoc hg hw P Q hp hq hP hQ hcross
  obtain ⟨C,hC,he⟩ := metric_error_near g y hg P Q hp hq
  have near : ∀ᶠ k in 𝓝 corner, OrientedNear S g O P Q y c k ∧ MetricError g P Q y C k := ho.and he
  obtain ⟨r,hr,hrset⟩ := Metric.mem_nhds_iff.mp near
  have hCp : 0<C+1 := by linarith
  obtain ⟨d,hd,hdmax⟩ := exists_between (lt_min (lt_min hr zero_lt_one) (div_pos hc hCp))
  obtain ⟨hdr,hd1⟩ := lt_min_iff.mp (lt_min_iff.mp hdmax).1
  have hCd : C*d ≤ c := by
    have h := (lt_div_iff₀ hCp).mp (lt_min_iff.mp hdmax).2
    nlinarith only [h,hd]
  refine ⟨d,hd,hd1,?_⟩
  intro u hu
  let b := 1-u
  let s := 1-d*b^2
  let t := d*u^2
  have hb0 : 0 ≤ b := sub_nonneg.mpr hu.2
  have hb1 : b ≤ 1 := by dsimp [b]; linarith [hu.1]
  have hu2 : u^2 ≤ 1 := by nlinarith only [mul_nonneg hu.1 (sub_nonneg.mpr hu.2), hu.2]
  have hb2 : b^2 ≤ 1 := by nlinarith only [mul_nonneg hb0 (sub_nonneg.mpr hb1), hb1]
  have hs : s∈J := by
    constructor <;> dsimp [s]
    · linarith only [mul_le_mul_of_nonneg_left hb2 hd.le,hd1]
    · linarith only [mul_nonneg hd.le (sq_nonneg b)]
  have ht : t∈J := ⟨mul_nonneg hd.le (sq_nonneg u),by dsimp [t]; linarith only [mul_le_mul_of_nonneg_left hu2 hd.le,hd1]⟩
  have hm : (s,t)∈Metric.ball ((1:ℝ),(0:ℝ)) r := by
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff,Real.dist_eq,Real.dist_eq,sub_zero,
      abs_of_nonpos (sub_nonpos.mpr hs.2),abs_of_nonneg ht.1]
    constructor
    · dsimp [s]; linarith only [mul_le_mul_of_nonneg_left hb2 hd.le,hdr]
    · dsimp [t]; linarith only [mul_le_mul_of_nonneg_left hu2 hd.le,hdr]
  obtain ⟨hOr,hEr⟩ := hrset hm
  obtain ⟨hD,horA,horB,hmix⟩ := hOr
  obtain ⟨heA,heB⟩ := hEr
  let z := Z (s,t)
  let M := g z
  let V := P.vel s
  let V' := Q.vel t
  change M V (O z)<0 at horA
  change M V' (O z)<0 at horB
  change M V V' ≤ -c at hmix
  change M V V - g (P.pos s) V V ≤ C*|t| at heA
  change M V' V' - g (Q.pos t) V' V' ≤ C*|s-1| at heB
  rw [abs_of_nonneg ht.1] at heA
  rw [abs_of_nonpos (sub_nonpos.mpr hs.2)] at heB
  have hA : M V V ≤ C*d*u^2 := by dsimp [t] at heA; nlinarith only [heA,(hP s hs).2.1]
  have hB : M V' V' ≤ C*d*b^2 := by dsimp [s] at heB; nlinarith only [heB,(hQ t ht).2.1]
  have hsym : M V' V = M V V' := symm z V' V
  change Okay S g O z (b • V + u • V')
  refine ⟨hD,?_,?_⟩
  · change M (b • V + u • V') (b • V + u • V') ≤ 0
    simp only [map_add,map_smul,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,hsym]
    have hbu := mul_nonneg hb0 hu.1
    have hbu1 : b*u ≤ 1 := (mul_le_mul_of_nonneg_left hu.2 hb0).trans (by simpa using hb1)
    have hsmall : C*d*(b*u) ≤ c := (mul_le_mul_of_nonneg_left hbu1 (mul_nonneg hC hd.le)).trans (by simpa using hCd)
    nlinarith only [mul_le_mul_of_nonneg_left hA (sq_nonneg b),mul_le_mul_of_nonneg_left hB (sq_nonneg u),
      mul_le_mul_of_nonneg_left hmix hbu, mul_nonpos_of_nonneg_of_nonpos hbu (sub_nonpos.mpr hsmall)]
  · change M (b • V + u • V') (O z)<0
    simp only [map_add,map_smul,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    by_cases h : u=0
    · simpa [b,h] using horA
    · exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos hb0 horA.le)
        (mul_neg_of_pos_of_neg (lt_of_le_of_ne hu.1 (Ne.symm h)) horB)

theorem transitive (T : VecField U) (hT : IsTimeOrientation G T) :
    ∀ p ∈ D, ∀ x ∈ D, ∀ q ∈ D,
      x ∈ causalFuture G T D p → q ∈ causalFuture G T D x → q ∈ causalFuture G T D p := by
  intro p _ x _ q _ h1 h2
  rcases h1 with hid|⟨α,ha,ha0,ha1⟩
  · rcases mem_singleton_iff.mp hid with rfl
    exact h2
  rcases h2 with hid|⟨β,hb,hb0,hb1⟩
  · rcases mem_singleton_iff.mp hid with rfl
    exact Or.inr ⟨α,ha,ha0,ha1⟩
  let P := fromCurve α ha.1
  let Q := fromCurve β hb.1
  have p0 : P.pos 0=p.val := congrArg Subtype.val ha0
  have p1 : P.pos 1=x.val := congrArg Subtype.val ha1
  have q0 : Q.pos 0=x.val := congrArg Subtype.val hb0
  have q1 : Q.pos 1=q.val := congrArg Subtype.val hb1
  have pG := fromCurve_good T α ha
  have qG := fromCurve_good T β hb
  have ha' : Good T x.val (P.vel 1) := p1 ▸ pG 1 (right_mem_Icc.mpr zero_le_one)
  have hb' : Good T x.val (Q.vel 0) := q0 ▸ qG 0 (left_mem_Icc.mpr zero_le_one)
  rcases directions T hT x (P.vel 1) (Q.vel 0) ha' hb' with ⟨c,hc,he⟩|hn
  · exact combine_parallel T P Q p x q p0 p1 q0 q1 (fun s => (α s).property)
      (fun s => (β s).property) pG qG c hc he
  · obtain ⟨d,hd,hd1,hmid⟩ := round_window (exterior) (F) (W T) x.val
      openS (fun b b' => eval_smooth x.val b b' x.property)
      (W_cont T hT x) (fun z v w => by change F z v w = F z w v; unfold F; simp only [matrix_eval]; simp only [isotropicMetric,Matrix.diagonal_apply]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; by_cases hij : i=j <;> simp [hij,Ne.symm]; ring)
      P Q p1 q0 pG qG hn
    exact combine_round T P Q p x q p0 p1 q0 q1 (fun s => (α s).property)
      (fun s => (β s).property) pG qG d hd hd1 hmid

end
end NoHair.TwoCentre.StaticCausality

open NoHair NoHair.TwoCentre Set Filter
open OAI.WeakMTWGlobalSupport OAI.WeakMTWGlobalSupport.CoordinateGeometry
open OAI.WeakMTWGlobalSupport.NormalNeighborhood NoHair.PseudoNormal
open scoped ContDiff Manifold BigOperators Topology
namespace NoHair.TwoCentre.StaticCausality
noncomputable section
private theorem sign_on_interval (f : ℝ → ℝ) (hf : Continuous f)
    (hn : ∀ t ∈ Icc (0 : ℝ) 1, f t ≠ 0) (u v : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    0 < f u ↔ 0 < f v := by
  have imp (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hp : 0 < f s) :
      0 < f t := by
    by_contra! h
    obtain ⟨z, hz, he⟩ := isPreconnected_Icc.intermediate_value ht hs hf.continuousOn
      (show (0:ℝ) ∈ Icc (f t) (f s) from ⟨h,hp.le⟩)
    exact hn z hz he
  exact ⟨imp u v hu hv, imp v u hv hu⟩



private theorem monotone_from_deriv (f d : ℝ → ℝ) (hd : ∀ s, HasDerivAt f (d s) s)
    (h : ∀ s ∈ J, 0 ≤ d s) : MonotoneOn f J := by
  have hf : Differentiable ℝ f := fun s => (hd s).differentiableAt
  exact monotoneOn_of_deriv_nonneg (convex_Icc (0:ℝ) 1) hf.continuous.continuousOn hf.differentiableOn
    (fun s hs => (hd s).deriv.symm ▸ h s (interior_subset hs))


private theorem arc_displacement  
    (T : VecField (U)) (hT : IsTimeOrientation (G) T) (γ : ℝ → U)
    (hγ : IsFutureCausalCurveIn (G) T (D) γ) (s : ℝ) (hs : s∈J) :
    dist (γ s) (γ 0) ≤ 2*|(γ 1).val 0-(γ 0).val 0| := by
  let f : ℝ → E4 := Subtype.val ∘ γ
  let v (t : ℝ) : E4 := velocity γ t
  have hval : ContMDiff I4 I4 1 (Subtype.val : U → E4) := contMDiff_subtype_val
  have hf : ContDiff ℝ 1 f := (hval.comp hγ.1).contDiff
  have hd (t : ℝ) : fderiv ℝ f t = (mfderiv 𝓘(ℝ, ℝ) I4 γ t : ℝ →L[ℝ] E4) := by
    have h := mfderiv_comp t (hval.mdifferentiableAt (by simp) (x := γ t)) (hγ.1.mdifferentiableAt (by simp))
    have hinc : (mfderiv I4 I4 (Subtype.val : U → E4) (γ t) : E4 →L[ℝ] E4) =
        ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := γ t)
    rw [hinc] at h
    rw [← mfderiv_eq_fderiv]
    exact h
  have hc (i : Fin 4) : ContDiff ℝ 1 (fun t => f t i) := (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hf
  have hder (i : Fin 4) (t : ℝ) : HasDerivAt (fun s => f s i) (v t i) t := by
    have h := ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp t ((hf.differentiable (by simp) t).hasFDerivAt)).hasDerivAt
    rw [hd] at h
    exact h
  have hcone (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (∀ i, |v t i| ≤ |v t 0|) ∧ 0 < (v t 0) * timeComponent (T (γ t)) := by
    obtain ⟨hx,hne,hvv,hvw⟩ := hγ.2 t ht
    exact cone_estimates (γ t) (exterior_profile _ hx)
      (v t) (T (γ t)) hne hvv hvw (hT.2 _)
  have hne (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : v t 0 ≠ 0 := by
    have h := (hcone t ht).2
    intro he
    rw [he, zero_mul] at h
    exact (lt_irrefl _) h
  have hcont : Continuous (fun t => v t 0) := by
    have he : (fun t => v t 0) = deriv (fun t => f t 0) := funext (fun t => (hder 0 t).deriv.symm)
    rw [he]
    exact (hc 0).continuous_deriv le_rfl
  let o : ℝ := if 0 < v 0 0 then 1 else -1
  have ho : o=1 ∨ o= -1 := by unfold o; split <;> simp
  have h₀ : (0:ℝ) ∈ J := left_mem_Icc.mpr zero_le_one
  have h₁ : (1:ℝ) ∈ J := right_mem_Icc.mpr zero_le_one
  have hsign (s : ℝ) (hs : s ∈ J) : 0 < o*v s 0 := by
    have he := sign_on_interval (fun t => v t 0) hcont hne 0 s h₀ hs
    unfold o
    split_ifs with h
    · simpa using he.mp h
    · have hh : v s 0 < 0 := lt_of_le_of_ne (le_of_not_gt (fun h' => h (he.mpr h'))) (hne s hs)
      simpa using hh
  have hmag (s : ℝ) (hs : s ∈ J) : |v s 0| = o*v s 0 := by
    have hh := abs_of_pos (hsign s hs)
    rw [abs_mul] at hh
    rcases ho with h|h <;> simpa [h] using hh
  have htmono : MonotoneOn (fun s => o*f s 0) J :=
    monotone_from_deriv _ _ (fun s => (hder 0 s).const_mul o) (fun s hs => (hsign s hs).le)
  have ht01 := htmono h₀ h₁ zero_le_one
  change o*f 0 0 ≤ o*f 1 0 at ht01
  have hclock : o*(f 1 0-f 0 0) = |f 1 0-f 0 0| := by
    rcases ho with h|h <;> rw [h] at ht01 ⊢
    · rw [abs_of_nonneg (by linarith : 0 ≤ f 1 0-f 0 0)]; ring
    · rw [abs_of_nonpos (by linarith : f 1 0-f 0 0 ≤ 0)]; ring
  have hcoords (i : Fin 4) : |f s i-f 0 i| ≤ |f 1 0-f 0 0| := by
    have hplus : MonotoneOn (fun s => o*f s 0+f s i) J :=
      monotone_from_deriv _ _ (fun s => ((hder 0 s).const_mul o).add (hder i s)) (fun s hs => by
        have h := (hcone s hs).1 i
        rw [hmag s hs] at h
        linarith [neg_abs_le (v s i)])
    have hminus : MonotoneOn (fun s => o*f s 0-f s i) J :=
      monotone_from_deriv _ _ (fun s => ((hder 0 s).const_mul o).sub (hder i s)) (fun s hs => by
        have h := (hcone s hs).1 i
        rw [hmag s hs] at h
        linarith [le_abs_self (v s i)])
    have ha := hplus h₀ hs hs.1
    have hb := hminus h₀ hs hs.1
    have hc := htmono hs h₁ hs.2
    beta_reduce at ha hb hc
    change |f s i-f 0 i| ≤ |f 1 0-f 0 0|
    rw [← hclock]
    exact abs_le.mpr ⟨by nlinarith only [ha,hc],by nlinarith only [hb,hc]⟩
  let B := |f 1 0-f 0 0|
  have hb : 0 ≤ B := abs_nonneg _
  have hsq (i : Fin 4) : (f s i-f 0 i)^2 ≤ B^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb).mpr (hcoords i)
  change ‖f s-f 0‖ ≤ 2*B
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
  change (f s 0-f 0 0)^2+(f s 1-f 0 1)^2+(f s 2-f 0 2)^2+(f s 3-f 0 3)^2 ≤ _
  nlinarith only [hsq 0,hsq 1,hsq 2,hsq 3]

theorem restrict_arc  (T : VecField (U)) (K : Set (U)) (γ : ℝ → U)
    (hγ : IsFutureCausalCurveIn (G) T K γ) (l h : ℝ) (hl : 0≤l) (hh : 0<h) (hlh : l+h≤1) :
    IsFutureCausalCurveIn (G) T K (fun s => γ (l+h*s)) := by
  let φ (s : ℝ) := l+h*s
  have hφ : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) 1 φ := contMDiff_iff_contDiff.mpr (by dsimp [φ]; fun_prop)
  refine ⟨hγ.1.comp hφ,?_⟩
  intro s hs
  have hi : φ s ∈ J := ⟨by dsimp [φ]; linarith [mul_nonneg hh.le hs.1],by dsimp [φ]; nlinarith only [hlh,mul_le_mul_of_nonneg_left hs.2 hh.le]⟩
  obtain ⟨hK,hn,hvv,hvT⟩ := hγ.2 (φ s) hi
  have dφ : HasDerivAt φ h s := by simpa [φ] using (((hasDerivAt_id s).const_mul h).const_add l)
  have hvel : (velocity (γ ∘ φ) s : E4) = h • (velocity γ (φ s) : E4) := by
    unfold velocity
    rw [mfderiv_comp s (hγ.1.mdifferentiableAt (by simp)) (hφ.mdifferentiableAt (by simp)),mfderiv_eq_fderiv]
    change mfderiv 𝓘(ℝ,ℝ) I4 γ (φ s) (fderiv ℝ φ s 1) = _
    rw [show fderiv ℝ φ s 1 = h from dφ.deriv]
    let L : ℝ →L[ℝ] E4 := mfderiv 𝓘(ℝ,ℝ) I4 γ (φ s)
    change L h = h • L 1
    simpa only [smul_eq_mul,mul_one] using L.map_smul h (1:ℝ)
  let A := matrixBilin (isotropicMetric (γ (φ s)).val)
  let v : E4 := velocity γ (φ s)
  let w : E4 := T (γ (φ s))
  change v ≠ 0 at hn
  change A v v ≤ 0 at hvv
  change A v w < 0 at hvT
  refine ⟨hK,?_⟩
  change (velocity (γ ∘ φ) s : E4) ≠ 0 ∧ A (velocity (γ ∘ φ) s) (velocity (γ ∘ φ) s) ≤ 0 ∧
    A (velocity (γ ∘ φ) s) w<0
  rw [hvel]
  change (h • v : E4) ≠ 0 ∧ A (h • v) (h • v) ≤ 0 ∧ A (h • v) w < 0
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
  exact ⟨smul_ne_zero hh.ne' hn,mul_nonpos_of_nonneg_of_nonpos hh.le (mul_nonpos_of_nonneg_of_nonpos hh.le hvv),
    mul_neg_of_pos_of_neg hh hvT⟩

private def composeRel {X : Type*} (A : Set (X × X)) : Set (X × X) := {z | ∃ x, (z.1,x)∈A ∧ (x,z.2)∈A}

private theorem compact_composition {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set (X × X)}
    (hA : IsCompact A) : IsCompact (composeRel A) := by
  let S : Set ((X×X)×(X×X)) := {z | z.1.2=z.2.1}
  have hs : IsClosed S := isClosed_eq (continuous_snd.comp continuous_fst) (continuous_fst.comp continuous_snd)
  let F (z : (X×X)×(X×X)) := (z.1.1,z.2.2)
  have e : composeRel A = F '' ((A ×ˢ A) ∩ S) := by
    ext z
    constructor
    · rintro ⟨x,h1,h2⟩
      exact ⟨((z.1,x),(x,z.2)),⟨⟨h1,h2⟩,rfl⟩,rfl⟩
    · rintro ⟨⟨⟨p,x⟩,⟨y,q⟩⟩,⟨⟨hx,hy⟩,h⟩,rfl⟩
      change x=y at h
      subst y
      exact ⟨x,hx,hy⟩
  rw [e]
  exact ((hA.prod hA).inter_right hs).image ((continuous_fst.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd))

private def shortRel  (T : VecField (U)) (K : Set (U)) (d : ℝ) : Set (U × U) :=
  {z | z.1∈K ∧ z.2∈K ∧ z.2∈causalFuture (G) T K z.1 ∧ |z.2.val 0-z.1.val 0|≤d}

private theorem bisect  (T : VecField (U)) (K : Set (U)) (d : ℝ) (hd : 0≤d) :
    shortRel T K (2*d) ⊆ composeRel (shortRel T K d) := by
  rintro ⟨p,q⟩ ⟨hp,hq,hj,hlen⟩
  by_cases hshort : |q.val 0-p.val 0|≤d
  · exact ⟨p,⟨hp,hp,Or.inl rfl,by simpa⟩,⟨hp,hq,hj,hshort⟩⟩
  rcases hj with he|⟨γ,hγ,h0,h1⟩
  · have hqp : q = p := Set.mem_singleton_iff.mp he
    exact (hshort (by simpa [hqp] using hd)).elim
  let t (s : ℝ) := (γ s).val 0
  have hc : Continuous t := (PiLp.continuous_apply 2 _ 0).comp (continuous_subtype_val.comp hγ.1.continuous)
  have hne : t 0 ≠ t 1 := by
    intro h
    change (γ 0).val 0 = (γ 1).val 0 at h
    rw [h0,h1] at h
    change p.val 0 = q.val 0 at h
    exact hshort (by rw [h,sub_self,abs_zero]; exact hd)
  let mid := (t 0+t 1)/2
  have hmid : mid ∈ t '' J := by
    rcases le_total (t 0) (t 1) with h|h
    · apply intermediate_value_Icc zero_le_one hc.continuousOn
      exact ⟨by dsimp [mid]; linarith,by dsimp [mid]; linarith⟩
    · apply intermediate_value_Icc' zero_le_one hc.continuousOn
      exact ⟨by dsimp [mid]; linarith,by dsimp [mid]; linarith⟩
  obtain ⟨s,hs,he⟩ := hmid
  have hs0 : 0<s := lt_of_le_of_ne hs.1 (fun h => by
    subst s; dsimp [mid] at he; apply hne; linarith)
  have hs1 : s<1 := lt_of_le_of_ne hs.2 (fun h => by
    subst s; dsimp [mid] at he; apply hne; linarith)
  have hsK := (hγ.2 s hs).1
  have hγa := restrict_arc T K γ hγ 0 s le_rfl hs0 (by linarith)
  have hγb := restrict_arc T K γ hγ s (1-s) hs.1 (by linarith) (by linarith)
  have hpq : |t 1-t 0| ≤ 2*d := by simpa only [t,h0,h1] using hlen
  have hhalf : |(t 1-t 0)/2| ≤ d := by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith
  have ha : t s-t 0=(t 1-t 0)/2 := by rw [he]; dsimp [mid]; ring
  have hb : t 1-t s=(t 1-t 0)/2 := by rw [he]; dsimp [mid]; ring
  refine ⟨γ s,⟨hp,hsK,Or.inr ⟨_,hγa,by simpa using h0,by simp⟩,?_⟩,
    ⟨hsK,hq,Or.inr ⟨_,hγb,by simp,by convert h1 using 2 <;> ring⟩,?_⟩⟩
  · rw [← h0]; change |t s-t 0|≤d; rwa [ha]
  · rw [← h1]; change |t 1-t s|≤d; rwa [hb]

theorem compact_limit (T : VecField U) (hT : IsTimeOrientation G T) :
    ∀ K : Set U, IsCompact K → K ⊆ D →
      closure {z : U × U | z.1 ∈ K ∧ z.2 ∈ K ∧ z.2 ∈ causalFuture G T K z.1} ⊆
        {z : U × U | z.2 ∈ causalFuture G T D z.1} := by
  intro K hK hKD
  let R := shortRel T K
  let JD : Set (U × U) := {z | z.2 ∈ causalFuture (G) T (D) z.1}
  have hloc (x : K) := local_closure T hT x.val (hKD x.property)
  choose V hOpen hContain hDom hLocal using hloc
  have hc : K ⊆ ⋃ x : K, V x := fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hContain ⟨x,hx⟩⟩
  obtain ⟨δ,hδ,hLeb⟩ := lebesgue_number_lemma_of_metric hK hOpen hc
  let d := δ/8
  have hd : 0<d := by dsimp [d]; linarith
  have hcompact (b : ℝ) : IsCompact (closure (R b)) := (hK.prod hK).of_isClosed_subset isClosed_closure
    (closure_minimal (fun z hz => ⟨hz.1,hz.2.1⟩) (hK.isClosed.prod hK.isClosed))
  have hinside (b : ℝ) : closure (R b) ⊆ K ×ˢ K := closure_minimal (fun z hz => ⟨hz.1,hz.2.1⟩) (hK.isClosed.prod hK.isClosed)
  have hbase : closure (R d) ⊆ JD := by
    intro z hz
    obtain ⟨x,hx⟩ := hLeb z.1 (hinside d hz).1
    have hdist : ∀ y∈R d, dist y.2 y.1 ≤ 2*d := by
      rintro y ⟨_,_,hJ,ht⟩
      rcases hJ with he|⟨γ,hγ,h0,h1⟩
      · rw [Set.mem_singleton_iff.mp he,dist_self]; linarith
      · have hg : IsFutureCausalCurveIn (G) T (D) γ :=
          ⟨hγ.1,fun s hs => ⟨hKD (hγ.2 s hs).1,(hγ.2 s hs).2⟩⟩
        have h := arc_displacement T hT γ hg 1 (right_mem_Icc.mpr zero_le_one)
        rw [h0,h1] at h; linarith
    have hs : dist z.2 z.1 ≤ 2*d := (closure_minimal (show R d ⊆ {y | dist y.2 y.1 ≤ 2*d} from hdist)
      (isClosed_le (continuous_snd.dist continuous_fst) continuous_const)) hz
    have hpx : z.1∈V x := hx (Metric.mem_ball_self hδ)
    have hqx : z.2∈V x := hx (show dist z.2 z.1<δ by dsimp [d] at hs; linarith)
    apply hLocal x z hpx hqx
    let N : Set (U × U) := {y | dist y.1 z.1 < d}
    have ho : IsOpen N := (Metric.isOpen_ball.preimage continuous_fst)
    have hzn : z ∈ N := by change dist z.1 z.1<d; simpa
    apply closure_mono _ (ho.inter_closure ⟨hzn,hz⟩)
    rintro y ⟨hy,hyR⟩
    change dist y.1 z.1<d at hy
    have near (v : U) (hv : dist v y.1 ≤ 2*d) : v∈V x := hx (by
      change dist v z.1<δ
      have := dist_triangle v y.1 z.1
      dsimp [d] at hv hy
      linarith)
    refine ⟨near y.1 (by rw [dist_self]; linarith),near y.2 (hdist y hyR),?_⟩
    rcases hyR.2.2.1 with he|⟨γ,hγ,h0,h1⟩
    · exact Or.inl he
    · refine Or.inr ⟨γ,⟨hγ.1,?_⟩,h0,h1⟩
      intro t ht
      have hg : IsFutureCausalCurveIn (G) T (D) γ :=
        ⟨hγ.1,fun s hs => ⟨hKD (hγ.2 s hs).1,(hγ.2 s hs).2⟩⟩
      have hh := arc_displacement T hT γ hg t ht
      rw [h0,h1] at hh
      exact ⟨near _ (by linarith [hyR.2.2.2]),(hγ.2 t ht).2⟩
  have hdyadic (n : ℕ) : closure (R ((2:ℝ)^n*d)) ⊆ JD := by
    induction n with
    | zero => simpa using hbase
    | succ n ih =>
      let b := (2:ℝ)^n*d
      have hsup : closure (R (2*b)) ⊆ composeRel (closure (R b)) := by
        apply closure_minimal _ (compact_composition (hcompact b)).isClosed
        intro z hz
        obtain ⟨x,hx,hy⟩ := bisect T K b (by dsimp [b]; positivity) hz
        exact ⟨x,subset_closure hx,subset_closure hy⟩
      intro z hz
      have he : (2:ℝ)^(n+1)*d=2*b := by dsimp [b]; ring
      rw [he] at hz
      obtain ⟨x,hx,hy⟩ := hsup hz
      exact transitive T hT z.1 (hKD (hinside b hx).1)
        x (hKD (hinside b hx).2) z.2 (hKD (hinside b hy).2) (ih hx) (ih hy)
  have hct : Continuous (fun z : U => |z.val 0|) := by fun_prop
  obtain ⟨M,hM⟩ := hK.bddAbove_image hct.abs.continuousOn
  have bound (x : U) (hx : x∈K) : |x.val 0|≤M := by
    simpa using hM (show |(|x.val 0|)| ∈ (fun z : U => |(|z.val 0|)|) '' K from ⟨x,hx,rfl⟩)
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (2*M/d) (by norm_num : (1:ℝ)<2)
  apply (closure_mono ?_).trans (hdyadic n)
  rintro z ⟨h1,h2,hj⟩
  refine ⟨h1,h2,hj,?_⟩
  have ht := (div_lt_iff₀ hd).mp hn
  linarith [abs_sub (z.2.val 0) (z.1.val 0),bound z.1 h1,bound z.2 h2]

end
end NoHair.TwoCentre.StaticCausality

open NoHair NoHair.TwoCentre Set Filter
open scoped ContDiff Manifold Topology
namespace NoHair.TwoCentre.StaticCausality
noncomputable section

theorem arc_between (T : VecField U) {γ : ℝ → U}
    (hg : IsFutureCausalCurveIn G T D γ) (t : ℝ) (ht : t∈J) :
    γ t ∈ causalFuture G T D (γ 0) ∧ γ 1 ∈ causalFuture G T D (γ t) := by
  constructor
  · rcases eq_or_lt_of_le ht.1 with h|h
    · rw [←h];exact Or.inl rfl
    · have H := restrict_arc T D γ hg 0 t le_rfl h (by linarith [ht.2])
      exact Or.inr ⟨_,H,by simp,by simp⟩
  · rcases eq_or_lt_of_le ht.2 with h|h
    · rw [h];exact Or.inl rfl
    · have H := restrict_arc T D γ hg t (1-t) ht.1 (by linarith) (by linarith)
      exact Or.inr ⟨_,H,by simp,by simp⟩

theorem compact_of_trapped (T : VecField U) (hT : IsTimeOrientation G T) (p q : U)
    (K : Set U) (hc : IsCompact K) (hs : causalFuture G T D p ∩ causalPast G T D q ⊆ K) :
    IsCompact (causalFuture G T D p ∩ causalPast G T D q) := by
  let A := causalFuture G T D p ∩ causalPast G T D q
  let R := {z : U × U | z.1∈K ∧ z.2∈K ∧ z.2∈causalFuture G T K z.1}
  have tr {a b c : U} := transitive T hT a a.property b b.property c c.property
  have inside {z : U} (hz : z ∈ A) : (p,z) ∈ R ∧ (z,q) ∈ R := by
    have hZ : z∈causalFuture G T D p := hz.1
    have hQ : q∈causalFuture G T D z := hz.2
    have hPQ := tr hZ hQ
    have hpK : p∈K := hs ⟨Or.inl rfl,hPQ⟩
    have hqK : q∈K := hs ⟨hPQ,Or.inl rfl⟩
    constructor
    · refine ⟨hpK,hs hz,?_⟩
      rcases hZ with eq|⟨γ,hγ,h0,h1⟩
      · exact Or.inl eq
      · refine Or.inr ⟨γ,⟨hγ.1,?_⟩,h0,h1⟩
        intro s ht
        obtain ⟨ha,hb⟩ := arc_between T hγ s ht
        rw [h0] at ha;rw [h1] at hb
        exact ⟨hs ⟨ha,tr hb hQ⟩,(hγ.2 s ht).2⟩
    · refine ⟨hs hz,hqK,?_⟩
      rcases hQ with eq|⟨γ,hγ,h0,h1⟩
      · exact Or.inl eq
      · refine Or.inr ⟨γ,⟨hγ.1,?_⟩,h0,h1⟩
        intro s ht
        obtain ⟨ha,hb⟩ := arc_between T hγ s ht
        rw [h0] at ha;rw [h1] at hb
        exact ⟨hs ⟨tr hZ ha,hb⟩,(hγ.2 s ht).2⟩
  have hlim := compact_limit T hT K hc (fun x _ => x.property)
  apply hc.of_isClosed_subset _ hs
  apply closure_subset_iff_isClosed.mp
  intro z hz
  have h1 : Continuous (fun u : U => (p,u)) := continuous_const.prodMk continuous_id
  have h2 : Continuous (fun u : U => (u,q)) := continuous_id.prodMk continuous_const
  exact ⟨hlim (MapsTo.closure (fun _ hu => (inside hu).1) h1 hz),
    hlim (MapsTo.closure (fun _ hu => (inside hu).2) h2 hz)⟩

end
end NoHair.TwoCentre.StaticCausality

open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Topology
open scoped ContDiff Manifold RealInnerProductSpace

namespace NoHair.TwoCentre.Model.Curves

noncomputable section

def radialSpeed (z : E4) (w : E4) : ℝ := ⟪angularDirection z, spatial w⟫

theorem spatial_inner (w v : E4) :
    ⟪spatial w, spatial v⟫ = w 1 * v 1 + w 2 * v 2 + w 3 * v 3 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, spatial]
  ring

theorem radialSpeed_coords (z w : E4) :
    radialSpeed z w = dr z 1 * w 1 + dr z 2 * w 2 + dr z 3 * w 3 := by
  unfold radialSpeed
  rw [← Model.spatial_coordinates 0 (angularDirection z), spatial_inner]
  rfl

theorem metric_eval (z : manifold) (v w : E4) :
    metric z v w =
    Advanced.gvv (parameters z) * v 0 * w 0
    + Advanced.gvr (parameters z) * (v 0 * radialSpeed z w + radialSpeed z v * w 0)
    + Advanced.grr (parameters z) * radialSpeed z v * radialSpeed z w
    + Advanced.angularScale (parameters z) / ‖spatial z‖ ^ 2 *
      (⟪spatial v, spatial w⟫ - radialSpeed z v * radialSpeed z w) := by
  change Matrix.toLinearMap₂' ℝ (metricCoeffs z) (WithLp.ofLp v) (WithLp.ofLp w) = _
  rw [Matrix.toLinearMap₂'_apply (R := ℝ) (metricCoeffs z : Matrix (Fin 4) (Fin 4) ℝ) (WithLp.ofLp v) (WithLp.ofLp w), spatial_inner]
  simp only [radialSpeed_coords, Fin.sum_univ_four, smul_eq_mul, metricCoeffs]
  have hd : dr z 0 = 0 := rfl
  simp (config := {decide := true}) [dt, spatialDelta, hd]
  ring

theorem angular_unit (z : manifold) : ‖angularDirection z‖ = 1 := by
  have hz : (3 : ℝ) / 4 < ‖spatial z‖ := z.property.1
  have hpos : 0 < ‖spatial z‖ := by linarith
  rw [angularDirection, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']


end
end NoHair.TwoCentre.Model.Curves


open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter Topology
open scoped ContDiff Manifold RealInnerProductSpace BigOperators

namespace NoHair.TwoCentre.Model.Signals

noncomputable section

theorem spatial_cont : Continuous spatial := by
  have h : ContDiff ℝ ∞ spatial := contDiff_euclidean.2 (fun i => contDiff_piLp_apply (p := 2) (i := i.succ))
  exact h.continuous

theorem outer_open : IsOpen Model.outer := by
  have h : IsOpen outerRegion := (isOpen_lt continuous_const spatial_cont.norm).inter
    (isOpen_ne_fun spatial_cont continuous_const)
  exact h.preimage continuous_subtype_val

theorem outer_subset : outerRegion ⊆ spacetime := by
  intro z hz
  exact ⟨lt_trans (by norm_num) hz.1, hz.2⟩

theorem model_chart_val {y : E4} (hy : y ∈ exterior) :
    (Model.chart y : E4) = toAdvanced y := by
  obtain ⟨_, hmap, _⟩ := Cartesian.exterior_and_frontier.2.1
  simp [Model.chart, outer_subset (hmap hy)]

theorem model_chart_diffeo : IsDiffeoOnto Model.chart exterior Model.outer := by
  obtain ⟨χ, hf, hb, hl, hr, hfs, hbs⟩ := Cartesian.exterior_and_frontier.2.1
  have hm : MapsTo Model.chart exterior Model.outer := by
    intro y hy
    change (Model.chart y : E4) ∈ outerRegion
    rw [model_chart_val hy]
    exact hf hy
  refine ⟨χ ∘ Subtype.val, hm, (fun _ hy => hb hy), ?_, ?_, ?_, ?_⟩
  · intro y hy
    change χ (Model.chart y : E4) = y
    rw [model_chart_val hy, hl hy]
  · intro z hz
    apply Subtype.ext
    exact (model_chart_val (hb hz)).trans (hr hz)
  · intro y hy
    apply (ContMDiffWithinAt.subtypeVal_comp_iff manifold Model.chart exterior y).mp
    exact hfs.congr (fun _ hz => model_chart_val hz) y hy
  · exact hbs.comp (contMDiff_subtype_val.contMDiffOn) (fun _ hz => hz)

theorem exterior_isOpen : IsOpen exterior := by
  have h (c : ℝ) : Continuous (squaredDistance c) := by unfold squaredDistance; fun_prop
  exact (isOpen_lt continuous_const (h (-1))).inter (isOpen_lt continuous_const (h 1))

abbrev L (y : E4) := mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) Model.chart y

theorem L_onto {y : E4} (hy : y ∈ exterior) : Function.Surjective (L y) := by
  obtain ⟨χ, hmap, hinv, hleft, hright, hs, ht⟩ := model_chart_diffeo
  have hx := hmap hy
  have hcomp : (Model.chart ∘ χ) =ᶠ[𝓝 (Model.chart y)] id :=
    Filter.mem_of_superset (outer_open.mem_nhds hx) (fun _ hz => hright hz)
  have hf := ((hs _ (hinv hx)).contMDiffAt (exterior_isOpen.mem_nhds (hinv hx))).mdifferentiableAt (by simp)
  have hi := ((ht _ hx).contMDiffAt (outer_open.mem_nhds hx)).mdifferentiableAt (by simp)
  have hder : mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) (Model.chart ∘ χ) (Model.chart y) =
      ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E4) (Model.chart y)) := hcomp.mfderiv_eq.trans mfderiv_id
  rw [mfderiv_comp _ hf hi, hleft hy] at hder
  intro v
  exact ⟨mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) χ (Model.chart y) v, DFunLike.congr_fun hder v⟩

theorem Upos (y : E4) : 0 < harmonicPotential y := by
  have h (c : ℝ) : 0 ≤ inverseDistance c y := by unfold inverseDistance; positivity
  unfold harmonicPotential
  linarith [h (-1), h 1]

theorem metric_pullback {y : E4} (hy : y ∈ exterior) (v w : E4) :
    metric (Model.chart y) (L y v) (L y w) = -(v 0 * w 0) / harmonicPotential y ^ 2 +
      harmonicPotential y ^ 2 * ⟪spatial v, spatial w⟫ := by
  obtain ⟨_, _, _, _, _, _, _, hmatch⟩ := Model.stationary_geometry
  let B : E4 →L[ℝ] E4 →L[ℝ] ℝ := metric (Model.chart y)
  let A : E4 →L[ℝ] E4 := L y
  have expand (x : E4) : ∑ i, x i • coordBasis i = x := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, coordBasis] using
      (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr x
  have hbas (i j : Fin 4) : B (A (coordBasis i)) (A (coordBasis j)) = isotropicMetric y i j :=
    congrFun (congrFun (hmatch y hy).1 i) j
  change B (A v) (A w) = _
  calc
    _ = B (A (∑ i, v i • coordBasis i)) (A (∑ i, w i • coordBasis i)) := by rw [expand v, expand w]
    _ = _ := by
      simp only [Curves.spatial_inner, Fin.sum_univ_four]
      simp (config := {decide := true}) [hbas, isotropicMetric]
      ring

theorem chart_time {y : E4} (hy : y ∈ exterior) : L y (coordBasis 0) = (coordBasis 0 : E4) := by
  have hreg (s : ℝ) : y + s • coordBasis 0 ∈ exterior := by
    simpa (config := {decide := true}) [exterior, squaredDistance, coordBasis] using hy
  have hs (s : ℝ) : spatial (y + s • coordBasis 0) = spatial y := by ext i; simp [spatial, coordBasis]
  have ht (s : ℝ) : (Model.chart (y + s • coordBasis 0) : E4) = (Model.chart y : E4) + s • coordBasis 0 := by
    rw [model_chart_val (hreg s), model_chart_val hy]
    simp only [toAdvanced, hs]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [coordinates, coordBasis]
      ring
    · simp [coordinates, coordBasis]
  have h0 : y + (0 : ℝ) • coordBasis 0 = y := by simp
  have hγ : HasDerivAt (fun s : ℝ => y + s • coordBasis 0) (coordBasis 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordBasis 0)).const_add y
  have ⟨_, _, _, _, _, smooth, _⟩ := model_chart_diffeo
  let b := Model.chart y
  have hval : HasMFDerivAt 𝓘(ℝ, E4) 𝓘(ℝ, E4) (Subtype.val : manifold → E4) b
      (ContinuousLinearMap.id ℝ E4) := by
    have d : MDifferentiableAt 𝓘(ℝ, E4) 𝓘(ℝ, E4) (Subtype.val : manifold → E4) b :=
      contMDiff_subtype_val.mdifferentiableAt (n := (1 : ℕ∞ω)) one_ne_zero
    have he : mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) (Subtype.val : manifold → E4) b =
        ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := 𝓘(ℝ, E4)) (x := b)
    exact he ▸ d.hasMFDerivAt
  have df : HasFDerivAt (fun z => (Model.chart z : E4)) (L y : E4 →L[ℝ] E4) y :=
    hasMFDerivAt_iff_hasFDerivAt.mp (hval.comp y
      (((smooth y hy).contMDiffAt (exterior_isOpen.mem_nhds hy)).mdifferentiableAt (by simp)).hasMFDerivAt)
  have df0 : HasFDerivAt (fun z => (Model.chart z : E4)) (L y : E4 →L[ℝ] E4) (y + (0 : ℝ) • coordBasis 0) := by rwa [h0]
  have hact := HasFDerivAt.comp_hasDerivAt (l := fun z : E4 => (Model.chart z : E4))
    (f := fun s : ℝ => y + s • coordBasis 0) (0 : ℝ) df0 hγ
  simp only [Function.comp_def] at hact
  have hdes : HasDerivAt (fun s : ℝ => (Model.chart y : E4) + s • coordBasis 0) (coordBasis 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordBasis 0)).const_add (Model.chart y : E4)
  rw [show (fun s : ℝ => (Model.chart (y + s • coordBasis 0) : E4)) = _ from funext ht] at hact
  exact hact.unique hdes

theorem time_orientation_pair (z : manifold) (hz : z ∈ Model.outer) :
    metric z (coordBasis 0) (orientation z) < 0 := by
  let p := parameters z
  have hpr : 0 < p.1 := sub_pos.mpr hz.1
  have hH : 0 < Advanced.H p := by
    have hd : 0 ≤ 1 / Advanced.distanceToOther p := by unfold Advanced.distanceToOther; positivity
    unfold Advanced.H
    nlinarith [mul_nonneg hpr.le (show 0 ≤ 1 + 1 / Advanced.distanceToOther p by linarith)]
  have hH0 : 0 < Advanced.H₀ p := by unfold Advanced.H₀; linarith
  have hvr : 0 < Advanced.gvr p := by unfold Advanced.gvr; positivity
  have hvv : Advanced.gvv p < 0 := div_neg_of_neg_of_pos (neg_lt_zero.mpr (sq_pos_of_pos hpr)) (sq_pos_of_pos hH)
  let a := Advanced.gvr p / (1 + Advanced.grr p ^ 2)
  have ha : 0 < a := by dsimp [a]; positivity
  let T : E4 := orientation z
  have hT : spatial T = -a • angularDirection z := Model.spatial_coordinates _ _
  have hVT : T 0 = 1 := rfl
  have hn : Curves.radialSpeed z T = -a := by
    change ⟪angularDirection z, spatial T⟫ = -a
    rw [hT, real_inner_smul_right, real_inner_self_eq_norm_sq, Curves.angular_unit]
    ring
  have hs0 : spatial (coordBasis 0) = 0 := by ext i; simp [spatial, coordBasis]
  have h0 : Curves.radialSpeed z (coordBasis 0) = 0 := by simp [Curves.radialSpeed, hs0]
  change metric z (coordBasis 0) T < 0
  rw [Curves.metric_eval, hVT, h0, hn, hs0, inner_zero_left]
  change Advanced.gvv p * 1 * 1 + Advanced.gvr p * (1 * -a + 0 * 1) + _ * 0 * -a + _ * (0 - 0 * -a) < 0
  nlinarith [mul_pos ha hvr]

noncomputable def iso : manifold → E4 := Classical.choose model_chart_diffeo
theorem iso_spec :
    MapsTo Model.chart exterior Model.outer ∧ MapsTo iso Model.outer exterior ∧
    LeftInvOn iso Model.chart exterior ∧ RightInvOn iso Model.chart Model.outer ∧
    ContMDiffOn 𝓘(ℝ, E4) 𝓘(ℝ, E4) ∞ Model.chart exterior ∧
    ContMDiffOn 𝓘(ℝ, E4) 𝓘(ℝ, E4) ∞ iso Model.outer := Classical.choose_spec model_chart_diffeo

theorem optical_future {y : E4} (hy : y ∈ exterior) (v : E4)
    (hf : IsFutureCausal metric orientation (Model.chart y) (L y v)) :
    0 < v 0 ∧ harmonicPotential y ^ 2 * ‖spatial v‖ ≤ v 0 := by
  let u := harmonicPotential y
  have hu : 0 < u := Upos y
  have hs0 : spatial (coordBasis 0) = 0 := by ext i; simp [spatial, coordBasis]
  obtain ⟨_, hm, _⟩ := model_chart_diffeo
  obtain ⟨_, _, _, _, hor, _⟩ := Model.stationary_geometry
  obtain ⟨w₀, hw₀⟩ := L_onto hy (orientation (Model.chart y))
  let w : E4 := w₀
  have hw : L y w = orientation (Model.chart y) := hw₀
  have hww := (metric_pullback hy w w).symm.trans_lt (show metric (Model.chart y) (L y w) (L y w) < 0 by
    rw [hw]; exact hor.2 _)
  have hwt := (metric_pullback hy (coordBasis 0) w).symm.trans_lt
    (show metric (Model.chart y) (L y (coordBasis 0)) (L y w) < 0 by
      rw [chart_time hy, hw]; exact time_orientation_pair _ (hm hy))
  rw [hs0, inner_zero_left] at hwt
  have hwpos : 0 < w 0 := by
    change -(1 * w 0) / u ^ 2 + u ^ 2 * 0 < 0 at hwt
    simpa [neg_div, hu.le, div_pos_iff_of_pos_right (sq_pos_of_pos hu)] using hwt
  rw [real_inner_self_eq_norm_sq] at hww
  have bound (a : E4) (hn : -(a 0 * a 0) / u ^ 2 + u ^ 2 * ‖spatial a‖ ^ 2 ≤ 0) :
      u ^ 2 * ‖spatial a‖ ≤ |a 0| := by
    have hsq := (le_div_iff₀ (sq_pos_of_pos hu)).mp (show u ^ 2 * ‖spatial a‖ ^ 2 ≤ (a 0 * a 0) / u ^ 2 by
      rw [neg_div] at hn; linarith)
    nlinarith [sq_abs (a 0), abs_nonneg (a 0), mul_nonneg (sq_nonneg u) (norm_nonneg (spatial a))]
  have hwbound : u ^ 2 * ‖spatial w‖ ≤ w 0 := (abs_of_pos hwpos) ▸ bound w hww.le
  have hvv := (metric_pullback hy v v).symm.trans_le hf.2.1
  rw [real_inner_self_eq_norm_sq] at hvv
  have hvbound := bound v hvv
  have hvpos : 0 < v 0 := by
    by_contra! hvneg
    rw [abs_of_nonpos hvneg] at hvbound
    have hi := (abs_le.mp (abs_real_inner_le_norm (spatial v) (spatial w))).1
    have hp := mul_le_mul hvbound hwbound (mul_nonneg (sq_nonneg u) (norm_nonneg _)) (neg_nonneg.mpr hvneg)
    have hpair := (metric_pullback hy v w).symm.trans_lt (show metric (Model.chart y) (L y v) (L y w) < 0 by
      rw [hw]; exact hf.2.2)
    change -(v 0 * w 0) / u^2 + u^2 * ⟪spatial v, spatial w⟫ < 0 at hpair
    rw [neg_div] at hpair
    have hpair' := (lt_div_iff₀ (sq_pos_of_pos hu)).mp
      (show u ^ 2 * ⟪spatial v, spatial w⟫ < v 0 * w 0 / u ^ 2 by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hi (sq_nonneg (u ^ 2))]
  exact ⟨hvpos, (abs_of_pos hvpos) ▸ hvbound⟩

def isoV (γ : ℝ → manifold) (t : ℝ) : E4 :=
  mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) iso (γ t) (velocity γ t)

set_option backward.isDefEq.respectTransparency false in
theorem lift_causal {γ : ℝ → manifold}
    (h : IsFutureCausalCurveIn metric orientation Model.outer γ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun s => iso (γ s)) (isoV γ t) t ∧ iso (γ t) ∈ exterior ∧
    0 < isoV γ t 0 ∧ harmonicPotential (iso (γ t)) ^ 2 * ‖spatial (isoV γ t)‖ ≤ isoV γ t 0 := by
  obtain ⟨_, hb, _, hr, hs, hi⟩ := iso_spec
  have hz := (h.2 t ht).1
  have hy := hb hz
  have hchi := ((hi _ hz).contMDiffAt (outer_open.mem_nhds hz)).mdifferentiableAt (by simp)
  have hchart := ((hs _ hy).contMDiffAt (exterior_isOpen.mem_nhds hy)).mdifferentiableAt (by simp)
  have hcurve := (h.1.mdifferentiableAt (by simp) (x := t)).hasMFDerivAt
  have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E4) (iso ∘ γ) t
      ((mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) iso (γ t)).comp (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E4) γ t)) :=
    hchi.hasMFDerivAt.comp t hcurve
  have der : HasDerivAt (fun s => iso (γ s)) (isoV γ t) t :=
    (hasMFDerivAt_iff_hasFDerivAt.mp hcomp).hasDerivAt
  have he : (Model.chart ∘ iso) =ᶠ[𝓝 (γ t)] id :=
    Filter.mem_of_superset (outer_open.mem_nhds hz) (fun x hx => hr hx)
  have hD : mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) (Model.chart ∘ iso) (γ t) =
      ContinuousLinearMap.id ℝ E4 := he.mfderiv_eq.trans mfderiv_id
  rw [mfderiv_comp _ hchart hchi] at hD
  have hdv : L (iso (γ t)) (isoV γ t) = velocity γ t := DFunLike.congr_fun hD _
  have hca : IsFutureCausal metric orientation (Model.chart (iso (γ t))) (L (iso (γ t)) (isoV γ t)) := by
    rw [hdv, hr hz]
    exact (h.2 t ht).2
  exact ⟨der,hy,optical_future hy _ hca⟩

def clock (z : manifold) := iso z 0

theorem interval_strict {γ : ℝ → manifold}
    (h : IsFutureCausalCurveIn metric orientation Model.outer γ) :
    StrictMonoOn (fun t => clock (γ t)) (Icc (0 : ℝ) 1) := by
  have hh (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s => clock (γ s)) (isoV γ t 0) t := by
    exact (PiLp.proj (p := 2) (β := fun _ : Fin 4 => ℝ) 0).hasFDerivAt.comp_hasDerivAt t (lift_causal h ht).1
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (fun t ht => (hh t ht).continuousAt.continuousWithinAt)
  intro t ht
  have ht' := interior_subset ht
  rw [(hh t ht').deriv]
  exact (lift_causal h ht').2.2.1

theorem future_clock {p q : manifold} (hq : q ∈ causalFuture metric orientation Model.outer p) :
    clock p ≤ clock q := by
  rcases hq with eq | ⟨γ,h,hs,he⟩
  · exact le_of_eq (congrArg clock eq.symm)
  · have hlt := interval_strict h (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_lt_one
    simpa [hs,he] using hlt.le

theorem spatial_dist (c : ℝ) (y : E4) :
    ‖spatial y - c • unitAxis‖ ^ 2 = squaredDistance c y := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp [spatial, unitAxis, squaredDistance, PiLp.sub_apply, PiLp.smul_apply]

theorem iso_regular (y : E4) :
    y ∈ exterior ↔ spatial y ≠ -unitAxis ∧ spatial y ≠ unitAxis := by
  change 0 < squaredDistance (-1) y ∧ 0 < squaredDistance 1 y ↔ _
  rw [← spatial_dist, ← spatial_dist, neg_one_smul, one_smul]
  simp only [sq_pos_iff, norm_ne_zero_iff, sub_ne_zero]

theorem optical_factor (y : E4) :
    harmonicPotential y = 1 + 1 / ‖spatial y - (-unitAxis)‖ + 1 / ‖spatial y - unitAxis‖ := by
  unfold harmonicPotential inverseDistance
  simp [← spatial_dist, Real.sqrt_sq (norm_nonneg _)]

theorem spatial_deriv {f : ℝ → E4} {v : E4} {t : ℝ} (hd : HasDerivAt f v t) :
    HasDerivAt (fun s => spatial (f s)) (spatial v) t := by
  let A : E4 →L[ℝ] E3 := LinearMap.toContinuousLinearMap {
    toFun := spatial, map_add' := fun _ _ => by ext; rfl, map_smul' := fun _ _ => by ext; rfl }
  exact A.hasFDerivAt.comp_hasDerivAt t hd

theorem time_deriv {f : ℝ → E4} {v : E4} {t : ℝ} (hd : HasDerivAt f v t) :
    HasDerivAt (fun s => f s 0) (v 0) t :=
  (PiLp.proj (p := 2) (β := fun _ : Fin 4 => ℝ) 0).hasFDerivAt.comp_hasDerivAt t hd

theorem join_coords (z : E4) : coordinates (z 0) (spatial z) = z := by
  ext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem coord_cont : Continuous (fun p : ℝ × E3 => coordinates p.1 p.2) := by
  have h : ContDiff ℝ ∞ (fun p : ℝ × E3 => coordinates p.1 p.2) := by
    apply contDiff_euclidean.2
    intro i
    refine Fin.cases (by exact contDiff_fst) (fun j => ?_) i
    simp only [coordinates, WithLp.ofLp_toLp, Fin.cons_succ]
    fun_prop
  exact h.continuous

theorem trapped (p : manifold) (hp : p∈Model.outer) (q : manifold) (hq : q∈Model.outer) :
    ∃ K : Set manifold, IsCompact K ∧ K ⊆ Model.outer ∧
      causalFuture metric orientation Model.outer p ∩ causalPast metric orientation Model.outer q ⊆ K := by
  obtain ⟨_, hback, _, hright, hsm, _⟩ := iso_spec
  let x₀ := spatial (iso p)
  have hreg := (iso_regular (iso p)).mp (hback hp)
  let budget := max 0 (clock q - clock p)
  obtain ⟨K, hc, h₁, h₂, htrap⟩ := optical_confinement (-unitAxis) unitAxis x₀ hreg.1 hreg.2
    budget (le_max_left _ _)
  let box := (Icc (clock p) (clock q)) ×ˢ (insert x₀ K)
  let ψ : ℝ × E3 → manifold := fun u => Model.chart (coordinates u.1 u.2)
  have hcomp : IsCompact box := isCompact_Icc.prod (hc.insert _)
  have hcoords : MapsTo (fun u : ℝ × E3 => coordinates u.1 u.2) box exterior := by
    intro u hu
    rw [iso_regular, Model.spatial_coordinates]
    rcases hu.2 with eq | hm
    · rw [eq]
      exact hreg
    · exact ⟨fun e => h₁ (e ▸ hm),fun e => h₂ (e ▸ hm)⟩
  have hψ : ContinuousOn ψ box := hsm.continuousOn.comp coord_cont.continuousOn hcoords
  refine ⟨ψ '' box,hcomp.image_of_continuousOn hψ,?_,?_⟩
  · rintro _ ⟨u,hu,rfl⟩
    exact iso_spec.1 (hcoords hu)
  · intro z hz
    have htime : clock z ∈ Icc (clock p) (clock q) := ⟨future_clock hz.1, future_clock hz.2⟩
    have hzin : z ∈ Model.outer ∧ spatial (iso z) ∈ insert x₀ K := by
      rcases hz.1 with hzp | ⟨γ,h,hs,he⟩
      · rw [show z = p from hzp]
        exact ⟨hp, mem_insert _ _⟩
      · have hstart : spatial (iso (γ 0)) = x₀ := by rw [hs]
        have hopt (s : ℝ) (hs' : s ∈ Icc (0 : ℝ) 1) :
            HasDerivAt (fun t => spatial (iso (γ t))) (spatial (isoV γ s)) s ∧
            HasDerivAt (fun t => iso (γ t) 0) (isoV γ s 0) s ∧
            spatial (iso (γ s)) ≠ -unitAxis ∧ spatial (iso (γ s)) ≠ unitAxis ∧
            (1 + 1 / ‖spatial (iso (γ s)) - (-unitAxis)‖ + 1 / ‖spatial (iso (γ s)) - unitAxis‖)^2 *
              ‖spatial (isoV γ s)‖ ≤ isoV γ s 0 := by
          obtain ⟨hd,hy,_,hv⟩ := lift_causal h hs'
          exact ⟨spatial_deriv hd,time_deriv hd,(iso_regular _).mp hy |>.1,(iso_regular _).mp hy |>.2,
            (optical_factor _ ▸ hv)⟩
        have htravel : iso (γ 1) 0 - iso (γ 0) 0 ≤ budget := by
          change clock (γ 1) - clock (γ 0) ≤ budget
          rw [he,hs]
          exact (sub_le_sub_right htime.2 _).trans (le_max_right _ _)
        have hend := htrap (fun s => spatial (iso (γ s))) (fun s => spatial (isoV γ s))
          (fun s => iso (γ s) 0) (fun s => isoV γ s 0) hstart hopt 1 (right_mem_Icc.mpr zero_le_one) htravel
        refine ⟨he ▸ (h.2 1 (right_mem_Icc.mpr zero_le_one)).1, Or.inr ?_⟩
        simpa only [he] using hend
    refine ⟨(clock z,spatial (iso z)),⟨htime,hzin.2⟩,?_⟩
    change Model.chart (coordinates (iso z 0) (spatial (iso z))) = z
    rw [join_coords, hright hzin.1]
end
end NoHair.TwoCentre.Model.Signals

open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian NoHair.TwoCentre.Model Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
namespace NoHair.TwoCentre.Model.CausalAtlas
open Signals StaticCausality
noncomputable section
set_option backward.isDefEq.respectTransparency false

def eTime : VecField StaticCausality.U := fun _ => coordBasis 0
theorem mono_time (x : U) (v : E4) : G x v (eTime x) = -(v 0)/harmonicPotential x.val^2 := by
  rw [StaticCausality.metric_formula x v (eTime x)]
  simp (config:={decide:=true}) [eTime,coordBasis]
theorem eTime_oriented : IsTimeOrientation G eTime := by
  constructor
  · apply continuous_iff_continuousAt.mpr;intro z
    apply (FiberBundle.continuousAt_section E4 z).2
    have he (x : U) : (trivializationAt E4 (TangentSpace 𝓘(ℝ,E4)) z
        (⟨x,eTime x⟩ : TangentBundle 𝓘(ℝ,E4) U)).2 = coordBasis 0 := by
      change tangentCoordChange 𝓘(ℝ,E4) x z x (coordBasis 0) = _
      have same : achart E4 z = achart E4 x := by rfl
      unfold tangentCoordChange;rw [same]
      exact (tangentBundleCore 𝓘(ℝ,E4) U).coordChange_self (achart E4 x) x (mem_achart_source E4 x) _
    simp_rw [he];exact continuousAt_const
  · intro x;rw [mono_time x (eTime x)]
    have hu := Signals.Upos x.val
    change -(timeComponent (eTime x)) / harmonicPotential x.val^2 < 0
    have hn : timeComponent (eTime x) = 1 := by simp [timeComponent,eTime,coordBasis]
    rw [hn];exact div_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos hu)

def forward (x : U) := Model.chart x.val
def back (z : manifold) : U := by
  classical
  exact if h : iso z∈exterior then ⟨iso z,h⟩ else ⟨axis 0,by change axis 0 ∈ exterior;norm_num [exterior,axis,squaredDistance,Set.mem_setOf_eq] <;> positivity⟩
theorem back_coe {z : manifold} (hz : z∈Model.outer) : ((back z : U) : E4) = iso z := by
  classical
  unfold back
  simp only [dif_pos (iso_spec.2.1 hz)]
theorem right_inv {z : manifold} (hz : z∈Model.outer) : forward (back z)=z := by
  unfold forward;rw [back_coe hz];exact iso_spec.2.2.2.1 hz
theorem left_inv (x : U) : back (forward x)=x := by
  apply Subtype.ext;exact (back_coe (z:=forward x) (iso_spec.1 x.property)).trans (iso_spec.2.2.1 x.property)

theorem forward_smooth : ContMDiff I4 I4 ∞ forward := by
  intro x
  have h := ((iso_spec.2.2.2.2.1 x.val x.property).contMDiffAt (exterior_isOpen.mem_nhds x.property))
  exact h.comp x (contMDiff_subtype_val.contMDiffAt)
theorem back_smooth (z : manifold) (hz : z∈Model.outer) : ContMDiffAt I4 I4 ∞ back z := by
  apply (ContMDiffAt.subtypeVal_comp_iff U back z).1
  apply ((iso_spec.2.2.2.2.2 z hz).contMDiffAt (outer_open.mem_nhds hz)).congr_of_eventuallyEq
  exact Filter.mem_of_superset (outer_open.mem_nhds hz) (fun y hy => back_coe hy)
theorem forward_der (x:U) : (mfderiv I4 I4 forward x : E4 →L[ℝ] E4) = L x.val := by
  have hf := ((iso_spec.2.2.2.2.1 x.val x.property).contMDiffAt (exterior_isOpen.mem_nhds x.property)).mdifferentiableAt (by simp)
  change mfderiv I4 I4 (Model.chart ∘ (Subtype.val : U → E4)) x = _
  have hv : mfderiv I4 I4 (Subtype.val : U → E4) x = ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I:=I4) (x:=x)
  rw [mfderiv_comp _ hf (contMDiff_subtype_val.mdifferentiableAt (n:=(1:ℕ∞ω)) one_ne_zero),hv]
  rfl

theorem isometric (x:U) (v w:E4) : metric (forward x) (L x.val v) (L x.val w)=G x v w := by
  exact (Signals.metric_pullback x.property v w).trans ((by rw [Curves.spatial_inner] : _ = _).trans (StaticCausality.metric_formula x v w).symm)

theorem causal_iff (x:U) (v:E4) :
    IsFutureCausal metric orientation (forward x) (L x.val v) ↔ IsFutureCausal G eTime x v := by
  have hu := Signals.Upos x.val
  constructor
  · intro h
    have hn : v≠0 := fun he => by have hv := h.1;rw [he,map_zero] at hv;exact hv rfl
    refine ⟨hn, (isometric x v v).symm.trans_le h.2.1,?_⟩
    rw [mono_time x v];exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (optical_future x.property v h).1) (sq_pos_of_pos hu)
  · intro h
    have hv : 0<v 0 := by
      have hi := h.2.2
      change G x v (eTime x)<0 at hi
      have hn := (mono_time x v).symm.trans_lt hi
      by_contra! he;exact (not_lt_of_ge (div_nonneg (neg_nonneg.mpr he) (sq_nonneg _))) hn
    obtain ⟨w,hw⟩ := L_onto x.property (orientation (forward x))
    have hww : G x w w<0 := by
      have hh := (isometric x w w).symm
      rw [hw] at hh
      exact hh.trans_lt (stationary_geometry.2.2.2.2.1.2 (forward x))
    have ht : L x.val (eTime x)=coordBasis 0 := chart_time x.property
    have hpair : G x w (eTime x)<0 := by
      have he := (isometric x (eTime x) w).symm
      rw [hw,ht] at he
      exact (StaticCausality.field_sym x.property w (eTime x)).trans (he) |>.trans_lt
        (time_orientation_pair (forward x) (iso_spec.1 x.property))
    have hwpos : 0 < timeComponent w := by
      have hn := (mono_time x w).symm.trans_lt hpair
      by_contra! he;exact (not_lt_of_ge (div_nonneg (neg_nonneg.mpr he) (sq_nonneg _))) hn
    have orient : metric (forward x) (L x.val v) (orientation (forward x)) < 0 := by
      have he := isometric x v w
      rw [hw] at he
      exact he.trans_lt (StaticCausality.cone_pair_negative x.property h.2.1 hww (mul_pos hv hwpos))
    refine ⟨?_,(isometric x v v).trans_le h.2.1,orient⟩
    intro he;rw [he,map_zero] at orient;exact (lt_irrefl (0:ℝ)) orient

set_option backward.isDefEq.respectTransparency false in
theorem map_future {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace E4 X] [ChartedSpace E4 Y]
    [IsManifold I4 ∞ X] [IsManifold I4 ∞ Y] {A : Set X} {B : Set Y} (hA : IsOpen A)
    {g : BilinField X} {G' : BilinField Y} {T : VecField X} {T' : VecField Y}
    (f : X→Y) (hm : MapsTo f A B) (hs : ∀ x ∈ A, ContMDiffAt I4 I4 ∞ f x)
    (hd : ∀ x ∈ A, ∀ v, IsFutureCausal g T x v → IsFutureCausal G' T' (f x) (mfderiv I4 I4 f x v))
    {p q : X} (h : q∈causalFuture g T A p) : f q∈causalFuture G' T' B (f p) := by
  rcases h with e|⟨γ,hγ,h0,h1⟩
  · exact Or.inl (congrArg f (mem_singleton_iff.mp e))
  let V := γ ⁻¹' A
  have hV : IsOpen V := hA.preimage hγ.1.continuous
  obtain ⟨b,hb,hbV,hbe⟩ := StaticCausality.fit_clock hV zero_lt_one (fun t ht => (hγ.2 t ht).1)
  let c := f ∘ γ ∘ b
  have hbM := hb.contMDiff
  have sm : ContMDiff 𝓘(ℝ,ℝ) I4 1 c := by
    intro t
    exact ((hs _ (hbV t)).of_le (show (1:ℕ∞ω)≤∞ by simp)).comp t ((hγ.1.comp hbM).contMDiffAt)
  have ev (t : ℝ) (ht:t∈J) : c =ᶠ[𝓝 t] (f ∘ γ) := (hbe t ht).fun_comp (f ∘ γ)
  refine Or.inr ⟨c,⟨sm,?_⟩, (ev 0 (left_mem_Icc.mpr zero_le_one)).self_of_nhds.trans (congrArg f h0),
      (ev 1 (right_mem_Icc.mpr zero_le_one)).self_of_nhds.trans (congrArg f h1)⟩
  intro t ht
  have ec := (ev t ht).self_of_nhds
  have dt : (velocity c t : E4) = mfderiv I4 I4 f (γ t) (velocity γ t) := by
    unfold velocity
    rw [(ev t ht).mfderiv_eq, mfderiv_comp t ((hs _ (hγ.2 t ht).1).mdifferentiableAt (by simp)) (hγ.1.mdifferentiableAt (by simp))]
    rfl
  exact ⟨ec ▸ hm (hγ.2 t ht).1, by change IsFutureCausal G' T' (c t) (velocity c t : E4);rw [dt,ec];exact hd _ (hγ.2 t ht).1 _ (hγ.2 t ht).2⟩

theorem forward_future {p q : U} (h : q∈causalFuture G eTime D p) :
    forward q ∈ causalFuture metric orientation Model.outer (forward p) := by
  apply map_future (hA:=openS.preimage continuous_subtype_val) forward (fun x _ => iso_spec.1 x.property)
      (fun x _ => forward_smooth.contMDiffAt) _ h
  intro x _ v hv
  have e : (mfderiv I4 I4 forward x v : E4)=L x.val v := DFunLike.congr_fun (forward_der x) v
  exact e ▸ (causal_iff x v).2 hv

theorem backward_future {p q : manifold} (h : q∈causalFuture metric orientation Model.outer p) :
    back q ∈ causalFuture G eTime D (back p) := by
  apply map_future (hA:=outer_open) back (fun x _ => (back x).property) back_smooth _ h
  intro x hx v hv
  let a := back x
  let w := mfderiv I4 I4 back x v
  have he : (forward ∘ back)=ᶠ[𝓝 x] id := Filter.mem_of_superset (outer_open.mem_nhds hx) (fun z hz => right_inv hz)
  have hd := he.mfderiv_eq (I:=I4) (I':=I4)
  rw [mfderiv_comp _ (forward_smooth.mdifferentiableAt (by simp)) ((back_smooth x hx).mdifferentiableAt (by simp)),mfderiv_id] at hd
  have hw : L a.val w = v := (DFunLike.congr_fun (forward_der a) w).symm.trans (DFunLike.congr_fun hd v)
  apply (causal_iff a w).mp
  rw [hw,show forward a=x from right_inv hx];exact hv

end
end NoHair.TwoCentre.Model.CausalAtlas

open NoHair NoHair.TwoCentre NoHair.TwoCentre.Model Set
open NoHair.TwoCentre.StaticCausality NoHair.TwoCentre.Model.CausalAtlas
open scoped ContDiff Manifold
namespace NoHair.TwoCentre.Model.CausalAtlas
noncomputable section

theorem closed (p : manifold) (hp : p∈Model.outer) (q : manifold) (hq : q∈Model.outer) :
    IsClosed (causalFuture metric orientation Model.outer p ∩ causalPast metric orientation Model.outer q) := by
  let A := causalFuture metric orientation Model.outer p ∩ causalPast metric orientation Model.outer q
  let B := causalFuture G eTime D (back p) ∩ causalPast G eTime D (back q)
  have hmap : MapsTo forward B A := by
    intro z hz
    have h1 := forward_future hz.1
    have h2 := forward_future hz.2
    rw [right_inv hp] at h1;rw [right_inv hq] at h2
    exact ⟨h1,h2⟩
  obtain ⟨K,hK,hKD,hAK⟩ := Signals.trapped p hp q hq
  have hb : ContinuousOn back K := fun z hz => (back_smooth z (hKD hz)).continuousAt.continuousWithinAt
  have hKB : B ⊆ back '' K := by
    intro z hz;exact ⟨forward z,hAK (hmap hz),left_inv z⟩
  have hc := compact_of_trapped eTime eTime_oriented (back p) (back q) (back '' K) (hK.image_of_continuousOn hb) hKB
  have himg : forward '' B = A := by
    apply subset_antisymm (image_subset_iff.mpr hmap)
    intro z hz
    exact ⟨back z,⟨backward_future hz.1,backward_future hz.2⟩,right_inv (hKD (hAK hz))⟩
  change IsClosed A;rw [←himg];exact (hc.image forward_smooth.continuous).isClosed

end
end NoHair.TwoCentre.Model.CausalAtlas
open NoHair NoHair.TwoCentre.Model Set
theorem solution : ∀ p ∈ outer, ∀ q ∈ outer,
    IsClosed (causalFuture metric orientation outer p ∩ causalPast metric orientation outer q) :=
  fun p hp q hq => CausalAtlas.closed p hp q hq
