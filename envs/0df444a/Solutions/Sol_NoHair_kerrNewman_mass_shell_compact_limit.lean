-- Prove2me | solution 1 for NoHair.kerrNewman_mass_shell_compact_limit
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:52:45.042187+00:00
-- url     : https://prove2.me/submissions/3db32018-2084-4718-9080-2a622b4cd629

import Definitions.Def_NoHair_KerrNewmanEinstein_Base
import Definitions.Def_NoHair_PseudoRiemannianNormalCoordinates
import Theorems.Thm_NoHair_kerrNewman_regularTensors

open NoHair Set

abbrev massShell (m a _e : ℝ) : Set E4 := {z | m < ksRadius a z}


open NoHair NoHair.KNE Set Filter
open scoped ContDiff Manifold BigOperators Topology

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 350000

/-! Regular parametrized arcs and rounding of causal corners. Matching first derivatives
give a regular join. For a strict corner the quadratic middle arc matches both endpoint jets. -/
namespace NoHair.MassShellJoining
noncomputable section

abbrev U (a : ℝ) := kerrNewmanSpacetime a
abbrev D (m a e : ℝ) := (Subtype.val : U a → E4) ⁻¹' massShell m a e
private abbrev I4 := 𝓘(ℝ, E4)
abbrev G (m a e : ℝ) := kerrNewmanMetricField m a e
private def timeComponent (v : E4) : ℝ := v 0
def kEval (a : ℝ) (z u : E4) := ∑ i, ksNull a z i * u i

private theorem metric_formula (m a e : ℝ) (x : U a) (v w : E4) :
    G m a e x v w = -(v 0*w 0) + v 1*w 1 + v 2*w 2 + v 3*w 3
      + ksProfile m a e x.val * kEval a x.val v * kEval a x.val w := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric m a e x.val) (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul, kerrNewmanMetric, kEval, Fin.sum_univ_four]
  simp [minkowski] <;> ring

private theorem exterior_profile (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (x : U a) (hx : x ∈ D m a e) : 0 ≤ ksProfile m a e x.val := by
  obtain ⟨hm, he⟩ := hp
  change m < ksRadius a x.val at hx
  have hm' : m ≤ ksRadius a x.val := hx.le
  have hnum : 0 ≤ 2*m*ksRadius a x.val - e^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hm' hm.le, he, sq_nonneg a, sq_nonneg m]
  unfold ksProfile
  exact div_nonneg (mul_nonneg (sq_nonneg _) hnum) (by positivity)

private theorem spatial_squares (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v : E4) (hv : G m a e x v v ≤ 0) :
    (v 1)^2 + (v 2)^2 + (v 3)^2 ≤ (v 0)^2 := by
  rw [metric_formula] at hv
  nlinarith only [hv, mul_nonneg hf (sq_nonneg (kEval a x.val v))]

private theorem spatial_kernel (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v : E4) (h0 : v 0 = 0) : 0 ≤ G m a e x v v := by
  rw [metric_formula, h0]
  nlinarith only [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3),
    mul_nonneg hf (sq_nonneg (kEval a x.val v))]

private theorem cone_estimates (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v w : E4) (hv : v ≠ 0) (hvv : G m a e x v v ≤ 0) (hvw : G m a e x v w < 0)
    (hww : G m a e x w w < 0) :
    (∀ i, |v i| ≤ |v 0|) ∧ 0 < (v 0)*(w 0) := by
  have hs := spatial_squares m a e x hf v hvv
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
  have hkernel := spatial_kernel m a e x hf ((w 0) • v - (v 0) • w)
    (by simp [smul_eq_mul, mul_comm])
  have hsym : G m a e x w v = G m a e x v w := by rw [metric_formula, metric_formula]; ring
  let A := matrixBilin (kerrNewmanMetric m a e x.val)
  change 0 ≤ A ((w 0) • v - (v 0) • w) ((w 0) • v - (v 0) • w) at hkernel
  change A w v = A v w at hsym
  change A w w < 0 at hww
  change A v v ≤ 0 at hvv
  change A v w < 0 at hvw
  simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, hsym] at hkernel
  nlinarith only [hkernel, mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (w 0)) hvv,
    mul_neg_of_pos_of_neg (sq_pos_iff.mpr hv0) hww, mul_nonneg_of_nonpos_of_nonpos hprod hvw.le]

private theorem matrix_eval (A : Matrix (Fin 4) (Fin 4) ℝ) (v w : E4) :
    matrixBilin A v w = ∑ i, ∑ j, v i * (w j * A i j) := by
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul]

private theorem radius_smooth (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    ContDiffAt ℝ ∞ (ksRadius a) z := by
  have hD := (ks_D_pos a z hz).ne'
  have hQ := (ks_Q_pos a z hz).ne'
  rw [ksRadius_eq']
  fun_prop (disch := assumption)

private theorem null_smooth (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => ksNull a w i) z := by
  have hr := radius_smooth a z hz
  have hne : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hne' := hz.ne'
  fin_cases i
  · simp only [Fin.zero_eta, ksNull_zero]; fun_prop
  · simp only [Fin.mk_one, ksNull_one]; fun_prop (disch := assumption)
  · change ContDiffAt ℝ ∞ (fun w => ksNull a w 2) z
    simp only [ksNull_two]; fun_prop (disch := assumption)
  · change ContDiffAt ℝ ∞ (fun w => ksNull a w 3) z
    simp only [ksNull_three]; fun_prop (disch := assumption)

private theorem ambient_velocity (a : ℝ) (γ : ℝ → U a) (hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ)
    (s : ℝ) (v : E4) (hd : HasDerivAt (fun t => (γ t).val) v s) : (velocity γ s : E4) = v := by
  have hval : ContMDiff I4 I4 1 (Subtype.val : U a → E4) := contMDiff_subtype_val
  have hcomp := mfderiv_comp s (hval.mdifferentiableAt (by simp) (x := γ s)) (hγ.mdifferentiableAt (by simp))
  have hinc : (mfderiv I4 I4 (Subtype.val : U a → E4) (γ s) : E4 →L[ℝ] E4) =
      ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := γ s)
  rw [hinc] at hcomp
  have h : fderiv ℝ (fun t => (γ t).val) s = (mfderiv 𝓘(ℝ,ℝ) I4 γ s : ℝ →L[ℝ] E4) := by
    rw [← mfderiv_eq_fderiv]
    exact hcomp
  exact (congrArg (fun A : ℝ →L[ℝ] E4 => A 1) h).symm.trans hd.deriv

abbrev J := Icc (0:ℝ) 1
abbrev F (m a e : ℝ) (z : E4) := matrixBilin (kerrNewmanMetric m a e z)
noncomputable def W (a : ℝ) (T : VecField (U a)) (z : E4) : E4 := by
  classical
  exact if h : z ∈ U a then (T ⟨z,h⟩ : E4) else 0

theorem W_on (a : ℝ) (T : VecField (U a)) (x : U a) :
    W a T x.val = (T x : E4) := by
  classical
  unfold W
  rw [dif_pos x.property]

theorem W_cont (m a e : ℝ) (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T)
    (x : U a) : ContinuousAt (W a T) x.val := by
  apply (U a).isOpen.isOpenEmbedding_subtypeVal.continuousAt_iff.mp
  have h := hT.1.continuousAt (x := x)
  rw [FiberBundle.continuousAt_section] at h
  have htr (y : U a) : (trivializationAt E4 (TangentSpace I4) x ⟨y,T y⟩).2 = (T y : E4) := by
    change tangentCoordChange I4 y y y (T y) = _
    exact tangentCoordChange_self (mem_extChartAt_source y)
  change ContinuousAt (fun y : U a => W a T y.val) x
  rw [show (fun y : U a => W a T y.val) = (fun y : U a => (T y : E4)) from funext (W_on a T)]
  simpa only [htr] using h

theorem eval_smooth (m a e : ℝ) (z v w : E4) (hz : 0 < ksRadius a z) :
    ContDiffAt ℝ 1 (fun k : E4 × E4 × E4 => F m a e k.1 k.2.1 k.2.2) (z,v,w) := by
  have hc (i j : Fin 4) : ContDiffAt ℝ ∞ (fun y => kerrNewmanMetric m a e y i j) z := by
    have hr := radius_smooth a z hz
    have hi := null_smooth a z hz i
    have hj := null_smooth a z hz j
    have hd := (ks_den_pos a z hz).ne'
    unfold kerrNewmanMetric ksProfile
    fun_prop (disch := assumption)
  simp_rw [F, matrix_eval]
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  have hk : ContDiffAt ℝ 1 (fun y : E4 => kerrNewmanMetric m a e y i j) z :=
    (hc i j).of_le (show (1:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hk' := hk.comp (f:=fun k : E4×E4×E4 => k.1) (z,v,w) contDiffAt_fst
  exact (((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt.comp _ (contDiffAt_fst.comp _ contDiffAt_snd))).mul
    ((((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffAt.comp _ (contDiffAt_snd.comp _ contDiffAt_snd))).mul hk')

def Good (m a e : ℝ) (T : VecField (U a)) (z v : E4) : Prop :=
  z ∈ massShell m a e ∧ F m a e z v v ≤ 0 ∧ F m a e z v (W a T z) < 0

private theorem good_scale (m a e : ℝ) (T : VecField (U a)) {z v : E4} (h : Good m a e T z v)
    {c : ℝ} (hc : 0<c) : Good m a e T z (c • v) := by
  obtain ⟨hz,hv,hw⟩ := h
  refine ⟨hz, ?_, ?_⟩
  · simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos hc.le (mul_nonpos_of_nonneg_of_nonpos hc.le hv)
  · simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hc hw

theorem directions (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) (T : VecField (U a))
    (hT : IsTimeOrientation (G m a e) T) (x : U a) (v w : E4)
    (hv : Good m a e T x.val v) (hw : Good m a e T x.val w) :
    (∃ c : ℝ, 0<c ∧ v=c • w) ∨ F m a e x.val v w < 0 := by
  have hf := exterior_profile m a e hp x hv.1
  have vn (h : E4) (hh : Good m a e T x.val h) : h ≠ 0 := by
    intro he
    have hh' := hh.2.2
    simp [he] at hh'
  have ht (h : E4) (hh : Good m a e T x.val h) : 0 < h 0 * timeComponent (T x) := by
    apply (cone_estimates m a e x hf h (T x) (vn h hh) hh.2.1 _ (hT.2 x)).2
    exact (show F m a e x.val h (T x : E4)<0 by simpa only [W_on] using hh.2.2)
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
    have hpos : 0 < F m a e x.val u u := by
      by_contra! hle
      have hsq := spatial_squares m a e x hf u hle
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
    let A := F m a e x.val
    have hsym : A w v = A v w := by
      change G m a e x w v = G m a e x v w
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

def fromCurve {a : ℝ} (γ : ℝ → U a) (hc : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ) : Arc :=
  let hval : ContMDiff I4 I4 1 (Subtype.val : U a → E4) := contMDiff_subtype_val
  let h : ContDiff ℝ 1 (Subtype.val ∘ γ) := (hval.comp hc).contDiff
  ⟨Subtype.val ∘ γ,deriv (Subtype.val ∘ γ),fun s => (h.differentiable (by simp) s).hasDerivAt,
    h.continuous_deriv le_rfl⟩

theorem fromCurve_good (m a e : ℝ) (T : VecField (U a)) (γ : ℝ → U a)
    (hγ : IsFutureCausalCurveIn (G m a e) T (D m a e) γ) (s : ℝ) (hs : s∈J) :
    Good m a e T ((fromCurve γ hγ.1).pos s) ((fromCurve γ hγ.1).vel s) := by
  let P := fromCurve γ hγ.1
  have he := ambient_velocity a γ hγ.1 s (P.vel s) (P.hasDeriv s)
  change Good m a e T (γ s).val (P.vel s)
  rw [← he]
  obtain ⟨hx,_,hv,ht⟩ := hγ.2 s hs
  change F m a e (γ s).val (velocity γ s:E4) (T (γ s):E4)<0 at ht
  exact ⟨hx,hv,by rw [W_on]; exact ht⟩

private theorem realize (m a e : ℝ) (T : VecField (U a)) (P : Arc) (L : ℝ) (hL : 0<L)
    (p q : U a) (h0 : P.pos 0=p.val) (h1 : P.pos L=q.val) (hU : ∀ s, P.pos s∈U a)
    (hg : ∀ s ∈ Icc (0:ℝ) L, Good m a e T (P.pos s) (P.vel s)) :
    q∈causalFuture (G m a e) T (D m a e) p := by
  let γ (s : ℝ) : U a := ⟨P.pos (L*s),hU _⟩
  have hc : ContDiff ℝ 1 (Subtype.val ∘ γ) := P.smooth.comp (contDiff_const.mul contDiff_id)
  have hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ := by
    intro s
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff γ univ s).mp (hc.contMDiff s)
  refine Or.inr ⟨γ,⟨hγ,?_⟩,Subtype.ext (by simpa [γ] using h0),Subtype.ext (by simpa [γ] using h1)⟩
  intro s hs
  have hls : L*s∈Icc (0:ℝ) L := ⟨mul_nonneg hL.le hs.1,by simpa using mul_le_mul_of_nonneg_left hs.2 hL.le⟩
  have h := good_scale m a e T (hg _ hls) hL
  have hd : HasDerivAt (fun t => (γ t).val) (L • P.vel (L*s)) s :=
    (P.hasDeriv (L*s)).scomp s (by simpa using (hasDerivAt_id s).const_mul L)
  have he := ambient_velocity a γ hγ s _ hd
  have htg : G m a e (γ s) (velocity γ s) (T (γ s)) < 0 := by
    change F m a e (γ s).val (velocity γ s : E4) (T (γ s) : E4) < 0
    rw [he, ← W_on a T (γ s)]
    exact h.2.2
  refine ⟨h.1,?_,?_,htg⟩
  · intro hh
    simp [hh] at htg
  · change F m a e (γ s).val (velocity γ s : E4) (velocity γ s : E4) ≤ 0
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

theorem combine_parallel (m a e : ℝ) (T : VecField (U a)) (P Q : Arc) (p x q : U a)
    (h0 : P.pos 0=p.val) (h1 : P.pos 1=x.val) (g0 : Q.pos 0=x.val) (g1 : Q.pos 1=q.val)
    (pU : ∀ s, P.pos s∈U a) (qU : ∀ s, Q.pos s∈U a)
    (pG : ∀ s∈J, Good m a e T (P.pos s) (P.vel s)) (qG : ∀ s∈J, Good m a e T (Q.pos s) (Q.vel s))
    (c : ℝ) (hc : 0<c) (he : P.vel 1=c • Q.vel 0) : q∈causalFuture (G m a e) T (D m a e) p := by
  let B := Q.affine c 1
  have hj : P.pos 1=B.pos 1 := by simpa [B,Arc.affine,Arc.reparam,g0] using h1
  have hv : P.vel 1=B.vel 1 := by simpa [B,Arc.affine,Arc.reparam] using he
  let A := join 1 P B hj hv
  let L := 1+1/c
  have hL : 1<L := by dsimp [L]; linarith [one_div_pos.mpr hc]
  have hlast : c*(L-1)=1 := by dsimp [L]; field_simp [hc.ne'] <;> ring
  apply realize m a e T A L (by linarith) p q
  · simpa [A,join] using h0
  · simpa [A,join,hL.not_ge,B,Arc.affine,Arc.reparam,hlast] using g1
  · intro s
    apply use_join 1 P B hj hv s (fun z _ => z∈U a) (fun _ => pU s) (fun _ => qU _)
  · intro s hs
    apply use_join 1 P B hj hv s (Good m a e T) (fun ht => pG s ⟨hs.1,ht⟩)
    intro ht
    apply good_scale m a e T _ hc
    apply qG _ ⟨mul_nonneg hc.le (sub_nonneg.mpr ht),?_⟩
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hs.2 1) hc.le).trans_eq hlast

theorem combine_round (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (P Q : Arc) (p x q : U a)
    (h0 : P.pos 0=p.val) (h1 : P.pos 1=x.val) (g0 : Q.pos 0=x.val) (g1 : Q.pos 1=q.val)
    (pU : ∀ s, P.pos s∈U a) (qU : ∀ s, Q.pos s∈U a)
    (pG : ∀ s∈J, Good m a e T (P.pos s) (P.vel s)) (qG : ∀ s∈J, Good m a e T (Q.pos s) (Q.vel s))
    (d : ℝ) (hd : 0<d) (hd1 : d<1)
    (hmid : ∀ u∈J,
      let s := 1-d*(1-u)^2
      let t := d*u^2
      Good m a e T (P.pos s+Q.pos t-x.val) ((1-u) • P.vel s + u • Q.vel t)) :
    q∈causalFuture (G m a e) T (D m a e) p := by
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
  have hmg (s : ℝ) (hl : 1-d ≤ s) (hr : s ≤ 1+d) : Good m a e T (M.pos s) (M.vel s) := by
    apply hmid (middleTime d s)
    constructor
    · exact div_nonneg (sub_nonneg.mpr hl) (by positivity)
    · apply (div_le_iff₀ (by positivity : 0<2*d)).mpr
      linarith
  have hdu {z : E4} (h : z∈massShell m a e) : z∈U a := by
    change m < ksRadius a z at h
    change 0<ksRadius a z
    linarith only [h,hp.1,Real.sqrt_nonneg (m^2-a^2-e^2)]
  apply realize m a e T path 2 (by norm_num) p q
  · simpa [path,A,join,show (0:ℝ) ≤ 1+d by linarith,show (0:ℝ) ≤ 1-d by linarith] using h0
  · simpa [path,join,show ¬ (2:ℝ) ≤ 1+d by linarith,B,Arc.affine,Arc.reparam,show (2:ℝ)-1=1 by norm_num] using g1
  · intro s
    apply use_join _ A B hj' hv' s (fun z _ => z∈U a) _ (fun _ => qU _)
    intro hr
    exact use_join _ P M hj hv s (fun z _ => z∈U a) (fun _ => pU _) (fun hl => hdu (hmg s hl hr).1)
  · intro s hs
    apply use_join _ A B hj' hv' s (Good m a e T)
    · intro hr
      apply use_join _ P M hj hv s (Good m a e T) _ (fun hl => hmg s hl hr)
      intro hl
      exact pG s ⟨hs.1,by linarith⟩
    · intro hl
      have hJ : s-1∈J := ⟨by linarith,by linarith [hs.2]⟩
      simpa [B,Arc.affine,Arc.reparam] using qG (s-1) hJ


end
end NoHair.MassShellJoining

open NoHair NoHair.KNE Set Filter
open OAI.WeakMTWGlobalSupport OAI.WeakMTWGlobalSupport.CoordinateGeometry
open OAI.WeakMTWGlobalSupport.NormalNeighborhood NoHair.PseudoNormal
open scoped ContDiff Manifold BigOperators Topology

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 270000

/-! The time and signed-energy tests for regular normal geodesics in the Kerr–Newman exterior. -/
namespace NoHair.MassShellGeodesics
noncomputable section

abbrev U (a : ℝ) := kerrNewmanSpacetime a
abbrev D (m a e : ℝ) := (Subtype.val : U a → E4) ⁻¹' massShell m a e
abbrev I4 := 𝓘(ℝ, E4)
abbrev G (m a e : ℝ) := kerrNewmanMetricField m a e
def timeComponent (v : E4) : ℝ := v 0
private def kEval (a : ℝ) (z u : E4) := ∑ i, ksNull a z i * u i

private theorem metric_formula (m a e : ℝ) (x : U a) (v w : E4) :
    G m a e x v w = -(v 0*w 0) + v 1*w 1 + v 2*w 2 + v 3*w 3
      + ksProfile m a e x.val * kEval a x.val v * kEval a x.val w := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric m a e x.val) (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul, kerrNewmanMetric, kEval, Fin.sum_univ_four]
  simp [minkowski] <;> ring

theorem exterior_profile (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (x : U a) (hx : x ∈ D m a e) : 0 ≤ ksProfile m a e x.val := by
  obtain ⟨hm, he⟩ := hp
  change m < ksRadius a x.val at hx
  have hm' : m ≤ ksRadius a x.val := hx.le
  have hnum : 0 ≤ 2*m*ksRadius a x.val - e^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hm' hm.le, he, sq_nonneg a, sq_nonneg m]
  unfold ksProfile
  exact div_nonneg (mul_nonneg (sq_nonneg _) hnum) (by positivity)

private theorem spatial_squares (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v : E4) (hv : G m a e x v v ≤ 0) :
    (v 1)^2 + (v 2)^2 + (v 3)^2 ≤ (v 0)^2 := by
  rw [metric_formula] at hv
  nlinarith only [hv, mul_nonneg hf (sq_nonneg (kEval a x.val v))]

private theorem spatial_kernel (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v : E4) (h0 : v 0 = 0) : 0 ≤ G m a e x v v := by
  rw [metric_formula, h0]
  nlinarith only [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3),
    mul_nonneg hf (sq_nonneg (kEval a x.val v))]

theorem cone_estimates (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v w : E4) (hv : v ≠ 0) (hvv : G m a e x v v ≤ 0) (hvw : G m a e x v w < 0)
    (hww : G m a e x w w < 0) :
    (∀ i, |v i| ≤ |v 0|) ∧ 0 < (v 0)*(w 0) := by
  have hs := spatial_squares m a e x hf v hvv
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
  have hkernel := spatial_kernel m a e x hf ((w 0) • v - (v 0) • w)
    (by simp [smul_eq_mul, mul_comm])
  have hsym : G m a e x w v = G m a e x v w := by rw [metric_formula, metric_formula]; ring
  let A := matrixBilin (kerrNewmanMetric m a e x.val)
  change 0 ≤ A ((w 0) • v - (v 0) • w) ((w 0) • v - (v 0) • w) at hkernel
  change A w v = A v w at hsym
  change A w w < 0 at hww
  change A v v ≤ 0 at hvv
  change A v w < 0 at hvw
  simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, hsym] at hkernel
  nlinarith only [hkernel, mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (w 0)) hvv,
    mul_neg_of_pos_of_neg (sq_pos_iff.mpr hv0) hww, mul_nonneg_of_nonpos_of_nonpos hprod hvw.le]

private theorem matrix_eval (A : Matrix (Fin 4) (Fin 4) ℝ) (v w : E4) :
    matrixBilin A v w = ∑ i, ∑ j, v i * (w j * A i j) := by
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul]

private theorem radius_smooth (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    ContDiffAt ℝ ∞ (ksRadius a) z := by
  have hD := (ks_D_pos a z hz).ne'
  have hQ := (ks_Q_pos a z hz).ne'
  rw [ksRadius_eq']
  fun_prop (disch := assumption)

private theorem null_smooth (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => ksNull a w i) z := by
  have hr := radius_smooth a z hz
  have hne : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hne' := hz.ne'
  fin_cases i
  · simp only [Fin.zero_eta, ksNull_zero]; fun_prop
  · simp only [Fin.mk_one, ksNull_one]; fun_prop (disch := assumption)
  · change ContDiffAt ℝ ∞ (fun w => ksNull a w 2) z
    simp only [ksNull_two]; fun_prop (disch := assumption)
  · change ContDiffAt ℝ ∞ (fun w => ksNull a w 3) z
    simp only [ksNull_three]; fun_prop (disch := assumption)

theorem ambient_velocity (a : ℝ) (γ : ℝ → U a) (hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ)
    (s : ℝ) (v : E4) (hd : HasDerivAt (fun t => (γ t).val) v s) : (velocity γ s : E4) = v := by
  have hval : ContMDiff I4 I4 1 (Subtype.val : U a → E4) := contMDiff_subtype_val
  have hcomp := mfderiv_comp s (hval.mdifferentiableAt (by simp) (x := γ s)) (hγ.mdifferentiableAt (by simp))
  have hinc : (mfderiv I4 I4 (Subtype.val : U a → E4) (γ s) : E4 →L[ℝ] E4) =
      ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := γ s)
  rw [hinc] at hcomp
  have h : fderiv ℝ (fun t => (γ t).val) s = (mfderiv 𝓘(ℝ,ℝ) I4 γ s : ℝ →L[ℝ] E4) := by
    rw [← mfderiv_eq_fderiv]
    exact hcomp
  exact (congrArg (fun A : ℝ →L[ℝ] E4 => A 1) h).symm.trans hd.deriv

abbrev J := Icc (0:ℝ) 1
abbrev F (m a e : ℝ) (z : E4) := matrixBilin (kerrNewmanMetric m a e z)
noncomputable def W (a : ℝ) (T : VecField (U a)) (z : E4) : E4 := by
  classical
  exact if h : z ∈ U a then (T ⟨z,h⟩ : E4) else 0

theorem W_on (a : ℝ) (T : VecField (U a)) (x : U a) :
    W a T x.val = (T x : E4) := by
  classical
  unfold W
  rw [dif_pos x.property]

theorem W_cont (m a e : ℝ) (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T)
    (x : U a) : ContinuousAt (W a T) x.val := by
  apply (U a).isOpen.isOpenEmbedding_subtypeVal.continuousAt_iff.mp
  have h := hT.1.continuousAt (x := x)
  rw [FiberBundle.continuousAt_section] at h
  have htr (y : U a) : (trivializationAt E4 (TangentSpace I4) x ⟨y,T y⟩).2 = (T y : E4) := by
    change tangentCoordChange I4 y y y (T y) = _
    exact tangentCoordChange_self (mem_extChartAt_source y)
  change ContinuousAt (fun y : U a => W a T y.val) x
  rw [show (fun y : U a => W a T y.val) = (fun y : U a => (T y : E4)) from funext (W_on a T)]
  simpa only [htr] using h

abbrev S (m a e : ℝ) := massShell m a e
theorem openS (m a e : ℝ) : IsOpen (S m a e) := isOpen_lt continuous_const (continuous_ksRadius a)
theorem inU (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) {z : E4}
    (h : z∈S m a e) : z∈U a := by
  change m < ksRadius a z at h
  change 0 < ksRadius a z
  linarith only [hp.1,h,Real.sqrt_nonneg (m^2-a^2-e^2)]

private theorem smooth_scalar_multiple {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → ℝ} {x : X} (hf : ContDiffAt ℝ ∞ f x) (v : Y) :
    ContDiffAt ℝ ∞ (fun z => f z • v) x := hf.smul_const v

set_option backward.defeqAttrib.useBackward true in
theorem field_smooth (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) :
    ContDiffOn ℝ ∞ (F m a e) (S m a e) := by
  let P (i : Fin 4) := EuclideanSpace.proj (𝕜:=ℝ) i
  have heP (i : Fin 4) (v : E4) : P i v = v i := rfl
  let B (i j : Fin 4) := (P i).smulRight (P j)
  have he (y : E4) : F m a e y = ∑ i, ∑ j, (kerrNewmanMetric m a e y i j) • B i j := by
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
  have hy' : 0 < ksRadius a y := inU m a e hp hy
  apply ContDiffAt.contDiffWithinAt
  rw [show F m a e = fun z => ∑ i, ∑ j, (kerrNewmanMetric m a e z i j) • B i j from funext he]
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  have hcoeff : ContDiffAt ℝ ∞ (fun z : E4 => kerrNewmanMetric m a e z i j) y := by
    have hR := radius_smooth a y hy'
    have hi := null_smooth a y hy' i
    have hj := null_smooth a y hy' j
    have hd := (ks_den_pos a y hy').ne'
    unfold kerrNewmanMetric ksProfile
    fun_prop (disch := assumption)
  first
  | exact smooth_scalar_multiple (Y:=MetricTensor E4) hcoeff (B i j)
  | convert! smooth_scalar_multiple (Y:=MetricTensor E4) hcoeff (B i j) using 1
  | let L : ℝ →L[ℝ] MetricTensor E4 := ContinuousLinearMap.toSpanSingleton ℝ (B i j)
    have hL := ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=ℝ) (F:=MetricTensor E4) (n:=∞) L
    exact hL.contDiffAt.comp (f:=fun z : E4 => kerrNewmanMetric m a e z i j) y hcoeff

theorem field_sym (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) {z : E4}
    (hz : z∈S m a e) (v w : E4) : F m a e z v w=F m a e z w v := by
  let x : U a := ⟨z,inU m a e hp hz⟩
  change G m a e x v w=G m a e x w v
  rw [metric_formula,metric_formula]; ring

theorem field_inv (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) {z : E4}
    (hz : z∈S m a e) : (F m a e z).IsInvertible := by
  let x : U a := ⟨z,inU m a e hp hz⟩
  obtain ⟨b,hb⟩ := (kerrNewman_regularTensors m a e).1 x
  let M := F m a e z
  change ∀ i j, M (b i) (b j) = minkowski i j at hb
  have hi : Function.Injective M := by
    apply (injective_iff_map_eq_zero M).mpr
    intro v hv
    have hs : (∑ i, b.repr v i • b i) = v := b.sum_repr v
    have hw (j : Fin 4) : (∑ i, b.repr v i * minkowski i j)=0 := by
      have eq := congrArg (fun L : E4 →L[ℝ] ℝ => L (b j)) hv
      change M v (b j)=0 at eq
      rw [←hs] at eq
      simpa only [map_sum,map_smul,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,hb] using eq
    have h0 (i : Fin 4) : b.repr v i = 0 := by
      have h := hw i
      fin_cases i <;> simpa [minkowski,Fin.sum_univ_four] using h
    rw [←hs]
    simp [h0]
  have hdim : Module.finrank ℝ E4=Module.finrank ℝ (E4→L[ℝ]ℝ) := (InnerProductSpace.toDual ℝ E4).toLinearEquiv.finrank_eq
  have hs : Function.Surjective M := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi
  exact ⟨ContinuousLinearEquiv.ofBijective M (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs),rfl⟩

theorem nonzero_time (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) {z v : E4}
    (hz : z∈S m a e) (hn : v≠0) (h : F m a e z v v ≤ 0) : v 0≠0 := by
  let x : U a := ⟨z,inU m a e hp hz⟩
  have hs := spatial_squares m a e x (exterior_profile m a e hp x hz) v h
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

theorem cone_pair_negative (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    {z v w : E4} (hz : z∈S m a e) (hvv : F m a e z v v ≤ 0) (hww : F m a e z w w < 0)
    (hvw : 0 < v 0*w 0) : F m a e z v w < 0 := by
  let x : U a := ⟨z,inU m a e hp hz⟩
  have hk := spatial_kernel m a e x (exterior_profile m a e hp x hz) ((w 0) • v - (v 0) • w)
    (by simp [smul_eq_mul,mul_comm])
  let A := F m a e z
  change 0 ≤ A ((w 0) • v - (v 0) • w) ((w 0) • v - (v 0) • w) at hk
  have he : A w v = A v w := field_sym m a e hp hz w v
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

private theorem fit_clock {A : Set ℝ} (hA : IsOpen A) {L : ℝ} (hL : 0 < L) (hS : Icc 0 L⊆A) :
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

abbrev NF (m a e : ℝ) (x₀ : E4) := NormalFlow (F m a e) (S m a e) x₀
abbrev span {m a e : ℝ} {x₀ : E4} (N : NF m a e x₀) := Icc (0:ℝ) N.time
abbrev Z {m a e : ℝ} {x₀ : E4} (N : NF m a e x₀) (p v : E4) (t : ℝ) := (N.flow (t,(p,v))).1
abbrev Velo {m a e : ℝ} {x₀ : E4} (N : NF m a e x₀) (p v : E4) (t : ℝ) := (N.flow (t,(p,v))).2

theorem radial_data {m a e : ℝ} {x₀ : E4} (N : NF m a e x₀) {p v : E4}
    (hv : (p,v)∈N.normal.source) :
    (∀ t∈span N, Z N p v t∈S m a e ∧ HasDerivAt (Z N p v) (Velo N p v t) t) ∧
    ContinuousOn (Velo N p v) (span N) ∧ Z N p v 0=p ∧ Velo N p v 0=v := by
  have h0 := N.initial (p,v) (N.source_stays (p,v) hv 0 ⟨le_rfl,N.time_pos.le⟩)
  refine ⟨fun t ht => ⟨(N.ode _ (N.source_stays _ hv t ht)).1,?_⟩,?_,congrArg Prod.fst h0,congrArg Prod.snd h0⟩
  · exact (N.ode _ (N.source_stays _ hv t ht)).2.fst
  · exact (N.flow_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (N.source_stays (p,v) hv)).snd

private theorem radial_nonzero {m a e : ℝ} (hp : IsKerrNewmanBlackHoleParams m a e) {x₀ : E4}
    (N : NF m a e x₀) {p v : E4} (hv : (p,v)∈N.normal.source) (hn : v≠0) {t : ℝ} (ht : t∈span N) :
    Velo N p v t≠0 := by
  intro hbad
  let f := geodesicSpray (F m a e)
  let u (s : ℝ) := N.flow (t-s,(p,v))
  let y := N.flow (t,(p,v))
  have htime {s : ℝ} (hs : s∈Icc 0 t) : t-s∈span N := ⟨sub_nonneg.mpr hs.2,by linarith [ht.2,hs.1]⟩
  have hdu (s : ℝ) (hs : s∈Icc 0 t) : HasDerivAt u (-f (u s)) s := by
    simpa [u,f,Function.comp_def] using ((N.ode _ (N.source_stays (p,v) hv _ (htime hs))).2.scomp s ((hasDerivAt_id s).const_sub t))
  have hy : f y=0 := by
    change (y.2,-OAI.WeakMTWGlobalSupport.CoordinateGeometry.christoffel (F m a e) y.1 y.2 y.2) = 0
    change y.2=0 at hbad
    simp [hbad]
  have hsmooth := contDiffOn_geodesicSpray_of_invertible (openS m a e) (field_smooth m a e hp) (fun z hz => field_inv m a e hp hz)
  have hz : EqOn u (fun _=>y) (Icc 0 t) := by
    apply FlowLinearization.unique_Icc (f:=fun z => -f z) (fun s hs => (hdu s hs).continuousAt.continuousWithinAt) continuousOn_const
    · intro z hz
      have hz' : z∈(S m a e) ×ˢ (univ : Set E4) := by
        rcases hz with ⟨s,hs,rfl⟩|⟨_,_,rfl⟩
        · exact ⟨(N.ode _ (N.source_stays (p,v) hv _ (htime hs))).1,mem_univ _⟩
        · exact ⟨(N.ode _ (N.source_stays (p,v) hv t ht)).1,mem_univ _⟩
      exact (((hsmooth z hz').contDiffAt (((openS m a e).prod isOpen_univ).mem_nhds hz')).of_le (by simp)).neg
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

theorem radial_future (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T) {x₀ : E4} (N : NF m a e x₀)
    (p q : U a) (htarget : (p.val,q.val)∈N.normal.target)
    (hE : initialEnergy N p.val q.val ≤ 0)
    (ho : 0 ≤ (q.val 0-p.val 0)*timeComponent (T p)) : q∈causalFuture (G m a e) T (D m a e) p := by
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
    have he := normalAt_zero_of_invertible N (openS m a e) (field_smooth m a e hp)
      (fun z hz => field_inv m a e hp hz) hh
    apply hdiag
    apply Subtype.ext
    calc
      q.val = N.normalAt p.val v := ((N.normalAt p.val).right_inv htarget).symm
      _ = p.val := hv0 ▸ he
  obtain ⟨hR,hdc,hfirst,_⟩ := radial_data N hv
  have henergy (t : ℝ) (ht : t∈span N) : F m a e (R t) (d t) (d t) ≤ 0 :=
    (flow_energy N (openS m a e) (field_smooth m a e hp) (fun _ hz => field_sym m a e hp hz)
      (fun _ hz => field_inv m a e hp hz) hv ht).trans_le hE
  have hdn (t : ℝ) (ht : t∈span N) := radial_nonzero hp N hv hvne ht
  have hdt (t : ℝ) (ht : t∈span N) : d t 0≠0 := nonzero_time m a e hp (hR _ ht).1 (hdn t ht) (henergy t ht)
  have h₀ : (0:ℝ)∈span N := ⟨le_rfl,N.time_pos.le⟩
  have hpS := N.base_mem hv
  have hor : o≠0 := by
    apply nonzero_time m a e hp hpS _ (hT.2 p).le
    intro h
    have hh := hT.2 p
    change (T p : E4)=0 at h
    change F m a e p.val (T p : E4) (T p : E4) < 0 at hh
    simp [h] at hh
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
  have horient (s : ℝ) (hs : s∈span N) : 0 < o*(W a T (R s)) 0 := by
    have hc : ContinuousOn (fun t => o*(W a T (R t)) 0) (span N) := by
      intro t ht
      let z : U a := ⟨R t,inU m a e hp (hR t ht).1⟩
      have hz : ContinuousAt (W a T) (R t) := W_cont m a e T hT z
      have hr : ContinuousAt R t := (hR t ht).2.continuousAt
      have ht' : ContinuousAt (fun s => W a T (R s)) t := hz.comp (f:=R) hr
      let proj : E4 →L[ℝ] ℝ := EuclideanSpace.proj 0
      have hh : ContinuousAt (fun s => proj (W a T (R s))) t :=
        proj.continuous.continuousAt.comp (f:=fun s => W a T (R s)) ht'
      exact (continuousAt_const.mul hh).continuousWithinAt
    have hn (t : ℝ) (ht : t∈span N) : o*(W a T (R t)) 0≠0 := by
      let z : U a := ⟨R t,inU m a e hp (hR t ht).1⟩
      have hg := hT.2 z
      change F m a e (R t) (T z : E4) (T z : E4) < 0 at hg
      have he : W a T (R t)=(T z:E4) := W_on a T z
      rw [he]
      exact mul_ne_zero hor (nonzero_time m a e hp (hR t ht).1 (fun hh => by simp [hh] at hg) hg.le)
    apply sign_prop hc hn h₀ _ s hs
    change 0 < o*(W a T (R 0)) 0
    rw [show R 0=p.val from hfirst,W_on]
    exact mul_self_pos.mpr hor
  let A : Set ℝ := {s | (s,(p.val,v))∈N.domain}
  have hA : IsOpen A := N.domain_open.preimage (continuous_id.prodMk continuous_const)
  obtain ⟨f,hf,hfA,hfe⟩ := fit_clock hA N.time_pos (N.source_stays (p.val,v) hv)
  let γ (t : ℝ) : U a := ⟨R (f (N.time*t)),inU m a e hp (N.ode _ (hfA _)).1⟩
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
    have hv' := ambient_velocity a γ hγ s _ hder
    have htim := hT.2 (γ s)
    have heW : W a T (R t)=(T (γ s):E4) := hz ▸ W_on a T (γ s)
    have hpair := cone_pair_negative m a e hp (hR t hts).1 (henergy t hts)
      (w:=W a T (R t)) (by
        change F m a e (R t) (W a T (R t)) (W a T (R t)) < 0
        rw [heW,←hz]
        exact htim) (common_sign (hsign t hts) (horient t hts))
    refine ⟨show (γ s).val∈S m a e by rw [hz]; exact (hR t hts).1,?_,?_,?_⟩
    · change (velocity γ s:E4)≠0
      rw [hv']
      exact smul_ne_zero N.time_pos.ne' (hdn t hts)
    · change F m a e (γ s).val (velocity γ s:E4) (velocity γ s:E4) ≤ 0
      rw [hv',hz]
      simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos N.time_pos.le (mul_nonpos_of_nonneg_of_nonpos N.time_pos.le (henergy t hts))
    · change F m a e (γ s).val (velocity γ s:E4) (T (γ s):E4) < 0
      rw [hv',hz,←heW]
      simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
      exact mul_neg_of_pos_of_neg N.time_pos hpair
  · simpa only [γ,mul_zero,eqF 0 h₀] using hfirst
  · simpa only [γ,mul_one,eqF _ (right_mem_Icc.mpr N.time_pos.le)] using hlast

theorem energy_cont {m a e : ℝ} (hp : IsKerrNewmanBlackHoleParams m a e) {x₀ : E4}
    (N : NF m a e x₀) {p q : E4} (hpS : p∈S m a e) (ht : (p,q)∈N.normal.target) :
    ContinuousAt (fun k : E4×E4 => initialEnergy N k.1 k.2) (p,q) := by
  have hF := ((field_smooth m a e hp p hpS).continuousWithinAt.continuousAt ((openS m a e).mem_nhds hpS)).comp
    (continuous_fst.continuousAt (x:=(p,q)))
  exact (hF.clm_apply (logVec_continuousAt N ht)).clm_apply (logVec_continuousAt N ht)


end
end NoHair.MassShellGeodesics
namespace NoHair.MassShellTrans

open NoHair NoHair.MassShellJoining Set Filter
open scoped ContDiff Manifold BigOperators Topology
noncomputable section
set_option maxHeartbeats 270000

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

private theorem cartesian_formula (m a e : ℝ) (y : E4) (v w : E4) :
    F m a e y v w = -(v 0*w 0) + v 1*w 1 + v 2*w 2 + v 3*w 3
      + ksProfile m a e y * kEval a y v * kEval a y w := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric m a e y) (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul, kerrNewmanMetric, kEval, Fin.sum_univ_four]
  simp [minkowski] <;> ring

theorem result (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T) :
    let U := kerrNewmanSpacetime a
    let D := (Subtype.val : U → E4) ⁻¹' massShell m a e
    let g := kerrNewmanMetricField m a e
    ∀ p ∈ D, ∀ x ∈ D, ∀ q ∈ D,
      x ∈ causalFuture g T D p → q ∈ causalFuture g T D x → q ∈ causalFuture g T D p := by
  dsimp only
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
  have pG := fromCurve_good m a e T α ha
  have qG := fromCurve_good m a e T β hb
  have ha' : Good m a e T x.val (P.vel 1) := p1 ▸ pG 1 (right_mem_Icc.mpr zero_le_one)
  have hb' : Good m a e T x.val (Q.vel 0) := q0 ▸ qG 0 (left_mem_Icc.mpr zero_le_one)
  rcases directions m a e hp T hT x (P.vel 1) (Q.vel 0) ha' hb' with ⟨c,hc,he⟩|hn
  · exact combine_parallel m a e T P Q p x q p0 p1 q0 q1 (fun s => (α s).property)
      (fun s => (β s).property) pG qG c hc he
  · obtain ⟨d,hd,hd1,hmid⟩ := round_window (massShell m a e) (F m a e) (W a T) x.val
      (isOpen_lt continuous_const (continuous_ksRadius a)) (fun b b' => eval_smooth m a e x.val b b' x.property)
      (W_cont m a e T hT x) (fun z v w => by rw [cartesian_formula,cartesian_formula]; ring)
      P Q p1 q0 pG qG hn
    exact combine_round m a e hp T P Q p x q p0 p1 q0 q1 (fun s => (α s).property)
      (fun s => (β s).property) pG qG d hd hd1 hmid

end
end NoHair.MassShellTrans
namespace NoHair.MassShellLocal

open NoHair NoHair.MassShellGeodesics Set Filter
open OAI.WeakMTWGlobalSupport OAI.WeakMTWGlobalSupport.CoordinateGeometry
open OAI.WeakMTWGlobalSupport.NormalNeighborhood NoHair.PseudoNormal
open scoped ContDiff Manifold BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 330000
noncomputable section

private theorem energy_barrier (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    {x₀ : E4} (N : NF m a e x₀) (base : E4) (c v : ℝ→E4) (o : ℝ)
    (hd : ∀ t, HasDerivAt c (v t) t) (hmemS : ∀ t∈J, c t∈S m a e)
    (htarget : ∀ t∈J, (base,c t)∈N.normal.target)
    (hcone : ∀ t∈J, F m a e (c t) (v t) (v t) ≤ 0)
    (hsign : ∀ t∈J, 0 < o*v t 0) (htime : ∀ t∈J, 0 < o*(c t 0-base 0))
    (hseed : initialEnergy N base (c 0) < 0) : initialEnergy N base (c 1) ≤ initialEnergy N base (c 0) := by
  have sG := field_smooth m a e hp
  have invG (z : E4) (hz : z∈S m a e) := field_inv m a e hp hz
  have symG (z : E4) (hz : z∈S m a e) := field_sym m a e hp hz
  let d (t : ℝ) := (2/N.time)*F m a e (c t) (terminalVelocity N base (c t)) (v t)
  have HE (t : ℝ) (ht : t∈J) : HasDerivAt (fun t => initialEnergy N base (c t)) (d t) t :=
    initialEnergy_deriv N (openS m a e) sG symG invG (htarget t ht) (hd t)
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
          F m a e (Z N base u r) (Velo N base u r) (Velo N base u r) < 0 :=
        (flow_energy N (openS m a e) sG symG invG hu hr).trans_lt (ha.trans_lt hseed)
      have hdt (r : ℝ) (hr : r∈span N) : Velo N base u r 0≠0 := by
        have hh := htim r hr
        exact nonzero_time m a e hp (hR r hr).1 (fun h => by simp [h] at hh) hh.le
      have hforward : 0 < o*(Z N base u N.time 0-Z N base u 0 0) := by
        rw [hlast,hfirst]
        exact htime t ht
      have hfin : N.time∈span N := right_mem_Icc.mpr N.time_pos.le
      have hsg := clock_positive N.time_pos (Z N base u) (Velo N base u) (fun r hr => (hR r hr).2) hC hdt hforward N.time hfin
      have hh := htim N.time hfin
      rw [hlast] at hh
      have hm := cone_pair_negative m a e hp (hmemS t ht) (hcone t ht) hh (common_sign (hsign t ht) hsg)
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

private theorem past_seed (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) {x₀ : E4} (N : NF m a e x₀)
    {p : E4} (hpS : p∈S m a e) (hsrc : (p,(0:E4))∈N.normal.source)
    (hlog : logVec N p p = 0) (w : E4) (hw : F m a e p w w < 0) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), initialEnergy N (p-s • w) p < 0 := by
  let f (s : ℝ) := logVec N (p-s • w) p
  let g (s : ℝ) := F m a e (p-s • w)
  have sm := field_smooth m a e hp
  have hG : ContinuousAt (F m a e) p := (sm p hpS).continuousWithinAt.continuousAt ((openS m a e).mem_nhds hpS)
  have gL : Tendsto g (𝓝[>] (0:ℝ)) (𝓝 (F m a e p)) := hG.tendsto.comp (past_shift_limit p w)
  have hd : HasDerivAt f (N.time⁻¹ • w) 0 := logVec_base_deriv N (openS m a e) sm
    (fun z hz => field_inv m a e hp hz) hsrc w
  have f0 : f 0 = 0 := by simpa only [f,zero_smul,sub_zero] using hlog
  exact scaled_norm_negative g (F m a e p) f (N.time⁻¹ • w) gL
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

private theorem energy_of_arc (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    {x₀ : E4} (N : NF m a e x₀) (V : Set E4) (hV : IsOpen V) (hVS : V⊆S m a e)
    (htar : ∀ p∈V, ∀ q∈V, (p,q)∈N.normal.target) (p q w : E4)
    (hpV : p∈V) (hqV : q∈V) (hsrc : (p,(0:E4))∈N.normal.source)
    (hlog : logVec N p p = 0) (hw : F m a e p w w < 0)
    (c v : ℝ→E4) (hd : ∀ t, HasDerivAt c (v t) t)
    (hmem : ∀ t∈J, c t∈V) (he0 : c 0=p) (he1 : c 1=q)
    (hcone : ∀ t∈J, F m a e (c t) (v t) (v t) ≤ 0)
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
    past_seed m a e hp N (hVS hpV) hsrc hlog w hw
  have hbound : ∀ᶠ s in 𝓝[>] (0:ℝ), initialEnergy N (b s) q ≤ 0 := by
    filter_upwards [hbase,bV,spos] with s hseed hsV hspos
    have htime (t : ℝ) (ht : t∈J) : 0 < o*(c t 0-b s 0) := by
      change 0 < o*(c t 0-(p 0-s*o))
      exact positive_shift (hdisp t ht) hone hspos
    have h := energy_barrier m a e hp N (b s) c v o hd (fun t ht => hVS (hmem t ht))
      (fun t ht => htar _ hsV _ (hmem t ht)) hcone hsign htime (by rwa [he0])
    rw [he0,he1] at h
    exact h.trans hseed.le
  exact past_energy_limit (fun k : E4×E4 => initialEnergy N k.1 k.2) p q w
    (energy_cont hp N (hVS hpV) (htar _ hpV _ hqV)) hbound


private theorem curve_necessary (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T) {x₀ : E4} (N : NF m a e x₀)
    (V : Set E4) (hV : IsOpen V) (hVS : V⊆S m a e) (hsrc : ∀ x∈V, (x,(0:E4))∈N.normal.source)
    (htar : ∀ p∈V, ∀ q∈V, (p,q)∈N.normal.target)
    (p q : U a) (hpV : p.val∈V) (hqV : q.val∈V)
    (hJ : q∈causalFuture (G m a e) T ((Subtype.val : U a → E4) ⁻¹' V) p) :
    initialEnergy N p.val q.val ≤ 0 ∧ 0 ≤ (q.val 0-p.val 0)*timeComponent (T p) := by
  have sG := field_smooth m a e hp
  have invG (z : E4) (hz : z∈S m a e) := field_inv m a e hp hz
  have hxsrc := hsrc p.val hpV
  have hlog0 : logVec N p.val p.val = 0 := by
    have he := normalAt_zero_of_invertible N (openS m a e) sG invG hxsrc
    simpa only [logVec,he] using (N.normalAt p.val).left_inv hxsrc
  rcases hJ with he|⟨γ,hγ,h0,h1⟩
  · have heq : q = p := mem_singleton_iff.mp he
    subst q
    constructor
    · change F m a e p.val (logVec N p.val p.val) (logVec N p.val p.val) ≤ 0
      simp only [hlog0,map_zero,ContinuousLinearMap.zero_apply,le_refl]
    · simp only [sub_self,zero_mul,le_refl]
  let c (t : ℝ) := (γ t).val
  let v := deriv c
  let w : E4 := T p
  let o := w 0
  have hval : ContMDiff I4 I4 1 (Subtype.val : U a→E4) := contMDiff_subtype_val
  have hc : ContDiff ℝ 1 c := (hval.comp hγ.1).contDiff
  have hd (t : ℝ) : HasDerivAt c (v t) t := (hc.differentiable (by simp) t).hasDerivAt
  have hvel (t : ℝ) := ambient_velocity a γ hγ.1 t (v t) (hd t)
  have hmem (t : ℝ) (ht : t∈J) : c t∈V := (hγ.2 t ht).1
  have he0 : c 0=p.val := congrArg Subtype.val h0
  have he1 : c 1=q.val := congrArg Subtype.val h1
  have hcone (t : ℝ) (ht : t∈J) : v t≠0 ∧ F m a e (c t) (v t) (v t) ≤ 0 ∧ 0 < (v t 0)*timeComponent (T (γ t)) := by
    obtain ⟨hx,hn,hv,hf⟩ := hγ.2 t ht
    have hh := (cone_estimates m a e (γ t) (exterior_profile m a e hp _ (hVS hx)) _ _ hn hv hf (hT.2 _)).2
    change 0 < timeComponent (velocity γ t) * timeComponent (T (γ t)) at hh
    rw [hvel] at hh
    change (velocity γ t:E4)≠0 at hn
    change F m a e (c t) (velocity γ t:E4) (velocity γ t:E4) ≤ 0 at hv
    rw [hvel] at hn hv
    exact ⟨hn,hv,hh⟩
  have h₀ : (0:ℝ)∈J := left_mem_Icc.mpr zero_le_one
  have h₁ : (1:ℝ)∈J := right_mem_Icc.mpr zero_le_one
  have hstart : 0 < o*v 0 0 := by
    have h := (hcone 0 h₀).2.2
    rw [h0,mul_comm] at h
    exact h
  have hn (t : ℝ) (ht : t∈J) : v t 0≠0 :=
    nonzero_time m a e hp (hVS (hmem t ht)) (hcone t ht).1 (hcone t ht).2.1
  obtain ⟨hsign,hdisp₀⟩ := clock_along c v o hd (hc.continuous_deriv le_rfl) hn hstart
  have hdisp (t : ℝ) (ht : t∈J) : 0 ≤ o*(c t 0-p.val 0) := by
    simpa only [he0] using hdisp₀ t ht
  refine ⟨energy_of_arc m a e hp N V hV hVS htar p.val q.val w hpV hqV hxsrc hlog0
    (hT.2 p) c v hd hmem he0 he1 (fun t ht => (hcone t ht).2.1) hsign hdisp,?_⟩
  rw [← he1,mul_comm]
  exact hdisp 1 h₁

theorem result (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T) :
    let U := kerrNewmanSpacetime a
    let D := (Subtype.val : U → E4) ⁻¹' massShell m a e
    let g := kerrNewmanMetricField m a e
    ∀ x ∈ D, ∃ V : Set U, IsOpen V ∧ x ∈ V ∧ V ⊆ D ∧
      ∀ z : U × U, z.1 ∈ V → z.2 ∈ V →
        z ∈ closure {y : U × U | y.1 ∈ V ∧ y.2 ∈ V ∧ y.2 ∈ causalFuture g T V y.1} →
          z.2 ∈ causalFuture g T D z.1 := by
  classical
  dsimp only
  intro x hx
  obtain ⟨N⟩ := exists_normalFlow_of_invertible (openS m a e) (field_smooth m a e hp)
    (fun z hz => field_inv m a e hp hz) (x₀:=x.val) hx
  have hdiag := normal_center N (openS m a e) (field_smooth m a e hp) (fun z hz => field_inv m a e hp hz) N.center_mem
  have htar : (x.val,x.val)∈N.normal.target := hdiag ▸ N.normal.map_source N.center_mem
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (N.normal.open_target.mem_nhds htar)
  let V := Metric.ball x.val r ∩ (S m a e ∩ {p | (p,(0:E4))∈N.normal.source})
  have hV : IsOpen V := Metric.isOpen_ball.inter ((openS m a e).inter
    (N.normal.open_source.preimage (continuous_id.prodMk continuous_const)))
  have hVS {z : E4} (hz : z∈V) := hz.2.1
  have htr (p : E4) (hp : p∈V) (q : E4) (hq : q∈V) : (p,q)∈N.normal.target := by
    apply hball
    rw [Metric.mem_ball,Prod.dist_eq]
    exact max_lt (Metric.mem_ball.mp hp.1) (Metric.mem_ball.mp hq.1)
  refine ⟨(Subtype.val : U a→E4) ⁻¹' V,hV.preimage continuous_subtype_val,
    ⟨Metric.mem_ball_self hr,hx,N.center_mem⟩,fun _ hz => hVS hz,?_⟩
  intro z hpV hqV hcl
  obtain ⟨seq,hseq,hlim⟩ := mem_closure_iff_seq_limit.mp hcl
  have hnec (n : ℕ) := curve_necessary m a e hp T hT N V hV (fun _ hz => hVS hz)
    (fun _ hz => hz.2.2) htr (seq n).1 (seq n).2 (hseq n).1 (hseq n).2.1 (hseq n).2.2
  have hP : Tendsto (fun n => (seq n).1.val) atTop (𝓝 z.1.val) :=
    (continuous_subtype_val.tendsto z.1).comp ((continuous_fst.tendsto z).comp hlim)
  have hQ : Tendsto (fun n => (seq n).2.val) atTop (𝓝 z.2.val) :=
    (continuous_subtype_val.tendsto z.2).comp ((continuous_snd.tendsto z).comp hlim)
  apply radial_future m a e hp T hT N z.1 z.2 (htr _ hpV _ hqV)
  · exact le_of_tendsto ((energy_cont hp N (hVS hpV) (htr _ hpV _ hqV)).tendsto.comp
      (hP.prodMk_nhds hQ)) (Eventually.of_forall fun n => (hnec n).1)
  · have hTlim : Tendsto (fun n => W a T (seq n).1.val) atTop (𝓝 (W a T z.1.val)) :=
      (W_cont m a e T hT z.1).tendsto.comp hP
    have hproj : Continuous timeComponent := (EuclideanSpace.proj (𝕜:=ℝ) (0 : Fin 4)).continuous
    have hQ0 : Tendsto (fun n => timeComponent (seq n).2.val) atTop (𝓝 (timeComponent z.2.val)) :=
      (hproj.tendsto _).comp hQ
    have hP0 : Tendsto (fun n => timeComponent (seq n).1.val) atTop (𝓝 (timeComponent z.1.val)) :=
      (hproj.tendsto _).comp hP
    have ht0 : Tendsto (fun n => timeComponent (W a T (seq n).1.val)) atTop (𝓝 (timeComponent (W a T z.1.val))) :=
      (hproj.tendsto _).comp hTlim
    have hT0 : Tendsto (fun n => timeComponent (T (seq n).1)) atTop (𝓝 (timeComponent (T z.1))) := by
      simpa only [W_on] using ht0
    exact ge_of_tendsto ((hQ0.sub hP0).mul hT0) (Eventually.of_forall fun n => (hnec n).2)

end
end NoHair.MassShellLocal
namespace NoHair.MassShellCompact

open NoHair Set
open scoped ContDiff Manifold BigOperators

noncomputable section

private abbrev U (a : ℝ) := kerrNewmanSpacetime a
private abbrev D (m a e : ℝ) := (Subtype.val : U a → E4) ⁻¹' massShell m a e
private abbrev I4 := 𝓘(ℝ, E4)
private abbrev G (m a e : ℝ) := kerrNewmanMetricField m a e
private def timeComponent (v : E4) : ℝ := v 0
private def kEval (a : ℝ) (z u : E4) := ∑ i, ksNull a z i * u i

private theorem metric_formula (m a e : ℝ) (x : U a) (v w : E4) :
    G m a e x v w = -(v 0*w 0) + v 1*w 1 + v 2*w 2 + v 3*w 3
      + ksProfile m a e x.val * kEval a x.val v * kEval a x.val w := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric m a e x.val) (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul, kerrNewmanMetric, kEval, Fin.sum_univ_four]
  simp [minkowski] <;> ring

private theorem exterior_profile (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (x : U a) (hx : x ∈ D m a e) : 0 ≤ ksProfile m a e x.val := by
  obtain ⟨hm, he⟩ := hp
  change m < ksRadius a x.val at hx
  have hm' : m ≤ ksRadius a x.val := hx.le
  have hnum : 0 ≤ 2*m*ksRadius a x.val - e^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hm' hm.le, he, sq_nonneg a, sq_nonneg m]
  unfold ksProfile
  exact div_nonneg (mul_nonneg (sq_nonneg _) hnum) (by positivity)

private theorem spatial_squares (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v : E4) (hv : G m a e x v v ≤ 0) :
    (v 1)^2 + (v 2)^2 + (v 3)^2 ≤ (v 0)^2 := by
  rw [metric_formula] at hv
  nlinarith only [hv, mul_nonneg hf (sq_nonneg (kEval a x.val v))]

private theorem spatial_kernel (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v : E4) (h0 : v 0 = 0) : 0 ≤ G m a e x v v := by
  rw [metric_formula, h0]
  nlinarith only [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3),
    mul_nonneg hf (sq_nonneg (kEval a x.val v))]

private theorem cone_estimates (m a e : ℝ) (x : U a) (hf : 0 ≤ ksProfile m a e x.val)
    (v w : E4) (hv : v ≠ 0) (hvv : G m a e x v v ≤ 0) (hvw : G m a e x v w < 0)
    (hww : G m a e x w w < 0) :
    (∀ i, |v i| ≤ |v 0|) ∧ 0 < (v 0)*(w 0) := by
  have hs := spatial_squares m a e x hf v hvv
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
  have hkernel := spatial_kernel m a e x hf ((w 0) • v - (v 0) • w)
    (by simp [smul_eq_mul, mul_comm])
  have hsym : G m a e x w v = G m a e x v w := by rw [metric_formula, metric_formula]; ring
  let A := matrixBilin (kerrNewmanMetric m a e x.val)
  change 0 ≤ A ((w 0) • v - (v 0) • w) ((w 0) • v - (v 0) • w) at hkernel
  change A w v = A v w at hsym
  change A w w < 0 at hww
  change A v v ≤ 0 at hvv
  change A v w < 0 at hvw
  simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, hsym] at hkernel
  nlinarith only [hkernel, mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (w 0)) hvv,
    mul_neg_of_pos_of_neg (sq_pos_iff.mpr hv0) hww, mul_nonneg_of_nonpos_of_nonpos hprod hvw.le]

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


private abbrev J := Icc (0:ℝ) 1
private theorem monotone_from_deriv (f d : ℝ → ℝ) (hd : ∀ s, HasDerivAt f (d s) s)
    (h : ∀ s ∈ J, 0 ≤ d s) : MonotoneOn f J := by
  have hf : Differentiable ℝ f := fun s => (hd s).differentiableAt
  exact monotoneOn_of_deriv_nonneg (convex_Icc (0:ℝ) 1) hf.continuous.continuousOn hf.differentiableOn
    (fun s hs => (hd s).deriv.symm ▸ h s (interior_subset hs))


private theorem arc_displacement (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T) (γ : ℝ → U a)
    (hγ : IsFutureCausalCurveIn (G m a e) T (D m a e) γ) (s : ℝ) (hs : s∈J) :
    dist (γ s) (γ 0) ≤ 2*|(γ 1).val 0-(γ 0).val 0| := by
  let f : ℝ → E4 := Subtype.val ∘ γ
  let v (t : ℝ) : E4 := velocity γ t
  have hval : ContMDiff I4 I4 1 (Subtype.val : U a → E4) := contMDiff_subtype_val
  have hf : ContDiff ℝ 1 f := (hval.comp hγ.1).contDiff
  have hd (t : ℝ) : fderiv ℝ f t = (mfderiv 𝓘(ℝ, ℝ) I4 γ t : ℝ →L[ℝ] E4) := by
    have h := mfderiv_comp t (hval.mdifferentiableAt (by simp) (x := γ t)) (hγ.1.mdifferentiableAt (by simp))
    have hinc : (mfderiv I4 I4 (Subtype.val : U a → E4) (γ t) : E4 →L[ℝ] E4) =
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
    exact cone_estimates m a e (γ t) (exterior_profile m a e hp _ hx)
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

private theorem restrict_arc (m a e : ℝ) (T : VecField (U a)) (K : Set (U a)) (γ : ℝ → U a)
    (hγ : IsFutureCausalCurveIn (G m a e) T K γ) (l h : ℝ) (hl : 0≤l) (hh : 0<h) (hlh : l+h≤1) :
    IsFutureCausalCurveIn (G m a e) T K (fun s => γ (l+h*s)) := by
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
  let A := matrixBilin (kerrNewmanMetric m a e (γ (φ s)).val)
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

private def shortRel (m a e : ℝ) (T : VecField (U a)) (K : Set (U a)) (d : ℝ) : Set (U a × U a) :=
  {z | z.1∈K ∧ z.2∈K ∧ z.2∈causalFuture (G m a e) T K z.1 ∧ |z.2.val 0-z.1.val 0|≤d}

private theorem bisect (m a e : ℝ) (T : VecField (U a)) (K : Set (U a)) (d : ℝ) (hd : 0≤d) :
    shortRel m a e T K (2*d) ⊆ composeRel (shortRel m a e T K d) := by
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
  have hγa := restrict_arc m a e T K γ hγ 0 s le_rfl hs0 (by linarith)
  have hγb := restrict_arc m a e T K γ hγ s (1-s) hs.1 (by linarith) (by linarith)
  have hpq : |t 1-t 0| ≤ 2*d := by simpa only [t,h0,h1] using hlen
  have hhalf : |(t 1-t 0)/2| ≤ d := by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith
  have ha : t s-t 0=(t 1-t 0)/2 := by rw [he]; dsimp [mid]; ring
  have hb : t 1-t s=(t 1-t 0)/2 := by rw [he]; dsimp [mid]; ring
  refine ⟨γ s,⟨hp,hsK,Or.inr ⟨_,hγa,by simpa using h0,by simp⟩,?_⟩,
    ⟨hsK,hq,Or.inr ⟨_,hγb,by simp,by convert h1 using 2 <;> ring⟩,?_⟩⟩
  · rw [← h0]; change |t s-t 0|≤d; rwa [ha]
  · rw [← h1]; change |t 1-t s|≤d; rwa [hb]

theorem result (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T) :
    let U := kerrNewmanSpacetime a
    let g := kerrNewmanMetricField m a e
    let D := (Subtype.val : U → E4) ⁻¹' massShell m a e
    ∀ K : Set U, IsCompact K → K ⊆ D →
      closure {z : U × U | z.1 ∈ K ∧ z.2 ∈ K ∧ z.2 ∈ causalFuture g T K z.1} ⊆
        {z : U × U | z.2 ∈ causalFuture g T D z.1} := by
  dsimp only
  intro K hK hKD
  let R := shortRel m a e T K
  let JD : Set (U a × U a) := {z | z.2 ∈ causalFuture (G m a e) T (D m a e) z.1}
  have hloc (x : K) := NoHair.MassShellLocal.result m a e hp T hT x.val (hKD x.property)
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
      · have hg : IsFutureCausalCurveIn (G m a e) T (D m a e) γ :=
          ⟨hγ.1,fun s hs => ⟨hKD (hγ.2 s hs).1,(hγ.2 s hs).2⟩⟩
        have h := arc_displacement m a e hp T hT γ hg 1 (right_mem_Icc.mpr zero_le_one)
        rw [h0,h1] at h; linarith
    have hs : dist z.2 z.1 ≤ 2*d := (closure_minimal (show R d ⊆ {y | dist y.2 y.1 ≤ 2*d} from hdist)
      (isClosed_le (continuous_snd.dist continuous_fst) continuous_const)) hz
    have hpx : z.1∈V x := hx (Metric.mem_ball_self hδ)
    have hqx : z.2∈V x := hx (show dist z.2 z.1<δ by dsimp [d] at hs; linarith)
    apply hLocal x z hpx hqx
    let N : Set (U a × U a) := {y | dist y.1 z.1 < d}
    have ho : IsOpen N := (Metric.isOpen_ball.preimage continuous_fst)
    have hzn : z ∈ N := by change dist z.1 z.1<d; simpa
    apply closure_mono _ (ho.inter_closure ⟨hzn,hz⟩)
    rintro y ⟨hy,hyR⟩
    change dist y.1 z.1<d at hy
    have near (v : U a) (hv : dist v y.1 ≤ 2*d) : v∈V x := hx (by
      change dist v z.1<δ
      have := dist_triangle v y.1 z.1
      dsimp [d] at hv hy
      linarith)
    refine ⟨near y.1 (by rw [dist_self]; linarith),near y.2 (hdist y hyR),?_⟩
    rcases hyR.2.2.1 with he|⟨γ,hγ,h0,h1⟩
    · exact Or.inl he
    · refine Or.inr ⟨γ,⟨hγ.1,?_⟩,h0,h1⟩
      intro t ht
      have hg : IsFutureCausalCurveIn (G m a e) T (D m a e) γ :=
        ⟨hγ.1,fun s hs => ⟨hKD (hγ.2 s hs).1,(hγ.2 s hs).2⟩⟩
      have hh := arc_displacement m a e hp T hT γ hg t ht
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
        obtain ⟨x,hx,hy⟩ := bisect m a e T K b (by dsimp [b]; positivity) hz
        exact ⟨x,subset_closure hx,subset_closure hy⟩
      intro z hz
      have he : (2:ℝ)^(n+1)*d=2*b := by dsimp [b]; ring
      rw [he] at hz
      obtain ⟨x,hx,hy⟩ := hsup hz
      exact NoHair.MassShellTrans.result m a e hp T hT z.1 (hKD (hinside b hx).1)
        x (hKD (hinside b hx).2) z.2 (hKD (hinside b hy).2) (ih hx) (ih hy)
  have hct : Continuous (fun z : U a => |z.val 0|) := by fun_prop
  obtain ⟨M,hM⟩ := hK.bddAbove_image hct.abs.continuousOn
  have bound (x : U a) (hx : x∈K) : |x.val 0|≤M := by
    simpa using hM (show |(|x.val 0|)| ∈ (fun z : U a => |(|z.val 0|)|) '' K from ⟨x,hx,rfl⟩)
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (2*M/d) (by norm_num : (1:ℝ)<2)
  apply (closure_mono ?_).trans (hdyadic n)
  rintro z ⟨h1,h2,hj⟩
  refine ⟨h1,h2,hj,?_⟩
  have ht := (div_lt_iff₀ hd).mp hn
  linarith [abs_sub (z.2.val 0) (z.1.val 0),bound z.1 h1,bound z.2 h2]

end
end NoHair.MassShellCompact

open NoHair Set

theorem solution (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T) :
    let U := kerrNewmanSpacetime a
    let g := kerrNewmanMetricField m a e
    let D := (Subtype.val : U → E4) ⁻¹' {z | m < ksRadius a z}
    ∀ K : Set U, IsCompact K → K ⊆ D →
      closure {z : U × U | z.1 ∈ K ∧ z.2 ∈ K ∧ z.2 ∈ causalFuture g T K z.1} ⊆
        {z : U × U | z.2 ∈ causalFuture g T D z.1} := NoHair.MassShellCompact.result m a e hp T hT
