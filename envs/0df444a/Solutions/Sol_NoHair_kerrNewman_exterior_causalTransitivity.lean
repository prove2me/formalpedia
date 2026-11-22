-- Prove2me | solution 1 for NoHair.kerrNewman_exterior_causalTransitivity
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T21:51:00.76069+00:00
-- url     : https://prove2.me/submissions/48ff4c37-9c26-46c2-afe7-dd0e96ce0729

import Definitions.Def_NoHair_RegularCausalJoins

open NoHair NoHair.CausalJoining Set Filter
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

theorem solution (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T) :
    let U := kerrNewmanSpacetime a
    let D := (Subtype.val : U → E4) ⁻¹' kerrNewmanDOC m a e
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
  · obtain ⟨d,hd,hd1,hmid⟩ := round_window (kerrNewmanDOC m a e) (F m a e) (W a T) x.val
      (isOpen_lt continuous_const (continuous_ksRadius a)) (fun b b' => eval_smooth m a e x.val b b' x.property)
      (W_cont m a e T hT x) (fun z v w => by rw [cartesian_formula,cartesian_formula]; ring)
      P Q p1 q0 pG qG hn
    exact combine_round m a e hp T P Q p x q p0 p1 q0 q1 (fun s => (α s).property)
      (fun s => (β s).property) pG qG d hd hd1 hmid
