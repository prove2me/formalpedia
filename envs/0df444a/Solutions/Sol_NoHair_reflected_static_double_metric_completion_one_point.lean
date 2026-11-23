-- Prove2me | solution 1 for NoHair.reflected_static_double_metric_completion_one_point
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:15:22.747974+00:00
-- url     : https://prove2.me/submissions/36843f6f-87ee-4f06-b2d6-19a859655e62

import Theorems.Thm_NoHair_reflected_negative_static_end_adds_one_metric_completion_point
import Theorems.Thm_NoHair_reflected_static_double_compact_truncations
import Theorems.Thm_NoHair_riemannian_distance_bound_of_differential
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

open Metric Manifold
open scoped NNReal
private abbrev X := ADMPoint
private abbrev I := 𝓘(ℝ,ADMPoint)
private abbrev J := 𝓘(ℝ,ℝ)

open UniformSpace
private abbrev A := Fin 3
private noncomputable abbrev e (i:A) : X := EuclideanSpace.single i 1
private lemma norm_in_chart {Q:Type} [MetricSpace Q] [ChartedSpace X Q] [IsManifold I ∞ Q]
    [RiemannianBundle (fun q : Q => TangentSpace I q)]
    (f : X → Q) (x v : X) : ‖mfderiv I I f x v‖^2 = staticChartQuadratic (riemannianEndCoeffs f) x v := by
  let D := mfderiv I I f x
  have rep : (∑ i : A, v i • e i) = v := by
    rw [Fin.sum_univ_three]
    ext j
    fin_cases j <;> simp +decide [e,EuclideanSpace.single,PiLp.single_apply]
  have dr : D v=∑ i : A, v i • D (e i) := by
    let P : X →ₗ[ℝ] TangentSpace I (f x) := D.toLinearMap
    change P v=∑ i:A, v i • P (e i)
    calc _ = P (∑ i:A, v i • e i) := congrArg P rep.symm
         _ = _ := by simp only [map_sum,map_smul]
  change ‖D v‖^2 = _
  rw [←real_inner_self_eq_norm_sq,dr]
  simp only [staticChartQuadratic,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [riemannianEndCoeffs,D,e]
  simp only [real_inner_comm]
  ring

private lemma proper_positive_chart (Q : Type) [MetricSpace Q] [ChartedSpace X Q] [IsManifold I ∞ Q]
    [RiemannianBundle (fun q : Q => TangentSpace I q)] [IsRiemannianManifold I Q]
    (e : OpenPartialHomeomorph X Q)
    (ce : ContMDiffOn I I ∞ e e.source) (ci : ContMDiffOn I I ∞ e.symm e.target)
    (L : ℝ) (lp:0<L) (inside : ∀ {x:X}, L<‖x‖ → x∈e.source)
    (lower : ∀ x : X, L<‖x‖ → ∀ v : X, ‖v‖≤2*‖mfderiv I I e x v‖)
    (V : Set Q) (hV : Bornology.IsBounded V) :
    ∃ T : ℝ, ∀ x : X, T<‖x‖ → e x ∉ V := by
  classical
  let χ : ContDiffBump (0:X) := ⟨1,2,by norm_num,by norm_num⟩
  have smoothB : ContDiff ℝ ∞ χ := χ.contDiff
  obtain ⟨K,lip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport χ.hasCompactSupport smoothB (by simp)
  let M : ℝ≥0 := 2*K+1
  have mp : (0:ℝ≥0)<M := by dsimp only [M]; positivity
  let z₀ : X := EuclideanSpace.single 0 (L+1)
  have zlen : ‖z₀‖=L+1 := by simp only [z₀,EuclideanSpace.norm_single,Real.norm_eq_abs,abs_of_pos (by linarith : 0<L+1)]
  have zsrc : z₀ ∈ e.source := inside (by rw [zlen]; linarith)
  let q₀ := e z₀
  obtain ⟨D,hD⟩ := hV.subset_closedBall q₀
  let T := 4*(L+‖z₀‖+1) + 4*(M:ℝ)*max D 0
  refine ⟨T,?_⟩
  intro x hx hxV
  have mx0 : 0 ≤ (M:ℝ) := M.property
  have big : 4*(L+‖z₀‖+1)<‖x‖ := by
    dsimp only [T] at hx
    linarith only [hx,mul_nonneg mx0 (le_max_right D 0)]
  let b := ‖x‖/4
  have bp : 0<b := by dsimp only [b]; linarith only [big,lp,norm_nonneg z₀]
  let U := closedBall x (2*b)
  have outer {y : X} (hy : y∈U) : L<‖y‖ ∧ ‖z₀‖<‖y‖ := by
    have dist := Metric.mem_closedBall.mp hy
    have tri := dist_triangle (0:X) y x
    simp only [dist_zero_left] at tri
    dsimp only [b] at dist
    constructor <;> linarith only [big,dist,tri,lp,norm_nonneg z₀]
  have ux : x∈U := mem_closedBall_self (by positivity)
  have us : U ⊆ e.source := fun y hy => inside (outer hy).1
  let l := fun y : X => b⁻¹ • (y-x)
  let g := fun y : X => b*χ (l y)
  have cl : ContDiff ℝ ∞ l := by
    change ContDiff ℝ ∞ (fun y : X => (b⁻¹ : ℝ) • (y-x))
    fun_prop
  have cg : ContDiff ℝ ∞ g := contDiff_const.mul (smoothB.comp cl)
  have lg : LipschitzWith K g := by
    apply LipschitzWith.of_dist_le_mul
    intro a t
    have distl : dist (l a) (l t)=b⁻¹*dist a t := by
      simp only [l,dist_eq_norm,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr bp),sub_sub_sub_cancel_right]
    have eg : dist (g a) (g t)= b * dist (χ (l a)) (χ (l t)) := by
      simp only [g,Real.dist_eq,←mul_sub,abs_mul,abs_of_pos bp]
    rw [eg]
    calc _ ≤ b*((K:ℝ)*dist (l a) (l t)) := mul_le_mul_of_nonneg_left (lip.dist_le_mul _ _) bp.le
         _ = _ := by rw [distl]; field_simp
  have gz {y : X} (hy : y∉U) : g y=0 := by
    have ht := lt_of_not_ge (fun z => hy (mem_closedBall.mpr z))
    have large : χ.rOut ≤ dist (l y) 0 := by
      change 2 ≤ dist (b⁻¹ • (y-x)) 0
      rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr bp),inv_mul_eq_div]
      apply (le_div_iff₀ bp).mpr
      simpa only [dist_eq_norm] using ht.le
    simp [g,χ.zero_of_le_dist large]
  let S := e '' U
  have cs : IsCompact S := (isCompact_closedBall _ _).image_of_continuousOn (e.continuousOn.mono us)
  let f := fun q : Q => if q∈e.target then g (e.symm q) else 0
  have out {q:Q} (nq : q∉S) : f q=0 := by
    by_cases t : q∈e.target
    · have h : e.symm q∉U := fun h => nq ⟨_,h,e.right_inv t⟩
      simp only [f,if_pos t,gz h]
    · exact if_neg t
  have outEv {q:Q} (nq : q∉S) : f =ᶠ[𝓝 q] (fun _ => 0) :=
    (show ∀ᶠ y in 𝓝 q, y∉S from cs.isClosed.isOpen_compl.mem_nhds nq).mono fun _ hy => out hy
  have pull {y:X} (hy : y∈e.source) : f (e y)=g y := by simp only [f,if_pos (e.map_source hy),e.left_inv hy]
  have cf : ContMDiff I J 1 f := by
    intro q
    by_cases t : q∈e.target
    · have ev : f =ᶠ[𝓝 q] (g ∘ e.symm) := (show ∀ᶠ y in 𝓝 q, y∈e.target from e.open_target.mem_nhds t).mono
        fun y hy => if_pos hy
      exact (((contMDiff_iff_contDiff.mpr (cg.of_le (by simp))).contMDiffAt).comp q
        ((ci.contMDiffAt (e.open_target.mem_nhds t)).of_le (by simp))).congr_of_eventuallyEq ev
    · have nq : q∉S := by rintro ⟨y,hy,rfl⟩; exact t (e.map_source (us hy))
      exact contMDiffAt_const.congr_of_eventuallyEq (outEv nq)
  have dfbound (q : Q) (v : TangentSpace I q) : ‖mfderiv I J f q v‖ ≤ (M:ℝ)*‖v‖ := by
    by_cases mem : q∈S
    · obtain ⟨y,hy,rfl⟩ := mem
      let φ : PartialDiffeomorph I I X Q ∞ := { e.toPartialEquiv with
        open_source := e.open_source, open_target := e.open_target,contMDiffOn_toFun := ce,contMDiffOn_invFun := ci }
      have localD : IsLocalDiffeomorphAt I I ∞ e y := ⟨φ,us hy,fun _ _ => rfl⟩
      obtain ⟨w,hw⟩ := (localD.mfderivToContinuousLinearEquiv (by simp)).surjective v
      change mfderiv I I e y w = v at hw
      have ev : f ∘ e =ᶠ[𝓝 y] g := (show ∀ᶠ z in 𝓝 y, z∈e.source from e.open_source.mem_nhds (us hy)).mono fun _ hz => pull hz
      have chain := mfderiv_comp (I':=I) y (cf.contMDiffAt.mdifferentiableAt one_ne_zero) (localD.mdifferentiableAt (by simp))
      rw [ev.mfderiv_eq,mfderiv_eq_fderiv] at chain
      have hw' := congrArg (fun A : X →L[ℝ] ℝ => A w) chain
      change fderiv ℝ g y w = mfderiv I J f (e y) (mfderiv I I e y w) at hw'
      rw [hw] at hw'
      have normed : ‖mfderiv I J f (e y) v‖=‖fderiv ℝ g y w‖ := by
        rw [norm_tangentSpace_vectorSpace]; exact congrArg (fun a : ℝ => ‖a‖) hw'.symm
      rw [normed]
      have low := lower y (outer hy).1 (w:X)
      rw [hw] at low
      have hi := norm_fderiv_le_of_lipschitz ℝ lg (x₀:=y)
      let euNorm : X → ℝ := fun z => ‖z‖
      calc _ ≤ ‖fderiv ℝ g y‖*euNorm w := (fderiv ℝ g y).le_opNorm w
           _ ≤ (K:ℝ)*(2*‖v‖) := mul_le_mul hi low (norm_nonneg _) K.property
           _ ≤ _ := by dsimp only [M]; push_cast; nlinarith only [norm_nonneg v]
    · have zero : mfderiv I J f q=0 := by rw [(outEv mem).mfderiv_eq,mfderiv_const] <;> rfl
      rw [zero,ContinuousLinearMap.zero_apply,norm_zero]
      positivity
  have LF := riemannian_distance_bound_of_differential Q f cf M mp dfbound
  have zoff : z₀∉U := fun hh => (outer hh).2.false
  have left : f (e x)=b := by
    rw [pull (us ux)]
    have yes : χ (0:X)=1 := χ.one_of_mem_closedBall (mem_closedBall_self χ.rIn_pos.le)
    simp [g,l,yes]
  have right : f q₀=0 := (pull zsrc).trans (gz zoff)
  have control := LF.dist_le_mul (e x) q₀
  rw [left,right,dist_zero_right,Real.norm_eq_abs,abs_of_pos bp] at control
  have boundD := mem_closedBall.mp (hD hxV)
  have bad := control.trans (mul_le_mul_of_nonneg_left (boundD.trans (le_max_left D 0)) mx0)
  dsimp only [T] at hx
  dsimp only [b] at bad
  linarith only [hx,bad,lp,norm_nonneg z₀]
theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h)
    (d : ReflectedStaticDouble Ω N h)
    (hpositiveEnd : ∃ R : ℝ, 0 < R ∧
      (∀ x : ADMPoint, R < ‖x‖ → ∀ v : ADMPoint, ‖v‖^2 / 4 ≤
        ∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h x i j * v i * v j) ∧
      ∀ (γ : ℝ → ADMPoint) (a b : ℝ), a ≤ b → ContDiff ℝ 1 γ →
        (∀ t ∈ Set.Icc a b, R < ‖γ t‖) →
        ‖γ b - γ a‖ ≤ 2 * ∫ t in a..b, Real.sqrt
          (∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h (γ t) i j * deriv γ t i * deriv γ t j))
    (hmass : Tendsto (staticADMFlux (staticPositiveMetric N h)) atTop (𝓝 0)) :
    ∃ p : UniformSpace.Completion d.carrier, (∀ q : d.carrier, (q : UniformSpace.Completion d.carrier) ≠ p) ∧
      Tendsto (fun x : ADMPoint => ((d.side false).symm x : UniformSpace.Completion d.carrier))
        (cocompact ADMPoint) (𝓝 p) ∧
      ∀ w : UniformSpace.Completion d.carrier, w = p ∨ ∃ q : d.carrier, (q : UniformSpace.Completion d.carrier) = w := by
  classical
  obtain ⟨p,newp,lim⟩ := reflected_negative_static_end_adds_one_metric_completion_point Ω W N h c d
  obtain ⟨R,rp,quad,_⟩ := hpositiveEnd
  obtain ⟨B,hB⟩ := c.compactComplement.isBounded.exists_norm_le
  let L := max R B
  have lp : 0<L := rp.trans_le (le_max_left _ _)
  have outside {x:X} (hx:B<‖x‖) : x∈Ω := by by_contra hn; exact hx.not_ge (hB x hn)
  let e := (d.side true).symm
  have inside {x:X} (hx:L<‖x‖) : x∈e.source := by
    change x∈(d.side true).target
    rw [d.target]
    exact outside ((le_max_right _ _).trans_lt hx)
  have low (x:X) (hx:L<‖x‖) (v:X) : ‖v‖≤2*‖mfderiv I I e x v‖ := by
    have ox := outside ((le_max_right _ _).trans_lt hx)
    have b := quad x ((le_max_left _ _).trans_lt hx) v
    have mt : riemannianEndCoeffs e x = staticPositiveMetric N h x := by simpa [e] using d.sideMetric true x ox
    have eq := norm_in_chart e x v
    simp only [staticChartQuadratic,mt] at eq
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    nlinarith only [b,eq]
  let inc := (fun q : d.carrier => (q : Completion d.carrier))
  have ci : Continuous inc := Completion.continuous_coe (α:=d.carrier)
  refine ⟨p,newp,lim,?_⟩
  intro w
  by_cases wp : w=p
  · exact Or.inl wp
  right
  let δ := dist w p / 3
  have dp : 0<δ := div_pos (dist_pos.mpr wp) (by norm_num)
  let U := ball w δ
  let V := inc ⁻¹' U
  have bv : Bornology.IsBounded V := (Completion.coe_isometry (α:=d.carrier)).antilipschitz.isBounded_preimage (isBounded_ball)
  obtain ⟨T₁,positive⟩ := proper_positive_chart d.carrier e (d.smoothInverse true) (d.smoothSide true) L lp inside low V bv
  have negEv : ∀ᶠ x : X in cocompact X, inc ((d.side false).symm x) ∈ ball p δ := lim (ball_mem_nhds _ dp)
  obtain ⟨A,cA,far⟩ := Filter.mem_cocompact.mp negEv
  obtain ⟨T₂,hT₂⟩ := cA.isBounded.exists_norm_le
  let T := max B (max T₁ T₂)
  let H := ((d.inc true '' {x : ↥(closure Ω) | T<‖x.val‖}) ∪
      (d.inc false '' {x : ↥(closure Ω) | T<‖x.val‖}))ᶜ
  have hH : IsCompact H := reflected_static_double_compact_truncations Ω N h d T
  have vh : V⊆H := by
    intro q hq
    change q ∉ _ ∪ _
    rintro (⟨x,big,rfl⟩|⟨x,big,rfl⟩)
    · have a : B<‖x.val‖ := (le_max_left _ _).trans_lt big
      have b : T₁<‖x.val‖ := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt big
      apply positive x.val b
      change (d.side true).symm x.val ∈ V
      rwa [d.inverseOnSide true x.val (outside a)]
    · have a : B<‖x.val‖ := (le_max_left _ _).trans_lt big
      have b : T₂<‖x.val‖ := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt big
      have dis := far (show x.val ∉ A from fun h => b.not_ge (hT₂ _ h))
      change inc ((d.side false).symm x.val) ∈ ball p δ at dis
      rw [d.inverseOnSide false x.val (outside a)] at dis
      have d1 := mem_ball.mp dis
      have d2 := mem_ball.mp (show inc (d.inc false x) ∈ ball w δ from hq)
      have h := dist_triangle w (inc (d.inc false x)) p
      rw [dist_comm w (inc (d.inc false x))] at h
      dsimp only [δ] at d1 d2
      linarith only [d1,d2,h,show 0 ≤ dist w p from dist_nonneg]
  have closed := (hH.image ci).isClosed
  have inImage : w∈inc '' H := by
    by_contra bad
    let S := U ∩ (inc '' H)ᶜ
    have os : IsOpen S := isOpen_ball.inter closed.isOpen_compl
    have non : S.Nonempty := ⟨w,mem_ball_self dp,bad⟩
    obtain ⟨q,hq⟩ := (Completion.denseRange_coe (α:=d.carrier)).exists_mem_open os non
    exact hq.2 ⟨q,vh hq.1,rfl⟩
  obtain ⟨q,_,eq⟩ := inImage
  exact ⟨q,eq⟩
