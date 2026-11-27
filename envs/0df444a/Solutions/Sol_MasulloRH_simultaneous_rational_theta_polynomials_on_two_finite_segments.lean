-- Prove2me | solution 1 for MasulloRH.simultaneous_rational_theta_polynomials_on_two_finite_segments
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T04:28:16.084202+00:00
-- url     : https://prove2.me/submissions/400eab21-8e4f-447b-b28d-cd7c9d20aa05

import Definitions.Def_MasulloRH_FiniteMellinBands
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open Set Filter Topology MeasureTheory MasulloRH.RationalThetaGrid
open MasulloRH.VerticalThetaApproximation MasulloRH.FiniteMellinBands

private theorem rationalCoefficients : DenseRange asComplex := by
  let e := Complex.equivRealProdCLM.symm
  have h := e.surjective.denseRange.comp
    ((Rat.denseRange_cast (𝕜:=ℝ)).prodMap (Rat.denseRange_cast (𝕜:=ℝ))) e.continuous
  convert h using 1
  funext z
  simp [asComplex,e,Complex.equivRealProdCLM_symm_apply]

private lemma expApply {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : C(X,ℂ)) (x : X) : NormedSpace.exp f x = Complex.exp (f x) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ x) (continuous_eval_const x) f

private noncomputable def waves {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (z : C(X,ℂ)) (q : ℚ) : C(X,ℂ) := NormedSpace.exp ((q:ℝ) • z)

private lemma waveValue {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (z : C(X,ℂ)) (q : ℚ) (x : X) : waves z q x = Complex.exp (z x * (q:ℝ)) := by
  rw [waves,expApply]
  simp [Complex.real_smul,mul_comm]

private lemma coordinates {X : Type*} [TopologicalSpace X] [CompactSpace X] (z : C(X,ℂ)) :
    z ∈ (Algebra.adjoin ℂ (range (waves z))).topologicalClosure := by
  let A := Algebra.adjoin ℂ (range (waves z))
  have hc := A.isClosed_topologicalClosure
  have inA (x : ℝ) : NormedSpace.exp (x • z) ∈ A.topologicalClosure := by
    let setOfScalars := {x : ℝ | NormedSpace.exp (x • z) ∈ A.topologicalClosure}
    have hclosed : IsClosed setOfScalars := hc.preimage
      (NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const))
    apply closure_minimal (t := setOfScalars) _ hclosed ((Rat.denseRange_cast (𝕜:=ℝ)) x)
    rintro _ ⟨r,rfl⟩
    exact A.le_topologicalClosure (Algebra.subset_adjoin ⟨r,rfl⟩)
  have hd : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • z)) z 0 := by
    simpa using (hasDerivAt_exp_smul_const z (0:ℝ))
  apply hc.mem_of_tendsto hd.tendsto_slope_zero
  apply Eventually.of_forall
  intro t
  rw [← Complex.coe_smul]
  exact A.topologicalClosure.smul_mem (A.topologicalClosure.sub_mem (inA _) (inA _)) _

private lemma closedSeparator {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (z : C(X,ℂ)) (L U T : ℝ) (hLU : L<U)
    (hx : ∀ x, ∃ t : ℝ, |t| ≤ T ∧ (z x=pointAt L t ∨ z x=pointAt U t)) :
    ∃ g : C(X,ℂ), g ∈ (Algebra.adjoin ℂ (range (waves z))).topologicalClosure ∧
      (∀ x t, z x=pointAt L t → g x=0) ∧ (∀ x t, z x=pointAt U t → g x=1) := by
  let A := Algebra.adjoin ℂ (range (waves z))
  let g : C(X,ℂ) := ⟨fun x => (((z x).re-L)/(U-L):ℝ),by fun_prop⟩
  have gL (x : X) (t : ℝ) (h : z x=pointAt L t) : g x=0 := by simp [g,h,pointAt]
  have gU (x : X) (t : ℝ) (h : z x=pointAt U t) : g x=1 := by
    have hdiff : (U:ℂ)-(L:ℂ)≠0 := by exact_mod_cast (sub_pos.mpr hLU).ne'
    simp [g,h,pointAt,hdiff]
  refine ⟨g,?_,gL,gU⟩
  apply A.isClosed_topologicalClosure.closure_eq ▸ (show g ∈ closure (A.topologicalClosure : Set C(X,ℂ)) from ?_)
  rw [Metric.mem_closure_iff]
  intro ε hε
  let h := Real.pi/(U-L)
  have hh : 0<h := div_pos Real.pi_pos (sub_pos.mpr hLU)
  have hmul : h*(U-L)=Real.pi := div_mul_cancel₀ _ (sub_pos.mpr hLU).ne'
  let w := NormedSpace.exp (((h:ℂ)*Complex.I) • (z - algebraMap ℂ C(X,ℂ) (L:ℂ)))
  have hw : w ∈ A.topologicalClosure := NormedSpace.exp_mem (R:=ℂ) A.isClosed_topologicalClosure
    (A.topologicalClosure.smul_mem (A.topologicalClosure.sub_mem (coordinates z)
      (A.topologicalClosure.algebraMap_mem _)) _)
  have split (c t : ℝ) :
      (h:ℂ)*Complex.I*(pointAt c t - (L:ℂ)) =
        ((-(h*t):ℝ):ℂ) + ((h*(c-L):ℝ):ℂ)*Complex.I := by
    simp only [pointAt,Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_sub]
    linear_combination (h:ℂ)*(t:ℂ)*Complex.I_sq
  have evalW (x : X) : w x = Complex.exp ((h:ℂ)*Complex.I*(z x-(L:ℂ))) := by
    rw [expApply];rfl
  let a := Real.exp (-h*T)
  have ha : 0<a := Real.exp_pos _
  let N := (|Real.log ε|+1)/a
  have hN : 0≤N := (div_pos (by positivity) ha).le
  have hNa : N*a=|Real.log ε|+1 := div_mul_cancel₀ _ ha.ne'
  let v := NormedSpace.exp (-NormedSpace.exp ((N:ℂ) • w))
  have hv : v ∈ A.topologicalClosure := NormedSpace.exp_mem (R:=ℂ) A.isClosed_topologicalClosure
    (A.topologicalClosure.neg_mem (NormedSpace.exp_mem (R:=ℂ) A.isClosed_topologicalClosure
      (A.topologicalClosure.smul_mem hw _)))
  refine ⟨v,hv,?_⟩
  rw [dist_eq_norm]
  have normBound : ‖g-v‖ ≤ Real.exp (-(N*a)) := by
    apply (ContinuousMap.norm_le _ (Real.exp_pos _).le).mpr
    intro x
    obtain ⟨t,ht,H⟩ := hx x
    let b := Real.exp (-h*t)
    have hab : a≤b := Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left (abs_le.mp ht).2 hh.le])
    have habN := mul_le_mul_of_nonneg_left hab hN
    have ev : v x = Complex.exp (-Complex.exp ((N:ℂ)*w x)) := by
      dsimp only [v];rw [expApply,ContinuousMap.neg_apply,expApply];rfl
    rcases H with hl|hu
    · have ww : w x=(b:ℂ) := by rw [evalW,hl,split];simp [b]
      rw [ContinuousMap.sub_apply,gL x t hl,ev,ww]
      simp only [← Complex.ofReal_mul,← Complex.ofReal_exp,← Complex.ofReal_neg,zero_sub,
        norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      linarith [Real.add_one_le_exp (N*b)]
    · have ww : w x=-(b:ℂ) := by
        rw [evalW,hu,split,hmul,Complex.exp_add,Complex.exp_pi_mul_I]
        simp [b]
      rw [ContinuousMap.sub_apply,gU x t hu,ev,ww]
      have e : Complex.exp (-Complex.exp ((N:ℂ)*(-(b:ℂ)))) =
          ((Real.exp (-Real.exp (-(N*b)))):ℂ) := by push_cast;ring_nf
      rw [e,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (by linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.exp_pos (-(N*b))).le)])]
      calc
        _ ≤ Real.exp (-(N*b)) := by linarith [Real.add_one_le_exp (-Real.exp (-(N*b)))]
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  apply normBound.trans_lt
  rw [hNa]
  exact (Real.exp_lt_exp.mpr (show -(|Real.log ε|+1)<Real.log ε by
    linarith [neg_abs_le (Real.log ε)])).trans_eq (Real.exp_log hε)

private lemma expand {X : Type*} [TopologicalSpace X] [CompactSpace X] (z : C(X,ℂ)) :
    (Algebra.adjoin ℂ (range (waves z))).toSubmodule = Submodule.span ℂ (range (waves z)) := by
  apply Algebra.adjoin_eq_span_of_subset
  refine Subset.trans ?_ Submodule.subset_span
  intro x hx
  refine Submonoid.closure_induction (fun _ => id) ⟨0,?_⟩ ?_ hx
  · ext k; simp [waveValue]
  · rintro _ _ _ _ ⟨p,rfl⟩ ⟨q,rfl⟩
    refine ⟨p+q,?_⟩
    ext k
    simp [waveValue,mul_add,Complex.exp_add]

theorem solution (L U T ε : ℝ) (hLU : L<U) (hε : 0<ε)
    {l r : ℕ} (a : Fin l → ℚ×ℚ) (x : Fin l → ℚ) (b : Fin r → ℚ×ℚ) (y : Fin r → ℚ) :
    ∃ (m : ℕ) (d : Fin m → ℚ×ℚ) (v : Fin m → ℚ), ∀ t : ℝ, |t|≤T →
      ‖poly d v (pointAt L t)-poly a x (pointAt L t)‖ < ε ∧
      ‖poly d v (pointAt U t)-poly b y (pointAt U t)‖ < ε := by
  classical
  let seg := fun c : ℝ => pointAt c '' Icc (-T) T
  let K := seg L ∪ seg U
  have cp (c : ℝ) : IsCompact (seg c) := isCompact_Icc.image (by unfold pointAt;fun_prop)
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp ((cp L).union (cp U))
  let z : C(K,ℂ) := ⟨Subtype.val,continuous_subtype_val⟩
  let A := Algebra.adjoin ℂ (range (waves z))
  have hK (s : K) : ∃ t, |t|≤T ∧ (z s=pointAt L t ∨ z s=pointAt U t) := by
    rcases s.prop with ⟨t,ht,e⟩|⟨t,ht,e⟩
    · exact ⟨t,abs_le.mpr ht,Or.inl e.symm⟩
    · exact ⟨t,abs_le.mpr ht,Or.inr e.symm⟩
  obtain ⟨g,hg,hL,hU⟩ := closedSeparator z L U T hLU hK
  let P := fun {m : ℕ} (a : Fin m → ℚ×ℚ) (x : Fin m → ℚ) => ∑ i, asComplex (a i) • waves z (x i)
  have hP {m : ℕ} (a : Fin m → ℚ×ℚ) (x : Fin m → ℚ) : P a x ∈ A.topologicalClosure := by
    apply A.topologicalClosure.sum_mem
    intro i _
    exact A.topologicalClosure.smul_mem (A.le_topologicalClosure (Algebra.subset_adjoin ⟨_,rfl⟩)) _
  let f := (1-g)*P a x + g*P b y
  have hf : f ∈ A.topologicalClosure := A.topologicalClosure.add_mem
    (A.topologicalClosure.mul_mem (A.topologicalClosure.sub_mem A.topologicalClosure.one_mem hg) (hP a x))
    (A.topologicalClosure.mul_mem hg (hP b y))
  change f ∈ closure (A : Set C(K,ℂ)) at hf
  obtain ⟨w,hw,hw'⟩ := Metric.mem_closure_iff.mp hf ε hε
  change w ∈ A.toSubmodule at hw
  rw [show A.toSubmodule = _ from expand z] at hw
  obtain ⟨m,c,s,hs⟩ := (Submodule.mem_span_set' (R:=ℂ)).mp hw
  choose v hv using fun i : Fin m => (s i).prop
  let F := fun u : Fin m → ℂ => ∑ i, u i • waves z (v i)
  have hF : Continuous F := by dsimp [F];fun_prop
  have hc : ∃ u, dist f (F u)<ε := ⟨c,by simpa [F,hv,hs] using hw'⟩
  have dense : DenseRange (fun d : Fin m → ℚ×ℚ => fun i => asComplex (d i)) :=
    DenseRange.piMap (fun _ => rationalCoefficients)
  obtain ⟨d,hd⟩ := dense.exists_mem_open (isOpen_lt (continuous_const.dist hF) continuous_const) hc
  change dist f (P d v)<ε at hd
  have evalP {n : ℕ} (a : Fin n → ℚ×ℚ) (y : Fin n → ℚ) (s : K) : P a y s = poly a y s.val := by
    simp [P,poly,ContinuousMap.sum_apply,waveValue,z]
  refine ⟨m,d,v,fun t ht => ⟨?_,?_⟩⟩
  · let s : K := ⟨pointAt L t,Or.inl ⟨t,abs_le.mp ht,rfl⟩⟩
    have h := (ContinuousMap.dist_apply_le_dist s (f:=f) (g:=P d v)).trans_lt hd
    simpa [f,hL s t rfl,evalP,dist_eq_norm,norm_sub_rev,s] using h
  · let s : K := ⟨pointAt U t,Or.inr ⟨t,abs_le.mp ht,rfl⟩⟩
    have h := (ContinuousMap.dist_apply_le_dist s (f:=f) (g:=P d v)).trans_lt hd
    simpa [f,hU s t rfl,evalP,dist_eq_norm,norm_sub_rev,s] using h
