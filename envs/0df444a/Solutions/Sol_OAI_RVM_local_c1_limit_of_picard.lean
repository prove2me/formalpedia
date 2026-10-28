-- Prove2me | solution 1 for OAI.RVM.local_c1_limit_of_picard
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:34:57.055325+00:00
-- url     : https://prove2.me/submissions/3609c992-2153-43ed-a6c8-939d9473ac94

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeMotion
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary relativistic geometry needed by the retarded-force identity. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM

lemma q_pos (v : Vec) : 0 < q v := by
  exact Real.sqrt_pos.2 (by positivity)

lemma q_sq (v : Vec) : q v ^ 2 = 1 + ‖v‖ ^ 2 := by
  exact Real.sq_sqrt (by positivity)

lemma norm_lt_q (v : Vec) : ‖v‖ < q v := by
  have hp := q_pos v
  have hs := q_sq v
  nlinarith [sq_nonneg ‖v‖, norm_nonneg v]

lemma norm_velocity_lt_one (v : Vec) : ‖velocity v‖ < 1 := by
  rw [velocity, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (q_pos v))]
  rw [← div_eq_inv_mul]
  exact (div_lt_one (q_pos v)).2 (norm_lt_q v)

open scoped Topology

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_ExtendedLorentz
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

lemma contDiff_q {k : ℕ∞ω} : ContDiff ℝ k q := by
  exact ((contDiff_const : ContDiff ℝ k (fun _ : Vec => (1 : ℝ))).add
    (contDiff_id.norm_sq ℝ)).sqrt (fun v => by positivity)

lemma contDiff_velocity {k : ℕ∞ω} : ContDiff ℝ k velocity := by
  exact (contDiff_q.inv (fun v => ne_of_gt (q_pos v))).smul contDiff_id

lemma sum_basis (v : Vec) : ∑ i : Fin 3, v i • basis i = v := by
  ext j
  simp [basis, Pi.single_apply]

lemma clm_sum_basis (L : Vec →L[ℝ] ℝ) (v : Vec) :
    L v = ∑ i : Fin 3, v i * L (basis i) := by
  conv_lhs => rw [← sum_basis v]
  simp only [map_sum, map_smul, smul_eq_mul]

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ParticleBySpacetime
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

lemma compactSupport_of_zero_off {W : Type*} [Zero W]
    {K : Set Vec} {g : Vec → W} (hK : IsCompact K)
    (hz : ∀ v ∉ K, g v = 0) : HasCompactSupport g := by
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro v hv
  by_contra hn
  exact hv (hz v hn)

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_EnergyBump
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

lemma spatialPartial_time_slice {G : ℝ × Vec → ℝ} {t : ℝ} {x : Vec}
    (hG : DifferentiableAt ℝ G (t,x)) (i : Fin 3) :
    spatialPartial (fun y => G (t,y)) x i = fderiv ℝ G (t,x) (0,basis i) := by
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L (basis i))
    (hG.hasFDerivAt.comp x ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))).fderiv

end RVM

end

open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_WaveGradient
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma dirD_component {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F : H → Vec} (hF : Differentiable ℝ F) (p e : H) (i : Fin 3) :
    dirD (fun z => F z i) e p = dirD F e p i := by
  have h := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp p (hF p).hasFDerivAt
  change HasFDerivAt (fun z => F z i) _ p at h
  unfold dirD
  rw [h.fderiv]
  rfl

lemma spaceCurl_apply (F : Field) (p : ℝ × Vec) (i : Fin 3) :
    spaceCurl F p i = dirD F (0,basis (curlA i)) p (curlB i) -
      dirD F (0,basis (curlB i)) p (curlA i) := rfl

lemma spaceCurl_slice {F : Field} (hF : Differentiable ℝ F) (t : ℝ) (x : Vec) :
    spaceCurl F (t,x) = curl (fun y => F (t,y)) x := by
  have hc (i : Fin 3) : Differentiable ℝ (fun p => F p i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).differentiable.comp hF
  have hh (i j : Fin 3) : spatialPartial (fun y => F (t,y) i) x j =
      dirD F (0,basis j) (t,x) i := by
    rw [spatialPartial_time_slice (hc i (t,x))]
    exact dirD_component hF (t,x) (0,basis j) i
  ext i
  fin_cases i <;> simp [spaceCurl_apply,curl,curlA,curlB,hh]

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_SpaceDiv
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma spaceDiv_slice {F : Field} (hF : Differentiable ℝ F) (t : ℝ) (x : Vec) :
    spaceDiv F (t,x) = divergence (fun y => F (t,y)) x := by
  unfold spaceDiv divergence
  apply Finset.sum_congr rfl
  intro i _
  have hc : Differentiable ℝ (fun p => F p i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).differentiable.comp hF
  rw [spatialPartial_time_slice (hc (t,x))]
  exact (dirD_component hF (t,x) (0,basis i) i).symm

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_NullConeFlux
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology NNReal
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory Metric
open scoped Topology Pointwise

namespace RVM

lemma cross_sub_right (a b c : Vec) : cross a (b-c) = cross a b-cross a c := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeRadius
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma fderiv_phase_split {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {g : Phase → H} {y v u K : Vec} (hg : DifferentiableAt ℝ g (y,v)) :
    fderiv ℝ (fun z => g (z,v)) y u+fderiv ℝ (fun w => g (y,w)) v K =
      fderiv ℝ g (y,v) (u,K) := by
  have hiy : HasFDerivAt (fun z : Vec => (z,v))
      ((ContinuousLinearMap.id ℝ Vec).prod (0 : Vec →L[ℝ] Vec)) y :=
    (hasFDerivAt_id y).prodMk (hasFDerivAt_const v y)
  have hiv : HasFDerivAt (fun w : Vec => (y,w))
      ((0 : Vec →L[ℝ] Vec).prod (ContinuousLinearMap.id ℝ Vec)) v :=
    (hasFDerivAt_const y v).prodMk (hasFDerivAt_id v)
  have hy := hg.hasFDerivAt.comp y hiy
  have hv := hg.hasFDerivAt.comp v hiv
  have hy' : fderiv ℝ (fun z => g (z,v)) y u=fderiv ℝ g (y,v) (u,0) := by
    convert congrArg (fun L : Vec →L[ℝ] H => L u) hy.fderiv using 1 <;> rfl
  have hv' : fderiv ℝ (fun w => g (y,w)) v K=fderiv ℝ g (y,v) (0,K) := by
    convert congrArg (fun L : Vec →L[ℝ] H => L K) hv.fderiv using 1 <;> rfl
  rw [hy',hv']
  rw [← map_add]
  congr 1
  ext <;> simp

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_CurvatureBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

lemma CurvatureBound.add {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f g : U → W} {H K : ℝ} (hf : CurvatureBound f H) (hg : CurvatureBound g K) :
    CurvatureBound (fun x => f x+g x) (H+K) := by
  intro x v
  have he : f (x+v)+g (x+v)+(f (x-v)+g (x-v))-(2:ℝ) • (f x+g x)=
      (f (x+v)+f (x-v)-(2:ℝ) • f x)+(g (x+v)+g (x-v)-(2:ℝ) • g x) := by module
  rw [he]
  exact ((norm_add_le _ _).trans (add_le_add (hf x v) (hg x v))).trans_eq (by ring)

lemma CurvatureBound.neg {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} {H : ℝ} (hf : CurvatureBound f H) : CurvatureBound (fun x => -f x) H := by
  intro x v
  simpa only [← neg_add,smul_neg,neg_sub_neg,norm_sub_rev] using hf x v

lemma CurvatureBound.sub {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f g : U → W} {H K : ℝ} (hf : CurvatureBound f H) (hg : CurvatureBound g K) :
    CurvatureBound (fun x => f x-g x) (H+K) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

end


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_CurvatureInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma CurvatureBound.taylor {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} {H : ℝ} (hc : CurvatureBound f H) (hH : 0≤H)
    (hf : Differentiable ℝ f) (x v : U) :
    ‖f (x+v)-f x-fderiv ℝ f x v‖≤H*‖v‖^2 := by
  let q : ℕ → W := fun n => (2:ℝ)^n • (f (x+(1/2:ℝ)^n • v)-f x)
  have hD : HasDerivAt (fun t : ℝ => f (x+t • v)) (fderiv ℝ f x v) 0 := by
    have hd := (hf (x+(0:ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0:ℝ)
      ((hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const v))
    simpa only [zero_smul,add_zero,one_smul,zero_add,Function.comp_def,Pi.add_apply,id_eq] using hd
  have hp : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num),
      Eventually.of_forall (fun n => by simp only [mem_Ioi]; positivity)⟩
  have hq : Tendsto q atTop (𝓝 (fderiv ℝ f x v)) := by
    simpa [Function.comp_def,q,← inv_pow] using hD.tendsto_slope_zero_right.comp hp
  have hb (n : ℕ) : dist (q n) (q (n+1))≤(H*‖v‖^2/2)*(1/2:ℝ)^n := by
    let r : ℝ := (1/2:ℝ)^n
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hn : 0≤(2:ℝ)^n := by positivity
    have hinv : (2:ℝ)^n*r=1 := by dsimp [r]; rw [← mul_pow]; norm_num
    have hcent := hc (x+(r/2) • v) ((r/2) • v)
    rw [show (x+(r/2) • v)+(r/2) • v=x+r • v by module,
      show (x+(r/2) • v)-(r/2) • v=x by module,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ r/2)] at hcent
    have he : q n-q (n+1)=(2:ℝ)^n • (f (x+r • v)+f x-(2:ℝ) • f (x+(r/2) • v)) := by
      dsimp only [q]
      rw [pow_succ,pow_succ]
      change (2:ℝ)^n • (f (x+r • v)-f x)-((2:ℝ)^n*2) • (f (x+(r*(1/2)) • v)-f x)=_
      rw [show r*(1/2)=r/2 by ring]
      module
    rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs,abs_of_nonneg hn]
    apply (mul_le_mul_of_nonneg_left hcent hn).trans
    have heq : (2:ℝ)^n*(H*(r/2*‖v‖)^2)=(H*‖v‖^2/4)*r := by
      calc
        _ = (H*‖v‖^2/4)*((2:ℝ)^n*r)*r := by ring
        _ = _ := by rw [hinv]; ring
    rw [heq]
    change (H*‖v‖^2/4)*r≤(H*‖v‖^2/2)*r
    gcongr
    nlinarith [mul_nonneg hH (sq_nonneg ‖v‖)]
  have hh := dist_le_of_le_geometric_of_tendsto₀ (r:=(1/2:ℝ)) (C:=H*‖v‖^2/2) (by norm_num) hb hq
  simpa only [q,pow_zero,one_smul,dist_eq_norm,show (H*‖v‖^2/2)/(1-(1/2:ℝ))=H*‖v‖^2 by ring] using hh

lemma fderiv_bound_of_curvature {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} {H ε δ : ℝ} (hc : CurvatureBound f H) (hH : 0≤H)
    (hf : Differentiable ℝ f) (hb : ∀ x, ‖f x‖≤ε) (hε : 0≤ε) (hδ : 0<δ) (x : U) :
    ‖fderiv ℝ f x‖≤2*ε/δ+H*δ := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  have hv' : ‖v‖≤1 := hv.le
  have ht := hc.taylor hH hf x (δ • v)
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hδ,map_smul] at ht
  have hb' : ‖f (x+δ • v)-f x‖≤2*ε := (norm_sub_le _ _).trans (by linarith [hb (x+δ • v),hb x])
  have hD : δ*‖fderiv ℝ f x v‖≤2*ε+H*δ^2 := by
    have hh := norm_sub_le (f (x+δ • v)-f x) (f (x+δ • v)-f x-δ • fderiv ℝ f x v)
    rw [sub_sub_cancel,norm_smul,Real.norm_eq_abs,abs_of_pos hδ] at hh
    have hv2 : ‖v‖^2≤1 := by nlinarith [norm_nonneg v]
    nlinarith [mul_le_mul_of_nonneg_left hv2 (show 0≤H*δ^2 by positivity)]
  have hD' : ‖fderiv ℝ f x v‖≤2*ε/δ+H*δ := by
    have hD' : ‖fderiv ℝ f x v‖≤(2*ε+H*δ^2)/δ :=
      (le_div_iff₀ hδ).mpr (by nlinarith [hD])
    convert hD' using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  simpa only [div_one] using hD'

lemma fderiv_difference_bound_of_curvature {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f g : U → W} {H ε δ : ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfc : CurvatureBound f H) (hgc : CurvatureBound g H) (hH : 0≤H)
    (hfg : ∀ x, ‖f x-g x‖≤ε) (hε : 0≤ε) (hδ : 0<δ) (x : U) :
    ‖fderiv ℝ f x-fderiv ℝ g x‖≤2*ε/δ+2*H*δ := by
  have hb := fderiv_bound_of_curvature (hfc.sub hgc) (add_nonneg hH hH) (hf.sub hg) hfg hε hδ x
  change ‖fderiv ℝ (f-g) x‖≤_ at hb
  rwa [fderiv_sub (hf x) (hg x),← two_mul H] at hb

lemma uniform_spatial_derivative_limit {X U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : ℕ → X × U → W} {f : X × U → W} {S : Set X} {H : ℝ} (hH : 0≤H)
    (hF : ∀ n, ∀ t∈S, Differentiable ℝ (fun x => F n (t,x)))
    (hc : ∀ n, ∀ t∈S, CurvatureBound (fun x => F n (t,x)) H)
    (hlim : TendstoUniformlyOn F f atTop {p | p.1∈S}) :
    ∃ D : X × U → (U →L[ℝ] W),
      TendstoUniformlyOn (fun n p => fderiv ℝ (fun x => F n (p.1,x)) p.2) D atTop {p | p.1∈S} ∧
      ∀ t∈S, ∀ x, HasFDerivAt (fun x => f (t,x)) (D (t,x)) x := by
  let DF : ℕ → X × U → (U →L[ℝ] W) := fun n p => fderiv ℝ (fun x => F n (p.1,x)) p.2
  have huc : UniformCauchySeqOn DF atTop {p | p.1∈S} := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    let δ := ε/(8*(H+1))
    let η := ε*δ/8
    have hδ : 0<δ := by dsimp [δ]; positivity
    have hη : 0<η := by dsimp [η]; positivity
    obtain ⟨K,hK⟩ := Metric.uniformCauchySeqOn_iff.mp hlim.uniformCauchySeqOn η hη
    refine ⟨K,?_⟩
    intro m hm n hn p hp
    have hh := fderiv_difference_bound_of_curvature (hF m p.1 hp) (hF n p.1 hp)
      (hc m p.1 hp) (hc n p.1 hp) hH
      (fun x => (show ‖F m (p.1,x)-F n (p.1,x)‖<η by simpa only [dist_eq_norm] using hK m hm n hn (p.1,x) hp).le)
      hη.le hδ p.2
    rw [dist_eq_norm]
    apply hh.trans_lt
    have hd : δ*(8*(H+1))=ε := by dsimp [δ]; exact div_mul_cancel₀ _ (by positivity)
    have he : 2*η/δ=ε/4 := by dsimp [η]; field_simp; ring
    rw [he]
    nlinarith [mul_nonneg hH hδ.le]
  have hpoint (p : X × U) : ∃ a : U →L[ℝ] W, p.1∈S → Tendsto (fun n => DF n p) atTop (𝓝 a) := by
    by_cases hp : p.1∈S
    · obtain ⟨a,ha⟩ := cauchySeq_tendsto_of_complete (huc.cauchySeq hp)
      exact ⟨a,fun _ => ha⟩
    · exact ⟨0,fun h => (hp h).elim⟩
  choose D hD using hpoint
  have hdlim := huc.tendstoUniformlyOn_of_tendsto (fun p hp => hD p hp)
  refine ⟨D,hdlim,?_⟩
  intro t ht x
  have hds : TendstoUniformly (fun n x => DF n (t,x)) (fun x => D (t,x)) atTop := by
    simpa only [Function.comp_def,preimage_ofPred_eq,ht,ofPred_true,tendstoUniformlyOn_univ] using hdlim.comp (fun x : U => (t,x))
  exact hasFDerivAt_of_tendstoUniformly hds (fun n x => (hF n t ht x).hasFDerivAt)
    (fun x => hlim.tendsto_at (x:=(t,x)) ht) x

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_MomentLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma uniform_compact_moment {X W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : ℕ → X → Vec → ℝ} {f : X → Vec → ℝ} {S : Set X} {P : ℝ}
    (hF : ∀ n, ∀ p∈S, Continuous (F n p)) (hf : ∀ p∈S, Continuous (f p))
    (hSF : ∀ n, ∀ p∈S, ∀ v : Vec, P<‖v‖ → F n p v=0)
    (hSf : ∀ p∈S, ∀ v : Vec, P<‖v‖ → f p v=0)
    (hlim : TendstoUniformlyOn (fun n (p : X × Vec) => F n p.1 p.2)
      (fun p => f p.1 p.2) atTop {p | p.1∈S})
    {ψ : Vec → W} (hψ : Continuous ψ) (hbψ : ∀ v, ‖ψ v‖≤1) :
    TendstoUniformlyOn (fun n p => ∫ v, F n p v • ψ v) (fun p => ∫ v, f p v • ψ v) atTop S := by
  let K := closedBall (0:Vec) P
  have hK : IsCompact K := isCompact_closedBall _ _
  have hkiF (n : ℕ) (p : X) (hp : p∈S) : HasCompactSupport (F n p) :=
    compactSupport_of_zero_off hK (fun v hv => hSF n p hp v (by simpa only [K,mem_closedBall_zero_iff,not_le] using hv))
  have hkif (p : X) (hp : p∈S) : HasCompactSupport (f p) :=
    compactSupport_of_zero_off hK (fun v hv => hSf p hp v (by simpa only [K,mem_closedBall_zero_iff,not_le] using hv))
  have hiF (n : ℕ) (p : X) (hp : p∈S) : Integrable (fun v => F n p v • ψ v) :=
    ((hF n p hp).smul hψ).integrable_of_hasCompactSupport (hkiF n p hp).smul_right
  have hif (p : X) (hp : p∈S) : Integrable (fun v => f p v • ψ v) :=
    ((hf p hp).smul hψ).integrable_of_hasCompactSupport (hkif p hp).smul_right
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ := ε/(volume.real K+1)
  have hδ : 0<δ := by dsimp [δ]; positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim δ hδ] with n hn p hp
  rw [dist_eq_norm,← integral_sub (hif p hp) (hiF n p hp)]
  have he : (∫ v in K, f p v • ψ v-F n p v • ψ v)=∫ v, f p v • ψ v-F n p v • ψ v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    have hv' : P<‖v‖ := by simpa only [K,mem_closedBall_zero_iff,not_le] using hv
    simp [hSf p hp v hv',hSF n p hp v hv']
  rw [← he]
  have hb : ∀ v∈K, ‖f p v • ψ v-F n p v • ψ v‖≤δ := by
    intro v hv
    have hh := hn (p,v) hp
    rw [dist_eq_norm,Real.norm_eq_abs] at hh
    rw [← sub_smul,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul hh.le (hbψ v) (norm_nonneg _) hδ.le).trans_eq (mul_one δ)
  apply (norm_setIntegral_le_of_norm_le_const hK.measure_lt_top hb).trans_lt
  have hd : δ*(volume.real K+1)=ε := by dsimp [δ]; exact div_mul_cancel₀ _ (by positivity)
  nlinarith

lemma continuous_velocity_slice {f : Particle} {T t : ℝ}
    (hf : ContinuousOn f {p | p.1∈Icc 0 T}) (ht : t∈Icc 0 T) (x : Vec) :
    Continuous (fun v => f (t,x,v)) := by
  apply continuousOn_univ.mp
  apply hf.comp ((continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn)
  exact fun _ _ => ht

lemma uniform_source_moments {f : ℕ → Particle} {g : Particle} {T A R P : ℝ}
    (hf : ∀ n, ContinuousOn (f n) {p | p.1∈Icc 0 T})
    (hg : ContinuousOn g {p | p.1∈Icc 0 T})
    (hbF : ∀ n, LocalParticleBound T A R P (f n)) (hbG : LocalParticleBound T A R P g)
    (hl : TendstoUniformlyOn f g atTop {p | p.1∈Icc 0 T}) :
    TendstoUniformlyOn (fun n (p : ℝ × Vec) => rho (fun z => f n (p.1,z)) p.2)
      (fun p => rho (fun z => g (p.1,z)) p.2) atTop {p | p.1∈Icc 0 T} ∧
    TendstoUniformlyOn (fun n (p : ℝ × Vec) => current (fun z => f n (p.1,z)) p.2)
      (fun p => current (fun z => g (p.1,z)) p.2) atTop {p | p.1∈Icc 0 T} := by
  have hcF (n : ℕ) (p : ℝ × Vec) (hp : p.1∈Icc 0 T) : Continuous (fun v => f n (p.1,p.2,v)) :=
    continuous_velocity_slice (hf n) hp p.2
  have hcG (p : ℝ × Vec) (hp : p.1∈Icc 0 T) : Continuous (fun v => g (p.1,p.2,v)) :=
    continuous_velocity_slice hg hp p.2
  have hsF (n : ℕ) (p : ℝ × Vec) (hp : p.1∈Icc 0 T) (v : Vec) (hv : P<‖v‖) : f n (p.1,p.2,v)=0 := by
    by_contra hn
    exact (not_le_of_gt hv) ((hbF n p.1 hp p.2 v).2 hn).2
  have hsG (p : ℝ × Vec) (hp : p.1∈Icc 0 T) (v : Vec) (hv : P<‖v‖) : g (p.1,p.2,v)=0 := by
    by_contra hn
    exact (not_le_of_gt hv) ((hbG p.1 hp p.2 v).2 hn).2
  have hl' := hl.comp (fun p : (ℝ × Vec) × Vec => (p.1.1,p.1.2,p.2))
  have hr := uniform_compact_moment hcF hcG hsF hsG hl' (continuous_const (y:=(1:ℝ))) (fun v => by norm_num)
  have hj := uniform_compact_moment hcF hcG hsF hsG hl' (contDiff_velocity (k:=1)).continuous
    (fun v => (norm_velocity_lt_one v).le)
  constructor
  · convert hr using 1; simp only [smul_eq_mul,mul_one,rho]; rfl
  · exact hj

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_PicardCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma hasFDerivWithinAt_uniform_limit_convex {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : ℕ → U → W} {DF : ℕ → U → (U →L[ℝ] W)}
    {f : U → W} {D : U → (U →L[ℝ] W)} {S : Set U}
    (hS : Convex ℝ S) (hcont : ContinuousOn D S)
    (hder : ∀ n, ∀ x∈S, HasFDerivWithinAt (F n) (DF n x) S x)
    (hD : TendstoUniformlyOn DF D atTop S)
    (hf : ∀ x∈S, Tendsto (fun n => F n x) atTop (𝓝 (f x))) {x : U} (hx : x∈S) :
    HasFDerivWithinAt f (D x) S x := by
  rw [hasFDerivWithinAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ,hδ,hnear⟩ := Metric.continuousWithinAt_iff.mp (hcont x hx) (ε/2) (by positivity)
  have hunif := Metric.tendstoUniformlyOn_iff.mp hD (ε/2) (by positivity)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hδ),self_mem_nhdsWithin] with y hy hyS
  apply le_of_tendsto (((hf y hyS).sub (hf x hx)).sub tendsto_const_nhds).norm
  filter_upwards [hunif] with n hn
  apply Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz => (hder n z hz.2).mono inter_subset_right) _
    ((convex_ball _ _).inter hS) ⟨mem_ball_self hδ,hx⟩ ⟨hy,hyS⟩
  intro z hz
  have ha := hn z hz.2
  have hb := hnear hz.2 hz.1
  rw [dist_eq_norm,norm_sub_rev] at ha
  rw [dist_eq_norm] at hb
  exact (norm_sub_le_norm_sub_add_norm_sub _ (D z) _).trans (by linarith)

lemma curl_eq_curlMap {g : Vec → Vec} (hg : Differentiable ℝ g) (x : Vec) :
    curl g x=curlMap (fderiv ℝ g x) := by
  have hi (i j : Fin 3) : spatialPartial (fun y => g y i) x j=(fderiv ℝ g x (basis j)) i := by
    have hh := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp x (hg x).hasFDerivAt
    change HasFDerivAt (fun y => g y i) _ x at hh
    rw [spatialPartial,hh.fderiv]
    rfl
  ext i
  fin_cases i <;> simp [curl,curlMap,hi]

lemma divergence_eq_divMap {g : Vec → Vec} (hg : Differentiable ℝ g) (x : Vec) :
    divergence g x=divMap (fderiv ℝ g x) := by
  change (∑ i : Fin 3, spatialPartial (fun y => g y i) x i)=∑ i : Fin 3, (fderiv ℝ g x) (basis i) i
  apply Finset.sum_congr rfl
  intro i hi
  have hh := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp x (hg x).hasFDerivAt
  change HasFDerivAt (fun y => g y i) _ x at hh
  rw [spatialPartial,hh.fderiv]
  rfl

lemma fderiv_spatial_slice {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : ℝ × U → W} (hF : Differentiable ℝ F) (p : ℝ × U) :
    fderiv ℝ (fun x => F (p.1,x)) p.2=(fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ ℝ U) :=
  ((hF p).hasFDerivAt.comp p.2 ((hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2))).fderiv

lemma fderiv_eq_assemble {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : ℝ × U → W} (hF : Differentiable ℝ F) (p : ℝ × U) :
    fderiv ℝ F p=assembleDerivative (fderiv ℝ F p (1,0)) (fderiv ℝ (fun x => F (p.1,x)) p.2) := by
  rw [fderiv_spatial_slice hF]
  apply ContinuousLinearMap.ext
  intro z
  change fderiv ℝ F p z=z.1 • fderiv ℝ F p (1,0)+fderiv ℝ F p (0,z.2)
  rw [← map_smul,← map_add]
  congr 1
  ext <;> simp

lemma uniform_assembleDerivative {X U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {A : ℕ → X → W} {D : ℕ → X → (U →L[ℝ] W)}
    {a : X → W} {d : X → (U →L[ℝ] W)} {S : Set X}
    (hA : TendstoUniformlyOn A a atTop S) (hD : TendstoUniformlyOn D d atTop S) :
    TendstoUniformlyOn (fun n x => assembleDerivative (A n x) (D n x))
      (fun x => assembleDerivative (a x) (d x)) atTop S := by
  have ha := ((ContinuousLinearMap.smulRightL ℝ (ℝ × U) W (ContinuousLinearMap.fst ℝ ℝ U)).uniformContinuous).comp_tendstoUniformlyOn hA
  have hd := (((ContinuousLinearMap.compL ℝ (ℝ × U) U W).flip (ContinuousLinearMap.snd ℝ ℝ U)).uniformContinuous).comp_tendstoUniformlyOn hD
  exact ha.add hd

lemma uniform_clm_apply_bounded {X U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {A : ℕ → X → (U →L[ℝ] W)} {U' : ℕ → X → U}
    {a : X → (U →L[ℝ] W)} {u : X → U} {S : Set X} {M N : ℝ}
    (hM : 0≤M) (hN : 0≤N)
    (hA : TendstoUniformlyOn A a atTop S) (hu : TendstoUniformlyOn U' u atTop S)
    (hbA : ∀ n, ∀ x∈S, ‖A n x‖≤M) (hbu : ∀ x∈S, ‖u x‖≤N) :
    TendstoUniformlyOn (fun n x => A n x (U' n x)) (fun x => a x (u x)) atTop S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ := ε/(2*(M+N+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hA δ hδ,
    Metric.tendstoUniformlyOn_iff.mp hu δ hδ] with n hnA hnu x hx
  rw [dist_comm,dist_eq_norm]
  have h1 := hnA x hx
  have h2 := hnu x hx
  rw [dist_comm,dist_eq_norm] at h1 h2
  have he : A n x (U' n x)-a x (u x)=A n x (U' n x-u x)+(A n x-a x) (u x) := by simp
  rw [he]
  apply (norm_add_le _ _).trans_lt
  have hb1 : ‖A n x (U' n x-u x)‖≤M*δ := (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul (hbA n x hx) h2.le (norm_nonneg _) hM)
  have hb2 : ‖(A n x-a x) (u x)‖≤δ*N := (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul h1.le (hbu x hx) (norm_nonneg _) hδ.le)
  have hd : δ*(2*(M+N+1))=ε := by dsimp [δ]; exact div_mul_cancel₀ _ (by positivity)
  nlinarith

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma c1_slab_uniform_derivative {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : ℕ → ℝ × U → W} {f : ℝ × U → W} {D : ℝ × U → ((ℝ × U) →L[ℝ] W)} {T : ℝ}
    (hT : 0<T) (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (hf : TendstoUniformlyOn F f atTop {p | p.1∈Icc 0 T})
    (hD : TendstoUniformlyOn (fun n p => fderiv ℝ (F n) p) D atTop {p | p.1∈Icc 0 T}) :
    ContDiffOn ℝ 1 f {p | p.1∈Icc 0 T} ∧
      ∀ p, p.1∈Icc 0 T → HasFDerivWithinAt f (D p) {p | p.1∈Icc 0 T} p := by
  have he : {p : ℝ × U | p.1∈Icc 0 T}=Icc 0 T ×ˢ (univ : Set U) := by ext p; simp
  have hconv : Convex ℝ {p : ℝ × U | p.1∈Icc 0 T} := by rw [he]; exact (convex_Icc (𝕜:=ℝ) 0 T).prod (convex_univ : Convex ℝ (univ : Set U))
  have hu : UniqueDiffOn ℝ {p : ℝ × U | p.1∈Icc 0 T} := by rw [he]; exact (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  have hDc : ContinuousOn D {p | p.1∈Icc 0 T} := hD.continuousOn
    (Frequently.of_forall fun n => ((hF n).continuous_fderiv (by simp)).continuousOn)
  have hd (p : ℝ × U) (hp : p.1∈Icc 0 T) := hasFDerivWithinAt_uniform_limit_convex hconv hDc
    (fun n q hq => (((hF n).differentiable (by simp)) q).hasFDerivAt.hasFDerivWithinAt)
    hD (fun q hq => hf.tendsto_at hq) hp
  refine ⟨?_,hd⟩
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n:=0) hu).mpr
  exact ⟨by simp, D, contDiffOn_zero.mpr hDc,hd⟩

lemma picard_field_full_derivative_limit {d : Datum} {S : ℕ → Solution}
    {E B : Field} {f : Particle} {T A R P H : ℝ} (_ : 0<T) (hH : 0≤H)
    (hr : ∀ n, PicardRegular d (S (n+1)))
    (hc : ∀ n, SpatialFieldCurvature T H (S (n+1)).E (S (n+1)).B)
    (hb : ∀ n, LocalParticleBound T A R P (S (n+1)).f)
    (hbf : LocalParticleBound T A R P f)
    (hfc : ContinuousOn f {p | p.1∈Icc 0 T})
    (hfl : TendstoUniformlyOn (fun n => (S (n+1)).f) f atTop {p | p.1∈Icc 0 T})
    (hEl : TendstoUniformlyOn (fun n => (S (n+1)).E) E atTop {p | p.1∈Icc 0 T})
    (hBl : TendstoUniformlyOn (fun n => (S (n+1)).B) B atTop {p | p.1∈Icc 0 T}) :
    ∃ XE XB : ℝ × Vec → (Vec →L[ℝ] Vec),
      TendstoUniformlyOn (fun n p => fderiv ℝ (fun x => (S (n+1)).E (p.1,x)) p.2) XE atTop {p | p.1∈Icc 0 T} ∧
      TendstoUniformlyOn (fun n p => fderiv ℝ (fun x => (S (n+1)).B (p.1,x)) p.2) XB atTop {p | p.1∈Icc 0 T} ∧
      (∀ t∈Icc 0 T, ∀ x, HasFDerivAt (fun y => E (t,y)) (XE (t,x)) x ∧
        HasFDerivAt (fun y => B (t,y)) (XB (t,x)) x) ∧
      TendstoUniformlyOn (fun n p => fderiv ℝ (S (n+1)).E p)
        (fun p => assembleDerivative (curlMap (XB p)-current (fun z => f (p.1,z)) p.2) (XE p)) atTop {p | p.1∈Icc 0 T} ∧
      TendstoUniformlyOn (fun n p => fderiv ℝ (S (n+1)).B p)
        (fun p => assembleDerivative (-curlMap (XE p)) (XB p)) atTop {p | p.1∈Icc 0 T} ∧
      (∀ p : ℝ × Vec, p.1∈Icc 0 T → divMap (XE p)=rho (fun z => f (p.1,z)) p.2 ∧ divMap (XB p)=0) := by
  have hEslice (n : ℕ) (t : ℝ) : Differentiable ℝ (fun x => (S (n+1)).E (t,x)) :=
    ((hr n).smooth_E.differentiable (by simp)).comp ((differentiable_const t).prodMk differentiable_id)
  have hBslice (n : ℕ) (t : ℝ) : Differentiable ℝ (fun x => (S (n+1)).B (t,x)) :=
    ((hr n).smooth_B.differentiable (by simp)).comp ((differentiable_const t).prodMk differentiable_id)
  obtain ⟨XE,hXE,hdE⟩ := uniform_spatial_derivative_limit hH (fun n t ht => hEslice n t)
    (fun n t ht => (hc n t ht).1) hEl
  obtain ⟨XB,hXB,hdB⟩ := uniform_spatial_derivative_limit hH (fun n t ht => hBslice n t)
    (fun n t ht => (hc n t ht).2) hBl
  obtain ⟨hρ,hj⟩ := uniform_source_moments (fun n => (hr n).smooth_f.continuous.continuousOn) hfc hb hbf hfl
  have hcurlE := curlMap.uniformContinuous.comp_tendstoUniformlyOn hXE
  have hcurlB := curlMap.uniformContinuous.comp_tendstoUniformlyOn hXB
  have htE := hcurlB.sub hj
  have htB := hcurlE.neg
  have hfullE := uniform_assembleDerivative htE hXE
  have hfullB := uniform_assembleDerivative htB hXB
  have he (n : ℕ) (p : ℝ × Vec) (hp : p.1∈Icc 0 T) :
      fderiv ℝ (S (n+1)).E p=assembleDerivative
        (curlMap (fderiv ℝ (fun x => (S (n+1)).B (p.1,x)) p.2)-current (fun z => (S (n+1)).f (p.1,z)) p.2)
        (fderiv ℝ (fun x => (S (n+1)).E (p.1,x)) p.2) := by
    rw [fderiv_eq_assemble ((hr n).smooth_E.differentiable (by simp))]
    congr 1
    have hh := ((hr n).maxwell p.1 hp.1 p.2).1
    rw [spaceCurl_slice ((hr n).smooth_B.differentiable (by simp)),curl_eq_curlMap (hBslice n p.1)] at hh
    exact hh
  have hb' (n : ℕ) (p : ℝ × Vec) (hp : p.1∈Icc 0 T) :
      fderiv ℝ (S (n+1)).B p=assembleDerivative
        (-curlMap (fderiv ℝ (fun x => (S (n+1)).E (p.1,x)) p.2))
        (fderiv ℝ (fun x => (S (n+1)).B (p.1,x)) p.2) := by
    rw [fderiv_eq_assemble ((hr n).smooth_B.differentiable (by simp))]
    congr 1
    have hh := ((hr n).maxwell p.1 hp.1 p.2).2.1
    rw [spaceCurl_slice ((hr n).smooth_E.differentiable (by simp)),curl_eq_curlMap (hEslice n p.1)] at hh
    exact hh
  refine ⟨XE,XB,hXE,hXB,fun t ht x => ⟨hdE t ht x,hdB t ht x⟩,
    hfullE.congr (Eventually.of_forall fun n p hp => (he n p hp).symm),
    hfullB.congr (Eventually.of_forall fun n p hp => (hb' n p hp).symm),?_⟩
  intro p hp
  have hde := (divMap.uniformContinuous.comp_tendstoUniformlyOn hXE).tendsto_at hp
  have hdb := (divMap.uniformContinuous.comp_tendstoUniformlyOn hXB).tendsto_at hp
  have heq (n : ℕ) : divMap (fderiv ℝ (fun x => (S (n+1)).E (p.1,x)) p.2)=rho (fun z => (S (n+1)).f (p.1,z)) p.2 := by
    rw [← divergence_eq_divMap (hEslice n p.1),← spaceDiv_slice ((hr n).smooth_E.differentiable (by simp))]
    exact ((hr n).maxwell p.1 hp.1 p.2).2.2.1
  have hbq (n : ℕ) : divMap (fderiv ℝ (fun x => (S (n+1)).B (p.1,x)) p.2)=0 := by
    rw [← divergence_eq_divMap (hBslice n p.1),← spaceDiv_slice ((hr n).smooth_B.differentiable (by simp))]
    exact ((hr n).maxwell p.1 hp.1 p.2).2.2.2
  change Tendsto (fun n => divMap (fderiv ℝ (fun x => (S (n+1)).E (p.1,x)) p.2)) _ _ at hde
  change Tendsto (fun n => divMap (fderiv ℝ (fun x => (S (n+1)).B (p.1,x)) p.2)) _ _ at hdb
  simp only [heq,hbq] at hde hdb
  exact ⟨tendsto_nhds_unique hde (hρ.tendsto_at hp),tendsto_nhds_unique hdb tendsto_const_nhds⟩

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_ParticleC1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma lorentzField_same_point_bound (E B E' B' : Field) (p : ℝ × Phase) :
    ‖lorentzField E B p-lorentzField E' B' p‖≤
      ‖E (p.1,p.2.1)-E' (p.1,p.2.1)‖+‖B (p.1,p.2.1)-B' (p.1,p.2.1)‖ := by
  have he : E (p.1,p.2.1)+cross (velocity p.2.2) (B (p.1,p.2.1))-
      (E' (p.1,p.2.1)+cross (velocity p.2.2) (B' (p.1,p.2.1)))=
      E (p.1,p.2.1)-E' (p.1,p.2.1)+cross (velocity p.2.2) (B (p.1,p.2.1)-B' (p.1,p.2.1)) := by
    rw [cross_sub_right]; abel
  have hb := (norm_cross_le (velocity p.2.2) (B (p.1,p.2.1)-B' (p.1,p.2.1))).trans
    (mul_le_mul_of_nonneg_right (norm_velocity_lt_one p.2.2).le (norm_nonneg _))
  change max ‖velocity p.2.2-velocity p.2.2‖
    ‖E (p.1,p.2.1)+cross (velocity p.2.2) (B (p.1,p.2.1))-
      (E' (p.1,p.2.1)+cross (velocity p.2.2) (B' (p.1,p.2.1)))‖≤_
  rw [sub_self,norm_zero,he]
  exact max_le (by positivity) ((norm_add_le _ _).trans (add_le_add le_rfl (by simpa only [one_mul] using hb)))

lemma uniform_lorentzField {E B : ℕ → Field} {e b : Field} {T : ℝ}
    (hE : TendstoUniformlyOn E e atTop {p | p.1∈Icc 0 T})
    (hB : TendstoUniformlyOn B b atTop {p | p.1∈Icc 0 T}) :
    TendstoUniformlyOn (fun n => lorentzField (E n) (B n)) (lorentzField e b) atTop {p | p.1∈Icc 0 T} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hE (ε/2) (by positivity),
    Metric.tendstoUniformlyOn_iff.mp hB (ε/2) (by positivity)] with n hnE hnB p hp
  have he := hnE (p.1,p.2.1) hp
  have hb := hnB (p.1,p.2.1) hp
  rw [dist_comm,dist_eq_norm] at he hb ⊢
  exact (lorentzField_same_point_bound _ _ _ _ p).trans_lt (by linarith)

lemma lorentzField_norm_bound {E B : Field} {T L : ℝ}
    (hL : 0≤L) (hb : GlobalFieldBound T L E B) (p : ℝ × Phase) (hp : p.1∈Icc 0 T) :
    ‖lorentzField E B p‖≤1+2*L := by
  have hh := hb p.1 hp p.2.1
  have hc := (norm_cross_le (velocity p.2.2) (B (p.1,p.2.1))).trans
    (mul_le_mul (norm_velocity_lt_one p.2.2).le hh.2 (norm_nonneg _) zero_le_one)
  change max ‖velocity p.2.2‖ ‖E (p.1,p.2.1)+cross (velocity p.2.2) (B (p.1,p.2.1))‖≤_
  exact max_le ((norm_velocity_lt_one p.2.2).le.trans (by linarith))
    ((norm_add_le _ _).trans (by linarith))

lemma picard_particle_full_derivative_limit {d : Datum} {S : ℕ → Solution}
    {E B : Field} {f : Particle} {T H M L : ℝ} (hH : 0≤H) (hM : 0≤M) (hL : 0≤L)
    (hr : ∀ n, PicardRegular d (S (n+1)))
    (htransport : ∀ n, TransportFor (S (n+1)) (S n).E (S n).B)
    (hc : ∀ n, PhaseParticleCurvature T H (S (n+1)).f)
    (hlip : ∀ n, PhaseParticleLip T M (S (n+1)).f)
    (hlb : GlobalFieldBound T L E B)
    (hfl : TendstoUniformlyOn (fun n => (S (n+1)).f) f atTop {p | p.1∈Icc 0 T})
    (hEl : TendstoUniformlyOn (fun n => (S n).E) E atTop {p | p.1∈Icc 0 T})
    (hBl : TendstoUniformlyOn (fun n => (S n).B) B atTop {p | p.1∈Icc 0 T}) :
    ∃ Z : ℝ × Phase → (Phase →L[ℝ] ℝ),
      TendstoUniformlyOn (fun n p => fderiv ℝ (fun z => (S (n+1)).f (p.1,z)) p.2) Z atTop {p | p.1∈Icc 0 T} ∧
      (∀ t∈Icc 0 T, ∀ z, HasFDerivAt (fun w => f (t,w)) (Z (t,z)) z) ∧
      TendstoUniformlyOn (fun n p => fderiv ℝ (S (n+1)).f p)
        (fun p => assembleDerivative (-Z p (lorentzField E B p)) (Z p)) atTop {p | p.1∈Icc 0 T} := by
  have hs (n : ℕ) (t : ℝ) : Differentiable ℝ (fun z => (S (n+1)).f (t,z)) :=
    ((hr n).smooth_f.differentiable (by simp)).comp ((differentiable_const t).prodMk differentiable_id)
  obtain ⟨Z,hZ,hdZ⟩ := uniform_spatial_derivative_limit hH (fun n t ht => hs n t) hc hfl
  have hbZ (n : ℕ) (p : ℝ × Phase) (hp : p.1∈Icc 0 T) :
      ‖fderiv ℝ (fun z => (S (n+1)).f (p.1,z)) p.2‖≤M := by
    apply norm_fderiv_le_of_lip' ℝ hM
    exact Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hlip n p.1 hp z p.2
  have heval := uniform_clm_apply_bounded hM (show 0≤1+2*L by positivity)
    hZ (uniform_lorentzField hEl hBl) hbZ (lorentzField_norm_bound hL hlb)
  have hh := uniform_assembleDerivative heval.neg hZ
  refine ⟨Z,hZ,hdZ,hh.congr (Eventually.of_forall fun n p hp => ?_)⟩
  symm
  change fderiv ℝ (S (n+1)).f p=assembleDerivative
    (-fderiv ℝ (fun z => (S (n+1)).f (p.1,z)) p.2 (lorentzField (S n).E (S n).B p))
    (fderiv ℝ (fun z => (S (n+1)).f (p.1,z)) p.2)
  rw [fderiv_eq_assemble ((hr n).smooth_f.differentiable (by simp))]
  congr 1
  have ht := htransport n p.1 p.2
  change fderiv ℝ (S (n+1)).f p (1,lorentzField (S n).E (S n).B p)=0 at ht
  have he : ((1 : ℝ),lorentzField (S n).E (S n).B p)=(1,0)+(0,lorentzField (S n).E (S n).B p) := by simp
  rw [he,map_add] at ht
  rw [fderiv_spatial_slice ((hr n).smooth_f.differentiable (by simp))]
  exact eq_neg_of_add_eq_zero_left ht

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_SlabEquations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma derivWithin_slab_assemble {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : ℝ × U → W} {a : W} {A : U →L[ℝ] W} {t T : ℝ} {x : U}
    (hT : 0<T) (ht : t∈Icc 0 T)
    (hd : HasFDerivWithinAt F (assembleDerivative a A) {p | p.1∈Icc 0 T} (t,x)) :
    derivWithin (fun r => F (r,x)) (Icc 0 T) t=a := by
  have hh := hd.comp_hasDerivWithinAt t
    (((hasDerivAt_id t).prodMk (hasDerivAt_const t x)).hasDerivWithinAt (s:=Icc 0 T))
    (fun r hr => hr)
  have he : assembleDerivative a A (1,0)=a := by simp [assembleDerivative]
  simpa only [Function.comp_def,id_eq,he] using hh.derivWithin (uniqueDiffOn_Icc hT t ht)

lemma slab_equations_of_derivatives {s : Solution} {T : ℝ} (hT : 0<T)
    {Z : ℝ × Phase → (Phase →L[ℝ] ℝ)} {XE XB : ℝ × Vec → (Vec →L[ℝ] Vec)}
    (hf : ∀ p : ℝ × Phase, p.1∈Icc 0 T → HasFDerivWithinAt s.f
      (assembleDerivative (-Z p (lorentzField s.E s.B p)) (Z p)) (particleSlab T) p)
    (hE : ∀ p : ℝ × Vec, p.1∈Icc 0 T → HasFDerivWithinAt s.E
      (assembleDerivative (curlMap (XB p)-current (fun z => s.f (p.1,z)) p.2) (XE p)) (fieldSlab T) p)
    (hB : ∀ p : ℝ × Vec, p.1∈Icc 0 T → HasFDerivWithinAt s.B
      (assembleDerivative (-curlMap (XE p)) (XB p)) (fieldSlab T) p)
    (hZ : ∀ t∈Icc 0 T, ∀ z, HasFDerivAt (fun w => s.f (t,w)) (Z (t,z)) z)
    (hXE : ∀ t∈Icc 0 T, ∀ x, HasFDerivAt (fun y => s.E (t,y)) (XE (t,x)) x)
    (hXB : ∀ t∈Icc 0 T, ∀ x, HasFDerivAt (fun y => s.B (t,y)) (XB (t,x)) x)
    (hGauss : ∀ p : ℝ × Vec, p.1∈Icc 0 T → divMap (XE p)=rho (fun z => s.f (p.1,z)) p.2 ∧ divMap (XB p)=0) :
    SlabEquations s T := by
  intro t ht
  have hsE : Differentiable ℝ (fun y => s.E (t,y)) := fun x => (hXE t ht x).differentiableAt
  have hsB : Differentiable ℝ (fun y => s.B (t,y)) := fun x => (hXB t ht x).differentiableAt
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro x v
    rw [derivWithin_slab_assemble hT ht (hf (t,x,v) ht)]
    simp only [spatialPartial]
    rw [← clm_sum_basis,← clm_sum_basis]
    rw [add_assoc,fderiv_phase_split (hZ t ht (x,v)).differentiableAt,(hZ t ht (x,v)).fderiv]
    exact neg_add_cancel _
  · intro x
    rw [derivWithin_slab_assemble hT ht (hE (t,x) ht),curl_eq_curlMap hsB,(hXB t ht x).fderiv]
    abel
  · intro x
    rw [derivWithin_slab_assemble hT ht (hB (t,x) ht),curl_eq_curlMap hsE,(hXE t ht x).fderiv]
    exact neg_add_cancel _
  · intro x
    rw [divergence_eq_divMap hsE,(hXE t ht x).fderiv]
    exact (hGauss (t,x) ht).1
  · intro x
    rw [divergence_eq_divMap hsB,(hXB t ht x).fderiv]
    exact (hGauss (t,x) ht).2

lemma local_c1_limit_of_picard_oai {d : Datum} {S : ℕ → Solution} {s : Solution}
    {T A R P H Hf M L : ℝ} (hT : 0<T) (hH : 0≤H) (hHf : 0≤Hf) (hM : 0≤M) (hL : 0≤L)
    (hr : ∀ n, PicardRegular d (S (n+1)))
    (htransport : ∀ n, TransportFor (S (n+1)) (S n).E (S n).B)
    (hc : ∀ n, SpatialFieldCurvature T H (S n).E (S n).B)
    (hcf : ∀ n, PhaseParticleCurvature T Hf (S (n+1)).f)
    (hb : ∀ n, LocalParticleBound T A R P (S (n+1)).f)
    (hlip : ∀ n, PhaseParticleLip T M (S (n+1)).f)
    (hlb : GlobalFieldBound T L s.E s.B)
    (hbf : LocalParticleBound T A R P s.f)
    (hfc : ContinuousOn s.f (particleSlab T))
    (hfl : TendstoUniformlyOn (fun n => (S (n+1)).f) s.f atTop (particleSlab T))
    (hEl : TendstoUniformlyOn (fun n => (S n).E) s.E atTop (fieldSlab T))
    (hBl : TendstoUniformlyOn (fun n => (S n).B) s.B atTop (fieldSlab T)) :
    ContDiffOn ℝ 1 s.f (particleSlab T) ∧ ContDiffOn ℝ 1 s.E (fieldSlab T) ∧
      ContDiffOn ℝ 1 s.B (fieldSlab T) ∧ SlabEquations s T := by
  have hEl' := hEl.seq_tendstoUniformlyOn (fun n => n+1) (tendsto_add_atTop_nat 1)
  have hBl' := hBl.seq_tendstoUniformlyOn (fun n => n+1) (tendsto_add_atTop_nat 1)
  obtain ⟨XE,XB,hXE,hXB,hs,hDE,hDB,hGauss⟩ := picard_field_full_derivative_limit hT hH hr
    (fun n => hc (n+1)) hb hbf hfc hfl hEl' hBl'
  obtain ⟨Z,hZ,hsZ,hDf⟩ := picard_particle_full_derivative_limit hHf hM hL hr htransport hcf hlip hlb hfl hEl hBl
  obtain ⟨hfC,hdf⟩ := c1_slab_uniform_derivative hT (fun n => (hr n).smooth_f) hfl hDf
  obtain ⟨hEC,hdE⟩ := c1_slab_uniform_derivative hT (fun n => (hr n).smooth_E) hEl' hDE
  obtain ⟨hBC,hdB⟩ := c1_slab_uniform_derivative hT (fun n => (hr n).smooth_B) hBl' hDB
  exact ⟨hfC,hEC,hBC,slab_equations_of_derivatives hT hdf hdE hdB hsZ
    (fun t ht x => (hs t ht x).1) (fun t ht x => (hs t ht x).2) hGauss⟩

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.local_c1_limit_of_picard_oai := @OAI.RVM.local_c1_limit_of_picard_oai
