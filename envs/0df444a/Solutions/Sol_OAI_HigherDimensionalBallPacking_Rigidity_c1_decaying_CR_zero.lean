-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.c1_decaying_CR_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T16:54:56.508224+00:00
-- url     : https://prove2.me/submissions/abe62d50-4a65-45d2-ae65-6cbd649e45e7

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp005
import Definitions.Def_OAIQ10Bp006

section
-- module Solutions.OAIQ10_BP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_CompatibleStructures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity

theorem stdDot_symm {n : ℕ} (v w : Phase n) : stdDot n v w = stdDot n w v := by
  simp only [stdDot_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem standardForm_skew {n : ℕ} (v w : Phase n) :
    standardForm v w = -standardForm w v := by
  unfold standardForm
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_RadialForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

theorem capacity_hasFDerivAt {n : ℕ} (x : Phase n) :
    HasFDerivAt capacity ((2 * Real.pi) • stdDot n x) x := by
  have hd := ((stdDot n).hasFDerivAt).clm_apply (hasFDerivAt_id x)
  have hh := hd.const_mul Real.pi
  have he : Real.pi • ((stdDot n x).comp (ContinuousLinearMap.id ℝ (Phase n)) +
      (stdDot n).flip x) = (2 * Real.pi) • stdDot n x := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [smul_apply, add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
    rw [stdDot_symm v x]
    ring
  simp only [id_eq] at hh
  rw [he] at hh
  have hefunc : (@capacity n) = fun y => Real.pi * stdDot n y y := funext capacity_eq_stdDot
  rw [hefunc]
  exact hh

theorem infinityGerm_eventuallyEq {n : ℕ} (u : ℂ → Phase n) (v : Phase n)
    {w : ℂ} (hw : w ≠ 0) :
    infinityGerm u v =ᶠ[𝓝 w] fun z => z • u z⁻¹ := by
  filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hw] with z hz
  exact ite_eq_right hz

theorem infinityGerm_analyticAt {n : ℕ} {u : ℂ → Phase n} {v : Phase n}
    (hholo : ∀ᶠ z in cocompact ℂ, DifferentiableAt ℂ u z)
    (hlim : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 v)) :
    AnalyticAt ℂ (infinityGerm u v) 0 := by
  have hi : Tendsto (fun w : ℂ => w⁻¹) (𝓝[≠] 0) (cocompact ℂ) := by
    rw [←Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_nhdsNE_zero
  have ht : Tendsto (fun w : ℂ => w • u w⁻¹) (𝓝[≠] 0) (𝓝 v) := by
    simpa only [Function.comp_def,inv_inv] using hlim.comp hi
  have he : infinityGerm u v = Function.update (fun w : ℂ => w • u w⁻¹) 0 v := by
    classical
    funext w
    by_cases hw : w = 0
    · subst w; simp [infinityGerm]
    · simp [infinityGerm,hw]
  have hc : ContinuousAt (infinityGerm u v) 0 := by
    classical
    rw [he,continuousAt_update_same]
    exact ht
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ hc
  filter_upwards [hi.eventually hholo,self_mem_nhdsWithin] with w hw hw0
  have hn : w ≠ 0 := hw0
  have hd : DifferentiableAt ℂ (fun z : ℂ => z • u z⁻¹) w :=
    differentiableAt_id.smul (hw.comp w (differentiableAt_id.inv hn))
  exact hd.congr_of_eventuallyEq (infinityGerm_eventuallyEq u v hn)

end HigherDimensionalBallPacking.Rigidity

namespace SymplecticBallPacking.Hamiltonian
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

theorem HasCompactSupport.comp_radiusSq {F : Type*} [Zero F] {g : ℝ → F}
    (hg : HasCompactSupport g) : HasCompactSupport (fun z : Plane => g (radiusSq z)) := by
  obtain ⟨B,hB,hbound⟩ := hg.isBounded.exists_pos_norm_le
  apply HasCompactSupport.intro ((isCompact_Icc : IsCompact (Icc (-(B+1)) (B+1))).prod (isCompact_Icc : IsCompact (Icc (-(B+1)) (B+1))))
  intro z hz
  by_contra hg0
  have hb := hbound (radiusSq z) (subset_tsupport g hg0)
  have hq : 0 ≤ radiusSq z := add_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [Real.norm_eq_abs,abs_of_nonneg hq] at hb
  apply hz
  dsimp only [radiusSq] at hb
  constructor <;> constructor <;> nlinarith [sq_nonneg z.1,sq_nonneg z.2]

theorem HasCompactSupport.comp_square {F : Type*} [Zero F] {g : ℝ → F}
    (hg : HasCompactSupport g) : HasCompactSupport (fun x : ℝ => g (x^2)) := by
  simpa only [radiusSq,zero_pow (by decide : (2:ℕ)≠0),add_zero] using
    HasCompactSupport.left_slice (HasCompactSupport.comp_radiusSq hg) 0

theorem integral_radial_derivative {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) : (∫ z : Plane,2*deriv g (radiusSq z))= -2*Real.pi*g 0 := by
  let h : ℝ → ℝ := fun r => g (r^2)
  have hh : ContDiff ℝ ∞ h := hg.comp (contDiff_id.pow 2)
  have hhC : HasCompactSupport h := HasCompactSupport.comp_square hc
  have hd (r : ℝ) : deriv h r=2*r*deriv g (r^2) := by
    have H := (hg.differentiable (by simp) (r^2)).hasDerivAt.comp r ((hasDerivAt_id r).pow 2)
    change HasDerivAt h _ r at H
    rw [H.deriv]
    simp only [Nat.cast_ofNat,mul_one,id_eq]
    norm_num
    ring
  rw [← integral_comp_polarCoord_symm]
  have he : (fun p : Plane => p.1 • (2*deriv g (radiusSq (polarCoord.symm p))))=
      (fun p : Plane => deriv h p.1 * (1 : ℝ)) := by
    funext p
    rw [radiusSq_polar,hd]
    simp only [smul_eq_mul]
    ring
  rw [he,polarCoord_target,Measure.volume_eq_prod,setIntegral_prod_mul (deriv h) (fun _ : ℝ => (1 : ℝ)),
    HasCompactSupport.integral_Ioi_deriv_eq (hh.of_le (by simp)) hhC]
  simp only [h,zero_pow (by decide : (2:ℕ)≠0),integral_const,smul_eq_mul,
    Measure.real,Measure.restrict_apply_univ,Real.volume_Ioo]
  rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : 0≤Real.pi-(-Real.pi))]
  ring

theorem radiusSq_hasFDerivAt (z : Plane) :
    HasFDerivAt radiusSq ((2:ℝ) • planarDot z) z := by
  have H := (((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := z)).pow 2).add
    (((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := z)).pow 2)
  change HasFDerivAt radiusSq _ z at H
  apply H.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  change (2 • z.1^(2-1))*v.1+(2 • z.2^(2-1))*v.2=2*(z.1*v.1+z.2*v.2)
  norm_num
  ring

end SymplecticBallPacking.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_PlanarResidueCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SymplecticBallPacking.Hamiltonian
open Set Function MeasureTheory Filter
open scoped ContDiff Topology

theorem planarCurl_contDiff {β : Plane → Plane →L[ℝ] ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (planarCurl β) :=
  (((hβ.fderiv_right (by simp)).clm_apply contDiff_const).clm_apply contDiff_const).sub
    (((hβ.fderiv_right (by simp)).clm_apply contDiff_const).clm_apply contDiff_const)

theorem planarCurl_compact {β : Plane → Plane →L[ℝ] ℝ} (hβ : HasCompactSupport β) :
    HasCompactSupport (planarCurl β) := by
  exact ((hβ.fderiv_apply (𝕜 := ℝ) (1,0)).comp_left
    (g := fun L : Plane →L[ℝ] ℝ => L (0,1)) rfl).sub
    ((hβ.fderiv_apply (𝕜 := ℝ) (0,1)).comp_left
    (g := fun L : Plane →L[ℝ] ℝ => L (1,0)) rfl)

theorem planarCurl_spatial_smul {f : Plane → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    {z : Plane}
    (hf : DifferentiableAt ℝ f z) (hβ : DifferentiableAt ℝ β z) :
    planarCurl (fun y => f y • β y) z=cutoffWedge f β z+f z*planarCurl β z := by
  unfold planarCurl cutoffWedge
  have H := hf.hasFDerivAt.smul hβ.hasFDerivAt
  change HasFDerivAt (fun y => f y • β y) _ z at H
  rw [H.fderiv]
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,smul_apply,smul_eq_mul]
  ring

theorem integral_cutoffWedge {f : Plane → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hβ : ContDiff ℝ ∞ β) :
    (∫ z,cutoffWedge f β z)= -(∫ z,f z*planarCurl β z) := by
  have hp : ContDiff ℝ ∞ (fun z => f z • β z) := hf.smul hβ
  have hpc : HasCompactSupport (fun z => f z • β z) := hc.smul_right
  have hci : Integrable (planarCurl (fun z => f z • β z)) := (planarCurl_contDiff hp).continuous.integrable_of_hasCompactSupport (planarCurl_compact hpc)
  have hgi : Integrable (fun z => f z*planarCurl β z) := (hf.mul (planarCurl_contDiff hβ)).continuous.integrable_of_hasCompactSupport hc.mul_right
  have he : cutoffWedge f β=(fun z => planarCurl (fun y => f y • β y) z-f z*planarCurl β z) := by
    funext z
    rw [planarCurl_spatial_smul (hf.differentiable (by simp) z) (hβ.differentiable (by simp) z)]
    ring
  rw [he,integral_sub hci hgi,show (∫ z,planarCurl (fun y => f y • β y) z)=0 from compact_planar_stokes hp hpc,zero_sub]

end SymplecticBallPacking.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_CurveArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)

theorem realCurve_fderiv {n : ℕ} {u : ℂ → Phase n} {z : Plane}
    (hu : DifferentiableAt ℝ u (Complex.equivRealProdCLM.symm z)) (v : Plane) :
    fderiv ℝ (realCurve u) z v =
      fderiv ℝ u (Complex.equivRealProdCLM.symm z) (Complex.equivRealProdCLM.symm v) := by
  rw [realCurve, fderiv_comp z hu Complex.equivRealProdCLM.symm.differentiableAt]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.fderiv]

theorem planarPullback_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : Plane → E} {α : E → E →L[ℝ] ℝ}
    (hv : ContDiff ℝ ∞ v) (hα : ContDiff ℝ ∞ α) :
    ContDiff ℝ ∞ (planarPullback v α) :=
  (hα.comp hv).clm_comp (hv.fderiv_right (by simp))

theorem oneForm_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : E → E →L[ℝ] ℝ} (hα : ContDiff ℝ ∞ α) : ContDiff ℝ ∞ (oneForm α) :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ)
    (0 : Fin 1)).toContinuousLinearEquiv.contDiff.comp hα

theorem planarCurl_eq_extDeriv {α : Plane → Plane →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (z : Plane) :
    planarCurl α z = extDeriv (oneForm α) z ![(1,0),(0,1)] := by
  rw [extDeriv_apply ((oneForm_smooth hα).differentiable (by simp) z)]
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    pow_one, neg_smul, zero_add]
  change planarCurl α z =
    fderiv ℝ (fun y => α y (0,1)) z (1,0) - fderiv ℝ (fun y => α y (1,0)) z (0,1)
  rw [fderiv_clm_apply (hα.differentiable (by simp) z) (differentiableAt_const _),
    fderiv_clm_apply (hα.differentiable (by simp) z) (differentiableAt_const _)]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    fderiv_const_apply, zero_apply, map_zero, zero_add]
  rfl

theorem planarPullback_curl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : Plane → E} {α : E → E →L[ℝ] ℝ}
    (hv : ContDiff ℝ ∞ v) (hα : ContDiff ℝ ∞ α) (z : Plane) :
    planarCurl (planarPullback v α) z =
      extDeriv (oneForm α) (v z) ![fderiv ℝ v z (1,0), fderiv ℝ v z (0,1)] := by
  rw [planarCurl_eq_extDeriv (planarPullback_smooth hv hα)]
  have he : oneForm (planarPullback v α) = fun y =>
      (oneForm α (v y)).compContinuousLinearMap (fderiv ℝ v y) := by
    funext y
    ext w
    rfl
  rw [he,extDeriv_pullback ((oneForm_smooth hα).differentiable (by simp) (v z))
    hv.contDiffAt (by
      norm_num [minSmoothness] <;> first | done | exact WithTop.coe_le_coe.mpr le_top)]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  ext i
  fin_cases i <;> rfl


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

theorem weightedPrimitive_differentiableAt {n : ℕ} {g : ℝ → ℝ} {x : Phase n}
    (hg : DifferentiableAt ℝ g (capacity x)) :
    DifferentiableAt ℝ (weightedPrimitive g) x :=
  ((hg.div_const (2 : ℝ)).comp x (capacity_hasFDerivAt x).differentiableAt).fun_smul
    (stdOmega n).differentiableAt

theorem weightedPrimitive_derivative {n : ℕ} {g : ℝ → ℝ} {dg : ℝ} {x : Phase n}
    (hg : HasDerivAt g dg (capacity x)) (v w : Phase n) :
    fderiv ℝ (weightedPrimitive g) x v w =
      (g (capacity x) / 2) * standardForm v w +
      Real.pi * dg * stdDot n x v * standardForm x w := by
  have hd := ((hg.div_const 2).comp_hasFDerivAt x (capacity_hasFDerivAt x)).smul
    (stdOmega n).hasFDerivAt
  change HasFDerivAt (weightedPrimitive g) _ x at hd
  rw [hd.fderiv]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,smul_eq_mul,stdOmega_apply,Function.comp_def]
  ring

theorem weightedPrimitive_extDeriv {n : ℕ} {g : ℝ → ℝ} {dg : ℝ} {x : Phase n}
    (hg : HasDerivAt g dg (capacity x)) (v w : Phase n) :
    extDeriv (oneForm (weightedPrimitive g)) x ![v,w] = weightedTwoForm (g (capacity x)) dg x v w := by
  have hα := weightedPrimitive_differentiableAt hg.differentiableAt
  have hω : DifferentiableAt ℝ (oneForm (weightedPrimitive g)) x :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Phase n) (F := ℝ)
      (0 : Fin 1)).toContinuousLinearEquiv.differentiableAt.comp x hα
  rw [extDeriv_apply hω,Fin.sum_univ_succ]
  simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    pow_one, neg_smul, zero_add]
  change fderiv ℝ (fun y => weightedPrimitive g y w) x v -
    fderiv ℝ (fun y => weightedPrimitive g y v) x w = _
  have he (a b : Phase n) :
      fderiv ℝ (fun y => weightedPrimitive g y a) x b =
        fderiv ℝ (weightedPrimitive g) x b a := by
    rw [fderiv_clm_apply hα (differentiableAt_const a)]
    simp
  rw [he w v,he v w,weightedPrimitive_derivative hg,weightedPrimitive_derivative hg,
    standardForm_skew w v]
  unfold weightedTwoForm
  ring



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_Correction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

theorem stdPrimitive_smooth (n : ℕ) : ContDiff ℝ ∞ (@stdPrimitive n) :=
  (contDiff_const (c := (1/2 : ℝ))).smul (stdOmega n).contDiff



open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)


end

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem stdPrimitive_extDeriv {n : ℕ} (x v w : Phase n) :
    extDeriv (oneForm stdPrimitive) x ![v,w] = standardForm v w := by
  have he : (@stdPrimitive n) = weightedPrimitive (fun _ => 1) := rfl
  rw [he,weightedPrimitive_extDeriv (hasDerivAt_const (capacity x) (1 : ℝ))]
  simp [weightedTwoForm]


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

theorem outerProfile_smooth (A : ℝ) : ContDiff ℝ ∞ (outerProfile A) :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).mul
    (contDiff_const.sub (Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const A)))

theorem outerProfile_compact {A : ℝ} (hA : 0 < A) : HasCompactSupport (outerProfile A) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-2:ℝ)) (b := 2*A))
  intro t ht
  have ht' : t < -2 ∨ 2*A < t := by simpa only [mem_Icc,not_and_or,not_le] using ht
  rcases ht' with ht' | ht'
  · simp only [outerProfile,Real.smoothTransition.zero_of_nonpos (by linarith : t+2 ≤ 0),zero_mul]
  · have h : 1 ≤ (t-A)/A := (le_div_iff₀ hA).mpr (by linarith)
    simp only [outerProfile,Real.smoothTransition.one_of_one_le h,sub_self,mul_zero]

theorem outerProfile_nonneg (A t : ℝ) : 0 ≤ outerProfile A t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (sub_nonneg.mpr (Real.smoothTransition.le_one _))

theorem outerProfile_zero_value {A : ℝ} (hA : 0 < A) : outerProfile A 0 = 1 := by
  have h : (0-A)/A ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hA.le
  simp only [outerProfile,zero_add,Real.smoothTransition.one_of_one_le (by norm_num : (1:ℝ)≤2),
    Real.smoothTransition.zero_of_nonpos h,sub_zero,mul_one]

theorem outerProfile_deriv {A t : ℝ} (ht : 0 ≤ t) :
    deriv (outerProfile A) t = -(deriv Real.smoothTransition ((t-A)/A) / A) := by
  have he : outerProfile A =ᶠ[𝓝 t] fun s => 1 - Real.smoothTransition ((s-A)/A) := by
    filter_upwards [isOpen_Ioi.mem_nhds (by linarith : (-1:ℝ) < t)] with s hs
    have hs' : -1 < s := hs
    simp only [outerProfile,Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ s + 2),one_mul]
  rw [he.deriv_eq]
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hh := (hs.differentiable (by simp) ((t-A)/A)).hasDerivAt.comp t
    (((hasDerivAt_id t).sub_const A).div_const A)
  have hd := hh.const_sub 1
  change HasDerivAt (fun s => 1 - Real.smoothTransition ((s-A)/A)) _ t at hd
  rw [hd.deriv]
  simp only [div_eq_mul_inv,one_mul]

theorem outerProfile_deriv_nonpos {A t : ℝ} (hA : 0 < A) (ht : 0 ≤ t) :
    deriv (outerProfile A) t ≤ 0 := by
  rw [outerProfile_deriv ht]
  exact neg_nonpos.mpr (div_nonneg Real.smoothTransition.monotone.deriv_nonneg hA.le)

theorem outerProfile_deriv_zero_before {A t : ℝ} (hA : 0 < A) (ht : 0 ≤ t) (htA : t < A) :
    deriv (outerProfile A) t = 0 := by
  have he : outerProfile A =ᶠ[𝓝 t] fun _ => 1 := by
    filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Ioo (-1:ℝ) A from ⟨by linarith,htA⟩)] with s hs
    have hn : (s-A)/A ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith [hs.2]) hA.le
    simp only [outerProfile,Real.smoothTransition.one_of_one_le (by linarith [hs.1] : 1 ≤ s + 2),
      Real.smoothTransition.zero_of_nonpos hn,sub_zero,mul_one]
  rw [he.deriv_eq,deriv_const]

theorem cutoffWedge_radial_rotation {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (β : Plane → Plane →L[ℝ] ℝ) (z : Plane) :
    cutoffWedge (fun y => g (radiusSq y)) β z =
      2 * deriv g (radiusSq z) * β z (planeRotation z) := by
  have hh := (hg.differentiable (by simp) (radiusSq z)).hasDerivAt.comp_hasFDerivAt z
    (radiusSq_hasFDerivAt z)
  change HasFDerivAt (fun y => g (radiusSq y)) _ z at hh
  have he : planeRotation z = (-z.2) • ((1,0) : Plane) + z.1 • (0,1) := by
    ext <;> simp [planeRotation]
  unfold cutoffWedge
  rw [hh.fderiv, he,map_add,map_smul,map_smul]
  simp only [smul_apply,smul_eq_mul,planarDot_apply]
  simp only [mul_one,mul_zero,add_zero,zero_add]
  ring



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_AngularPoles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane)

theorem complex_inv_fderiv_real {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    fderiv ℝ (fun y : ℂ => y⁻¹) z w = -(z^2)⁻¹ * w := by
  rw [((hasDerivAt_inv hz).hasFDerivAt.restrictScalars ℝ).fderiv]
  change w * (-(z^2)⁻¹) = _
  ring

theorem equivRealProd_rotation (z : Plane) :
    Complex.equivRealProdCLM.symm (planeRotation z) =
      Complex.I * Complex.equivRealProdCLM.symm z := by
  apply Complex.ext <;> simp [planeRotation,Complex.equivRealProdCLM_symm_apply]



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_GlobalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity

theorem outerProfile_one {A t : ℝ} (hA : 0 < A) (ht : 0 ≤ t) (htA : t ≤ A) :
    outerProfile A t = 1 := by
  simp only [outerProfile,
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ t + 2),
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr htA) hA.le),
    sub_zero, mul_one]

theorem outerProfile_mono {A B t : ℝ} (hA : 0 < A) (hAB : A ≤ B) (ht : 0 ≤ t) :
    outerProfile A t ≤ outerProfile B t := by
  have hB : 0 < B := hA.trans_le hAB
  have hd : (t-B)/B ≤ (t-A)/A := by
    rw [div_le_div_iff₀ hB hA]
    nlinarith
  unfold outerProfile
  apply mul_le_mul_of_nonneg_left _ (Real.smoothTransition.nonneg _)
  exact sub_le_sub_left (Real.smoothTransition.monotone hd) 1



theorem affine_primitive_angular_limit_zero {n : ℕ} {u v : ℂ → Phase n}
    (hv : ContDiffAt ℝ ∞ v 0)
    (he : u =ᶠ[cocompact ℂ] fun z : ℂ => v z⁻¹)
    {α : Phase n → Phase n →L[ℝ] ℝ} (hα : Continuous α) :
    Tendsto (fun z : ℂ => α (u z) (fderiv ℝ u z (Complex.I*z)))
      (cocompact ℂ) (𝓝 0) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [←Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hdu := (hv.fderiv_right (m := 0) (by simp)).continuousAt.tendsto.comp hi
  have harg : Tendsto (fun z : ℂ => -Complex.I*z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa using hi.const_mul (-Complex.I)
  have hdv : Tendsto (fun z : ℂ => fderiv ℝ v z⁻¹ (-Complex.I*z⁻¹))
      (cocompact ℂ) (𝓝 0) := by
    simpa only [Function.comp_def, map_zero] using
      (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hdu.prodMk_nhds harg)
  have hprim : Tendsto (fun z : ℂ => α (v z⁻¹)) (cocompact ℂ) (𝓝 (α (v 0))) :=
    hα.continuousAt.tendsto.comp (hv.continuousAt.tendsto.comp hi)
  have hl : Tendsto (fun z : ℂ => α (v z⁻¹) (fderiv ℝ v z⁻¹ (-Complex.I*z⁻¹)))
      (cocompact ℂ) (𝓝 0) := by
    simpa only [Function.comp_def, map_zero] using
      (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hprim.prodMk_nhds hdv)
  have hnear : ∀ᶠ z in cocompact ℂ, u =ᶠ[𝓝 z] fun y : ℂ => v y⁻¹ := by
    obtain ⟨K,hK,hKs⟩ := mem_cocompact.mp he
    filter_upwards [hK.compl_mem_cocompact] with z hz
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hz] with y hy
    exact hKs hy
  have hd : ∀ᶠ w in 𝓝 (0:ℂ), DifferentiableAt ℝ v w :=
    ((hv.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by simp)).mono
      (fun _ hw => hw.differentiableAt (by simp))
  apply hl.congr'
  filter_upwards [hnear, hi.eventually hd,
    (isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz hvz hz0
  rw [hz.self_of_nhds, hz.fderiv_eq]
  have hiD : DifferentiableAt ℝ (fun y : ℂ => y⁻¹) z :=
    (hasDerivAt_inv hz0).differentiableAt.restrictScalars ℝ
  have hh : HasFDerivAt (fun y : ℂ => v y⁻¹)
      ((fderiv ℝ v z⁻¹).comp (fderiv ℝ (fun y : ℂ => y⁻¹) z)) z :=
    hvz.hasFDerivAt.comp z hiD.hasFDerivAt
  rw [hh.fderiv]
  change _ = α (v z⁻¹) (fderiv ℝ v z⁻¹ (fderiv ℝ (fun w : ℂ => w⁻¹) z (Complex.I*z)))
  rw [complex_inv_fderiv_real hz0]
  have heq : -(z^2)⁻¹ * (Complex.I*z) = -Complex.I*z⁻¹ := by field_simp
  rw [heq]



end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_AffineEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity

theorem outerCutoff_integrable {f : Plane → ℝ} (hf : Continuous f) {A : ℝ} (hA : 0<A) :
    Integrable (fun z => outerProfile A (radiusSq z)*f z) := by
  apply (((outerProfile_smooth A).comp radiusSq_smooth).continuous.mul hf).integrable_of_hasCompactSupport
  exact (HasCompactSupport.comp_radiusSq (outerProfile_compact hA)).mul_right

theorem integrable_of_nonneg_of_outerCutoff_limit {f : Plane → ℝ}
    (hf : Continuous f) (hp : ∀ z, 0 ≤ f z) {E : ℝ}
    (hlim : Tendsto (fun j : ℕ => ∫ z, outerProfile ((j:ℝ)+1) (radiusSq z)*f z)
      atTop (𝓝 E)) : Integrable f ∧ (∫ z, f z) = E := by
  let g (j : ℕ) (z : Plane) := outerProfile ((j:ℝ)+1) (radiusSq z)*f z
  have hA (j : ℕ) : 0 < (j:ℝ)+1 := by positivity
  have hgpos (j : ℕ) (z : Plane) : 0 ≤ g j z := mul_nonneg (outerProfile_nonneg _ _) (hp z)
  have hn : Tendsto (fun j : ℕ => (j:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hEn : 0 ≤ E := ge_of_tendsto hlim (Filter.Eventually.of_forall fun j => integral_nonneg (hgpos j))
  have hmeas (j : ℕ) : AEMeasurable (fun z => ENNReal.ofReal (g j z)) :=
    (ENNReal.continuous_ofReal.comp
      (((outerProfile_smooth _).comp radiusSq_smooth).continuous.mul hf)).aemeasurable
  have hmono : ∀ᵐ z : Plane, Monotone (fun j : ℕ => ENNReal.ofReal (g j z)) := by
    apply Filter.Eventually.of_forall
    intro z i j hij
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (outerProfile_mono (hA i) (by exact_mod_cast Nat.add_le_add_right hij 1)
        (radiusSq_nonneg z)) (hp z)
  have hpoint : ∀ᵐ z : Plane, Tendsto
      (fun j : ℕ => ENNReal.ofReal (g j z)) atTop (𝓝 (ENNReal.ofReal (f z))) := by
    apply Filter.Eventually.of_forall
    intro z
    apply Filter.EventuallyEq.tendsto
    filter_upwards [hn.eventually (eventually_ge_atTop (radiusSq z))] with j hj
    simp only [g,outerProfile_one (hA j) (radiusSq_nonneg z) hj,one_mul]
  have hm := lintegral_tendsto_of_tendsto_of_monotone hmeas hmono hpoint
  have heq (j : ℕ) : (∫⁻ z, ENNReal.ofReal (g j z)) = ENNReal.ofReal (∫ z, g j z) :=
    (ofReal_integral_eq_lintegral_ofReal (outerCutoff_integrable hf (hA j))
      (Filter.Eventually.of_forall (hgpos j))).symm
  simp_rw [heq] at hm
  have hmval := tendsto_nhds_unique hm (ENNReal.tendsto_ofReal hlim)
  have hi : Integrable f := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs,abs_of_nonneg (hp _)]
    rw [hmval]
    exact ENNReal.ofReal_lt_top
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hp)
    hi.aestronglyMeasurable,hmval,ENNReal.toReal_ofReal hEn]

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_C1Energy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
namespace TwoPointContinuation

variable {G E : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 omit [NormedSpace ℝ G] [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] in
 theorem approxBump_shrinks : Tendsto (fun j : ℕ => (approxBump (G:=G) j).rOut) atTop (𝓝 0) := by
  simp only [approxBump,one_div]
  exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

 theorem mollify_tendsto (μ : Measure G) [μ.IsAddHaarMeasure] {f : G → E}
    (hf : Continuous f) (x : G) : Tendsto (fun j => mollify μ j f x) atTop (𝓝 (f x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous approxBump_shrinks hf x

 omit [CompleteSpace E] in
 theorem mollify_smooth (μ : Measure G) [μ.IsAddHaarMeasure] {f : G → E}
    (hf : Continuous f) (j : ℕ) : ContDiff ℝ ∞ (mollify μ j f) := by
  exact (approxBump (G:=G) j).hasCompactSupport_normed.contDiff_convolution_left
    (lsmul ℝ ℝ) (approxBump j).contDiff_normed hf.locallyIntegrable

 omit [CompleteSpace E] in
 theorem mollify_fderiv (μ : Measure G) [μ.IsAddHaarMeasure] {f : G → E}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (j : ℕ) (x : G) :
    fderiv ℝ (mollify μ j f) x=mollify μ j (fderiv ℝ f) x := by
  have h := hc.hasFDerivAt_convolution_right (lsmul ℝ ℝ)
    (μ:=μ) ((approxBump (G:=G) j).continuous_normed (μ:=μ)).locallyIntegrable hf x
  unfold mollify
  rw [h.fderiv]
  rfl

 theorem mollify_fderiv_tendsto (μ : Measure G) [μ.IsAddHaarMeasure] {f : G → E}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (x : G) :
    Tendsto (fun j => fderiv ℝ (mollify μ j f) x) atTop (𝓝 (fderiv ℝ f x)) := by
  simp_rw [mollify_fderiv μ hf hc]
  exact mollify_tendsto μ (hf.continuous_fderiv one_ne_zero) x

 theorem mollify_norm_le (μ : Measure G) [μ.IsAddHaarMeasure] {f : G → E}
    (hf : Continuous f) {M : ℝ} (hM : ∀ x, ‖f x‖≤M) (j : ℕ) (x : G) :
    ‖mollify μ j f x‖≤3*M := by
  have h := (approxBump (G:=G) j).dist_normed_convolution_le
    (μ:=μ) hf.aestronglyMeasurable (x₀:=x) (ε:=2*M) (fun y _ => by
      exact (dist_le_norm_add_norm _ _).trans (by linarith [hM y,hM x]))
  change dist (mollify μ j f x) (f x)≤2*M at h
  calc
    ‖mollify μ j f x‖ ≤ ‖mollify μ j f x-f x‖+‖f x‖ := by
      simpa using norm_add_le (mollify μ j f x-f x) (f x)
    _ ≤ 3*M := by rw [dist_eq_norm] at h; linarith [hM x]

end TwoPointContinuation

 

 

open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
namespace TwoPointContinuation
variable {G E : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

 theorem mollify_jet_integral_tendsto (μ : Measure G) [μ.IsAddHaarMeasure]
    {f : G → E} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (A : G × (E × (G →L[ℝ] E)) → ℝ) (hA : Continuous A)
    (K : Set G) (hK : IsCompact K) (hzero : ∀ z, z ∉ K → ∀ v, A (z,v)=0) :
    Tendsto (fun j => ∫ z, A (z,(mollify μ j f z,fderiv ℝ (mollify μ j f) z)) ∂μ)
      atTop (𝓝 (∫ z, A (z,(f z,fderiv ℝ f z)) ∂μ)) := by
  classical
  obtain ⟨M,hM⟩ := (hc.isCompact_range hf.continuous).isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := ((hc.fderiv ℝ).isCompact_range
    (hf.continuous_fderiv one_ne_zero)).isBounded.exists_norm_le
  have hmb (z : G) : ‖f z‖ ≤ M := hM _ (mem_range_self z)
  have hnb (z : G) : ‖fderiv ℝ f z‖ ≤ N := hN _ (mem_range_self z)
  let L := K ×ˢ (Metric.closedBall (0:E) (3*M) ×ˢ Metric.closedBall (0:G →L[ℝ] E) (3*N))
  have hL : IsCompact L := hK.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  obtain ⟨B,hB⟩ := (hL.image hA).isBounded.exists_norm_le
  have hb (j : ℕ) (z : G) (hz : z ∈ K) :
      ‖A (z,(mollify μ j f z,fderiv ℝ (mollify μ j f) z))‖≤B := by
    apply hB _ (mem_image_of_mem A ?_)
    refine ⟨hz,?_,?_⟩
    · simpa only [Metric.mem_closedBall,dist_zero_right] using mollify_norm_le μ hf.continuous hmb j z
    · rw [mollify_fderiv μ hf hc]
      simpa only [Metric.mem_closedBall,dist_zero_right] using
        mollify_norm_le μ (hf.continuous_fderiv one_ne_zero) hnb j z
  apply tendsto_integral_of_dominated_convergence (K.indicator (fun _ => B))
  · intro j
    exact (hA.comp (continuous_id.prodMk ((mollify_smooth μ hf.continuous j).continuous.prodMk
      ((mollify_smooth μ hf.continuous j).continuous_fderiv (by simp))))).aestronglyMeasurable
  · rw [integrable_indicator_iff hK.measurableSet]
    exact (integrableOn_const (C:=B) hK.measure_lt_top.ne)
  · intro j
    apply Eventually.of_forall
    intro z
    by_cases hz : z ∈ K
    · simpa only [indicator_of_mem hz] using hb j z hz
    · simp only [hzero z hz,indicator_of_notMem hz,norm_zero,le_refl]
  · apply Eventually.of_forall
    intro z
    exact (hA.tendsto _).comp (tendsto_const_nhds.prodMk_nhds
      ((mollify_tendsto μ hf.continuous z).prodMk_nhds (mollify_fderiv_tendsto μ hf hc z)))

end TwoPointContinuation

 

 

 

open scoped ContDiff Topology
open Set Filter Function MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity
open TwoPointContinuation

 theorem c1Area_continuous {n : ℕ} {u : Plane → Phase n} (hu : ContDiff ℝ 1 u) :
    Continuous (c1Area u) := by
  unfold c1Area
  simp only [← stdOmega_apply]
  exact ((stdOmega n).continuous.comp ((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const)).clm_apply
    ((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const)

 theorem c1_standard_stokes_compact {n : ℕ} {u : Plane → Phase n}
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u)
    {χ : Plane → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    (∫ z,cutoffWedge χ (planarPullback u stdPrimitive) z)= -(∫ z,χ z*c1Area u z) := by
  let A : Plane × (Phase n × (Plane →L[ℝ] Phase n)) → ℝ :=
    fun y => χ y.1*standardForm (y.2.2 (1,0)) (y.2.2 (0,1))
  let B : Plane × (Phase n × (Plane →L[ℝ] Phase n)) → ℝ :=
    fun y => fderiv ℝ χ y.1 (1,0)*stdPrimitive y.2.1 (y.2.2 (0,1))-
      fderiv ℝ χ y.1 (0,1)*stdPrimitive y.2.1 (y.2.2 (1,0))
  have hA : Continuous A := by
    simp only [A,← stdOmega_apply]
    fun_prop
  have hP : Continuous (fun y : Plane × (Phase n × (Plane →L[ℝ] Phase n)) =>
      stdPrimitive y.2.1) := (stdPrimitive_smooth n).continuous.comp continuous_snd.fst
  have hB : Continuous B := by
    have hd := hχ.continuous_fderiv (show (∞ : WithTop ℕ∞)≠0 by simp)
    exact (((hd.comp continuous_fst).clm_apply continuous_const).mul
      (hP.clm_apply (continuous_snd.snd.clm_apply continuous_const))).sub
      (((hd.comp continuous_fst).clm_apply continuous_const).mul
      (hP.clm_apply (continuous_snd.snd.clm_apply continuous_const)))
  let K := tsupport χ ∪ tsupport (fderiv ℝ χ)
  have hK : IsCompact K := hχc.union (hχc.fderiv ℝ)
  have hAz : ∀ z, z ∉ K → ∀ v, A (z,v)=0 := by
    intro z hz v
    have hz' : z ∉ tsupport χ := fun h => hz (Or.inl h)
    simp only [A,image_eq_zero_of_notMem_tsupport hz',zero_mul]
  have hBz : ∀ z, z ∉ K → ∀ v, B (z,v)=0 := by
    intro z hz v
    have hz' : z ∉ tsupport (fderiv ℝ χ) := fun h => hz (Or.inr h)
    simp only [B,image_eq_zero_of_notMem_tsupport hz',zero_apply,zero_mul,sub_self]
  have ha := mollify_jet_integral_tendsto volume hu hc A hA K hK hAz
  have hb := mollify_jet_integral_tendsto volume hu hc B hB K hK hBz
  have he (j : ℕ) :
      (∫ z,A (z,(mollify volume j u z,fderiv ℝ (mollify volume j u) z)))=
      -(∫ z,B (z,(mollify volume j u z,fderiv ℝ (mollify volume j u) z))) := by
    have h := integral_cutoffWedge hχ hχc
      (planarPullback_smooth (mollify_smooth volume hu.continuous j) (stdPrimitive_smooth n))
    have he (z : Plane) : planarCurl (planarPullback (mollify volume j u) stdPrimitive) z=
        standardForm (fderiv ℝ (mollify volume j u) z (1,0)) (fderiv ℝ (mollify volume j u) z (0,1)) := by
      rw [planarPullback_curl (mollify_smooth volume hu.continuous j) (stdPrimitive_smooth n)]
      exact stdPrimitive_extDeriv _ _ _
    simp_rw [he] at h
    change (∫ z,B (z,(mollify volume j u z,fderiv ℝ (mollify volume j u) z)))=
      -(∫ z,A (z,(mollify volume j u z,fderiv ℝ (mollify volume j u) z))) at h
    linarith
  have ht := tendsto_nhds_unique ha (hb.neg.congr (fun j => (he j).symm))
  change (∫ z,χ z*c1Area u z)= -(∫ z,cutoffWedge χ (planarPullback u stdPrimitive) z) at ht
  linarith

 theorem c1_local_compact {n : ℕ} {u : Plane → Phase n}
    (hu : ContDiff ℝ 1 u) {K : Set Plane} (hK : IsCompact K) :
    ∃ v : Plane → Phase n, ContDiff ℝ 1 v ∧ HasCompactSupport v ∧
      ∀ z ∈ K, v =ᶠ[𝓝 z] u := by
  obtain ⟨R,hR,hRb⟩ := hK.isBounded.exists_pos_norm_le
  let b : ContDiffBump (0:Plane) := ⟨R+1,R+2,by linarith,by linarith⟩
  refine ⟨fun z => b z • u z,b.contDiff.smul hu,b.hasCompactSupport.smul_right,?_⟩
  intro z hz
  have hm : z ∈ Metric.ball (0:Plane) b.rIn := by
    simp only [Metric.mem_ball,dist_zero_right]
    change ‖z‖<R+1
    linarith [hRb z hz]
  filter_upwards [b.eventuallyEq_one_of_mem_ball hm] with y hy
  simp only [hy,Pi.one_apply,one_smul]

 theorem c1_standard_stokes {n : ℕ} {u : Plane → Phase n}
    (hu : ContDiff ℝ 1 u) {χ : Plane → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    (∫ z,cutoffWedge χ (planarPullback u stdPrimitive) z)= -(∫ z,χ z*c1Area u z) := by
  let K := tsupport χ ∪ tsupport (fderiv ℝ χ)
  have hK : IsCompact K := hχc.union (hχc.fderiv ℝ)
  obtain ⟨v,hv,hvc,hvu⟩ := c1_local_compact hu hK
  have heA : (fun z => χ z*c1Area v z)=fun z => χ z*c1Area u z := by
    funext z
    by_cases hz : z ∈ K
    · simp only [c1Area,(hvu z hz).fderiv_eq]
    · have hz' : z ∉ tsupport χ := fun h => hz (Or.inl h)
      simp only [image_eq_zero_of_notMem_tsupport hz',zero_mul]
  have heB : cutoffWedge χ (planarPullback v stdPrimitive)=cutoffWedge χ (planarPullback u stdPrimitive) := by
    funext z
    by_cases hz : z ∈ K
    · simp only [cutoffWedge,planarPullback,(hvu z hz).self_of_nhds,(hvu z hz).fderiv_eq]
    · have hz' : z ∉ tsupport (fderiv ℝ χ) := fun h => hz (Or.inr h)
      simp only [cutoffWedge,image_eq_zero_of_notMem_tsupport hz',zero_apply,
        zero_mul,sub_self]
  have h := c1_standard_stokes_compact hv hvc hχ hχc
  rwa [heA,heB] at h

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology
open Set Filter Function MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity

theorem continuous_boundary_bounds {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : Continuous β) {A k ε : ℝ} (hA : 0 < A)
    (he : ∀ z : Plane, A ≤ radiusSq z → |β z (planeRotation z) - k| ≤ ε) :
    2 * Real.pi * (k-ε) ≤ (- ∫ z : Plane, 2 * deriv (outerProfile A) (radiusSq z) * β z (planeRotation z)) ∧
      (- ∫ z : Plane, 2 * deriv (outerProfile A) (radiusSq z) * β z (planeRotation z)) ≤ 2 * Real.pi * (k+ε) := by
  let g := outerProfile A
  have hg : ContDiff ℝ ∞ g := outerProfile_smooth A
  have hgc : HasCompactSupport g := outerProfile_compact hA
  have hdi : Integrable (fun z : Plane => 2 * deriv g (radiusSq z)) :=
    (((hg.continuous_deriv (by simp)).comp radiusSq_smooth.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.comp_radiusSq hgc.deriv)).const_mul 2
  have hwi : Integrable (fun z : Plane => 2 * deriv g (radiusSq z) * β z (planeRotation z)) := by
    exact ((((hg.continuous_deriv (by simp)).comp radiusSq_smooth.continuous).const_mul 2).mul
      (hβ.clm_apply (continuous_snd.neg.prodMk continuous_fst))).integrable_of_hasCompactSupport
      (HasCompactSupport.comp_radiusSq hgc.deriv).mul_left.mul_right
  have hp (z : Plane) :
      2 * deriv g (radiusSq z) * (k+ε) ≤ 2 * deriv g (radiusSq z) * β z (planeRotation z) ∧
      2 * deriv g (radiusSq z) * β z (planeRotation z) ≤ 2 * deriv g (radiusSq z) * (k-ε) := by
    by_cases hd : deriv g (radiusSq z) = 0
    · simp only [hd, mul_zero, zero_mul, le_refl, and_self]
    have hz : A ≤ radiusSq z := by
      by_contra! hn
      exact hd (outerProfile_deriv_zero_before hA (radiusSq_nonneg z) hn)
    have hb := abs_le.mp (he z hz)
    have hdn : 2 * deriv g (radiusSq z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by norm_num)
        (outerProfile_deriv_nonpos hA (radiusSq_nonneg z))
    exact ⟨mul_le_mul_of_nonpos_left (by linarith [hb.2]) hdn,
      mul_le_mul_of_nonpos_left (by linarith [hb.1]) hdn⟩
  have hlo := integral_mono (hdi.mul_const (k+ε)) hwi (fun z => (hp z).1)
  have hhi := integral_mono hwi (hdi.mul_const (k-ε)) (fun z => (hp z).2)
  have hg0 : g 0 = 1 := outerProfile_zero_value hA
  rw [integral_mul_const, integral_radial_derivative hg hgc, hg0] at hlo hhi
  change _ ≤ - ∫ z : Plane, 2 * deriv g (radiusSq z) * β z (planeRotation z) ∧ _
  constructor <;> nlinarith

theorem continuous_boundary_limit {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : Continuous β) {k : ℝ}
    (hlim : Tendsto (fun z => β z (planeRotation z)) (cocompact Plane) (𝓝 k)) :
    Tendsto (fun A : ℝ => - ∫ z : Plane, 2 * deriv (outerProfile A) (radiusSq z) * β z (planeRotation z)) atTop (𝓝 (2 * Real.pi * k)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (4 * Real.pi)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : 2 * Real.pi * δ = ε / 2 := by
    dsimp [δ]
    field_simp
    ring
  have he : ∀ᶠ z in cocompact Plane, |β z (planeRotation z) - k| ≤ δ := by
    filter_upwards [(Metric.tendsto_nhds.mp hlim) δ hδ] with z hz
    exact (Real.dist_eq _ _ ▸ hz).le
  obtain ⟨K,hK,hKs⟩ := mem_cocompact.mp he
  obtain ⟨B,hB,hbound⟩ := (hK.image radiusSq_smooth.continuous).isBounded.exists_pos_norm_le
  filter_upwards [eventually_ge_atTop (B+1)] with A hA
  have hApos : 0 < A := by linarith
  have hb := continuous_boundary_bounds hβ hApos (k := k) (ε := δ) (by
    intro z hz
    apply hKs
    intro hzK
    have hx := hbound (radiusSq z) ⟨z,hzK,rfl⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (radiusSq_nonneg z)] at hx
    linarith)
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> nlinarith [hb.1, hb.2]

 theorem c1_pullback_continuous {n : ℕ} {u : Plane → Phase n} (hu : ContDiff ℝ 1 u) :
    Continuous (planarPullback u stdPrimitive) :=
  ((stdPrimitive_smooth n).continuous.comp hu.continuous).clm_comp
    (hu.continuous_fderiv one_ne_zero)

 theorem c1_area_of_nonneg_of_angular_limit {n : ℕ} {u : Plane → Phase n}
    (hu : ContDiff ℝ 1 u) (hp : ∀ z, 0 ≤ c1Area u z)
    (hl : Tendsto (fun z => planarPullback u stdPrimitive z (planeRotation z))
      (cocompact Plane) (𝓝 0)) :
    Integrable (c1Area u) ∧ (∫ z,c1Area u z)=0 := by
  apply integrable_of_nonneg_of_outerCutoff_limit (c1Area_continuous hu) hp
  have hlim := (continuous_boundary_limit (c1_pullback_continuous hu) hl).comp
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  simp only [mul_zero] at hlim
  apply hlim.congr
  intro j
  have hA : 0<(j:ℝ)+1 := by positivity
  have h := c1_standard_stokes hu
    ((outerProfile_smooth ((j:ℝ)+1)).comp radiusSq_smooth)
    (HasCompactSupport.comp_radiusSq (outerProfile_compact hA))
  dsimp only [Function.comp_def] at h
  simp_rw [cutoffWedge_radial_rotation (outerProfile_smooth ((j:ℝ)+1))] at h
  dsimp only [Function.comp_def]
  linarith

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FrozenOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology
open Set Filter Function MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem decaying_holomorphic_extends {n : ℕ} {u : ℂ → Phase n}
    (hholo : ∀ᶠ z in cocompact ℂ, DifferentiableAt ℂ u z)
    (hlim : Tendsto u (cocompact ℂ) (𝓝 0)) :
    ∃ v : ℂ → Phase n, ContDiffAt ℝ ∞ v 0 ∧
      u =ᶠ[cocompact ℂ] fun z => v z⁻¹ := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 (0:ℂ)) := by
    rw [←Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  have hl : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 (0:Phase n)) := by
    simpa only [zero_smul] using hi.smul hlim
  let V := infinityGerm u 0
  have hV : AnalyticAt ℂ V 0 := infinityGerm_analyticAt hholo hl
  have hV0 : V 0 = 0 := by simp [V,infinityGerm]
  obtain ⟨r,hr,hVr⟩ := hV.exists_ball_analyticOnNhd
  have hball : Metric.ball (0:ℂ) r ∈ 𝓝 (0:ℂ) := Metric.ball_mem_nhds _ hr
  have hv := ((Complex.differentiableOn_dslope hball).mpr hVr.differentiableOn).analyticAt hball
  refine ⟨dslope V 0,hv.contDiffAt.restrict_scalars ℝ,?_⟩
  filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
  have hz0 : z ≠ 0 := by simpa using hz
  rw [dslope_of_ne V (inv_ne_zero hz0)]
  simp only [slope_def_module,sub_zero,V,infinityGerm,inv_ne_zero hz0,
    ite_false,ite_true,sub_zero,inv_inv,smul_smul,mul_inv_cancel₀ hz0,one_smul]

 theorem c1_decaying_CR_zero_oai {n : ℕ} (K : ℂ → End n)
    (hK : ∀ z, Compatible (K z)) {u : ℂ → Phase n}
    (hu : ContDiff ℝ 1 u)
    (hCR : ∀ z, fderiv ℝ u z Complex.I=K z (fderiv ℝ u z 1))
    (hholo : ∀ᶠ z in cocompact ℂ, DifferentiableAt ℂ u z)
    (hlim : Tendsto u (cocompact ℂ) (𝓝 0)) : u=0 := by
  obtain ⟨v,hv,he⟩ := decaying_holomorphic_extends hholo hlim
  have hru : ContDiff ℝ 1 (realCurve u) := hu.comp Complex.equivRealProdCLM.symm.contDiff
  have hcr (z : Plane) : fderiv ℝ (realCurve u) z (0,1)=
      K (Complex.equivRealProdCLM.symm z) (fderiv ℝ (realCurve u) z (1,0)) := by
    rw [realCurve_fderiv (hu.differentiable one_ne_zero _),realCurve_fderiv (hu.differentiable one_ne_zero _)]
    simpa only [Complex.equivRealProdCLM_symm_apply,Complex.ofReal_zero,Complex.ofReal_one,
      zero_mul,one_mul,add_zero,zero_add] using hCR (Complex.equivRealProdCLM.symm z)
  have hpos (z : Plane) : 0 ≤ c1Area (realCurve u) z := by
    unfold c1Area
    rw [hcr]
    by_cases hz : fderiv ℝ (realCurve u) z (1,0)=0
    · simp [hz,standardForm]
    · exact ((hK _).2.2 _ hz).le
  have hang : Tendsto (fun z : Plane => planarPullback (realCurve u) stdPrimitive z (planeRotation z))
      (cocompact Plane) (𝓝 0) := by
    have hr : Tendsto Complex.equivRealProdCLM.symm (cocompact Plane) (cocompact ℂ) :=
      Complex.equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding.tendsto_cocompact
    have hh := (affine_primitive_angular_limit_zero hv he (stdPrimitive_smooth n).continuous).comp hr
    apply hh.congr
    intro z
    change stdPrimitive _ _=stdPrimitive _ _
    have hd := realCurve_fderiv (z:=z) (hu.differentiable one_ne_zero _) (planeRotation z)
    rw [equivRealProd_rotation] at hd
    exact congrArg (stdPrimitive (u (Complex.equivRealProdCLM.symm z))) hd.symm
  obtain ⟨hai,ha0⟩ := c1_area_of_nonneg_of_angular_limit hru hpos hang
  have ha : c1Area (realCurve u)=0 :=
    ((c1Area_continuous hru).ae_eq_iff_eq volume continuous_const).mp
      ((integral_eq_zero_iff_of_nonneg hpos hai).mp ha0)
  have hx (z : Plane) : fderiv ℝ (realCurve u) z (1,0)=0 := by
    by_contra hn
    have hp := (hK (Complex.equivRealProdCLM.symm z)).2.2 _ hn
    have hz := congrFun ha z
    change standardForm _ _=0 at hz
    rw [hcr] at hz
    linarith
  have hd (z : Plane) : fderiv ℝ (realCurve u) z=0 := by
    apply ContinuousLinearMap.ext
    intro w
    have hw : w=w.1 • ((1,0):Plane)+w.2 • ((0,1):Plane) := by ext <;> simp
    rw [hw,map_add,map_smul,map_smul,hx,hcr,hx,map_zero]
    simp
  have hc (z : ℂ) : u z=u 0 := by
    have hh := is_const_of_fderiv_eq_zero (hru.differentiable one_ne_zero)
      hd (Complex.equivRealProdCLM z) 0
    simpa only [realCurve,Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply,map_zero] using hh
  have hec : u=fun _ => u 0 := funext hc
  have hz : u 0=0 := tendsto_nhds_unique tendsto_const_nhds (hec ▸ hlim)
  funext z
  exact (hc z).trans hz

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.c1_decaying_CR_zero_oai := @OAI.HigherDimensionalBallPacking.Rigidity.c1_decaying_CR_zero_oai
