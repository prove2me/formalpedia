-- Prove2me | solution 1 for OAI.Release061.Biholomorph.hermitian_model_bounded_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:53:41.97969+00:00
-- url     : https://prove2.me/submissions/6af7428a-8217-48ad-93c2-b3542af5bee4

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S003
import Theorems.Thm_OAI_Release061_Biholomorph_WeightedLieModel_exists_positive_real
import Theorems.Thm_OAI_Release061_Biholomorph_exists_actual_aut_chart_unimodular_jacobian

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CompactFaithfulIsotropy
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter Topology TopologicalSpace
open scoped Classical
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

theorem firstJet_injective (hU : IsOpen U) (hc : IsPreconnected U)
    (hb : Bornology.IsBounded U) (p : U) : Function.Injective (firstJet p) := by
  intro a b hab
  have hp : a.toHomeomorph p=b.toHomeomorph p := congrArg Prod.fst hab
  have hd : a.derivativeAt p=b.derivativeAt p := congrArg Prod.snd hab
  have he : b⁻¹*a=1 := by
    apply eq_one_of_firstJet hU hc hb (b⁻¹*a) p
    · simp only [mul_apply,inv_apply,hp,Homeomorph.symm_apply_apply]
    · rw [derivativeAt_mul hU,hp,hd]
      rw [← derivativeAt_mul hU,inv_mul_cancel,derivativeAt_one hU]
  exact (inv_mul_eq_one.mp he).symm

theorem compact_stabilizer (hU : IsOpen U) (hc : IsPreconnected U)
    (hb : Bornology.IsBounded U) [LocallyCompactSpace U]
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U) :
    IsCompact {a : Biholomorph U U | a.toHomeomorph p=p} := by
  exact (bounded_divisible_automorphism_evaluation_proper hU hc hb Γ hhol p).isCompact_preimage
    isCompact_singleton

theorem compact_faithful_isotropy (hU : IsOpen U) (hc : IsPreconnected U)
    (hb : Bornology.IsBounded U) [LocallyCompactSpace U]
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U) :
    IsCompact ((fun a : Biholomorph U U => a.derivativeAt p) '' {a | a.toHomeomorph p=p}) ∧
    InjOn (fun a : Biholomorph U U => a.derivativeAt p) {a | a.toHomeomorph p=p} := by
  refine ⟨(compact_stabilizer hU hc hb Γ hhol p).image (derivativeAt_continuous hU p),?_⟩
  intro a ha b hbfix hd
  apply firstJet_injective hU hc hb p
  exact Prod.ext (ha.trans hbfix.symm) hd

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GeneratorAdjointContinuous
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061

namespace Biholomorph

section
open Set Filter Topology Metric
open scoped Classical
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)

include hU hc hbd Γ hhol ha ha0 ham

theorem generatorAdjoint_slope_tendsto (Y : completeGeneratorSpace hU hc hbd Γ hhol) :
    Tendsto (fun t : ℝ => t⁻¹ • (generatorAdjoint hU hc hbd Γ hhol (a t) Y-
        generatorAdjoint hU hc hbd Γ hhol (a 0) Y)) (𝓝[≠] 0)
      (𝓝 (-⁅oneParameterGenerator hU hc hbd Γ hhol a ha ha0 ham,Y⁆)) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro x
  have hd : HasDerivAt (fun t : ℝ => pushForwardGenerator (a t) Y.val x)
      (-VectorField.lieBracket ℂ (infinitesimalGenerator a) Y.val x) 0 := by
    by_cases hx : x∈U
    · exact pushForwardGenerator_hasDerivAt_zero hU hbd a ha ha0 ham Y.val
        (Y.property.analyticOnNhd hU hbd) x hx
    · have hbr := VectorField.lieBracket_eq_zero_of_eq_zero (𝕜 := ℂ)
        (infinitesimalGenerator_of_not_mem a hx) (Y.property.eq_zero_of_not_mem hx)
      simpa only [pushForwardGenerator,dite_eq_right hx,hbr,neg_zero] using
        hasDerivAt_const (0:ℝ) (0 : Affine n)
  apply hd.tendsto_slope.congr'
  filter_upwards [] with t
  change (t-(0:ℝ))⁻¹ • (pushForwardGenerator (a t) Y.val x-pushForwardGenerator (a 0) Y.val x)=
    t⁻¹ • (pushForwardGenerator (a t) Y.val x-pushForwardGenerator (a 0) Y.val x)
  rw [sub_zero]

theorem generatorAdjoint_coordinates_hasDerivAt_zero {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (completeGeneratorSpace hU hc hbd Γ hhol))
    (Y : completeGeneratorSpace hU hc hbd Γ hhol) :
    HasDerivAt (fun t : ℝ => b.equivFun (generatorAdjoint hU hc hbd Γ hhol (a t) Y))
      (b.equivFun (-⁅oneParameterGenerator hU hc hbd Γ hhol a ha ha0 ham,Y⁆)) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have ht := (continuous_equivFun_basis b).continuousAt.tendsto.comp
    (generatorAdjoint_slope_tendsto hU hc hbd Γ hhol a ha ha0 ham Y)
  apply ht.congr'
  filter_upwards [] with t
  simp only [Function.comp_apply,slope_def_module,sub_zero,map_smul,map_sub]

end

open Set Filter Topology Metric
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GeneratorDeterminantDerivZero
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061

section
open Set Filter Topology Matrix

theorem hasDerivAt_matrix_det_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ℝ → Matrix ι ι ℝ} {A : Matrix ι ι ℝ} {s : ℝ}
    (hf : HasDerivAt f A s) (hfs : f s=1) :
    HasDerivAt (fun t => (f t).det) A.trace s := by
  let D : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
    { toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
      cont := continuous_id.matrix_det }
  have hd := (D.hasFDerivAt (f s)).comp_hasDerivAt s hf
  have hlin : D.linearDeriv (f s) A=A.trace := by
    have he := D.linearDeriv_apply (f s) A
    rw [he,hfs]
    apply Finset.sum_congr rfl
    intro i hi
    change (Matrix.updateRow (1 : Matrix ι ι ℝ) i (A i)).det=A i i
    have heq : (∑ k : ι, (A i k) • (1 : Matrix ι ι ℝ) k)=A i := by
      funext j
      simp [Matrix.one_apply]
    rw [← heq,Matrix.det_updateRow_sum,Matrix.det_one,smul_eq_mul,mul_one,heq]
  rw [hlin] at hd
  exact hd
end

open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (completeGeneratorSpace hU hc hbd Γ hhol))

 theorem generatorDeterminant_ne_zero (q : Biholomorph U U) :
    generatorDeterminant hU hc hbd Γ hhol b q≠0 := by
  intro he
  have h := (generatorDeterminant hU hc hbd Γ hhol b).map_mul q q⁻¹
  rw [mul_inv_cancel,map_one,he,zero_mul] at h
  exact one_ne_zero h

variable (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)

 theorem generatorAdjointMatrix_hasDerivAt_zero :
    HasDerivAt (fun t : ℝ => generatorAdjointMatrix hU hc hbd Γ hhol b (a t))
      (-LinearMap.toMatrix b b (LieAlgebra.ad ℝ (completeGeneratorSpace hU hc hbd Γ hhol)
        (oneParameterGenerator hU hc hbd Γ hhol a ha ha0 ham))) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have h := hasDerivAt_pi.mp
    (generatorAdjoint_coordinates_hasDerivAt_zero hU hc hbd Γ hhol a ha ha0 ham b (b j)) i
  simpa only [generatorAdjointMatrix,Matrix.neg_apply,LinearMap.toMatrix_apply,
    map_neg,Pi.neg_apply,Module.Basis.equivFun_apply,LieAlgebra.ad_apply,LinearEquiv.coe_coe] using h

theorem generatorDeterminant_hasDerivAt_zero :
    HasDerivAt (fun t : ℝ => generatorDeterminant hU hc hbd Γ hhol b (a t))
      (-LinearMap.trace ℝ (completeGeneratorSpace hU hc hbd Γ hhol)
        (LieAlgebra.ad ℝ (completeGeneratorSpace hU hc hbd Γ hhol)
          (oneParameterGenerator hU hc hbd Γ hhol a ha ha0 ham))) 0 := by
  have h := hasDerivAt_matrix_det_one
    (generatorAdjointMatrix_hasDerivAt_zero hU hc hbd Γ hhol b a ha ha0 ham)
    (by rw [ha0,generatorAdjointMatrix_one])
  simpa only [generatorDeterminant,MonoidHom.coe_mk,OneHom.coe_mk,Matrix.trace_neg,
    LinearMap.trace_eq_matrix_trace ℝ b] using h

include ham in
 theorem generatorDeterminant_flow_pos (t : ℝ) :
    0<generatorDeterminant hU hc hbd Γ hhol b (a t) := by
  have h : t=t/2+t/2 := by ring
  rw [h,ham,map_mul]
  exact mul_self_pos.mpr (generatorDeterminant_ne_zero hU hc hbd Γ hhol b (a (t/2)))
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_OneParameterDerivativeJoint
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
include hU

variable (hbd : Bornology.IsBounded U) (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
include hbd ha ha0 ham

theorem oneParameter_derivativeAt_hasDerivAt (s : ℝ) (p : U) :
    HasDerivAt (fun t => (a t).derivativeAt p)
      ((fderiv ℂ (infinitesimalGenerator a) ((a s).toHomeomorph p).val).comp ((a s).derivativeAt p)) s := by
  let y : U := (a s).toHomeomorph p
  have hd0 := oneParameter_fderiv_hasDerivAt_zero hU hbd a ha ha0 ham y.val y.property
  have hd0' : HasDerivAt (fun t => (a t).derivativeAt y)
      (fderiv ℂ (infinitesimalGenerator a) y.val) (s-s) := by simpa only [sub_self,derivativeAt] using hd0
  have his : HasDerivAt (fun t : ℝ => t-s) 1 s := by simpa only [id_eq] using (hasDerivAt_id s).sub_const s
  have hdt := hd0'.scomp s (h := fun t : ℝ => t-s) his
  simp only [one_smul] at hdt
  let L := ((ContinuousLinearMap.compL ℂ (Affine n) (Affine n) (Affine n)).flip
    ((a s).derivativeAt p)).restrictScalars ℝ
  have hd := L.hasFDerivAt.comp_hasDerivAt s hdt
  have he (t : ℝ) : (a t).derivativeAt p=((a (t-s)).derivativeAt y).comp ((a s).derivativeAt p) := by
    have hat : a t=a (t-s)*a s := by rw [← ham,sub_add_cancel]
    rw [hat,derivativeAt_mul hU]
  have heq : (fun t => (a t).derivativeAt p)=(fun t => ((a (t-s)).derivativeAt y).comp ((a s).derivativeAt p)) := funext he
  rw [heq]
  exact hd

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ContinuousAutTransport
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061

namespace Biholomorph

open Set Filter Topology

variable {n m : ℕ} {U : Set (Affine n)} {D : Set (Affine m)}

theorem continuous_of_joint_evaluation {T : Type*} [TopologicalSpace T]
    (a : T → Biholomorph U U)
    (hf : Continuous fun p : T × U => (a p.1).toHomeomorph p.2)
    (hi : Continuous fun p : T × U => (a p.1).toHomeomorph.symm p.2) :
    Continuous a := by
  apply compactOpenPair_isEmbedding.isInducing.continuous_iff.mpr
  exact (ContinuousMap.continuous_of_continuous_uncurry _ hf).prodMk
    (ContinuousMap.continuous_of_continuous_uncurry _ hi)

theorem continuous_joint_evaluation [LocallyCompactSpace U] :
    Continuous fun p : Biholomorph U U × U => p.1.toHomeomorph p.2 := by
  exact continuous_eval.comp
    ((continuous_compactOpenPair.fst.comp continuous_fst).prodMk continuous_snd)

theorem continuous_joint_inverse_evaluation [LocallyCompactSpace U] :
    Continuous fun p : Biholomorph U U × U => p.1.toHomeomorph.symm p.2 := by
  exact continuous_eval.comp
    ((continuous_compactOpenPair.snd.comp continuous_fst).prodMk continuous_snd)

theorem continuous_autTransport [LocallyCompactSpace U]
    (e : Biholomorph U D) : Continuous (autTransport e) := by
  apply continuous_of_joint_evaluation
  · exact e.toHomeomorph.continuous.comp (continuous_joint_evaluation.comp
      (continuous_fst.prodMk (e.toHomeomorph.symm.continuous.comp continuous_snd)))
  · exact e.toHomeomorph.continuous.comp (continuous_joint_inverse_evaluation.comp
      (continuous_fst.prodMk (e.toHomeomorph.symm.continuous.comp continuous_snd)))

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AdNilpotentPositiveDilations
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology
namespace Biholomorph
variable {n : ℕ} {D : Set (Affine n)}

 theorem translationAut_add (v : Affine n)
    (hD : ∀ t : ℝ, ∀ x, x+t • v ∈ D ↔ x∈D) (s t : ℝ) :
    translationAut v hD (s+t)=translationAut v hD s*translationAut v hD t := by
  apply Biholomorph.ext
  intro x
  apply Subtype.ext
  simp only [translationAut_apply,mul_apply,add_smul]
  abel

 theorem continuous_translationAut (v : Affine n)
    (hD : ∀ t : ℝ, ∀ x, x+t • v ∈ D ↔ x∈D) : Continuous (translationAut v hD) := by
  apply continuous_of_joint_evaluation
  · apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_snd).add (continuous_fst.smul continuous_const)
  · apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_snd).add
      (continuous_fst.neg.smul continuous_const)

 theorem linearAut_translation_conjugate (v : Affine n)
    (hD : ∀ t : ℝ, ∀ x, x+t • v ∈ D ↔ x∈D)
    (L : Affine n ≃L[ℂ] Affine n) (hL : ∀ x, L x∈D ↔ x∈D)
    (r : ℝ) (hv : L v=r • v) (t : ℝ) :
    linearAut L hL*translationAut v hD t*(linearAut L hL)⁻¹=
      translationAut v hD (r*t) := by
  apply Biholomorph.ext
  intro x
  apply Subtype.ext
  change L (L.symm x.val+t • v)=x.val+(r*t) • v
  have hs : L (t • v)=t • L v := (L.restrictScalars ℝ).map_smul t v
  rw [map_add,hs,L.apply_symm_apply,hv,smul_smul,mul_comm t r]

end Biholomorph
end Release061

open Filter Topology

theorem LinearMap.isNilpotent_of_positive_smul_conjugate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (A : E →ₗ[ℝ] E)
    (hA : ∀ r : ℝ, 0 < r → ∃ e : E ≃ₗ[ℝ] E, e.conj A = r • A) :
    IsNilpotent A := by
  apply (LinearMap.isNilpotent_iff_charpoly A).2
  apply Polynomial.funext
  intro t
  let F : ℝ → ℝ := fun r =>
    (t • ContinuousLinearMap.id ℝ E-r • A.toContinuousLinearMap).det
  have hF : Continuous F := ContinuousLinearMap.continuous_det.comp
    (continuous_const.sub (continuous_id.smul continuous_const))
  have hpos (r : ℝ) (hr : 0 < r) : F r=A.charpoly.eval t := by
    obtain ⟨e,he⟩ := hA r hr
    have hh := congrArg (Polynomial.eval t) (e.charpoly_conj A)
    rw [he,LinearMap.eval_charpoly] at hh
    exact hh
  have hlim : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (F 0)) :=
    hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hconst : F =ᶠ[𝓝[>] (0 : ℝ)] fun _ => A.charpoly.eval t := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hpos r hr
  have hEq : F 0=A.charpoly.eval t := tendsto_nhds_unique hlim
    (tendsto_const_nhds.congr' hconst.symm)
  rw [←hEq]
  simp [F,ContinuousLinearMap.det,LinearMap.det_smul]

theorem LinearMap.isNilpotent_of_positive_smul_conjugate_algebraic
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] E)
    (hA : ∀ r : ℝ, 0 < r → ∃ e : E ≃ₗ[ℝ] E, e.conj A = r • A) :
    IsNilpotent A := by
  classical
  let b := Module.Free.chooseBasis ℝ E
  let e := b.equivFun
  have h := LinearMap.isNilpotent_of_positive_smul_conjugate (e.conj A) (by
    intro r hr
    obtain ⟨g,hg⟩ := hA r hr
    refine ⟨(e.symm.trans g).trans e,?_⟩
    apply LinearMap.ext
    intro x
    have hh := congrArg (fun T : E →ₗ[ℝ] E => e (T (e.symm x))) hg
    simpa [LinearEquiv.conj_apply,LinearEquiv.trans_apply] using hh)
  obtain ⟨N,hN⟩ := h
  have heq : e.conjRingEquiv A=e.conj A := by
    apply LinearMap.ext
    intro x
    rfl
  exact ⟨N,e.conjRingEquiv.injective (by simpa only [map_pow,map_zero,heq] using hN)⟩

theorem LieAlgebra.ad_isNilpotent_of_positive_dilations
    {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    (X : L) (hX : ∀ r : ℝ, 0 < r → ∃ e : L ≃ₗ⁅ℝ⁆ L, e X=r • X) :
    IsNilpotent (LieAlgebra.ad ℝ L X) := by
  apply LinearMap.isNilpotent_of_positive_smul_conjugate_algebraic
  intro r hr
  obtain ⟨e,he⟩ := hX r hr
  refine ⟨e.toLinearEquiv,?_⟩
  apply LinearMap.ext
  intro Y
  change e ⁅X,e.symm Y⁆ = r • ⁅X,Y⁆
  rw [e.map_lie,he,e.apply_symm_apply,smul_lie]

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CoordinateFieldApply
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
namespace Release061
open Set Filter Topology
namespace Biholomorph
open scoped Classical
variable {n m : ℕ} {U : Set (Affine n)} {D : Set (Affine m)}

 theorem coordinateField_symm_cancel (hU : IsOpen U) (hD : IsOpen D)
    (e : Biholomorph U D) (X : Affine n → Affine n)
    (hX : ∀ x, x∉U → X x=0) : coordinateField e.symm (coordinateField e X)=X := by
  funext x
  by_cases hx : x∈U
  · rw [coordinateField_apply _ _ ⟨x,hx⟩,coordinateField_apply]
    change e.symm.mapDerivative (e.toHomeomorph ⟨x,hx⟩)
      (e.mapDerivative (e.toHomeomorph.symm (e.toHomeomorph ⟨x,hx⟩))
        (X (e.toHomeomorph.symm (e.toHomeomorph ⟨x,hx⟩)).val))=X x
    rw [e.toHomeomorph.symm_apply_apply]
    exact congrArg (fun L : Affine n →L[ℂ] Affine n => L (X x))
      (mapDerivative_symm_comp hU hD e ⟨x,hx⟩)
  · simp only [coordinateField,dite_eq_right hx,hX x hx]

 theorem infinitesimalGenerator_autTransport (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U) (e : Biholomorph U D)
    (a : ℝ → Biholomorph U U) (ha : Continuous a) (ha0 : a 0=1)
    (ham : ∀ s t, a (s+t)=a s*a t) :
    infinitesimalGenerator (fun t => autTransport e (a t))=
      coordinateField e (infinitesimalGenerator a) := by
  funext x
  by_cases hx : x∈D
  · let y : U := e.toHomeomorph.symm ⟨x,hx⟩
    have hy : (a 0).ambientAut y.val=y.val := by rw [ha0,ambientAut_apply,one_apply]
    have hq : HasFDerivAt e.ambientMap ((e.mapDerivative y).restrictScalars ℝ)
        ((a 0).ambientAut y.val) := by
      rw [hy]
      exact ((e.ambientMap_analytic hU y.val y.property).differentiableAt.hasFDerivAt).restrictScalars ℝ
    have hcomp := hq.comp_hasDerivAt 0 (infinitesimalGenerator_hasDerivAt hU hbd a ha ha0 ham y.val)
    have heq : (fun t => e.ambientMap ((a t).ambientAut y.val))=
        (fun t => (autTransport e (a t)).ambientAut x) := by
      funext t
      rw [ambientAut_apply (autTransport e (a t)) ⟨x,hx⟩,
        ambientAut_apply,ambientMap_apply]
      rfl
    change HasDerivAt (fun t => e.ambientMap ((a t).ambientAut y.val))
      ((e.mapDerivative y) (infinitesimalGenerator a y.val)) 0 at hcomp
    rw [heq] at hcomp
    change deriv (fun t => (autTransport e (a t)).ambientAut x) 0=_
    rw [hcomp.deriv,coordinateField,dite_eq_left hx]
  · rw [infinitesimalGenerator_of_not_mem _ hx,coordinateField,dite_eq_right hx]

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_LieBracketIndicatorConst
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
attribute [-simp] _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
namespace Release061
open Set Filter Topology
namespace Biholomorph

section
open scoped Classical
variable {n : ℕ} {D : Set (Affine n)}

 theorem infinitesimalGenerator_translationAut (v : Affine n)
    (hD : ∀ t : ℝ, ∀ x, x+t • v∈D ↔ x∈D) :
    infinitesimalGenerator (translationAut v hD)=D.indicator (fun _ => v) := by
  funext x
  by_cases hx : x∈D
  · have hh : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by
      convert ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x using 1 <;> first | rfl | exact (one_smul ℝ v).symm
    change deriv (fun t => (translationAut v hD t).ambientAut x) 0=_
    have he : (fun t => (translationAut v hD t).ambientAut x)=fun t => x+t • v := by
      funext t
      rw [ambientAut_apply _ ⟨x,hx⟩,translationAut_apply]
    rw [he,hh.deriv,Set.indicator_of_mem hx]
  · rw [infinitesimalGenerator_of_not_mem _ hx,Set.indicator_of_notMem hx]

 theorem transported_translation_generator_in_model {m : ℕ} {U : Set (Affine m)}
    (hU : IsOpen U) [LocallyCompactSpace U] (hbd : Bornology.IsBounded U)
    [LocallyCompactSpace D] (e : Biholomorph D U)
    (v : Affine n) (hD : ∀ t : ℝ, ∀ x, x+t • v∈D ↔ x∈D) :
    coordinateField e.symm
      (infinitesimalGenerator (fun t => autTransport e (translationAut v hD t)))=
      D.indicator (fun _ => v) := by
  let b : ℝ → Biholomorph U U := fun t => autTransport e (translationAut v hD t)
  have hb : Continuous b := (continuous_autTransport e).comp (continuous_translationAut v hD)
  have hb0 : b 0=1 := by simp [b]
  have hbm : ∀ s t, b (s+t)=b s*b t := by
    intro s t; simp only [b,translationAut_add,autTransport_mul]
  rw [←infinitesimalGenerator_autTransport hU hbd e.symm b hb hb0 hbm]
  have he : (fun t => autTransport e.symm (b t))=translationAut v hD := by
    funext t
    exact autTransport_symm_cancel e (translationAut v hD t)
  rw [he,infinitesimalGenerator_translationAut]

end

open scoped Classical
variable {n m : ℕ} {D : Set (Affine n)} {U : Set (Affine m)}

 theorem infinitesimalGenerator_eq_indicator_of_hasDerivAt
    (a : ℝ → Biholomorph D D) (V : Affine n → Affine n)
    (hd : ∀ x : D, HasDerivAt (fun t => (a t).toHomeomorph x |>.val) (V x.val) 0) :
    infinitesimalGenerator a=D.indicator V := by
  funext x
  by_cases hx : x∈D
  · change deriv (fun t => (a t).ambientAut x) 0=_
    have he : (fun t => (a t).ambientAut x)=fun t => ((a t).toHomeomorph ⟨x,hx⟩).val := by
      funext t; exact ambientAut_apply _ ⟨x,hx⟩
    rw [he,(hd ⟨x,hx⟩).deriv,Set.indicator_of_mem hx]
  · rw [infinitesimalGenerator_of_not_mem _ hx,Set.indicator_of_notMem hx]

 theorem exists_complete_generator_in_model
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U] [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    [LocallyCompactSpace D] (e : Biholomorph D U)
    (a : ℝ → Biholomorph D D) (ha : Continuous a) (ha0 : a 0=1)
    (ham : ∀ s t, a (s+t)=a s*a t) (V : Affine n → Affine n)
    (hd : ∀ x : D, HasDerivAt (fun t => ((a t).toHomeomorph x).val) (V x.val) 0) :
    ∃ X : completeGeneratorSpace hU hc hbd Γ hhol,
      coordinateField e.symm X.val=D.indicator V := by
  let b : ℝ → Biholomorph U U := fun t => autTransport e (a t)
  have hb : Continuous b := (continuous_autTransport e).comp ha
  have hb0 : b 0=1 := by simp [b,ha0]
  have hbm : ∀ s t, b (s+t)=b s*b t := by
    intro s t; simp only [b,ham,autTransport_mul]
  refine ⟨⟨infinitesimalGenerator b,⟨b,hb,hb0,hbm,rfl⟩⟩,?_⟩
  rw [←infinitesimalGenerator_autTransport hU hbd e.symm b hb hb0 hbm]
  have he : (fun t => autTransport e.symm (b t))=a := by
    funext t; exact autTransport_symm_cancel e (a t)
  rw [he]
  exact infinitesimalGenerator_eq_indicator_of_hasDerivAt a V hd

 theorem exists_complete_linear_generator_in_model
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U] [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    [LocallyCompactSpace D] (e : Biholomorph D U)
    (L : ℝ → Affine n ≃L[ℂ] Affine n)
    (hL : ∀ t x, L t x∈D ↔ x∈D)
    (h0 : ∀ x, L 0 x=x) (hm : ∀ s t x, L (s+t) x=L s (L t x))
    (hcont : Continuous (fun p : ℝ × Affine n => L p.1 p.2))
    (A : Affine n →L[ℂ] Affine n)
    (hd : ∀ x, HasDerivAt (fun t => L t x) (A x) 0) :
    ∃ X : completeGeneratorSpace hU hc hbd Γ hhol,
      coordinateField e.symm X.val=D.indicator A := by
  let a : ℝ → Biholomorph D D := fun t => linearAut (L t) (hL t)
  have ha : Continuous a := by
    apply continuous_of_joint_evaluation
    · apply Continuous.subtype_mk
      exact hcont.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    · have hi : ∀ t x, (L t).symm x=L (-t) x := by
        intro t x
        apply (L t).injective
        rw [(L t).apply_symm_apply,←hm,add_neg_cancel,h0]
      apply Continuous.subtype_mk
      change Continuous (fun p : ℝ × D => (L p.1).symm p.2.val)
      simp_rw [hi]
      exact hcont.comp (continuous_fst.neg.prodMk (continuous_subtype_val.comp continuous_snd))
  apply exists_complete_generator_in_model hU hc hbd Γ hhol e a ha
  · apply Biholomorph.ext
    intro x
    apply Subtype.ext
    exact h0 x.val
  · intro s t
    apply Biholomorph.ext
    intro x
    apply Subtype.ext
    exact hm s t x.val
  · intro x
    exact hd x.val

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FieldSecondJet
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
attribute [-simp] _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
namespace Release061
open Set Filter Topology
namespace Biholomorph

 theorem hasDerivAt_rotationScalar : HasDerivAt rotationScalar Complex.I 0 := by
  have h : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    convert Complex.ofRealCLM.hasDerivAt using 1 <;> rfl
  convert (h.mul_const Complex.I).cexp using 1 <;> first | rfl | simp

 theorem hasDerivAt_flatTangentialRotation (r k : ℕ) (x : Affine (r+k)) :
    HasDerivAt (fun t => flatTangentialRotation r k t x) (flatTangentialInfinitesimal r k x) 0 := by
  let e := affineProductCoordinates r k
  have hp := (hasDerivAt_rotationScalar.smul_const (e.symm x).1).prodMk
    (hasDerivAt_const (0 : ℝ) (e.symm x).2)
  have hh := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := Affine r × Affine k)
    (E := Affine (r+k)) 0 (e.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt hp
  convert hh using 1 <;> rfl

 theorem flatTangentialRotation_mem {r k : ℕ} (D : Set (Affine r × Affine k))
    (hr : ∀ c : ℂ, ‖c‖=1 → ∀ p, (c • p.1,p.2)∈D ↔ p∈D)
    (t : ℝ) (x : Affine (r+k)) :
    flatTangentialRotation r k t x∈(affineProductCoordinates r k) '' D ↔
      x∈(affineProductCoordinates r k) '' D := by
  let e := affineProductCoordinates r k
  have hi (y : Affine (r+k)) : y∈e '' D ↔ e.symm y∈D := by
    constructor
    · rintro ⟨p,hp,rfl⟩; simpa only [e.symm_apply_apply] using hp
    · intro h; exact ⟨e.symm y,h,e.apply_symm_apply y⟩
  rw [hi,hi]
  change e.symm (e (rotationScalar t • (e.symm x).1,(e.symm x).2)) ∈ D ↔ _
  rw [e.symm_apply_apply]
  exact hr _ (rotationScalar_norm t) _

 theorem exists_actual_model_rotation {r k n : ℕ}
    (D : Set (Affine r × Affine k))
    (hr : ∀ c : ℂ, ‖c‖=1 → ∀ p, (c • p.1,p.2)∈D ↔ p∈D)
    {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    [LocallyCompactSpace ((affineProductCoordinates r k) '' D)]
    (e : Biholomorph ((affineProductCoordinates r k) '' D) U) :
    ∃ H : completeGeneratorSpace hU hc hbd Γ hhol,
      coordinateField e.symm H.val=((affineProductCoordinates r k) '' D).indicator
        (flatTangentialInfinitesimal r k) := by
  apply exists_complete_linear_generator_in_model hU hc hbd Γ hhol e
    (flatTangentialRotation r k) (flatTangentialRotation_mem D hr)
  · intro x
    simp
  · intro s t x
    simp [mul_smul]
  · simp_rw [flatTangentialRotation_apply]
    apply (affineProductCoordinates r k).continuous.comp
    have hc : Continuous rotationScalar := by
      exact Complex.continuous_exp.comp ((Complex.continuous_ofReal).mul_const Complex.I)
    exact ((hc.comp continuous_fst).smul
      (continuous_fst.comp ((affineProductCoordinates r k).symm.continuous.comp continuous_snd))).prodMk
      (continuous_snd.comp ((affineProductCoordinates r k).symm.continuous.comp continuous_snd))
  · exact hasDerivAt_flatTangentialRotation r k

end Biholomorph
end Release061

open Filter Topology
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 omit [CompleteSpace E] in
 theorem hasFDerivAt_centeredLinear (A : E →L[ℂ] E) (p x : E) :
    HasFDerivAt (fun y => A (y-p)) A x := by
  convert A.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const p) using 1 <;> rfl

 omit [CompleteSpace E] in
 theorem lieBracket_centeredLinear_eq (A : E →L[ℂ] E) (p : E) (V : E → E) :
    VectorField.lieBracket ℂ (fun y => A (y-p)) V =
      fun x => (fderiv ℂ V x) (A (x-p))-A (V x) := by
  funext x
  rw [VectorField.lieBracket,(hasFDerivAt_centeredLinear A p x).fderiv]

 theorem fderiv_lieBracket_centeredLinear (A : E →L[ℂ] E) (p : E)
    {V : E → E} {x : E} (hV : AnalyticAt ℂ V x) :
    fderiv ℂ (VectorField.lieBracket ℂ (fun y => A (y-p)) V) x=
      (fderiv ℂ V x).comp A+(fderiv ℂ (fderiv ℂ V) x).flip (A (x-p))-
        A.comp (fderiv ℂ V x) := by
  rw [lieBracket_centeredLinear_eq]
  have hd := (hV.fderiv.differentiableAt.hasFDerivAt.clm_apply
    (hasFDerivAt_centeredLinear A p x)).sub
    (A.hasFDerivAt.comp x hV.differentiableAt.hasFDerivAt)
  exact hd.fderiv

 omit [CompleteSpace E] in
 theorem lieBracket_centeredLinear_zeroJet (A : E →L[ℂ] E) (p : E) (V : E → E) :
    VectorField.lieBracket ℂ (fun y => A (y-p)) V p= -A (V p) := by
  rw [lieBracket_centeredLinear_eq]
  simp

 theorem lieBracket_centeredLinear_firstJet (A : E →L[ℂ] E) (p : E)
    {V : E → E} (hV : AnalyticAt ℂ V p) :
    fderiv ℂ (VectorField.lieBracket ℂ (fun y => A (y-p)) V) p=
      (fderiv ℂ V p).comp A-A.comp (fderiv ℂ V p) := by
  rw [fderiv_lieBracket_centeredLinear A p hV]
  simp

 theorem lieBracket_centeredLinear_secondJet (A : E →L[ℂ] E) (p : E)
    {V : E → E} (hV : AnalyticAt ℂ V p) (u v : E) :
    (fderiv ℂ (fderiv ℂ (VectorField.lieBracket ℂ (fun y => A (y-p)) V)) p) u v=
      (fderiv ℂ (fderiv ℂ V) p) u (A v)+
      (fderiv ℂ (fderiv ℂ V) p) v (A u)-A ((fderiv ℂ (fderiv ℂ V) p) u v) := by
  let R : E → E →L[ℂ] E →L[ℂ] E := fun x => (fderiv ℂ (fderiv ℂ V) x).flip
  have hR : DifferentiableAt ℂ R p := by
    have hL : Differentiable ℂ (fun B : E →L[ℂ] E →L[ℂ] E => B.flip) := by
      exact LinearIsometryEquiv.differentiable (𝕜 := ℂ) (E := E →L[ℂ] E →L[ℂ] E)
        (F := E →L[ℂ] E →L[ℂ] E) (ContinuousLinearMap.flipₗᵢ ℂ E E E)
    exact DifferentiableAt.comp (𝕜 := ℂ) (F := E →L[ℂ] E →L[ℂ] E)
      (G := E →L[ℂ] E →L[ℂ] E) p (hL _) hV.fderiv.fderiv.differentiableAt
  have he : fderiv ℂ (VectorField.lieBracket ℂ (fun y => A (y-p)) V) =ᶠ[𝓝 p]
      fun x => (fderiv ℂ V x).comp A+R x (A (x-p))-A.comp (fderiv ℂ V x) := by
    filter_upwards [hV.eventually_analyticAt] with x hx
    exact fderiv_lieBracket_centeredLinear A p hx
  rw [he.fderiv_eq]
  have h1 := hV.fderiv.differentiableAt.hasFDerivAt.clm_comp (hasFDerivAt_const A p)
  have h2 := hR.hasFDerivAt.clm_apply (hasFDerivAt_centeredLinear A p p)
  have h3 := (hasFDerivAt_const A p).clm_comp hV.fderiv.differentiableAt.hasFDerivAt
  have hd := (h1.add h2).sub h3
  change (fderiv ℂ (((fun x => (fderiv ℂ V x).comp A)+fun x => R x (A (x-p)))-
    fun x => A.comp (fderiv ℂ V x)) p) u v=_
  rw [hd.fderiv]
  simp only [R, add_apply, sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, zero_apply]
  simp only [sub_self, map_zero, zero_apply, zero_add, add_zero]
end

open Filter Topology

section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace E] in
theorem ZeroSecondJet.comp {f : F → G} {g : E → F} {p : E}
    (hf : AnalyticAt ℂ f (g p)) (hg : AnalyticAt ℂ g p)
    (hz : ZeroSecondJet f (g p)) : ZeroSecondJet (f ∘ g) p := by
  obtain ⟨hz0,hz1,hz2⟩ := hz
  refine ⟨hz0,?_,?_⟩
  · rw [fderiv_comp p hf.differentiableAt hg.differentiableAt,hz1,ContinuousLinearMap.zero_comp]
  · have he : fderiv ℂ (f ∘ g) =ᶠ[𝓝 p]
        fun x => (fderiv ℂ f (g x)).comp (fderiv ℂ g x) := by
      filter_upwards [hg.eventually_analyticAt,
        hg.continuousAt.preimage_mem_nhds hf.eventually_analyticAt] with x hx hx'
      exact fderiv_comp x hx'.differentiableAt hx.differentiableAt
    rw [he.fderiv_eq]
    have hd := (hf.fderiv.differentiableAt.hasFDerivAt.comp p hg.differentiableAt.hasFDerivAt).clm_comp
      hg.fderiv.differentiableAt.hasFDerivAt
    simp only [Function.comp_def] at hd
    rw [hd.fderiv]
    simp [hz1,hz2]

omit [CompleteSpace E] in
theorem ZeroSecondJet.clm_apply {H : E → F →L[ℂ] G} {Z : E → F} {p : E}
    (hH : AnalyticAt ℂ H p) (hZ : AnalyticAt ℂ Z p)
    (hz : ZeroSecondJet Z p) : ZeroSecondJet (fun x => H x (Z x)) p := by
  obtain ⟨hz0,hz1,hz2⟩ := hz
  refine ⟨by simp [hz0],?_,?_⟩
  · rw [fderiv_clm_apply hH.differentiableAt hZ.differentiableAt]
    simp [hz0,hz1]
  · let R : E → F →L[ℂ] E →L[ℂ] G := fun x => (fderiv ℂ H x).flip
    let L : (E →L[ℂ] F →L[ℂ] G) →L[ℂ] (F →L[ℂ] E →L[ℂ] G) :=
      (ContinuousLinearMap.flipₗᵢ ℂ E F G).toContinuousLinearEquiv.toContinuousLinearMap
    have hR : DifferentiableAt ℂ R p := by
      change DifferentiableAt ℂ (L ∘ fderiv ℂ H) p
      have hL : Differentiable ℂ (fun B : E →L[ℂ] F →L[ℂ] G => B.flip) := by
        exact LinearIsometryEquiv.differentiable (𝕜 := ℂ) (E := E →L[ℂ] F →L[ℂ] G)
          (F := F →L[ℂ] E →L[ℂ] G) (ContinuousLinearMap.flipₗᵢ ℂ E F G)
      exact DifferentiableAt.comp (𝕜 := ℂ) (F := E →L[ℂ] F →L[ℂ] G)
        (G := F →L[ℂ] E →L[ℂ] G) p (hL _) hH.fderiv.differentiableAt
    have he : fderiv ℂ (fun x => H x (Z x)) =ᶠ[𝓝 p]
        fun x => (H x).comp (fderiv ℂ Z x)+R x (Z x) := by
      filter_upwards [hH.eventually_analyticAt,hZ.eventually_analyticAt] with x hx hx'
      exact fderiv_clm_apply hx.differentiableAt hx'.differentiableAt
    rw [he.fderiv_eq]
    have ha := hH.differentiableAt.hasFDerivAt.clm_comp hZ.fderiv.differentiableAt.hasFDerivAt
    have hb := hR.hasFDerivAt.clm_apply hZ.differentiableAt.hasFDerivAt
    change fderiv ℂ ((fun x => (H x).comp (fderiv ℂ Z x)) + fun x => R x (Z x)) p=0
    rw [(ha.add hb).fderiv]
    simp [hz0,hz1,hz2]

end

open Filter Topology

open Polynomial

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticSecondJetCoordinates
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial

open Filter Topology

variable {E V ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [AddCommGroup V] [Module ℂ V]
    (F : V →ₗ[ℂ] (E → E)) (p : E) (hF : ∀ X, AnalyticAt ℂ (F X) p)
    (b : Module.Basis ι ℂ E)

 omit [CompleteSpace E] in
 theorem basis_coordinate_diagonal (A : E →L[ℂ] E) (w : ι → ℂ)
    (hA : ∀ i, A (b i)=w i • b i) (x : E) (i : ι) :
    b.repr (A x) i=w i*b.repr x i := by
  classical
  have he : (b.coord i).comp A.toLinearMap=w i • b.coord i := by
    apply b.ext
    intro j
    simp only [LinearMap.comp_apply,ContinuousLinearMap.coe_coe,hA,map_smul,
      LinearMap.smul_apply,Module.Basis.coord_apply,Module.Basis.repr_self,Finsupp.single_apply,
      smul_eq_mul]
    split_ifs with h
    · subst j; rfl
    · simp
  exact LinearMap.congr_fun he x

 theorem analyticSecondJetCoordinates_euler (A : E →L[ℂ] E) (w : ι → ℂ)
    (hA : ∀ i, A (b i)=w i • b i) (B : Module.End ℂ V)
    (hB : ∀ X, F (B X) =ᶠ[𝓝 p] VectorField.lieBracket ℂ (fun y => A (y-p)) (F X)) :
    ∀ X j, analyticSecondJetCoordinates F p hF b (B X) j=
      secondJetWeight w j*analyticSecondJetCoordinates F p hF b X j := by
  intro X j
  rcases j with i | (⟨i,j⟩ | ⟨i,j,k⟩)
  · change b.repr (F (B X) p) i=(-w i)*b.repr (F X p) i
    rw [(hB X).eq_of_nhds,lieBracket_centeredLinear_zeroJet,map_neg,Finsupp.neg_apply,
      basis_coordinate_diagonal b A w hA,neg_mul]
  · change b.repr (fderiv ℂ (F (B X)) p (b j)) i=(w j-w i)*b.repr (fderiv ℂ (F X) p (b j)) i
    rw [(hB X).fderiv_eq,lieBracket_centeredLinear_firstJet A p (hF X)]
    simp only [sub_apply,ContinuousLinearMap.comp_apply,hA,map_smul,
      map_sub,Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul,basis_coordinate_diagonal b A w hA]
    ring
  · change b.repr (fderiv ℂ (fderiv ℂ (F (B X))) p (b j) (b k)) i=
      (w j+w k-w i)*b.repr (fderiv ℂ (fderiv ℂ (F X)) p (b j) (b k)) i
    rw [(hB X).fderiv.fderiv_eq,lieBracket_centeredLinear_secondJet A p (hF X),hA,hA]
    simp only [map_smul,map_add,map_sub,Finsupp.add_apply,
      Finsupp.sub_apply,Finsupp.smul_apply,smul_eq_mul,basis_coordinate_diagonal b A w hA]
    rw [((hF X).contDiffAt.isSymmSndFDerivAt_of_omega) (b k) (b j)]
    ring

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_HermPartUnit
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Hermitian
open Complex
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [Module ℂ E]
  [IsScalarTower ℝ ℂ E]

omit [IsScalarTower ℝ ℂ E] in
lemma hermPart_conj (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hs : ∀ x y, B x y = B y x)
    (x y : E) : hermPart B y x = star (hermPart B x y) := by
  apply Complex.ext <;> simp [hermPart,hs y x,hs (I • y) (I • x),hs y (I • x),hs (I • y) x]
  ring

end Release061.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CommutingGeneratorsValueZero
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
namespace Release061
open Set Filter Topology
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U)
include hU hbd

theorem pushForwardGenerator_eq_of_bracket_zero
    (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    {Y : Affine n → Affine n} (hY : IsCompleteGenerator U Y)
    (hbr : VectorField.lieBracket ℂ (infinitesimalGenerator a) Y=0) (s : ℝ) :
    pushForwardGenerator (a s) Y=Y := by
  funext x
  by_cases hx : x∈U
  · have hd (t : ℝ) : HasDerivAt (fun r => pushForwardGenerator (a r) Y x) 0 t := by
      let q : U := (a t).toHomeomorph.symm ⟨x,hx⟩
      have h0 := pushForwardGenerator_hasDerivAt_zero hU hbd a ha ha0 ham Y
        (hY.analyticOnNhd hU hbd) q.val q.property
      rw [hbr,Pi.zero_apply,neg_zero] at h0
      have hs : HasDerivAt (fun r => pushForwardGenerator (a (r-t)) Y q.val) 0 t := by
        have h0' : HasDerivAt (fun r => pushForwardGenerator (a r) Y q.val) 0 (t-t) :=
          sub_self t ▸ h0
        convert h0'.scomp t (h := fun r : ℝ => r-t) ((hasDerivAt_id t).sub_const t) using 1 <;> first | rfl | exact (smul_zero _).symm
      have hh := (((a t).derivativeAt q).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hs
      rw [map_zero] at hh
      apply hh.congr_of_eventuallyEq
      filter_upwards [] with r
      change pushForwardGenerator (a r) Y x =
        (a t).derivativeAt q (pushForwardGenerator (a (r-t)) Y q.val)
      rw [←pushForwardGenerator_apply (a t) _ ⟨x,hx⟩,←pushForwardGenerator_mul hU,
        ←ham,add_sub_cancel]
    have he := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
      (fun t => (hd t).deriv) s 0
    rw [ha0,pushForwardGenerator_one hU (fun _ hz => hY.eq_zero_of_not_mem hz)] at he
    exact he
  · rw [pushForwardGenerator,dite_eq_right hx,hY.eq_zero_of_not_mem hx]

 theorem generator_cross_equivariant
    (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    {Y : Affine n → Affine n} (hY : IsCompleteGenerator U Y)
    (hbr : VectorField.lieBracket ℂ (infinitesimalGenerator a) Y=0)
    (p : U) (t : ℝ) :
    Y ((a t).toHomeomorph p).val=(a t).derivativeAt p (Y p.val) := by
  have he := congrFun (pushForwardGenerator_eq_of_bracket_zero hU hbd a ha ha0 ham hY hbr t)
    ((a t).toHomeomorph p).val
  rw [pushForwardGenerator_apply] at he
  simpa only [Homeomorph.symm_apply_apply] using he.symm

theorem commuting_generators_value_zero
    (a b : ℝ → Biholomorph U U) (ha : Continuous a) (hb : Continuous b)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    (hb0 : b 0=1) (hbm : ∀ s t, b (s+t)=b s*b t)
    (hbr : VectorField.lieBracket ℂ (infinitesimalGenerator b) (infinitesimalGenerator a)=0)
    (p : U) (hrel : infinitesimalGenerator b p.val=Complex.I • infinitesimalGenerator a p.val) :
    infinitesimalGenerator a p.val=0 := by
  let f : ℂ → Affine n := fun z =>
    ((a z.re).toHomeomorph ((b z.im).toHomeomorph p)).val
  have hba (t : ℝ) : infinitesimalGenerator b ((b t).toHomeomorph p).val=
      Complex.I • infinitesimalGenerator a ((b t).toHomeomorph p).val := by
    rw [infinitesimalGenerator_equivariant hU b hb hbd hb0 hbm p t,hrel,map_smul,
      generator_cross_equivariant hU hbd b hb hb0 hbm ⟨a,ha,ha0,ham,rfl⟩ hbr p t]
  have hf : Differentiable ℂ f := by
    intro z
    let q : U := (b z.im).toHomeomorph p
    let v : Affine n := infinitesimalGenerator a ((a z.re).toHomeomorph q).val
    have hB := ((oneParameter_orbit_ODE hU b hb hbd hb0 hbm p z.im).hasFDerivAt).comp z
      Complex.imCLM.hasFDerivAt
    have hA := (oneParameter_joint_hasStrictFDerivAt hU a ha hbd ha0 ham z.re q).hasFDerivAt
    have hR := hA.comp z (Complex.reCLM.hasFDerivAt.prodMk hB)
    have he : (ContinuousLinearMap.toSpanSingleton ℂ v).restrictScalars ℝ =
        ((ContinuousLinearMap.toSpanSingleton ℝ v).coprod
          (((a z.re).derivativeAt q).restrictScalars ℝ)).comp
          (Complex.reCLM.prod ((ContinuousLinearMap.toSpanSingleton ℝ
            (infinitesimalGenerator b q.val)).comp Complex.imCLM)) := by
      apply ContinuousLinearMap.ext
      intro w
      simp only [ContinuousLinearMap.toSpanSingleton_apply,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coprod_apply,ContinuousLinearMap.prod_apply,
        Complex.reCLM_apply,Complex.imCLM_apply]
      change w • v = w.re • v + ((a z.re).derivativeAt q)
        (w.im • infinitesimalGenerator b q.val)
      rw [hba,ContinuousLinearMap.map_smul_of_tower,map_smul,
        ←infinitesimalGenerator_equivariant hU a ha hbd ha0 ham q z.re]
      exact Hermitian.complex_smul_split w v
    apply (hasFDerivAt_of_restrictScalars (𝕜 := ℝ) hR he).differentiableAt.congr_of_eventuallyEq
    filter_upwards [] with w
    exact (ambientAut_apply (a w.re) ((b w.im).toHomeomorph p)).symm
  have hbounded : Bornology.IsBounded (Set.range f) := hbd.subset
    (by rintro _ ⟨z,rfl⟩; exact ((a z.re).toHomeomorph ((b z.im).toHomeomorph p)).property)
  have hconst (t : ℝ) : ((a t).toHomeomorph p).val=p.val := by
    have hh := hf.apply_eq_apply_of_bounded hbounded (t : ℂ) 0
    simpa only [f,Complex.ofReal_re,Complex.ofReal_im,Complex.zero_re,Complex.zero_im,
      hb0,ha0,one_apply] using hh
  exact (oneParameter_hasDerivAt_zero hU a ha hbd ha0 ham p).unique
    ((hasDerivAt_const (0 : ℝ) p.val).congr_of_eventuallyEq (Eventually.of_forall hconst))
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ZeroISmul
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
namespace Release061

section
open Set Filter Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

theorem flow_generator_commutes (a : ℝ → A) (d : A)
    (_ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t) (hd : HasDerivAt a d 0) (s : ℝ) :
    d*a s=a s*d := by
  have h1 := hd.mul_const (a s)
  have h2 := hd.const_mul (a s)
  have he : (fun t => a t*a s)=(fun t => a s*a t) := by
    funext t; rw [←ham,←ham,add_comm]
  rw [he] at h1
  exact h1.unique h2

theorem bounded_complex_flow_generator_zero (a b : ℝ → A) (d : A)
    (ha0 : a 0=1) (hb0 : b 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    (hda : ∀ t, HasDerivAt a (d*a t) t)
    (hdb : ∀ t, HasDerivAt b ((Complex.I • d)*b t) t)
    (hbd : Bornology.IsBounded (Set.range (fun z : ℂ => a z.re*b z.im))) : d=0 := by
  let f : ℂ → A := fun z => a z.re*b z.im
  have hd0 : HasDerivAt a d 0 := by simpa only [ha0,mul_one] using hda 0
  have hc := flow_generator_commutes a d ha0 ham hd0
  have hf : Differentiable ℂ f := by
    intro z
    have hA := (hda z.re).hasFDerivAt.comp z Complex.reCLM.hasFDerivAt
    have hB := (hdb z.im).hasFDerivAt.comp z Complex.imCLM.hasFDerivAt
    have hR := hA.mul' hB
    let v := d*a z.re*b z.im
    have he : (ContinuousLinearMap.toSpanSingleton ℂ v).restrictScalars ℝ =
        (a z.re • ((ContinuousLinearMap.toSpanSingleton ℝ ((Complex.I • d)*b z.im)).comp
          Complex.imCLM)) +
        (MulOpposite.op (b z.im) • ((ContinuousLinearMap.toSpanSingleton ℝ (d*a z.re)).comp Complex.reCLM)) := by
      ext w
      change w • v = a z.re*(w.im • ((Complex.I • d)*b z.im)) +
        (w.re • (d*a z.re))*b z.im
      rw [mul_smul_comm,smul_mul_assoc,mul_smul_comm,←mul_assoc,←hc,
        smul_mul_assoc]
      change w • v=w.im • (Complex.I • v)+w.re • v
      rw [add_comm]
      calc
        w • v = ((w.re : ℂ)+(w.im : ℂ)*Complex.I) • v := by rw [Complex.re_add_im]
        _ = (w.re : ℂ) • v+(w.im : ℂ) • (Complex.I • v) := by rw [add_smul,mul_smul]
        _ = _ := congrArg₂ (fun u u' : A => u+u')
          (RCLike.real_smul_eq_coe_smul (K := ℂ) w.re v).symm
          (RCLike.real_smul_eq_coe_smul (K := ℂ) w.im (Complex.I • v)).symm
    exact (hasFDerivAt_of_restrictScalars (𝕜 := ℝ) hR he).differentiableAt
  have hconst (t : ℝ) : a t=1 := by
    have hh := hf.apply_eq_apply_of_bounded hbd (t : ℂ) 0
    simpa only [f,Complex.ofReal_re,Complex.ofReal_im,Complex.zero_re,Complex.zero_im,
      hb0,ha0,mul_one] using hh
  exact hd0.unique ((hasDerivAt_const (0 : ℝ) (1 : A)).congr_of_eventuallyEq
    (Eventually.of_forall hconst))
end

open Set Filter Topology
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_IsotropyCompleteGeneratorsTotally
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
namespace Release061
open Set Filter Topology
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
include hU hc hbd
 theorem IsCompleteGenerator.eq_zero_of_zero_jet {X : Affine n → Affine n}
    (hX : IsCompleteGenerator U X) (p : U)
    (hval : X p.val=0) (hder : fderiv ℂ X p.val=0) : X=0 := by
  obtain ⟨a,ha,ha0,ham,rfl⟩ := hX
  have he : a=fun _ => 1 := funext fun t => oneParameter_eq_one_of_generator_zero_jet
    hU a ha hc.isPreconnected hbd ha0 ham p hval hder t
  rw [he,infinitesimalGenerator_one]

variable (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
include Γ hhol

theorem isotropy_complete_generators_totally_real {X Y : Affine n → Affine n}
    (hX : IsCompleteGenerator U X) (hY : IsCompleteGenerator U Y) (p : U)
    (hXp : X p.val=0) (hYp : Y p.val=0)
    (hrel : fderiv ℂ Y p.val=Complex.I • fderiv ℂ X p.val) : X=0 := by
  obtain ⟨a,ha,ha0,ham,rfl⟩ := hX
  obtain ⟨b,hb,hb0,hbm,rfl⟩ := hY
  have hfixA := oneParameter_fixed_of_generator_zero hU a ha hbd ha0 ham p hXp
  have hfixB := oneParameter_fixed_of_generator_zero hU b hb hbd hb0 hbm p hYp
  let A : ℝ → (Affine n →L[ℂ] Affine n) := fun t => (a t).derivativeAt p
  let B : ℝ → (Affine n →L[ℂ] Affine n) := fun t => (b t).derivativeAt p
  have hA0 : A 0=1 := by dsimp only [A]; rw [ha0,derivativeAt_one hU]
  have hB0 : B 0=1 := by dsimp only [B]; rw [hb0,derivativeAt_one hU]
  have hAm (s t : ℝ) : A (s+t)=A s*A t := by
    dsimp only [A]
    rw [ham,derivativeAt_mul hU,hfixA]
    rfl
  have hAd (t : ℝ) : HasDerivAt A ((fderiv ℂ (infinitesimalGenerator a) p.val)*A t) t := by
    have hd := oneParameter_derivativeAt_hasDerivAt hU hbd a ha ha0 ham t p
    rw [hfixA] at hd
    exact hd
  have hBd (t : ℝ) : HasDerivAt B ((Complex.I • fderiv ℂ (infinitesimalGenerator a) p.val)*B t) t := by
    have hd := oneParameter_derivativeAt_hasDerivAt hU hbd b hb hb0 hbm t p
    rw [hfixB,hrel] at hd
    exact hd
  have hbounded : Bornology.IsBounded (Set.range (fun z : ℂ => A z.re*B z.im)) := by
    apply ((compact_faithful_isotropy hU hc.isPreconnected hbd Γ hhol p).1.isBounded).subset
    rintro _ ⟨z,rfl⟩
    refine ⟨a z.re*b z.im,?_,?_⟩
    · change (a z.re).toHomeomorph ((b z.im).toHomeomorph p)=p
      rw [hfixB,hfixA]
    · change (a z.re*b z.im).derivativeAt p=A z.re*B z.im
      rw [derivativeAt_mul hU,hfixB]
      rfl
  have hz := bounded_complex_flow_generator_zero A B
    (fderiv ℂ (infinitesimalGenerator a) p.val) hA0 hB0 hAm hAd hBd hbounded
  exact IsCompleteGenerator.eq_zero_of_zero_jet hU hc hbd ⟨a,ha,ha0,ham,rfl⟩ p hXp hz
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ComplexTensorNormalForm
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
attribute [-simp] _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
namespace Release061
open Set Filter Topology
open scoped Classical
variable {n : ℕ}

theorem bracket_zero_firstJet_of_zero_secondJet
    {Z W : Affine n → Affine n} {p : Affine n}
    (hZ : AnalyticAt ℂ Z p) (hW : AnalyticAt ℂ W p)
    (hz0 : Z p=0) (hz1 : fderiv ℂ Z p=0)
    (hz2 : fderiv ℂ (fderiv ℂ Z) p=0) :
    VectorField.lieBracket ℂ Z W p=0 ∧ fderiv ℂ (VectorField.lieBracket ℂ Z W) p=0 := by
  refine ⟨?_,?_⟩
  · simp only [VectorField.lieBracket,hz0,hz1,map_zero,zero_apply,sub_zero]
  · have hA := hW.fderiv.differentiableAt.hasFDerivAt.clm_apply hZ.differentiableAt.hasFDerivAt
    have hB := hZ.fderiv.differentiableAt.hasFDerivAt.clm_apply hW.differentiableAt.hasFDerivAt
    have hder := hA.sub hB
    change fderiv ℂ ((fun y => (fderiv ℂ W y) (Z y)) - fun y => (fderiv ℂ Z y) (W y)) p=0
    rw [hder.fderiv]
    simp [hz0,hz1,hz2]

 theorem eq_I_smul_of_add_I_smul_eq_zero {E : Type*} [AddCommGroup E] [Module ℂ E]
    {x y : E} (h : x+Complex.I • y=0) : y=Complex.I • x := by
  have hh := congrArg (fun v => Complex.I • v) h
  simp only [smul_add,smul_smul,Complex.I_mul_I,neg_one_smul,smul_zero] at hh
  exact (eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hh)).symm

namespace Biholomorph
variable {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
include hU hc hbd Γ hhol

theorem complex_complete_generators_secondJet_zero
    {X Y : Affine n → Affine n} (hX : IsCompleteGenerator U X) (hY : IsCompleteGenerator U Y)
    (p : U) (hz0 : (X+Complex.I • Y) p.val=0)
    (hz1 : fderiv ℂ (X+Complex.I • Y) p.val=0)
    (hz2 : fderiv ℂ (fderiv ℂ (X+Complex.I • Y)) p.val=0) : X=0 ∧ Y=0 := by
  have haX := hX.analyticOnNhd hU hbd
  have haY := hY.analyticOnNhd hU hbd
  have haZ : AnalyticOnNhd ℂ (X+Complex.I • Y) U := fun x hx =>
    (haX x hx).add ((haY x hx).const_smul)
  have hbe : VectorField.lieBracket ℂ (X+Complex.I • Y) Y =ᶠ[𝓝 p.val]
      VectorField.lieBracket ℂ X Y := by
    filter_upwards [hU.mem_nhds p.property] with x hx
    rw [VectorField.lieBracket_add_left (haX x hx).differentiableAt
      ((haY x hx).differentiableAt.const_smul Complex.I),
      VectorField.lieBracket_const_smul_left (haY x hx).differentiableAt,
      VectorField.lieBracket_self,Pi.zero_apply,smul_zero,add_zero]
  obtain ⟨hbrp0,hbrp1⟩ := bracket_zero_firstJet_of_zero_secondJet (haZ p.val p.property)
    (haY p.val p.property) hz0 hz1 hz2
  rw [hbe.eq_of_nhds] at hbrp0
  rw [hbe.fderiv_eq] at hbrp1
  have hbr : VectorField.lieBracket ℂ X Y=0 :=
    (hX.lieBracket hU hc hbd Γ hhol hY).eq_zero_of_zero_jet hU hc hbd p hbrp0 hbrp1
  have hvalrel : Y p.val=Complex.I • X p.val := eq_I_smul_of_add_I_smul_eq_zero hz0
  have hderrel : fderiv ℂ Y p.val=Complex.I • fderiv ℂ X p.val := by
    rw [fderiv_add (haX p.val p.property).differentiableAt
      ((haY p.val p.property).differentiableAt.const_smul Complex.I),
      fderiv_const_smul (haY p.val p.property).differentiableAt] at hz1
    exact eq_I_smul_of_add_I_smul_eq_zero hz1
  have hXp : X p.val=0 := by
    obtain ⟨a,ha,ha0,ham,rfl⟩ := hX
    obtain ⟨b,hb,hb0,hbm,rfl⟩ := hY
    apply commuting_generators_value_zero hU hbd a b ha hb ha0 ham hb0 hbm _ p hvalrel
    funext x
    rw [VectorField.lieBracket_swap,hbr,Pi.zero_apply,neg_zero]
  have hYp : Y p.val=0 := by rw [hvalrel,hXp,smul_zero]
  have hx := isotropy_complete_generators_totally_real hU hc hbd Γ hhol hX hY p hXp hYp hderrel
  refine ⟨hx,hY.eq_zero_of_zero_jet hU hc hbd p hYp ?_⟩
  rw [hderrel,hx,fderiv_zero]
  change Complex.I • (0 : Affine n →L[ℂ] Affine n)=0
  exact smul_zero (A := Affine n →L[ℂ] Affine n) Complex.I
end Biholomorph
end Release061

open scoped TensorProduct
open Set Filter Topology

theorem complex_tensor_normalForm {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Z : ℂ ⊗[ℝ] V) : ∃ X Y : V, Z=1 ⊗ₜ[ℝ] X+Complex.I ⊗ₜ[ℝ] Y := by
  induction Z using OAI.tensorInductionOn with
  | tmul z X =>
    refine ⟨z.re • X,z.im • X,?_⟩
    rw [TensorProduct.tmul_smul,TensorProduct.tmul_smul,TensorProduct.smul_tmul',TensorProduct.smul_tmul',←TensorProduct.add_tmul]
    congr 1
    apply Complex.ext <;> simp [Complex.real_smul]
  | add Z W hZ hW =>
    obtain ⟨X,Y,rfl⟩ := hZ
    obtain ⟨X',Y',rfl⟩ := hW
    exact ⟨X+X',Y+Y',by simp only [TensorProduct.tmul_add]; abel⟩

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ImagPartLieReal
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
namespace Complexification
section Linear
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

@[simp] theorem realPart_I_smul (Z : ℂ ⊗[ℝ] V) : realPart (Complex.I • Z) = -imagPart Z := by
  obtain ⟨X,Y,rfl⟩ := complex_tensor_normalForm Z
  simp [smul_add,TensorProduct.smul_tmul']
@[simp] theorem imagPart_I_smul (Z : ℂ ⊗[ℝ] V) : imagPart (Complex.I • Z) = realPart Z := by
  obtain ⟨X,Y,rfl⟩ := complex_tensor_normalForm Z
  simp [smul_add,TensorProduct.smul_tmul']

@[simp] theorem realPart_real_smul (c : ℝ) (Z : ℂ ⊗[ℝ] V) :
    realPart ((c : ℂ) • Z)=c • realPart Z := by
  obtain ⟨X,Y,rfl⟩ := complex_tensor_normalForm Z
  simp [smul_add,TensorProduct.smul_tmul',Complex.mul_re]
@[simp] theorem imagPart_real_smul (c : ℝ) (Z : ℂ ⊗[ℝ] V) :
    imagPart ((c : ℂ) • Z)=c • imagPart Z := by
  obtain ⟨X,Y,rfl⟩ := complex_tensor_normalForm Z
  simp [smul_add,TensorProduct.smul_tmul',Complex.mul_im]

end Linear
variable {V : Type*} [LieRing V] [LieAlgebra ℝ V]

@[simp] theorem realPart_lie_ofReal (X : V) (Z : ℂ ⊗[ℝ] V) :
    realPart ⁅ofReal X,Z⁆=⁅X,realPart Z⁆ := by
  obtain ⟨Y,W,rfl⟩ := complex_tensor_normalForm Z
  simp [ofReal,LieRing.lie_add,LieAlgebra.ExtendScalars.bracket_tmul]
@[simp] theorem imagPart_lie_ofReal (X : V) (Z : ℂ ⊗[ℝ] V) :
    imagPart ⁅ofReal X,Z⁆=⁅X,imagPart Z⁆ := by
  obtain ⟨Y,W,rfl⟩ := complex_tensor_normalForm Z
  simp [ofReal,LieRing.lie_add,LieAlgebra.ExtendScalars.bracket_tmul]

end Complexification

open Filter Topology

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_Geometry
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
namespace LieFieldJets
variable {G E ι : Type*} [LieRing G] [LieAlgebra ℂ G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (F : G →ₗ[ℂ] (E → E)) (p : E) (hF : ∀ X, AnalyticAt ℂ (F X) p)
    (hjet : ∀ X, ZeroSecondJet (F X) p → X=0)
    (hlie : ∀ X Y, F ⁅X,Y⁆=VectorField.lieBracket ℂ (F X) (F Y))
    (b : Module.Basis ι ℂ E)

include hlie
 omit [CompleteSpace E] in
 theorem centered_bracket (L : G) (A : E →L[ℂ] E)
    (hL : F L =ᶠ[𝓝 p] fun x => A (x-p)) (X : G) :
    F ⁅L,X⁆ =ᶠ[𝓝 p] VectorField.lieBracket ℂ (fun x => A (x-p)) (F X) := by
  rw [hlie]
  filter_upwards [hL.eventually_nhds] with x hx
  have he : F L =ᶠ[𝓝 x] fun y => A (y-p) := hx
  simp only [VectorField.lieBracket,he.eq_of_nhds,he.fderiv_eq]

 theorem conjugated_diagonal (c : G ≃ₗ⁅ℂ⁆ G) (L : G) (A : E →L[ℂ] E)
    (hL : F (c L) =ᶠ[𝓝 p] fun x => A (x-p)) (w : ι → ℂ)
    (hA : ∀ i, A (b i)=w i • b i) :
    ∀ X j, analyticSecondJetCoordinates F p hF b (c ⁅L,X⁆) j=
      secondJetWeight w j*analyticSecondJetCoordinates F p hF b (c X) j := by
  intro X j
  rw [c.map_lie]
  exact analyticSecondJetCoordinates_euler F p hF b A w hA
    (LieAlgebra.ad ℂ G (c L))
    (fun X => centered_bracket F p hlie (c L) A hL X) (c X) j

end LieFieldJets

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_InnerExp
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
attribute [-simp] _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
namespace Release061
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

 theorem complexGeneratorField_analytic (Z : ComplexGenerators hU hc hbd Γ hhol) :
    AnalyticOnNhd ℂ (complexGeneratorField hU hc hbd Γ hhol Z) U := by
  obtain ⟨X,Y,rfl⟩ := complex_tensor_normalForm Z
  simp only [map_add,complexGeneratorField_tmul,one_smul]
  intro p hp
  exact (X.property.analyticOnNhd hU hbd p hp).add (Y.property.analyticOnNhd hU hbd p hp).const_smul

 theorem complexGeneratorField_zero_outside (Z : ComplexGenerators hU hc hbd Γ hhol)
    {x : Affine n} (hx : x∉U) : complexGeneratorField hU hc hbd Γ hhol Z x=0 := by
  obtain ⟨X,Y,rfl⟩ := complex_tensor_normalForm Z
  simp only [map_add,complexGeneratorField_tmul,one_smul,Pi.add_apply,Pi.smul_apply,
    X.property.eq_zero_of_not_mem hx,Y.property.eq_zero_of_not_mem hx,smul_zero,add_zero]

 theorem complexGeneratorField_secondJet_injective (Z : ComplexGenerators hU hc hbd Γ hhol)
    (p : U) (h0 : complexGeneratorField hU hc hbd Γ hhol Z p.val=0)
    (h1 : fderiv ℂ (complexGeneratorField hU hc hbd Γ hhol Z) p.val=0)
    (h2 : fderiv ℂ (fderiv ℂ (complexGeneratorField hU hc hbd Γ hhol Z)) p.val=0) : Z=0 := by
  obtain ⟨X,Y,rfl⟩ := complex_tensor_normalForm Z
  simp only [map_add,complexGeneratorField_tmul,one_smul] at h0 h1 h2
  obtain ⟨hX,hY⟩ := complex_complete_generators_secondJet_zero hU hc hbd Γ hhol
    X.property Y.property p h0 h1 h2
  have hx : X=0 := Subtype.ext hX
  have hy : Y=0 := Subtype.ext hY
  simp [hx,hy]

end Biholomorph
end Release061

open scoped TensorProduct
namespace LieAlgebra
open scoped _root_.LieAlgebra
variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

variable [LieAlgebra ℚ L]

 theorem innerExp_apply_of_square_zero (T : L) (hT : IsNilpotent (LieAlgebra.ad ℂ L T))
    (c : ℂ) (X : L) (hX : ⁅T,⁅T,X⁆⁆=0) : innerExp T hT c X=X+c • ⁅T,X⁆ := by
  let A := c • LieAlgebra.ad ℂ L T
  have hn : IsNilpotent A := hT.smul c
  have hs : (A^2) • X=0 := by
    change A (A X)=0
    simp [A,hX]
  change IsNilpotent.exp A X=_
  have he := IsNilpotent.exp_smul_eq_sum hs hn
  change IsNilpotent.exp A X= _ at he
  rw [he]
  simp [Finset.sum_range_succ,A,Module.End.smul_def]

 theorem innerExp_euler (T E : L) (hT : IsNilpotent (LieAlgebra.ad ℂ L T))
    (hTE : ⁅T,E⁆=T) (c : ℂ) : innerExp T hT c E=E+c • T := by
  rw [innerExp_apply_of_square_zero T hT c E (by rw [hTE,lie_self]),hTE]

 theorem innerExp_fixed (T : L) (hT : IsNilpotent (LieAlgebra.ad ℂ L T))
    (c : ℂ) (X : L) (hTX : ⁅T,X⁆=0) : innerExp T hT c X=X := by
  rw [innerExp_apply_of_square_zero T hT c X (by rw [hTX,lie_zero]),hTX,smul_zero,add_zero]

end LieAlgebra

open scoped TensorProduct

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ModelNormalTranslationAd
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
namespace Release061
open Set Filter Topology
namespace Biholomorph

section
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

theorem generator_ad_isNilpotent_of_scaled_flow
    (a : ℝ → Biholomorph U U) (ha : Continuous a) (ha0 : a 0=1)
    (ham : ∀ s t, a (s+t)=a s*a t)
    (hdil : ∀ r : ℝ, 0 < r → ∃ q : Biholomorph U U,
      ∀ t, q*a t*q⁻¹=a (r*t)) :
    IsNilpotent (LieAlgebra.ad ℝ (completeGeneratorSpace hU hc hbd Γ hhol)
      ⟨infinitesimalGenerator a,⟨a,ha,ha0,ham,rfl⟩⟩) := by
  let := finiteDimensional_completeGeneratorSpace hU hc hbd Γ hhol
  apply LieAlgebra.ad_isNilpotent_of_positive_dilations
  intro r hr
  obtain ⟨q,hq⟩ := hdil r hr
  refine ⟨generatorLieAdjoint hU hbd hc Γ hhol q,?_⟩
  apply Subtype.ext
  change pushForwardGenerator q (infinitesimalGenerator a)=r • infinitesimalGenerator a
  rw [←infinitesimalGenerator_conjugate hU hbd a ha ha0 ham q,
    show (fun t => q*a t*q⁻¹)=(fun t => a (r*t)) from funext hq]
  exact infinitesimalGenerator_time_smul hU hbd a ha ha0 ham r
end

 theorem flatWeightedScale_mem {r k : ℕ} (D : Set (Affine r × Affine k))
    (hd : ∀ t : ℝ, 0<t → ∀ p, (Real.sqrt t • p.1,t • p.2)∈D ↔ p∈D)
    {t : ℝ} (ht : 0<t) (x : Affine (r+k)) :
    flatWeightedScale ht x∈(affineProductCoordinates r k) '' D ↔
      x∈(affineProductCoordinates r k) '' D := by
  let e : (Affine r × Affine k) ≃L[ℂ] Affine (r+k) := affineProductCoordinates r k
  have hi (y : Affine (r+k)) : y∈e '' D ↔ e.symm y∈D := by
    constructor
    · rintro ⟨p,hp,rfl⟩; simpa only [e.symm_apply_apply] using hp
    · intro h; exact ⟨e.symm y,h,e.apply_symm_apply y⟩
  rw [hi,hi]
  change e.symm (e (weightedScaleCLE ht (e.symm x)))∈D ↔ _
  rw [e.symm_apply_apply]
  exact hd t ht (e.symm x)

 theorem flatWeightedScale_normal {r k : ℕ} {t : ℝ} (ht : 0<t) (a : Fin k → ℝ) :
    flatWeightedScale ht (flatNormalVector r k a)=t • flatNormalVector r k a := by
  let e : (Affine r × Affine k) ≃L[ℂ] Affine (r+k) := affineProductCoordinates r k
  change e (weightedScaleCLE ht (e.symm (e (0,fun i => (a i : ℂ)))) )=
    t • e (0,fun i => (a i : ℂ))
  rw [e.symm_apply_apply,←show e (t • (0,fun i => (a i : ℂ)))=
    t • e (0,fun i => (a i : ℂ)) from (e.toContinuousLinearMap.restrictScalars ℝ).map_smul t (0,fun i => (a i : ℂ))]
  congr 1
  simp only [weightedScaleCLE_apply,smul_zero,Prod.smul_mk]

theorem model_normal_translation_ad_nilpotent {r k n : ℕ}
    (D : Set (Affine r × Affine k))
    (htr : ∀ p : Affine r × Affine k, ∀ a : Fin k → ℝ,
      (p.1,fun i => p.2 i+(a i : ℂ)) ∈ D ↔ p∈D)
    (hd : ∀ t : ℝ, 0<t → ∀ p, (Real.sqrt t • p.1,t • p.2)∈D ↔ p∈D)
    {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    [LocallyCompactSpace ((affineProductCoordinates r k) '' D)]
    (e : Biholomorph ((affineProductCoordinates r k) '' D) U) (a : Fin k → ℝ) :
    ∃ b : ℝ → Biholomorph U U, Continuous b ∧ b 0=1 ∧
      (∀ s t, b (s+t)=b s*b t) ∧
      (∀ t, b t=autTransport e (translationAut (flatNormalVector r k a)
        (flatNormal_translation_mem D htr a) t)) ∧
      ∃ X : completeGeneratorSpace hU hc hbd Γ hhol,
        X.val=infinitesimalGenerator b ∧ IsNilpotent (LieAlgebra.ad ℝ _ X) := by
  let v := flatNormalVector r k a
  let hD := flatNormal_translation_mem D htr a
  let b : ℝ → Biholomorph U U := fun t => autTransport e (translationAut v hD t)
  have hb : Continuous b := (continuous_autTransport e).comp (continuous_translationAut v hD)
  have hb0 : b 0=1 := by simp [b]
  have hbm : ∀ s t, b (s+t)=b s*b t := by
    intro s t
    simp only [b,translationAut_add,autTransport_mul]
  refine ⟨b,hb,hb0,hbm,fun _ => rfl,⟨infinitesimalGenerator b,⟨b,hb,hb0,hbm,rfl⟩⟩,rfl,?_⟩
  apply generator_ad_isNilpotent_of_scaled_flow hU hc hbd Γ hhol b hb hb0 hbm
  intro t ht
  let L : Affine (r+k) ≃L[ℂ] Affine (r+k) := flatWeightedScale ht
  let hL := flatWeightedScale_mem D hd ht
  refine ⟨autTransport e (linearAut L hL),?_⟩
  intro s
  change autTransport e (linearAut L hL)*autTransport e (translationAut v hD s)*
    (autTransport e (linearAut L hL))⁻¹=autTransport e (translationAut v hD (t*s))
  rw [←autTransport_inv,←autTransport_mul,←autTransport_mul,
    linearAut_translation_conjugate v hD L hL t (flatWeightedScale_normal ht a)]

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FlatWeightedEuler
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
attribute [-simp] _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
namespace Release061
open Set Filter Topology
namespace Biholomorph

 theorem sqrt_exp_eq (t : ℝ) : Real.sqrt (Real.exp t)=Real.exp (t/2) := by
  rw [Real.sqrt_eq_iff_eq_sq (Real.exp_pos t).le (Real.exp_pos (t/2)).le,
    ←Real.exp_nat_mul]
  congr 1
  ring

 theorem flatWeightedScale_exp_apply {r k : ℕ} (t : ℝ) (x : Affine (r+k)) :
    flatWeightedScale (Real.exp_pos t) x=affineProductCoordinates r k
      (Real.exp (t/2) • ((affineProductCoordinates r k).symm x).1,
        Real.exp t • ((affineProductCoordinates r k).symm x).2) := by
  change affineProductCoordinates r k
    (Real.sqrt (Real.exp t) • ((affineProductCoordinates r k).symm x).1,
      Real.exp t • ((affineProductCoordinates r k).symm x).2)=_
  rw [sqrt_exp_eq]

 theorem hasDerivAt_flatWeightedScale_exp {r k : ℕ} (x : Affine (r+k)) :
    HasDerivAt (fun t : ℝ => flatWeightedScale (Real.exp_pos t) x)
      (flatWeightedEuler r k x) 0 := by
  let e := affineProductCoordinates r k
  have ha : HasDerivAt (fun t : ℝ => Real.exp (t/2)) (1/2) 0 := by
    convert (Real.hasDerivAt_exp (0/2)).comp 0 ((hasDerivAt_id (0 : ℝ)).div_const 2) using 1 <;> first | rfl | norm_num
  have hb : HasDerivAt Real.exp 1 0 := by simpa using Real.hasDerivAt_exp 0
  have hp := (ha.smul_const (e.symm x).1).prodMk (hb.smul_const (e.symm x).2)
  have hh := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := Affine r × Affine k)
    (E := Affine (r+k)) 0 (e.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt hp
  simp only [one_smul] at hh
  convert hh using 1 <;> try rfl
  · funext t
    exact flatWeightedScale_exp_apply t x
  · change e ((1/2 : ℂ) • (e.symm x).1,(e.symm x).2)=e ((1/2 : ℝ) • (e.symm x).1,(e.symm x).2)
    congr 2
    ext i
    simp [Complex.real_smul]

 theorem exists_actual_model_euler {r k n : ℕ}
    (D : Set (Affine r × Affine k))
    (hd : ∀ t : ℝ, 0<t → ∀ p, (Real.sqrt t • p.1,t • p.2)∈D ↔ p∈D)
    {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    [LocallyCompactSpace ((affineProductCoordinates r k) '' D)]
    (e : Biholomorph ((affineProductCoordinates r k) '' D) U) :
    ∃ E : completeGeneratorSpace hU hc hbd Γ hhol,
      coordinateField e.symm E.val=((affineProductCoordinates r k) '' D).indicator (flatWeightedEuler r k) := by
  apply exists_complete_linear_generator_in_model hU hc hbd Γ hhol e
    (fun t => flatWeightedScale (Real.exp_pos t))
    (fun t => flatWeightedScale_mem D hd (Real.exp_pos t))
  · intro x
    rw [flatWeightedScale_exp_apply]
    simp
  · intro s t x
    rw [flatWeightedScale_exp_apply (s+t),flatWeightedScale_exp_apply s,flatWeightedScale_exp_apply t]
    simp only [ContinuousLinearEquiv.symm_apply_apply,add_div,Real.exp_add,mul_smul]
  · simp_rw [flatWeightedScale_exp_apply]
    apply (affineProductCoordinates r k).continuous.comp
    exact ((Real.continuous_exp.comp (continuous_fst.div_const 2)).smul
      (continuous_fst.comp ((affineProductCoordinates r k).symm.continuous.comp continuous_snd))).prodMk
      ((Real.continuous_exp.comp continuous_fst).smul
        (continuous_snd.comp ((affineProductCoordinates r k).symm.continuous.comp continuous_snd)))
  · exact hasDerivAt_flatWeightedScale_exp

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ModelRotationWeight
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
attribute [-simp] _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
namespace Release061
namespace Biholomorph

 theorem flatWeightedEuler_basis (r k : ℕ) (i : ModelIndex r k) :
    flatWeightedEuler r k (modelBasis r k i)=modelEulerWeight i • modelBasis r k i := by
  rcases i with i|i <;>
    simp [modelBasis,flatWeightedEuler,modelEulerWeight,Module.Basis.prod_apply,
      ←map_smul]

 theorem flatTangentialInfinitesimal_basis (r k : ℕ) (i : ModelIndex r k) :
    flatTangentialInfinitesimal r k (modelBasis r k i)=modelRotationWeight i • modelBasis r k i := by
  rcases i with i|i <;>
    simp [modelBasis,flatTangentialInfinitesimal,modelRotationWeight,Module.Basis.prod_apply,
      ←map_smul]

 theorem flatTangentialInfinitesimal_normal {r k : ℕ} (a : Fin k → ℝ) :
    flatTangentialInfinitesimal r k (flatNormalVector r k a)=0 := by
  simp [flatTangentialInfinitesimal,flatNormalVector]

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_EulerSpectrum
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
namespace Release061.Biholomorph

namespace WeightedLieModel
variable {r k : ℕ} {G : Type*} [LieRing G] [LieAlgebra ℝ G]
    (M : WeightedLieModel r k G)

attribute [local instance] OAI.Release061.Biholomorph.WeightedLieModel.complexificationRatLieAlgebra
theorem center_euler : M.center M.E=M.E-Complex.I • M.T := by
  rw [center,LieAlgebra.innerExp_euler _ _ _ M.translation_euler]
  simp [sub_eq_add_neg]

theorem centered_euler_germ : M.field (M.center M.E) =ᶠ[𝓝 M.point]
    fun x => flatWeightedEuler r k (x-M.point) := by
  rw [M.center_euler,map_sub,map_smul]
  filter_upwards [M.euler_germ,M.translation_germ] with x hx hy
  simp only [Pi.sub_apply,Pi.smul_apply,hx,hy,map_sub,map_smul,point,flatWeightedEuler_normal]

end WeightedLieModel
end Release061.Biholomorph

open Filter Topology
open scoped TensorProduct

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FirstJetConstMul
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
include hU

theorem exists_firstJet_mul_const_strictFDeriv
    (p : U) (g : Biholomorph U U) (c : E → Biholomorph U U) (t₀ : E)
    (L : E →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n)))
    (hc : HasStrictFDerivAt (fun t => ambientFirstJet (g.toHomeomorph p) (c t)) L t₀) :
    ∃ L' : E →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n)),
      HasStrictFDerivAt (fun t => ambientFirstJet p (c t*g)) L' t₀ := by
  let B := (ContinuousLinearMap.compL ℂ (Affine n) (Affine n) (Affine n)).bilinearRestrictScalars ℝ
  have hB := (B.isBoundedBilinearMap.hasStrictFDerivAt
    ((c t₀).derivativeAt (g.toHomeomorph p),g.derivativeAt p)).comp t₀
    (hc.snd.prodMk (show HasStrictFDerivAt (fun _ : E => g.derivativeAt p)
      (0 : E →L[ℝ] (Affine n →L[ℂ] Affine n)) t₀ from hasStrictFDerivAt_const _ t₀))
  have hpair := hc.fst.prodMk hB
  have he : (fun t => ambientFirstJet p (c t*g)) =
      (fun t => ((c t).ambientAut (g.toHomeomorph p).val,
        ((c t).derivativeAt (g.toHomeomorph p)).comp (g.derivativeAt p))) := by
    funext t
    apply Prod.ext
    · simp only [ambientFirstJet,ambientAut_apply,mul_apply]
    · exact derivativeAt_mul hU (c t) g p
  rw [he]
  exact ⟨_,hpair⟩

theorem exists_firstJet_const_mul_strictFDeriv
    (p : U) (g : Biholomorph U U) (c : E → Biholomorph U U) (t₀ : E)
    (L : E →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n)))
    (hc : HasStrictFDerivAt (fun t => ambientFirstJet p (c t)) L t₀) :
    ∃ L' : E →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n)),
      HasStrictFDerivAt (fun t => ambientFirstJet p (g*c t)) L' t₀ := by
  have hy : (c t₀).ambientAut p.val∈U := by
    rw [ambientAut_apply]
    exact ((c t₀).toHomeomorph p).property
  have hA := ((g.ambientAut_analytic hU _ hy).hasStrictFDerivAt).restrictScalars ℝ
  have hD := ((g.ambientAut_analytic hU _ hy).fderiv.hasStrictFDerivAt).restrictScalars ℝ
  have hAv := hA.comp t₀ hc.fst
  have hDv := hD.comp t₀ hc.fst
  let B := (ContinuousLinearMap.compL ℂ (Affine n) (Affine n) (Affine n)).bilinearRestrictScalars ℝ
  have hB := (B.isBoundedBilinearMap.hasStrictFDerivAt
    (fderiv ℂ g.ambientAut ((c t₀).ambientAut p.val),(c t₀).derivativeAt p)).comp t₀ (hDv.prodMk hc.snd)
  have hpair := hAv.prodMk hB
  have he : (fun t => ambientFirstJet p (g*c t)) =
      (fun t => (g.ambientAut ((c t).ambientAut p.val),
        (fderiv ℂ g.ambientAut ((c t).ambientAut p.val)).comp ((c t).derivativeAt p))) := by
    funext t
    apply Prod.ext
    · simp only [ambientFirstJet,ambientAut_apply,mul_apply]
    · simpa only [ambientFirstJet,ambientAut_apply,derivativeAt] using derivativeAt_mul hU g (c t) p
  rw [he]
  exact ⟨_,hpair⟩
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ProjectedChartConjugationDifferential
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
include hU

theorem oneParameter_firstJet_hasDerivAt_zero (hbd : Bornology.IsBounded U)
    (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t) (p : U) :
    HasDerivAt (fun t => ambientFirstJet p (a t))
      (infinitesimalGenerator a p.val, fderiv ℂ (infinitesimalGenerator a) p.val) 0 := by
  have hv := oneParameter_hasDerivAt_zero hU a ha hbd ha0 ham p
  have hd := oneParameter_fderiv_hasDerivAt_zero hU hbd a ha ha0 ham p.val p.property
  simpa only [ambientFirstJet,ambientAut_apply,derivativeAt] using hv.prodMk hd

variable (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U)
include hU hc hbd Γ hhol

theorem projected_chart_conjugation_differential
    (P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ]
        LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p))
    (e : OpenPartialHomeomorph (Biholomorph U U)
        (LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p)))
    (he : (e : Biholomorph U U → _)=(fun a => P (ambientFirstJet p a)))
    (he1 : 1∈e.source)
    (hreg : ∀ p' : U, ∃ L : LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p) →L[ℝ]
        (Affine n × (Affine n →L[ℂ] Affine n)),
      HasStrictFDerivAt (𝕜 := ℝ) (E := LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p))
        (F := Affine n × (Affine n →L[ℂ] Affine n)) (fun t => ambientFirstJet p' (e.symm t)) L (e 1))
    (g : Biholomorph U U) :
    ∃ L : LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p) →L[ℝ]
        LinearMap.range (completeGeneratorFirstJet hU hc hbd Γ hhol p),
      HasStrictFDerivAt (𝕜 := ℝ) (fun t => e (g*e.symm t*g⁻¹)) L (e 1) ∧
      ∀ X : completeGeneratorSpace hU hc hbd Γ hhol,
        L (P (completeGeneratorFirstJet hU hc hbd Γ hhol p X))=
          P (completeGeneratorFirstJet hU hc hbd Γ hhol p (generatorAdjoint hU hc hbd Γ hhol g X)) := by
  let J := completeGeneratorFirstJet hU hc hbd Γ hhol p
  let R : Type := J.range
  let _ : NormedAddCommGroup R := Submodule.normedAddCommGroup _
  let _ : NormedSpace ℝ R := Submodule.normedSpace _
  obtain ⟨L0,hL0⟩ := hreg (g⁻¹.toHomeomorph p)
  obtain ⟨L1,hL1⟩ := exists_firstJet_mul_const_strictFDeriv (E := R) hU p g⁻¹ e.symm (e 1) L0 hL0
  obtain ⟨L2,hL2⟩ := exists_firstJet_const_mul_strictFDeriv (E := R) hU p g
    (fun t => e.symm t*g⁻¹) (e 1) L1 hL1
  have hPc := ContinuousLinearMap.hasStrictFDerivAt (𝕜 := ℝ)
    (E := Affine n × (Affine n →L[ℂ] Affine n)) (F := R)
    (x := ambientFirstJet p (g*(e.symm (e 1)*g⁻¹))) P
  have hproj := HasStrictFDerivAt.comp (𝕜 := ℝ) (E := R)
    (F := Affine n × (Affine n →L[ℂ] Affine n)) (G := R) (e 1) hPc hL2
  have hL : HasStrictFDerivAt (fun t => e (g*e.symm t*g⁻¹)) (P.comp L2) (e 1) := by
    simpa only [he,mul_assoc] using hproj
  refine ⟨P.comp L2,hL,?_⟩
  intro X
  obtain ⟨a,ha,ha0,ham,hgen⟩ := X.property
  have hja : HasDerivAt (fun s => ambientFirstJet p (a s)) (J X) 0 := by
    have hh := oneParameter_firstJet_hasDerivAt_zero hU hbd a ha ha0 ham p
    rw [hgen] at hh
    exact hh
  have hpa : HasDerivAt (fun s => e (a s)) (P (J X)) 0 := by
    have hp := (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ)
      (E := Affine n × (Affine n →L[ℂ] Affine n)) (F := R)
      (x := ambientFirstJet p (a 0)) P).comp_hasDerivAt 0 hja
    simpa only [Function.comp_def,he] using hp
  have hL' : HasFDerivAt (fun t : R => e (g*e.symm t*g⁻¹)) (P.comp L2) (e (a 0)) := by
    simpa only [ha0] using hL.hasFDerivAt
  have hchain := hL'.comp_hasDerivAt (0:ℝ) hpa
  have hasrc : ∀ᶠ s in 𝓝 (0:ℝ), a s∈e.source := by
    have ht : Tendsto a (𝓝 0) (𝓝 (1 : Biholomorph U U)) := by simpa only [ha0] using ha.continuousAt.tendsto (x := 0)
    exact ht (e.open_source.mem_nhds he1)
  have hconj : HasDerivAt (fun s => e (g*a s*g⁻¹)) ((P.comp L2) (P (J X))) 0 := by
    apply hchain.congr_of_eventuallyEq
    filter_upwards [hasrc] with s hs
    simp only [Function.comp_def,e.left_inv hs]
  have hca : Continuous (fun s => g*a s*g⁻¹) := (continuous_const.mul ha).mul continuous_const
  have hca0 : g*a 0*g⁻¹=1 := by simp only [ha0,mul_one,mul_inv_cancel]
  have hcam : ∀ s t, g*a (s+t)*g⁻¹=(g*a s*g⁻¹)*(g*a t*g⁻¹) := by
    intro s t
    rw [ham]
    group
  have hcj := oneParameter_firstJet_hasDerivAt_zero hU hbd (fun s => g*a s*g⁻¹) hca hca0 hcam p
  rw [infinitesimalGenerator_conjugate hU hbd a ha ha0 ham g,hgen] at hcj
  have hcj' : HasDerivAt (fun s => ambientFirstJet p (g*a s*g⁻¹))
      (J (generatorAdjoint hU hc hbd Γ hhol g X)) 0 := hcj
  have hpj := (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ)
      (E := Affine n × (Affine n →L[ℂ] Affine n)) (F := R)
      (x := ambientFirstJet p (g*a 0*g⁻¹)) P).comp_hasDerivAt 0 hcj'
  have hpj' : HasDerivAt (fun s => e (g*a s*g⁻¹))
      (P (J (generatorAdjoint hU hc hbd Γ hhol g X))) 0 := by simpa only [Function.comp_def,he] using hpj
  exact hconj.unique hpj'
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CompleteGeneratorTraceAd
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
attribute [-simp] _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set Filter Topology
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
include hU hc hbd Γ hhol

theorem generatorAdjoint_abs_det_one (g : Biholomorph U U) :
    |(generatorAdjoint hU hc hbd Γ hhol g).toLinearMap.det|=1 := by
  obtain ⟨p,hp⟩ := hc.nonempty
  let p : U := ⟨p,hp⟩
  let J := completeGeneratorFirstJet hU hc hbd Γ hhol p
  let R : Type := J.range
  let _ : NormedAddCommGroup R := Submodule.normedAddCommGroup _
  let _ : NormedSpace ℝ R := Submodule.normedSpace _
  obtain ⟨P,e,he,he1,hP,hreg,hdet⟩ := exists_actual_aut_chart_unimodular_jacobian hU hc hbd Γ hhol p
  have hreg' (p' : U) : ∃ L : R →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n)),
      HasStrictFDerivAt (fun t => ambientFirstJet p' (e.symm t)) L (e 1) :=
    ⟨_,(hreg p' (e 1) (e.map_source he1)).hasStrictFDerivAt (by simp)⟩
  obtain ⟨L,hL,hLX⟩ := projected_chart_conjugation_differential hU hc hbd Γ hhol p
    P e he he1 hreg' g
  let j : completeGeneratorSpace hU hc hbd Γ hhol ≃ₗ[ℝ] R :=
    LinearEquiv.ofInjective J (completeGeneratorFirstJet_injective hU hc hbd Γ hhol p)
  have hj (X : completeGeneratorSpace hU hc hbd Γ hhol) : P (J X)=j X := by
    apply Subtype.ext
    exact hP X
  have hconj : L.toLinearMap=j.toLinearMap ∘ₗ
      (generatorAdjoint hU hc hbd Γ hhol g).toLinearMap ∘ₗ j.symm.toLinearMap := by
    apply LinearMap.ext
    intro v
    obtain ⟨X,rfl⟩ := j.surjective v
    change L (j X)=j (generatorAdjoint hU hc hbd Γ hhol g (j.symm (j X)))
    rw [j.symm_apply_apply,←hj,←hj]
    exact hLX X
  have hd : L.det=(generatorAdjoint hU hc hbd Γ hhol g).toLinearMap.det := by
    change L.toLinearMap.det=_
    rw [hconj,LinearMap.det_conj]
  rw [←hd,←hL.hasFDerivAt.fderiv]
  exact hdet g

theorem completeGenerator_trace_ad_eq_zero
    (X : completeGeneratorSpace hU hc hbd Γ hhol) :
    LinearMap.trace ℝ (completeGeneratorSpace hU hc hbd Γ hhol)
      (LieAlgebra.ad ℝ (completeGeneratorSpace hU hc hbd Γ hhol) X)=0 := by
  classical
  let _ : FiniteDimensional ℝ (completeGeneratorSpace hU hc hbd Γ hhol) :=
    finiteDimensional_completeGeneratorSpace hU hc hbd Γ hhol
  let b := Module.finBasis ℝ (completeGeneratorSpace hU hc hbd Γ hhol)
  obtain ⟨a,ha,ha0,ham,hgen⟩ := X.property
  have hg : oneParameterGenerator hU hc hbd Γ hhol a ha ha0 ham=X := by
    apply Subtype.ext
    exact hgen
  have hdet (t : ℝ) : generatorDeterminant hU hc hbd Γ hhol b (a t)=1 := by
    have hh := generatorAdjoint_abs_det_one hU hc hbd Γ hhol (a t)
    have he : generatorDeterminant hU hc hbd Γ hhol b (a t)=
        (generatorAdjoint hU hc hbd Γ hhol (a t)).toLinearMap.det := by
      exact LinearMap.det_toMatrix b _
    rw [←he,abs_of_pos (generatorDeterminant_flow_pos hU hc hbd Γ hhol b a ham t)] at hh
    exact hh
  have hd := generatorDeterminant_hasDerivAt_zero hU hc hbd Γ hhol b a ha ha0 ham
  rw [hg] at hd
  have hzero := hd.unique (hasDerivAt_const (0 : ℝ) (1 : ℝ) |>.congr_of_eventuallyEq
    (Filter.Eventually.of_forall hdet))
  exact neg_eq_zero.mp hzero
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CoordinateFieldLinear
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
namespace Release061
open Set Filter Topology
namespace Biholomorph
open scoped Classical
variable {n m : ℕ} {U : Set (Affine n)} {D : Set (Affine m)}

 theorem coordinateField_analytic (hU : IsOpen U) (hD : IsOpen D)
    (e : Biholomorph U D) {X : Affine n → Affine n} (hX : AnalyticOnNhd ℂ X U) :
    AnalyticOnNhd ℂ (coordinateField e X) D := by
  apply analyticOnNhd_of_differentiableOn_affine hD
  intro x hx
  let p : D := ⟨x,hx⟩
  let y : U := e.toHomeomorph.symm p
  have hg : DifferentiableAt ℂ e.symm.ambientMap x :=
    (e.symm.ambientMap_analytic hD x hx).differentiableAt
  have he : e.symm.ambientMap x=y.val := ambientMap_apply e.symm p
  have hF := (e.ambientMap_analytic hU y.val y.property).fderiv.differentiableAt
  have hG := (hX y.val y.property).differentiableAt
  rw [←he] at hF hG
  have hh := (hF.comp x hg).clm_apply (hG.comp x hg)
  apply (hh.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [hD.mem_nhds hx] with z hz
  rw [coordinateField_apply e X ⟨z,hz⟩]
  simp only [Function.comp_def,ambientMap_apply e.symm ⟨z,hz⟩,mapDerivative]
  rfl

 theorem coordinateField_eq_pullback (hU : IsOpen U) (hD : IsOpen D)
    (e : Biholomorph U D) (X : Affine n → Affine n) (p : D) :
    coordinateField e X p.val=VectorField.pullback ℂ e.symm.ambientMap X p.val := by
  rw [VectorField.pullback_eq_of_fderiv_eq
    (M := mapDerivativeEquiv hD hU e.symm p) rfl]
  change coordinateField e X p.val=e.mapDerivative (e.toHomeomorph.symm p)
    (X (e.symm.ambientMap p.val))
  rw [ambientMap_apply,coordinateField_apply]
  rfl

 theorem coordinateField_lieBracket (hU : IsOpen U) (hD : IsOpen D)
    (e : Biholomorph U D) {X Y : Affine n → Affine n}
    (hX : AnalyticOnNhd ℂ X U) (hY : AnalyticOnNhd ℂ Y U) :
    coordinateField e (VectorField.lieBracket ℂ X Y)=
      VectorField.lieBracket ℂ (coordinateField e X) (coordinateField e Y) := by
  funext x
  by_cases hx : x∈D
  · have hXeq : coordinateField e X =ᶠ[𝓝 x] VectorField.pullback ℂ e.symm.ambientMap X := by
      filter_upwards [hD.mem_nhds hx] with z hz
      exact coordinateField_eq_pullback hU hD e X ⟨z,hz⟩
    have hYeq : coordinateField e Y =ᶠ[𝓝 x] VectorField.pullback ℂ e.symm.ambientMap Y := by
      filter_upwards [hD.mem_nhds hx] with z hz
      exact coordinateField_eq_pullback hU hD e Y ⟨z,hz⟩
    rw [coordinateField_eq_pullback hU hD e _ ⟨x,hx⟩,
      hXeq.lieBracket_vectorField_eq hYeq]
    apply VectorField.pullback_lieBracket (le_top : minSmoothness ℂ 2 ≤ ⊤)
      (e.symm.ambientMap_analytic hD x hx).contDiffAt
    · rw [ambientMap_apply e.symm ⟨x,hx⟩]
      exact (hX _ (e.toHomeomorph.symm ⟨x,hx⟩).property).differentiableAt
    · rw [ambientMap_apply e.symm ⟨x,hx⟩]
      exact (hY _ (e.toHomeomorph.symm ⟨x,hx⟩).property).differentiableAt
  · simp only [coordinateField,dite_eq_right hx,VectorField.lieBracket,map_zero,sub_zero]

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_Geometry2
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
attribute [-simp] _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set Filter Topology
namespace Biholomorph
variable {n m : ℕ} {U : Set (Affine n)} {D : Set (Affine m)}

 theorem coordinateField_value_zero_iff (hU : IsOpen U) (hD : IsOpen D)
    (e : Biholomorph U D) (X : Affine n → Affine n) (p : D) :
    coordinateField e X p.val=0 ↔ X (e.toHomeomorph.symm p).val=0 := by
  rw [coordinateField_apply]
  change mapDerivativeEquiv hU hD e (e.toHomeomorph.symm p) (X (e.toHomeomorph.symm p).val)=0 ↔ _
  exact (mapDerivativeEquiv hU hD e (e.toHomeomorph.symm p)).map_eq_zero_iff

 theorem coordinateField_fderiv_of_zero (hU : IsOpen U) (hD : IsOpen D)
    (e : Biholomorph U D) {X : Affine n → Affine n} (hX : AnalyticOnNhd ℂ X U)
    (p : D) (hp : X (e.toHomeomorph.symm p).val=0) :
    fderiv ℂ (coordinateField e X) p.val=
      (e.mapDerivative (e.toHomeomorph.symm p)).comp
        ((fderiv ℂ X (e.toHomeomorph.symm p).val).comp (e.symm.mapDerivative p)) := by
  let g := e.symm.ambientMap
  have hg : AnalyticAt ℂ g p.val := e.symm.ambientMap_analytic hD p.val p.property
  have he : g p.val=(e.toHomeomorph.symm p).val := ambientMap_apply e.symm p
  have hh : AnalyticAt ℂ e.ambientMap (g p.val) := by
    rw [he]; exact e.ambientMap_analytic hU _ (e.toHomeomorph.symm p).property
  have hx : AnalyticAt ℂ X (g p.val) := by
    rw [he]; exact hX _ (e.toHomeomorph.symm p).property
  have hz := (hh.fderiv.differentiableAt.hasFDerivAt.comp p.val hg.differentiableAt.hasFDerivAt).clm_apply
    (hx.differentiableAt.hasFDerivAt.comp p.val hg.differentiableAt.hasFDerivAt)
  have hf : coordinateField e X =ᶠ[𝓝 p.val] fun x => fderiv ℂ e.ambientMap (g x) (X (g x)) := by
    filter_upwards [hD.mem_nhds p.property] with x hx'
    rw [coordinateField_apply e X ⟨x,hx'⟩]
    simp only [g,ambientMap_apply e.symm ⟨x,hx'⟩,mapDerivative]
    rfl
  rw [hf.fderiv_eq]
  change fderiv ℂ (fun y => ((fderiv ℂ e.ambientMap ∘ g) y) ((X ∘ g) y)) p.val = _
  rw [hz.fderiv]
  ext v
  simp [he,hp,mapDerivative,g]

variable (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (hD : IsOpen D) (e : Biholomorph U D)
include hU hc hbd hD

variable (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U] [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
include Γ hhol
 theorem model_isotropy_totally_real {X Y : Affine n → Affine n}
    (hX : IsCompleteGenerator U X) (hY : IsCompleteGenerator U Y) (p : D)
    (hx : coordinateField e X p.val=0) (hy : coordinateField e Y p.val=0)
    (hrel : fderiv ℂ (coordinateField e Y) p.val=Complex.I • fderiv ℂ (coordinateField e X) p.val) : X=0 := by
  have hx0 := (coordinateField_value_zero_iff hU hD e X p).mp hx
  have hy0 := (coordinateField_value_zero_iff hU hD e Y p).mp hy
  apply isotropy_complete_generators_totally_real hU hc hbd Γ hhol hX hY (e.toHomeomorph.symm p) hx0 hy0
  rw [coordinateField_fderiv_of_zero hU hD e (hX.analyticOnNhd hU hbd) p hx0,
    coordinateField_fderiv_of_zero hU hD e (hY.analyticOnNhd hU hbd) p hy0] at hrel
  let A := mapDerivativeEquiv hU hD e (e.toHomeomorph.symm p)
  let B := mapDerivativeEquiv hD hU e.symm p
  apply ContinuousLinearMap.ext
  intro v
  have hz := congrArg (fun L : Affine m →L[ℂ] Affine m => L (B.symm v)) hrel
  change A (fderiv ℂ Y (e.toHomeomorph.symm p).val (B (B.symm v)))=
    Complex.I • A (fderiv ℂ X (e.toHomeomorph.symm p).val (B (B.symm v))) at hz
  rw [B.apply_symm_apply,←map_smul] at hz
  exact A.injective hz

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ModelComplexField
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set Filter Topology
open scoped TensorProduct
namespace Biholomorph

section
variable {n m : ℕ} {U : Set (Affine n)} {D : Set (Affine m)}

variable (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

 theorem complexGeneratorField_lie (Z W : ComplexGenerators hU hc hbd Γ hhol) :
    complexGeneratorField hU hc hbd Γ hhol ⁅Z,W⁆ =
      VectorField.lieBracket ℂ (complexGeneratorField hU hc hbd Γ hhol Z)
        (complexGeneratorField hU hc hbd Γ hhol W) := by
  let F := complexGeneratorField hU hc hbd Γ hhol
  funext x
  by_cases hx : x∈U
  · have hd (Y : ComplexGenerators hU hc hbd Γ hhol) : DifferentiableAt ℂ (F Y) x :=
      (complexGeneratorField_analytic hU hc hbd Γ hhol Y x hx).differentiableAt
    change F ⁅Z,W⁆ x=VectorField.lieBracket ℂ (F Z) (F W) x
    induction Z using OAI.tensorInductionOn with
    | tmul z X =>
      induction W using OAI.tensorInductionOn with
      | tmul w Y =>
        simp only [LieAlgebra.ExtendScalars.bracket_tmul,F,complexGeneratorField_tmul,Pi.smul_apply]
        rw [VectorField.lieBracket_const_smul_left (X.property.analyticOnNhd hU hbd x hx).differentiableAt,
          VectorField.lieBracket_const_smul_right (Y.property.analyticOnNhd hU hbd x hx).differentiableAt]
        exact mul_smul z w (VectorField.lieBracket ℂ X.val Y.val x)
      | add W₁ W₂ ih₁ ih₂ =>
        rw [LieRing.lie_add,map_add,Pi.add_apply,ih₁,ih₂,map_add,VectorField.lieBracket_add_right (hd W₁) (hd W₂)]
    | add Z₁ Z₂ ih₁ ih₂ =>
      rw [add_lie,map_add,Pi.add_apply,ih₁,ih₂,map_add,VectorField.lieBracket_add_left (hd Z₁) (hd Z₂)]
  · simp only [VectorField.lieBracket,complexGeneratorField_zero_outside hU hc hbd Γ hhol _ hx,
      map_zero,sub_zero]

end

open scoped Classical
variable {n m : ℕ} {U : Set (Affine n)} {D : Set (Affine m)}

 theorem coordinateField_zeroSecondJet (hU : IsOpen U) (hD : IsOpen D)
    (e : Biholomorph U D) {X : Affine n → Affine n} (hX : AnalyticOnNhd ℂ X U)
    (p : D) (hz : ZeroSecondJet X (e.toHomeomorph.symm p).val) :
    ZeroSecondJet (coordinateField e X) p.val := by
  let g := e.symm.ambientMap
  have hg : AnalyticAt ℂ g p.val := e.symm.ambientMap_analytic hD p.val p.property
  have he : g p.val=(e.toHomeomorph.symm p).val := ambientMap_apply e.symm p
  have hh : AnalyticAt ℂ e.ambientMap (g p.val) := by
    rw [he]; exact e.ambientMap_analytic hU _ (e.toHomeomorph.symm p).property
  have hx : AnalyticAt ℂ X (g p.val) := by
    rw [he]; exact hX _ (e.toHomeomorph.symm p).property
  rw [←he] at hz
  have hjet := ZeroSecondJet.clm_apply (hh.fderiv.comp hg) (hx.comp hg) (hz.comp hx hg)
  apply hjet.congr
  filter_upwards [hD.mem_nhds p.property] with x hx
  change (fderiv ℂ e.ambientMap (g x)) (X (g x))=coordinateField e X x
  rw [coordinateField_apply e X ⟨x,hx⟩]
  dsimp only [g]
  rw [ambientMap_apply e.symm ⟨x,hx⟩]
  rfl

variable (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

 theorem modelComplexField_analytic (hD : IsOpen D) (e : Biholomorph U D)
    (Z : ComplexGenerators hU hc hbd Γ hhol) :
    AnalyticOnNhd ℂ (modelComplexField hU hc hbd Γ hhol e Z) D :=
  coordinateField_analytic hU hD e (complexGeneratorField_analytic hU hc hbd Γ hhol Z)

 theorem modelComplexField_lie (hD : IsOpen D) (e : Biholomorph U D)
    (Z W : ComplexGenerators hU hc hbd Γ hhol) :
    modelComplexField hU hc hbd Γ hhol e ⁅Z,W⁆ =
      VectorField.lieBracket ℂ (modelComplexField hU hc hbd Γ hhol e Z)
        (modelComplexField hU hc hbd Γ hhol e W) := by
  change coordinateField e (complexGeneratorField hU hc hbd Γ hhol ⁅Z,W⁆)=_
  rw [complexGeneratorField_lie]
  exact coordinateField_lieBracket hU hD e
    (complexGeneratorField_analytic hU hc hbd Γ hhol Z)
    (complexGeneratorField_analytic hU hc hbd Γ hhol W)

 theorem modelComplexField_secondJet_injective (hD : IsOpen D) (e : Biholomorph U D)
    (Z : ComplexGenerators hU hc hbd Γ hhol) (p : D)
    (hz : ZeroSecondJet (modelComplexField hU hc hbd Γ hhol e Z) p.val) : Z=0 := by
  have hjet := coordinateField_zeroSecondJet hD hU e.symm
    (modelComplexField_analytic hU hc hbd Γ hhol hD e Z) (e.toHomeomorph.symm p)
    (by
      change ZeroSecondJet _ (e.toHomeomorph (e.toHomeomorph.symm p)).val
      rwa [e.toHomeomorph.apply_symm_apply])
  change ZeroSecondJet (coordinateField e.symm
    (coordinateField e (complexGeneratorField hU hc hbd Γ hhol Z))) _ at hjet
  rw [coordinateField_symm_cancel hU hD e _
    (fun x hx => complexGeneratorField_zero_outside hU hc hbd Γ hhol Z hx)] at hjet
  exact complexGeneratorField_secondJet_injective hU hc hbd Γ hhol Z
    (e.toHomeomorph.symm p) hjet.1 hjet.2.1 hjet.2.2

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_Geometry3
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
attribute [-simp] _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061.Biholomorph
open Set Filter Topology
open scoped TensorProduct
variable {n m : ℕ} {U : Set (Affine n)} {D : Set (Affine m)}
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U] [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

 theorem modelComplexField_ofReal (e : Biholomorph U D)
    (X : completeGeneratorSpace hU hc hbd Γ hhol) :
    modelComplexField hU hc hbd Γ hhol e (Complexification.ofReal X)=coordinateField e X.val := by
  simp only [modelComplexField, LinearMap.comp_apply, Complexification.ofReal_apply,
    complexGeneratorField_tmul, one_smul]
  rfl

 theorem exists_actual_weightedLieModel {r k : ℕ} (D : Set (Affine r × Affine k))
    (hDo : IsOpen D)
    (htr : ∀ p : Affine r × Affine k, ∀ a : Fin k → ℝ,
      (p.1,fun i => p.2 i+(a i : ℂ)) ∈ D ↔ p∈D)
    (hd : ∀ t : ℝ, 0<t → ∀ p, (Real.sqrt t • p.1,t • p.2)∈D ↔ p∈D)
    (hr : ∀ c : ℂ, ‖c‖=1 → ∀ p, (c • p.1,p.2)∈D ↔ p∈D)
    [LocallyCompactSpace ((affineProductCoordinates r k) '' D)]
    (e : Biholomorph ((affineProductCoordinates r k) '' D) U)
    (a : Fin k → ℝ) (ha : (0,fun i => Complex.I*(a i : ℂ))∈D) :
    ∃ M : WeightedLieModel r k (completeGeneratorSpace hU hc hbd Γ hhol),
      M.normal=a ∧ M.field=modelComplexField hU hc hbd Γ hhol e.symm := by
  let S := (affineProductCoordinates r k) '' D
  have hS : IsOpen S := (affineProductCoordinates r k).isOpenMap _ hDo
  have hpa : Complex.I • flatNormalVector r k a∈S := by
    have he : Complex.I • flatNormalVector r k a=
        affineProductCoordinates r k (0,fun i => Complex.I*(a i : ℂ)) := by
      rw [flatNormalVector,←map_smul]
      congr 1
      ext i <;> simp
    rw [he]
    exact ⟨_,ha,rfl⟩
  let p : S := ⟨_,hpa⟩
  obtain ⟨E,hE⟩ := exists_actual_model_euler D hd hU hc hbd Γ hhol e
  obtain ⟨H,hH⟩ := exists_actual_model_rotation D hr hU hc hbd Γ hhol e
  obtain ⟨b,hb,hb0,hbm,hbe,T,hT,hnil⟩ := model_normal_translation_ad_nilpotent D htr hd hU hc hbd Γ hhol e a
  have hTf : coordinateField e.symm T.val=S.indicator (fun _ => flatNormalVector r k a) := by
    rw [hT,funext hbe]
    exact transported_translation_generator_in_model hU hbd e _ _
  let F := modelComplexField hU hc hbd Γ hhol e.symm
  have hF (X : completeGeneratorSpace hU hc hbd Γ hhol) :
      F (Complexification.ofReal X)=coordinateField e.symm X.val :=
    modelComplexField_ofReal hU hc hbd Γ hhol e.symm X
  refine ⟨{
    field := F
    normal := a
    euler := E
    translation := T
    rotation := H
    analytic := fun X => modelComplexField_analytic hU hc hbd Γ hhol hS e.symm X _ hpa
    jet_injective := fun X hz => modelComplexField_secondJet_injective hU hc hbd Γ hhol hS e.symm X p hz
    lie := modelComplexField_lie hU hc hbd Γ hhol hS e.symm
    euler_germ := ?_
    translation_germ := ?_
    rotation_germ := ?_
    nilpotent := hnil
    isotropy_real := ?_
  },rfl,rfl⟩
  · rw [hF,hE]
    filter_upwards [hS.mem_nhds hpa] with x hx
    exact Set.indicator_of_mem hx _
  · rw [hF,hTf]
    filter_upwards [hS.mem_nhds hpa] with x hx
    exact Set.indicator_of_mem hx _
  · rw [hF,hH]
    filter_upwards [hS.mem_nhds hpa] with x hx
    exact Set.indicator_of_mem hx _
  · intro X Y hx hy hrel
    simp only [hF] at hx hy hrel
    apply Subtype.ext
    exact model_isotropy_totally_real hU hc hbd hS e.symm Γ hhol X.property Y.property p hx hy hrel

end Release061.Biholomorph

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_HeisenbergShiftAxis
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Hermitian
open Set Complex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] {k : ℕ}

omit [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] in

theorem heisenbergShift_residual
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (a : E) (p : E × (Fin k → ℂ)) :
    (fun i => ((heisenbergShift B a p).2 i).im -
      hermQuadratic B (heisenbergShift B a p).1 i) =
      (fun i => (p.2 i).im - hermQuadratic B p.1 i) := by
  funext i
  have hc := congrArg re (hermPart_conj (symmetrize (B i)) (symmetrize_symm (B i)) p.1 a)
  simp only [star_def,conj_re] at hc
  simp only [heisenbergShift,hermQuadratic,hermPart_add_left,hermPart_add_right,
    add_re,add_im,mul_re,mul_im,I_re,I_im,ofReal_re,ofReal_im]
  norm_num only [show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl]
  rw [hc]
  ring

omit [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] in
lemma heisenbergShift_mem
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (C : Set (Fin k → ℝ)) (a : E)
    (p : E × (Fin k → ℂ)) :
    heisenbergShift B a p ∈ quadraticDomain (hermQuadratic B) C ↔
      p ∈ quadraticDomain (hermQuadratic B) C := by
  change (fun i => ((heisenbergShift B a p).2 i).im -
    hermQuadratic B (heisenbergShift B a p).1 i) ∈ C ↔ _
  rw [heisenbergShift_residual]
  rfl

omit [FiniteDimensional ℂ E] in

theorem heisenbergShift_axis
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : E × (Fin k → ℂ)) :
    heisenbergShift B (-p.1) p =
      (0,fun i => p.2 i - I*(hermQuadratic B p.1 i : ℂ)) := by
  apply Prod.ext
  · simp [heisenbergShift]
  · funext i
    have hQ : hermQuadratic B (-p.1) = hermQuadratic B p.1 := by
      simpa using hermQuadratic_real_smul B (-1) p.1
    have hdiag : hermPart (symmetrize (B i)) p.1 p.1 =
        (hermQuadratic B p.1 i : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using hermPart_diag_real (symmetrize (B i)) (symmetrize_symm (B i)) p.1
    simp only [heisenbergShift,hermPart_neg_right,hQ]
    rw [hdiag]
    ring

end Release061.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_InvolutionDerivativeNegId
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter Topology
open scoped Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem involution_derivative_neg_id {f : E → E} {p : E} {A : E →L[ℂ] E}
    (hf : HasStrictFDerivAt f A p) (hp : f p=p)
    (hinv : ∀ᶠ x in 𝓝 p, f (f x)=x)
    (hiso : ∀ᶠ x in 𝓝 p, f x=x → x=p) : A = -1 := by
  have hff : HasFDerivAt (f ∘ f) (A.comp A) p := by
    have hh : HasFDerivAt f A (f p) := hp.symm ▸ hf.hasFDerivAt
    exact hh.comp p hf.hasFDerivAt
  have hA2 : A.comp A=1 := by
    have heq : (f ∘ f) =ᶠ[𝓝 p] id := hinv
    exact hff.unique ((hasFDerivAt_id p).congr_of_eventuallyEq heq)
  have hAA (x : E) : A (A x)=x := congrArg (fun L : E →L[ℂ] E => L x) hA2
  let φ : E → E := fun x => (1/2 : ℂ) • ((x-p)+A (f x-p))
  have hφp : φ p=0 := by simp [φ,hp]
  have hφder : HasStrictFDerivAt φ ((ContinuousLinearEquiv.refl ℂ E) : E →L[ℂ] E) p := by
    have hh := (((hasStrictFDerivAt_id p).sub_const p).add
      (A.hasStrictFDerivAt.comp p (hf.sub_const p))).const_smul (1/2 : ℂ)
    convert hh using 1
    · rfl
    · change (1 : E →L[ℂ] E)=(1/2 : ℂ) • (1+A.comp A)
      rw [hA2]
      module
  have hcomm : ∀ᶠ x in 𝓝 p, φ (f x)=A (φ x) := by
    filter_upwards [hinv] with x hx
    simp only [φ,hx,map_smul,map_add,hAA]
    congr 1
    abel
  let ψ := hφder.localInverse φ (ContinuousLinearEquiv.refl ℂ E) p
  have hψ : Tendsto ψ (𝓝 0) (𝓝 p) := by
    simpa only [hφp] using hφder.localInverse_tendsto
  have hright : ∀ᶠ y in 𝓝 0, φ (ψ y)=y := by
    simpa only [hφp] using hφder.eventually_right_inverse
  have hleft : ∀ᶠ x in 𝓝 p, ψ (φ x)=x := hφder.eventually_left_inverse
  have hfc : Tendsto f (𝓝 p) (𝓝 p) := by simpa only [hp] using hf.continuousAt.tendsto
  have hleftf : ∀ᶠ x in 𝓝 p, ψ (φ (f x))=f x := hfc hleft
  have hzero : ∀ᶠ y in 𝓝 0, A y=y → y=0 := by
    filter_upwards [hright,hψ (hleftf.and (hcomm.and hiso))] with y hy hq hfix
    obtain ⟨hfl,hc,hi⟩ := hq
    have hfy : f (ψ y)=ψ y := by
      rw [hc,hy,hfix] at hfl
      exact hfl.symm
    have hqy := hi hfy
    rw [hqy,hφp] at hy
    exact hy.symm
  have hfixed : ∀ v : E, A v=v → v=0 := by
    intro v hv
    have ht : Tendsto (fun t : ℂ => t • v) (𝓝 0) (𝓝 0) := by
      have hcont : Continuous (fun t : ℂ => t • v) := by fun_prop
      simpa only [zero_smul] using hcont.tendsto (0 : ℂ)
    have he : ∀ᶠ t : ℂ in 𝓝 0, t • v=0 := by
      filter_upwards [ht hzero] with t ht'
      exact ht' (by simp only [map_smul,hv])
    have he' := he.filter_mono (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0)
    obtain ⟨t,ht,hne⟩ := (he'.and self_mem_nhdsWithin).exists
    exact (smul_eq_zero.mp ht).resolve_left (by simpa using hne)
  ext v
  have hh := hfixed (A v+v) (by simp only [map_add,hAA]; abel)
  simpa using eq_neg_of_add_eq_zero_left hh

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PointSymmetryNegId
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem isolated_fixedPoint_of_neg_id [CompleteSpace E]
    {f : E → E} {p : E} (hf : AnalyticAt ℂ f p) (hp : f p = p)
    (hd : HasFDerivAt f (-1 : E →L[ℂ] E) p) :
    ∀ᶠ x in 𝓝 p, f x = x → x = p := by
  let g : E → E := fun x => (1/2 : ℂ) • (x-f x)
  have hg : AnalyticAt ℂ g p := (analyticAt_id.sub hf).const_smul
  have hgder : HasFDerivAt g (1 : E →L[ℂ] E) p := by
    have hh := ((hasFDerivAt_id p).sub hd).const_smul (1/2 : ℂ)
    convert hh using 1
    · rfl
    · change (1 : E →L[ℂ] E) = (1/2 : ℂ) • (1-(-1))
      module
  have hs : HasStrictFDerivAt g ((ContinuousLinearEquiv.refl ℂ E) : E →L[ℂ] E) p := by
    simpa only [hgder.fderiv,ContinuousLinearEquiv.coe_refl,ContinuousLinearMap.one_def]
      using hg.hasStrictFDerivAt
  have hleft := hs.eventually_left_inverse
  have hp' := hs.localInverse_apply_image
  filter_upwards [hleft] with x hx hfx
  have he : g x = g p := by simp [g,hfx,hp]
  rw [he] at hx
  exact hx.symm.trans hp'

theorem cartan_involution_of_neg_id [ProperSpace E] [SecondCountableTopology E]
    {S : Set E} (hS : IsOpen S) (hconn : IsPreconnected S)
    (hb : Bornology.IsBounded S) {f : E → E}
    (hf : AnalyticOnNhd ℂ f S) (hm : MapsTo f S S)
    {p : E} (hp : p ∈ S) (hfix : f p = p)
    (hd : HasFDerivAt f (-1 : E →L[ℂ] E) p) :
    (∀ x ∈ S, f (f x) = x) ∧ ∀ᶠ x in 𝓝 p, f x = x → x = p := by
  refine ⟨?_,isolated_fixedPoint_of_neg_id (hf p hp) hfix hd⟩
  have hdf : HasFDerivAt f (-1 : E →L[ℂ] E) (f p) := hfix.symm ▸ hd
  have hdd : HasFDerivAt (f ∘ f) (1 : E →L[ℂ] E) p := by
    have hh := hdf.comp p hd
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp
  have hff : (f ∘ f) p = p := by simp [hfix]
  exact cartan_uniqueness_bounded hS hconn hb (hf.comp hf hm) (hm.comp hm) hp hff hdd

end

open Set Filter Metric
open scoped Topology

theorem Biholomorph.pointSymmetry_of_neg_id {n : ℕ} {S : Set (Affine n)}
    (hS : IsOpen S) (hconn : IsPreconnected S) (hb : Bornology.IsBounded S)
    (σ : Biholomorph S S) (p : S) (hfix : σ.toHomeomorph p = p)
    (hd : HasFDerivAt (ambientExtend (fun x => (σ.toHomeomorph x).val))
      (-1 : Affine n →L[ℂ] Affine n) p.val) :
    Function.Involutive σ.toHomeomorph ∧ σ.toHomeomorph p = p ∧
      ∃ W : Set S, IsOpen W ∧ p ∈ W ∧
        ∀ q ∈ W, σ.toHomeomorph q = q → q = p := by
  let f := ambientExtend (fun x => (σ.toHomeomorph x).val)
  have hf : AnalyticOnNhd ℂ f S := σ.holomorphic_toFun.analyticOnNhd_extend hS
  have hm : MapsTo f S S := by
    intro x hx
    rw [show f x = (σ.toHomeomorph ⟨x,hx⟩).val from ambientExtend_apply _ ⟨x,hx⟩]
    exact (σ.toHomeomorph ⟨x,hx⟩).property
  have hfp : f p.val = p.val := by
    rw [show f p.val = (σ.toHomeomorph p).val from ambientExtend_apply _ p,hfix]
  obtain ⟨hi,hiso⟩ := cartan_involution_of_neg_id hS hconn hb hf hm p.property hfp hd
  refine ⟨?_,hfix,?_⟩
  · intro q
    apply Subtype.ext
    have hh := hi q q.property
    rw [show f q.val = (σ.toHomeomorph q).val from ambientExtend_apply _ q] at hh
    rw [show f (σ.toHomeomorph q).val = (σ.toHomeomorph (σ.toHomeomorph q)).val
      from ambientExtend_apply _ _] at hh
    exact hh
  · obtain ⟨r,hr,hWsub⟩ := Metric.mem_nhds_iff.mp hiso
    refine ⟨(Subtype.val : S → Affine n) ⁻¹' ball p.val r,
      isOpen_ball.preimage continuous_subtype_val,mem_ball_self hr,?_⟩
    intro q hq hqfix
    apply Subtype.ext
    apply hWsub hq
    rw [show f q.val = (σ.toHomeomorph q).val from ambientExtend_apply _ q,hqfix]

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_IsotropyRepresentationUnitsCompact
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

namespace Biholomorph

section
open Set Filter Topology
variable {n : ℕ} {U : Set (Affine n)}

theorem negative_derivative_of_pointSymmetry (hU : IsOpen U)
    (a : Biholomorph U U) (p : U)
    (hi : Function.Involutive a.toHomeomorph) (hfix : a.toHomeomorph p=p)
    (his : ∃ W : Set U, IsOpen W ∧ p ∈ W ∧ ∀ q ∈ W, a.toHomeomorph q=q → q=p) :
    a.derivativeAt p = -1 := by
  apply involution_derivative_neg_id ((a.ambientAut_analytic hU _ p.property).hasStrictFDerivAt)
    (by simpa only [ambientAut_apply] using congrArg Subtype.val hfix)
  · filter_upwards [hU.mem_nhds p.property] with x hx
    rw [ambientAut_apply a ⟨x,hx⟩,ambientAut_apply a (a.toHomeomorph ⟨x,hx⟩),hi]
  · obtain ⟨W,hW,hp,hiso⟩ := his
    filter_upwards [(hU.isOpenMap_subtype_val W hW).mem_nhds ⟨p,hp,rfl⟩] with x hx hf
    obtain ⟨q,hq,rfl⟩ := hx
    have he : a.toHomeomorph q=q := Subtype.ext (by simpa only [ambientAut_apply] using hf)
    exact congrArg Subtype.val (hiso q hq he)

theorem boundedSymmetricDomain_iff_negative_isotropy (hU : IsOpen U)
    (hc : IsConnected U) (hb : Bornology.IsBounded U) :
    IsBoundedSymmetricDomain U ↔
      ∀ p : U, (-1 : Affine n →L[ℂ] Affine n) ∈
        (fun a : Biholomorph U U => a.derivativeAt p) '' {a | a.toHomeomorph p=p} := by
  constructor
  · intro h p
    obtain ⟨a,hi,hfix,his⟩ := h.2.2.2 p
    exact ⟨a,hfix,negative_derivative_of_pointSymmetry hU a p hi hfix his⟩
  · intro h
    refine ⟨hU,hc,hb,?_⟩
    intro p
    obtain ⟨a,hfix,hd⟩ := h p
    refine ⟨a,?_⟩
    apply a.pointSymmetry_of_neg_id hU hc.isPreconnected hb p hfix
    have hh := (a.ambientAut_analytic hU _ p.property).differentiableAt.hasFDerivAt
    change a.derivativeAt p = -1 at hd
    rwa [← derivativeAt,hd] at hh

end

open Set Filter Topology TopologicalSpace

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_IsotropyCentralShiftZero
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set Filter Topology

 theorem bounded_rotated_flow_generator_zero {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (a q : ℝ → A) (d : A) (c : ℝ)
    (ha0 : a 0=1) (hq0 : q 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    (hda : ∀ t, HasDerivAt a (d*a t) t)
    (hdq : ∀ t, HasDerivAt q ((Complex.I • ((c : ℂ) • (1 : A)-d))*q t) t)
    (hbd : Bornology.IsBounded (Set.range (fun z : ℂ => a z.re*q z.im))) : d=0 := by
  let s : ℝ → ℂ := fun t => Complex.exp (((c*t : ℝ) : ℂ)*Complex.I)
  let b : ℝ → A := fun t => s t • q (-t)
  have hs0 : s 0=1 := by simp [s]
  have hsn (t : ℝ) : ‖s t‖=1 := Complex.norm_exp_ofReal_mul_I (c*t)
  have hsd (t : ℝ) : HasDerivAt s (((c : ℂ)*Complex.I)*s t) t := by
    have h : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
      convert Complex.ofRealCLM.hasDerivAt using 1 <;> rfl
    convert ((h.const_mul (c : ℂ)).mul_const Complex.I).cexp using 1 <;>
      simp [s,Complex.ofReal_mul,mul_comm]
  have hdb (t : ℝ) : HasDerivAt b ((Complex.I • d)*b t) t := by
    have hq := (hdq (-t)).scomp t (hasDerivAt_neg t)
    have hb := (hsd t).smul hq
    change HasDerivAt b _ t at hb
    have he : s t • (- (Complex.I • ((c : ℂ) • (1 : A)-d)*q (-t))) +
        ((c : ℂ)*Complex.I*s t) • q (-t) = (Complex.I • d)*b t := by
      simp only [b, smul_mul_assoc, mul_smul_comm, one_mul, smul_sub, smul_smul,
        smul_neg, sub_mul]
      module
    rw [neg_one_smul] at hb
    exact he ▸ hb
  apply bounded_complex_flow_generator_zero a b d ha0 (by simp [b,hs0,hq0]) ham hda hdb
  obtain ⟨C,hC⟩ := (isBounded_iff_forall_norm_le.mp hbd)
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C,?_⟩
  rintro x ⟨z,rfl⟩
  change ‖a z.re*b z.im‖ ≤ C
  rw [show a z.re*b z.im=s z.im • (a z.re*q (-z.im)) by simp [b],norm_smul,hsn,one_mul]
  exact hC _ ⟨star z,by simp⟩

namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
include hU hc hbd Γ hhol

theorem isotropy_central_shift_zero {X Y : Affine n → Affine n}
    (hX : IsCompleteGenerator U X) (hY : IsCompleteGenerator U Y) (p : U) (c : ℝ)
    (hXp : X p.val=0) (hYp : Y p.val=0)
    (hrel : fderiv ℂ Y p.val=Complex.I • ((c : ℂ) • (1 : Affine n →L[ℂ] Affine n)-fderiv ℂ X p.val)) : X=0 := by
  obtain ⟨a,ha,ha0,ham,rfl⟩ := hX
  obtain ⟨q,hq,hq0,hqm,rfl⟩ := hY
  have hfixA := oneParameter_fixed_of_generator_zero hU a ha hbd ha0 ham p hXp
  have hfixQ := oneParameter_fixed_of_generator_zero hU q hq hbd hq0 hqm p hYp
  let A : ℝ → (Affine n →L[ℂ] Affine n) := fun t => (a t).derivativeAt p
  let Q : ℝ → (Affine n →L[ℂ] Affine n) := fun t => (q t).derivativeAt p
  have hA0 : A 0=1 := by dsimp only [A]; rw [ha0,derivativeAt_one hU]
  have hQ0 : Q 0=1 := by dsimp only [Q]; rw [hq0,derivativeAt_one hU]
  have hAm (s t : ℝ) : A (s+t)=A s*A t := by
    dsimp only [A]
    rw [ham,derivativeAt_mul hU,hfixA]
    rfl
  have hAd (t : ℝ) : HasDerivAt A ((fderiv ℂ (infinitesimalGenerator a) p.val)*A t) t := by
    have hd := oneParameter_derivativeAt_hasDerivAt hU hbd a ha ha0 ham t p
    rw [hfixA] at hd
    exact hd
  have hQd (t : ℝ) : HasDerivAt Q
      ((Complex.I • ((c : ℂ) • (1 : Affine n →L[ℂ] Affine n)-fderiv ℂ (infinitesimalGenerator a) p.val))*Q t) t := by
    have hd := oneParameter_derivativeAt_hasDerivAt hU hbd q hq hq0 hqm t p
    rw [hfixQ,hrel] at hd
    exact hd
  have hbounded : Bornology.IsBounded (Set.range (fun z : ℂ => A z.re*Q z.im)) := by
    apply ((compact_faithful_isotropy hU hc.isPreconnected hbd Γ hhol p).1.isBounded).subset
    rintro _ ⟨z,rfl⟩
    refine ⟨a z.re*q z.im,?_,?_⟩
    · change (a z.re).toHomeomorph ((q z.im).toHomeomorph p)=p
      rw [hfixQ,hfixA]
    · change (a z.re*q z.im).derivativeAt p=A z.re*Q z.im
      rw [derivativeAt_mul hU,hfixQ]
      rfl
  have hz := bounded_rotated_flow_generator_zero A Q
    (fderiv ℂ (infinitesimalGenerator a) p.val) c hA0 hQ0 hAm hAd hQd hbounded
  exact IsCompleteGenerator.eq_zero_of_zero_jet hU hc hbd ⟨a,ha,ha0,ham,rfl⟩ p hXp hz

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ModelIsotropyCentralShift
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set Filter Topology

theorem scalar_linear_ode {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (c : ℂ) (hd : ∀ t, HasDerivAt f (c • f t) t) (t : ℝ) :
    f t=Complex.exp ((t : ℂ)*c) • f 0 := by
  let s : ℝ → ℂ := fun t => Complex.exp (-((t : ℂ)*c))
  have hs (u : ℝ) : HasDerivAt s ((-c)*s u) u := by
    have hu : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 u := by
      convert Complex.ofRealCLM.hasDerivAt using 1 <;> rfl
    convert ((hu.mul_const c).neg).cexp using 1
    all_goals try with_reducible_and_instances rfl
    simp [s,mul_comm]
  have hd0 (u : ℝ) : HasDerivAt (fun u => s u • f u) 0 u := by
    have hh := (hs u).smul (hd u)
    have he : s u • (c • f u)+(-c*s u) • f u=0 := by
      rw [smul_smul,neg_mul,neg_smul,←sub_eq_add_neg,mul_comm]
      exact sub_self _
    exact he ▸ hh
  have hconst := is_const_of_deriv_eq_zero (fun u => (hd0 u).differentiableAt)
    (fun u => (hd0 u).deriv) t 0
  have hz : s t • f t=f 0 := by simpa [s] using hconst
  have hh := congrArg (fun v => Complex.exp ((t : ℂ)*c) • v) hz
  simpa only [s,smul_smul,←Complex.exp_add,add_neg_cancel,Complex.exp_zero,one_smul] using hh

namespace Biholomorph

section
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U)
include hU hbd

theorem negative_isotropy_of_scalar_generator {X : Affine n → Affine n}
    (hX : IsCompleteGenerator U X) (p : U) (hp : X p.val=0)
    (hd : fderiv ℂ X p.val=(2*Complex.I) • (1 : Affine n →L[ℂ] Affine n)) :
    ∃ a : Biholomorph U U, a.toHomeomorph p=p ∧ a.derivativeAt p= -1 := by
  obtain ⟨a,ha,ha0,ham,rfl⟩ := hX
  have hfix := oneParameter_fixed_of_generator_zero hU a ha hbd ha0 ham p hp
  let A : ℝ → (Affine n →L[ℂ] Affine n) := fun t => (a t).derivativeAt p
  have hAd (t : ℝ) : HasDerivAt A ((2*Complex.I) • A t) t := by
    have he := oneParameter_derivativeAt_hasDerivAt hU hbd a ha ha0 ham t p
    rw [hfix,hd] at he
    change HasDerivAt A (((2*Complex.I) • (1 : Affine n →L[ℂ] Affine n))*A t) t at he
    have hj : ((2*Complex.I) • (1 : Affine n →L[ℂ] Affine n))*A t=(2*Complex.I) • A t := by
      ext v
      rfl
    rwa [hj] at he
  refine ⟨a (Real.pi/2),hfix _,?_⟩
  have he := scalar_linear_ode A (2*Complex.I) hAd (Real.pi/2)
  have hA0 : A 0=1 := by dsimp only [A]; rw [ha0,derivativeAt_one hU]
  rw [hA0] at he
  have hc : ((Real.pi/2 : ℝ) : ℂ)*(2*Complex.I)=(Real.pi : ℂ)*Complex.I := by
    push_cast
    ring
  rw [hc,Complex.exp_pi_mul_I,neg_one_smul] at he
  exact he

end

open Set
variable {n m : ℕ} {U : Set (Affine n)} {D : Set (Affine m)}
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (hD : IsOpen D) (e : Biholomorph U D)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U] [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
include hU hc hbd hD Γ hhol

theorem model_isotropy_central_shift_zero {X Y : Affine n → Affine n}
    (hX : IsCompleteGenerator U X) (hY : IsCompleteGenerator U Y) (p : D) (c : ℝ)
    (hx : coordinateField e X p.val=0) (hy : coordinateField e Y p.val=0)
    (hrel : fderiv ℂ (coordinateField e Y) p.val=Complex.I •
      ((c : ℂ) • (1 : Affine m →L[ℂ] Affine m)-fderiv ℂ (coordinateField e X) p.val)) : X=0 := by
  have hx0 := (coordinateField_value_zero_iff hU hD e X p).mp hx
  have hy0 := (coordinateField_value_zero_iff hU hD e Y p).mp hy
  apply isotropy_central_shift_zero hU hc hbd Γ hhol hX hY (e.toHomeomorph.symm p) c hx0 hy0
  rw [coordinateField_fderiv_of_zero hU hD e (hX.analyticOnNhd hU hbd) p hx0,
    coordinateField_fderiv_of_zero hU hD e (hY.analyticOnNhd hU hbd) p hy0] at hrel
  let A := mapDerivativeEquiv hU hD e (e.toHomeomorph.symm p)
  let B := mapDerivativeEquiv hD hU e.symm p
  apply ContinuousLinearMap.ext
  intro v
  have hz := congrArg (fun L : Affine m →L[ℂ] Affine m => L (A v)) hrel
  have hBA : B (A v)=v := by
    have hh := congrArg (fun L : Affine n →L[ℂ] Affine n => L v)
      (mapDerivative_symm_comp hU hD e (e.toHomeomorph.symm p))
    simpa only [A,B,mapDerivativeEquiv_apply,e.toHomeomorph.apply_symm_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using hh
  change A (fderiv ℂ Y (e.toHomeomorph.symm p).val (B (A v)))=
    Complex.I • ((c : ℂ) • (A v)-A (fderiv ℂ X (e.toHomeomorph.symm p).val (B (A v)))) at hz
  rw [hBA,←map_smul,←map_sub,←map_smul] at hz
  exact A.injective hz
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_OneKernel
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
attribute [-simp] _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061.Biholomorph.WeightedLieModel
variable {r k : ℕ} {G : Type*} [LieRing G] [LieAlgebra ℝ G]
    (M : WeightedLieModel r k G)

attribute [local instance] complexificationRatLieAlgebra

theorem euler_jet (X : ℂ ⊗[ℝ] G) (j : SecondJetIndex (ModelIndex r k)) :
    M.jet (M.center ⁅M.E,X⁆) j=secondJetWeight modelEulerWeight j*M.jet (M.center X) j :=
  LieFieldJets.conjugated_diagonal M.field M.point M.analytic M.lie (modelBasis r k)
    M.center M.E (flatWeightedEuler r k) M.centered_euler_germ modelEulerWeight
    (flatWeightedEuler_basis r k) X j

theorem eigen_jet_zero {X : ℂ ⊗[ℝ] G} {μ : ℂ} (hX : ⁅M.E,X⁆=μ • X)
    (j : SecondJetIndex (ModelIndex r k)) (hj : secondJetWeight modelEulerWeight j≠μ) :
    M.jet (M.center X) j=0 := by
  have he := M.euler_jet X j
  simp only [hX,map_smul,Pi.smul_apply,smul_eq_mul] at he
  have hh : (secondJetWeight modelEulerWeight j-μ)*M.jet (M.center X) j=0 := by
    rw [sub_mul,←he,sub_self]
  exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hj)

theorem centered_value_zero {X : ℂ ⊗[ℝ] G} {μ : ℂ} (hX : ⁅M.E,X⁆=μ • X)
    (hμ : μ=0 ∨ μ=1/2 ∨ μ=1) : M.field (M.center X) M.point=0 := by
  apply (modelBasis r k).ext_elem
  intro i
  have hh := M.eigen_jet_zero hX (.inl i) (by
    rcases hμ with rfl|rfl|rfl <;> cases i <;> norm_num [secondJetWeight,modelEulerWeight])
  simpa [jet,analyticSecondJetCoordinates] using hh

theorem centered_firstJet_one_zero {X : ℂ ⊗[ℝ] G} (hX : ⁅M.E,X⁆=(1 : ℂ) • X) :
    M.firstJet (M.center X)=0 := by
  apply ContinuousLinearMap.coe_injective
  apply (modelBasis r k).ext
  intro j
  apply (modelBasis r k).ext_elem
  intro i
  have hh := M.eigen_jet_zero hX (.inr (.inl (i,j))) (by
    cases i <;> cases j <;> norm_num [secondJetWeight,modelEulerWeight])
  simpa [jet,analyticSecondJetCoordinates,firstJet] using hh

theorem ofReal_eigen {X : G} {μ : ℝ} (hX : ⁅M.euler,X⁆=μ • X) :
    ⁅M.E,Complexification.ofReal X⁆=(μ : ℂ) • Complexification.ofReal X := by
  rw [←Complexification.ofReal_lie,hX,map_smul]
  exact (IsScalarTower.algebraMap_smul ℂ μ (Complexification.ofReal X)).symm

theorem center_of_commutes {X : ℂ ⊗[ℝ] G} (hX : ⁅M.T,X⁆=0) : M.center X=X :=
  LieAlgebra.innerExp_fixed _ _ _ _ hX

end Release061.Biholomorph.WeightedLieModel

open scoped TensorProduct

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PositiveVertexJets
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
attribute [-simp] _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
namespace LieAlgebra
open scoped _root_.LieAlgebra
variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [LieAlgebra ℚ L]

theorem innerExp_apply_of_cube_zero (T : L) (hT : IsNilpotent (LieAlgebra.ad ℂ L T))
    (c : ℂ) (X : L) (hX : ⁅T,⁅T,⁅T,X⁆⁆⁆=0) :
    innerExp T hT c X=X+c • ⁅T,X⁆+(c^2/2) • ⁅T,⁅T,X⁆⁆ := by
  let A := c • LieAlgebra.ad ℂ L T
  have hn : IsNilpotent A := hT.smul c
  have hs : (A^3) • X=0 := by
    change A (A (A X))=0
    simp [A,hX]
  change IsNilpotent.exp A X=_
  have he := IsNilpotent.exp_smul_eq_sum hs hn
  change IsNilpotent.exp A X= _ at he
  rw [he]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,Module.End.one_apply,
    Nat.factorial_zero,Nat.factorial_succ,Module.End.smul_def]
  simp [A,Module.End.pow_apply,smul_smul]
  module
end LieAlgebra

open Filter Topology
open scoped TensorProduct
namespace Release061.Biholomorph.WeightedLieModel
variable {r k : ℕ} {G : Type*} [LieRing G] [LieAlgebra ℝ G]
    (M : WeightedLieModel r k G)

theorem field_euler_value : M.field M.E M.point=Complex.I • M.u := by
  rw [M.euler_germ.eq_of_nhds,map_smul,flatWeightedEuler_normal]

theorem field_translation_value : M.field M.T M.point=M.u :=
  M.translation_germ.eq_of_nhds

theorem field_rotation_value : M.field M.H M.point=0 := by
  rw [M.rotation_germ.eq_of_nhds,map_smul,flatTangentialInfinitesimal_normal,smul_zero]

theorem firstJet_euler : M.firstJet M.E=flatWeightedEuler r k := by
  change fderiv ℂ (M.field M.E) M.point=_
  rw [M.euler_germ.fderiv_eq,(flatWeightedEuler r k).fderiv]

theorem firstJet_translation : M.firstJet M.T=0 := by
  change fderiv ℂ (M.field M.T) M.point=_
  rw [M.translation_germ.fderiv_eq,fderiv_const_apply]

theorem firstJet_rotation : M.firstJet M.H=flatTangentialInfinitesimal r k := by
  change fderiv ℂ (M.field M.H) M.point=_
  rw [M.rotation_germ.fderiv_eq,(flatTangentialInfinitesimal r k).fderiv]

theorem ofReal_smul (c : ℝ) (X : G) :
    Complexification.ofReal (c • X)=(c : ℂ) • Complexification.ofReal X := by
  rw [map_smul]
  exact (IsScalarTower.algebraMap_smul ℂ c (Complexification.ofReal X)).symm

theorem positive_vertex_jets (V : G) (hV : ⁅M.euler,V⁆=V)
    (hTV : ⁅M.translation,⁅M.translation,V⁆⁆=(-2 : ℝ) • M.translation) :
    let W := ⁅M.translation,V⁆+(2 : ℝ) • M.euler
    M.field (Complexification.ofReal W) M.point=0 ∧
    M.field (Complexification.ofReal V) M.point=M.u ∧
    M.firstJet (Complexification.ofReal V)=
      Complex.I • (M.firstJet (Complexification.ofReal W)-(2 : ℂ) • flatWeightedEuler r k) := by
  let := complexificationRatLieAlgebra (G := G)
  let Z := Complexification.ofReal V
  let W := ⁅M.translation,V⁆+(2 : ℝ) • M.euler
  let C := Complexification.ofReal W
  have hZ : ⁅M.E,Z⁆=(1 : ℂ) • Z := by
    simpa only [Complex.ofReal_one,one_smul] using M.ofReal_eigen (μ := 1) (by simpa using hV)
  have hC : C=⁅M.T,Z⁆+(2 : ℂ) • M.E := by
    simp only [C,W,map_add,Complexification.ofReal_lie,ofReal_smul,Complex.ofReal_ofNat]
    rfl
  have hTTZ : ⁅M.T,⁅M.T,Z⁆⁆=(-2 : ℂ) • M.T := by
    rw [←Complexification.ofReal_lie,←Complexification.ofReal_lie,hTV,ofReal_smul]
    norm_num
  have hTC : ⁅M.T,C⁆=0 := by
    rw [hC,LieRing.lie_add,LieAlgebra.lie_smul (2 : ℂ) M.T M.E,M.translation_euler,hTTZ]
    module
  have hEC : ⁅M.E,C⁆=(0 : ℂ) • C := by
    rw [hC,LieRing.lie_add,LieAlgebra.lie_smul (2 : ℂ) M.E M.E,lie_self,smul_zero,add_zero]
    simpa only [sub_self,zero_smul] using M.bracket_translation_eigen hZ
  have hcC : M.center C=C := M.center_of_commutes hTC
  have hCp : M.field C M.point=0 := by
    simpa only [hcC] using M.centered_value_zero hEC (Or.inl rfl)
  have hTTTZ : ⁅M.T,⁅M.T,⁅M.T,Z⁆⁆⁆=0 := by
    rw [hTTZ,LieAlgebra.lie_smul (-2 : ℂ) M.T M.T,lie_self,smul_zero]
  have hcZ : M.center Z=Z-Complex.I • C+(2*Complex.I) • M.E+M.T := by
    rw [center,LieAlgebra.innerExp_apply_of_cube_zero _ _ _ _ hTTTZ,hTTZ]
    rw [hC]
    simp only [smul_add,smul_smul,sub_eq_add_neg]
    norm_num
    module
  have hval : M.field Z M.point=M.u := by
    have hz := M.centered_value_zero hZ (Or.inr (Or.inr rfl))
    rw [hcZ] at hz
    simp only [map_add,map_sub,map_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,
      hCp,M.field_euler_value,M.field_translation_value,smul_zero,sub_zero,smul_smul] at hz
    rw [mul_assoc,Complex.I_mul_I,mul_neg_one] at hz
    apply sub_eq_zero.mp
    calc
      M.field Z M.point-M.u = M.field Z M.point+(-2 : ℂ) • M.u+M.u := by module
      _=0 := hz
  have hder : M.firstJet Z=Complex.I • (M.firstJet C-(2 : ℂ) • flatWeightedEuler r k) := by
    have hz := M.centered_firstJet_one_zero hZ
    rw [hcZ] at hz
    simp only [map_add,map_sub,map_smul,M.firstJet_euler,M.firstJet_translation,add_zero] at hz
    apply sub_eq_zero.mp
    calc
      M.firstJet Z-Complex.I • (M.firstJet C-(2 : ℂ) • flatWeightedEuler r k) =
        M.firstJet Z-Complex.I • M.firstJet C+(2*Complex.I) • flatWeightedEuler r k := by module
      _=0 := hz
  exact ⟨hCp,hval,hder⟩

end Release061.Biholomorph.WeightedLieModel

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ModelAxisNegativeIsotropy
attribute [-simp] _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061.Biholomorph

section
open Set
variable {n m : ℕ} {U : Set (Affine n)} {D : Set (Affine m)}

theorem coordinateField_scalar_derivative (hU : IsOpen U) (hD : IsOpen D)
    (e : Biholomorph U D) {X : Affine n → Affine n} (hX : AnalyticOnNhd ℂ X U)
    (p : D) (c : ℂ) (hx : coordinateField e X p.val=0)
    (hd : fderiv ℂ (coordinateField e X) p.val=c • (1 : Affine m →L[ℂ] Affine m)) :
    fderiv ℂ X (e.toHomeomorph.symm p).val=c • (1 : Affine n →L[ℂ] Affine n) := by
  have hx0 := (coordinateField_value_zero_iff hU hD e X p).mp hx
  rw [coordinateField_fderiv_of_zero hU hD e hX p hx0] at hd
  let A := mapDerivativeEquiv hU hD e (e.toHomeomorph.symm p)
  apply ContinuousLinearMap.ext
  intro v
  have hh := congrArg (fun L : Affine m →L[ℂ] Affine m => L (A v)) hd
  have hi : e.symm.mapDerivative p (A v)=v := by
    have he := congrArg (fun L : Affine n →L[ℂ] Affine n => L v)
      (mapDerivative_symm_comp hU hD e (e.toHomeomorph.symm p))
    simpa only [A,mapDerivativeEquiv_apply,e.toHomeomorph.apply_symm_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using he
  change A (fderiv ℂ X (e.toHomeomorph.symm p).val (e.symm.mapDerivative p (A v)))=c • A v at hh
  rw [hi,←map_smul] at hh
  exact A.injective hh

theorem model_negative_isotropy_of_scalar_generator
    (hU : IsOpen U) [LocallyCompactSpace U] (hbd : Bornology.IsBounded U)
    (hD : IsOpen D) (e : Biholomorph U D)
    {X : Affine n → Affine n} (hX : IsCompleteGenerator U X) (p : D)
    (hx : coordinateField e X p.val=0)
    (hd : fderiv ℂ (coordinateField e X) p.val=(2*Complex.I) • (1 : Affine m →L[ℂ] Affine m)) :
    ∃ a : Biholomorph U U, a.toHomeomorph (e.toHomeomorph.symm p)=e.toHomeomorph.symm p ∧
      a.derivativeAt (e.toHomeomorph.symm p)= -1 := by
  apply negative_isotropy_of_scalar_generator hU hbd hX (e.toHomeomorph.symm p)
  · exact (coordinateField_value_zero_iff hU hD e X p).mp hx
  · exact coordinateField_scalar_derivative hU hD e (hX.analyticOnNhd hU hbd) p (2*Complex.I) hx hd
end

open Set Filter Topology
open scoped TensorProduct

theorem flatTangentialInfinitesimal_euler (r k : ℕ) :
    flatTangentialInfinitesimal r k=Complex.I •
      ((2 : ℂ) • (1 : Affine (r+k) →L[ℂ] Affine (r+k))-(2 : ℂ) • flatWeightedEuler r k) := by
  apply ContinuousLinearMap.coe_injective
  apply (modelBasis r k).ext
  intro j
  change flatTangentialInfinitesimal r k (modelBasis r k j)=
    Complex.I • ((2 : ℂ) • modelBasis r k j-(2 : ℂ) • flatWeightedEuler r k (modelBasis r k j))
  rw [flatTangentialInfinitesimal_basis,flatWeightedEuler_basis]
  cases j <;> simp only [modelRotationWeight,modelEulerWeight] <;> module

variable {n : ℕ} {U : Set (Affine n)}
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U] [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

include hU hc hbd Γ hhol in

theorem model_axis_negative_isotropy {r k : ℕ} (D : Set (Affine r × Affine k))
    (hDo : IsOpen D)
    (htr : ∀ p : Affine r × Affine k, ∀ a : Fin k → ℝ,
      (p.1,fun i => p.2 i+(a i : ℂ)) ∈ D ↔ p∈D)
    (hd : ∀ t : ℝ, 0<t → ∀ p, (Real.sqrt t • p.1,t • p.2)∈D ↔ p∈D)
    (hr : ∀ c : ℂ, ‖c‖=1 → ∀ p, (c • p.1,p.2)∈D ↔ p∈D)
    [LocallyCompactSpace ((affineProductCoordinates r k) '' D)]
    (e : Biholomorph ((affineProductCoordinates r k) '' D) U)
    (p : (affineProductCoordinates r k) '' D) (a : Fin k → ℝ)
    (hp : p.val=Complex.I • flatNormalVector r k a) :
    ∃ b : Biholomorph U U, b.toHomeomorph (e.toHomeomorph p)=e.toHomeomorph p ∧
      b.derivativeAt (e.toHomeomorph p)= -1 := by
  let S := (affineProductCoordinates r k) '' D
  have hS : IsOpen S := (affineProductCoordinates r k).isOpenMap _ hDo
  have hpa : affineProductCoordinates r k (0,fun i => Complex.I*(a i : ℂ))=p.val := by
    rw [hp,flatNormalVector,←map_smul]
    congr 1
    ext i <;> simp
  have ha : (0,fun i => Complex.I*(a i : ℂ))∈D := by
    obtain ⟨q,hq,hqp⟩ := p.property
    have hqeq := (affineProductCoordinates r k).injective (hqp.trans hpa.symm)
    simpa only [hqeq] using hq
  let G := completeGeneratorSpace hU hc hbd Γ hhol
  let _ : FiniteDimensional ℝ G := finiteDimensional_completeGeneratorSpace hU hc hbd Γ hhol
  obtain ⟨M,hnormal,hfield⟩ := exists_actual_weightedLieModel hU hc hbd Γ hhol D hDo htr hd hr e a ha
  have hpoint : M.point=p.val := by rw [WeightedLieModel.point,hnormal,hp]
  have hF (X : G) : M.field (Complexification.ofReal X)=coordinateField e.symm X.val := by
    rw [hfield,modelComplexField_ofReal]
  obtain ⟨V,hV,hTV⟩ := M.exists_positive_real
    (completeGenerator_trace_ad_eq_zero hU hc hbd Γ hhol M.euler)
  let W : G := ⁅M.translation,V⁆+(2 : ℝ) • M.euler
  let Q : G := M.translation-V+M.rotation
  obtain ⟨hWp,hVp,hVd⟩ := M.positive_vertex_jets V hV hTV
  change M.field (Complexification.ofReal W) M.point=0 at hWp
  change M.firstJet (Complexification.ofReal V)=
    Complex.I • (M.firstJet (Complexification.ofReal W)-(2 : ℂ) • flatWeightedEuler r k) at hVd
  have hQp : M.field (Complexification.ofReal Q) M.point=0 := by
    simp only [Q,map_add,map_sub,Pi.add_apply,Pi.sub_apply,M.field_translation_value,hVp,
      M.field_rotation_value,sub_self,add_zero]
  have hQd : M.firstJet (Complexification.ofReal Q)=Complex.I •
      ((2 : ℂ) • (1 : Affine (r+k) →L[ℂ] Affine (r+k))-M.firstJet (Complexification.ofReal W)) := by
    simp only [Q,map_add,map_sub,M.firstJet_translation,M.firstJet_rotation,hVd]
    rw [flatTangentialInfinitesimal_euler]
    module
  have hWzero : W=0 := by
    have hx := hWp
    have hy := hQp
    have hrel := hQd
    change fderiv ℂ (M.field (Complexification.ofReal Q)) M.point=Complex.I •
      ((2 : ℂ) • (1 : Affine (r+k) →L[ℂ] Affine (r+k))-
        fderiv ℂ (M.field (Complexification.ofReal W)) M.point) at hrel
    simp only [hF,hpoint] at hx hy hrel
    apply Subtype.ext
    exact model_isotropy_central_shift_zero hU hc hbd hS e.symm Γ hhol W.property Q.property p 2 hx hy
      (by simpa only [Complex.ofReal_ofNat] using hrel)
  have hQscalar : M.firstJet (Complexification.ofReal Q)=
      (2*Complex.I) • (1 : Affine (r+k) →L[ℂ] Affine (r+k)) := by
    rw [hQd,hWzero,map_zero,map_zero,sub_zero,smul_smul]
    congr 1
    ring
  change fderiv ℂ (M.field (Complexification.ofReal Q)) M.point=_ at hQscalar
  simp only [hF,hpoint] at hQp hQscalar
  exact model_negative_isotropy_of_scalar_generator hU hbd hS e.symm Q.property p hQp hQscalar

end Release061.Biholomorph

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_QuadraticModelResidualFiber
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Hermitian
open Set Complex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] {k : ℕ}

omit [IsScalarTower ℝ ℂ E] [NormedSpace ℝ E] [FiniteDimensional ℂ E] in
lemma normalTranslation_analytic (a : Fin k → ℝ) :
    AnalyticOnNhd ℂ (normalTranslation (E := E) a) univ := by
  intro p _
  exact analyticAt_id.add analyticAt_const

omit [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] in
lemma normalTranslation_mem
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (C : Set (Fin k → ℝ))
    (a : Fin k → ℝ) (p : E × (Fin k → ℂ)) :
    normalTranslation a p ∈ quadraticDomain (hermQuadratic B) C ↔
      p ∈ quadraticDomain (hermQuadratic B) C := by
  change (fun i => (p.2 i+(a i : ℂ)).im-hermQuadratic B (p.1+0) i) ∈ C ↔ _
  simp only [add_zero,add_im,ofReal_im,add_zero]
  rfl

lemma axisNormalization_apply
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : E × (Fin k → ℂ)) :
    axisNormalization B p p =
      (0,fun i => I*((p.2 i).im-hermQuadratic B p.1 i : ℝ)) := by
  change normalTranslation _ (heisenbergShift B (-p.1) p) = _
  rw [heisenbergShift_axis]
  apply Prod.ext
  · simp [normalTranslation]
  · funext i
    apply Complex.ext <;> simp [normalTranslation]

lemma axisNormalization_mem
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (C : Set (Fin k → ℝ))
    (p q : E × (Fin k → ℂ)) :
    axisNormalization B p q ∈ quadraticDomain (hermQuadratic B) C ↔
      q ∈ quadraticDomain (hermQuadratic B) C := by
  change normalTranslation _ (heisenbergShift B (-p.1) q) ∈ _ ↔ _
  rw [normalTranslation_mem,heisenbergShift_mem]

lemma axisNormalization_analytic
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : E × (Fin k → ℂ)) :
    AnalyticOnNhd ℂ (axisNormalization B p) univ := by
  intro q _
  exact (normalTranslation_analytic _ _ (mem_univ _)).comp
    (heisenbergShift_analytic B (-p.1) q (mem_univ _))

lemma axisNormalization_inverse_analytic
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : E × (Fin k → ℂ)) :
    AnalyticOnNhd ℂ (axisNormalization B p).symm univ := by
  intro q _
  have ht : AnalyticAt ℂ (normalTranslation (E := E) (fun i => -(p.2 i).re)).symm q := by
    unfold normalTranslation
    rw [Homeomorph.addRight_symm]
    exact analyticAt_id.add analyticAt_const
  exact (heisenbergShift_analytic B (-(-p.1)) _ (mem_univ _)).comp ht

end Release061.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_HermitianModelSymmetric
attribute [-simp] _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set Filter Topology
namespace Biholomorph

theorem hermitian_model_to_axis {r k : ℕ}
    (B : Fin k → Affine r →ₗ[ℝ] Affine r →ₗ[ℝ] ℝ) (C : Set (Fin k → ℝ))
    (p : (affineProductCoordinates r k) '' quadraticDomain (Hermitian.hermQuadratic B) C) :
    ∃ b : Biholomorph
        ((affineProductCoordinates r k) '' quadraticDomain (Hermitian.hermQuadratic B) C)
        ((affineProductCoordinates r k) '' quadraticDomain (Hermitian.hermQuadratic B) C),
      ∃ a : Fin k → ℝ, (b.toHomeomorph p).val=Complex.I • flatNormalVector r k a := by
  let L := affineProductCoordinates r k
  let D := quadraticDomain (Hermitian.hermQuadratic B) C
  let S := L '' D
  let q := L.symm p.val
  let a := Hermitian.axisNormalization B q
  let f := (L.toHomeomorph.symm.trans a).trans L.toHomeomorph
  have hf : AnalyticOnNhd ℂ f univ := by
    intro x _
    exact (L.toContinuousLinearMap.analyticAt _).comp
      ((Hermitian.axisNormalization_analytic B q _ (mem_univ _)).comp
        (L.symm.toContinuousLinearMap.analyticAt x))
  have hfi : AnalyticOnNhd ℂ f.symm univ := by
    intro x _
    exact (L.toContinuousLinearMap.analyticAt _).comp
      ((Hermitian.axisNormalization_inverse_analytic B q _ (mem_univ _)).comp
        (L.symm.toContinuousLinearMap.analyticAt x))
  have hm : MapsTo f S S := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨a x,(Hermitian.axisNormalization_mem B C q x).mpr hx,?_⟩
    simp [f]
  have hmi : MapsTo f.symm S S := by
    rintro _ ⟨x,hx,rfl⟩
    have hi : a.symm x∈D := (Hermitian.axisNormalization_mem B C q (a.symm x)).mp
      (by simpa only [a,a.apply_symm_apply] using hx)
    refine ⟨a.symm x,hi,?_⟩
    simp [f]
  let b := biholomorphOfAmbientInverse S S f f.symm (hf.mono (subset_univ _))
    (hfi.mono (subset_univ _)) hm hmi (fun x _ => f.symm_apply_apply x)
    (fun x _ => f.apply_symm_apply x)
  refine ⟨b,fun i => (q.2 i).im-Hermitian.hermQuadratic B q.1 i,?_⟩
  change L (a q)=_
  rw [Hermitian.axisNormalization_apply]
  rw [flatNormalVector,←map_smul]
  congr 1
  ext i <;> simp

variable {n : ℕ} {U : Set (Affine n)}
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U] [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

include hU hc hbd Γ hhol in

theorem hermitian_model_bounded_symmetric_oai {r k : ℕ}
    (B : Fin k → Affine r →ₗ[ℝ] Affine r →ₗ[ℝ] ℝ) (C : Set (Fin k → ℝ))
    (hDo : IsOpen (quadraticDomain (Hermitian.hermQuadratic B) C))
    (htr : ∀ p : Affine r × Affine k, ∀ a : Fin k → ℝ,
      (p.1,fun i => p.2 i+(a i : ℂ)) ∈ quadraticDomain (Hermitian.hermQuadratic B) C ↔
        p∈quadraticDomain (Hermitian.hermQuadratic B) C)
    (hd : ∀ t : ℝ, 0<t → ∀ p, (Real.sqrt t • p.1,t • p.2)∈
      quadraticDomain (Hermitian.hermQuadratic B) C ↔ p∈quadraticDomain (Hermitian.hermQuadratic B) C)
    (hr : ∀ c : ℂ, ‖c‖=1 → ∀ p, (c • p.1,p.2)∈quadraticDomain (Hermitian.hermQuadratic B) C ↔
      p∈quadraticDomain (Hermitian.hermQuadratic B) C)
    [LocallyCompactSpace ((affineProductCoordinates r k) '' quadraticDomain (Hermitian.hermQuadratic B) C)]
    (e : Biholomorph ((affineProductCoordinates r k) '' quadraticDomain (Hermitian.hermQuadratic B) C) U) :
    IsBoundedSymmetricDomain U := by
  apply (boundedSymmetricDomain_iff_negative_isotropy hU hc hbd).mpr
  intro p
  let q := e.toHomeomorph.symm p
  obtain ⟨b,a,ha⟩ := hermitian_model_to_axis B C q
  let e' := b.symm.trans e
  let q' := b.toHomeomorph q
  have hep : e'.toHomeomorph q'=p := by
    change e.toHomeomorph (b.toHomeomorph.symm (b.toHomeomorph (e.toHomeomorph.symm p)))=p
    simp only [b.toHomeomorph.symm_apply_apply,e.toHomeomorph.apply_symm_apply]
  obtain ⟨s,hs,hd'⟩ := model_axis_negative_isotropy hU hc hbd Γ hhol
    (quadraticDomain (Hermitian.hermQuadratic B) C) hDo htr hd hr e' q' a ha
  rw [hep] at hs hd'
  exact ⟨s,hs,hd'⟩

end Biholomorph
end Release061

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Release061.Biholomorph.hermitian_model_bounded_symmetric_oai.{u_1} := @OAI.Release061.Biholomorph.hermitian_model_bounded_symmetric_oai.{u_1}
