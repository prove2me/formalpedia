-- Prove2me | solution 1 for OAI.Release061.NashPatch.null_nonsmallgood_generic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:01:03.881294+00:00
-- url     : https://prove2.me/submissions/30350cfd-ba66-4b85-a09d-adeb9f6440f0

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S000
import Definitions.Def_OAIQ025S001
import Theorems.Thm_OAI_Release061_NashBoundaryChart_locally_small_slope_good

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticImplicitScalar
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061


open Set Filter Topology

theorem analytic_local_inverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {a : E} (hf : AnalyticAt ℂ f a)
    (i : E ≃L[ℂ] F) (hi : HasFDerivAt f (i : E →L[ℂ] F) a) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ a ∈ e.source ∧
      AnalyticAt ℂ e.symm (f a) := by
  have hs : HasStrictFDerivAt f (i : E →L[ℂ] F) a := by
    simpa only [hi.fderiv] using hf.hasStrictFDerivAt
  let e := hs.toOpenPartialHomeomorph f
  refine ⟨e, hs.toOpenPartialHomeomorph_coe, hs.mem_toOpenPartialHomeomorph_source, ?_⟩
  obtain ⟨p, hp⟩ := hf
  have he : (e : E → F) = f := hs.toOpenPartialHomeomorph_coe
  have hpe : HasFPowerSeriesAt e p a := he ▸ hp
  have hcoeff : p 1 = (continuousMultilinearCurryFin1 ℂ E F).symm
      (i : E →L[ℂ] F) := by
    apply (continuousMultilinearCurryFin1 ℂ E F).injective
    simpa using hp.hasFDerivAt.unique hi
  simpa only [he] using
    (e.hasFPowerSeriesAt_symm hs.mem_toOpenPartialHomeomorph_source hpe hcoeff).analyticAt

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialSignSetInf
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
namespace Release061.PolynomialSignSet
open Set
open scoped Classical

lemma norm_lt_polynomial {X ι κ : Type*} [Fintype κ] {c : X → ι → ℝ}
    (p : κ → MvPolynomial ι ℝ) (q : MvPolynomial ι ℝ) :
    PolynomialSignSet c {x | ‖fun k => MvPolynomial.eval (c x) (p k)‖ <
      MvPolynomial.eval (c x) q} := by
  have h := (PolynomialSignSet.positive (c := c) q).inter
    (PolynomialSignSet.forall_finite (fun k x =>
      0 < MvPolynomial.eval (c x) (q+p k) ∧ 0 < MvPolynomial.eval (c x) (q-p k))
      (fun k => (PolynomialSignSet.positive (q+p k)).inter
        (PolynomialSignSet.positive (q-p k))))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_inter_iff,mem_ofPred_eq,MvPolynomial.eval_add,MvPolynomial.eval_sub]
  constructor
  · intro hx
    have hq : 0 < MvPolynomial.eval (c x) q := (norm_nonneg _).trans_lt hx
    refine ⟨hq,fun k => ?_⟩
    have hk := (pi_norm_lt_iff hq).mp hx k
    rw [Real.norm_eq_abs,abs_lt] at hk
    constructor <;> linarith [hk.1,hk.2]
  · rintro ⟨hq,h⟩
    apply (pi_norm_lt_iff hq).mpr
    intro k
    rw [Real.norm_eq_abs,abs_lt]
    constructor <;> linarith [(h k).1,(h k).2]

end Release061.PolynomialSignSet

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_Pair
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
open Set
open SignElimination
open scoped Classical

namespace SemialgebraicOn
variable {ι κ δ : Type*}
variable {B C : Set (ι → ℝ)} {f : (ι → ℝ) → (κ → ℝ)}

lemma restrict (hf : SemialgebraicOn B f) (hC : PolynomialSignSet id C) :
    SemialgebraicOn (B ∩ C) f := by
  have hc := hC.coordinate_preimage (fun z : (ι → ℝ) × (κ → ℝ) => z.1) Sum.inl
    (d := fun z => Sum.elim z.1 z.2) (by intro z i; rfl)
  unfold SemialgebraicOn at hf ⊢
  convert hf.inter hc using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp only [mem_inter_iff,mem_ofPred_eq,mem_preimage]
  tauto

lemma mono (hf : SemialgebraicOn B f) (hC : PolynomialSignSet id C) (hCB : C ⊆ B) :
    SemialgebraicOn C f := by
  simpa only [inter_eq_right.mpr hCB] using hf.restrict hC

lemma preimage [Finite κ] (hf : SemialgebraicOn B f) {S : Set (κ → ℝ)} (hS : PolynomialSignSet id S) :
    PolynomialSignSet id (B ∩ f ⁻¹' S) := by
  have hs := hS.coordinate_preimage (fun z : (ι → ℝ) × (κ → ℝ) => z.2) Sum.inr
    (d := fun z => Sum.elim z.1 z.2) (by intro z i; rfl)
  have hh := polynomialSignSet_projection_finite (c := id) (hf.inter hs)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_inter_iff,mem_preimage,mem_ofPred_eq]
  constructor
  · intro h
    exact ⟨f x,⟨h.1,rfl⟩,h.2⟩
  · rintro ⟨y,⟨hx,rfl⟩,hy⟩
    exact ⟨hx,hy⟩

end SemialgebraicOn
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_RealPolynomialAnalyticRoot
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

theorem real_analytic_local_inverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {a : E} (hf : AnalyticAt ℝ f a)
    (i : E ≃L[ℝ] F) (hi : HasFDerivAt f (i : E →L[ℝ] F) a) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ a ∈ e.source ∧
      AnalyticAt ℝ e.symm (f a) := by
  have hs : HasStrictFDerivAt f (i : E →L[ℝ] F) a := by
    simpa only [hi.fderiv] using hf.hasStrictFDerivAt
  let e := hs.toOpenPartialHomeomorph f
  refine ⟨e, hs.toOpenPartialHomeomorph_coe, hs.mem_toOpenPartialHomeomorph_source, ?_⟩
  obtain ⟨p, hp⟩ := hf
  have he : (e : E → F) = f := hs.toOpenPartialHomeomorph_coe
  have hpe : HasFPowerSeriesAt e p a := he ▸ hp
  have hcoeff : p 1 = (continuousMultilinearCurryFin1 ℝ E F).symm
      (i : E →L[ℝ] F) := by
    apply (continuousMultilinearCurryFin1 ℝ E F).injective
    simpa using hp.hasFDerivAt.unique hi
  simpa only [he] using
    (e.hasFPowerSeriesAt_symm hs.mem_toOpenPartialHomeomorph_source hpe hcoeff).analyticAt

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SemialgebraicOffsetLimitsFamily
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
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
open Set Filter Topology Metric MeasureTheory Classical
open SignElimination

theorem isSemialgebraic_iff_polynomialSignSet {n : ℕ} {S : Set (Affine n)} :
    IsSemialgebraic S ↔ PolynomialSignSet realCoordinates S := by
  constructor
  · intro h
    induction h with
    | zero p => exact .zero p
    | positive p => exact .positive p
    | compl _ ih => exact ih.compl
    | union _ _ ih ih' => exact ih.union ih'
  · intro h
    induction h with
    | zero p => exact .zero p
    | positive p => exact .positive p
    | compl _ ih => exact ih.compl
    | union _ _ ih ih' => exact ih.union ih'

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CenteredChartGerms
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
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

theorem Biholomorph.centered_chart_germs {n m : ℕ} {V W : Set (Affine n)}
    {B : Set (Affine m)} (e : Biholomorph W B) (hWV : W ⊆ V)
    (hW : IsOpen ((Subtype.val : V → Affine n) ⁻¹' W)) (hB : IsOpen B)
    {q : Affine n} (hq : q ∈ W) :
    ∃ (F : Affine m → Affine n) (G : Affine n → Affine m),
      F 0 = q ∧ AnalyticAt ℂ F 0 ∧ AnalyticAt ℂ G q ∧
      (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id ∧
      (∀ᶠ y in 𝓝[V] q, F (G y) = y) ∧
      (∀ᶠ z in 𝓝 (0 : Affine m), F z ∈ V) := by
  let b : Affine m := (e.toHomeomorph ⟨q,hq⟩).val
  have hb : b ∈ B := (e.toHomeomorph ⟨q,hq⟩).property
  let f := ambientExtend (fun y : B => (e.toHomeomorph.symm y).val)
  have hf : AnalyticOnNhd ℂ f B := e.holomorphic_invFun.analyticOnNhd_extend hB
  have hfb : f b = q := by
    rw [show f b = (e.toHomeomorph.symm (e.toHomeomorph ⟨q,hq⟩)).val from ambientExtend_apply _ _]
    simp
  obtain ⟨O,hO,hqO,g,hg,hge⟩ := e.holomorphic_toFun ⟨q,hq⟩
  let F : Affine m → Affine n := fun z => f (z+b)
  let G : Affine n → Affine m := fun y => g y-b
  have hF0 : F 0 = q := by simpa only [F,zero_add] using hfb
  have hF : AnalyticAt ℂ F 0 := by
    have htr : AnalyticAt ℂ (fun z : Affine m => z+b) 0 := analyticAt_id.add analyticAt_const
    have hf' : AnalyticAt ℂ f (0+b) := by simpa only [zero_add] using hf b hb
    exact hf'.comp (f := fun z : Affine m => z+b) (x := 0) htr
  have hG : AnalyticAt ℂ G q := (hg q hqO).sub analyticAt_const
  refine ⟨F,G,hF0,hF,hG,?_,?_,?_⟩
  · have hzB : ∀ᶠ z in 𝓝 (0 : Affine m), z+b ∈ B :=
      ((continuous_id.add continuous_const).continuousAt (x := (0 : Affine m))).preimage_mem_nhds
        (by simpa using hB.mem_nhds hb)
    have hzO : ∀ᶠ z in 𝓝 (0 : Affine m), F z ∈ O :=
      hF.continuousAt.preimage_mem_nhds (by simpa only [hF0] using hO.mem_nhds hqO)
    filter_upwards [hzB,hzO] with z hz hz'
    have hfy : f (z+b) = (e.toHomeomorph.symm ⟨z+b,hz⟩).val := ambientExtend_apply (fun y : B => (e.toHomeomorph.symm y).val) ⟨z+b,hz⟩
    have hfw : F z ∈ W := by rw [show F z = f (z+b) from rfl,hfy]; exact (e.toHomeomorph.symm ⟨z+b,hz⟩).property
    have he : g (F z) = z+b := by
      rw [hge ⟨F z,hfw⟩ hz']
      have heq : (⟨F z,hfw⟩ : W) = e.toHomeomorph.symm ⟨z+b,hz⟩ := Subtype.ext hfy
      rw [heq]
      exact congrArg Subtype.val (e.toHomeomorph.apply_symm_apply ⟨z+b,hz⟩)
    change g (F z)-b = z
    rw [he,add_sub_cancel_right]
  · obtain ⟨O',hO',hWO'⟩ := isOpen_induced_iff.mp hW
    have hqO' : q ∈ O' := by
      have hh : (⟨q,hWV hq⟩ : V) ∈ (Subtype.val : V → Affine n) ⁻¹' W := hq
      rwa [← hWO'] at hh
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hO'.mem_nhds hqO'),
      mem_nhdsWithin_of_mem_nhds (hO.mem_nhds hqO)] with y hyV hyO' hyO
    have hyW : y ∈ W := by
      have hh : (⟨y,hyV⟩ : V) ∈ (Subtype.val : V → Affine n) ⁻¹' O' := hyO'
      rwa [hWO'] at hh
    have hgy := hge ⟨y,hyW⟩ hyO
    change f (g y-b+b) = y
    rw [sub_add_cancel,hgy]
    rw [show f (e.toHomeomorph ⟨y,hyW⟩).val =
      (e.toHomeomorph.symm (e.toHomeomorph ⟨y,hyW⟩)).val from ambientExtend_apply _ _]
    simp
  · have hzB : ∀ᶠ z in 𝓝 (0 : Affine m), z+b ∈ B :=
      ((continuous_id.add continuous_const).continuousAt (x := (0 : Affine m))).preimage_mem_nhds
        (by simpa using hB.mem_nhds hb)
    filter_upwards [hzB] with z hz
    change f (z+b) ∈ V
    rw [show f (z+b) = (e.toHomeomorph.symm ⟨z+b,hz⟩).val from ambientExtend_apply (fun y : B => (e.toHomeomorph.symm y).val) ⟨z+b,hz⟩]
    exact hWV (e.toHomeomorph.symm ⟨z+b,hz⟩).property

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SemialgebraicBoundaryFiniteNash
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
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
open Set Filter Topology Metric
open SignElimination
open scoped Classical

lemma isSemialgebraic_real_image {n : ℕ} {S : Set (Affine n)} (hS : IsSemialgebraic S) :
    PolynomialSignSet id (complexRealEquiv n '' S) := by
  have hh := (isSemialgebraic_iff_polynomialSignSet.mp hS).coordinate_preimage
    (complexRealEquiv n).symm finSumFinEquiv
    (d := id) (by intro x j; cases j <;> rfl)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_image,mem_preimage]
  constructor
  · rintro ⟨z,hz,rfl⟩
    simpa using hz
  · intro hx
    exact ⟨_,hx,(complexRealEquiv n).apply_symm_apply x⟩

namespace NashPatch
variable {n : ℕ}

lemma analytic_complexMap (p : NashPatch (n+n)) : AnalyticOnNhd ℝ p.complexMap p.domain := by
  intro x hx
  exact ((complexRealEquiv n).symm.analyticAt _).comp (p.analytic_toFun x hx)

lemma injective_fderiv_complexMap (p : NashPatch (n+n)) {x : Fin p.dim → ℝ} (hx : x ∈ p.domain) :
    Function.Injective (fderiv ℝ p.complexMap x) := by
  have he := ((complexRealEquiv n).symm.hasFDerivAt.comp x
    (p.analytic_toFun x hx).differentiableAt.hasFDerivAt).fderiv
  change Function.Injective (fderiv ℝ ((complexRealEquiv n).symm ∘ p.toFun) x)
  rw [he]
  exact (complexRealEquiv n).symm.injective.comp (p.injective_fderiv x hx)

end NashPatch

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AffineInverseGermSemialgebraic
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
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
open Set Filter Topology
open scoped Classical

theorem linear_projection_chart_germ {m N : ℕ} (V : Set (Affine N))
    (F : Affine m → Affine N) (G : Affine N → Affine m)
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (F 0))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFG : ∀ᶠ y in 𝓝[V] (F 0), F (G y) = y)
    (hFV : ∀ᶠ z in 𝓝 (0 : Affine m), F z ∈ V) :
    ∃ (π : Affine N →L[ℂ] Affine m) (H : Affine m → Affine N),
      H 0 = F 0 ∧ AnalyticAt ℂ H 0 ∧
      (∀ᶠ z in 𝓝 (0 : Affine m), π (H z - F 0) = z) ∧
      (∀ᶠ y in 𝓝[V] (F 0), H (π (y-F 0)) = y) ∧
      (∀ᶠ z in 𝓝 (0 : Affine m), H z ∈ V) := by
  let π := fderiv ℂ G (F 0)
  have hid : π.comp (fderiv ℂ F 0) = ContinuousLinearMap.id ℂ _ :=
    ((hG.differentiableAt.hasFDerivAt.comp 0 hF.differentiableAt.hasFDerivAt).congr_of_eventuallyEq hGF.symm).unique (hasFDerivAt_id 0)
  have hG0 : G (F 0) = 0 := hGF.eq_of_nhds
  let f : Affine m → Affine m := fun z => π (F z-F 0)
  have hf : AnalyticAt ℂ f 0 := (π.analyticAt _).comp (hF.sub analyticAt_const)
  have hf0 : f 0 = 0 := by simp [f]
  have hfd : HasFDerivAt f (ContinuousLinearEquiv.refl ℂ (Affine m) : Affine m →L[ℂ] Affine m) 0 := by
    have hh := π.hasFDerivAt.comp 0 (hF.differentiableAt.hasFDerivAt.sub_const (F 0))
    simpa only [Function.comp_def,hid,ContinuousLinearEquiv.coe_refl] using hh
  obtain ⟨e,he,h0,hea⟩ := analytic_local_inverse hf (ContinuousLinearEquiv.refl ℂ (Affine m)) hfd
  have he0 : e 0 = 0 := by rw [he]; exact hf0
  have hinv0 : e.symm 0 = 0 := by simpa only [he0] using e.left_inv h0
  have htarget : (0 : Affine m) ∈ e.target := by simpa only [he0] using e.map_source h0
  have hean : AnalyticAt ℂ e.symm 0 := by simpa only [hf0] using hea
  have het : Tendsto e.symm (𝓝 (0 : Affine m)) (𝓝 0) := by
    simpa only [ContinuousAt,hinv0] using hean.continuousAt
  let H := F ∘ e.symm
  refine ⟨π,H,by simp only [H,Function.comp_apply,hinv0],?_,?_,?_,het hFV⟩
  · exact (by simpa only [hinv0] using hF : AnalyticAt ℂ F (e.symm 0)).comp hean
  · filter_upwards [e.open_target.mem_nhds htarget] with z hz
    simpa only [H,he,f,Function.comp_apply] using e.right_inv hz
  · have hGs : ∀ᶠ y in 𝓝 (F 0), G y ∈ e.source :=
      hG.continuousAt.preimage_mem_nhds (by simpa only [hG0] using e.open_source.mem_nhds h0)
    filter_upwards [hFG,mem_nhdsWithin_of_mem_nhds hGs] with y hy hys
    have hl := e.left_inv hys
    rw [he] at hl
    have hfy : f (G y) = π (y-F 0) := by simp only [f,hy]
    rw [hfy] at hl
    change F (e.symm (π (y-F 0))) = y
    rw [hl,hy]
end

open Set Filter Topology Metric
open scoped Classical

theorem SemialgebraicOn.affine {ι κ : Type*} [Fintype ι] [Finite κ]
    {B : Set (ι → ℝ)} (hB : PolynomialSignSet id B)
    (L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (b : κ → ℝ) :
    SemialgebraicOn B (fun y => L y + b) := by
  classical
  let p (j : κ) : MvPolynomial ι ℝ :=
    (∑ i, MvPolynomial.C (L (Pi.single i 1) j) * MvPolynomial.X i) + MvPolynomial.C (b j)
  apply (SemialgebraicOn.polynomial hB p).congr
  intro y _
  have hy : y = ∑ i : ι, y i • Pi.single i (1 : ℝ) := by
    ext i
    simp [Pi.single_apply]
  funext j
  simp only [p,MvPolynomial.eval_add,map_sum,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X,Pi.add_apply]
  congr 1
  conv_rhs => rw [hy]
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

lemma polynomialSignSet_real_ball {ι : Type*} [Fintype ι] (p : ι → ℝ) (r : ℝ) :
    PolynomialSignSet id {y : ι → ℝ | ‖y-p‖ < r} := by
  convert PolynomialSignSet.norm_lt_polynomial (c := id)
    (fun j => MvPolynomial.X j - MvPolynomial.C (p j)) (MvPolynomial.C r) using 1
  all_goals try with_reducible_and_instances rfl
  ext y
  simp only [mem_ofPred_eq,id_eq,map_sub,MvPolynomial.eval_X,MvPolynomial.eval_C,Pi.sub_def]

theorem semialgebraicOn_inverse_restrict {ι κ : Type*}
    {B : Set (ι → ℝ)} {T : Set (κ → ℝ)}
    (hB : PolynomialSignSet id B) (g : (κ → ℝ) → (ι → ℝ))
    (hg : SemialgebraicOn T g) (f : (ι → ℝ) → (κ → ℝ))
    (hf : MapsTo f B T) (hgf : ∀ x ∈ B, g (f x) = x)
    (hfg : ∀ y ∈ T, g y ∈ B → f (g y) = y) : SemialgebraicOn B f := by
  have hh := hg.coordinate_preimage (fun z : (ι → ℝ) × (κ → ℝ) => (z.2,z.1))
    (Equiv.sumComm κ ι) (d := fun z => Sum.elim z.1 z.2)
    (by intro z i; cases i <;> rfl)
  have hb := hB.coordinate_preimage (fun z : (ι → ℝ) × (κ → ℝ) => z.1) Sum.inl
    (d := fun z => Sum.elim z.1 z.2) (by intros; rfl)
  unfold SemialgebraicOn
  convert hb.inter hh using 1
  all_goals try with_reducible_and_instances rfl
  ext ⟨x,y⟩
  simp only [mem_inter_iff,mem_preimage,mem_ofPred_eq]
  constructor
  · rintro ⟨hx,rfl⟩
    exact ⟨hx,hf hx,(hgf _ hx).symm⟩
  · rintro ⟨hx,hy,he⟩
    exact ⟨hx,(hfg _ hy (he ▸ hx)).symm.trans (congrArg f he.symm)⟩

theorem affine_inverse_germ_semialgebraic {ι κ : Type*} [Fintype ι] [Fintype κ]
    {V : Set (κ → ℝ)} (hV : PolynomialSignSet id V)
    (f : (ι → ℝ) → (κ → ℝ)) (L : (κ → ℝ) →ₗ[ℝ] (ι → ℝ)) (b : ι → ℝ)
    (hf : ContinuousAt f 0)
    (hgf : ∀ᶠ x in 𝓝 (0 : ι → ℝ), L (f x) + b = x)
    (hfg : ∀ᶠ y in 𝓝[V] (f 0), f (L y + b) = y)
    (hfv : ∀ᶠ x in 𝓝 (0 : ι → ℝ), f x ∈ V) :
    ∃ r : ℝ, 0 < r ∧ SemialgebraicOn {x : ι → ℝ | ‖x‖ < r} f := by
  have hfg' := eventually_nhdsWithin_iff.mp hfg
  obtain ⟨ρ,hρ,hρfg⟩ := Metric.mem_nhds_iff.mp hfg'
  let T := V ∩ {y : κ → ℝ | ‖y-f 0‖ < ρ}
  have hT : PolynomialSignSet id T := hV.inter (polynomialSignSet_real_ball (f 0) ρ)
  have hnear : ∀ᶠ x in 𝓝 (0 : ι → ℝ), f x ∈ T := by
    have hh : ∀ᶠ x in 𝓝 (0 : ι → ℝ), f x ∈ Metric.ball (f 0) ρ :=
      hf.preimage_mem_nhds (Metric.ball_mem_nhds _ hρ)
    filter_upwards [hfv,hh] with x hx hx'
    exact ⟨hx,by simpa only [mem_ofPred_eq,Metric.mem_ball,dist_eq_norm] using hx'⟩
  obtain ⟨r,hr,hrinv⟩ := Metric.mem_nhds_iff.mp (hnear.and hgf)
  refine ⟨r,hr,?_⟩
  apply semialgebraicOn_inverse_restrict
    (by simpa only [sub_zero] using polynomialSignSet_real_ball (0 : ι → ℝ) r)
    (fun y => L y+b) (SemialgebraicOn.affine hT L b) f
  · intro x hx
    exact (hrinv (by simpa only [mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hx)).1
  · intro x hx
    exact (hrinv (by simpa only [mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hx)).2
  · intro y hy _
    exact hρfg (by simpa only [mem_ofPred_eq,Metric.mem_ball,dist_eq_norm] using hy.2) hy.1
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GenericNormalGraphProjection
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
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

lemma complexGraphRealEquiv_snd {r k : ℕ} (p : Affine r × Affine k) :
    (complexGraphRealEquiv r k p).2 = fun i => (p.2 i).im := rfl

theorem generic_normal_graph_projection_injective {r k d : ℕ}
    (M : (Fin d → ℝ) →L[ℝ] (Affine r × Affine k))
    (hM : Function.Injective M) (h0 : ∀ v i, ((M v).2 i).im = 0) :
    Function.Injective ((ContinuousLinearMap.fst ℝ (Fin ((r+r)+k) → ℝ) (Fin k → ℝ)).comp
      ((complexGraphRealEquiv r k).toContinuousLinearMap.comp M)) := by
  intro a b hab
  apply hM
  apply (complexGraphRealEquiv r k).injective
  apply Prod.ext hab
  change (complexGraphRealEquiv r k (M a)).2 = (complexGraphRealEquiv r k (M b)).2
  simp only [complexGraphRealEquiv_snd,h0]
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SemialgebraicAnalyticLocalInverse
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
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
open Set Filter Topology
open scoped Classical

theorem semialgebraic_projection_chart_germ {m N : ℕ} (V : Set (Affine N))
    (hV : IsSemialgebraic V)
    (F : Affine m → Affine N) (G : Affine N → Affine m)
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (F 0))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFG : ∀ᶠ y in 𝓝[V] (F 0), F (G y) = y)
    (hFV : ∀ᶠ z in 𝓝 (0 : Affine m), F z ∈ V) :
    ∃ (π : Affine N →L[ℂ] Affine m) (H : Affine m → Affine N),
      H 0 = F 0 ∧ AnalyticAt ℂ H 0 ∧
      (∀ᶠ z in 𝓝 (0 : Affine m), π (H z - F 0) = z) ∧
      (∀ᶠ y in 𝓝[V] (F 0), H (π (y-F 0)) = y) ∧
      (∀ᶠ z in 𝓝 (0 : Affine m), H z ∈ V) ∧
      ∃ r : ℝ, 0 < r ∧ SemialgebraicOn {x : Fin (m+m) → ℝ | ‖x‖ < r}
        (fun x => complexRealEquiv N (H ((complexRealEquiv m).symm x))) := by
  obtain ⟨π,H,h0,hH,hπH,hHπ,hHV⟩ := linear_projection_chart_germ V F G hF hG hGF hFG hFV
  refine ⟨π,H,h0,hH,hπH,hHπ,hHV,?_⟩
  let e := complexRealEquiv m
  let d := complexRealEquiv N
  let f := fun x => d (H (e.symm x))
  let L := e.toLinearMap.comp ((π.restrictScalars ℝ).toLinearMap.comp d.symm.toLinearMap)
  let b := -L (d (F 0))
  have hg (y : Fin (N+N) → ℝ) : L y+b = e (π (d.symm y-F 0)) := by
    simp [L,b,sub_eq_add_neg]
  have hef : Tendsto e.symm (𝓝 (0 : Fin (m+m) → ℝ)) (𝓝 (0 : Affine m)) := by
    simpa only [map_zero] using e.symm.continuous.tendsto 0
  have hfH : ContinuousAt (fun x => H (e.symm x)) (0 : Fin (m+m) → ℝ) := by
    apply ContinuousAt.comp_of_eq hH.continuousAt e.symm.continuous.continuousAt
    exact map_zero e.symm
  have hf : ContinuousAt f 0 := d.continuous.continuousAt.comp hfH
  apply affine_inverse_germ_semialgebraic (isSemialgebraic_real_image hV) f L b hf
  · filter_upwards [hef hπH] with x hx
    change π (H (e.symm x)-F 0) = e.symm x at hx
    rw [hg]
    simp only [f,d.symm_apply_apply,hx,e.apply_symm_apply]
  · have hd : Tendsto d.symm (𝓝[d '' V] (f 0)) (𝓝[V] (F 0)) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have hh := (d.symm.continuous.tendsto (f 0)).mono_left
          (nhdsWithin_le_nhds (s := d '' V))
        simpa only [f,map_zero,h0,d.symm_apply_apply] using hh
      · filter_upwards [self_mem_nhdsWithin] with y hy
        obtain ⟨z,hz,rfl⟩ := hy
        simpa only [d.symm_apply_apply] using hz
    filter_upwards [hd hHπ] with y hy
    rw [hg]
    change d (H (e.symm (e (π (d.symm y-F 0))))) = y
    rw [e.symm_apply_apply,hy,d.apply_symm_apply]
  · filter_upwards [hef hHV] with x hx
    exact ⟨_,hx,rfl⟩
end

open Set Filter Topology Metric
open scoped Classical

theorem semialgebraic_analytic_local_inverse {d n : ℕ}
    {B : Set (Fin d → ℝ)} (hB : IsOpen B)
    {f : (Fin d → ℝ) → (Fin n → ℝ)} (hfs : SemialgebraicOn B f)
    {x : Fin d → ℝ} (hx : x ∈ B) (hfa : AnalyticAt ℝ f x)
    (L : (Fin d → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (hd : HasFDerivAt f (L : (Fin d → ℝ) →L[ℝ] (Fin n → ℝ)) x) :
    ∃ e : OpenPartialHomeomorph (Fin d → ℝ) (Fin n → ℝ),
      (e : (Fin d → ℝ) → (Fin n → ℝ)) = f ∧ x ∈ e.source ∧
      ∃ r : ℝ, 0 < r ∧ ball (f x) r ⊆ e.target ∧
        MapsTo e.symm (ball (f x) r) B ∧
        AnalyticOnNhd ℝ e.symm (ball (f x) r) ∧
        SemialgebraicOn (ball (f x) r) e.symm := by
  obtain ⟨e,he,hes,hea⟩ := real_analytic_local_inverse hfa L hd
  have het : f x ∈ e.target := by simpa only [he] using e.map_source hes
  have heinv : e.symm (f x) = x := by simpa only [he] using e.left_inv hes
  obtain ⟨ρ,hρ,hρsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hB.mem_nhds hx) (e.open_source.mem_nhds hes))
  have hTs : PolynomialSignSet id (ball x ρ) := by
    simpa only [ball,dist_eq_norm] using polynomialSignSet_real_ball x ρ
  have hfgs : SemialgebraicOn (ball x ρ) f := hfs.mono hTs (fun y hy => (hρsub hy).1)
  have hl : ∀ᶠ y in 𝓝 (f x), e.symm y ∈ ball x ρ := by
    apply (by simpa only [heinv] using hea.continuousAt.tendsto : Tendsto e.symm (𝓝 (f x)) (𝓝 x))
    exact Metric.ball_mem_nhds _ hρ
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp
    (hl.and (Filter.Eventually.and (e.open_target.mem_nhds het) hea.eventually_analyticAt))
  refine ⟨e,he,hes,r,hr,fun y hy => (hrsub hy).2.1,
    fun y hy => (hρsub (hrsub hy).1).1,fun y hy => (hrsub hy).2.2,?_⟩
  apply semialgebraicOn_inverse_restrict
    (by simpa only [ball,dist_eq_norm] using polynomialSignSet_real_ball (f x) r)
    f hfgs e.symm
  · exact fun y hy => (hrsub hy).1
  · intro y hy
    have hh := e.right_inv (hrsub hy).2.1
    simpa only [he] using hh
  · intro y hy _
    have hh := e.left_inv (hρsub hy).2
    simpa only [he] using hh
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ComplexNashNormalGraph
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
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
open Set Filter Topology Metric
open scoped Classical

theorem complex_nash_normal_graph {d r k : ℕ}
    (B : Set (Fin d → ℝ)) (hB : IsOpen B)
    (q : (Fin d → ℝ) → Affine r × Affine k)
    (hqa : AnalyticOnNhd ℝ q B)
    (hqs : SemialgebraicOn B (fun x => (complexGraphRealEquiv r k (q x)).1))
    (hqn : SemialgebraicOn B (fun x => (complexGraphRealEquiv r k (q x)).2))
    {a : Fin d → ℝ} (ha : a ∈ B) (hq0 : q a = 0)
    (hdim : d = (r+r)+k) (hqi : Function.Injective (fderiv ℝ q a))
    (hqt : ∀ v i, (((fderiv ℝ q a) v).2 i).im = 0) :
    ∃ (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin ((r+r)+k) → ℝ))
      (R : ℝ) (φ : (Fin ((r+r)+k) → ℝ) → (Fin k → ℝ)),
      (e : (Fin d → ℝ) → _) = (fun x => (complexGraphRealEquiv r k (q x)).1) ∧
      a ∈ e.source ∧ e.symm 0 = a ∧ 0 < R ∧ ball 0 R ⊆ e.target ∧
      MapsTo e.symm (ball 0 R) B ∧
      AnalyticOnNhd ℝ e.symm (ball 0 R) ∧ SemialgebraicOn (ball 0 R) e.symm ∧
      AnalyticOnNhd ℝ φ (ball 0 R) ∧ SemialgebraicOn (ball 0 R) φ ∧
      φ 0 = 0 ∧ fderiv ℝ φ 0 = 0 ∧
      (∀ s ∈ ball 0 R, complexGraphRealEquiv r k (q (e.symm s)) = (s,φ s)) ∧
      (∀ᶠ x in 𝓝 a, e x ∈ ball 0 R ∧
        complexGraphRealEquiv r k (q x) = (e x,φ (e x))) := by
  let P := (ContinuousLinearMap.fst ℝ (Fin ((r+r)+k) → ℝ) (Fin k → ℝ)).comp
    (complexGraphRealEquiv r k).toContinuousLinearMap
  let Q := (ContinuousLinearMap.snd ℝ (Fin ((r+r)+k) → ℝ) (Fin k → ℝ)).comp
    (complexGraphRealEquiv r k).toContinuousLinearMap
  let f := P ∘ q
  let g := Q ∘ q
  have hf : AnalyticOnNhd ℝ f B := fun x hx => (P.analyticAt (q x)).comp (hqa x hx)
  have hg : AnalyticOnNhd ℝ g B := fun x hx => (Q.analyticAt (q x)).comp (hqa x hx)
  have hf0 : f a = 0 := by change P (q a) = 0; rw [hq0,map_zero]
  have hg0 : g a = 0 := by change Q (q a) = 0; rw [hq0,map_zero]
  let A := P.comp (fderiv ℝ q a)
  have hi : Function.Injective A := generic_normal_graph_projection_injective
    (fderiv ℝ q a) hqi hqt
  let L := (A.toLinearMap.linearEquivOfInjective hi (by simp [hdim])).toContinuousLinearEquiv
  have heL : (L : (Fin d → ℝ) →L[ℝ] (Fin ((r+r)+k) → ℝ)) = A := by ext v i; rfl
  have hfd : HasFDerivAt f A a := P.hasFDerivAt.comp a (hqa a ha).differentiableAt.hasFDerivAt
  obtain ⟨e,he,hes,R,hR,hRt,hRB,hea,hesa⟩ :=
    semialgebraic_analytic_local_inverse hB hqs ha (hf a ha) L (heL.symm ▸ hfd)
  simp only [hq0,map_zero,Prod.fst_zero] at hRt hRB hea hesa
  have hein : e.symm 0 = a := by
    have hh := e.left_inv hes
    change e.symm ((e : (Fin d → ℝ) → _) a) = a at hh
    rw [he,show (fun x => (complexGraphRealEquiv r k (q x)).1) = f from rfl,hf0] at hh
    exact hh
  let φ := g ∘ e.symm
  have hφa : AnalyticOnNhd ℝ φ (ball 0 R) :=
    fun s hs => (hg _ (hRB hs)).comp (hea s hs)
  have hφs : SemialgebraicOn (ball 0 R) φ := hqn.comp hesa hRB
  have hQ : Q.comp (fderiv ℝ q a) = 0 := by
    ext v i
    exact hqt v i
  have hgd : HasFDerivAt g (0 : (Fin d → ℝ) →L[ℝ] (Fin k → ℝ)) a := by
    have hh := Q.hasFDerivAt.comp a (hqa a ha).differentiableAt.hasFDerivAt
    rwa [hQ] at hh
  have hder : fderiv ℝ φ 0 = 0 := by
    have hh := (hein.symm ▸ hgd).comp 0 (hea 0 (mem_ball_self hR)).differentiableAt.hasFDerivAt
    exact hh.fderiv
  have hgraph : ∀ s ∈ ball 0 R, complexGraphRealEquiv r k (q (e.symm s)) = (s,φ s) := by
    intro s hs
    apply Prod.ext
    · have hh := e.right_inv (hRt hs)
      simpa only [he] using hh
    · rfl
  refine ⟨e,R,φ,he,hes,hein,hR,hRt,hRB,hea,hesa,hφa,hφs,?_,hder,hgraph,?_⟩
  · change g (e.symm 0) = 0
    rw [hein,hg0]
  · have hnear : ∀ᶠ x in 𝓝 a, e x ∈ ball 0 R := by
      have hec : ContinuousAt (e : (Fin d → ℝ) → _) a := e.continuousAt hes
      have he0 : e a = 0 := by rw [he]; exact hf0
      apply hec.preimage_mem_nhds
      rw [he0]
      exact ball_mem_nhds _ hR
    filter_upwards [hnear,e.open_source.mem_nhds hes] with x hx hxs
    refine ⟨hx,?_⟩
    have hh := hgraph (e x) hx
    simpa only [e.left_inv hxs] using hh
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CoordinateDerivativeRank
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
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

theorem complex_span_real_linear_range {d N : ℕ}
    (L : (Fin d → ℝ) →ₗ[ℝ] (Fin N → ℂ)) :
    Submodule.span ℂ (range L) =
      Submodule.span ℂ (range (fun i => L (Pi.single i 1))) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    have hx : x = ∑ i : Fin d, x i • Pi.single i (1 : ℝ) := by
      ext j
      simp [Pi.single_apply]
    rw [hx,map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    change ((x i : ℂ) • L (Pi.single i 1)) ∈ _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i))
  · apply Submodule.span_mono
    rintro _ ⟨i,rfl⟩
    exact mem_range_self _

theorem matrix_rank_eq_complex_tangent_dimension {d N : ℕ}
    (L : (Fin d → ℝ) →ₗ[ℝ] (Fin N → ℂ)) :
    Matrix.rank (fun j i => L (Pi.single i 1) j) =
      Module.finrank ℂ (Submodule.span ℂ (range L)) := by
  rw [complex_span_real_linear_range L]
  exact Matrix.rank_eq_finrank_span_cols _

theorem complex_tangent_eq_of_rank_ge {d N m : ℕ}
    (L : (Fin d → ℝ) →ₗ[ℝ] (Fin N → ℂ))
    (T : Submodule ℂ (Fin N → ℂ)) (hT : Module.finrank ℂ T = m)
    (hLT : ∀ x, L x ∈ T)
    (hr : m ≤ Matrix.rank (fun j i => L (Pi.single i 1) j)) :
    Submodule.span ℂ (range L) = T := by
  have hle : Submodule.span ℂ (range L) ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    exact hLT x
  apply Submodule.eq_of_le_of_finrank_eq hle
  apply Nat.le_antisymm (Submodule.finrank_mono hle)
  simpa only [matrix_rank_eq_complex_tangent_dimension,hT] using hr

theorem chart_tangent_finrank {m N : ℕ}
    (F : (Fin m → ℂ) → (Fin N → ℂ))
    (G : (Fin N → ℂ) → (Fin m → ℂ)) {a : Fin m → ℂ}
    (hF : AnalyticAt ℂ F a) (hG : AnalyticAt ℂ G (F a))
    (hGF : (G ∘ F) =ᶠ[𝓝 a] id) :
    Module.finrank ℂ (LinearMap.range (fderiv ℂ F a).toLinearMap) = m := by
  have hcomp := hG.differentiableAt.hasFDerivAt.comp a hF.differentiableAt.hasFDerivAt
  have hid := hcomp.congr_of_eventuallyEq hGF.symm
  have hi : (fderiv ℂ G (F a)).comp (fderiv ℂ F a) = ContinuousLinearMap.id ℂ _ :=
    hid.unique (hasFDerivAt_id a)
  have hinj : Function.Injective (fderiv ℂ F a) := by
    intro x y hxy
    have hh := congrArg (fderiv ℂ G (F a)) hxy
    simpa only [← ContinuousLinearMap.comp_apply,hi,ContinuousLinearMap.id_apply] using hh
  simpa using LinearMap.finrank_range_of_inj (f := (fderiv ℂ F a).toLinearMap) hinj

theorem real_derivative_mem_chart_tangent {d m N : ℕ}
    (F : (Fin m → ℂ) → (Fin N → ℂ))
    (G : (Fin N → ℂ) → (Fin m → ℂ))
    (q : (Fin d → ℝ) → (Fin N → ℂ)) {x : Fin d → ℝ}
    (hF : AnalyticAt ℂ F (G (q x))) (hG : AnalyticAt ℂ G (q x))
    (hq : DifferentiableAt ℝ q x)
    (hFG : (F ∘ G ∘ q) =ᶠ[𝓝 x] q) (v : Fin d → ℝ) :
    fderiv ℝ q x v ∈ LinearMap.range (fderiv ℂ F (G (q x))).toLinearMap := by
  have hGc := hG.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hFc := hF.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hc := hFc.comp x (hGc.comp x hq.hasFDerivAt)
  have he := hc.congr_of_eventuallyEq hFG.symm
  have hd := he.fderiv
  refine ⟨fderiv ℂ G (q x) (fderiv ℝ q x v),?_⟩
  exact (congrArg (fun L : (Fin d → ℝ) →L[ℝ] (Fin N → ℂ) => L v) hd).symm

theorem coordinate_derivative_rank {d N : ℕ}
    (q : (Fin d → ℝ) → (Fin N → ℂ)) {x : Fin d → ℝ}
    (hq : DifferentiableAt ℝ q x) :
    Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)) =
      Module.finrank ℂ (Submodule.span ℂ (range (fderiv ℝ q x))) := by
  have he (j : Fin N) : fderiv ℝ (fun y => q y j) x =
      (ContinuousLinearMap.proj j).comp (fderiv ℝ q x) := by
    exact ((ContinuousLinearMap.proj j).hasFDerivAt.comp x hq.hasFDerivAt).fderiv
  simp_rw [he,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
  exact matrix_rank_eq_complex_tangent_dimension (fderiv ℝ q x).toLinearMap

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_HolomorphicSupportIndependent
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

section
open Set
open scoped Classical

theorem complex_independent_of_generic_real_conormals
    {E ι : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E]
    [IsScalarTower ℝ ℂ E] [Fintype ι]
    (S : Set E) (hS : Submodule.span ℂ S = ⊤)
    (l : ι → E →ₗ[ℂ] ℂ)
    (hz : ∀ i, ∀ x ∈ S, (l i x).re = 0)
    (hi : LinearIndependent ℝ
      (fun i => Complex.reCLM.toLinearMap.comp ((l i).restrictScalars ℝ))) :
    LinearIndependent ℂ l := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  let B : E →ₗ[ℂ] ℂ := ∑ i, (c i).im • l i
  have hBS : S ⊆ LinearMap.ker B := by
    intro x hx
    have hr : (B x).re = 0 := by
      simp [B,LinearMap.sum_apply,LinearMap.smul_apply,hz _ x hx]
    have hh := congrArg (fun f : E →ₗ[ℂ] ℂ => (f x).re) hc
    have him : (B x).im = 0 := by
      simp only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,Complex.re_sum,
        Complex.mul_re,hz _ x hx,mul_zero,zero_sub,Finset.sum_neg_distrib,
        LinearMap.zero_apply,Complex.zero_re,neg_eq_zero] at hh
      simpa [B,LinearMap.sum_apply,LinearMap.smul_apply,Complex.smul_im] using hh
    exact Complex.ext hr him
  have hB : B = 0 := by
    apply LinearMap.ker_eq_top.mp
    apply top_unique
    rw [← hS]
    exact Submodule.span_le.mpr hBS
  have hbi : ∑ i, (c i).im •
      (Complex.reCLM.toLinearMap.comp ((l i).restrictScalars ℝ)) = 0 := by
    ext x
    have hh := congrArg (fun f : E →ₗ[ℂ] ℂ => (f x).re) hB
    simpa [B,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,
      Complex.smul_re] using hh
  have hci := Fintype.linearIndependent_iff.mp hi (fun i => (c i).im) hbi
  have hbr : ∑ i, (c i).re •
      (Complex.reCLM.toLinearMap.comp ((l i).restrictScalars ℝ)) = 0 := by
    ext x
    have hh := congrArg (fun f : E →ₗ[ℂ] ℂ => (f x).re) hc
    simpa [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,
      Complex.mul_re,hci] using hh
  have hcr := Fintype.linearIndependent_iff.mp hi (fun i => (c i).re) hbr
  intro i
  exact Complex.ext (hcr i) (hci i)
end

open Set Filter Topology
open scoped Classical

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GenericTangentComplexNormal
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
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
open Set
open scoped Classical

theorem independent_functionals_surjective {𝕜 E ι : Type*} [Field 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E] [Fintype ι]
    (l : ι → Module.Dual 𝕜 E) (hi : LinearIndependent 𝕜 l) :
    Function.Surjective (LinearMap.pi l) := by
  classical
  have hexp (L : Module.Dual 𝕜 (ι → 𝕜)) (v : ι → 𝕜) :
      L v = ∑ i, v i * L (Pi.single i 1) := by
    have hv : v = ∑ i : ι, v i • Pi.single i (1 : 𝕜) := by
      ext i
      simp [Pi.single_apply]
    conv_lhs => rw [hv]
    simp only [map_sum,map_smul,smul_eq_mul]
  apply LinearMap.dualMap_injective_iff.mp
  intro L Q hLQ
  have hzero : ∑ i, (L-Q) (Pi.single i 1) • l i = 0 := by
    ext x
    have he := congrArg (fun D : Module.Dual 𝕜 E => D x) hLQ
    change L (fun i => l i x) = Q (fun i => l i x) at he
    have hz : (L-Q) (fun i => l i x) = 0 := sub_eq_zero.mpr he
    rw [hexp] at hz
    simpa only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,
      mul_comm,LinearMap.zero_apply] using hz
  have hc := Fintype.linearIndependent_iff.mp hi _ hzero
  apply LinearMap.ext
  intro v
  apply sub_eq_zero.mp
  change (L-Q) v = 0
  rw [hexp]
  simp only [hc,mul_zero,Finset.sum_const_zero]

theorem exists_scalar_continuousLinearEquiv_prod_ker
    {𝕜 E X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X]
    (A : E →L[𝕜] X) (hA : Function.Surjective A) :
    ∃ e : E ≃L[𝕜] X × LinearMap.ker A.toLinearMap, ∀ v, (e v).1 = A v := by
  obtain ⟨R,hR⟩ := ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hA
  let K := LinearMap.ker A.toLinearMap
  let L : E →ₗ[𝕜] X × K :=
    { toFun := fun v => (A v,⟨v-R (A v),by change A (v-R (A v)) = 0; rw [map_sub,hR,sub_self]⟩)
      map_add' := by intro v w; ext <;> simp [map_add]; abel
      map_smul' := by intro c v; ext <;> simp [map_smul,smul_sub] }
  have hinj : Function.Injective L := by
    intro v w he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg (fun p : X × K => (p.2 : E)) he
    change A v = A w at h1
    change v-R (A v) = w-R (A w) at h2
    rw [h1] at h2
    exact sub_left_injective h2
  have hsurj : Function.Surjective L := by
    rintro ⟨x,k⟩
    refine ⟨R x+k,?_⟩
    have hk : A k = 0 := k.property
    have ha : A (R x+k) = x := by rw [map_add,hR,hk,add_zero]
    apply Prod.ext
    · exact ha
    · apply Subtype.ext
      change R x+(k : E)-R (A (R x+k)) = k
      rw [ha]
      abel
  exact ⟨(LinearEquiv.ofBijective L ⟨hinj,hsurj⟩).toContinuousLinearEquiv,fun _ => rfl⟩

lemma submodule_basis_independent {𝕜 E ι : Type*} [Field 𝕜]
    [AddCommGroup E] [Module 𝕜 E] (S : Submodule 𝕜 E)
    (b : Module.Basis ι 𝕜 S) : LinearIndependent 𝕜 (fun i => (b i : E)) := by
  exact b.linearIndependent.map' S.subtype (Submodule.ker_subtype S)

lemma real_conormal_basis_complex_independent {n k : ℕ}
    (S : Submodule ℝ (Affine n)) (hS : Submodule.span ℂ (S : Set (Affine n)) = ⊤)
    (b : Module.Basis (Fin k) ℝ ↥S.dualAnnihilator) :
    LinearIndependent ℂ (fun i => (b i).val.extendRCLike (𝕜 := ℂ)) := by
  have hreal (i : Fin k) : Complex.reCLM.toLinearMap.comp
      (((b i).val.extendRCLike (𝕜 := ℂ)).restrictScalars ℝ) = (b i).val := by
    apply LinearMap.ext
    intro x
    exact Module.Dual.re_extendRCLike_apply (𝕜 := ℂ) (b i).val x
  apply complex_independent_of_generic_real_conormals (S : Set (Affine n)) hS
    (fun i => (b i).val.extendRCLike)
  · intro i x hx
    exact (Module.Dual.re_extendRCLike_apply (𝕜 := ℂ) (b i).val x).trans
      ((Submodule.mem_dualAnnihilator _).mp (b i).property x hx)
  · have hb := submodule_basis_independent S.dualAnnihilator b
    simpa only [hreal] using hb

lemma real_conormal_basis_vanishing_iff {n k : ℕ}
    (S : Submodule ℝ (Affine n))
    (b : Module.Basis (Fin k) ℝ ↥S.dualAnnihilator) (x : Affine n) :
    x ∈ S ↔ ∀ i, (b i).val x = 0 := by
  constructor
  · intro hx i
    exact (Submodule.mem_dualAnnihilator _).mp (b i).property x hx
  · intro h
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := S)]
    apply (Submodule.mem_dualCoannihilator _).mpr
    intro Q hQ
    let q : S.dualAnnihilator := ⟨Q,hQ⟩
    have heq := b.sum_repr q
    have heq' := congrArg (fun v : S.dualAnnihilator => v.val x) heq
    simpa only [Submodule.coe_sum,Submodule.coe_smul_of_tower,
      LinearMap.sum_apply,LinearMap.smul_apply,h,smul_zero,Finset.sum_const_zero] using heq'.symm

theorem generic_tangent_complex_normal_form {n : ℕ}
    (S : Submodule ℝ (Affine n)) (hS : Submodule.span ℂ (S : Set (Affine n)) = ⊤) :
    ∃ r : ℕ, ∃ e : Affine n ≃L[ℂ]
      (Affine r × Affine (Module.finrank ℝ S.dualAnnihilator)),
      r + Module.finrank ℝ S.dualAnnihilator = n ∧
      ∀ x, x ∈ S ↔ ∀ i, ((e x).2 i).im = 0 := by
  let _ : Module.Free ℝ ↥S.dualAnnihilator := Module.Free.of_divisionRing ℝ ↥S.dualAnnihilator
  let k := Module.finrank ℝ S.dualAnnihilator
  let b : Module.Basis (Fin k) ℝ ↥S.dualAnnihilator := Module.finBasis ℝ ↥S.dualAnnihilator
  let l : Fin k → Module.Dual ℂ (Affine n) := fun i => (b i).val.extendRCLike
  have hi : LinearIndependent ℂ l := real_conormal_basis_complex_independent S hS b
  let L : Affine n →L[ℂ] Affine k := (LinearMap.pi l).toContinuousLinearMap
  let A : Affine n →L[ℂ] Affine k := Complex.I • L
  have hA : Function.Surjective A := by
    intro y
    obtain ⟨x,hx⟩ := independent_functionals_surjective l hi ((-Complex.I) • y)
    refine ⟨x,?_⟩
    change Complex.I • L x = y
    change L x = (-Complex.I) • y at hx
    rw [hx,smul_smul]
    simp
  obtain ⟨e,he⟩ := exists_scalar_continuousLinearEquiv_prod_ker A hA
  let r := Module.finrank ℂ (LinearMap.ker A.toLinearMap)
  let c : LinearMap.ker A.toLinearMap ≃L[ℂ] Affine r :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [r,Affine])
  let f := (e.trans ((ContinuousLinearEquiv.refl ℂ (Affine k)).prodCongr c)).trans
    (ContinuousLinearEquiv.prodComm ℂ (Affine k) (Affine r))
  have hf (x : Affine n) : (f x).2 = A x := he x
  have hdim : r+k=n := by
    have hh := f.toLinearEquiv.finrank_eq
    simpa only [Module.finrank_prod,Affine,Module.finrank_pi,
      Fintype.card_fin] using hh.symm
  refine ⟨r,f,hdim,?_⟩
  intro x
  have hx (i : Fin k) : ((f x).2 i).im = (b i).val x := by
    rw [hf]
    change (Complex.I * l i x).im = (b i).val x
    simp only [Complex.I_mul_im]
    exact Module.Dual.re_extendRCLike_apply (𝕜 := ℂ) (b i).val x
  simp only [hx]
  exact real_conormal_basis_vanishing_iff S b x
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_NashCellGeometricRank
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

section
open Set Filter Topology

theorem real_parametric_span_eq_chart_of_rank_ge {d m N : ℕ}
    (F : (Fin m → ℂ) → (Fin N → ℂ))
    (G : (Fin N → ℂ) → (Fin m → ℂ))
    (q : (Fin d → ℝ) → (Fin N → ℂ)) {x : Fin d → ℝ}
    (hF0 : F 0 = q x) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hq : DifferentiableAt ℝ q x)
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Fin m → ℂ)] id)
    (hFG : (F ∘ G ∘ q) =ᶠ[𝓝 x] q)
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1))) :
    Submodule.span ℂ (range (fderiv ℝ q x)) =
      LinearMap.range (fderiv ℂ F 0).toLinearMap := by
  have hG0 : G (q x) = 0 := by
    simpa only [Function.comp_apply,hF0,Function.id_def] using hGF.eq_of_nhds
  apply complex_tangent_eq_of_rank_ge (fderiv ℝ q x).toLinearMap
    (LinearMap.range (fderiv ℂ F 0).toLinearMap)
  · exact chart_tangent_finrank F G hF (hF0 ▸ hG) hGF
  · intro v
    have hv := real_derivative_mem_chart_tangent F G q (hG0 ▸ hF) hG hq hFG v
    change fderiv ℝ q x v ∈ _
    simpa only [hG0] using hv
  · rw [matrix_rank_eq_complex_tangent_dimension]
    rwa [coordinate_derivative_rank q hq] at hr

end

open Set Filter Topology MeasureTheory

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_InjectiveConormalFinrank
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
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

theorem chart_tangent_identities {d m N : ℕ}
    (F : Affine m → Affine N) (G : Affine N → Affine m)
    (q : (Fin d → ℝ) → Affine N) {x : Fin d → ℝ}
    (hF0 : F 0 = q x) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hq : DifferentiableAt ℝ q x)
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFG : (F ∘ G ∘ q) =ᶠ[𝓝 x] q) :
    G (q x) = 0 ∧
    (fderiv ℂ G (q x)).comp (fderiv ℂ F 0) = ContinuousLinearMap.id ℂ _ ∧
    ((fderiv ℂ F 0).restrictScalars ℝ).comp (fderiv ℝ (G ∘ q) x) = fderiv ℝ q x ∧
    Function.Injective (fderiv ℂ F 0) := by
  have hG0 : G (q x) = 0 := by
    simpa only [Function.comp_apply,hF0,Function.id_def] using hGF.eq_of_nhds
  have hg : AnalyticAt ℂ G (F 0) := hF0 ▸ hG
  have hid := (hg.differentiableAt.hasFDerivAt.comp 0 hF.differentiableAt.hasFDerivAt).congr_of_eventuallyEq hGF.symm
  have hi : (fderiv ℂ G (q x)).comp (fderiv ℂ F 0) = ContinuousLinearMap.id ℂ _ := by
    simpa only [hF0] using hid.unique (hasFDerivAt_id (0 : Affine m))
  refine ⟨hG0,hi,?_,?_⟩
  · have hr : DifferentiableAt ℝ (G ∘ q) x := hG.differentiableAt.restrictScalars ℝ |>.comp x hq
    have hf : AnalyticAt ℂ F ((G ∘ q) x) := by simpa only [Function.comp_apply,hG0] using hF
    have hh := (hf.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp x hr.hasFDerivAt
    have he := hh.congr_of_eventuallyEq hFG.symm
    simpa only [Function.comp_apply,hG0] using he.fderiv.symm
  · intro a b hab
    have hh := congrArg (fderiv ℂ G (q x)) hab
    simpa only [← ContinuousLinearMap.comp_apply,hi,ContinuousLinearMap.id_apply] using hh

theorem chart_parametric_generic {d m N : ℕ}
    (F : Affine m → Affine N) (G : Affine N → Affine m)
    (q : (Fin d → ℝ) → Affine N) {x : Fin d → ℝ}
    (hF0 : F 0 = q x) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hq : DifferentiableAt ℝ q x) (hqi : Function.Injective (fderiv ℝ q x))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFG : (F ∘ G ∘ q) =ᶠ[𝓝 x] q)
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1))) :
    Function.Injective (fderiv ℝ (G ∘ q) x) ∧
    Submodule.span ℂ (range (fderiv ℝ (G ∘ q) x)) = ⊤ := by
  obtain ⟨hG0,hi,hd,hFi⟩ := chart_tangent_identities F G q hF0 hF hG hq hGF hFG
  have hspan := real_parametric_span_eq_chart_of_rank_ge F G q hF0 hF hG hq hGF hFG hr
  have hder : fderiv ℝ (G ∘ q) x = ((fderiv ℂ G (q x)).restrictScalars ℝ).comp (fderiv ℝ q x) :=
    ((hG.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp x hq.hasFDerivAt).fderiv
  refine ⟨?_,?_⟩
  · intro a b hab
    apply hqi
    rw [← hd]
    exact congrArg ((fderiv ℂ F 0).restrictScalars ℝ) hab
  · let W := Submodule.span ℂ (range (fderiv ℝ (G ∘ q) x))
    have hle : Submodule.span ℂ (range (fderiv ℝ q x)) ≤
        W.comap (fderiv ℂ G (q x)).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨v,rfl⟩
      change fderiv ℂ G (q x) (fderiv ℝ q x v) ∈ W
      have he : fderiv ℂ G (q x) (fderiv ℝ q x v) = fderiv ℝ (G ∘ q) x v := by
        rw [hder]; rfl
      rw [he]
      exact Submodule.subset_span (mem_range_self v)
    apply top_unique
    intro v _
    have hv : fderiv ℂ F 0 v ∈ Submodule.span ℂ (range (fderiv ℝ q x)) := by
      rw [hspan]; exact ⟨v,rfl⟩
    have hh := hle hv
    change fderiv ℂ G (q x) (fderiv ℂ F 0 v) ∈ W at hh
    simpa only [← ContinuousLinearMap.comp_apply,hi,ContinuousLinearMap.id_apply] using hh

theorem injective_conormal_finrank {d m : ℕ}
    (M : (Fin d → ℝ) →L[ℝ] Affine m) (hM : Function.Injective M) :
    d + Module.finrank ℝ (LinearMap.range M.toLinearMap).dualAnnihilator = 2*m := by
  have hr : Module.finrank ℝ (LinearMap.range M.toLinearMap) = d := by
    simpa using LinearMap.finrank_range_of_inj (f := M.toLinearMap) hM
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range M.toLinearMap)
  simpa [hr,Affine,Module.finrank_pi_fintype,Nat.mul_comm] using h
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GenericNashNormalCoordinates
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
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
open Set Filter Topology Metric
open scoped Classical

theorem generic_nash_normal_coordinates {d m : ℕ}
    (B : Set (Fin d → ℝ)) (hB : IsOpen B)
    (q : (Fin d → ℝ) → Affine m) (hqa : AnalyticOnNhd ℝ q B)
    (hqs : SemialgebraicOn B (fun x => complexRealEquiv m (q x)))
    {a : Fin d → ℝ} (ha : a ∈ B)
    (hqi : Function.Injective (fderiv ℝ q a))
    (hqg : Submodule.span ℂ (range (fderiv ℝ q a)) = ⊤) :
    Nonempty (NashNormalCoordinates B q a) := by
  let S := LinearMap.range (fderiv ℝ q a).toLinearMap
  let k := Module.finrank ℝ S.dualAnnihilator
  obtain ⟨r,e,he,het⟩ := generic_tangent_complex_normal_form S hqg
  have hdk : d+k=2*m := injective_conormal_finrank (fderiv ℝ q a) hqi
  have hdr : d=(r+r)+k := by omega
  let er := e.toContinuousLinearMap.restrictScalars ℝ
  let u := fun x => e (q x-q a)
  have hua : AnalyticOnNhd ℝ u B := by
    intro x hx
    have hs : AnalyticAt ℝ (fun y => q y-q a) x := (hqa x hx).sub analyticAt_const
    exact (er.analyticAt (q x-q a)).comp (f := fun y => q y-q a) hs
  have hu0 : u a = 0 := by simp only [u,sub_self,map_zero]
  have hud : HasFDerivAt u (er.comp (fderiv ℝ q a)) a := by
    have hs : HasFDerivAt (fun x => q x-q a) (fderiv ℝ q a) a :=
      (hqa a ha).differentiableAt.hasFDerivAt.sub_const (q a)
    exact er.hasFDerivAt.comp a hs
  have hui : Function.Injective (fderiv ℝ u a) := by
    rw [hud.fderiv]
    exact e.injective.comp hqi
  have hut : ∀ v i, (((fderiv ℝ u a) v).2 i).im = 0 := by
    intro v i
    rw [hud.fderiv]
    exact (het ((fderiv ℝ q a) v)).mp ⟨v,rfl⟩ i
  let L := (complexGraphRealEquiv r k).toContinuousLinearMap.comp
    (er.comp (complexRealEquiv m).symm.toContinuousLinearMap)
  let P := (ContinuousLinearMap.fst ℝ (Fin ((r+r)+k) → ℝ) (Fin k → ℝ)).comp L
  let Q := (ContinuousLinearMap.snd ℝ (Fin ((r+r)+k) → ℝ) (Fin k → ℝ)).comp L
  have hPs : SemialgebraicOn B (fun x => (complexGraphRealEquiv r k (u x)).1) := by
    have hh := (SemialgebraicOn.affine PolynomialSignSet.univ P.toLinearMap
      (-P (complexRealEquiv m (q a)))).comp hqs (fun _ _ => mem_univ _)
    apply hh.congr
    intro x _
    simp [P,L,u,er,sub_eq_add_neg]
  have hQs : SemialgebraicOn B (fun x => (complexGraphRealEquiv r k (u x)).2) := by
    have hh := (SemialgebraicOn.affine PolynomialSignSet.univ Q.toLinearMap
      (-Q (complexRealEquiv m (q a)))).comp hqs (fun _ _ => mem_univ _)
    apply hh.congr
    intro x _
    simp [Q,L,u,er,sub_eq_add_neg]
  obtain ⟨p,R,φ,hp,hps,hp0,hR,hRt,hRB,hia,his,hφa,hφs,hφ0,hφd,hgr,hlgr⟩ :=
    complex_nash_normal_graph B hB u hua hPs hQs ha hu0 hdr hui hut
  exact ⟨⟨r,k,he,hdr,e,p,R,hR,φ,hp,hps,hp0,hRt,hRB,hia,his,hφa,hφs,hφ0,hφd,hgr,hlgr⟩⟩
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ProjectionNashChartGerms
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
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
open Set Filter Topology

theorem inverse_germ_boundary_transfer {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (U V : Set Y) (hUV : U ⊆ V) (hV : IsClosed V)
    (F : X → Y) (G : Y → X) (hG : Continuous G) (p : Y)
    (hFG : ∀ᶠ y in 𝓝[V] p, F (G y) = y)
    (T : Set X) (hT : IsOpen T) (hpT : G p ∈ T) :
    ∃ W : Set Y, IsOpen W ∧ p ∈ W ∧
      ∀ y ∈ (closure U \ U) ∩ W,
        G y ∈ (closure (T ∩ F ⁻¹' U) \ (T ∩ F ⁻¹' U)) ∧
        G y ∈ T ∧ F (G y) = y := by
  have hfg := eventually_nhdsWithin_iff.mp hFG
  have hgt : ∀ᶠ y in 𝓝 p, G y ∈ T :=
    hG.continuousAt.preimage_mem_nhds (hT.mem_nhds hpT)
  obtain ⟨W,hW,hWo,hpW⟩ := mem_nhds_iff.mp (hfg.and hgt)
  refine ⟨W,hWo,hpW,?_⟩
  intro y hy
  have hyV : y ∈ V := closure_minimal hUV hV hy.1.1
  have hgy : F (G y) = y := (hW hy.2).1 hyV
  have hym : y ∈ closure (W ∩ U) := hWo.inter_closure ⟨hy.2,hy.1.1⟩
  have hmap : MapsTo G (W ∩ U) (T ∩ F ⁻¹' U) := by
    intro z hz
    exact ⟨(hW hz.1).2,by change F (G z) ∈ U; rw [(hW hz.1).1 (hUV hz.2)]; exact hz.2⟩
  refine ⟨⟨hG.continuousAt.continuousWithinAt.mem_closure hym hmap,?_⟩,
    (hW hy.2).2,hgy⟩
  intro hz
  apply hy.1.2
  simpa only [mem_preimage,hgy] using hz.2

theorem semialgebraic_nash_chart_preimage {m N : ℕ}
    {U : Set (Affine N)} (hU : IsSemialgebraic U)
    {B : Set (Fin (m+m) → ℝ)} (H : Affine m → Affine N)
    (hH : SemialgebraicOn B
      (fun x => complexRealEquiv N (H ((complexRealEquiv m).symm x)))) :
    PolynomialSignSet id (B ∩ (fun x => H ((complexRealEquiv m).symm x)) ⁻¹' U) := by
  convert hH.preimage (isSemialgebraic_real_image hU) using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_inter_iff,mem_preimage,mem_image]
  constructor
  · rintro ⟨hx,hy⟩
    exact ⟨hx,_,hy,rfl⟩
  · rintro ⟨hx,y,hy,he⟩
    exact ⟨hx,(complexRealEquiv N).injective he ▸ hy⟩
end

open Set Filter Topology Metric
open scoped Classical

theorem projection_nash_chart_of_germs {m N : ℕ} (V : Set (Affine N))
    (hV : IsSemialgebraic V) (F : Affine m → Affine N) (G : Affine N → Affine m)
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (F 0))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFG : ∀ᶠ y in 𝓝[V] (F 0), F (G y) = y)
    (hFV : ∀ᶠ z in 𝓝 (0 : Affine m), F z ∈ V) :
    Nonempty (ProjectionNashChart V (F 0) m) := by
  obtain ⟨π,H,h0,hH,hπH,hHπ,hHV,r,hr,hHs⟩ :=
    semialgebraic_projection_chart_germ V hV F G hF hG hGF hFG hFV
  have ht : Tendsto (complexRealEquiv m).symm (𝓝 (0 : Fin (m+m) → ℝ)) (𝓝 0) := by
    simpa only [map_zero] using (complexRealEquiv m).symm.continuous.tendsto 0
  have hn := ht (hH.eventually_analyticAt.and (hπH.and hHV))
  obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp hn
  let ρ := min r R
  have hρ : 0 < ρ := lt_min hr hR
  have hρsub {z : Affine m} (hz : ‖complexRealEquiv m z‖ < ρ) :
      AnalyticAt ℂ H z ∧ π (H z-F 0) = z ∧ H z ∈ V := by
    have hh := hsub (show complexRealEquiv m z ∈ ball 0 R from by
      simpa only [mem_ball,dist_zero_right] using lt_of_lt_of_le hz (min_le_right r R))
    simpa only [mem_preimage,mem_ofPred_eq,ContinuousLinearEquiv.symm_apply_apply] using hh
  refine ⟨⟨π,H,ρ,hρ,h0,(fun z hz => (hρsub hz).1),?_,
    (fun z hz => (hρsub hz).2.1),hHπ,(fun z hz => (hρsub hz).2.2)⟩⟩
  exact hHs.mono (by simpa only [sub_zero] using polynomialSignSet_real_ball (0 : Fin (m+m) → ℝ) ρ)
    (fun _ hz => lt_of_lt_of_le hz (min_le_left r R))
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_NashNormalGraphBoundary
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
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
open Set Filter Topology MeasureTheory
open scoped Classical

theorem locally_null_bad_set {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] (μ : Measure X) (A : Set X) (P : X → Prop)
    (h : ∀ x ∈ A, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ μ {y | y ∈ A ∧ y ∈ W ∧ ¬ P y} = 0) :
    μ {y | y ∈ A ∧ ¬ P y} = 0 := by
  choose W hWo hxW hn using fun x : A => h x.val x.property
  obtain ⟨C,hCc,hCov⟩ := (HereditarilyLindelofSpace.isLindelof A).elim_countable_subcover W hWo (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxW ⟨x,hx⟩⟩)
  have hnull : μ (⋃ x ∈ C, {y | y ∈ A ∧ y ∈ W x ∧ ¬ P y}) = 0 :=
    measure_biUnion_null_iff hCc |>.mpr (fun x _ => hn x)
  apply measure_mono_null _ hnull
  intro y hy
  obtain ⟨x,hx,hxy⟩ := mem_iUnion₂.mp (hCov hy.1)
  exact mem_iUnion₂.mpr ⟨x,hx,hy.1,hxy,hy.2⟩
end

open Set Filter Topology Metric
open scoped Classical

lemma polynomialSignSet_linear_product_preimage {a b c : ℕ}
    {S : Set (Fin c → ℝ)} (hS : PolynomialSignSet id S)
    (L : ((Fin a → ℝ) × (Fin b → ℝ)) →ₗ[ℝ] (Fin c → ℝ)) :
    PolynomialSignSet (fun z => Sum.elim z.1 z.2) (L ⁻¹' S) := by
  let e := LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) ℝ ℝ
  have hh := (SemialgebraicOn.affine PolynomialSignSet.univ (L.comp e.toLinearMap) 0).preimage hS
  simp only [univ_inter,add_zero] at hh
  exact hh.coordinate_preimage (fun z : (Fin a → ℝ) × (Fin b → ℝ) => Sum.elim z.1 z.2) id (by intro z i; rfl)

theorem nash_normal_graph_boundary {d m N : ℕ}
    (U V : Set (Affine N)) (hUV : U ⊆ V) (hV : IsClosed V) (hUs : IsSemialgebraic U)
    (B : Set (Fin d → ℝ)) (q : (Fin d → ℝ) → Affine N)
    (hqa : AnalyticOnNhd ℝ q B)
    (hqb : ∀ x ∈ B, q x ∈ closure U \ U)
    {a : Fin d → ℝ} (ha : a ∈ B)
    (π : Affine N →L[ℂ] Affine m) (H : Affine m → Affine N)
    (hHπ : ∀ᶠ y in 𝓝[V] (q a), H (π (y-q a)) = y)
    (r : ℝ) (hr : 0 < r)
    (hHs : SemialgebraicOn {x : Fin (m+m) → ℝ | ‖x‖ < r}
      (fun x => complexRealEquiv N (H ((complexRealEquiv m).symm x))))
    (nc : NashNormalCoordinates B (fun x => π (q x-q a)) a) :
    let C := (nc.coordinates.toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv.trans
      (complexGraphRealEquiv nc.tangentDim nc.normalDim)
    let D := {z | ‖complexRealEquiv m (C.symm z)‖ < r ∧ H (C.symm z) ∈ U}
    PolynomialSignSet (fun z => Sum.elim z.1 z.2) D ∧
      ∃ R : ℝ, 0 < R ∧ R ≤ nc.radius ∧
        ∀ s ∈ ball 0 R, (s,nc.graph s) ∈ closure D \ D ∧
          ‖complexRealEquiv m (C.symm (s,nc.graph s))‖ < r ∧
          H (C.symm (s,nc.graph s)) = q (nc.parameters.symm s) := by
  let C := (nc.coordinates.toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv.trans
    (complexGraphRealEquiv nc.tangentDim nc.normalDim)
  let T := {z | ‖complexRealEquiv m (C.symm z)‖ < r}
  let F := H ∘ C.symm
  let G := fun y => C (π (y-q a))
  let D := T ∩ F ⁻¹' U
  have hDs : PolynomialSignSet (fun z => Sum.elim z.1 z.2) D := by
    have hu := semialgebraic_nash_chart_preimage hUs H hHs
    have hh := polynomialSignSet_linear_product_preimage hu
      ((complexRealEquiv m).toLinearMap.comp C.symm.toLinearMap)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    change (‖complexRealEquiv m (C.symm z)‖ < r ∧ H (C.symm z) ∈ U) ↔
      (‖complexRealEquiv m (C.symm z)‖ < r ∧
        H ((complexRealEquiv m).symm (complexRealEquiv m (C.symm z))) ∈ U)
    rw [ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨hDs,?_⟩
  have hG : Continuous G := C.continuous.comp (π.continuous.comp (continuous_id.sub continuous_const))
  have hFG : ∀ᶠ y in 𝓝[V] (q a), F (G y) = y := by
    simpa only [F,G,Function.comp_apply,C.symm_apply_apply] using hHπ
  have hT : IsOpen T := isOpen_lt
    ((complexRealEquiv m).continuous.comp C.symm.continuous |>.norm) continuous_const
  have h0T : G (q a) ∈ T := by change ‖complexRealEquiv m (C.symm (C (π (q a-q a))))‖ < r; simpa using hr
  obtain ⟨W,hW,haW,htrans⟩ := inverse_germ_boundary_transfer U V hUV hV F G hG (q a) hFG T hT h0T
  have hinvc : ContinuousAt nc.parameters.symm 0 :=
    (nc.inverse_analytic 0 (mem_ball_self nc.radius_pos)).continuousAt
  have hqc : ContinuousAt (q ∘ nc.parameters.symm) 0 :=
    ContinuousAt.comp_of_eq (hqa a ha).continuousAt hinvc nc.inverse_zero
  have hnear : ∀ᶠ s in 𝓝 (0 : Fin ((nc.tangentDim+nc.tangentDim)+nc.normalDim) → ℝ),
      s ∈ ball 0 nc.radius ∧ q (nc.parameters.symm s) ∈ W :=
    inter_mem (ball_mem_nhds _ nc.radius_pos) (by
      apply hqc.preimage_mem_nhds
      simpa only [Function.comp_apply,nc.inverse_zero] using hW.mem_nhds haW)
  obtain ⟨R,hR,hRsub⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨min R nc.radius,lt_min hR nc.radius_pos,min_le_right _ _,?_⟩
  intro s hs
  have hsR : s ∈ ball 0 R := ball_subset_ball (min_le_left _ _) hs
  have hh := hRsub hsR
  have hxB := nc.inverse_mapsTo hh.1
  have hg := htrans _ ⟨hqb _ hxB,hh.2⟩
  have hgraph : G (q (nc.parameters.symm s)) = (s,nc.graph s) := by
    change complexGraphRealEquiv nc.tangentDim nc.normalDim
      (nc.coordinates (π (q (nc.parameters.symm s)-q a))) = _
    have h := nc.graph_identity s hh.1
    simpa only [sub_self,map_zero,sub_zero] using h
  rw [hgraph] at hg
  exact hg
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_LocallyGoodNashBoundary
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
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
open Set Filter Topology Metric MeasureTheory
open scoped Classical

theorem nash_boundary_chart_of_projection {d m N : ℕ}
    (U V : Set (Affine N)) (hUV : U ⊆ V) (hV : IsClosed V) (hUs : IsSemialgebraic U)
    (B : Set (Fin d → ℝ)) (hB : IsOpen B)
    (q : (Fin d → ℝ) → Affine N) (hqa : AnalyticOnNhd ℝ q B)
    (hqs : SemialgebraicOn B (fun x => complexRealEquiv N (q x)))
    (hqb : ∀ x ∈ B, q x ∈ closure U \ U)
    {a : Fin d → ℝ} (ha : a ∈ B)
    (hqi : Function.Injective (fderiv ℝ q a))
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) a (Pi.single i 1)))
    (c : ProjectionNashChart V (q a) m) :
    ∃ b : NashBoundaryChart (m := m) U V B q, b.center = a := by
  let G := fun y => c.projection (y-q a)
  have hG : AnalyticAt ℂ G (q a) :=
    (c.projection.analyticAt _).comp (analyticAt_id.sub analyticAt_const)
  have hF : AnalyticAt ℂ c.inverse 0 := c.inverse_analytic 0 (by simpa only [mem_ofPred_eq,map_zero,norm_zero] using c.radius_pos)
  have hnear : ∀ᶠ z : Affine m in 𝓝 0, ‖complexRealEquiv m z‖ < c.radius :=
    (isOpen_lt ((complexRealEquiv m).continuous.norm) continuous_const).mem_nhds (by simpa only [mem_ofPred_eq,map_zero,norm_zero] using c.radius_pos)
  have hGF : (G ∘ c.inverse) =ᶠ[𝓝 (0 : Affine m)] id := by
    filter_upwards [hnear] with z hz
    exact c.left_inverse z hz
  have hqV : ∀ᶠ x in 𝓝 a, q x ∈ V := by
    filter_upwards [hB.mem_nhds ha] with x hx
    exact closure_minimal hUV hV (hqb x hx).1
  have ht : Tendsto q (𝓝 a) (𝓝[V] (q a)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(hqa a ha).continuousAt,hqV⟩
  have hFGq : (c.inverse ∘ G ∘ q) =ᶠ[𝓝 a] q := ht c.right_inverse
  obtain ⟨hMi,hMg⟩ := chart_parametric_generic c.inverse G q c.inverse_zero hF hG
    (hqa a ha).differentiableAt hqi hGF hFGq hr
  have hMa : AnalyticOnNhd ℝ (G ∘ q) B := by
    intro x hx
    exact ((c.projection.restrictScalars ℝ).analyticAt _).comp ((hqa x hx).sub analyticAt_const)
  let L := (complexRealEquiv m).toLinearMap.comp
    ((c.projection.restrictScalars ℝ).toLinearMap.comp (complexRealEquiv N).symm.toLinearMap)
  have hMs : SemialgebraicOn B (fun x => complexRealEquiv m ((G ∘ q) x)) := by
    have hs := (SemialgebraicOn.affine PolynomialSignSet.univ L (-L (complexRealEquiv N (q a)))).comp
      hqs (fun _ _ => mem_univ _)
    apply hs.congr
    intro x _
    simp [L,G,sub_eq_add_neg]
  obtain ⟨nc⟩ := generic_nash_normal_coordinates B hB (G ∘ q) hMa hMs ha hMi hMg
  obtain ⟨hDs,R,hR,hRle,hboundary⟩ := nash_normal_graph_boundary U V hUV hV hUs B q hqa hqb ha
    c.projection c.inverse c.right_inverse c.radius c.radius_pos c.inverse_semialgebraic nc
  exact ⟨⟨a,ha,c,nc,R,hR,hRle,hDs,hboundary⟩,rfl⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_LocallySmallSlopeGood
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
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

open Set Filter Topology Metric MeasureTheory
open scoped Classical

theorem locally_small_slope_good_nash_boundary {d m N : ℕ}
    (U V : Set (Affine N)) (hUV : U ⊆ V) (hV : IsClosed V) (hUs : IsSemialgebraic U)
    (B : Set (Fin d → ℝ)) (hB : IsOpen B)
    (q : (Fin d → ℝ) → Affine N) (hqa : AnalyticOnNhd ℝ q B)
    (hqs : SemialgebraicOn B (fun x => complexRealEquiv N (q x)))
    (hqb : ∀ x ∈ B, q x ∈ closure U \ U)
    {a : Fin d → ℝ} (ha : a ∈ B)
    (hqi : Function.Injective (fderiv ℝ q a))
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) a (Pi.single i 1)))
    (c : ProjectionNashChart V (q a) m) :
    ∃ W : Set (Fin d → ℝ), IsOpen W ∧ a ∈ W ∧
      volume {x | x ∈ W ∧ ¬ SmallSlopeGoodNashBoundary m U V B q x} = 0 := by
  obtain ⟨c,hca⟩ := nash_boundary_chart_of_projection U V hUV hV hUs B hB q hqa hqs hqb ha hqi hr c
  obtain ⟨W,hW,hcW,hnull⟩ := c.locally_small_slope_good
  refine ⟨W,hW,hca ▸ hcW,measure_mono_null ?_ hnull⟩
  intro x hx
  exact ⟨hx.1,hx.2⟩
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SmallSlopeGoodSupported
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
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
open Set Filter Topology Metric MeasureTheory
open scoped Classical

theorem NashPatch.null_nonsmallgood_generic_oai {m N : ℕ}
    (U V : Set (Affine N)) (hUV : U ⊆ V) (hVc : IsClosed V)
    (hVs : IsSemialgebraic V) (hUs : IsSemialgebraic U)
    (p : NashPatch (N+N))
    (hp : ∀ x ∈ p.domain, p.complexMap x ∈ closure U \ U ∧
      ∃ W : Set (Affine N), W ⊆ V ∧
        IsOpen ((Subtype.val : V → Affine N) ⁻¹' W) ∧ p.complexMap x ∈ W ∧
        ∃ B : Set (Affine m), IsOpen B ∧ Nonempty (Biholomorph W B)) :
    volume {x | x ∈ p.domain ∧ m ≤ p.complexRank x ∧
      ¬ SmallSlopeGoodNashBoundary m U V p.domain p.complexMap x} = 0 := by
  let A := {x | x ∈ p.domain ∧ m ≤ p.complexRank x}
  have hh := locally_null_bad_set volume A (SmallSlopeGoodNashBoundary m U V p.domain p.complexMap)
  have hqs : SemialgebraicOn p.domain (fun x => complexRealEquiv N (p.complexMap x)) := by
    apply p.semialgebraic_toFun.congr
    intro x _
    exact ((complexRealEquiv N).apply_symm_apply (p.toFun x)).symm
  have hlocal : ∀ a ∈ A, ∃ W : Set (Fin p.dim → ℝ), IsOpen W ∧ a ∈ W ∧
      volume {x | x ∈ A ∧ x ∈ W ∧ ¬ SmallSlopeGoodNashBoundary m U V p.domain p.complexMap x} = 0 := by
    intro a ha
    obtain ⟨_,W,hWV,hW,haW,T,hT,⟨e⟩⟩ := hp a ha.1
    obtain ⟨F,G,hF0,hF,hG,hGF,hFG,hFV⟩ := e.centered_chart_germs hWV hW hT haW
    obtain ⟨c⟩ := projection_nash_chart_of_germs V hVs F G hF
      (by simpa only [hF0] using hG) hGF (by simpa only [hF0] using hFG) hFV
    have c' : ProjectionNashChart V (p.complexMap a) m := hF0 ▸ c
    obtain ⟨W',hW',haW',hnull⟩ := locally_small_slope_good_nash_boundary U V hUV hVc hUs
      p.domain p.isOpen_domain p.complexMap p.analytic_complexMap hqs
      (fun x hx => (hp x hx).1) ha.1 (p.injective_fderiv_complexMap ha.1) ha.2 c'
    refine ⟨W',hW',haW',measure_mono_null ?_ hnull⟩
    intro x hx
    exact ⟨hx.2.1,hx.2.2⟩
  have hnull := hh hlocal
  simpa only [A,mem_ofPred_eq,and_assoc] using hnull
end

open Set Filter Topology MeasureTheory
open scoped Classical

end Release061

end

end OAI
end

theorem solution : type_of% @OAI.Release061.NashPatch.null_nonsmallgood_generic_oai := @OAI.Release061.NashPatch.null_nonsmallgood_generic_oai
