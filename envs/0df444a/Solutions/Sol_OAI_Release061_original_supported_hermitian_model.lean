-- Prove2me | solution 1 for OAI.Release061.original_supported_hermitian_model
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:08:36.764765+00:00
-- url     : https://prove2.me/submissions/e4172118-8df8-4698-878f-401aa0fe5838

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S003
import Theorems.Thm_OAI_Release061_NashBoundaryChart_scaling_chart
import Theorems.Thm_OAI_Release061_NashBoundaryScalingChart_global_from_two_sided
import Theorems.Thm_OAI_Release061_NashBoundaryScalingChart_independent_support_rows
import Theorems.Thm_OAI_Release061_cocompact_bounded_affine_smooth
import Theorems.Thm_OAI_Release061_interior_balls_from_small_slope_graphs
import Theorems.Thm_OAI_Release061_original_small_slope_good_supported_boundary

section
-- module Solutions.OAIQ025_SD.Compat
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_Basic
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Release061

theorem IsAffineAlgebraic.isClosed {n : ℕ} {V : Set (Affine n)}
    (hV : IsAffineAlgebraic V) : IsClosed V := by
  obtain ⟨P, rfl⟩ := hV
  have heq : {z | ∀ p ∈ P, MvPolynomial.eval z p = 0} =
      ⋂ p ∈ P, {z | MvPolynomial.eval z p = 0} := by ext; simp
  rw [heq]
  exact isClosed_biInter fun p _ => isClosed_eq p.continuous_eval continuous_const

theorem locallyCompact_of_relative_open {n : ℕ} {V U : Set (Affine n)}
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U)) :
    LocallyCompactSpace U := by
  have hloc := hU.isLocallyClosed.image
    Topology.IsEmbedding.subtypeVal.isInducing
    (by simpa using hV.isClosed.isLocallyClosed)
  have heq : (Subtype.val : V → Affine n) ''
      ((Subtype.val : V → Affine n) ⁻¹' U) = U := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hUV hx⟩, hx, rfl⟩
  rw [heq] at hloc
  exact hloc.locallyCompactSpace

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticImplicitScalar
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
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
-- module Solutions.OAIQ025_SD.SymmetricDomains_ScalarEquicontinuousHolomorphy
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra


theorem zeroLocus_closed {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    IsClosed (MvPolynomial.zeroLocus ℂ I) := by
  have he : MvPolynomial.zeroLocus ℂ I = ⋂ p ∈ I,
      {z : Fin n → ℂ | MvPolynomial.eval z p = 0} := by
    ext z; simp only [MvPolynomial.zeroLocus, mem_iInter, mem_ofPred_eq]; rfl
  rw [he]
  exact isClosed_iInter fun p => isClosed_iInter fun _ =>
    isClosed_eq (MvPolynomial.continuous_eval p) continuous_const

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ContinuityPrinciple
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra
open Set

theorem continuity_principle_of_interior_anchor {d n : ℕ} {X Γ : Type*}
    [TopologicalSpace X] [PreconnectedSpace X] [SequentialSpace X]
    (S Q : Set (Affine d)) (hS : IsOpen S) (hconn : IsPreconnected S)
    (hQ : IsCompact Q) (hSQ : S ⊆ Q)
    (V U : Set (Affine n)) (_hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    [LocallyCompactSpace U] (hbounded : Bornology.IsBounded U)
    [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (K : Set U) (hK : IsCompact K) (hrep : ∀ x : U, ∃ k ∈ K, ∃ γ : Γ, γ • k = x)
    (A : X → Q → V) (hA : Continuous (Function.uncurry A))
    (hAh : ∀ t, HolomorphicOnSubset S (fun x => (A t ⟨x.val,hSQ x.property⟩).val))
    (hanchor : ∀ t, ∃ x : S, (A t ⟨x.val,hSQ x.property⟩).val ∈ U)
    (hboundary : ∀ t (x : Q), x.val ∉ S → (A t x).val ∈ U)
    (hstart : ∃ t, ∀ x, (A t x).val ∈ U) :
    ∀ t x, (A t x).val ∈ U := by
  classical
  let T : Set X := {t | ∀ x, (A t x).val ∈ U}
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  have hopen : IsOpen T := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have hop := hU.preimage hA
    obtain ⟨O,W,hO,_hW,htO,hQW,hOW⟩ := generalized_tube_lemma
      (s := {t}) isCompact_singleton (t := univ) isCompact_univ hop (by
        rintro ⟨u,x⟩ ⟨hu,_⟩
        rcases mem_singleton_iff.mp hu with rfl
        exact ht x)
    apply mem_of_superset (hO.mem_nhds (htO (mem_singleton t)))
    intro u hu x
    exact hOW (show (u,x) ∈ O ×ˢ W from ⟨hu,hQW (mem_univ x)⟩)
  have hclosed : IsClosed T := by
    apply IsSeqClosed.isClosed
    intro ts t hts ht
    obtain ⟨x₀,hx₀⟩ := hanchor t
    let F : ℕ → S → U := fun i x => ⟨(A (ts i) ⟨x.val,hSQ x.property⟩).val,
      hts i ⟨x.val,hSQ x.property⟩⟩
    have hlim (x : S) : Tendsto (fun i => (F i x).val) atTop
        (𝓝 (A t ⟨x.val,hSQ x.property⟩).val) :=
      (continuous_subtype_val.continuousAt.comp (hA.continuousAt.comp
        (continuous_id.prodMk continuous_const).continuousAt)).tendsto.comp ht
    have hbase : ∃ C : Set U, IsCompact C ∧ ∀ᶠ i in atTop, F i x₀ ∈ C := by
      obtain ⟨C,hC,hCn⟩ := exists_compact_mem_nhds (⟨_,hx₀⟩ : U)
      have hh : Tendsto (fun i => F i x₀) atTop (𝓝 (⟨_,hx₀⟩ : U)) :=
        tendsto_subtype_rng.mpr (hlim x₀)
      exact ⟨C,hC,hh hCn⟩
    have hall := bounded_cocompact_holomorphic_family_limit S hS hconn U hbounded
      hhol K hK hrep F atTop x₀ hbase
      (HolomorphicOnSubset.locallyEventually hS (fun i => hAh (ts i)) atTop)
      (fun x => (A t ⟨x.val,hSQ x.property⟩).val) hlim
    intro x
    by_cases hx : x.val ∈ S
    · exact hall ⟨x.val,hx⟩
    · exact hboundary t x hx
  have hT : T = univ := IsClopen.eq_univ ⟨hclosed,hopen⟩ hstart
  intro t
  change t ∈ T
  rw [hT]
  trivial

theorem interior_anchor_of_boundary {d n : ℕ}
    (S Q : Set (Affine d)) (hSQ : S ⊆ Q) (hQS : Q ⊆ closure S)
    (hboundary : (Q \ S).Nonempty)
    (V U : Set (Affine n)) (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (A : Q → V) (hA : Continuous A)
    (hAb : ∀ x : Q, x.val ∉ S → (A x).val ∈ U) :
    ∃ x : S, (A ⟨x.val,hSQ x.property⟩).val ∈ U := by
  obtain ⟨b,hbQ,hbS⟩ := hboundary
  obtain ⟨f,hf,hfl⟩ := mem_closure_iff_seq_limit.mp (hQS hbQ)
  let F : ℕ → Q := fun i => ⟨f i,hSQ (hf i)⟩
  have hlim : Tendsto F atTop (𝓝 (⟨b,hbQ⟩ : Q)) := tendsto_subtype_rng.mpr hfl
  have he : ∀ᶠ i in atTop, (A (F i)).val ∈ U :=
    (hA.continuousAt.tendsto.comp hlim) (hU.mem_nhds (hAb ⟨b,hbQ⟩ hbS))
  obtain ⟨i,hi⟩ := he.exists
  exact ⟨⟨f i,hf i⟩,hi⟩

theorem bounded_cocompact_continuity_principle {d n : ℕ} {X Γ : Type*}
    [TopologicalSpace X] [PreconnectedSpace X] [SequentialSpace X]
    (S Q : Set (Affine d)) (hS : IsOpen S) (hconn : IsPreconnected S)
    (hQ : IsCompact Q) (hSQ : S ⊆ Q) (hQS : Q ⊆ closure S)
    (hbd : (Q \ S).Nonempty)
    (V U : Set (Affine n)) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    [LocallyCompactSpace U] (hbounded : Bornology.IsBounded U)
    [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (K : Set U) (hK : IsCompact K) (hrep : ∀ x : U, ∃ k ∈ K, ∃ γ : Γ, γ • k = x)
    (A : X → Q → V) (hA : Continuous (Function.uncurry A))
    (hAh : ∀ t, HolomorphicOnSubset S (fun x => (A t ⟨x.val,hSQ x.property⟩).val))
    (hboundary : ∀ t (x : Q), x.val ∉ S → (A t x).val ∈ U)
    (hstart : ∃ t, ∀ x, (A t x).val ∈ U) :
    ∀ t x, (A t x).val ∈ U := by
  apply continuity_principle_of_interior_anchor S Q hS hconn hQ hSQ V U hUV hU
    hbounded hhol K hK hrep A hA hAh _ hboundary hstart
  intro t
  exact interior_anchor_of_boundary S Q hSQ hQS hbd V U hU (A t)
    (hA.comp (continuous_const.prodMk continuous_id)) (hboundary t)

theorem bounded_cocompact_disc_continuity {n : ℕ} {Γ : Type*}
    (V U : Set (Affine n)) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    [LocallyCompactSpace U] (hbounded : Bornology.IsBounded U)
    [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (K : Set U) (hK : IsCompact K) (hrep : ∀ x : U, ∃ k ∈ K, ∃ γ : Γ, γ • k = x)
    (A : Icc (0 : ℝ) 1 → closedBall (0 : Affine 1) 1 → V)
    (hA : Continuous (Function.uncurry A))
    (hAh : ∀ t, HolomorphicOnSubset (ball (0 : Affine 1) 1)
      (fun x => (A t ⟨x.val,ball_subset_closedBall x.property⟩).val))
    (hboundary : ∀ t (x : closedBall (0 : Affine 1) 1), ‖x.val‖ = 1 → (A t x).val ∈ U)
    (hstart : ∀ x, (A ⟨0,by simp⟩ x).val ∈ U) :
    ∀ t x, (A t x).val ∈ U := by
  apply bounded_cocompact_continuity_principle (ball (0 : Affine 1) 1)
    (closedBall (0 : Affine 1) 1) isOpen_ball (convex_ball _ _).isPreconnected
    (isCompact_closedBall _ _) ball_subset_closedBall _ _ V U hUV hU
    hbounded hhol K hK hrep A hA hAh _ ⟨⟨0,by simp⟩,hstart⟩
  · rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
  · refine ⟨fun _ => 1,?_,?_⟩ <;> simp
  · intro t x hx
    apply hboundary t x
    have hleft := x.property
    rw [mem_closedBall,dist_zero_right] at hleft
    rw [mem_ball,dist_zero_right,not_lt] at hx
    exact le_antisymm hleft hx

open Filter
open scoped Topology

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_UniformSmallOperators
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
namespace Release061

section

lemma continuousOn_uniformly_compact {P E F : Type*} [TopologicalSpace P]
    [TopologicalSpace E] [PseudoMetricSpace F]
    {K : Set E} (hK : IsCompact K) {V : Set P} {p₀ : P} (hV : V ∈ 𝓝 p₀)
    {f : P → E → F} (hf : ContinuousOn (Function.uncurry f) (V ×ˢ K)) :
    TendstoUniformlyOn f (f p₀) (𝓝 p₀) K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨W,hW,hw⟩ := hK.mem_uniformity_of_prod hf (mem_of_mem_nhds hV)
    (Metric.dist_mem_uniformity hε)
  rw [nhdsWithin_eq_nhds.mpr hV] at hW
  filter_upwards [hW] with p hp
  intro x hx
  simpa only [Set.mem_ofPred_eq,dist_comm] using hw p hp x hx

end

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_EventualOffsetBall
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
namespace Release061
open Set Filter Metric
open scoped Topology

lemma offsetDistance_lipschitz {S E : Type*} [MetricSpace E] [SMul ℝ E]
    (A : S → Set E) (s : S) (t : ℝ) : LipschitzWith 1 (offsetDistance A s t) := by
  unfold offsetDistance
  convert (LipschitzWith.const (α := E) (1 : ℝ)).min
    (lipschitz_infDist_pt (offsetScaled A s t)ᶜ) using 1; norm_num

lemma offset_excluded_nonempty {S E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : S → Set E) (s : S) (t : ℝ) (h0 : (0 : E) ∉ A s) :
    (offsetScaled A s t)ᶜ.Nonempty := ⟨0,by simpa [offsetScaled] using h0⟩

lemma ball_subset_offsetScaled {S E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : S → Set E} {s : S} {t c : ℝ} {v : E} (ht : 0 < t)
    (hball : ball v (c*t) ⊆ A s) : ball (t⁻¹ • v) c ⊆ offsetScaled A s t := by
  intro x hx
  change t • x ∈ A s
  apply hball
  have he : dist (t • x) v = t * dist x (t⁻¹ • v) := by
    nth_rw 1 [← smul_inv_smul₀ ht.ne' v]
    rw [dist_smul₀,Real.norm_eq_abs,abs_of_pos ht]
  rw [mem_ball,he,mul_comm c t]
  exact mul_lt_mul_of_pos_left hx ht

lemma radius_le_infDist_compl {E : Type*} [PseudoMetricSpace E]
    {A : Set E} {v : E} {c : ℝ} (hne : Aᶜ.Nonempty) (hball : ball v c ⊆ A) :
    c ≤ infDist v Aᶜ := by
  apply (le_infDist hne).mpr
  intro y hy
  by_contra h
  exact hy (hball (by simpa only [mem_ball,dist_comm] using lt_of_not_ge h))

theorem excluded_offset_noncollapse {S E : Type*} [TopologicalSpace S]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (A : S → Set E) (F : Set E) {s₀ : S} {s : ℕ → S} {t : ℕ → ℝ} {v : ℕ → E}
    (hs : Tendsto s atTop (𝓝 s₀)) (ht : Tendsto t atTop (𝓝 0))
    (htpos : ∀ j, 0 < t j) (h0 : ∀ j, (0 : E) ∉ A (s j))
    {c C : ℝ} (hc : 0 < c) (hbound : ∀ j, ‖v j‖ ≤ C*t j)
    (hball : ∀ j, ball (v j) (c*t j) ⊆ A (s j))
    (hexcluded : ∀ (s' : ℕ → S) (t' : ℕ → ℝ) (v' : ℕ → E) (w : E),
      Tendsto s' atTop (𝓝 s₀) → Tendsto t' atTop (𝓝 0) →
      (∀ j, 0 < t' j) → Tendsto v' atTop (𝓝 w) → w ∈ F →
      Tendsto (fun j => infDist (v' j) (offsetScaled A (s' j) (t' j))ᶜ) atTop (𝓝 0)) :
    F ≠ univ := by
  let w : ℕ → E := fun j => (t j)⁻¹ • v j
  have hw (j : ℕ) : w j ∈ closedBall (0 : E) C := by
    rw [mem_closedBall,dist_zero_right]
    dsimp [w]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (htpos j))]
    calc (t j)⁻¹ * ‖v j‖ ≤ (t j)⁻¹*(C*t j) :=
          mul_le_mul_of_nonneg_left (hbound j) (inv_nonneg.mpr (htpos j).le)
      _ = C := by field_simp [(htpos j).ne']
  obtain ⟨a,_,φ,hφ,hwa⟩ := (isCompact_closedBall (0 : E) C).tendsto_subseq hw
  intro hF
  have hlim := hexcluded (s ∘ φ) (t ∘ φ) (w ∘ φ) a (hs.comp hφ.tendsto_atTop)
    (ht.comp hφ.tendsto_atTop) (fun j => htpos (φ j)) hwa (by rw [hF]; trivial)
  have hb : ∀ j, c ≤ infDist (w (φ j)) (offsetScaled A (s (φ j)) (t (φ j)))ᶜ := by
    intro j
    exact radius_le_infDist_compl (offset_excluded_nonempty A _ _ (h0 (φ j)))
      (ball_subset_offsetScaled (htpos (φ j)) (hball (φ j)))
  have hc0 : c ≤ (0 : ℝ) := ge_of_tendsto hlim (Eventually.of_forall hb)
  exact not_le_of_gt hc hc0

lemma complex_ball_offset_ball {k : ℕ} {Ω : Set (Fin k → ℂ)} {a : Fin k → ℂ}
    {r : ℝ} (φ : (Fin k → ℝ) → Fin k → ℝ)
    (hball : ball a r ⊆ Ω) :
    ball ((fun i => (a i).im) - φ (fun i => (a i).re)) r ⊆
      {v : Fin k → ℝ | (fun i => ((a i).re : ℂ)+Complex.I*((φ (fun i => (a i).re) i+v i) : ℂ)) ∈ Ω} := by
  intro v hv
  apply hball
  rw [mem_ball,dist_eq_norm] at hv ⊢
  have he : (fun i => ((a i).re : ℂ)+Complex.I*((φ (fun i => (a i).re) i+v i) : ℂ)) - a =
      fun i => Complex.I*((v-((fun i => (a i).im)-φ (fun i => (a i).re))) i : ℂ) := by
    funext i
    apply Complex.ext <;> simp; ring
  rw [he]
  simpa only [Pi.norm_def,nnnorm_mul,Complex.nnnorm_I,Complex.nnnorm_real,one_mul] using hv

lemma tendsto_of_truncated_zero {I : Type*} {l : Filter I} {f : I → ℝ}
    (h : Tendsto (fun i => min 1 (f i)) l (𝓝 0)) : Tendsto f l (𝓝 0) := by
  have he : ∀ᶠ i in l, f i < 1 := by
    filter_upwards [(tendsto_order.mp h).2 1 zero_lt_one] with i hi
    rcases min_lt_iff.mp hi with hi | hi
    · exact (lt_irrefl _ hi).elim
    · exact hi
  exact h.congr' (he.mono fun i hi => min_eq_right hi.le)

lemma moving_offsetDistance_limit {S E I : Type*} [MetricSpace E] [SMul ℝ E]
    (A : S → Set E) (s : I → S) (t : I → ℝ) {l : Filter I} {v : I → E} {w : E} {a : ℝ}
    (h : Tendsto (fun j => offsetDistance A (s j) (t j) w) l (𝓝 a))
    (hv : Tendsto v l (𝓝 w)) :
    Tendsto (fun j => offsetDistance A (s j) (t j) (v j)) l (𝓝 a) := by
  apply h.congr_dist
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun j => by simpa only [NNReal.coe_one,one_mul] using
      (offsetDistance_lipschitz A (s j) (t j)).dist_le_mul w (v j))
  simpa only [dist_self] using (tendsto_const_nhds (x := w) (f := l)).dist hv

lemma excluded_limit_from_offsetDistance {S E I : Type*} [MetricSpace E] [SMul ℝ E]
    (A : S → Set E) (s : I → S) (t : I → ℝ) {l : Filter I} {v : I → E} {w : E}
    (h : Tendsto (fun j => offsetDistance A (s j) (t j) w) l (𝓝 0))
    (hv : Tendsto v l (𝓝 w)) :
    Tendsto (fun j => infDist (v j) (offsetScaled A (s j) (t j))ᶜ) l (𝓝 0) :=
  tendsto_of_truncated_zero (moving_offsetDistance_limit A s t h hv)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_NormalOffsetNoncollapse
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
namespace Release061
open Set Filter Metric
open scoped Topology NNReal

lemma complex_re_norm_le {k : ℕ} (a : Fin k → ℂ) : ‖fun i => (a i).re‖ ≤ ‖a‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact (RCLike.norm_re_le_norm (a i)).trans (norm_le_pi_norm a i)

lemma complex_im_norm_le {k : ℕ} (a : Fin k → ℂ) : ‖fun i => (a i).im‖ ≤ ‖a‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact (RCLike.norm_im_le_norm (a i)).trans (norm_le_pi_norm a i)

theorem complex_balls_to_normal_offsets {k : ℕ} {Ω : Set (Fin k → ℂ)}
    {φ : (Fin k → ℝ) → Fin k → ℝ} (hφ : ContDiffAt ℝ 1 φ 0) (hφ0 : φ 0 = 0)
    {ρ c C t₀ : ℝ} (hρ : 0 < ρ) (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 < t₀)
    (hballs : ∀ t, 0 < t → t < t₀ → ∃ a : Fin k → ℂ, ‖a‖ ≤ C*t ∧ ball a (c*t) ⊆ Ω) :
    ∃ D t₁ : ℝ, 0 < D ∧ 0 < t₁ ∧ ∀ t, 0 < t → t < t₁ →
      ∃ x v : Fin k → ℝ, ‖x‖ ≤ C*t ∧ ‖v‖ ≤ D*t ∧
        ball v (c*t) ⊆ {u | ‖u‖ < ρ ∧
          (fun i => (x i : ℂ)+Complex.I*((φ x i+u i) : ℂ)) ∈ Ω} := by
  obtain ⟨K,S,hS,hK⟩ := hφ.exists_lipschitzOnWith
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hS
  let D : ℝ := (1+(K:ℝ))*C
  have hD : 0 < D := mul_pos (by positivity) hC
  let t₁ := min t₀ (min (r/(C+1)) (ρ/(D+c+1)))
  have ht₁ : 0 < t₁ := lt_min ht₀ (lt_min (div_pos hr (by positivity)) (div_pos hρ (by positivity)))
  refine ⟨D,t₁,hD,ht₁,?_⟩
  intro t ht htt
  have htt₀ : t < t₀ := htt.trans_le (min_le_left _ _)
  have htr : t < r/(C+1) := (htt.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have htρ : t < ρ/(D+c+1) := (htt.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hCr : C*t < r := by
    have hh := (lt_div_iff₀ (by positivity : 0 < C+1)).mp htr
    nlinarith
  have hDr : D*t+c*t < ρ := by
    have hh := (lt_div_iff₀ (by positivity : 0 < D+c+1)).mp htρ
    nlinarith
  obtain ⟨a,ha,hab⟩ := hballs t ht htt₀
  let x : Fin k → ℝ := fun i => (a i).re
  let v : Fin k → ℝ := (fun i => (a i).im)-φ x
  have hx : ‖x‖ ≤ C*t := (complex_re_norm_le a).trans ha
  have hxS : x ∈ S := hrs (mem_ball_zero_iff.mpr (hx.trans_lt hCr))
  have hφb : ‖φ x‖ ≤ (K:ℝ)*‖x‖ := by
    simpa only [hφ0,dist_zero_right] using hK.dist_le_mul x hxS 0 (mem_of_mem_nhds hS)
  have hv : ‖v‖ ≤ D*t := by
    calc ‖v‖ ≤ ‖fun i => (a i).im‖+‖φ x‖ := norm_sub_le _ _
         _ ≤ C*t+(K:ℝ)*(C*t) := add_le_add ((complex_im_norm_le a).trans ha)
           (hφb.trans (mul_le_mul_of_nonneg_left hx K.coe_nonneg))
         _ = D*t := by dsimp [D]; ring
  refine ⟨x,v,hx,hv,?_⟩
  intro u hu
  refine ⟨?_,complex_ball_offset_ball φ hab hu⟩
  have hh : ‖u-v‖ < c*t := by simpa only [mem_ball,dist_eq_norm] using hu
  calc ‖u‖ ≤ ‖u-v‖+‖v‖ := norm_le_norm_sub_add _ _
       _ < c*t+D*t := add_lt_add_of_lt_of_le hh hv
       _ < ρ := by linarith

theorem normal_offset_noncollapse {k : ℕ} {Ω : Set (Fin k → ℂ)}
    {φ : (Fin k → ℝ) → Fin k → ℝ} (hφ : ContDiffAt ℝ 1 φ 0) (hφ0 : φ 0 = 0)
    {ρ c C t₀ : ℝ} (hρ : 0 < ρ) (hc : 0 < c) (hC : 0 < C) (ht₀ : 0 < t₀)
    (hballs : ∀ t, 0 < t → t < t₀ → ∃ a : Fin k → ℂ, ‖a‖ ≤ C*t ∧ ball a (c*t) ⊆ Ω)
    (hbdry : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ),
      (fun i => (x i : ℂ)+Complex.I*(φ x i : ℂ)) ∉ Ω)
    (F : Set (Fin k → ℝ))
    (hexcluded : ∀ (s : ℕ → Fin k → ℝ) (t : ℕ → ℝ) (v : ℕ → Fin k → ℝ) (w : Fin k → ℝ),
      Tendsto s atTop (𝓝 0) → Tendsto t atTop (𝓝 0) → (∀ j, 0 < t j) →
      Tendsto v atTop (𝓝 w) → w ∈ F →
      Tendsto (fun j => infDist (v j)
        (offsetScaled (fun x => {u | ‖u‖ < ρ ∧
          (fun i => (x i : ℂ)+Complex.I*((φ x i+u i) : ℂ)) ∈ Ω}) (s j) (t j))ᶜ)
        atTop (𝓝 0)) : F ≠ univ := by
  obtain ⟨D,t₁,_,ht₁,hfiber⟩ := complex_balls_to_normal_offsets hφ hφ0 hρ hc hC ht₀ hballs
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hbdry
  have hτ : 0 < min t₁ (r/(C+1)) := lt_min ht₁ (div_pos hr (by positivity))
  obtain ⟨t,_,ht,htlim⟩ := exists_seq_strictAnti_tendsto' hτ
  choose x v hx hv hb using fun j => hfiber (t j) (ht j).1 ((ht j).2.trans_le (min_le_left _ _))
  have hxlim : Tendsto x atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) hx
    simpa only [mul_zero] using htlim.const_mul C
  apply excluded_offset_noncollapse _ F hxlim htlim (fun j => (ht j).1) ?_ hc hv hb hexcluded
  intro j hj
  have hxr : ‖x j‖ < r := by
    have hh := (lt_div_iff₀ (by positivity : 0 < C+1)).mp
      ((ht j).2.trans_le (min_le_right _ _))
    nlinarith [hx j,(ht j).1]
  have hh := hrs (mem_ball_zero_iff.mpr hxr)
  apply hh
  simpa only [Pi.zero_apply,Complex.ofReal_zero,add_zero] using hj.2

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_WeightedTaylorUniformlyCompact
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
namespace Release061

open Set Filter Metric Asymptotics
open scoped Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma parabolicScale_norm {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (x : E × F) :
    ‖parabolicScale u x‖ ≤ u*‖x‖ := by
  rw [parabolicScale,Prod.norm_def,max_le_iff]
  constructor
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hu]
    exact mul_le_mul_of_nonneg_left (norm_fst_le x) hu
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg u)]
    calc u^2*‖x.2‖ ≤ u*‖x.2‖ := mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)
         _ ≤ u*‖x‖ := mul_le_mul_of_nonneg_left (norm_snd_le x) hu

lemma parabolic_cubic_remainder {R : E × F → G} (hR : R =O[𝓝 0] (fun x => ‖x‖^3))
    {K : Set (E × F)} (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn (fun u x => (u^2)⁻¹ • R (parabolicScale u x))
      (fun _ => 0) (𝓝[>] (0 : ℝ)) K := by
  obtain ⟨C,hC,hbound⟩ := hR.exists_pos
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hbound.bound
  obtain ⟨M,hM,hKM⟩ := hK.exists_pos_norm_le
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have huid : Tendsto (id : ℝ → ℝ) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have huM : ∀ᶠ u : ℝ in 𝓝[>] 0, u*M < r := by
    exact (tendsto_order.mp (show Tendsto (fun u : ℝ => u*M) (𝓝[>] 0) (𝓝 0) by
      simpa using huid.mul_const M)).2 r hr
  have huε : ∀ᶠ u : ℝ in 𝓝[>] 0, C*M^3*u < ε := by
    exact (tendsto_order.mp (show Tendsto (fun u : ℝ => C*M^3*u) (𝓝[>] 0) (𝓝 0) by
      simpa using huid.const_mul (C*M^3))).2 ε hε
  filter_upwards [self_mem_nhdsWithin,huM,huε,
    show ∀ᶠ u : ℝ in 𝓝[>] 0, u < 1 from (tendsto_order.mp huid).2 1 zero_lt_one] with u hu hur huε hu1
  intro x hx
  have hn : ‖parabolicScale u x‖ ≤ u*M :=
    (parabolicScale_norm hu.le hu1.le x).trans (mul_le_mul_of_nonneg_left (hKM x hx) hu.le)
  have hb := hrs (mem_ball_zero_iff.mpr (hn.trans_lt hur))
  have hb' : ‖R (parabolicScale u x)‖ ≤ C*(u*M)^3 := by
    apply hb.trans
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) 3)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 3) hC.le
  rw [dist_zero_left,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (sq_pos_of_pos hu))]
  calc (u^2)⁻¹ * ‖R (parabolicScale u x)‖ ≤ (u^2)⁻¹*(C*(u*M)^3) :=
         mul_le_mul_of_nonneg_left hb' (inv_nonneg.mpr (sq_nonneg u))
       _ = C*M^3*u := by field_simp
       _ < ε := huε

lemma multilinear_one_eval (p : FormalMultilinearSeries ℝ (E × F) G) (x : E × F) :
    p 1 (fun _ => x) = (continuousMultilinearCurryFin1 ℝ (E × F) G (p 1)) x := by
  rw [continuousMultilinearCurryFin1_apply]
  congr 1

lemma parabolic_partialSum {f : E × F → G} {p : FormalMultilinearSeries ℝ (E × F) G}
    (hf : HasFPowerSeriesAt f p 0) (hf0 : f 0 = 0)
    (hlin : ∀ z : E, p 1 (fun _ => (z,0)) = 0) {u : ℝ} (hu : u ≠ 0) (x : E × F) :
    (u^2)⁻¹ • p.partialSum 3 (parabolicScale u x) =
      p 1 (fun _ => (0,x.2)) + p 2 (fun _ => (x.1,u • x.2)) := by
  let L := continuousMultilinearCurryFin1 ℝ (E × F) G (p 1)
  have hL : ∀ z : E, L (z,0) = 0 := by
    intro z
    simpa only [L,← multilinear_one_eval] using hlin z
  have hδ : parabolicScale u x = (u • x.1,0)+(u^2) • (0,x.2) := by
    ext <;> simp [parabolicScale]
  have hδ' : parabolicScale u x = u • (x.1,u • x.2) := by
    ext <;> simp [parabolicScale,smul_smul,pow_two]
  have hfirst : p 1 (fun _ => parabolicScale u x) = u^2 • p 1 (fun _ => (0,x.2)) := by
    rw [multilinear_one_eval,hδ,map_add,map_smul]
    change L (u • x.1,0)+(u^2) • L (0,x.2) = _
    rw [hL,zero_add,← multilinear_one_eval]
  have hsecond : p 2 (fun _ => parabolicScale u x) = u^2 • p 2 (fun _ => (x.1,u • x.2)) := by
    simp only [hδ']
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      (p 2).map_smul_univ (fun _ => u) (fun _ => (x.1,u • x.2))
  simp only [FormalMultilinearSeries.partialSum,Finset.sum_range_succ,Finset.sum_range_zero,
    zero_add,hf.coeff_zero,hf0,hfirst,hsecond,smul_add,inv_smul_smul₀ (pow_ne_zero 2 hu)]

theorem parabolic_taylor_uniformly_compact {f : E × F → G}
    {p : FormalMultilinearSeries ℝ (E × F) G} (hf : HasFPowerSeriesAt f p 0)
    (hf0 : f 0 = 0) (hlin : ∀ z : E, p 1 (fun _ => (z,0)) = 0)
    {K : Set (E × F)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun u x => (u^2)⁻¹ • f (parabolicScale u x))
      (fun x => p 1 (fun _ => (0,x.2)) + p 2 (fun _ => (x.1,0)))
      (𝓝[>] (0 : ℝ)) K := by
  have hR : (fun x => f x-p.partialSum 3 x) =O[𝓝 0] (fun x => ‖x‖^3) := by
    simpa only [zero_add] using hf.isBigO_sub_partialSum_pow 3
  have hrem := parabolic_cubic_remainder hR hK.isBounded
  have hpoly : TendstoUniformlyOn
      (fun u (x : E × F) => p 1 (fun _ => (0,x.2))+p 2 (fun _ => (x.1,u • x.2)))
      (fun x => p 1 (fun _ => (0,x.2))+p 2 (fun _ => (x.1,0))) (𝓝[>] (0 : ℝ)) K := by
    have hcont : Continuous (fun q : ℝ × (E × F) =>
        p 1 (fun _ => (0,q.2.2))+p 2 (fun _ => (q.2.1,q.1 • q.2.2))) := by fun_prop
    have hh := continuousOn_uniformly_compact
      (f := fun u (x : E × F) => p 1 (fun _ => (0,x.2))+p 2 (fun _ => (x.1,u • x.2))) hK (univ_mem : (univ : Set ℝ) ∈ 𝓝 (0:ℝ))
      hcont.continuousOn
    have hh' := tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr
      (hh.tendstoUniformlyOnFilter.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds))
    simpa only [zero_smul] using hh'
  have hh : TendstoUniformlyOn
      (fun u x => (u^2)⁻¹ • (f (parabolicScale u x)-p.partialSum 3 (parabolicScale u x)) +
        (p 1 (fun _ => (0,x.2))+p 2 (fun _ => (x.1,u • x.2))))
      (fun x => p 1 (fun _ => (0,x.2))+p 2 (fun _ => (x.1,0))) (𝓝[>] (0 : ℝ)) K := by
    exact (hrem.add hpoly).congr_right (fun x _hx => zero_add _)
  apply hh.congr
  filter_upwards [self_mem_nhdsWithin] with u hu
  intro x _hx
  dsimp only
  rw [← parabolic_partialSum hf hf0 hlin hu.ne' x,← smul_add,sub_add_cancel]

lemma uniform_reindex {I J X Y : Type*} [UniformSpace Y] {l : Filter I} {r : Filter J}
    {A : I → X → Y} {a : X → Y} {K : Set X} (ha : TendstoUniformlyOn A a l K)
    {u : J → I} (hu : Tendsto u r l) : TendstoUniformlyOn (fun j => A (u j)) a r K :=
  fun V hV => hu.eventually (ha V hV)

lemma sqrt_tendsto_pos : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact Real.sqrt_pos.mpr ht

theorem weighted_taylor_uniformly_compact {f : E × F → G}
    (hf : AnalyticAt ℝ f 0) (hf0 : f 0 = 0)
    (hlin : ∀ z : E, fderiv ℝ f 0 (z,0) = 0) :
    ∃ q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) G,
      ∀ K : Set (E × F), IsCompact K →
      TendstoUniformlyOn (fun t x => t⁻¹ • f (weightedScale t x))
        (fun x => fderiv ℝ f 0 (0,x.2)+q (fun _ => x.1)) (𝓝[>] (0 : ℝ)) K := by
  obtain ⟨p,hp⟩ := hf
  let q := (p 2).compContinuousLinearMap (fun _ => ContinuousLinearMap.inl ℝ E F)
  refine ⟨q,fun K hK => ?_⟩
  have hh := parabolic_taylor_uniformly_compact hp hf0
    (fun z => by simpa only [multilinear_one_eval,← hp.fderiv_eq] using hlin z) hK
  have hu := uniform_reindex hh sqrt_tendsto_pos
  have hce : (fun x : E × F => p 1 (fun _ => (0,x.2))+p 2 (fun _ => (x.1,0))) =
      (fun x => fderiv ℝ f 0 (0,x.2)+q (fun _ => x.1)) := by
    funext x
    simp only [multilinear_one_eval,hp.fderiv_eq,q,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,ContinuousLinearMap.inl_apply]
  rw [hce] at hu
  apply hu.congr
  filter_upwards [self_mem_nhdsWithin] with t ht
  intro x _hx
  simp only [parabolicScale,weightedScale,Real.sq_sqrt ht.le]

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_WeightedSquaredChartLimit
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
namespace Release061
open Set Filter Metric Asymptotics
open scoped Topology
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma parabolicScale_tendsto (x : E × F) :
    Tendsto (fun u => parabolicScale u x) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hc : Continuous (fun u => parabolicScale u x) := by
    unfold parabolicScale
    fun_prop
  simpa [parabolicScale,Prod.zero_eq_mk] using (hc.tendsto 0).mono_left
    (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)

lemma parabolicScale_isBigO (x : E × F) :
    (fun u => parabolicScale u x) =O[𝓝[>] (0:ℝ)] (fun u : ℝ => u) := by
  apply IsBigO.of_bound ‖x‖
  filter_upwards [show ∀ᶠ u : ℝ in 𝓝[>] 0, 0 < u from self_mem_nhdsWithin,
    show ∀ᶠ u : ℝ in 𝓝[>] 0, u < 1 from
      (tendsto_order.mp (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (id : ℝ → ℝ) (𝓝[>] 0) (𝓝 0))).2 1 zero_lt_one] with u hu hu1
  simpa only [Real.norm_eq_abs,abs_of_pos hu,mul_comm] using
    parabolicScale_norm hu.le hu1.le x

theorem parabolic_first_derivative {Φ : E × F → G} {L : (E × F) →L[ℝ] G}
    (hΦ : HasFDerivAt Φ L 0) (x : E × F) :
    Tendsto (fun u : ℝ => u⁻¹ • (Φ (parabolicScale u x)-Φ 0))
      (𝓝[>] 0) (𝓝 (L (x.1,0))) := by
  have hrem : (fun u => Φ (parabolicScale u x)-Φ 0-L (parabolicScale u x))
      =o[𝓝[>] (0:ℝ)] (fun u : ℝ => u) := by
    have hh := hΦ.isLittleO.comp_tendsto (parabolicScale_tendsto x)
    simp only [sub_zero,Function.comp_def] at hh
    exact hh.trans_isBigO (parabolicScale_isBigO x)
  have hlin : Tendsto (fun u : ℝ => L (x.1,u • x.2)) (𝓝[>] 0) (𝓝 (L (x.1,0))) := by
    have hc : Continuous (fun u : ℝ => L (x.1,u • x.2)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hsum := hrem.tendsto_inv_smul_nhds_zero.add hlin
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [show ∀ᶠ u : ℝ in 𝓝[>] 0, 0 < u from self_mem_nhdsWithin] with u hu
  have hh : parabolicScale u x = u • (x.1,u • x.2) := by
    ext <;> simp [parabolicScale,pow_two,smul_smul]
  rw [hh,map_smul,smul_sub,inv_smul_smul₀ hu.ne',sub_add_cancel]

lemma weighted_first_derivative {Φ : E × F → G} {L : (E × F) →L[ℝ] G}
    (hΦ : HasFDerivAt Φ L 0) (x : E × F) :
    Tendsto (fun t : ℝ => (Real.sqrt t)⁻¹ • (Φ (weightedScale t x)-Φ 0))
      (𝓝[>] 0) (𝓝 (L (x.1,0))) := by
  have hh := (parabolic_first_derivative hΦ x).comp sqrt_tendsto_pos
  apply hh.congr'
  filter_upwards [show ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t from self_mem_nhdsWithin] with t ht
  simp only [Function.comp_def,parabolicScale,weightedScale,Real.sq_sqrt ht.le]

lemma weighted_squared_chart_limit {Φ : E × F → G} {L : (E × F) →L[ℝ] G}
    (hΦ : HasFDerivAt Φ L 0) (x : E × F) :
    Tendsto (fun t : ℝ => t⁻¹*‖Φ (weightedScale t x)-Φ 0‖^2)
      (𝓝[>] 0) (𝓝 (‖L (x.1,0)‖^2)) := by
  have hh := (weighted_first_derivative hΦ x).norm.pow 2
  apply hh.congr'
  filter_upwards [show ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t from self_mem_nhdsWithin] with t ht
  simp only [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (Real.sqrt_nonneg t),
    mul_pow,inv_pow,Real.sq_sqrt ht.le]

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ClosedMaximizerRelation
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
namespace Release061

section
open Set Filter Metric Complex
open scoped Topology
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem analytic_peak_weighted_bound {f : E × F → ℂ}
    {p : FormalMultilinearSeries ℂ (E × F) ℂ}
    (hf : HasFPowerSeriesAt f p 0) (hf0 : f 0 = 0)
    (hlin : ∀ z : E, p 1 (fun _ => (z,0)) = 0)
    {Φ : E × F → G} {L : (E × F) →L[ℝ] G}
    (hΦ : HasFDerivAt Φ L 0) (x : E × F)
    (hpeak : ∀ᶠ t : ℝ in 𝓝[>] 0,
      ‖Φ (weightedScale t x)-Φ 0‖^2 ≤ -(f (weightedScale t x)).re) :
    ‖L (x.1,0)‖^2 ≤ -(p 1 (fun _ => (0,x.2))+p 2 (fun _ => (x.1,0))).re := by
  have ht := parabolic_taylor_uniformly_compact (hf.restrictScalars (𝕜 := ℝ)) hf0
    hlin (isCompact_singleton (x := x))
  have ht' := (uniform_reindex ht sqrt_tendsto_pos).tendsto_at (mem_singleton x)
  have hh : Tendsto (fun t : ℝ => t⁻¹ • f (weightedScale t x)) (𝓝[>] 0)
      (𝓝 (p 1 (fun _ => (0,x.2))+p 2 (fun _ => (x.1,0)))) := by
    apply ht'.congr'
    filter_upwards [show ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t from self_mem_nhdsWithin] with t ht
    simp only [parabolicScale,weightedScale,Real.sq_sqrt ht.le]
  have hright : Tendsto (fun t : ℝ => t⁻¹*(-(f (weightedScale t x)).re)) (𝓝[>] 0)
      (𝓝 (-(p 1 (fun _ => (0,x.2))+p 2 (fun _ => (x.1,0))).re)) := by
    simpa only [Function.comp_def,neg_re,smul_re,smul_eq_mul,mul_neg] using
      (Complex.continuous_re.continuousAt.tendsto.comp hh).neg
  apply le_of_tendsto_of_tendsto (weighted_squared_chart_limit hΦ x) hright
  filter_upwards [hpeak,show ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t from self_mem_nhdsWithin] with t hp ht
  exact mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr ht.le)

end

open Set MeasureTheory _root_.Module Filter
open scoped Topology ENNReal

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CocompactChartDiscContinuity
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
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
namespace Release061
open scoped Topology
open Set Filter Metric

lemma affineClosedDiscCoordinate_continuous : Continuous affineClosedDiscCoordinate := by
  apply Continuous.subtype_mk
  exact (continuous_apply 0).comp continuous_subtype_val

theorem bounded_cocompact_chart_disc_continuity {n k : ℕ} {Γ : Type*}
    (V U : Set (Affine n)) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    [LocallyCompactSpace U] (hbounded : Bornology.IsBounded U)
    [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (K : Set U) (hK : IsCompact K) (hrep : ∀ x : U, ∃ k ∈ K, ∃ γ : Γ, γ • k = x)
    {ε : ℝ} (Φ : Affine k → Affine n)
    (hΦ : AnalyticOnNhd ℂ Φ (ball 0 ε)) (hΦV : MapsTo Φ (ball 0 ε) V) :
    Wiener.DiscContinuityWithin k (Φ ⁻¹' U) ε := by
  intro A hA hAh hsmall hbd hstart
  let B : Icc (0 : ℝ) 1 → closedBall (0 : Affine 1) 1 → V :=
    fun s x => ⟨Φ (A s (affineClosedDiscCoordinate x)),hΦV (by simpa only [mem_ball,dist_zero_right] using hsmall s (affineClosedDiscCoordinate x))⟩
  have hAc : Continuous (fun p : Icc (0 : ℝ) 1 × closedBall (0 : Affine 1) 1 =>
      A p.1 (affineClosedDiscCoordinate p.2)) :=
    hA.comp (continuous_fst.prodMk (affineClosedDiscCoordinate_continuous.comp continuous_snd))
  have hB : Continuous (Function.uncurry B) := by
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (hΦ _ (by simpa only [mem_ball,dist_zero_right] using hsmall p.1 (affineClosedDiscCoordinate p.2))).continuousAt.comp hAc.continuousAt
  have hBh (s : Icc (0 : ℝ) 1) : HolomorphicOnSubset (ball (0 : Affine 1) 1)
      (fun x => (B s ⟨x.val,ball_subset_closedBall x.property⟩).val) := by
    obtain ⟨g,hg,he⟩ := hAh s
    have hcoord : AnalyticOnNhd ℂ (fun x : Affine 1 => x 0) (ball 0 1) :=
      fun _ _ => (ContinuousLinearMap.proj 0 : Affine 1 →L[ℂ] ℂ).analyticAt _
    have hgP : AnalyticOnNhd ℂ (fun x : Affine 1 => g (x 0)) (ball 0 1) :=
      hg.comp hcoord (fun x hx => by
        simpa only [mem_ball,dist_zero_right,norm_affine_one] using hx)
    have hcomp : AnalyticOnNhd ℂ (fun x : Affine 1 => Φ (g (x 0))) (ball 0 1) := by
      apply hΦ.comp hgP
      intro x hx
      have hh := hsmall s (affineClosedDiscCoordinate ⟨x,ball_subset_closedBall hx⟩)
      rw [he] at hh
      simpa only [mem_ball,dist_zero_right,affineClosedDiscCoordinate] using hh
    intro p
    refine ⟨ball 0 1,isOpen_ball,p.property,fun x => Φ (g (x 0)),hcomp,?_⟩
    intro q _
    change Φ (g (q.val 0)) = Φ (A s (affineClosedDiscCoordinate ⟨q.val,ball_subset_closedBall q.property⟩))
    rw [he]; rfl
  have hall := bounded_cocompact_disc_continuity V U hUV hU hbounded hhol K hK hrep B hB hBh
    (fun s x hx => hbd s (affineClosedDiscCoordinate x) (by
      change ‖x.val 0‖ = 1; rwa [norm_affine_one] at hx))
    (fun x => hstart (affineClosedDiscCoordinate x))
  intro s z
  let x : closedBall (0 : Affine 1) 1 := ⟨fun _ => z.val,by
    rw [mem_closedBall,dist_zero_right,norm_affine_one]
    exact mem_closedBall_zero_iff.mp z.property⟩
  exact hall s x

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ComplexifyRealContinuousEquiv
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

section
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem positive_ray_mem_connectedComponentIn {C : Set E}
    (hC : ∀ r : ℝ, 0 < r → ∀ v ∈ C, r • v ∈ C)
    {v : E} (hv : v ∈ C) {r : ℝ} (hr : 0 < r) :
    r • v ∈ connectedComponentIn C v := by
  have hcont : Continuous (fun t : ℝ => t • v) := continuous_id.smul continuous_const
  have hpre : IsPreconnected ((fun t : ℝ => t • v) '' Ioi 0) :=
    isPreconnected_Ioi.image _ hcont.continuousOn
  have hmem : v ∈ (fun t : ℝ => t • v) '' Ioi 0 := ⟨1,by norm_num,one_smul ℝ v⟩
  have hsub : (fun t : ℝ => t • v) '' Ioi 0 ⊆ C := by
    rintro _ ⟨t,ht,rfl⟩
    exact hC t ht v hv
  exact hpre.subset_connectedComponentIn hmem hsub ⟨r,hr,rfl⟩

theorem cone_connectedComponentIn_smul_iff {C : Set E}
    (hC : ∀ r : ℝ, 0 < r → ∀ v ∈ C, r • v ∈ C)
    (a : E) {r : ℝ} (hr : 0 < r) (v : E) :
    r • v ∈ connectedComponentIn C a ↔ v ∈ connectedComponentIn C a := by
  have hpres : ∀ {s : ℝ}, 0 < s → ∀ {y : E}, y ∈ connectedComponentIn C a →
      s • y ∈ connectedComponentIn C a := by
    intro s hs y hy
    rw [connectedComponentIn_eq hy]
    exact positive_ray_mem_connectedComponentIn hC (connectedComponentIn_subset C a hy) hs
  constructor
  · intro hv
    have hi := hpres (inv_pos.mpr hr) hv
    simpa only [smul_smul,inv_mul_cancel₀ hr.ne',one_smul] using hi
  · exact hpres hr

theorem open_cone_component {C : Set E} (ho : IsOpen C)
    (hC : ∀ r : ℝ, 0 < r → ∀ v ∈ C, r • v ∈ C) {a : E} (ha : a ∈ C) :
    IsOpen (connectedComponentIn C a) ∧ IsConnected (connectedComponentIn C a) ∧
      ∀ r : ℝ, 0 < r → ∀ v,
        r • v ∈ connectedComponentIn C a ↔ v ∈ connectedComponentIn C a := by
  exact ⟨ho.connectedComponentIn,isConnected_connectedComponentIn_iff.mpr ha,
    fun _ hr v => cone_connectedComponentIn_smul_iff hC a hr v⟩

end

open Complex

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CoordinateDerivativeRank
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
-- module Solutions.OAIQ025_SD.SymmetricDomains_LogarithmicPeakBound
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
namespace Release061

open Set Complex

theorem logarithmic_peak_bound {X : Type*} (h : X → ℂ) (E : X → ℝ)
    {q : X} (hq : h q ≠ 0) (hb : ‖h q‖ ≤ Real.exp (-E q)) :
    (Complex.log (h q)).re ≤ -E q := by
  rw [Complex.log_re]
  apply Real.log_le_iff_le_exp (norm_pos_iff.mpr hq) |>.mpr
  exact hb

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SemialgebraicBoundaryFiniteNash
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
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
-- module Solutions.OAIQ025_SD.SymmetricDomains_SemialgebraicChartBoundaryData
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
open Set Filter Topology Metric MeasureTheory Classical
open SignElimination

lemma offset_joint_moving_limit {S E I : Type*} [TopologicalSpace S]
    [MetricSpace E] [SMul ℝ E] (A : S → Set E) {s₀ : S} {f : E → ℝ}
    (h : ∀ y, Tendsto (fun p : S × ℝ => offsetDistance A p.1 p.2 y)
      (𝓝[{p : S × ℝ | 0 < p.2}] (s₀,0)) (𝓝 (f y)))
    {l : Filter I} {s : I → S} {t : I → ℝ} {v : I → E} {w : E}
    (hs : Tendsto s l (𝓝 s₀)) (ht : Tendsto t l (𝓝 0))
    (hpos : ∀ᶠ i in l, 0 < t i) (hv : Tendsto v l (𝓝 w)) :
    Tendsto (fun i => offsetDistance A (s i) (t i) (v i)) l (𝓝 (f w)) := by
  have hp₀ : Tendsto (fun i : I => (s i,t i)) l (𝓝 (s₀,(0 : ℝ))) := hs.prodMk_nhds ht
  have hmem : ∀ᶠ i : I in l, (s i,t i) ∈ {p : S × ℝ | 0 < p.2} := hpos
  have hp : Tendsto (fun i : I => (s i,t i)) l (𝓝[{p : S × ℝ | 0 < p.2}] (s₀,0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hp₀,hmem⟩
  have hh := (h w).comp hp
  exact moving_offsetDistance_limit A s t hh hv

lemma offset_joint_excluded_limit {S E I : Type*} [TopologicalSpace S]
    [MetricSpace E] [SMul ℝ E] (A : S → Set E) {s₀ : S} {f : E → ℝ}
    (h : ∀ y, Tendsto (fun p : S × ℝ => offsetDistance A p.1 p.2 y)
      (𝓝[{p : S × ℝ | 0 < p.2}] (s₀,0)) (𝓝 (f y)))
    {l : Filter I} {s : I → S} {t : I → ℝ} {v : I → E} {w : E}
    (hs : Tendsto s l (𝓝 s₀)) (ht : Tendsto t l (𝓝 0))
    (hpos : ∀ᶠ i in l, 0 < t i) (hv : Tendsto v l (𝓝 w)) (hw : f w = 0) :
    Tendsto (fun i => infDist (v i) (offsetScaled A (s i) (t i))ᶜ) l (𝓝 0) := by
  apply tendsto_of_truncated_zero
  simpa only [offsetDistance, hw] using offset_joint_moving_limit A h hs ht hpos hv

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_OldOffsetOldPosition
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
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

theorem analytic_chart_right_inverse_of_dimension {m N : ℕ} {V : Set (Affine N)}
    {a : Affine m} (F : Affine m → Affine N) (G : Affine N → Affine m)
    (hF : AnalyticAt ℂ F a) (hG : AnalyticAt ℂ G (F a))
    (hGF : (G ∘ F) =ᶠ[𝓝 a] id)
    (hFV : ∀ᶠ z in 𝓝 a, F z ∈ V)
    (H : Affine m → Affine N) (J : Affine N → Affine m)
    (hH0 : H 0 = F a) (hH : AnalyticAt ℂ H 0) (hJ : AnalyticAt ℂ J (F a))
    (hJH : (J ∘ H) =ᶠ[𝓝 (0 : Affine m)] id)
    (hHJ : ∀ᶠ y in 𝓝[V] (F a), H (J y) = y) :
    ∀ᶠ y in 𝓝[V] (F a), F (G y) = y := by
  have hJ0 : J (F a) = 0 := by simpa only [Function.comp_apply,hH0,id_eq] using hJH.eq_of_nhds
  let A : Affine m → Affine m := J ∘ F
  have hA : AnalyticAt ℂ A a := hJ.comp hF
  have hA0 : A a = 0 := hJ0
  have htF : Tendsto F (𝓝 a) (𝓝[V] (F a)) := tendsto_nhdsWithin_iff.mpr ⟨hF.continuousAt,hFV⟩
  have hHA : (H ∘ A) =ᶠ[𝓝 a] F := htF hHJ
  have hH' : AnalyticAt ℂ H (A a) := hA0.symm ▸ hH
  have hdHA : (fderiv ℂ H (A a)).comp (fderiv ℂ A a) = fderiv ℂ F a :=
    ((hH'.differentiableAt.hasFDerivAt.comp a hA.differentiableAt.hasFDerivAt).congr_of_eventuallyEq hHA.symm).unique hF.differentiableAt.hasFDerivAt
  have hdGF : (fderiv ℂ G (F a)).comp (fderiv ℂ F a) = ContinuousLinearMap.id ℂ _ :=
    ((hG.differentiableAt.hasFDerivAt.comp a hF.differentiableAt.hasFDerivAt).congr_of_eventuallyEq hGF.symm).unique (hasFDerivAt_id a)
  have hi : Function.Injective (fderiv ℂ A a) := by
    intro u v huv
    have hw : (fderiv ℂ F a) u = (fderiv ℂ F a) v := by
      rw [← hdHA]
      exact congrArg (fderiv ℂ H (A a)) huv
    have hx := congrArg (fderiv ℂ G (F a)) hw
    simpa only [← ContinuousLinearMap.comp_apply,hdGF,ContinuousLinearMap.id_apply] using hx
  let L := ((fderiv ℂ A a).toLinearMap.linearEquivOfInjective hi rfl).toContinuousLinearEquiv
  have hL : (L : Affine m →L[ℂ] Affine m) = fderiv ℂ A a := rfl
  obtain ⟨e,he,hes,hea⟩ := analytic_local_inverse hA L (hL.symm ▸ hA.differentiableAt.hasFDerivAt)
  have heAa : e a = A a := congrFun he a
  have hesym : e.symm (A a) = a := by rw [← heAa]; exact e.left_inv hes
  have hetarget : A a ∈ e.target := heAa ▸ e.map_source hes
  have het : Tendsto e.symm (𝓝 (A a)) (𝓝 a) := by
    simpa only [ContinuousAt,hesym] using hea.continuousAt
  let B : Affine N → Affine m := e.symm ∘ J
  have hB : Tendsto B (𝓝 (F a)) (𝓝 a) := het.comp hJ.continuousAt
  have hBHA : ∀ᶠ y in 𝓝 (F a), H (A (B y)) = F (B y) := hB hHA
  have hBGF : ∀ᶠ y in 𝓝 (F a), G (F (B y)) = B y := hB hGF
  have hJt : ∀ᶠ y in 𝓝 (F a), J y ∈ e.target :=
    hJ.continuousAt (e.open_target.mem_nhds hetarget)
  filter_upwards [hHJ,mem_nhdsWithin_of_mem_nhds hBHA,
    mem_nhdsWithin_of_mem_nhds hBGF,mem_nhdsWithin_of_mem_nhds hJt] with y hy hya hyb hyt
  have hAB : A (B y) = J y := by
    simpa only [he,B,Function.comp_apply] using e.right_inv hyt
  have hFB : F (B y) = y := by rw [← hya,hAB,hy]
  rw [hFB] at hyb
  rw [hyb,hFB]

theorem ProjectionNashChart.right_inverse_at {N m : ℕ} {V : Set (Affine N)}
    {p : Affine N} (c : ProjectionNashChart V p m) {a : Affine m}
    (ha : ‖complexRealEquiv m a‖ < c.radius)
    (H : Affine m → Affine N) (J : Affine N → Affine m)
    (hH0 : H 0 = c.inverse a) (hH : AnalyticAt ℂ H 0)
    (hJ : AnalyticAt ℂ J (c.inverse a))
    (hJH : (J ∘ H) =ᶠ[𝓝 (0 : Affine m)] id)
    (hHJ : ∀ᶠ y in 𝓝[V] (c.inverse a), H (J y) = y) :
    ∀ᶠ y in 𝓝[V] (c.inverse a), c.inverse (c.projection (y-p)) = y := by
  have hT : IsOpen {z : Affine m | ‖complexRealEquiv m z‖ < c.radius} :=
    isOpen_lt ((complexRealEquiv m).continuous.norm) continuous_const
  apply analytic_chart_right_inverse_of_dimension c.inverse (fun y => c.projection (y-p))
    (c.inverse_analytic a ha) ((c.projection.analyticAt _).comp (analyticAt_id.sub analyticAt_const))
    _ _ H J hH0 hH hJ hJH hHJ
  · filter_upwards [hT.mem_nhds ha] with z hz
    exact c.left_inverse z hz
  · filter_upwards [hT.mem_nhds ha] with z hz
    exact c.inverse_mem z hz

namespace NashBoundaryChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

 theorem oldOffset_analyticAt (c : NashBoundaryChart (m := m) U V B q) {s}
    (hs : s ∈ ball 0 c.graphRadius) : AnalyticAt ℝ c.oldOffset (c.oldPosition s) := by
  have hC := c.normal.realCoordinates.toContinuousLinearMap.analyticAt (c.oldPosition s)
  have hp : AnalyticAt ℝ c.oldParameter (c.oldPosition s) := analyticAt_fst.comp hC
  have hφ : AnalyticAt ℝ c.normal.graph (c.oldParameter (c.oldPosition s)) := by
    simpa only [oldParameter_oldPosition] using c.normal.graph_analytic s (ball_subset_ball c.graphRadius_le hs)
  exact (analyticAt_snd.comp hC).sub (hφ.comp hp)

 theorem oldPosition_inverse (c : NashBoundaryChart (m := m) U V B q) {x}
    (hgood : c.GoodAt x) : c.chart.inverse (c.oldPosition (c.normal.parameters x)) = q x := by
  simpa only [oldPosition,c.normal.parameters.left_inv hgood.1] using
    (c.graph_boundary (c.normal.parameters x) hgood.2.1).2.2

 theorem oldPosition_projection (c : NashBoundaryChart (m := m) U V B q) {x}
    (hgood : c.GoodAt x) : c.oldPosition (c.normal.parameters x) = c.chart.projection (q x-q c.center) := by
  have h := c.chart.left_inverse (c.oldPosition (c.normal.parameters x))
    (c.graph_boundary (c.normal.parameters x) hgood.2.1).2.1
  rw [c.oldPosition_inverse hgood] at h
  exact h.symm

end NashBoundaryChart
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ProjectionTangentGeneric
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
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

theorem coordinate_rank_ge_of_chart_generic {d m N : ℕ}
    (q : (Fin d → ℝ) → Affine N) {x : Fin d → ℝ}
    (J : Affine N → Affine m) (hJ : AnalyticAt ℂ J (q x))
    (hq : DifferentiableAt ℝ q x)
    (hgen : Submodule.span ℂ (range (fderiv ℝ (J ∘ q) x)) = ⊤) :
    m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)) := by
  let M := (fderiv ℂ J (q x)).toLinearMap
  let S := Submodule.span ℂ (range (fderiv ℝ q x))
  have hd : fderiv ℝ (J ∘ q) x = ((fderiv ℂ J (q x)).restrictScalars ℝ).comp (fderiv ℝ q x) :=
    ((hJ.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp x hq.hasFDerivAt).fderiv
  have hmap : S.map M = ⊤ := by
    dsimp only [S]
    rw [Submodule.map_span]
    have he : M '' range (fderiv ℝ q x) = range (fderiv ℝ (J ∘ q) x) := by
      rw [← range_comp,hd]
      rfl
    rw [he,hgen]
  rw [coordinate_derivative_rank q hq]
  have hh := Submodule.finrank_map_le M S
  rw [hmap] at hh
  simpa only [finrank_top,Affine,Module.finrank_pi,Fintype.card_fin,S] using hh

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GenericSurjectiveRealNormal
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
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
namespace Release061.NashBoundaryChart
open Set Filter Topology Metric
open scoped Classical
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

 theorem oldOffset_hasFDerivAt (c : NashBoundaryChart (m := m) U V B q) {s}
    (hs : s ∈ ball 0 c.graphRadius) :
    HasFDerivAt c.oldOffset (c.oldOffsetDerivative s) (c.oldPosition s) := by
  have hC := c.normal.realCoordinates.toContinuousLinearMap.hasFDerivAt (x := c.oldPosition s)
  have hP := (ContinuousLinearMap.fst ℝ _ _).hasFDerivAt.comp (c.oldPosition s) hC
  have hQ := (ContinuousLinearMap.snd ℝ _ _).hasFDerivAt.comp (c.oldPosition s) hC
  have hφ := (c.normal.graph_analytic s (ball_subset_ball c.graphRadius_le hs)).differentiableAt.hasFDerivAt
  have hφ' : HasFDerivAt c.normal.graph (fderiv ℝ c.normal.graph s)
      (c.oldParameter (c.oldPosition s)) := by simpa only [oldParameter_oldPosition] using hφ
  exact hQ.sub (hφ'.comp (c.oldPosition s) hP)

end Release061.NashBoundaryChart

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_OffsetDerivative
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
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

namespace NashBoundaryScalingChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N} {c : NashBoundaryChart (m := m) U V B q}
variable {x : Fin d → ℝ}

theorem offset_derivative (s : NashBoundaryScalingChart c x) (hgood : c.GoodAt x)
    (z : Affine s.tangentDim × Affine s.normalDim) :
    fderiv ℝ (fun y => (s.offsets y).2) 0 z = s.normalMap (Flatten.imaginaryPart s.normalDim z.2) := by
  let a := c.oldPosition (c.normal.parameters x)
  let f : (Affine s.tangentDim × Affine s.normalDim) → Affine m := fun y => s.coordinates.symm y+a
  have hf : HasFDerivAt f (s.coordinates.symm.toContinuousLinearMap.restrictScalars ℝ) 0 :=
    (s.coordinates.symm.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.add_const a
  have hD : HasFDerivAt c.oldOffset (c.oldOffsetDerivative (c.normal.parameters x)) (f 0) := by
    simpa only [f,map_zero,zero_add] using c.oldOffset_hasFDerivAt hgood.2.1
  have he : (fun y => (s.offsets y).2) = c.oldOffset ∘ f := by
    funext y
    rw [s.offsets_eq]
    rfl
  rw [he,(hD.comp 0 hf).fderiv]
  exact s.differential z
end NashBoundaryScalingChart
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SelectExcludedOffsets
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
namespace Release061
open Set Filter Metric
open scoped Topology

lemma compact_eventual_inclusion {X : Type*} [MetricSpace X] {K : Set X}
    (hK : IsCompact K) (D : ℝ → Set X)
    (htest : ∀ (t : ℕ → ℝ) (x : ℕ → X) (a : X),
      Tendsto t atTop (𝓝 0) → (∀ j, 0 < t j) → (∀ j, x j ∈ K) →
      a ∈ K → Tendsto x atTop (𝓝 a) → ∀ᶠ j in atTop, x j ∈ D (t j)) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, K ⊆ D t := by
  by_contra h
  have hfreq : ∃ᶠ t : ℝ in 𝓝[>] 0, ¬ K ⊆ D t := not_eventually.mp h
  have hex (j : ℕ) : ∃ t : ℝ, 0 < t ∧ t < 1/((j:ℝ)+1) ∧ ∃ x ∈ K, x ∉ D t := by
    have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1/((j:ℝ)+1) :=
      (tendsto_order.mp (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (id : ℝ → ℝ) (𝓝[>] 0) (𝓝 0))).2 _ (by positivity)
    obtain ⟨t,ht,htp,hts⟩ := (hfreq.and_eventually ((show ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t from self_mem_nhdsWithin).and hsmall)).exists
    obtain ⟨x,hx,hxd⟩ := not_subset.mp ht
    exact ⟨t,htp,hts,x,hx,hxd⟩
  choose t htp hts x hx hxd using hex
  have ht : Tendsto t atTop (𝓝 0) := squeeze_zero (fun j => (htp j).le)
    (fun j => (hts j).le) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨a,ha,φ,hφ,hxa⟩ := hK.tendsto_subseq hx
  have hh := htest (t ∘ φ) (x ∘ φ) a (ht.comp hφ.tendsto_atTop)
    (fun j => htp (φ j)) (fun j => hx (φ j)) ha hxa
  obtain ⟨j,hj⟩ := hh.exists
  exact hxd (φ j) hj

lemma offsetDistance_pos_mem {S E : Type*} [MetricSpace E] [SMul ℝ E]
    (A : S → Set E) (s : S) (t : ℝ) (v : E)
    (h : 0 < offsetDistance A s t v) : v ∈ offsetScaled A s t := by
  by_contra hn
  have hz : offsetDistance A s t v = 0 := by
    rw [offsetDistance,infDist_zero_of_mem hn]
    norm_num
  exact (ne_of_gt h) hz

theorem compact_inclusion_from_offsets {X S E : Type*} [MetricSpace X]
    [PseudoMetricSpace S] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : S → Set E) (D : ℝ → Set X) (s : ℝ → X → S) (Rₜ : ℝ → X → E)
    (R : X → E) (d : E → ℝ) (s₀ : S)
    {K : Set X} (hK : IsCompact K) (hRcont : ContinuousOn R K)
    (hs : TendstoUniformlyOn s (fun _ => s₀) (𝓝[>] (0 : ℝ)) K)
    (hR : TendstoUniformlyOn Rₜ R (𝓝[>] (0 : ℝ)) K)
    (hjoint : ∀ (s' : ℕ → S) (t' : ℕ → ℝ), Tendsto s' atTop (𝓝 s₀) →
      Tendsto t' atTop (𝓝 0) → (∀ j, 0 < t' j) → ∀ v : E,
      Tendsto (fun j => offsetDistance A (s' j) (t' j) v) atTop (𝓝 (d v)))
    (hmatch : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ x ∈ K,
      (x ∈ D t ↔ Rₜ t x ∈ offsetScaled A (s t x) t))
    (hpos : ∀ x ∈ K, 0 < d (R x)) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, K ⊆ D t := by
  apply compact_eventual_inclusion hK D
  intro t x a ht htp hx ha hxa
  have ht' : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall htp⟩
  have hxa' : Tendsto x atTop (𝓝[K] a) :=
    tendsto_nhdsWithin_iff.mpr ⟨hxa,Eventually.of_forall hx⟩
  have hs' : Tendsto (fun j => s (t j) (x j)) atTop (𝓝 s₀) :=
    (uniform_reindex hs ht').tendsto_comp continuousWithinAt_const hxa'
  have hR' : Tendsto (fun j => Rₜ (t j) (x j)) atTop (𝓝 (R a)) :=
    (uniform_reindex hR ht').tendsto_comp (hRcont a ha) hxa'
  have hd := moving_offsetDistance_limit A (fun j => s (t j) (x j)) t
    (hjoint _ t hs' ht htp (R a)) hR'
  filter_upwards [(tendsto_order.mp hd).1 0 (hpos a ha),ht'.eventually hmatch] with j hj hm
  exact (hm (x j) (hx j)).mpr (offsetDistance_pos_mem A _ _ _ hj)

lemma select_excluded_offsets {S E : Type*} [MetricSpace E] [SMul ℝ E]
    (A : S → Set E) (s : ℕ → S) (t : ℕ → ℝ) (v : ℕ → E)
    (hne : ∀ j, (offsetScaled A (s j) (t j))ᶜ.Nonempty)
    (hd : Tendsto (fun j => infDist (v j) (offsetScaled A (s j) (t j))ᶜ) atTop (𝓝 0)) :
    ∃ u : ℕ → E, (∀ j, u j ∉ offsetScaled A (s j) (t j)) ∧
      Tendsto (fun j => dist (u j) (v j)) atTop (𝓝 0) := by
  have hex (j : ℕ) : ∃ u ∈ (offsetScaled A (s j) (t j))ᶜ,
      dist (v j) u < infDist (v j) (offsetScaled A (s j) (t j))ᶜ+1/((j:ℝ)+1) :=
    (infDist_lt_iff (hne j)).mp (lt_add_of_pos_right _ (by positivity))
  choose u hu hdu using hex
  refine ⟨u,hu,?_⟩
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun j => by simpa only [dist_comm] using (hdu j).le)
  simpa only [zero_add] using hd.add tendsto_one_div_add_atTop_nhds_zero_nat

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_WeightedUnscaleC1Error
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
namespace Release061
open Set Filter Metric
open scoped Topology NNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma weightedUnscale_sub (t : ℝ) (x y : E × F) :
    weightedUnscale t (x-y) = weightedUnscale t x-weightedUnscale t y := by
  ext <;> simp [weightedUnscale,smul_sub]

lemma weightedUnscale_norm {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (x : E × F) :
    ‖weightedUnscale t x‖ ≤ t⁻¹*‖x‖ := by
  have hs : t ≤ Real.sqrt t := by
    have hs0 := Real.sqrt_nonneg t
    have hs1 : Real.sqrt t ≤ 1 := by exact (Real.sqrt_le_one).mpr ht1
    nlinarith [Real.sq_sqrt ht.le]
  have hi : (Real.sqrt t)⁻¹ ≤ t⁻¹ := inv_anti₀ ht hs
  rw [weightedUnscale,Prod.norm_def,max_le_iff]
  constructor
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    exact (mul_le_mul_of_nonneg_right hi (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le x) (inv_nonneg.mpr ht.le))
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr ht.le)]
    exact mul_le_mul_of_nonneg_left (norm_snd_le x) (inv_nonneg.mpr ht.le)

lemma weightedScale_uniform_zero {K : Set (E × F)} (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn (fun t x => weightedScale t x) (fun _ => 0)
      (𝓝[>] (0 : ℝ)) K := by
  obtain ⟨M,hM,hMK⟩ := hK.exists_pos_norm_le
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hs : Tendsto (fun t : ℝ => Real.sqrt t*M) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_mul] using sqrt_tendsto_pos.mono_right nhdsWithin_le_nhds |>.mul_const M
  filter_upwards [self_mem_nhdsWithin,(tendsto_order.mp hs).2 ε hε,
    tendsto_id.mono_left nhdsWithin_le_nhds |>.eventually (Iio_mem_nhds (show (0:ℝ) < 1 from zero_lt_one))] with t ht he ht1
  intro x hx
  have hδ : weightedScale t x = parabolicScale (Real.sqrt t) x := by
    simp only [weightedScale,parabolicScale,Real.sq_sqrt ht.le]
  rw [dist_zero_left,hδ]
  exact ((parabolicScale_norm (Real.sqrt_nonneg _) ((Real.sqrt_le_one).mpr ht1.le) x).trans
    (mul_le_mul_of_nonneg_left (hMK x hx) (Real.sqrt_nonneg _))).trans_lt he

lemma weightedScale_continuous_uniform {Y : Type*} [UniformSpace Y]
    {f : E × F → Y} (hf : ContinuousAt f 0) {K : Set (E × F)}
    (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn (fun t x => f (weightedScale t x)) (fun _ => f 0)
      (𝓝[>] (0 : ℝ)) K := by
  apply tendsto_prod_principal_iff.mp
  exact hf.tendsto.comp (tendsto_prod_principal_iff.mpr (weightedScale_uniform_zero hK))

lemma weightedScale_eventually_mem {K : Set (E × F)} (hK : Bornology.IsBounded K)
    {U : Set (E × F)} (hU : U ∈ 𝓝 (0 : E × F)) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ x ∈ K, weightedScale t x ∈ U := by
  have hh := (tendsto_prod_principal_iff.mpr (weightedScale_uniform_zero hK)).eventually hU
  rw [Filter.eventually_prod_principal_iff] at hh
  exact hh

theorem weightedUnscale_C1_error {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {χ : Y → E × F} {y₀ : Y} (hχ : ContDiffAt ℝ 1 χ y₀)
    {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝 0)) (htp : ∀ j, 0 < t j)
    {q q' : ℕ → Y} (hq : Tendsto q atTop (𝓝 y₀)) (hq' : Tendsto q' atTop (𝓝 y₀))
    (herr : Tendsto (fun j => (t j)⁻¹*dist (q' j) (q j)) atTop (𝓝 0)) :
    Tendsto (fun j => weightedUnscale (t j) (χ (q' j))-
      weightedUnscale (t j) (χ (q j))) atTop (𝓝 0) := by
  obtain ⟨C,V,hV,hC⟩ := hχ.exists_lipschitzOnWith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (show ∀ᶠ j in atTop, ‖weightedUnscale (t j) (χ (q' j))-
      weightedUnscale (t j) (χ (q j))‖ ≤ (C:ℝ)*((t j)⁻¹*dist (q' j) (q j)) from ?_)
    (by simpa only [mul_zero] using herr.const_mul (C:ℝ))
  filter_upwards [hq.eventually hV,hq'.eventually hV,(tendsto_order.mp ht).2 1 zero_lt_one]
    with j hqv hqv' ht1
  rw [← weightedUnscale_sub]
  calc ‖weightedUnscale (t j) (χ (q' j)-χ (q j))‖
      ≤ (t j)⁻¹*‖χ (q' j)-χ (q j)‖ := weightedUnscale_norm (htp j) ht1.le _
    _ ≤ (t j)⁻¹*((C:ℝ)*dist (q' j) (q j)) :=
      mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hC.dist_le_mul _ hqv' _ hqv)
        (inv_nonneg.mpr (htp j).le)
    _ = (C:ℝ)*((t j)⁻¹*dist (q' j) (q j)) := by ring

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_WeightedChartTwoSided
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
namespace Release061
open Set Filter Metric
open scoped Topology
variable {E F S V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma weightedScale_point_tendsto (x : E × F) :
    Tendsto (fun t => weightedScale t x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  (weightedScale_uniform_zero (isCompact_singleton (x := x)).isBounded).tendsto_at (mem_singleton x)

theorem excluded_points_in_scaled_chart
    (e : OpenPartialHomeomorph (E × F) (S × V)) (A : S → Set V)
    (he : (0 : E × F) ∈ e.source) {s₀ : S} (he0 : e 0 = (s₀,0))
    (hei : ContDiffAt ℝ 1 e.symm (s₀,0)) (hA : ∀ s, (0 : V) ∉ A s)
    (d : V → ℝ)
    (hjoint : ∀ (s' : ℕ → S) (t' : ℕ → ℝ), Tendsto s' atTop (𝓝 s₀) →
      Tendsto t' atTop (𝓝 0) → (∀ j, 0 < t' j) → ∀ v : V,
      Tendsto (fun j => offsetDistance A (s' j) (t' j) v) atTop (𝓝 (d v)))
    (x : E × F) {r : V}
    (hr : Tendsto (fun t => t⁻¹ • (e (weightedScale t x)).2) (𝓝[>] (0 : ℝ)) (𝓝 r))
    (hdr : d r = 0) (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0)) (htp : ∀ j, 0 < t j) :
    ∃ y : ℕ → E × F, Tendsto y atTop (𝓝 x) ∧
      (∀ j, y j ∉ chartScaledDomain e A (t j)) ∧
      ∀ j, weightedScale (t j) (y j) ∈ e.source := by
  classical
  have ht' : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall htp⟩
  let q : ℕ → S × V := fun j => e (weightedScale (t j) x)
  let v : ℕ → V := fun j => (t j)⁻¹ • (q j).2
  have hδ := (weightedScale_point_tendsto x).comp ht'
  have hq : Tendsto q atTop (𝓝 (s₀,0)) := by
    simpa only [q,Function.comp_def,he0] using (e.continuousAt he).tendsto.comp hδ
  have hv : Tendsto v atTop (𝓝 r) := hr.comp ht'
  have hd : Tendsto (fun j => infDist (v j) (offsetScaled A (q j).1 (t j))ᶜ) atTop (𝓝 0) :=
    excluded_limit_from_offsetDistance A (fun j => (q j).1) t
      (by simpa only [hdr,Function.comp_def] using hjoint _ t ((continuous_fst.tendsto (s₀,(0:V))).comp hq) ht htp r) hv
  obtain ⟨u,hu,hud⟩ := select_excluded_offsets A (fun j => (q j).1) t v
    (fun j => offset_excluded_nonempty A _ _ (hA _)) hd
  let q' : ℕ → S × V := fun j => ((q j).1,(t j) • u j)
  have hdiff (j : ℕ) : dist (q' j) (q j) = t j * dist (u j) (v j) := by
    have hc : (t j) • v j = (q j).2 := by simp only [v,smul_inv_smul₀ (htp j).ne']
    change dist ((q j).1,(t j) • u j) (q j) = _
    rw [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg (x := (t j) • u j) (y := (q j).2))]
    rw [← hc,dist_smul₀,Real.norm_eq_abs,abs_of_pos (htp j)]
  have hqd : Tendsto (fun j => dist (q' j) (q j)) atTop (𝓝 0) := by
    simp_rw [hdiff]
    simpa only [zero_mul] using ht.mul hud
  have hq' : Tendsto q' atTop (𝓝 (s₀,0)) :=
    hq.congr_dist (by simpa only [dist_comm] using hqd)
  have herr : Tendsto (fun j => (t j)⁻¹*dist (q' j) (q j)) atTop (𝓝 0) := by
    simpa only [hdiff,inv_mul_cancel_left₀ (htp _).ne'] using hud
  have herror := weightedUnscale_C1_error hei ht htp hq hq' herr
  have hsource : ∀ᶠ j in atTop, weightedScale (t j) x ∈ e.source :=
    hδ.eventually (e.open_source.mem_nhds he)
  have hrest : ∀ᶠ j in atTop, weightedUnscale (t j) (e.symm (q j)) = x := by
    filter_upwards [hsource] with j hj
    change weightedUnscale (t j) (e.symm (e (weightedScale (t j) x))) = x
    rw [e.left_inv hj,weightedUnscale_scale (htp j)]
  have hylim : Tendsto (fun j => weightedUnscale (t j) (e.symm (q' j))) atTop (𝓝 x) := by
    apply tendsto_sub_nhds_zero_iff.mp
    exact herror.congr' (hrest.mono fun j hj => by rw [hj])
  have htarget : (s₀,(0:V)) ∈ e.target := he0 ▸ e.map_source he
  have hevent : ∀ᶠ j in atTop, q' j ∈ e.target := hq'.eventually (e.open_target.mem_nhds htarget)
  let y : ℕ → E × F := fun j => if q' j ∈ e.target then
    weightedUnscale (t j) (e.symm (q' j)) else 0
  have hy0 (j : ℕ) : weightedScale (t j) (0 : E × F) = 0 := by simp [weightedScale]
  refine ⟨y,hylim.congr' (hevent.mono fun j hj => by simp only [y,ite_eq_left hj]),?_,?_⟩
  · intro j
    by_cases hj : q' j ∈ e.target
    · have hc : weightedScale (t j) (y j) = e.symm (q' j) := by
        simp only [y,ite_eq_left hj,weightedScale_unscale (htp j)]
      intro hmem
      have hnormal := hmem.2
      rw [hc,e.right_inv hj] at hnormal
      exact hu j hnormal
    · intro hmem
      have hnormal := hmem.2
      simp only [y,ite_eq_right hj,hy0,he0] at hnormal
      exact hA s₀ hnormal
  · intro j
    by_cases hj : q' j ∈ e.target
    · simpa only [y,ite_eq_left hj,weightedScale_unscale (htp j)] using e.map_target hj
    · simpa only [y,ite_eq_right hj,hy0] using he

theorem weighted_chart_two_sided
    (e : OpenPartialHomeomorph (E × F) (S × V)) (A : S → Set V)
    (he : (0 : E × F) ∈ e.source) {s₀ : S} (he0 : e 0 = (s₀,0))
    (hei : ContDiffAt ℝ 1 e.symm (s₀,0)) (hA : ∀ s, (0 : V) ∉ A s)
    (ha : AnalyticAt ℝ (fun x => (e x).2) 0)
    (hlin : ∀ z : E, fderiv ℝ (fun x => (e x).2) 0 (z,0) = 0)
    (d : V → ℝ) (hd : ∀ v, 0 ≤ d v)
    (hjoint : ∀ (s' : ℕ → S) (t' : ℕ → ℝ), Tendsto s' atTop (𝓝 s₀) →
      Tendsto t' atTop (𝓝 0) → (∀ j, 0 < t' j) → ∀ v : V,
      Tendsto (fun j => offsetDistance A (s' j) (t' j) v) atTop (𝓝 (d v))) :
    ∃ Q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) V,
      let R : E × F → V := fun x => fderiv ℝ (fun x => (e x).2) 0 (0,x.2)+Q (fun _ => x.1)
      (∀ K : Set (E × F), IsCompact K → K ⊆ {x | d (R x) ≠ 0} →
        ∀ᶠ t : ℝ in 𝓝[>] 0, K ⊆ chartScaledDomain e A t) ∧
      (∀ x : E × F, d (R x) = 0 → ∀ (t : ℕ → ℝ),
        Tendsto t atTop (𝓝 0) → (∀ j, 0 < t j) →
        ∃ y : ℕ → E × F, Tendsto y atTop (𝓝 x) ∧
          (∀ j, y j ∉ chartScaledDomain e A (t j)) ∧
          ∀ j, weightedScale (t j) (y j) ∈ e.source) := by
  obtain ⟨Q,hQ⟩ := weighted_taylor_uniformly_compact ha
    (by simp only [he0]) hlin
  refine ⟨Q,?_,?_⟩
  · intro K hK hKR
    apply compact_inclusion_from_offsets A (chartScaledDomain e A)
      (fun t x => (e (weightedScale t x)).1)
      (fun t x => t⁻¹ • (e (weightedScale t x)).2)
      (fun x => fderiv ℝ (fun x => (e x).2) 0 (0,x.2)+Q (fun _ => x.1)) d s₀ hK
    · fun_prop
    · simpa only [he0] using weightedScale_continuous_uniform
        (e.continuousAt he |>.fst) hK.isBounded
    · exact hQ K hK
    · exact hjoint
    · filter_upwards [weightedScale_eventually_mem hK.isBounded (e.open_source.mem_nhds he),
        self_mem_nhdsWithin] with t ht htp
      intro x hx
      have htpos : 0 < t := htp
      simp only [chartScaledDomain,mem_ofPred_eq,ht x hx,true_and,offsetScaled,
        smul_inv_smul₀ htpos.ne']
    · intro x hx
      exact lt_of_le_of_ne (hd _) (Ne.symm (hKR hx))
  · intro x hx t ht htp
    exact excluded_points_in_scaled_chart e A he he0 hei hA d hjoint x
      ((hQ {x} isCompact_singleton).tendsto_at (mem_singleton x)) hx t ht htp

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_Cutoff
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
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
namespace NashBoundaryChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

lemma family_zero_not_mem (c : NashBoundaryChart (m := m) U V B q) (s) :
    0 ∉ c.family s := by
  intro h
  have hs := h.1
  have hbd := (c.graph_boundary s hs).1.2
  exact hbd (by simpa only [add_zero] using h.2.2)
end NashBoundaryChart

namespace NashBoundaryScalingChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N} {c : NashBoundaryChart (m := m) U V B q}
variable {x : Fin d → ℝ}

theorem two_sided (s : NashBoundaryScalingChart c x) (hgood : c.GoodAt x)
    (f : (Fin c.normal.normalDim → ℝ) → ℝ)
    (hf : ∀ y, Tendsto (fun p : (Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ) × ℝ =>
      offsetDistance c.family p.1 p.2 y)
      (𝓝[{p : (Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ) × ℝ | 0 < p.2}]
        (c.normal.parameters x,0)) (𝓝 (f y)))
    (hfnonneg : ∀ y, 0 ≤ f y) :
    ∃ Q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Affine s.tangentDim) (Fin c.normal.normalDim → ℝ),
      let R : Affine s.tangentDim × Affine s.normalDim → (Fin c.normal.normalDim → ℝ) :=
        fun z => s.normalMap (Flatten.imaginaryPart s.normalDim z.2)+Q (fun _ => z.1)
      (∀ K : Set (Affine s.tangentDim × Affine s.normalDim), IsCompact K → K ⊆ {z | f (R z) ≠ 0} →
        ∀ᶠ t : ℝ in 𝓝[>] 0, K ⊆ chartScaledDomain s.offsets c.family t) ∧
      (∀ z : Affine s.tangentDim × Affine s.normalDim, f (R z) = 0 → ∀ t : ℕ → ℝ,
        Tendsto t atTop (𝓝 0) → (∀ j, 0 < t j) →
        ∃ y : ℕ → Affine s.tangentDim × Affine s.normalDim, Tendsto y atTop (𝓝 z) ∧
          (∀ j, y j ∉ chartScaledDomain s.offsets c.family (t j)) ∧
          ∀ j, weightedScale (t j) (y j) ∈ s.offsets.source) := by
  have hlin : ∀ z : Affine s.tangentDim, fderiv ℝ (fun y => (s.offsets y).2) 0 (z,0) = 0 := by
    intro z
    rw [s.offset_derivative hgood]
    simp only [map_zero]
  have hjoint : ∀ (a : ℕ → (Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ))
      (t : ℕ → ℝ), Tendsto a atTop (𝓝 (c.normal.parameters x)) → Tendsto t atTop (𝓝 0) →
      (∀ j, 0 < t j) → ∀ v, Tendsto (fun j => offsetDistance c.family (a j) (t j) v) atTop (𝓝 (f v)) := by
    intro a t ha ht htp v
    have hp : Tendsto (fun j => (a j,t j)) atTop
        (𝓝[{p : (Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ) × ℝ | 0 < p.2}]
          (c.normal.parameters x,0)) :=
      tendsto_nhdsWithin_iff.mpr ⟨ha.prodMk_nhds ht,Eventually.of_forall htp⟩
    exact Filter.Tendsto.comp (f := fun j => (a j,t j)) (g := fun p => offsetDistance c.family p.1 p.2 v) (hf v) hp
  obtain ⟨Q,hQ⟩ := weighted_chart_two_sided s.offsets c.family s.source_zero s.offsets_zero
    s.inverse_analytic.contDiffAt (c.family_zero_not_mem) (analyticAt_snd.comp s.analytic) hlin f hfnonneg hjoint
  refine ⟨Q,?_⟩
  simpa only [s.offset_derivative hgood] using hQ

theorem exists_cutoff (s : NashBoundaryScalingChart c x) (hgood : c.GoodAt x) :
    ∃ s' : NashBoundaryScalingChart c x,
      s'.tangentDim=s.tangentDim ∧ s'.normalDim=s.normalDim ∧
      ∀ z ∈ s'.offsets.source,
        c.oldParameter (s'.coordinates.symm z+c.oldPosition (c.normal.parameters x)) ∈ ball 0 c.graphRadius ∧
        ‖complexRealEquiv m (s'.coordinates.symm z+c.oldPosition (c.normal.parameters x))‖ < c.chart.radius ∧
        ‖c.oldOffset (s'.coordinates.symm z+c.oldPosition (c.normal.parameters x))‖ < 1 := by
  let a := c.oldPosition (c.normal.parameters x)
  have hs : ∀ᶠ z : Affine s.tangentDim × Affine s.normalDim in 𝓝 0,
      c.oldParameter (s.coordinates.symm z+a) ∈ ball 0 c.graphRadius := by
    have hcont : ContinuousAt (fun z => c.oldParameter (s.coordinates.symm z+a)) 0 :=
      (continuous_fst.comp (c.normal.realCoordinates.continuous.comp
        (s.coordinates.symm.continuous.add continuous_const))).continuousAt
    apply hcont.preimage_mem_nhds
    simpa only [map_zero,zero_add,a,c.oldParameter_oldPosition] using isOpen_ball.mem_nhds hgood.2.1
  have hn : ∀ᶠ z : Affine s.tangentDim × Affine s.normalDim in 𝓝 0,
      ‖complexRealEquiv m (s.coordinates.symm z+a)‖ < c.chart.radius := by
    have hcont : ContinuousAt (fun z => ‖complexRealEquiv m (s.coordinates.symm z+a)‖) 0 :=
      ((complexRealEquiv m).continuous.comp (s.coordinates.symm.continuous.add continuous_const)).norm.continuousAt
    apply hcont.eventually_lt continuousAt_const
    simpa only [map_zero,zero_add,a,NashBoundaryChart.oldPosition] using (c.graph_boundary _ hgood.2.1).2.1
  have hv : ∀ᶠ z : Affine s.tangentDim × Affine s.normalDim in 𝓝 0,
      ‖c.oldOffset (s.coordinates.symm z+a)‖ < 1 := by
    have ha : ContinuousAt (fun z : Affine s.tangentDim × Affine s.normalDim => s.coordinates.symm z+a) 0 :=
      (s.coordinates.symm.continuous.add continuous_const).continuousAt
    have hc : ContinuousAt c.oldOffset (s.coordinates.symm 0+a) := by
      simpa only [map_zero,zero_add,a] using (c.oldOffset_analyticAt hgood.2.1).continuousAt
    apply (hc.comp (f := fun z : Affine s.tangentDim × Affine s.normalDim => s.coordinates.symm z+a) (x := 0) ha).norm.eventually_lt continuousAt_const
    simp only [Function.comp_apply,map_zero,zero_add,a,c.oldOffset_oldPosition,norm_zero,zero_lt_one]
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp (hs.and (hn.and hv))
  let e := s.offsets.restr (ball 0 r)
  have he : (0 : Affine s.tangentDim × Affine s.normalDim) ∈ e.source := by
    rw [OpenPartialHomeomorph.restr_source' _ _ isOpen_ball]
    exact ⟨s.source_zero,mem_ball_self hr⟩
  let s' : NashBoundaryScalingChart c x := {s with offsets := e, source_zero := he}
  refine ⟨s',rfl,rfl,?_⟩
  intro z hz
  have hzr : z ∈ ball 0 r := by
    exact (show z ∈ s.offsets.source ∩ ball 0 r from by
      simpa only [s',e,OpenPartialHomeomorph.restr_source' _ _ isOpen_ball] using hz).2
  exact hrsub hzr
end NashBoundaryScalingChart
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ForwardBackwardGerm
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.ambientAction_subtype
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
namespace NashBoundaryChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

lemma reconstruct_oldPosition (c : NashBoundaryChart (m := m) U V B q) (z : Affine m) :
    c.normal.realCoordinates.symm (c.oldParameter z,c.normal.graph (c.oldParameter z)+c.oldOffset z) = z := by
  rw [oldOffset,add_sub_cancel]
  exact c.normal.realCoordinates.symm_apply_apply z
end NashBoundaryChart
namespace NashBoundaryScalingChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N} {c : NashBoundaryChart (m := m) U V B q}
variable {x : Fin d → ℝ}

@[simp] theorem forward_zero (s : NashBoundaryScalingChart c x) (hgood : c.GoodAt x) :
    s.forward 0=q x := by
  simpa only [forward,map_zero,zero_add] using c.oldPosition_inverse hgood

@[simp] theorem backward_center (s : NashBoundaryScalingChart c x) (hgood : c.GoodAt x) :
    s.backward (q x)=0 := by
  simp only [backward,← c.oldPosition_projection hgood,sub_self,map_zero]

theorem forward_mem_variety (s : NashBoundaryScalingChart c x) (hcut : s.HasCutoffs)
    {z : Affine s.tangentDim × Affine s.normalDim} (hz : z ∈ s.offsets.source) :
    s.forward z ∈ V := c.chart.inverse_mem _ (hcut z hz).2.1

theorem family_iff (s : NashBoundaryScalingChart c x) (hcut : s.HasCutoffs)
    {z : Affine s.tangentDim × Affine s.normalDim} (hz : z ∈ s.offsets.source) :
    (s.offsets z).2 ∈ c.family (s.offsets z).1 ↔ s.forward z ∈ U := by
  rw [s.offsets_eq]
  change (_ ∧ _ ∧ _ ∧ _) ↔ _
  rw [c.reconstruct_oldPosition]
  exact ⟨fun h => h.2.2.2,fun h => ⟨(hcut z hz).1,(hcut z hz).2.2,(hcut z hz).2.1,h⟩⟩

theorem domain_eq (s : NashBoundaryScalingChart c x) (hcut : s.HasCutoffs) (t : ℝ) :
    s.domain t = chartScaledDomain s.offsets c.family t := by
  ext z
  constructor
  · rintro ⟨hz,hu⟩
    exact ⟨hz,(s.family_iff hcut hz).mpr hu⟩
  · rintro ⟨hz,hu⟩
    exact ⟨hz,(s.family_iff hcut hz).mp hu⟩

theorem forward_backward_germ (s : NashBoundaryScalingChart c x) (hgood : c.GoodAt x)
    (F : Affine m → Affine N) (G : Affine N → Affine m)
    (hF0 : F 0 = q x) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFG : ∀ᶠ y in 𝓝[V] (q x), F (G y)=y) :
    ∀ᶠ y in 𝓝[V] (q x), s.forward (s.backward y)=y := by
  have he := c.chart.right_inverse_at (a := c.oldPosition (c.normal.parameters x)) (c.graph_boundary _ hgood.2.1).2.1 F G
    (by simpa only [c.oldPosition_inverse hgood] using hF0) hF
    (by simpa only [c.oldPosition_inverse hgood] using hG) hGF
    (by simpa only [c.oldPosition_inverse hgood] using hFG)
  rw [c.oldPosition_inverse hgood] at he
  filter_upwards [he] with y hy
  simpa only [forward,backward,s.coordinates.symm_apply_apply,sub_add_cancel] using hy
end NashBoundaryScalingChart
end Release061

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
lemma quadratic_decomposition (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x : E) :
    B x x = (hermPart B x x).re + (holPart B x x).re := by
  simp [hermPart,holPart]
  ring

lemma hermPart_smul_both (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (c : ℂ) (x y : E) :
    hermPart B (c • x) (c • y) = (Complex.normSq c : ℂ)*hermPart B x y := by
  rw [hermPart_smul_left,hermPart_smul_right,← mul_assoc,Complex.mul_conj]

lemma holPart_smul_both (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (c : ℂ) (x y : E) :
    holPart B (c • x) (c • y) = c^2*holPart B x y := by
  rw [holPart_smul_left,holPart_smul_right]
  ring

omit [IsScalarTower ℝ ℂ E] [Module ℂ E] in
lemma symmetrize_diag (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x : E) :
    symmetrize B x x = B x x := by
  simp [symmetrize]
  ring

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]

omit [FiniteDimensional ℂ F] in
lemma hermPart_unit (B : F →ₗ[ℝ] F →ₗ[ℝ] ℝ) (c : ℂ) (hc : ‖c‖ = 1) (x y : F) :
    hermPart B (c • x) (c • y) = hermPart B x y := by
  rw [hermPart_smul_both,Complex.normSq_eq_norm_sq,hc]
  norm_num

end Release061.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_HolQuadraticSmul
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
open Set Complex
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {k : ℕ}

omit [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] in
lemma vector_decomposition (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (z : E) (i : Fin k) :
    B i z z = hermQuadratic B z i + (holQuadratic B z i).re := by
  rw [← symmetrize_diag (B i) z]
  exact quadratic_decomposition (symmetrize (B i)) z

lemma quadraticShear_analytic (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (x : E × (Fin k → ℂ)) : AnalyticAt ℂ (quadraticShear B) x := by
  exact analyticAt_fst.prod (analyticAt_snd.sub
    ((holQuadratic_analytic B x.1).comp analyticAt_fst |>.const_smul (c := I)))

lemma quadraticShear_inverse_analytic (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (x : E × (Fin k → ℂ)) : AnalyticAt ℂ (quadraticShear B).symm x := by
  exact analyticAt_fst.prod (analyticAt_snd.add
    ((holQuadratic_analytic B x.1).comp analyticAt_fst |>.const_smul (c := I)))

lemma quadraticShear_residual (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (x : E × (Fin k → ℂ)) :
    (fun i => ((quadraticShear B x).2 i).im-hermQuadratic B (quadraticShear B x).1 i) =
      (fun i => (x.2 i).im-B i x.1 x.1) := by
  funext i
  change (x.2 i-I*holQuadratic B x.1 i).im-hermQuadratic B x.1 i = _
  simp only [sub_im,I_mul_im]
  rw [vector_decomposition B x.1 i]
  ring

omit [FiniteDimensional ℂ E] in
lemma hermQuadratic_unit (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (c : ℂ) (hc : ‖c‖ = 1)
    (z : E) : hermQuadratic B (c • z) = hermQuadratic B z := by
  funext i
  exact congrArg re (hermPart_unit (symmetrize (B i)) c hc z z)

omit [FiniteDimensional ℂ E] in
lemma holQuadratic_smul (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (c : ℂ) (z : E) :
    holQuadratic B (c • z) = c^2 • holQuadratic B z := by
  funext i
  exact holPart_smul_both (symmetrize (B i)) c z z

end Release061.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_LocallySmallSlopeGood
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
open Set Filter Topology Metric

theorem offset_joint_excluded_subfamily {S X E : Type*} [TopologicalSpace S]
    [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : S → Set E) (B : X → Set E) {i : X → S} {x₀ : X} {s₀ : S}
    (hi : Tendsto i (𝓝 x₀) (𝓝 s₀))
    (hBA : ∀ᶠ x in 𝓝 x₀, B x ⊆ A (i x))
    (h0 : ∀ᶠ x in 𝓝 x₀, (0 : E) ∉ A (i x))
    (f : E → ℝ)
    (hf : ∀ y, Tendsto (fun p : S × ℝ => offsetDistance A p.1 p.2 y)
      (𝓝[{p : S × ℝ | 0 < p.2}] (s₀,0)) (𝓝 (f y)))
    (s : ℕ → X) (t : ℕ → ℝ) (v : ℕ → E) (w : E)
    (hs : Tendsto s atTop (𝓝 x₀)) (ht : Tendsto t atTop (𝓝 0))
    (hpos : ∀ j, 0 < t j) (hv : Tendsto v atTop (𝓝 w)) (hw : f w = 0) :
    Tendsto (fun j => infDist (v j) (offsetScaled B (s j) (t j))ᶜ) atTop (𝓝 0) := by
  have hlim := offset_joint_excluded_limit A hf (hi.comp hs) ht
    (Eventually.of_forall hpos) hv hw
  apply squeeze_zero' (Eventually.of_forall fun _ => infDist_nonneg)
    ?_ hlim
  filter_upwards [hs hBA,hs h0] with j hBj h0j
  apply infDist_le_infDist_of_subset ?_ (offset_excluded_nonempty A (i (s j)) (t j) h0j)
  exact compl_subset_compl.mpr (fun y hy => hBj hy)

theorem small_slope_family_noncollapse {S : Type*} [TopologicalSpace S]
    {k : ℕ} {Ω : Set (Fin k → ℂ)} (hΩ : IsOpen Ω)
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (hCP : Wiener.DiscContinuityWithin k Ω ε)
    {φ : (Fin k → ℝ) → Fin k → ℝ} (hφ : AnalyticAt ℝ φ 0) (hφ0 : φ 0 = 0)
    (hdφ : ‖fderiv ℝ φ 0‖ < 1/2)
    {G : (Fin k → ℝ) × ℝ → Fin k → ℂ} (hG : AnalyticAt ℝ G 0)
    (hG0 : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ),
      G (x,0) = fun j => (x j : ℂ)+Complex.I*(φ x j : ℂ))
    (hGΩ : ∀ᶠ p in 𝓝 (0 : (Fin k → ℝ) × ℝ), 0 < p.2 → G p ∈ Ω)
    (hbdry : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ),
      (fun j => (x j : ℂ)+Complex.I*(φ x j : ℂ)) ∉ Ω)
    (A : S → Set (Fin k → ℝ)) {i : (Fin k → ℝ) → S} {s₀ : S}
    (hi : Tendsto i (𝓝 0) (𝓝 s₀))
    (hBA : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ),
      {v | ‖v‖ < ρ ∧ (fun j => (x j : ℂ)+Complex.I*((φ x j+v j) : ℂ)) ∈ Ω} ⊆ A (i x))
    (h0 : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), (0 : Fin k → ℝ) ∉ A (i x))
    (f : (Fin k → ℝ) → ℝ)
    (hf : ∀ y, Tendsto (fun p : S × ℝ => offsetDistance A p.1 p.2 y)
      (𝓝[{p : S × ℝ | 0 < p.2}] (s₀,0)) (𝓝 (f y))) : {y | f y = 0} ≠ univ := by
  obtain ⟨c,C,t₀,hc,hC,ht₀,hballs⟩ := interior_balls_from_small_slope_graphs
    hΩ hε hCP hφ hφ0 hdφ hG hG0 hGΩ
  apply normal_offset_noncollapse hφ.contDiffAt hφ0 hρ hc hC ht₀ hballs hbdry {y | f y = 0}
  intro s t v w hs ht hpos hv hw
  exact offset_joint_excluded_subfamily A _ hi hBA h0 f hf s t v w hs ht hpos hv hw
end

open Set Filter Topology Metric MeasureTheory
open scoped Classical

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SliceGraphDerivativeBound
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
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

lemma normalParameterInjection_norm_le (r k : ℕ) (x : Fin k → ℝ) :
    ‖normalParameterInjection r k x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro j
  change ‖Sum.elim (fun _ => (0:ℝ)) x (finSumFinEquiv.symm j)‖ ≤ ‖x‖
  cases h : finSumFinEquiv.symm j with
  | inl a => simpa only [Sum.elim_inl,norm_zero] using norm_nonneg x
  | inr a => exact norm_le_pi_norm x a

lemma normalParameterInjection_opNorm (r k : ℕ) : ‖normalParameterInjection r k‖ ≤ 1 :=
  (normalParameterInjection r k).opNorm_le_bound zero_le_one (by
    intro x
    simpa only [one_mul] using normalParameterInjection_norm_le r k x)

lemma complexGraphRealEquiv_normal {r k : ℕ} (w : Affine k) :
    complexGraphRealEquiv r k (0,w) =
      (normalParameterInjection r k (fun j => (w j).re),fun j => (w j).im) := by
  apply Prod.ext
  · funext j
    change Sum.elim (complexRealEquiv r 0) (fun j => (w j).re) (finSumFinEquiv.symm j) = _
    simp only [map_zero]
    rfl
  · rfl

lemma ProjectionNashChart.coordinateDomain_isOpen {N m s k : ℕ}
    {V U : Set (Affine N)} {p : Affine N} (c : ProjectionNashChart V p m)
    (hU : IsOpen ((Subtype.val : V → Affine N) ⁻¹' U))
    (e : Affine m ≃L[ℝ] ((Fin s → ℝ) × (Fin k → ℝ))) :
    IsOpen (c.coordinateDomain U e) := by
  obtain ⟨O,hO,he⟩ := isOpen_induced_iff.mp hU
  let S := {z : Affine m | ‖complexRealEquiv m z‖ < c.radius}
  have hS : IsOpen S := isOpen_lt (complexRealEquiv m).continuous.norm continuous_const
  have hopen : IsOpen (S ∩ c.inverse ⁻¹' O) :=
    c.inverse_analytic.continuousOn.isOpen_inter_preimage hS hO
  have hE : c.coordinateDomain U e = e.symm ⁻¹' (S ∩ c.inverse ⁻¹' O) := by
    ext z
    change (_ ∧ _) ↔ (_ ∧ _)
    constructor
    · rintro ⟨hz,hu⟩
      refine ⟨hz,?_⟩
      have hv := c.inverse_mem _ hz
      exact (Set.ext_iff.mp he ⟨_,hv⟩).mpr hu
    · rintro ⟨hz,hu⟩
      refine ⟨hz,?_⟩
      have hv := c.inverse_mem _ hz
      exact (Set.ext_iff.mp he ⟨_,hv⟩).mp hu
  rw [hE]
  exact hopen.preimage e.symm.continuous

namespace NashBoundaryChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

lemma sliceLift_analytic (c : NashBoundaryChart (m := m) U V B q) (s) :
    AnalyticOnNhd ℂ (c.sliceLift s) univ := by
  intro w _
  exact analyticAt_const.add (c.normalInjection.analyticAt w)

lemma sliceParameter_zero (c : NashBoundaryChart (m := m) U V B q) (s) :
    c.sliceParameter s 0 = s := by simp only [sliceParameter,map_zero,add_zero]

lemma sliceGraph_zero (c : NashBoundaryChart (m := m) U V B q) (s) :
    c.sliceGraph s 0 = 0 := by simp only [sliceGraph,sliceParameter_zero,sub_self]

lemma slice_real_coordinates (c : NashBoundaryChart (m := m) U V B q) (s)
    (w : Affine c.normal.normalDim) :
    c.normal.realCoordinates (c.sliceLift s w) =
      (c.sliceParameter s (fun j => (w j).re),c.normal.graph s+(fun j => (w j).im)) := by
  rw [sliceLift,map_add,c.normal.realCoordinates.apply_symm_apply]
  have h : c.normal.realCoordinates (c.normalInjection w) =
      (normalParameterInjection c.normal.tangentDim c.normal.normalDim (fun j => (w j).re),fun j => (w j).im) := by
    change complexGraphRealEquiv _ _ (c.normal.coordinates (c.normal.coordinates.symm (0,w))) = _
    rw [c.normal.coordinates.apply_symm_apply]
    exact complexGraphRealEquiv_normal w
  rw [h]
  rfl

lemma sliceDomain_isOpen (c : NashBoundaryChart (m := m) U V B q)
    (hU : IsOpen ((Subtype.val : V → Affine N) ⁻¹' U)) (s) : IsOpen (c.sliceDomain s) := by
  exact (c.chart.coordinateDomain_isOpen hU c.normal.realCoordinates).preimage
    (c.normal.realCoordinates.continuous.comp ((continuous_const.add c.normalInjection.continuous)))

lemma sliceGraph_analytic (c : NashBoundaryChart (m := m) U V B q) {s}
    (hs : s ∈ ball 0 c.graphRadius) : AnalyticAt ℝ (c.sliceGraph s) 0 := by
  have ha : AnalyticAt ℝ (c.sliceParameter s) 0 :=
    analyticAt_const.add ((normalParameterInjection _ _).analyticAt 0)
  have hg : AnalyticAt ℝ c.normal.graph (c.sliceParameter s 0) := by
    rw [c.sliceParameter_zero]
    exact c.normal.graph_analytic s (ball_subset_ball c.graphRadius_le hs)
  exact (hg.comp ha).sub analyticAt_const

lemma sliceGraph_derivative_bound (c : NashBoundaryChart (m := m) U V B q) {s}
    (hs : s ∈ ball 0 c.graphRadius) :
    ‖fderiv ℝ (c.sliceGraph s) 0‖ ≤ ‖fderiv ℝ c.normal.graph s‖ := by
  have hp : HasFDerivAt (c.sliceParameter s)
      (normalParameterInjection c.normal.tangentDim c.normal.normalDim) 0 :=
    ((normalParameterInjection _ _).hasFDerivAt).const_add s
  have hg := (c.normal.graph_analytic s (ball_subset_ball c.graphRadius_le hs)).differentiableAt.hasFDerivAt
  rw [← c.sliceParameter_zero s] at hg
  have hd := (hg.comp 0 hp).sub_const (c.normal.graph s)
  change HasFDerivAt (c.sliceGraph s) _ _ at hd
  rw [hd.fderiv]
  simp only [sliceParameter_zero]
  calc
    _ ≤ ‖fderiv ℝ c.normal.graph s‖ *
        ‖normalParameterInjection c.normal.tangentDim c.normal.normalDim‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ c.normal.graph s‖ * 1 :=
      mul_le_mul_of_nonneg_left
        (normalParameterInjection_opNorm c.normal.tangentDim c.normal.normalDim)
        (norm_nonneg _)
    _ = ‖fderiv ℝ c.normal.graph s‖ := mul_one _
end NashBoundaryChart
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SliceApproachingGraphs
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.NashBoundaryScalingChart.backward_center _root_.OAI.Release061.NashBoundaryScalingChart.forward_zero _root_.OAI.Release061.ambientAction_subtype
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
namespace Release061.NashBoundaryChart
open Set Filter Topology Metric
open scoped Classical
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

lemma sliceParameter_analytic (c : NashBoundaryChart (m := m) U V B q) (s) :
    AnalyticOnNhd ℝ (c.sliceParameter s) univ := by
  intro x _
  exact analyticAt_const.add ((normalParameterInjection _ _).analyticAt x)

lemma slice_graph_coordinates (c : NashBoundaryChart (m := m) U V B q) (s)
    (x v : Fin c.normal.normalDim → ℝ) :
    c.normal.realCoordinates (c.sliceLift s (fun j => (x j : ℂ)+Complex.I*((c.sliceGraph s x j+v j) : ℂ))) =
      (c.sliceParameter s x,c.normal.graph (c.sliceParameter s x)+v) := by
  rw [c.slice_real_coordinates]
  have hre : (fun j => ((x j : ℂ)+Complex.I*((c.sliceGraph s x j+v j) : ℂ)).re) = x := by
    funext j
    simp
  have him : (fun j => ((x j : ℂ)+Complex.I*((c.sliceGraph s x j+v j) : ℂ)).im) = c.sliceGraph s x+v := by
    funext j
    simp
  rw [hre,him]
  congr 1
  funext j
  simp only [sliceGraph,Pi.add_apply,Pi.sub_apply]
  ring

lemma slice_family_sub_and_boundary (c : NashBoundaryChart (m := m) U V B q) {s}
    (hs : s ∈ ball 0 c.graphRadius) :
    ∀ᶠ x in 𝓝 (0 : Fin c.normal.normalDim → ℝ),
      ({v | ‖v‖ < 1 ∧ (fun j => (x j : ℂ)+Complex.I*((c.sliceGraph s x j+v j) : ℂ)) ∈ c.sliceDomain s} ⊆ c.family (c.sliceParameter s x)) ∧
      (0 : Fin c.normal.normalDim → ℝ) ∉ c.family (c.sliceParameter s x) ∧
      (fun j => (x j : ℂ)+Complex.I*(c.sliceGraph s x j : ℂ)) ∉ c.sliceDomain s := by
  have ht : Tendsto (c.sliceParameter s) (𝓝 0) (𝓝 s) := by
    simpa only [sliceParameter_zero] using (c.sliceParameter_analytic s 0 (mem_univ _)).continuousAt.tendsto
  filter_upwards [ht (isOpen_ball.mem_nhds hs)] with x hx
  have hboundary := (c.graph_boundary (c.sliceParameter s x) hx).1.2
  refine ⟨?_,?_,?_⟩
  · intro v hv
    refine ⟨hx,hv.1,?_⟩
    have hvD := hv.2
    change c.normal.realCoordinates (c.sliceLift s (fun j => (x j : ℂ)+Complex.I*((c.sliceGraph s x j+v j) : ℂ))) ∈ c.chart.coordinateDomain U c.normal.realCoordinates at hvD
    rw [c.slice_graph_coordinates] at hvD
    exact hvD
  · intro hz
    apply hboundary
    simpa only [add_zero] using hz.2.2
  · intro hz
    apply hboundary
    have he : c.normal.realCoordinates (c.sliceLift s (fun j => (x j : ℂ)+Complex.I*(c.sliceGraph s x j : ℂ))) =
        (c.sliceParameter s x,c.normal.graph (c.sliceParameter s x)) := by
      simpa using c.slice_graph_coordinates s x 0
    change c.normal.realCoordinates (c.sliceLift s (fun j => (x j : ℂ)+Complex.I*(c.sliceGraph s x j : ℂ))) ∈ c.chart.coordinateDomain U c.normal.realCoordinates at hz
    rwa [he] at hz

theorem slice_approaching_graphs (c : NashBoundaryChart (m := m) U V B q) {s}
    (hs : s ∈ ball 0 c.graphRadius)
    (hdata : BoundaryOffsetData c.family (ball 0 c.graphRadius) s) :
    ∃ G : (Fin c.normal.normalDim → ℝ) × ℝ → Affine c.normal.normalDim,
      AnalyticAt ℝ G 0 ∧
      (∀ᶠ x in 𝓝 (0 : Fin c.normal.normalDim → ℝ),
        G (x,0) = fun j => (x j : ℂ)+Complex.I*(c.sliceGraph s x j : ℂ)) ∧
      ∀ᶠ p in 𝓝 (0 : (Fin c.normal.normalDim → ℝ) × ℝ), 0 < p.2 → G p ∈ c.sliceDomain s := by
  obtain ⟨r,hr,η,hη,ψ,_hrB,hψ,hψ0,hψin⟩ := hdata.1
  let J : (Fin c.normal.normalDim → ℝ) × ℝ →
      (Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ) × ℝ :=
    fun p => (c.sliceParameter s p.1,p.2)
  have hfst : AnalyticAt ℝ (fun p : (Fin c.normal.normalDim → ℝ) × ℝ => p.1) 0 := analyticAt_fst
  have hJa : AnalyticAt ℝ J 0 :=
    ((c.sliceParameter_analytic s (0 : Fin c.normal.normalDim → ℝ) (mem_univ _)).comp_of_eq hfst rfl).prod analyticAt_snd
  have hJ0 : J 0 = (s,0) := by simp only [J,Prod.fst_zero,Prod.snd_zero,sliceParameter_zero]
  have hψa : AnalyticAt ℝ (ψ ∘ J) 0 := by
    have hp : AnalyticAt ℝ ψ (J 0) := by
      rw [hJ0]
      exact hψ _ ⟨mem_ball_self hr,mem_ball_self hη⟩
    exact hp.comp hJa
  let G : (Fin c.normal.normalDim → ℝ) × ℝ → Affine c.normal.normalDim :=
    fun p => Flatten.realEmbedding c.normal.normalDim p.1 +
      Complex.I • Flatten.realEmbedding c.normal.normalDim
        (c.sliceGraph s p.1+ψ (J p))
  have hreal : AnalyticAt ℝ (fun p => Flatten.realEmbedding c.normal.normalDim
      (c.sliceGraph s p.1 + ψ (J p))) 0 :=
    ((Flatten.realEmbedding _).analyticAt _).comp
      (((c.sliceGraph_analytic hs).comp_of_eq hfst rfl).add hψa)
  have hi : AnalyticAt ℝ (fun z : Affine c.normal.normalDim => Complex.I • z)
      (Flatten.realEmbedding c.normal.normalDim (c.sliceGraph s 0 + ψ (J 0))) :=
    ((Complex.I • ContinuousLinearMap.id ℂ (Affine c.normal.normalDim)).restrictScalars ℝ).analyticAt _
  have hGa : AnalyticAt ℝ G 0 :=
    ((Flatten.realEmbedding _).analyticAt _ |>.comp hfst).add (hi.comp_of_eq hreal rfl)
  have ht : Tendsto (c.sliceParameter s) (𝓝 0) (𝓝 s) := by
    simpa only [sliceParameter_zero] using (c.sliceParameter_analytic s 0 (mem_univ _)).continuousAt.tendsto
  refine ⟨G,hGa,?_,?_⟩
  · filter_upwards [ht (ball_mem_nhds s hr)] with x hx
    have hz := hψ0 _ hx
    change G (x,0) = _
    simp only [G,J,hz,add_zero]
    rfl
  · have hJt : Tendsto J (𝓝 0) (𝓝 (s,0)) := hJ0 ▸ hJa.continuousAt.tendsto
    have hn : ball s r ×ˢ ball 0 η ∈ 𝓝 (s,(0:ℝ)) :=
      (isOpen_ball.prod isOpen_ball).mem_nhds ⟨mem_ball_self hr,mem_ball_self hη⟩
    filter_upwards [hJt hn] with p hp
    intro hp0
    have hplt : p.2 < η := by
      have h := mem_ball_zero_iff.mp hp.2
      exact (le_abs_self p.2).trans_lt h
    have hin := hψin _ hp.1 p.2 ⟨hp0,hplt⟩
    change c.normal.realCoordinates (c.sliceLift s (G p)) ∈ c.chart.coordinateDomain U c.normal.realCoordinates
    have he : G p = fun j => (p.1 j : ℂ)+Complex.I*((c.sliceGraph s p.1 j+(ψ (J p)) j) : ℂ) := by
      funext coordinate
      change (p.1 coordinate : ℂ) + Complex.I *
          ((c.sliceGraph s p.1 coordinate + ψ (J p) coordinate : ℝ) : ℂ) = _
      rw [Complex.ofReal_add]
    rw [he,c.slice_graph_coordinates]
    exact hin.2.2
end Release061.NashBoundaryChart

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_JointZeroConeProper
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
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
namespace Release061.NashBoundaryChart
open Set Filter Topology Metric
open scoped Classical
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

lemma sliceDomain_iff (c : NashBoundaryChart (m := m) U V B q) (s) (w) :
    w ∈ c.sliceDomain s ↔ ‖complexRealEquiv m (c.sliceLift s w)‖ < c.chart.radius ∧
      c.chart.inverse (c.sliceLift s w) ∈ U := by
  change (‖complexRealEquiv m (c.normal.realCoordinates.symm (c.normal.realCoordinates (c.sliceLift s w)))‖ < c.chart.radius ∧
      c.chart.inverse (c.normal.realCoordinates.symm (c.normal.realCoordinates (c.sliceLift s w))) ∈ U) ↔ _
  rw [c.normal.realCoordinates.symm_apply_apply]

theorem slice_disc_continuity {Γ : Type*}
    (c : NashBoundaryChart (m := m) U V B q) {s}
    (hs : s ∈ ball 0 c.graphRadius) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine N) ⁻¹' U))
    [LocallyCompactSpace U] (hbounded : Bornology.IsBounded U)
    [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (K : Set U) (hK : IsCompact K) (hrep : ∀ x : U, ∃ k ∈ K, ∃ γ : Γ, γ • k = x) :
    ∃ ε : ℝ, 0 < ε ∧ Wiener.DiscContinuityWithin c.normal.normalDim (c.sliceDomain s) ε := by
  have hz : ‖complexRealEquiv m (c.sliceLift s 0)‖ < c.chart.radius := by
    simpa only [sliceLift,map_zero,add_zero] using (c.graph_boundary s hs).2.1
  have hn : ∀ᶠ w in 𝓝 (0 : Affine c.normal.normalDim),
      ‖complexRealEquiv m (c.sliceLift s w)‖ < c.chart.radius :=
    ((complexRealEquiv m).continuous.continuousAt.comp
      (c.sliceLift_analytic s 0 (mem_univ _)).continuousAt).norm.eventually_lt continuousAt_const hz
  obtain ⟨ε,hε,hsmall⟩ := Metric.mem_nhds_iff.mp hn
  let Φ : Affine c.normal.normalDim → Affine N := c.chart.inverse ∘ c.sliceLift s
  have hΦ : AnalyticOnNhd ℂ Φ (ball 0 ε) := by
    intro w hw
    exact (c.chart.inverse_analytic _ (hsmall hw)).comp (c.sliceLift_analytic s w (mem_univ _))
  have hΦV : MapsTo Φ (ball 0 ε) V := fun w hw => c.chart.inverse_mem _ (hsmall hw)
  have hCP := bounded_cocompact_chart_disc_continuity V U hUV hU hbounded hhol K hK hrep Φ hΦ hΦV
  refine ⟨ε,hε,?_⟩
  intro A hA hAh hAr hbd hstart
  have hall := hCP A hA hAh hAr
    (fun t z hz => ((c.sliceDomain_iff s _).mp (hbd t z hz)).2)
    (fun z => ((c.sliceDomain_iff s _).mp (hstart z)).2)
  intro t z
  apply (c.sliceDomain_iff s _).mpr
  exact ⟨hsmall (mem_ball_zero_iff.mpr (hAr t z)),hall t z⟩

theorem joint_zero_cone_proper {Γ : Type*}
    (c : NashBoundaryChart (m := m) U V B q) {s}
    (hs : s ∈ ball 0 c.graphRadius)
    (hd : ‖fderiv ℝ c.normal.graph s‖ < 1/2)
    (hdata : BoundaryOffsetData c.family (ball 0 c.graphRadius) s)
    (hUV : U ⊆ V) (hU : IsOpen ((Subtype.val : V → Affine N) ⁻¹' U))
    [LocallyCompactSpace U] (hbounded : Bornology.IsBounded U)
    [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (K : Set U) (hK : IsCompact K) (hrep : ∀ x : U, ∃ k ∈ K, ∃ γ : Γ, γ • k = x)
    (f : (Fin c.normal.normalDim → ℝ) → ℝ)
    (hf : ∀ y, Tendsto (fun p : (Fin (c.normal.tangentDim+c.normal.tangentDim+c.normal.normalDim) → ℝ) × ℝ =>
        offsetDistance c.family p.1 p.2 y)
      (𝓝[{p | 0 < p.2}] (s,0)) (𝓝 (f y))) : {y | f y = 0} ≠ univ := by
  obtain ⟨ε,hε,hCP⟩ := c.slice_disc_continuity hs hUV hU hbounded hhol K hK hrep
  obtain ⟨G,hG,hG0,hGU⟩ := c.slice_approaching_graphs hs hdata
  have hlocal := c.slice_family_sub_and_boundary hs
  have hi : Tendsto (c.sliceParameter s) (𝓝 0) (𝓝 s) := by
    simpa only [sliceParameter_zero] using (c.sliceParameter_analytic s 0 (mem_univ _)).continuousAt.tendsto
  exact small_slope_family_noncollapse (c.sliceDomain_isOpen hU s) hε zero_lt_one hCP
    (c.sliceGraph_analytic hs) (c.sliceGraph_zero s) ((c.sliceGraph_derivative_bound hs).trans_lt hd)
    hG hG0 hGU (hlocal.mono fun _ h => h.2.2) c.family hi
    (hlocal.mono fun _ h => h.1) (hlocal.mono fun _ h => h.2.1) f hf
end Release061.NashBoundaryChart

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_Local
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
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
namespace NashBoundaryScalingChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N} {c : NashBoundaryChart (m := m) U V B q}
variable {x : Fin d → ℝ}

theorem exists_local_chart (s : NashBoundaryScalingChart c x) (hgood : c.GoodAt x)
    (hcut : s.HasCutoffs) (hq : q x ∈ V)
    (F : Affine m → Affine N) (G : Affine N → Affine m)
    (hF0 : F 0 = q x) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFG : ∀ᶠ y in 𝓝[V] (q x), F (G y)=y) :
    ∃ s' : NashBoundaryScalingChart c x,
      s'.tangentDim=s.tangentDim ∧ s'.normalDim=s.normalDim ∧ s'.HasCutoffs ∧
      ∃ Ω : Set (Affine N), Ω ⊆ V ∧ IsOpen ((Subtype.val : V → Affine N) ⁻¹' Ω) ∧ q x ∈ Ω ∧
        MapsTo s'.forward s'.offsets.source Ω ∧ MapsTo s'.backward Ω s'.offsets.source ∧
        (∀ y ∈ Ω, s'.forward (s'.backward y)=y) := by
  have he := s.forward_backward_germ hgood F G hF0 hF hG hGF hFG
  rw [eventually_nhdsWithin_iff] at he
  obtain ⟨W,hWsub,hWo,hpW⟩ := _root_.mem_nhds_iff.mp he
  have hf : ContinuousAt s.forward 0 :=
    (s.forward_analytic hcut 0 s.source_zero).continuousAt
  have heW : ∀ᶠ z in 𝓝 (0 : Affine s.tangentDim × Affine s.normalDim), s.forward z ∈ W := by
    apply hf.preimage_mem_nhds
    rw [s.forward_zero hgood]
    exact hWo.mem_nhds hpW
  obtain ⟨r,hr,hrW⟩ := Metric.mem_nhds_iff.mp heW
  let e := s.offsets.restr (ball 0 r)
  have he0 : (0 : Affine s.tangentDim × Affine s.normalDim) ∈ e.source := by
    rw [OpenPartialHomeomorph.restr_source' _ _ isOpen_ball]
    exact ⟨s.source_zero,mem_ball_self hr⟩
  let s' : NashBoundaryScalingChart c x := {s with offsets := e, source_zero := he0}
  have hs's : s'.offsets.source ⊆ s.offsets.source := by
    intro z hz
    exact (show z ∈ s.offsets.source ∩ ball 0 r from by
      simpa only [s',e,OpenPartialHomeomorph.restr_source' _ _ isOpen_ball] using hz).1
  have hcut' : s'.HasCutoffs := fun z hz => hcut z (hs's hz)
  have hsW : MapsTo s'.forward s'.offsets.source W := by
    intro z hz
    exact hrW (show z ∈ ball 0 r from (show z ∈ s.offsets.source ∩ ball 0 r from by
      simpa only [s',e,OpenPartialHomeomorph.restr_source' _ _ isOpen_ball] using hz).2)
  let Ω := V ∩ W ∩ s'.backward ⁻¹' s'.offsets.source
  have hΩV : Ω ⊆ V := fun _ hy => hy.1.1
  have hΩo : IsOpen ((Subtype.val : V → Affine N) ⁻¹' Ω) := by
    have hh : (Subtype.val : V → Affine N) ⁻¹' Ω =
        (Subtype.val : V → Affine N) ⁻¹' W ∩
        (fun y : V => s'.backward y.val) ⁻¹' s'.offsets.source := by
      ext y; simp only [Ω,mem_preimage,mem_inter_iff,y.property,true_and]
    rw [hh]
    exact (hWo.preimage continuous_subtype_val).inter
      (s'.offsets.open_source.preimage ((s'.backward_analytic.continuous).comp continuous_subtype_val))
  refine ⟨s',rfl,rfl,hcut',Ω,hΩV,hΩo,?_,?_,fun _ hy => hy.2,?_⟩
  · exact ⟨⟨hq,hpW⟩,by change s'.backward (q x) ∈ s'.offsets.source; rw [s'.backward_center hgood]; exact s'.source_zero⟩
  · intro z hz
    exact ⟨⟨s'.forward_mem_variety hcut' hz,hsW hz⟩,by change s'.backward (s'.forward z) ∈ s'.offsets.source; rw [s'.backward_forward hcut' hz]; exact hz⟩
  · intro y hy
    exact hWsub hy.1.2 hy.1.1

end NashBoundaryScalingChart
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_NoncollapsedSupportedBoundary
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
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

lemma SmallSlopeGoodNashBoundary.noncollapsed {d m N : ℕ} {Γ : Type*}
    {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
    {q : (Fin d → ℝ) → Affine N} {x : Fin d → ℝ}
    (hgood : SmallSlopeGoodNashBoundary m U V B q x)
    (hUV : U ⊆ V) (hU : IsOpen ((Subtype.val : V → Affine N) ⁻¹' U))
    [LocallyCompactSpace U] (hbounded : Bornology.IsBounded U)
    [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (K : Set U) (hK : IsCompact K) (hrep : ∀ x : U, ∃ k ∈ K, ∃ γ : Γ, γ • k = x) :
    NoncollapsedGoodNashBoundary m U V B q x := by
  obtain ⟨c,hc,hd⟩ := hgood
  exact ⟨c,hc,hd,fun f hf => c.joint_zero_cone_proper hc.2.1 hd hc.2.2 hUV hU hbounded hhol K hK hrep f hf⟩

theorem original_noncollapsed_supported_boundary {n : ℕ} (V U : Set (Affine n))
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (hc : IsConnected U) (hn : ¬ U.Subsingleton) (hb : Bornology.IsBounded U)
    (hs : IsSemialgebraic U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
    ∃ (m : ℕ) (C : Finset (NashPatch (n+n))),
      ∀ (bad : ∀ p : C, Set (Fin p.val.dim → ℝ)), (∀ p, volume (bad p) = 0) →
        ∃ (p : C) (x : Fin p.val.dim → ℝ) (k : ℕ)
          (F : Affine m → Affine n) (G : Affine n → Affine m)
          (h : Fin k → Affine n → ℂ),
          x ∈ p.val.domain ∧ x ∉ bad p ∧ p.val.complexMap x ∈ closure U \ U ∧
          NoncollapsedGoodNashBoundary m U (MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U))
            p.val.domain p.val.complexMap x ∧
          1 ≤ k ∧ k ≤ m ∧ p.val.dim + k = 2*m ∧
          F 0 = p.val.complexMap x ∧ AnalyticAt ℂ F 0 ∧
          AnalyticAt ℂ G (p.val.complexMap x) ∧
          (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id ∧
          (∀ᶠ y in 𝓝[MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U)] (p.val.complexMap x), F (G y) = y) ∧
          (∀ᶠ z in 𝓝 (0 : Affine m), F z ∈ MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U)) ∧
          Submodule.span ℂ (range (fderiv ℝ (G ∘ p.val.complexMap) x)) = ⊤ ∧
          (∀ i, AnalyticOnNhd ℂ (h i) univ) ∧
          (∀ i, h i (p.val.complexMap x) = 1) ∧
          (∀ i, ∀ z ∈ closure U, ‖h i z‖ ≤ Real.exp (-(dist z (p.val.complexMap x))^2)) ∧
          (∀ i, AnalyticAt ℂ (fun z => Complex.log (h i (F z))) 0) ∧
          LinearIndependent ℝ (fun i => (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).toLinearMap) ∧
          LinearIndependent ℂ (fun i => (fderiv ℂ (fun z => Complex.log (h i (F z))) 0).toLinearMap) ∧
          ∀ i, (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).comp (fderiv ℝ (G ∘ p.val.complexMap) x) = 0 := by
  let : LocallyCompactSpace U := locallyCompact_of_relative_open hV hUV hU
  let : ContinuousConstSMul Γ U := ⟨fun γ => ((hhol γ).continuous).subtype_mk _⟩
  obtain ⟨K,hK,hrep⟩ := exists_compact_orbit_representatives (X := U) (Γ := Γ)
  let I := MvPolynomial.vanishingIdeal ℂ U
  have hUI : U ⊆ MvPolynomial.zeroLocus ℂ I := fun z hz p hp => hp z hz
  have hIV : MvPolynomial.zeroLocus ℂ I ⊆ V := by
    obtain ⟨R,hR⟩ := hV
    intro z hz
    rw [hR]
    intro p hp
    apply hz p
    intro y hy
    exact (hR ▸ hUV hy) p hp
  have hUIopen : IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ I → Affine n) ⁻¹' U) :=
    hU.preimage (continuous_inclusion hIV)
  obtain ⟨m,C,he⟩ := original_small_slope_good_supported_boundary V U hV hUV hU hc hn hb hs Γ hhol
  refine ⟨m,C,fun bad hbad => ?_⟩
  obtain ⟨p,x,k,F,G,h,hxp,hxb,hbd,hgood,hrest⟩ := he bad hbad
  exact ⟨p,x,k,F,G,h,hxp,hxb,hbd,hgood.noncollapsed hUI hUIopen hb hhol K hK hrep,hrest⟩
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_QuadraticDomainConnectedComponent
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

open Set Complex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k : ℕ}

omit [NormedSpace ℂ E] in
lemma quadraticDomain_eq_preimage (H : E → Fin k → ℝ) (hH : Continuous H)
    (C : Set (Fin k → ℝ)) :
    quadraticDomain H C = (quadraticDomainCoordinates H hH) ⁻¹' (univ ×ˢ (univ ×ˢ C)) := by
  ext p
  simp only [quadraticDomain,mem_ofPred_eq,mem_preimage,mem_prod,mem_univ,true_and]
  rfl

theorem quadraticDomain_isConnected (H : E → Fin k → ℝ) (hH : Continuous H)
    (C : Set (Fin k → ℝ)) (hC : IsConnected C) : IsConnected (quadraticDomain H C) := by
  rw [quadraticDomain_eq_preimage H hH]
  exact (quadraticDomainCoordinates H hH).isConnected_preimage.mpr
    (isConnected_univ.prod (isConnected_univ.prod hC))

omit [NormedSpace ℂ E] in
lemma quadraticDomain_axis (H : E → Fin k → ℝ) (hH0 : H 0 = 0)
    {C : Set (Fin k → ℝ)} {a : Fin k → ℝ} (ha : a ∈ C) :
    ((0 : E),fun i => I*(a i : ℂ)) ∈ quadraticDomain H C := by
  simpa [quadraticDomain,hH0] using ha

lemma quadraticDomain_unit_rotation (H : E → Fin k → ℝ) (C : Set (Fin k → ℝ))
    (c : ℂ) (hHc : ∀ z, H (c • z) = H z) (p : E × (Fin k → ℂ)) :
    (c • p.1,p.2) ∈ quadraticDomain H C ↔ p ∈ quadraticDomain H C := by
  simp [quadraticDomain,hHc]

theorem quadraticDomain_connectedComponent (H : E → Fin k → ℝ)
    (hH : Continuous H) (C : Set (Fin k → ℝ)) (p : E × (Fin k → ℂ)) :
    connectedComponentIn (quadraticDomain H C) p =
      quadraticDomain H (connectedComponentIn C (fun i => (p.2 i).im-H p.1 i)) := by
  let q : E × (Fin k → ℂ) → Fin k → ℝ := fun x i => (x.2 i).im-H x.1 i
  have hq : Continuous q := by
    apply continuous_pi
    intro i
    exact (Complex.continuous_im.comp ((continuous_apply i).comp continuous_snd)).sub
      (((continuous_apply i).comp hH).comp continuous_fst)
  change connectedComponentIn (quadraticDomain H C) p =
    quadraticDomain H (connectedComponentIn C (q p))
  by_cases hp : p ∈ quadraticDomain H C
  · have hpc : q p ∈ C := hp
    apply Subset.antisymm
    · intro x hx
      have hpre : IsPreconnected (q '' connectedComponentIn (quadraticDomain H C) p) :=
        isPreconnected_connectedComponentIn.image q hq.continuousOn
      have hmem : q p ∈ q '' connectedComponentIn (quadraticDomain H C) p :=
        ⟨p,mem_connectedComponentIn hp,rfl⟩
      have hsub : q '' connectedComponentIn (quadraticDomain H C) p ⊆ C := by
        rintro _ ⟨y,hy,rfl⟩
        exact connectedComponentIn_subset (quadraticDomain H C) p hy
      exact hpre.subset_connectedComponentIn hmem hsub ⟨x,hx,rfl⟩
    · have hpre := (quadraticDomain_isConnected H hH (connectedComponentIn C (q p))
        (isConnected_connectedComponentIn_iff.mpr hpc)).isPreconnected
      have hmem : p ∈ quadraticDomain H (connectedComponentIn C (q p)) :=
        mem_connectedComponentIn hpc
      have hsub : quadraticDomain H (connectedComponentIn C (q p)) ⊆ quadraticDomain H C := by
        intro x hx
        exact connectedComponentIn_subset C (q p) hx
      exact hpre.subset_connectedComponentIn hmem hsub
  · have hpc : q p ∉ C := hp
    rw [connectedComponentIn_eq_empty hp,connectedComponentIn_eq_empty hpc]
    simp [quadraticDomain]

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_RawQuadraticModelNormalization
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.NashBoundaryScalingChart.backward_center _root_.OAI.Release061.NashBoundaryScalingChart.forward_zero _root_.OAI.Release061.ambientAction_subtype
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

lemma residualQuadraticCoefficients_diag {r k l : ℕ}
    (L : (Fin k → ℝ) ≃L[ℝ] (Fin l → ℝ))
    (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Affine r) (Fin l → ℝ))
    (z : Affine r) :
    (fun i => residualQuadraticCoefficients L Q i z z) = -L.symm (Q (fun _ => z)) := by
  ext i
  let P := ((ContinuousLinearMap.proj i).comp (-L.symm.toContinuousLinearMap)).compContinuousMultilinearMap Q
  change (continuousMultilinearCurryFin1 ℝ (Affine r) ℝ (P.curryLeft z)) z = _
  rw [continuousMultilinearCurryFin1_apply,ContinuousMultilinearMap.curryLeft_apply]
  change (-L.symm (Q (Fin.cons z (Fin.snoc 0 z)))) i = _
  have he : Fin.cons z (Fin.snoc 0 z)=(fun _ : Fin 2 => z) := by
    funext j
    fin_cases j <;> rfl
  rw [he]

lemma residualQuadraticCoefficients_continuous {r k l : ℕ}
    (L : (Fin k → ℝ) ≃L[ℝ] (Fin l → ℝ))
    (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Affine r) (Fin l → ℝ)) :
    Continuous (fun z => fun i => residualQuadraticCoefficients L Q i z z) := by
  have he : (fun z i => residualQuadraticCoefficients L Q i z z) =
      (fun z => -L.symm (Q (fun _ => z))) :=
    funext (residualQuadraticCoefficients_diag L Q)
  rw [he]
  exact (L.symm.continuous.comp (Q.cont.comp (continuous_pi fun _ => continuous_id))).neg

lemma residualQuadraticCoefficients_zero {r k l : ℕ}
    (L : (Fin k → ℝ) ≃L[ℝ] (Fin l → ℝ))
    (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Affine r) (Fin l → ℝ)) :
    (fun i => residualQuadraticCoefficients L Q i 0 0) = 0 := by
  ext i
  simp

theorem quadraticShear_biholomorph {r k : ℕ}
    (B : Fin k → Affine r →ₗ[ℝ] Affine r →ₗ[ℝ] ℝ) (C : Set (Fin k → ℝ)) :
    Nonempty (Biholomorph
      ((affineProductCoordinates r k) '' quadraticDomain (fun z i => B i z z) C)
      ((affineProductCoordinates r k) '' quadraticDomain (Hermitian.hermQuadratic B) C)) := by
  let e := affineProductCoordinates r k
  let σ := Hermitian.quadraticShear B
  let φ := e.symm.toHomeomorph.trans (σ.trans e.toHomeomorph)
  have ha : ∀ x, AnalyticAt ℂ φ x := by
    intro x
    exact (e.toContinuousLinearMap.analyticAt _).comp
      ((Hermitian.quadraticShear_analytic B _).comp (e.symm.toContinuousLinearMap.analyticAt _))
  have hai : ∀ x, AnalyticAt ℂ φ.symm x := by
    intro x
    exact (e.toContinuousLinearMap.analyticAt _).comp
      ((Hermitian.quadraticShear_inverse_analytic B _).comp (e.symm.toContinuousLinearMap.analyticAt _))
  have himage : φ '' (e '' quadraticDomain (fun z i => B i z z) C) =
      e '' quadraticDomain (Hermitian.hermQuadratic B) C := by
    ext y
    constructor
    · rintro ⟨x,⟨z,hz,rfl⟩,rfl⟩
      refine ⟨σ z,?_,?_⟩
      · change (fun i => ((σ z).2 i).im-Hermitian.hermQuadratic B (σ z).1 i) ∈ C
        rw [Hermitian.quadraticShear_residual]
        exact hz
      · change e (σ z)=e (σ (e.symm (e z)))
        rw [e.symm_apply_apply]
    · rintro ⟨z,hz,rfl⟩
      refine ⟨e (σ.symm z),⟨σ.symm z,?_,rfl⟩,?_⟩
      · have hres := Hermitian.quadraticShear_residual B (σ.symm z)
        change (fun i => ((σ.symm z).2 i).im-B i (σ.symm z).1 (σ.symm z).1) ∈ C
        rw [← hres]
        change (fun i => ((σ (σ.symm z)).2 i).im-
          Hermitian.hermQuadratic B (σ (σ.symm z)).1 i) ∈ C
        rw [σ.apply_symm_apply]
        exact hz
      · change e (σ (e.symm (e (σ.symm z))))=e z
        rw [e.symm_apply_apply,σ.apply_symm_apply]
  exact ⟨himage ▸ Biholomorph.ofEntireHomeomorph φ ha hai _⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_StrictModelSupports
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
namespace Release061.Hermitian
open Set Filter Metric Complex
open scoped Topology NNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma injective_squared_lower_bound [FiniteDimensional ℂ E]
    (J : E →ₗ[ℂ] F) (hJ : Function.Injective J) :
    ∃ c : ℝ, 0 < c ∧ ∀ z, c*‖z‖^2 ≤ ‖J z‖^2 := by
  obtain ⟨K,hK,hbound⟩ := J.injective_iff_antilipschitz.mp hJ
  have hK' : 0 < (K : ℝ) := hK
  refine ⟨((K:ℝ)^2)⁻¹,inv_pos.mpr (sq_pos_of_pos hK'),fun z => ?_⟩
  have h := ZeroHomClass.bound_of_antilipschitz J hbound z
  have hsq : ‖z‖^2 ≤ (K:ℝ)^2*‖J z‖^2 := by
    nlinarith [norm_nonneg z,norm_nonneg (J z)]
  exact (inv_mul_le_iff₀ (sq_pos_of_pos hK')).mpr hsq

lemma cancel_quadratic_support {W : Type*} {D : Set (E × W)}
    (hinv : ∀ x ∈ D, (I • x.1,x.2) ∈ D)
    (J : E →ₗ[ℂ] F) (a : W → ℝ) (P : E → ℂ)
    (hP : ∀ z, P (I • z) = -P z)
    (hbound : ∀ x ∈ D, ‖J x.1‖^2 ≤ a x.2+(P x.1).re) :
    ∀ x ∈ D, ‖J x.1‖^2 ≤ a x.2 := by
  intro x hx
  have h1 := hbound x hx
  have h2 := hbound (I • x.1,x.2) (hinv x hx)
  simp only [map_smul,norm_smul,norm_I,one_mul,hP,neg_re] at h2
  linarith

end Release061.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SupportedWeightedLimit
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.NashBoundaryScalingChart.backward_center _root_.OAI.Release061.NashBoundaryScalingChart.forward_zero _root_.OAI.Release061.ambientAction_subtype
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
open Set Filter Topology Metric Complex
open scoped Classical

lemma independentSupportCoordinates_apply {k : ℕ}
    (β : Fin k → Fin k → ℝ) (hβ : LinearIndependent ℝ β) (v : Fin k → ℝ) (i : Fin k) :
    independentSupportCoordinates β hβ v i = ∑ j, β i j*v j := rfl

theorem supported_weighted_limit {r k N : ℕ}
    (Φ : Affine r × Affine k → Affine N) (hΦ : AnalyticAt ℂ Φ 0)
    (U : Set (Affine N)) (O : Set (Affine r × Affine k))
    (hcover : ∀ z ∈ O, ∀ᶠ t : ℝ in 𝓝[>] 0, Φ (weightedScale t z) ∈ U)
    (h : Affine N → ℂ) (hh : ContinuousAt h (Φ 0)) (hh0 : h (Φ 0)=1)
    (hpeak : ∀ y ∈ U, ‖h y‖ ≤ Real.exp (-(‖y-Φ 0‖^2)))
    (ha : AnalyticAt ℂ (fun z => Complex.log (h (Φ z))) 0)
    (β : Fin k → ℝ)
    (hβ : ∀ z, fderiv ℂ (fun z => Complex.log (h (Φ z))) 0 z =
      I*∑ j, (β j : ℂ)*z.2 j) :
    ∃ A : Affine r → ℂ, (∀ z, A (I • z) = -A z) ∧
      ∀ z ∈ O, ‖fderiv ℂ Φ 0 (z.1,0)‖^2 ≤
        (∑ j, β j*(z.2 j).im)-(A z.1).re := by
  obtain ⟨p,hp⟩ := ha
  have hf0 : Complex.log (h (Φ 0))=0 := by rw [hh0,Complex.log_one]
  have hp1 : ∀ z, p 1 (fun _ => z) = I*∑ j, (β j : ℂ)*z.2 j := by
    intro z
    rw [← hβ]
    exact congrArg (fun L => L z) hp.hasFDerivAt.fderiv.symm
  refine ⟨fun z => p 2 (fun _ => (z,0)),?_,?_⟩
  · intro z
    have he : (fun _ : Fin 2 => (I • z,(0 : Affine k))) =
        (fun j : Fin 2 => I • (fun _ : Fin 2 => (z,(0 : Affine k))) j) := by
      funext i
      simp
    change p 2 (fun _ => (I • z,(0 : Affine k))) = -p 2 (fun _ => (z,(0 : Affine k)))
    rw [he,(p 2).map_smul_univ]
    simp
  · intro z hz
    have ht : Tendsto (fun t => Φ (weightedScale t z)) (𝓝[>] (0 : ℝ)) (𝓝 (Φ 0)) :=
      hΦ.continuousAt.tendsto.comp (weightedScale_point_tendsto z)
    have hn : ∀ᶠ t : ℝ in 𝓝[>] 0, h (Φ (weightedScale t z)) ≠ 0 := by
      have hc := hh.tendsto.comp ht
      exact hc.eventually (isOpen_ne.mem_nhds (by rw [hh0]; exact one_ne_zero))
    have hb : ∀ᶠ t : ℝ in 𝓝[>] 0,
        ‖Φ (weightedScale t z)-Φ 0‖^2 ≤ -(Complex.log (h (Φ (weightedScale t z)))).re := by
      filter_upwards [hn,hcover z hz] with t htn htu
      linarith [logarithmic_peak_bound h (fun y => ‖y-Φ 0‖^2) htn (hpeak _ htu)]
    have H := analytic_peak_weighted_bound hp hf0 (fun z => by simp [hp1])
      (hΦ.differentiableAt.hasFDerivAt.restrictScalars ℝ) z hb
    rw [hp1] at H
    simpa only [add_re,I_mul_re,Complex.im_sum,mul_im,ofReal_im,ofReal_re,zero_mul,
      zero_add,neg_add_rev,neg_neg,ContinuousLinearMap.coe_restrictScalars',
      sub_eq_add_neg,add_comm] using H
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SupportedHermitianWeightedModel
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
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
open Set Filter Topology Metric Complex
open scoped Classical

theorem supported_hermitian_weighted_model {r k N : ℕ}
    (B : Fin k → Affine r →ₗ[ℝ] Affine r →ₗ[ℝ] ℝ) (C : Set (Fin k → ℝ))
    (Φ : Affine r × Affine k → Affine N) (hΦ : AnalyticAt ℂ Φ 0)
    (hi : Function.Injective (fderiv ℂ Φ 0))
    (U : Set (Affine N))
    (hcover : ∀ z ∈ quadraticDomain (fun z i => B i z z) C,
      ∀ᶠ t : ℝ in 𝓝[>] 0, Φ (weightedScale t z) ∈ U)
    (h : Fin k → Affine N → ℂ) (hh : ∀ i, ContinuousAt (h i) (Φ 0))
    (hh0 : ∀ i, h i (Φ 0)=1)
    (hpeak : ∀ i y, y ∈ U → ‖h i y‖ ≤ Real.exp (-(‖y-Φ 0‖^2)))
    (ha : ∀ i, AnalyticAt ℂ (fun z => Complex.log (h i (Φ z))) 0)
    (β : Fin k → Fin k → ℝ) (hβ : LinearIndependent ℝ β)
    (hβeq : ∀ i z, fderiv ℂ (fun z => Complex.log (h i (Φ z))) 0 z =
      I*∑ j, (β i j : ℂ)*z.2 j) :
    ∃ (e : (Fin k → ℝ) ≃L[ℝ] (Fin k → ℝ)) (c : ℝ), 0 < c ∧
      ∀ z ∈ quadraticDomain (Hermitian.hermQuadratic B) C,
        ∀ i, c*‖z.1‖^2 ≤ e (fun j => (z.2 j).im) i := by
  have hx (i : Fin k) := supported_weighted_limit Φ hΦ U
    (quadraticDomain (fun z i => B i z z) C) hcover (h i) (hh i) (hh0 i)
    (hpeak i) (ha i) (β i) (hβeq i)
  choose A hA hAbound using hx
  let J : Affine r →ₗ[ℂ] Affine N := (fderiv ℂ Φ 0).toLinearMap.comp
    (LinearMap.inl ℂ (Affine r) (Affine k))
  have hJ : Function.Injective J := by
    intro z z' hz
    change fderiv ℂ Φ 0 (z,0)=fderiv ℂ Φ 0 (z',0) at hz
    exact congrArg Prod.fst (hi hz)
  obtain ⟨c,hc,hco⟩ := Hermitian.injective_squared_lower_bound J hJ
  let e := independentSupportCoordinates β hβ
  let P : Fin k → Affine r → ℂ := fun i z =>
    (∑ j, (β i j : ℂ)*Hermitian.holQuadratic B z j)-A i z
  have hP : ∀ i z, P i (I • z) = -P i z := by
    intro i z
    simp only [P,Hermitian.holQuadratic_smul,I_sq,neg_smul,one_smul,Pi.neg_apply,
      mul_neg,Finset.sum_neg_distrib,hA]
    ring
  have hbound : ∀ z ∈ quadraticDomain (Hermitian.hermQuadratic B) C,
      ∀ i, ‖J z.1‖^2 ≤ e (fun j => (z.2 j).im) i+(P i z.1).re := by
    intro z hz i
    let z' := (Hermitian.quadraticShear B).symm z
    have hz' : z' ∈ quadraticDomain (fun z i => B i z z) C := by
      have hr := Hermitian.quadraticShear_residual B z'
      change (fun i => (z'.2 i).im-B i z'.1 z'.1) ∈ C
      rw [← hr]
      change (fun i => (((Hermitian.quadraticShear B) ((Hermitian.quadraticShear B).symm z)).2 i).im-
        Hermitian.hermQuadratic B ((Hermitian.quadraticShear B) ((Hermitian.quadraticShear B).symm z)).1 i) ∈ C
      rw [(Hermitian.quadraticShear B).apply_symm_apply]
      exact hz
    have H := hAbound i z' hz'
    change ‖J z.1‖^2 ≤ (∑ j, β i j*(z.2 j+I*Hermitian.holQuadratic B z.1 j).im)-(A i z.1).re at H
    have he : (∑ j, β i j*(z.2 j+I*Hermitian.holQuadratic B z.1 j).im)-(A i z.1).re =
        e (fun j => (z.2 j).im) i+(P i z.1).re := by
      simp only [e,independentSupportCoordinates_apply,P,add_im,I_mul_im,mul_add,
        Finset.sum_add_distrib,sub_re,Complex.re_sum,mul_re,ofReal_re,ofReal_im,
        zero_mul,sub_zero]
      ring
    rw [he] at H
    exact H
  refine ⟨e,c,hc,?_⟩
  intro z hz i
  have hinv : ∀ x ∈ quadraticDomain (Hermitian.hermQuadratic B) C,
      (I • x.1,x.2) ∈ quadraticDomain (Hermitian.hermQuadratic B) C := by
    intro x hx
    exact (quadraticDomain_unit_rotation _ C I
      (fun z => Hermitian.hermQuadratic_unit B I norm_I z) x).mpr hx
  exact (hco z.1).trans (Hermitian.cancel_quadratic_support hinv J
    (fun w => e (fun j => (w j).im) i) (P i) (hP i)
      (fun z hz => hbound z hz i) z hz)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SupportedHermitianModel
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply
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

theorem original_supported_hermitian_model_oai {N : ℕ} (V U : Set (Affine N))
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine N) ⁻¹' U))
    (hc : IsConnected U) (hn : ¬ U.Subsingleton) (hb : Bornology.IsBounded U)
    (hs : IsSemialgebraic U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
    ∃ (r k : ℕ) (B : Fin k → Affine r →ₗ[ℝ] Affine r →ₗ[ℝ] ℝ)
      (C : Set (Fin k → ℝ)) (e : (Fin k → ℝ) ≃L[ℝ] (Fin k → ℝ)) (c : ℝ),
      1 ≤ k ∧ IsOpen C ∧ IsConnected C ∧ (0 : Fin k → ℝ) ∉ C ∧
      (∀ t : ℝ, 0 < t → ∀ y, t • y ∈ C ↔ y ∈ C) ∧ 0 < c ∧
      (∀ z ∈ quadraticDomain (Hermitian.hermQuadratic B) C,
        ∀ i, c*‖z.1‖^2 ≤ e (fun j => (z.2 j).im) i) ∧
      Nonempty (Biholomorph U
        ((affineProductCoordinates r k) '' quadraticDomain (Hermitian.hermQuadratic B) C)) := by
  let : LocallyCompactSpace U := locallyCompact_of_relative_open hV hUV hU
  have hsm := cocompact_bounded_affine_smooth V U hV hUV hU hc hb Γ hhol
  let V' := MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U)
  have hUV' : U ⊆ V' := fun z hz p hp => hp z hz
  have hV'V : V' ⊆ V := by
    obtain ⟨R,hR⟩ := hV
    intro z hz
    rw [hR]
    intro p hp
    exact hz p (fun y hy => (hR ▸ hUV hy) p hp)
  have hU' : IsOpen ((Subtype.val : V' → Affine N) ⁻¹' U) :=
    hU.preimage (continuous_inclusion hV'V)
  have hV'closed : IsClosed V' := zeroLocus_closed _
  obtain ⟨m,C,hC⟩ := original_noncollapsed_supported_boundary V U hV hUV hU hc hn hb hs Γ hhol
  obtain ⟨p,x,k,F,G,h,hxp,_hxb,hbd,hgood,hk,hkm,hdk,hF0,hF,hG,hGF,hFG,hFV,hgen,
    hha,hh0,hpeak,hlog,hI,_hCI,hzero⟩ := hC (fun _ => ∅) (fun _ => measure_empty)
  obtain ⟨c,hcgood,_hslope,hproper⟩ := hgood
  have hq := (p.val.analytic_complexMap x hxp).differentiableAt
  have hqi := p.val.injective_fderiv_complexMap hxp
  have hr := coordinate_rank_ge_of_chart_generic p.val.complexMap G hG hq hgen
  obtain ⟨s₀⟩ := c.scaling_chart hcgood hq hqi hr
  obtain ⟨s₁,_hs₁t,_hs₁n,hcut₁⟩ := s₀.exists_cutoff hcgood
  have hpxV' : p.val.complexMap x ∈ V' := hV'closed.closure_subset_iff.mpr hUV' hbd.1
  obtain ⟨s,_hst,_hsn,hcut,Ω,hΩV,hΩo,hpΩ,hfΩ,hgS,hfg⟩ :=
    s₁.exists_local_chart hcgood hcut₁ hpxV' F G hF0 hF hG hGF hFG
  have hnk : s.normalDim=k := by
    have h1 := c.normal.real_dimension
    have h2 := c.normal.complex_dimension
    have h3 := s.normal_dimension
    omega
  subst k
  obtain ⟨hnew,β,hβ,hβeq⟩ := s.independent_support_rows hcgood hcut hq hqi hr
    F G hF0 hF hG hGF hFG hFV h hlog hI hzero
  obtain ⟨f,hfl,hfb,hft,_hfut,_hfclosed,hf0,hfcone⟩ := hcgood.2.2.2
  obtain ⟨Q,hcov,hexc⟩ := s.two_sided hcgood f hft (fun y => (hfb y).1)
  have hfne : ∃ v, f v ≠ 0 := by
    by_contra! hall
    apply hproper f hft
    ext y
    simp only [mem_ofPred_eq,mem_univ,iff_true]
    exact hall y
  obtain ⟨v,hv⟩ := hfne
  let a := s.normalMap.symm v
  let w : Affine s.normalDim := fun i => Complex.I*(a i : ℂ)
  let R : Affine s.tangentDim × Affine s.normalDim → Fin c.normal.normalDim → ℝ :=
    fun z => s.normalMap (Flatten.imaginaryPart s.normalDim z.2)+Q (fun _ => z.1)
  let O : Set (Affine s.tangentDim × Affine s.normalDim) := {z | f (R z) ≠ 0}
  have hRc : Continuous R := by
    apply Continuous.add
    · exact s.normalMap.continuous.comp ((Flatten.imaginaryPart s.normalDim).continuous.comp continuous_snd)
    · exact Q.cont.comp (continuous_pi fun _ => continuous_fst)
  have hOo : IsOpen O := isOpen_ne_fun (hfl.continuous.comp hRc) continuous_const
  have hw : (0,w) ∈ O := by
    have hQ0 : Q (fun _ : Fin 2 => (0 : Affine s.tangentDim))=0 := Q.map_zero
    have hwim : Flatten.imaginaryPart s.normalDim w=a := by
      ext i
      simp [Flatten.imaginaryPart,w]
    change f (s.normalMap (Flatten.imaginaryPart s.normalDim w)+Q (fun _ => 0)) ≠ 0
    rw [hQ0,add_zero,hwim]
    simpa only [a,s.normalMap.apply_symm_apply] using hv
  have hhb : ∀ i y, y ∈ U → ‖h i y‖ ≤ 1 := by
    intro i y hy
    exact (hpeak i y (subset_closure hy)).trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
  have hpk : ∀ y ∈ U, ‖h (⟨0,by omega⟩ : Fin s.normalDim) y‖ ≤
      Real.exp (-(‖y-p.val.complexMap x‖^2)) := by
    intro y hy
    simpa only [dist_eq_norm] using hpeak ⟨0,by omega⟩ y (subset_closure hy)
  have hcover : ∀ K, IsCompact K → K ⊆ O → ∀ᶠ t : ℝ in 𝓝[>] 0, K ⊆ s.domain t := by
    intro K hK hKO
    simpa only [s.domain_eq hcut] using hcov K hK hKO
  have hexclude : ∀ z ∉ O, ∀ t : ℕ → ℝ, Tendsto t atTop (𝓝 0) → (∀ j, 0 < t j) →
      ∃ y : ℕ → Affine s.tangentDim × Affine s.normalDim,
        Tendsto y atTop (𝓝 z) ∧ ∀ᶠ j in atTop, y j ∉ s.domain (t j) := by
    intro z hz t ht htp
    have hz' : f (R z)=0 := not_not.mp hz
    obtain ⟨y,hy,hey,_hchart⟩ := hexc z hz' t ht htp
    refine ⟨y,hy,Eventually.of_forall fun j => ?_⟩
    simpa only [s.domain_eq hcut] using hey j
  have hglob := s.global_from_two_sided hcgood hcut hUV' hU' hc hb hsm Γ hhol
    Ω hΩV hΩo hpΩ hfΩ hgS hfg h
    (fun i y => (hha i y (mem_univ _)).differentiableAt) hh0 hhb
    ⟨0,by omega⟩ hpk β hβ hβeq O hOo w hw hcover hexclude
  let L := s.normalMap
  let B₀ := residualQuadraticCoefficients L Q
  let H : Affine s.tangentDim → Fin s.normalDim → ℝ := fun z i => B₀ i z z
  let C₀ : Set (Fin s.normalDim → ℝ) := {y | f (L y) ≠ 0}
  let C := connectedComponentIn C₀ a
  let e₀ := affineProductCoordinates s.tangentDim s.normalDim
  have ha : a ∈ C₀ := by
    change f (s.normalMap (s.normalMap.symm v)) ≠ 0
    simpa only [s.normalMap.apply_symm_apply] using hv
  have hH : Continuous H := residualQuadraticCoefficients_continuous L Q
  have hH0 : H 0=0 := residualQuadraticCoefficients_zero L Q
  have hC₀ : IsOpen C₀ := isOpen_ne_fun (hfl.continuous.comp L.continuous) continuous_const
  have hcone₀ : ∀ t : ℝ, 0 < t → ∀ y ∈ C₀, t • y ∈ C₀ := by
    intro t ht y hy
    change f (L (t • y)) ≠ 0
    rw [map_smul]
    exact (hfcone t ht (L y)).not.mp hy
  obtain ⟨hCo,hCc,hCcone⟩ := open_cone_component hC₀ hcone₀ ha
  have hCzero : (0 : Fin s.normalDim → ℝ) ∉ C := by
    intro h
    have h' := connectedComponentIn_subset C₀ a h
    exact h' (by simpa only [map_zero,mem_ofPred_eq] using hf0)
  have hp : (0,w) ∈ quadraticDomain H C₀ := quadraticDomain_axis H hH0 ha
  have hpa : (fun i => (w i).im-H 0 i)=a := by
    simp only [w,hH0,Pi.zero_apply,sub_zero,Complex.I_mul_im,Complex.ofReal_re]
  have hraw : O=quadraticDomain H C₀ := by
    ext z
    have he : L (Flatten.imaginaryPart s.normalDim z.2-H z.1)=
        L (Flatten.imaginaryPart s.normalDim z.2)+Q (fun _ => z.1) := by
      rw [show H z.1= -L.symm (Q (fun _ => z.1)) from residualQuadraticCoefficients_diag L Q z.1,
        sub_neg_eq_add,map_add,L.apply_symm_apply]
    change f (L (Flatten.imaginaryPart s.normalDim z.2)+Q (fun _ => z.1)) ≠ 0 ↔
      f (L (Flatten.imaginaryPart s.normalDim z.2-H z.1)) ≠ 0
    rw [he]
  have hcc : connectedComponentIn (e₀ '' O) (e₀ (0,w)) =
      e₀ '' quadraticDomain H C := by
    rw [hraw]
    change connectedComponentIn (e₀.toHomeomorph '' quadraticDomain H C₀) (e₀.toHomeomorph (0,w)) = _
    rw [← e₀.toHomeomorph.image_connectedComponentIn hp,
      quadraticDomain_connectedComponent H hH C₀ (0,w),hpa]
    rfl
  have hrawsub : quadraticDomain H C ⊆ O := by
    rw [hraw]
    intro z hz
    exact connectedComponentIn_subset C₀ a hz
  have hcover₀ : ∀ z ∈ quadraticDomain H C,
      ∀ᶠ t : ℝ in 𝓝[>] 0, s.forward (weightedScale t z) ∈ U := by
    intro z hz
    have hh := hcover {z} (isCompact_singleton) (singleton_subset_iff.mpr (hrawsub hz))
    filter_upwards [hh] with t ht
    exact (ht (mem_singleton z)).2
  have hΦ := s.forward_analytic hcut 0 s.source_zero
  have hΨ := s.backward_analytic (q := p.val.complexMap) (p.val.complexMap x) (mem_univ _)
  have hbgf : (s.backward ∘ s.forward) =ᶠ[𝓝 (0 : Affine s.tangentDim × Affine s.normalDim)] id := by
    filter_upwards [s.offsets.open_source.mem_nhds s.source_zero] with z hz
    exact s.backward_forward hcut hz
  have hleft : (fderiv ℂ s.backward (p.val.complexMap x)).comp (fderiv ℂ s.forward 0)=1 := by
    have hd := ((s.forward_zero hcgood).symm ▸ hΨ.differentiableAt.hasFDerivAt).comp 0 hΦ.differentiableAt.hasFDerivAt
    have hd' := hd.congr_of_eventuallyEq hbgf.symm
    simpa only [s.forward_zero hcgood,fderiv_id,ContinuousLinearMap.one_def] using hd'.fderiv.symm
  have hΦi : Function.Injective (fderiv ℂ s.forward 0) := by
    intro z z' hz
    have H := congrArg (fderiv ℂ s.backward (p.val.complexMap x)) hz
    simpa only [←ContinuousLinearMap.comp_apply,hleft,one_apply_eq_self] using H
  obtain ⟨e,c₀,hc₀,hbounds⟩ := supported_hermitian_weighted_model B₀ C s.forward hΦ hΦi U
    hcover₀ h (fun i => by simpa only [s.forward_zero hcgood] using (hha i _ (mem_univ _)).continuousAt)
    (fun i => by simpa only [s.forward_zero hcgood] using hh0 i)
    (fun i y hy => by simpa only [s.forward_zero hcgood,dist_eq_norm] using hpeak i y (subset_closure hy))
    hnew β hβ hβeq
  obtain ⟨g⟩ := hglob
  have g' : Biholomorph U (e₀ '' quadraticDomain H C) := hcc ▸ g
  obtain ⟨shear⟩ := quadraticShear_biholomorph B₀ C
  exact ⟨s.tangentDim,s.normalDim,B₀,C,e,c₀,hk,hCo,hCc,hCzero,hCcone,hc₀,hbounds,
    ⟨g'.trans shear⟩⟩

end Release061

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Release061.original_supported_hermitian_model_oai.{u_1} := @OAI.Release061.original_supported_hermitian_model_oai.{u_1}
