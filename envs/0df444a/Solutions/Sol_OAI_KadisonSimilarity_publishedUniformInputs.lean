-- Prove2me | solution 1 for OAI.KadisonSimilarity.publishedUniformInputs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T15:41:14.958236+00:00
-- url     : https://prove2.me/submissions/4ae3aa79-e4bf-4760-a9d4-37ba1390e327

import Mathlib
import Definitions.Def_OAIQ075A041
import Theorems.Thm_OAI_KadisonSimilarity_ae_common_fiber_scalar_center

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_WeakOperatorCompactness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak-operator compactness of a norm ball, obtained from compact scalar
matrix-coefficient discs and the Hilbert-space representation of bounded forms. -/

noncomputable section
namespace KadisonSimilarity

open scoped Topology
open ContinuousLinearMapWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem norm_operatorOfForm_le (f : H → H → ℂ) (hf : IsOperatorForm f) (R : ℝ)
    (hR : 0 ≤ R) (hb : ∀ x y, ‖f x y‖ ≤ R * ‖x‖ * ‖y‖) :
    ‖operatorOfForm f hf R hb‖ ≤ R := by
  apply norm_le_of_matrix_coefficients _ hR
  intro x y
  rw [← norm_inner_symm, operatorOfForm_inner]
  convert hb x y using 1
  all_goals try with_reducible_and_instances rfl
  ring

omit [CompleteSpace H] in
private theorem isClosed_operatorForms : IsClosed {f : H → H → ℂ | IsOperatorForm f} := by
  have hc (x y : H) : Continuous (fun f : H → H → ℂ => f x y) :=
    (continuous_apply y).comp (continuous_apply x)
  unfold IsOperatorForm
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
  · refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z => ?_
    exact isClosed_eq (hc (x + y) z) ((hc x z).add (hc y z))
  · refine isClosed_iInter fun c => isClosed_iInter fun x => isClosed_iInter fun y => ?_
    exact isClosed_eq (hc (c • x) y) (continuous_const.mul (hc x y))
  · refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z => ?_
    exact isClosed_eq (hc x (y + z)) ((hc x y).add (hc x z))
  · refine isClosed_iInter fun c => isClosed_iInter fun x => isClosed_iInter fun y => ?_
    exact isClosed_eq (hc x (c • y)) (continuous_const.mul (hc x y))

omit [CompleteSpace H] in
private theorem isCompact_boundedOperatorForms (R : ℝ) :
    IsCompact (boundedOperatorForms (H := H) R) := by
  have hd : IsCompact {f : H → H → ℂ | ∀ x y, f x y ∈ Metric.closedBall 0 (R * ‖x‖ * ‖y‖)} :=
    isCompact_pi_infinite fun x => isCompact_pi_infinite fun y => isCompact_closedBall _ _
  have he : boundedOperatorForms (H := H) R =
      {f | IsOperatorForm f} ∩ {f : H → H → ℂ | ∀ x y,
        f x y ∈ Metric.closedBall 0 (R * ‖x‖ * ‖y‖)} := by
    ext f
    simp [boundedOperatorForms, Metric.mem_closedBall, dist_zero_right]
  rw [he]
  exact hd.inter_left isClosed_operatorForms

private theorem continuous_boundedFormOperator (R : ℝ) :
    Continuous (boundedFormOperator (H := H) R) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro x y
  have he : (fun f : boundedOperatorForms (H := H) R =>
      inner ℂ y (boundedFormOperator R f x)) =
      fun f => star (f.val x y) := by
    funext f
    change inner ℂ y (operatorOfForm f.val f.property.1 R f.property.2 x) = _
    rw [← inner_conj_symm, operatorOfForm_inner]
    rfl
  rw [he]
  have hc : Continuous (fun f : H → H → ℂ => f x y) :=
    (continuous_apply y).comp (continuous_apply x)
  exact (hc.comp continuous_subtype_val).star

/-- The closed norm ball in bounded operators on a Hilbert space is compact
in the weak-operator topology. -/
theorem isCompact_weakOperator_ball (R : ℝ) (hR : 0 ≤ R) :
    IsCompact {T : H →WOT[ℂ] H | ‖toCLM T‖ ≤ R} := by
  let : CompactSpace (boundedOperatorForms (H := H) R) :=
    isCompact_iff_compactSpace.mp (isCompact_boundedOperatorForms R)
  have himage : Set.range (boundedFormOperator (H := H) R) =
      {T : H →WOT[ℂ] H | ‖toCLM T‖ ≤ R} := by
    ext T
    constructor
    · rintro ⟨f, rfl⟩
      exact norm_operatorOfForm_le f.val f.property.1 R hR f.property.2
    · intro hT
      let f : H → H → ℂ := fun x y => inner ℂ (T x) y
      have hf : IsOperatorForm f := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro x y z; simp [f, inner_add_left]
        · intro c x y; simp [f, inner_smul_left, mul_comm]
        · intro x y z; simp [f, inner_add_right]
        · intro c x y; simp [f, inner_smul_right]
      have hb : ∀ x y, ‖f x y‖ ≤ R * ‖x‖ * ‖y‖ := by
        intro x y
        calc
          ‖f x y‖ ≤ ‖T x‖ * ‖y‖ := norm_inner_le_norm _ _
          _ ≤ (‖toCLM T‖ * ‖x‖) * ‖y‖ :=
            mul_le_mul_of_nonneg_right ((toCLM T).le_opNorm x) (norm_nonneg y)
          _ ≤ R * ‖x‖ * ‖y‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hT (norm_nonneg x)) (norm_nonneg y)
      refine ⟨⟨f, hf, hb⟩, ?_⟩
      apply ContinuousLinearMapWOT.ext_inner
      intro x y
      change inner ℂ y (operatorOfForm f hf R hb x) = inner ℂ y (T x)
      rw [← inner_conj_symm, operatorOfForm_inner]
      exact inner_conj_symm _ _
  rw [← himage]
  exact isCompact_range (continuous_boundedFormOperator R)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SeparableContractionTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countable weak-operator contraction tests

On a separable Hilbert space, the weak-operator unit ball embeds in a countable
product of copies of `ℂ`, by its coefficients on a dense sequence of vectors.
Compactness makes this an embedding. Thus each von Neumann algebra has a
countable weakly dense family of contractions.
-/

noncomputable section

namespace KadisonSimilarity

open ContinuousLinearMapWOT
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

/-- Countably many matrix coefficients determine the topology on the weak
operator unit ball of a separable Hilbert space. -/
theorem secondCountable_weakOperatorUnitBall :
    SecondCountableTopology (WeakOperatorUnitBall H) := by
  let d : ℕ → H := TopologicalSpace.denseSeq H
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq H
  let f : WeakOperatorUnitBall H → ℕ → ℕ → ℂ :=
    fun T i j => inner ℂ (d i) ((T : H →WOT[ℂ] H) (d j))
  have hf : Continuous f := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact ContinuousLinearMapWOT.continuous_inner_apply continuous_subtype_val (d j) (d i)
  have hinj : Function.Injective f := by
    intro S T h
    apply Subtype.ext
    apply ContinuousLinearMapWOT.ext_inner
    intro x y
    apply hd.induction_on₂ (p := fun x y =>
      inner ℂ y ((S : H →WOT[ℂ] H) x) = inner ℂ y ((T : H →WOT[ℂ] H) x))
      (isClosed_eq (by fun_prop) (by fun_prop)) _ x y
    intro i j
    exact congrFun (congrFun h j) i
  let : CompactSpace (WeakOperatorUnitBall H) :=
    isCompact_iff_compactSpace.mp (isCompact_weakOperator_ball (H := H) 1 zero_le_one)
  exact (hf.isClosedEmbedding hinj).isEmbedding.secondCountableTopology

/-- A concrete von Neumann algebra on a separable Hilbert space has a
countable weak-operator dense family in its closed unit ball. -/
theorem exists_separable_contraction_tests (P : VonNeumannAlgebra H) :
    ∃ test : ℕ → P.toStarSubalgebra,
      (∀ n, ‖test n‖ ≤ 1) ∧
      ∀ T : H →L[ℂ] H, T ∈ P → ‖T‖ ≤ 1 →
        ofCLM T ∈ closure (Set.range fun n => ofCLM (test n : H →L[ℂ] H)) := by
  let : SecondCountableTopology (WeakOperatorUnitBall H) :=
    secondCountable_weakOperatorUnitBall
  let B := {T : WeakOperatorUnitBall H // toCLM T.val ∈ P}
  let : SecondCountableTopology B :=
    (show Topology.IsEmbedding (Subtype.val : B → WeakOperatorUnitBall H) from
      Topology.IsEmbedding.subtypeVal).secondCountableTopology
  let : TopologicalSpace.SeparableSpace B := inferInstance
  let : Nonempty B := ⟨⟨⟨ofCLM 0, by simp⟩, P.zero_mem⟩⟩
  let d : ℕ → B := TopologicalSpace.denseSeq B
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq B
  let test : ℕ → P.toStarSubalgebra :=
    fun n => ⟨toCLM (d n).val.val, (d n).property⟩
  refine ⟨test, fun n => (d n).val.property, ?_⟩
  intro T hT hn
  let t : B := ⟨⟨ofCLM T, hn⟩, hT⟩
  let inclusion : B → H →WOT[ℂ] H := fun x => x.val.val
  have hc : Continuous inclusion := continuous_subtype_val.comp continuous_subtype_val
  change inclusion t ∈ _
  exact map_mem_closure (f := inclusion) hc (hd t) (by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, rfl⟩)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DenseStarRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending the pointwise algebra in a fiber

This is the norm-continuity step in Blackadar, III.5.1.11. A contractive
unital ring representation on a dense subring extends to the C-star algebra.
Preservation of star and of `i · 1` makes that extension a complex star
representation. Countability is needed only to gather almost-everywhere
relations on a common conull set, not for the extension itself.
-/

noncomputable section
namespace KadisonSimilarity

open scoped Topology CStarAlgebra

variable {A : Type*} [CStarAlgebra A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem denseSubringRepresentation_continuous
    (S : Subring A) (hdense : Dense (S : Set A))
    (f : S →+* (H →L[ℂ] H)) (hnorm : ∀ a : S, ‖f a‖ ≤ ‖a‖) :
    Continuous (denseSubringRepresentation S hdense f hnorm) := by
  exact (uniformContinuous_uniformly_extend
    isUniformEmbedding_subtype_val.isUniformInducing hdense.denseRange_val
    (denseSubring_uniformContinuous S f hnorm)).continuous

omit [CompleteSpace H] in
/-- Continuity of an additive map gives real linearity; preserving `i · 1`
then forces preservation of every complex scalar. -/
theorem continuousRingHom_commutes_complex
    (F : A →+* (H →L[ℂ] H)) (hF : Continuous F)
    (hI : F (algebraMap ℂ A Complex.I) = algebraMap ℂ (H →L[ℂ] H) Complex.I) :
    ∀ z : ℂ, F (algebraMap ℂ A z) = algebraMap ℂ (H →L[ℂ] H) z := by
  have hr (r : ℝ) : F (algebraMap ℂ A (r : ℂ)) =
      algebraMap ℂ (H →L[ℂ] H) (r : ℂ) := by
    calc
      F (algebraMap ℂ A (r : ℂ)) = F (r • (1 : A)) := by
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ), Algebra.algebraMap_eq_smul_one]
        rfl
      _ = r • F 1 := map_real_smul F hF r 1
      _ = algebraMap ℂ (H →L[ℂ] H) (r : ℂ) := by
        rw [map_one, RCLike.real_smul_eq_coe_smul (K := ℂ),
          Algebra.algebraMap_eq_smul_one]
        rfl
  intro z
  calc
    F (algebraMap ℂ A z) =
        F (algebraMap ℂ A ((z.re : ℂ) + (z.im : ℂ) * Complex.I)) := by
      rw [Complex.re_add_im]
    _ = algebraMap ℂ (H →L[ℂ] H) ((z.re : ℂ) + (z.im : ℂ) * Complex.I) := by
      simp only [map_add, map_mul, hr, hI]
    _ = algebraMap ℂ (H →L[ℂ] H) z := by rw [Complex.re_add_im]

/-- A continuous ring extension is a complex star representation when its
dense restriction preserves star and the scalar `i`. -/
theorem exists_starRepresentation_of_ring_extension
    (S : Subring A) (hdense : Dense (S : Set A))
    (hstarS : ∀ a ∈ S, star a ∈ S) (hIS : algebraMap ℂ A Complex.I ∈ S)
    (f : S →+* (H →L[ℂ] H)) (F : A →+* (H →L[ℂ] H))
    (hF : Continuous F) (hext : ∀ a : S, F a = f a)
    (hstar : ∀ a : S, f ⟨star a.val, hstarS a.val a.property⟩ = star (f a))
    (hI : f ⟨algebraMap ℂ A Complex.I, hIS⟩ = algebraMap ℂ (H →L[ℂ] H) Complex.I) :
    ∃ σ : A →⋆ₐ[ℂ] (H →L[ℂ] H), ∀ a : S, σ a = f a := by
  have hFstar : ∀ a : A, F (star a) = star (F a) := by
    intro a
    refine hdense.denseRange_val.induction_on
      (p := fun a => F (star a) = star (F a)) a
      (isClosed_eq (hF.comp continuous_star) (continuous_star.comp hF)) ?_
    intro b
    calc
      F (star (b : A)) = f ⟨star b.val, hstarS b.val b.property⟩ :=
        hext ⟨star b.val, hstarS b.val b.property⟩
      _ = star (f b) := hstar b
      _ = star (F (b : A)) :=
        congrArg star (hext b).symm
  have hFI : F (algebraMap ℂ A Complex.I) = algebraMap ℂ (H →L[ℂ] H) Complex.I := by
    exact (hext ⟨algebraMap ℂ A Complex.I, hIS⟩).trans hI
  let σ : A →⋆ₐ[ℂ] (H →L[ℂ] H) := {
    F with
    commutes' := continuousRingHom_commutes_complex F hF hFI
    map_star' := hFstar }
  exact ⟨σ, hext⟩

/-- A contractive unital ring representation on a dense star subring extends
to a complex star representation when it preserves the scalar `i`. -/
theorem exists_starRepresentation_of_dense_subring
    (S : Subring A) (hdense : Dense (S : Set A))
    (hstarS : ∀ a ∈ S, star a ∈ S) (hIS : algebraMap ℂ A Complex.I ∈ S)
    (f : S →+* (H →L[ℂ] H)) (hnorm : ∀ a : S, ‖f a‖ ≤ ‖a‖)
    (hstar : ∀ a : S, f ⟨star a.val, hstarS a.val a.property⟩ = star (f a))
    (hI : f ⟨algebraMap ℂ A Complex.I, hIS⟩ = algebraMap ℂ (H →L[ℂ] H) Complex.I) :
    ∃ σ : A →⋆ₐ[ℂ] (H →L[ℂ] H), ∀ a : S, σ a = f a :=
  exists_starRepresentation_of_ring_extension S hdense hstarS hIS f
    (denseSubringRepresentation S hdense f hnorm)
    (denseSubringRepresentation_continuous S hdense f hnorm)
    (denseSubringRepresentation_apply S hdense f hnorm) hstar hI

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_AEStarRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common conull set for fiber representations

Countability of the dense subring lets all algebraic identities and norm
bounds hold on a single conull set. Each of those fibers then has the genuine
complex star representation constructed in `DenseStarRepresentation`.
Exceptional fibers are left out of the existence assertion.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter

variable {A : Type*} [CStarAlgebra A]
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (K : Ω → Type*) [∀ x, NormedAddCommGroup (K x)]
  [∀ x, InnerProductSpace ℂ (K x)] [∀ x, CompleteSpace (K x)]

/-- Pointwise representatives on a countable dense star subring extend to
complex star representations almost everywhere. Each input identity is
required only almost everywhere for its fixed tuple of arguments. -/
theorem ae_exists_starRepresentation_of_countable_subring
    (S : Subring A) [Countable S] (hdense : Dense (S : Set A))
    (hstarS : ∀ a ∈ S, star a ∈ S) (hIS : algebraMap ℂ A Complex.I ∈ S)
    (f : ∀ _a : S, ∀ x, K x →L[ℂ] K x)
    (hzero : ∀ᵐ x ∂μ, f 0 x = 0)
    (hone : ∀ᵐ x ∂μ, f 1 x = 1)
    (hadd : ∀ a b : S, ∀ᵐ x ∂μ, f (a + b) x = f a x + f b x)
    (hmul : ∀ a b : S, ∀ᵐ x ∂μ, f (a * b) x = f a x * f b x)
    (hnorm : ∀ a : S, ∀ᵐ x ∂μ, ‖f a x‖ ≤ ‖a‖)
    (hstar : ∀ a : S, ∀ᵐ x ∂μ,
      f ⟨star a.val, hstarS a.val a.property⟩ x = star (f a x))
    (hI : ∀ᵐ x ∂μ, f ⟨algebraMap ℂ A Complex.I, hIS⟩ x =
      algebraMap ℂ (K x →L[ℂ] K x) Complex.I) :
    ∀ᵐ x ∂μ, ∃ σ : A →⋆ₐ[ℂ] (K x →L[ℂ] K x), ∀ a : S, σ a = f a x := by
  have hadd_all : ∀ᵐ x ∂μ, ∀ a b : S, f (a + b) x = f a x + f b x :=
    eventually_countable_forall.mpr fun a => eventually_countable_forall.mpr (hadd a)
  have hmul_all : ∀ᵐ x ∂μ, ∀ a b : S, f (a * b) x = f a x * f b x :=
    eventually_countable_forall.mpr fun a => eventually_countable_forall.mpr (hmul a)
  have hnorm_all : ∀ᵐ x ∂μ, ∀ a : S, ‖f a x‖ ≤ ‖a‖ :=
    eventually_countable_forall.mpr hnorm
  have hstar_all : ∀ᵐ x ∂μ, ∀ a : S,
      f ⟨star a.val, hstarS a.val a.property⟩ x = star (f a x) :=
    eventually_countable_forall.mpr hstar
  filter_upwards [hzero, hone, hadd_all, hmul_all, hnorm_all, hstar_all, hI]
    with x hz ho ha hm hn hs hi
  let F : S →+* (K x →L[ℂ] K x) := {
    toFun := fun a => f a x
    map_zero' := hz
    map_one' := ho
    map_add' := ha
    map_mul' := hm }
  exact exists_starRepresentation_of_dense_subring S hdense hstarS hIS F hn hs hi

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CountableDenseStarSubring
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countable dense star subrings

A separable complex C-star algebra has a countable norm-dense subring,
closed under star and containing the scalar `i`. This supplies the domain
on which countably many almost-everywhere algebra identities suffice.
-/

noncomputable section
namespace KadisonSimilarity

open scoped Topology Pointwise

theorem countable_subringClosure {R : Type*} [Ring R] {s : Set R}
    (hs : s.Countable) : (Subring.closure s : Set R).Countable := by
  let : Countable s := hs.to_subtype
  let f : FreeRing s →+* R := FreeRing.lift (fun x : s => (x : R))
  have hle : Subring.closure s ≤ f.range := Subring.closure_le.mpr fun x hx => by
    exact ⟨FreeRing.of ⟨x, hx⟩, FreeRing.lift_of _ _⟩
  exact (Set.countable_range f).mono hle

theorem star_mem_subringClosure_union {R : Type*} [Ring R] [StarRing R]
    (s : Set R) {x : R} (hx : x ∈ Subring.closure (s ∪ star s)) :
    star x ∈ Subring.closure (s ∪ star s) := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
      apply Subring.subset_closure
      rcases hx with hx | hx
      · exact Or.inr (Set.star_mem_star.mpr hx)
      · exact Or.inl (Set.mem_star.mp hx)
  | zero => simpa only [star_zero] using (Subring.closure (s ∪ star s)).zero_mem
  | one => simpa only [star_one] using (Subring.closure (s ∪ star s)).one_mem
  | add x y _ _ hx hy => simpa only [star_add] using add_mem hx hy
  | neg x _ hx => simpa only [star_neg] using neg_mem hx
  | mul x y _ _ hx hy => simpa only [star_mul] using mul_mem hy hx

/-- A concrete countable domain for gathering the pointwise fiber laws. -/
theorem exists_countable_dense_star_subring (A : Type*) [CStarAlgebra A]
    [TopologicalSpace.SeparableSpace A] :
    ∃ S : Subring A, (S : Set A).Countable ∧ Dense (S : Set A) ∧
      (∀ a ∈ S, star a ∈ S) ∧ algebraMap ℂ A Complex.I ∈ S := by
  let s : Set A := Set.range (TopologicalSpace.denseSeq A) ∪
    {algebraMap ℂ A Complex.I}
  let S := Subring.closure (s ∪ star s)
  have hs : s.Countable := (Set.countable_range _).union (Set.countable_singleton _)
  have hstar : (star s).Countable := by
    rw [← Set.image_star]
    exact hs.image star
  refine ⟨S, countable_subringClosure (hs.union hstar), ?_, ?_, ?_⟩
  · exact (TopologicalSpace.denseRange_denseSeq A).mono fun a ha =>
      Subring.subset_closure (Or.inl (Or.inl ha))
  · exact fun a ha => star_mem_subringClosure_union s ha
  · exact Subring.subset_closure (Or.inl (Or.inr (Set.mem_singleton _)))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_AERepresentationAgreement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Agreement of the reconstructed fiber representations

For each fixed algebra element, the genuine representations reconstructed
from a countable dense subring agree almost everywhere with the original
operator representatives. Only countably many approximants are used for
that element; no uncountable intersection of conull sets is taken.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology CStarAlgebra

variable {A : Type*} [CStarAlgebra A]
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (K : Ω → Type*) [∀ x, NormedAddCommGroup (K x)]
  [∀ x, InnerProductSpace ℂ (K x)] [∀ x, CompleteSpace (K x)]

/-- Every extension of the dense-subring representatives has the correct
value at a fixed `a`, outside a null set that may depend on `a`. -/
theorem ae_starRepresentation_agrees_at
    (S : Subring A) (hdense : Dense (S : Set A))
    (f : ∀ _a : A, ∀ x, K x →L[ℂ] K x)
    (hsub : ∀ a b : A, ∀ᵐ x ∂μ, f (a - b) x = f a x - f b x)
    (hnorm : ∀ a : A, ∀ᵐ x ∂μ, ‖f a x‖ ≤ ‖a‖) (a : A) :
    ∀ᵐ x ∂μ, ∀ σ : A →⋆ₐ[ℂ] (K x →L[ℂ] K x),
      (∀ b : S, σ b = f b x) → σ a = f a x := by
  obtain ⟨b, hb, hlim⟩ := mem_closure_iff_seq_limit.mp (hdense a)
  have hsub_all : ∀ᵐ x ∂μ, ∀ n : ℕ, f (a - b n) x = f a x - f (b n) x :=
    eventually_countable_forall.mpr (fun n => hsub a (b n))
  have hnorm_all : ∀ᵐ x ∂μ, ∀ n : ℕ, ‖f (a - b n) x‖ ≤ ‖a - b n‖ :=
    eventually_countable_forall.mpr (fun n => hnorm (a - b n))
  filter_upwards [hsub_all, hnorm_all] with x hsubx hnormx
  intro σ hσ
  have hbound (n : ℕ) : ‖σ a - f a x‖ ≤ ‖a - b n‖ + ‖a - b n‖ := by
    calc
      ‖σ a - f a x‖ ≤ ‖σ a - σ (b n)‖ + ‖σ (b n) - f a x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖a - b n‖ + ‖a - b n‖ := add_le_add
        (by rw [← map_sub]; exact NonUnitalStarAlgHom.norm_apply_le σ _)
        (by
          rw [hσ ⟨b n, hb n⟩, norm_sub_rev, ← hsubx n]
          exact hnormx n)
  have hzero : Tendsto (fun n => ‖a - b n‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a)).sub hlim).norm
  have hle : ‖σ a - f a x‖ ≤ 0 := by
    simpa only [zero_add] using ge_of_tendsto' (hzero.add hzero) hbound
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hle (norm_nonneg _)))

/-- Countably many fiber relations suffice for genuine representations,
and their values agree almost everywhere with every fixed original section.
The statement leaves exceptional fibers unspecified. -/
theorem exists_dense_subring_ae_fiber_representations
    [TopologicalSpace.SeparableSpace A]
    (f : ∀ _a : A, ∀ x, K x →L[ℂ] K x)
    (hzero : ∀ᵐ x ∂μ, f 0 x = 0)
    (hone : ∀ᵐ x ∂μ, f 1 x = 1)
    (hadd : ∀ a b : A, ∀ᵐ x ∂μ, f (a + b) x = f a x + f b x)
    (hmul : ∀ a b : A, ∀ᵐ x ∂μ, f (a * b) x = f a x * f b x)
    (hnorm : ∀ a : A, ∀ᵐ x ∂μ, ‖f a x‖ ≤ ‖a‖)
    (hstar : ∀ a : A, ∀ᵐ x ∂μ, f (star a) x = star (f a x))
    (hI : ∀ᵐ x ∂μ, f (algebraMap ℂ A Complex.I) x =
      algebraMap ℂ (K x →L[ℂ] K x) Complex.I) :
    ∃ S : Subring A, Countable S ∧ Dense (S : Set A) ∧
      (∀ᵐ x ∂μ, ∃ σ : A →⋆ₐ[ℂ] (K x →L[ℂ] K x), ∀ b : S, σ b = f b x) ∧
      (∀ a : A, ∀ᵐ x ∂μ, ∀ σ : A →⋆ₐ[ℂ] (K x →L[ℂ] K x),
        (∀ b : S, σ b = f b x) → σ a = f a x) := by
  obtain ⟨S, hcount, hdense, hstarS, hIS⟩ := exists_countable_dense_star_subring A
  let : Countable S := hcount.to_subtype
  refine ⟨S, inferInstance, hdense, ?_, ?_⟩
  · exact ae_exists_starRepresentation_of_countable_subring μ K S hdense hstarS hIS
      (fun b x => f b x) hzero hone (fun a b => hadd a b) (fun a b => hmul a b)
      (fun a => hnorm a) (fun a => hstar a) hI
  · intro a
    apply ae_starRepresentation_agrees_at μ K S hdense f _ hnorm a
    intro b c
    filter_upwards [hadd (b - c) c] with x hx
    apply eq_sub_iff_add_eq.mpr
    simpa only [sub_add_cancel] using hx.symm

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ConullStarRepresentations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Genuine fiber representations on a measurable conull base

Restricting to a measurable conull set allows the almost-everywhere
representation theorem to be used as an actual family of representations.
The original section for each fixed algebra element remains unchanged
almost everywhere after this restriction.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter

variable {A : Type*} [CStarAlgebra A]
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (K : Ω → Type*) [∀ x, NormedAddCommGroup (K x)]
  [∀ x, InnerProductSpace ℂ (K x)] [∀ x, CompleteSpace (K x)]

/-- Choose genuine representations on a measurable conull set, retaining
the prescribed representatives almost everywhere for each fixed element. -/
theorem exists_conull_starRepresentations
    (S : Subring A) (f : ∀ _a : A, ∀ x, K x →L[ℂ] K x)
    (hexists : ∀ᵐ x ∂μ, ∃ σ : A →⋆ₐ[ℂ] (K x →L[ℂ] K x),
      ∀ b : S, σ b = f b x)
    (hagrees : ∀ a : A, ∀ᵐ x ∂μ, ∀ σ : A →⋆ₐ[ℂ] (K x →L[ℂ] K x),
      (∀ b : S, σ b = f b x) → σ a = f a x) :
    ∃ s : Set Ω, MeasurableSet s ∧ μ sᶜ = 0 ∧
      ∃ σ : ∀ x : s, A →⋆ₐ[ℂ] (K x →L[ℂ] K x),
        ∀ a : A, ∀ᵐ x ∂Measure.comap ((↑) : s → Ω) μ, σ x a = f a x := by
  classical
  obtain ⟨s, hs, hsm, hsexists⟩ := hexists.exists_measurable_mem
  choose σ hσ using fun x : s => hsexists x x.property
  refine ⟨s, hsm, ?_, σ, ?_⟩
  · exact (mem_ae_iff.mp hs)
  · intro a
    have h := (ae_restrict_iff_subtype hsm).mp (ae_restrict_of_ae (hagrees a))
    exact h.mono fun x hx => hx (σ x) (hσ x)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DiagonalFieldAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise action on all L² vectors

The field reconstructed from constant columns acts pointwise on arbitrary
L² vectors. Indicator constants give a dense class; two successive AE
subsequences prove that the pointwise-action identity is norm closed.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [TopologicalSpace.SeparableSpace H]

omit [IsFiniteMeasure μ] [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
/-- An AE norm bound on a conull pointwise field bounds the original L²
operator. This proves the converse direction of the essential-norm formula. -/
theorem norm_le_of_conull_pointwise_action
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (s : Set Ω) (hsm : MeasurableSet s) (hsnull : μ sᶜ = 0)
    (field : ∀ _a : s, H →L[ℂ] H)
    (haction : ∀ f : Lp H 2 μ, ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ,
      T f a = field a (f a))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ, ‖field a‖ ≤ C) : ‖T‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  have hs : ∀ᵐ a ∂μ, a ∈ s := mem_ae_iff.mpr hsnull
  have hsub : ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ, ‖T f a‖ ≤ C * ‖f a‖ := by
    filter_upwards [haction f, hbound] with a he hb
    rw [he]
    exact ((field a).le_opNorm _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  have hglobal : ∀ᵐ a ∂μ, ‖T f a‖ ≤ C * ‖f a‖ := by
    have hr : ∀ᵐ a ∂μ.restrict s, ‖T f a‖ ≤ C * ‖f a‖ :=
      (ae_restrict_iff_subtype (μ := μ)
        (p := fun a : Ω => ‖T f a‖ ≤ C * ‖f a‖) hsm).mpr hsub
    filter_upwards [hs, (ae_restrict_iff' hsm).mp hr] with a ha h
    exact h ha
  calc
    ‖T f‖ ≤ ‖(C : ℂ) • f‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hglobal, Lp.coeFn_smul (C : ℂ) f] with a ha he
      rw [he, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hC]
      exact ha
    _ = C * ‖f‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DiagonalFieldAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Algebraic laws for fields of diagonal-commuting operators

The fields are constructed from the actual operators. Their algebraic laws
hold almost everywhere, by the pointwise action on all L² vectors and a
countable dense family of constant columns.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem diagonalField_norm
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ (r : Set Ω) (hr : MeasurableSet r),
      T * l2Localization μ r hr = l2Localization μ r hr * T) (a : Ω) :
    ‖diagonalField μ T hT a‖ ≤ ‖T‖ :=
  (Classical.choose_spec (exists_global_diagonal_field μ T hT)).1 a

omit [CompleteSpace H] in
/-- Zero is preserved by any field realizing its pointwise action. -/
theorem pointwise_field_zero (R : Ω → H →L[ℂ] H)
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, (0 : Lp H 2 μ →L[ℂ] Lp H 2 μ) f a = R a (f a)) :
    ∀ᵐ a ∂μ, R a = 0 := by
  apply ae_operator_eq_of_forall_vectors
  intro x
  filter_upwards [pointwise_action_column μ 0 R hR x, Lp.coeFn_zero H 2 μ] with a ha hz
  simpa only [zero_apply, hz, Pi.zero_apply] using ha.symm

omit [CompleteSpace H] in
/-- The identity is preserved almost everywhere. -/
theorem pointwise_field_one (R : Ω → H →L[ℂ] H)
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, (1 : Lp H 2 μ →L[ℂ] Lp H 2 μ) f a = R a (f a)) :
    ∀ᵐ a ∂μ, R a = 1 := by
  apply ae_operator_eq_of_forall_vectors
  intro x
  filter_upwards [pointwise_action_column μ 1 R hR x, Lp.coeFn_const 2 μ x] with a ha hc
  simpa only [one_apply_eq_self, hc, Function.const_apply] using ha.symm

omit [CompleteSpace H] in
/-- Addition of L² operators becomes addition of their fields. -/
theorem pointwise_field_add
    (T S : Lp H 2 μ →L[ℂ] Lp H 2 μ) (R Q U : Ω → H →L[ℂ] H)
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a))
    (hQ : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, S f a = Q a (f a))
    (hU : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, (T + S) f a = U a (f a)) :
    ∀ᵐ a ∂μ, U a = R a + Q a := by
  apply ae_operator_eq_of_forall_vectors
  intro x
  filter_upwards [pointwise_action_column μ T R hR x,
    pointwise_action_column μ S Q hQ x, pointwise_action_column μ (T + S) U hU x,
    Lp.coeFn_add (T (Lp.const 2 μ x)) (S (Lp.const 2 μ x))] with a hr hq hu hadd
  simpa only [add_apply, hadd, Pi.add_apply, hr, hq] using hu.symm

omit [CompleteSpace H] in
/-- Complex scalar multiplication, in particular multiplication by `i`,
is inherited from the actual L² operators. -/
theorem pointwise_field_smul
    (c : ℂ) (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) (R U : Ω → H →L[ℂ] H)
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a))
    (hU : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, (c • T) f a = U a (f a)) :
    ∀ᵐ a ∂μ, U a = c • R a := by
  apply ae_operator_eq_of_forall_vectors
  intro x
  filter_upwards [pointwise_action_column μ T R hR x,
    pointwise_action_column μ (c • T) U hU x,
    Lp.coeFn_smul c (T (Lp.const 2 μ x))] with a hr hu hsmul
  simpa only [smul_apply, hsmul, Pi.smul_apply, hr] using hu.symm

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DiagonalFieldAdjoint
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Adjoint compatibility of the actual diagonal field

Localized inner products recover the adjoint identity almost everywhere.
Together with the algebraic laws, this supplies the raw AE relations needed
for the conull fiber-representation construction.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A measurable localization is symmetric for the L² inner product. -/
theorem l2Localization_inner (s : Set Ω) (hs : MeasurableSet s)
    (f g : Lp H 2 μ) :
    inner ℂ (l2Localization μ s hs f) g = inner ℂ f (l2Localization μ s hs g) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2Localization_ae μ s hs f, l2Localization_ae μ s hs g]
    with a hf hg
  rw [hf, hg]
  by_cases ha : a ∈ s
  · simp only [Set.indicator_of_mem ha]
  · simp only [Set.indicator_of_notMem ha, inner_zero_left, inner_zero_right]

omit [CompleteSpace H] in
/-- The right-indicator version of the standard L² set-integral formula. -/
theorem inner_indicatorConstLp_right (f : Lp H 2 μ)
    (s : Set Ω) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (y : H) :
    inner ℂ f (indicatorConstLp 2 hs hμs y) = ∫ a in s, inner ℂ (f a) y ∂μ := by
  rw [L2.inner_def, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := y)]
    with a ha
  rw [ha]
  by_cases h : a ∈ s
  · simp only [Set.indicator_of_mem h]
  · simp only [Set.indicator_of_notMem h, inner_zero_right]

variable [IsFiniteMeasure μ]

/-- Equality of all localized inner products identifies adjoint constant
columns almost everywhere. -/
theorem diagonal_adjoint_columns
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ (r : Set Ω) (hr : MeasurableSet r),
      T * l2Localization μ r hr = l2Localization μ r hr * T) (x y : H) :
    ∀ᵐ a ∂μ, inner ℂ x (T (Lp.const 2 μ y) a) =
      inner ℂ ((star T) (Lp.const 2 μ x) a) y := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s _ hμs
    exact (integrableOn_Lp_of_measure_ne_top (T (Lp.const 2 μ y))
      fact_one_le_two_ennreal.elim hμs.ne).const_inner x
  · intro s _ hμs
    exact (integrableOn_Lp_of_measure_ne_top ((star T) (Lp.const 2 μ x))
      fact_one_le_two_ennreal.elim hμs.ne).inner_const y
  · intro s hs hμs
    have hcomm := congrArg (fun A : Lp H 2 μ →L[ℂ] Lp H 2 μ => A (Lp.const 2 μ y))
      (hT s hs)
    change T (l2Localization μ s hs (Lp.const 2 μ y)) =
      l2Localization μ s hs (T (Lp.const 2 μ y)) at hcomm
    calc
      (∫ a in s, inner ℂ x (T (Lp.const 2 μ y) a) ∂μ) =
          inner ℂ (indicatorConstLp 2 hs hμs.ne x) (T (Lp.const 2 μ y)) :=
        (L2.inner_indicatorConstLp_eq_setIntegral_inner ℂ _ hs x hμs.ne).symm
      _ = inner ℂ (l2Localization μ s hs (Lp.const 2 μ x)) (T (Lp.const 2 μ y)) := by
        rw [l2Localization_const]
      _ = inner ℂ (Lp.const 2 μ x) (l2Localization μ s hs (T (Lp.const 2 μ y))) :=
        l2Localization_inner μ s hs _ _
      _ = inner ℂ (Lp.const 2 μ x) (T (l2Localization μ s hs (Lp.const 2 μ y))) := by
        rw [hcomm]
      _ = inner ℂ ((star T) (Lp.const 2 μ x)) (l2Localization μ s hs (Lp.const 2 μ y)) :=
        (ContinuousLinearMap.adjoint_inner_left T _ _).symm
      _ = inner ℂ ((star T) (Lp.const 2 μ x)) (indicatorConstLp 2 hs hμs.ne y) := by
        rw [l2Localization_const]
      _ = ∫ a in s, inner ℂ ((star T) (Lp.const 2 μ x) a) y ∂μ :=
        inner_indicatorConstLp_right μ _ s hs hμs.ne y

variable [TopologicalSpace.SeparableSpace H]

/-- Adjoint compatibility follows from the original operator's localized
inner products, rather than being postulated as a field relation. -/
theorem pointwise_field_star
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ (r : Set Ω) (hr : MeasurableSet r),
      T * l2Localization μ r hr = l2Localization μ r hr * T)
    (R Q : Ω → H →L[ℂ] H)
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a))
    (hQ : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, (star T) f a = Q a (f a)) :
    ∀ᵐ a ∂μ, Q a = star (R a) := by
  apply ae_operator_eq_of_forall_vectors
  intro x
  have hpair (y : H) : ∀ᵐ a ∂μ, inner ℂ (Q a x) y = inner ℂ x (R a y) := by
    filter_upwards [diagonal_adjoint_columns μ T hT x y,
      pointwise_action_column μ T R hR y,
      pointwise_action_column μ (star T) Q hQ x] with a ha hr hq
    rw [hr, hq] at ha
    exact ha.symm
  have hall : ∀ᵐ a ∂μ, ∀ n : ℕ,
      inner ℂ (Q a x) (TopologicalSpace.denseSeq H n) =
        inner ℂ x (R a (TopologicalSpace.denseSeq H n)) :=
    eventually_countable_forall.mpr fun n => hpair (TopologicalSpace.denseSeq H n)
  filter_upwards [hall] with a ha
  apply ext_inner_right ℂ
  intro y
  have heq : (fun z => inner ℂ (Q a x) z) = (fun z => inner ℂ x (R a z)) :=
    (TopologicalSpace.denseRange_denseSeq H).equalizer
      (by fun_prop) (by fun_prop) (funext ha)
  rw [congrFun heq y]
  exact (ContinuousLinearMap.adjoint_inner_left (R a) y x).symm

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_DiagonalFiberRepresentations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Genuine representations of the diagonal commutant

For a norm-separable C-star algebra acting on a constant-fiber L² space,
commutation with measurable localizations gives genuine representations on
a conull base. All raw AE algebraic relations are derived from the actual
L² action. The original operator norm is recovered from the fiber norms.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology ENNReal CStarAlgebra

variable {A Ω H : Type*} [CStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- Actual diagonal-commuting representations decompose into genuine fiber
representations, with pointwise action on every L² vector and the exact
scalar norm-bound equivalence. -/
theorem exists_conull_diagonal_star_representations
    (σ : A →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (hσ : ∀ (b : A) (r : Set Ω) (hr : MeasurableSet r),
      σ b * l2Localization μ r hr = l2Localization μ r hr * σ b) :
    ∃ s : Set Ω, MeasurableSet s ∧ μ sᶜ = 0 ∧
      ∃ ρ : ∀ _a : s, A →⋆ₐ[ℂ] (H →L[ℂ] H),
        (∀ (b : A) (f : Lp H 2 μ),
          ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ,
            σ b f a = ρ a b (f a)) ∧
        ∀ (b : A) (C : ℝ), 0 ≤ C →
          (‖σ b‖ ≤ C ↔ ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ, ‖ρ a b‖ ≤ C) := by
  let F : A → Ω → H →L[ℂ] H := fun b => diagonalField μ (σ b) (hσ b)
  have hact (b : A) (f : Lp H 2 μ) : ∀ᵐ a ∂μ, σ b f a = F b a (f a) :=
    diagonalField_action μ (σ b) (hσ b) f
  have hzero : ∀ᵐ a ∂μ, F 0 a = 0 :=
    pointwise_field_zero μ _ (by simpa only [map_zero] using hact 0)
  have hone : ∀ᵐ a ∂μ, F 1 a = 1 :=
    pointwise_field_one μ _ (by simpa only [map_one] using hact 1)
  have hadd (b c : A) : ∀ᵐ a ∂μ, F (b + c) a = F b a + F c a :=
    pointwise_field_add μ (σ b) (σ c) _ _ _ (hact b) (hact c)
      (by simpa only [map_add] using hact (b + c))
  have hmul (b c : A) : ∀ᵐ a ∂μ, F (b * c) a = F b a * F c a :=
    pointwise_field_mul μ (σ b) (σ c) _ _ _ (hact b) (hact c)
      (by simpa only [map_mul] using hact (b * c))
  have hnorm (b : A) : ∀ᵐ a ∂μ, ‖F b a‖ ≤ ‖b‖ :=
    .of_forall fun a => (diagonalField_norm μ (σ b) (hσ b) a).trans
      (NonUnitalStarAlgHom.norm_apply_le σ b)
  have hstar (b : A) : ∀ᵐ a ∂μ, F (star b) a = star (F b a) :=
    pointwise_field_star μ (σ b) (hσ b) _ _ (hact b)
      (by simpa only [map_star] using hact (star b))
  have hI : ∀ᵐ a ∂μ, F (algebraMap ℂ A Complex.I) a =
      algebraMap ℂ (H →L[ℂ] H) Complex.I := by
    have hσI : σ (algebraMap ℂ A Complex.I) = Complex.I • 1 := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one]
    have hi := pointwise_field_smul μ Complex.I 1 (F 1)
      (F (algebraMap ℂ A Complex.I))
      (by simpa only [map_one] using hact 1)
      (by simpa only [hσI] using
        hact (algebraMap ℂ A Complex.I))
    filter_upwards [hi, hone] with a ha ho
    simpa only [ho, Algebra.algebraMap_eq_smul_one] using ha
  obtain ⟨S, _, _, hexists, hagrees⟩ :=
    exists_dense_subring_ae_fiber_representations μ (fun _ => H)
      F hzero hone hadd hmul hnorm hstar hI
  obtain ⟨s, hsm, hsnull, ρ, hρ⟩ :=
    exists_conull_starRepresentations μ (fun _ => H) S F hexists hagrees
  have haction (b : A) (f : Lp H 2 μ) :
      ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ, σ b f a = ρ a b (f a) := by
    have h := (ae_restrict_iff_subtype hsm).mp (ae_restrict_of_ae (hact b f))
    filter_upwards [h, hρ b] with a ha hb
    rw [hb]
    exact ha
  refine ⟨s, hsm, hsnull, ρ, haction, ?_⟩
  intro b C hC
  constructor
  · intro hb
    have hn : ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ, ‖F b a‖ ≤ ‖σ b‖ := by
      apply (ae_restrict_iff_subtype (μ := μ)
        (p := fun a : Ω => ‖F b a‖ ≤ ‖σ b‖) hsm).mp
      exact ae_restrict_of_ae (.of_forall (diagonalField_norm μ (σ b) (hσ b)))
    filter_upwards [hρ b, hn] with a ha hn
    rw [ha]
    exact hn.trans hb
  · exact norm_le_of_conull_pointwise_action μ (σ b) s hsm hsnull
      (fun a => ρ a b) (haction b) C hC

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_UnitalizedExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extension by zero is a nonunital star homomorphism. Its unitization
provides a genuine representation whose distinguished projection recovers
the original Hilbert subspace. -/

noncomputable section
namespace KadisonSimilarity

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (J : H →ₗᵢ[ℂ] K)

variable {B : Type*} [CStarAlgebra B] (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] in
theorem separable_unitization [TopologicalSpace.SeparableSpace B] :
    TopologicalSpace.SeparableSpace (Unitization ℂ B) :=
  (Unitization.uniformEquivProd.symm.surjective.denseRange).separableSpace
    Unitization.uniformEquivProd.symm.continuous

theorem unitalizedExtension_apply (b : Unitization ℂ B) :
    unitalizedExtension J σ b = b.fst • (1 : K →L[ℂ] K) +
      isometricExtension J (σ b.snd) := by
  change algebraMap ℂ (K →L[ℂ] K) b.fst + isometricExtension J (σ b.snd) = _
  rw [Algebra.algebraMap_eq_smul_one]

theorem unitalizedExtension_commutes (R : K →L[ℂ] K)
    (hR : ∀ b, isometricExtension J (σ b) * R = R * isometricExtension J (σ b))
    (b : Unitization ℂ B) :
    unitalizedExtension J σ b * R = R * unitalizedExtension J σ b := by
  rw [unitalizedExtension_apply, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, one_mul, mul_one, hR]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CommonFiberRepresentations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Genuine representations of a norm-separable algebra on the fibers of
the common spectral model. The old unit supplies the projection onto the
fibers of the original Hilbert space. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {A B H : Type*} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [CStarAlgebra B] [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

/-- Every commuting norm-separable algebra has genuine unital fiber
representations after adjoining the ambient identity. -/
theorem exists_conull_common_representations
    (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hσ : ∀ b a, σ b * π a = π a * σ b) :
    ∃ s : Set (WeakDual.characterSpace ℂ A), MeasurableSet s ∧
      (cyclicCommonBaseMeasure π D) sᶜ = 0 ∧
      ∃ ρ : ∀ _x : s, Unitization ℂ B →⋆ₐ[ℂ]
          (ScalarHilbertCoordinates D.generators →L[ℂ] ScalarHilbertCoordinates D.generators),
        ∀ (b : B) (f : CommonCyclicHilbert π D),
          ∀ᵐ (x : s) ∂Measure.comap ((↑) : s → WeakDual.characterSpace ℂ A)
              (cyclicCommonBaseMeasure π D),
            isometricExtension (cyclicCommonEmbedding π D) (σ b) f x =
              ρ x (Unitization.inr b) (f x) := by
  let : TopologicalSpace.SeparableSpace (Unitization ℂ B) := separable_unitization
  obtain ⟨s, hsm, hsnull, ρ, haction, _⟩ :=
    exists_conull_diagonal_star_representations (cyclicCommonBaseMeasure π D)
      (unitalizedExtension (cyclicCommonEmbedding π D) σ) (by
        intro b r hr
        apply unitalizedExtension_commutes
        intro c
        exact commonExtension_commutes_localizations π D (σ c) (hσ c) r hr)
  refine ⟨s, hsm, hsnull, ρ, ?_⟩
  intro b f
  simpa only [unitalizedExtension_inr] using haction (Unitization.inr b) f

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CountablyGeneratedCStarAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.BoundedHochschild.WeakSubspace.preannihilator_closed_instance _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCStarQuotient.starSubalgebra_closed _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildCorners.corner_closed _root_.OAI.HochschildMatrixSystems.MatrixSystem.commutant_closed _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.canonicalGeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.cstarCornerSubalgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.separableReducingTestSpace_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerClosed _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.algebra_closed _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A separable C-star algebra generating a separably represented algebra

The complex linear span of the words in a countable family and its adjoints
is separable. Its norm closure is therefore a separable C-star algebra.
Applying this to the countable weakly dense contraction tests gives an
actual norm-separable C-star subalgebra whose bicommutant is the original
von Neumann algebra.
-/

noncomputable section
namespace KadisonSimilarity

open ContinuousLinearMapWOT
open scoped Topology Pointwise

variable {A : Type*} [CStarAlgebra A]

/-- Words in a countable generating set and its adjoints span a separable
complex star algebra. -/
theorem isSeparable_starAlgebra_adjoin {s : Set A} (hs : s.Countable) :
    TopologicalSpace.IsSeparable (StarAlgebra.adjoin ℂ s : Set A) := by
  have hstar : (star s).Countable := by
    rw [← Set.image_star]
    exact hs.image star
  have hunion := hs.union hstar
  let : Countable {x : A // x ∈ s ∪ star s} := hunion.to_subtype
  have hwords : (Submonoid.closure (s ∪ star s) : Set A).Countable := by
    rw [Submonoid.closure_eq_mrange, MonoidHom.coe_mrange]
    exact Set.countable_range _
  change TopologicalSpace.IsSeparable
    ((StarAlgebra.adjoin ℂ s).toSubalgebra.toSubmodule : Set A)
  rw [StarAlgebra.adjoin_eq_span]
  exact hwords.isSeparable.span

instance sequenceGeneratedCStarAlgebra_separable (g : ℕ → A) :
    TopologicalSpace.SeparableSpace (sequenceGeneratedCStarAlgebra g) := by
  apply TopologicalSpace.IsSeparable.separableSpace
  exact (isSeparable_starAlgebra_adjoin (Set.countable_range g)).closure

theorem mem_sequenceGeneratedCStarAlgebra (g : ℕ → A) (n : ℕ) :
    g n ∈ sequenceGeneratedCStarAlgebra g :=
  (StarSubalgebra.le_topologicalClosure _)
    (StarAlgebra.subset_adjoin ℂ (Set.range g) (Set.mem_range_self n))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A concrete von Neumann algebra contains the weak closure of any of its
subsets, proved directly from commutation with its commutant. -/
theorem mem_vonNeumannAlgebra_of_mem_weakClosure
    (P : VonNeumannAlgebra H) (S : Set (H →L[ℂ] H)) (hS : S ⊆ P)
    (T : H →L[ℂ] H) (hT : ofCLM T ∈ closure (ofCLM '' S)) : T ∈ P := by
  rw [← P.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro R hR
  have hc : IsClosed {X : H →WOT[ℂ] H | ofCLM R * X = X * ofCLM R} :=
    isClosed_eq (continuous_const_mul _) (continuous_mul_const _)
  have hs : ofCLM '' S ⊆ {X : H →WOT[ℂ] H | ofCLM R * X = X * ofCLM R} := by
    rintro _ ⟨X, hX, rfl⟩
    exact congrArg ofCLM ((VonNeumannAlgebra.mem_commutant_iff.mp hR) X (hS hX)).symm
  exact congrArg toCLM (closure_minimal hs hc hT)

/-- A norm-closed star subalgebra contained in `P`, containing a weakly dense
family of contractions, has bicommutant exactly `P`. -/
theorem representationVonNeumannAlgebra_subtype_eq_of_dense_tests
    (P : VonNeumannAlgebra H) (B : StarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (B : Set (H →L[ℂ] H))]
    (hB : B ≤ P.toStarSubalgebra) (g : ℕ → H →L[ℂ] H) (hg : ∀ n, g n ∈ B)
    (hdense : ∀ T : H →L[ℂ] H, T ∈ P → ‖T‖ ≤ 1 →
      ofCLM T ∈ closure (Set.range fun n => ofCLM (g n))) :
    representationVonNeumannAlgebra B.subtype = P := by
  let Q := representationVonNeumannAlgebra B.subtype
  apply VonNeumannAlgebra.ext
  intro T
  constructor
  · intro hT
    rw [← P.commutant_commutant]
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro R hR
    have hT' : T ∈ Set.centralizer (Set.centralizer
        (B.subtype.range : Set (H →L[ℂ] H))) := by
      simpa only [← SetLike.mem_coe, coe_representationVonNeumannAlgebra] using hT
    apply hT' R
    rintro _ ⟨b, rfl⟩
    exact (VonNeumannAlgebra.mem_commutant_iff.mp hR) b (hB b.property)
  · intro hT
    by_cases hz : T = 0
    · rw [hz, ← SetLike.mem_coe, coe_representationVonNeumannAlgebra]
      intro R _
      simp
    let c : ℂ := (‖T‖ : ℂ)⁻¹
    have hnorm : ‖c • T‖ ≤ 1 := by
      simp only [c, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg T), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz), le_refl]
    have hC : c • T ∈ Q := by
      apply mem_vonNeumannAlgebra_of_mem_weakClosure Q (Set.range g)
      · rintro _ ⟨n, rfl⟩
        exact mem_representationVonNeumannAlgebra B.subtype ⟨g n, hg n⟩
      · simpa only [Set.range_comp'] using
          hdense (c • T) (P.toStarSubalgebra.smul_mem hT c) hnorm
    have hback : (‖T‖ : ℂ) • (c • T) = T := by
      rw [smul_smul]
      simp only [c, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)),
        one_smul]
    rw [← hback]
    exact Q.toStarSubalgebra.smul_mem hC _

/-- Every concretely separably represented von Neumann algebra is the
bicommutant of an actual norm-separable unital C-star subalgebra. -/
theorem exists_separable_generating_cstar_subalgebra
    [TopologicalSpace.SeparableSpace H] (P : VonNeumannAlgebra H) :
    ∃ B : StarSubalgebra ℂ (H →L[ℂ] H),
      IsClosed (B : Set (H →L[ℂ] H)) ∧ TopologicalSpace.SeparableSpace B ∧
      B ≤ P.toStarSubalgebra ∧ (starSubalgebraCommutant B).commutant = P := by
  obtain ⟨test, _, hdense⟩ := exists_separable_contraction_tests P
  let g : ℕ → H →L[ℂ] H := fun n => test n
  let B := sequenceGeneratedCStarAlgebra g
  have hPclosed : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
    change IsClosed (P : Set (H →L[ℂ] H))
    rw [← P.centralizer_centralizer]
    exact Set.isClosed_centralizer _
  have hB : B ≤ P.toStarSubalgebra := by
    apply StarSubalgebra.topologicalClosure_minimal _ hPclosed
    apply StarAlgebra.adjoin_le
    rintro _ ⟨n, rfl⟩
    exact (test n).property
  refine ⟨B, inferInstance, inferInstance, hB, ?_⟩
  have hmain := representationVonNeumannAlgebra_subtype_eq_of_dense_tests P B hB g
    (mem_sequenceGeneratedCStarAlgebra g) hdense
  have hrange : B.subtype.range = B := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      exact b.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  simpa only [representationVonNeumannAlgebra, hrange] using hmain

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_JointCStarSource
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common separable source for an algebra and its commutant

Taking the norm closure of the joint star algebra preserves norm separability.
When the two sources generate `P` and `P'`, the common source generates the
commutant of the center. This puts both sources in one fiber representation.
-/

noncomputable section
namespace KadisonSimilarity

open scoped Topology

variable {A : Type*} [CStarAlgebra A]

theorem jointCStarSource_minimal (B C S : StarSubalgebra ℂ A)
    (hB : B ≤ S) (hC : C ≤ S) (hS : IsClosed (S : Set A)) :
    jointCStarSource B C ≤ S :=
  StarSubalgebra.topologicalClosure_minimal (sup_le hB hC) hS

/-- Countable dense subsets of the two algebras already generate their
joint norm closure. -/
theorem jointCStarSource_eq_dense_generators
    (B C : StarSubalgebra ℂ A)
    (b : ℕ → B) (hb : DenseRange b) (c : ℕ → C) (hc : DenseRange c) :
    jointCStarSource B C =
      (StarAlgebra.adjoin ℂ
        (Set.range (fun n => (b n : A)) ∪ Set.range (fun n => (c n : A)))).topologicalClosure := by
  let S := (StarAlgebra.adjoin ℂ
    (Set.range (fun n => (b n : A)) ∪ Set.range (fun n => (c n : A)))).topologicalClosure
  have hS : IsClosed (S : Set A) := StarSubalgebra.isClosed_topologicalClosure _
  have hbS : B ≤ S := by
    intro x hx
    exact hb.induction_on (p := fun y : B => (y : A) ∈ S)
      (⟨x, hx⟩ : B) (hS.preimage continuous_subtype_val) (fun n =>
      StarSubalgebra.le_topologicalClosure _
        (StarAlgebra.subset_adjoin ℂ _ (Or.inl (Set.mem_range_self n))))
  have hcS : C ≤ S := by
    intro x hx
    exact hc.induction_on (p := fun y : C => (y : A) ∈ S)
      (⟨x, hx⟩ : C) (hS.preimage continuous_subtype_val) (fun n =>
      StarSubalgebra.le_topologicalClosure _
        (StarAlgebra.subset_adjoin ℂ _ (Or.inr (Set.mem_range_self n))))
  apply le_antisymm (jointCStarSource_minimal B C S hbS hcS hS)
  apply StarSubalgebra.topologicalClosure_minimal _
    (StarSubalgebra.isClosed_topologicalClosure _)
  apply StarAlgebra.adjoin_le
  rintro x (⟨n, rfl⟩ | ⟨n, rfl⟩)
  · exact le_jointCStarSource_left B C (b n).property
  · exact le_jointCStarSource_right B C (c n).property

instance jointCStarSource_separable (B C : StarSubalgebra ℂ A)
    [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C] :
    TopologicalSpace.SeparableSpace (jointCStarSource B C) := by
  obtain ⟨b, hb⟩ := TopologicalSpace.exists_dense_seq B
  obtain ⟨c, hc⟩ := TopologicalSpace.exists_dense_seq C
  rw [jointCStarSource_eq_dense_generators B C b hb c hc]
  apply TopologicalSpace.IsSeparable.separableSpace
  exact (isSeparable_starAlgebra_adjoin
    ((Set.countable_range _).union (Set.countable_range _))).closure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem source_commutant_eq
    (B : StarSubalgebra ℂ (H →L[ℂ] H)) (P : VonNeumannAlgebra H)
    (hB : (starSubalgebraCommutant B).commutant = P) :
    starSubalgebraCommutant B = P.commutant := by
  have h := congrArg VonNeumannAlgebra.commutant hB
  simpa only [VonNeumannAlgebra.commutant_commutant] using h

/-- The joint source has exactly the original center as commutant. -/
theorem jointCStarSource_commutant
    (P : VonNeumannAlgebra H) (B C : StarSubalgebra ℂ (H →L[ℂ] H))
    (hB : B ≤ P.toStarSubalgebra) (hC : C ≤ P.commutant.toStarSubalgebra)
    (hBgen : (starSubalgebraCommutant B).commutant = P)
    (hCgen : (starSubalgebraCommutant C).commutant = P.commutant) :
    starSubalgebraCommutant (jointCStarSource B C) = vonNeumannCenter P := by
  have hB' := source_commutant_eq B P hBgen
  have hC' : starSubalgebraCommutant C = P := by
    simpa only [VonNeumannAlgebra.commutant_commutant] using
      source_commutant_eq C P.commutant hCgen
  have hclosed : IsClosed ((vonNeumannCenter P).commutant.toStarSubalgebra :
      Set (H →L[ℂ] H)) := by
    change IsClosed ((vonNeumannCenter P).commutant : Set (H →L[ℂ] H))
    rw [VonNeumannAlgebra.coe_commutant]
    exact Set.isClosed_centralizer _
  have hBcentral : B ≤ (vonNeumannCenter P).commutant.toStarSubalgebra :=
    hB.trans (le_center_commutant P)
  have hCcentral : C ≤ (vonNeumannCenter P).commutant.toStarSubalgebra := by
    intro x hx
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro z hz
    exact (VonNeumannAlgebra.mem_commutant_iff.mp (hC hx)) z hz.1
  have hS := jointCStarSource_minimal B C _ hBcentral hCcentral hclosed
  apply VonNeumannAlgebra.ext
  intro T
  constructor
  · intro hT
    have hcomm : ∀ x ∈ jointCStarSource B C, x * T = T * x := by
      simpa only [← SetLike.mem_coe, coe_starSubalgebraCommutant,
        Set.mem_centralizer_iff] using hT
    have hTB : T ∈ starSubalgebraCommutant B := by
      simpa only [← SetLike.mem_coe, coe_starSubalgebraCommutant,
        Set.mem_centralizer_iff] using
        (show ∀ x ∈ B, x * T = T * x from fun x hx =>
          hcomm x (le_jointCStarSource_left B C hx))
    have hTC : T ∈ starSubalgebraCommutant C := by
      simpa only [← SetLike.mem_coe, coe_starSubalgebraCommutant,
        Set.mem_centralizer_iff] using
        (show ∀ x ∈ C, x * T = T * x from fun x hx =>
          hcomm x (le_jointCStarSource_right B C hx))
    rw [hB'] at hTB
    rw [hC'] at hTC
    exact ⟨hTC, hTB⟩
  · intro hT
    rw [← SetLike.mem_coe, coe_starSubalgebraCommutant]
    intro x hx
    exact ((VonNeumannAlgebra.mem_commutant_iff.mp (hS hx)) T hT).symm

theorem jointCStarSource_bicommutant
    (P : VonNeumannAlgebra H) (B C : StarSubalgebra ℂ (H →L[ℂ] H))
    (hB : B ≤ P.toStarSubalgebra) (hC : C ≤ P.commutant.toStarSubalgebra)
    (hBgen : (starSubalgebraCommutant B).commutant = P)
    (hCgen : (starSubalgebraCommutant C).commutant = P.commutant) :
    (starSubalgebraCommutant (jointCStarSource B C)).commutant =
      (vonNeumannCenter P).commutant :=
  congrArg VonNeumannAlgebra.commutant (jointCStarSource_commutant P B C hB hC hBgen hCgen)

/-- Simultaneously choose weak generators for the algebra and commutant,
with a norm-separable common source generating the central commutant. -/
theorem exists_separable_joint_cstar_source [TopologicalSpace.SeparableSpace H]
    (P : VonNeumannAlgebra H) :
    ∃ B C : StarSubalgebra ℂ (H →L[ℂ] H),
      IsClosed (B : Set (H →L[ℂ] H)) ∧ IsClosed (C : Set (H →L[ℂ] H)) ∧
      TopologicalSpace.SeparableSpace B ∧ TopologicalSpace.SeparableSpace C ∧
      B ≤ P.toStarSubalgebra ∧ C ≤ P.commutant.toStarSubalgebra ∧
      (starSubalgebraCommutant B).commutant = P ∧
      (starSubalgebraCommutant C).commutant = P.commutant ∧
      (starSubalgebraCommutant (jointCStarSource B C)).commutant =
        (vonNeumannCenter P).commutant := by
  obtain ⟨B, hBclosed, hBsep, hB, hBgen⟩ := exists_separable_generating_cstar_subalgebra P
  obtain ⟨C, hCclosed, hCsep, hC, hCgen⟩ :=
    exists_separable_generating_cstar_subalgebra P.commutant
  exact ⟨B, C, hBclosed, hCclosed, hBsep, hCsep, hB, hC, hBgen, hCgen,
    jointCStarSource_bicommutant P B C hB hC hBgen hCgen⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_CentralCStarSource
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A norm-separable commutative C-star source for the center. Its commutant
is the full central commutant, so its common spectral fields apply to every
operator required by the central-decomposition estimate. -/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every star subalgebra of the center is commutative. -/
theorem central_subalgebra_isMulCommutative (P : VonNeumannAlgebra H)
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (hA : A ≤ (vonNeumannCenter P).toStarSubalgebra) :
    IsMulCommutative A := by
  apply IsMulCommutative.of_setLike_mul_comm
  intro x hx y hy
  exact (VonNeumannAlgebra.mem_commutant_iff.mp (hA hy).2) x (hA hx).1

/-- The source inclusion has exactly its original star subalgebra as range. -/
theorem subtype_star_range (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    A.subtype.range = A := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact a.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- A weakly generating central source has the full central commutant. -/
theorem central_source_commutant (P : VonNeumannAlgebra H)
    (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hgen : (starSubalgebraCommutant A).commutant = vonNeumannCenter P) :
    starSubalgebraCommutant A = (vonNeumannCenter P).commutant := by
  have h := congrArg VonNeumannAlgebra.commutant hgen
  simpa only [VonNeumannAlgebra.commutant_commutant] using h

/-- Choose only a norm-separable source; the center itself need not be
norm separable. -/
theorem exists_separable_central_source [TopologicalSpace.SeparableSpace H]
    (P : VonNeumannAlgebra H) :
    ∃ A : StarSubalgebra ℂ (H →L[ℂ] H),
      IsClosed (A : Set (H →L[ℂ] H)) ∧ TopologicalSpace.SeparableSpace A ∧
      IsMulCommutative A ∧ A ≤ (vonNeumannCenter P).toStarSubalgebra ∧
      starSubalgebraCommutant A = (vonNeumannCenter P).commutant := by
  obtain ⟨A, hclosed, hsep, hA, hgen⟩ :=
    exists_separable_generating_cstar_subalgebra (vonNeumannCenter P)
  exact ⟨A, hclosed, hsep, central_subalgebra_isMulCommutative P A hA, hA,
    central_source_commutant P A hgen⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SeparableModelConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The separable central model is constructed from the represented
algebra. All norm, density and factor-fiber properties are proved. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory
open scoped IsMulCommutative

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- Construct the central factor decomposition needed by the manuscript's
separable estimate, including possible zero fibers. -/
theorem exists_publishedSeparableModel (P : VonNeumannAlgebra H) :
    Nonempty (PublishedSeparableModel P) := by
  obtain ⟨A, hAclosed, hAsep, hAcomm, _hA, hcentral⟩ := exists_separable_central_source P
  let : IsClosed (A : Set (H →L[ℂ] H)) := hAclosed
  let : TopologicalSpace.SeparableSpace A := hAsep
  let : IsMulCommutative A := hAcomm
  let π := A.subtype
  let D := cyclicDecompositionData π.range
  let : MeasurableSpace (WeakDual.characterSpace ℂ A) := commonCyclicMeasurable
  let : BorelSpace (WeakDual.characterSpace ℂ A) := commonCyclicBorel
  let := commonCyclicCountable π D
  have hcentral' : starSubalgebraCommutant π.range = (vonNeumannCenter P).commutant := by
    simpa only [π, subtype_star_range] using hcentral
  obtain ⟨B, C, hBclosed, hCclosed, hBsep, hCsep, hB, hC, hBgen, _hCgen, hSgen⟩ :=
    exists_separable_joint_cstar_source P
  let : IsClosed (B : Set (H →L[ℂ] H)) := hBclosed
  let : IsClosed (C : Set (H →L[ℂ] H)) := hCclosed
  let : TopologicalSpace.SeparableSpace B := hBsep
  let : TopologicalSpace.SeparableSpace C := hCsep
  have hSgen' : representationVonNeumannAlgebra (jointCStarSource B C).subtype =
      starSubalgebraCommutant π.range := by
    rw [representationVonNeumannAlgebra, subtype_star_range, hSgen, hcentral']
  have hcomm (b : jointCStarSource B C) (a : A) :
      (b : H →L[ℂ] H) * π a = π a * b := by
    have hb : (b : H →L[ℂ] H) ∈ starSubalgebraCommutant π.range := by
      rw [← hSgen']
      exact mem_representationVonNeumannAlgebra (jointCStarSource B C).subtype b
    exact commutant_commutes_representation π ⟨b.val, hb⟩ a
  obtain ⟨s, hs, hnull, ρ, hρ⟩ := exists_conull_common_representations π D
    (jointCStarSource B C).subtype hcomm
  let φ := StarSubalgebra.inclusion (le_jointCStarSource_left B C)
  let ρB := fun x => unitizationRestrict φ (ρ x)
  have hρB (b : B) (f : CommonCyclicHilbert π D) :
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → WeakDual.characterSpace ℂ A)
        (cyclicCommonBaseMeasure π D),
        isometricExtension (cyclicCommonEmbedding π D) (b : H →L[ℂ] H) f x =
          ρB x (Unitization.inr b) (f x) := by
    have h := hρ (φ b) f
    change ∀ᵐ x : s ∂Measure.comap ((↑) : s → WeakDual.characterSpace ℂ A)
      (cyclicCommonBaseMeasure π D),
      isometricExtension (cyclicCommonEmbedding π D) (b : H →L[ℂ] H) f x =
        ρ x (Unitization.inr (φ b)) (f x) at h
    simpa only [ρB, unitizationRestrict_inr] using h
  have hBgen' : representationVonNeumannAlgebra B.subtype = P := by
    rw [representationVonNeumannAlgebra, subtype_star_range]
    exact hBgen
  let DC := commonProjectionCentralData π D P B hB hBgen' hcentral' s hs hnull ρB hρB
  have hBC (b : B) (c : C) :
      (b : H →L[ℂ] H) * (c : H →L[ℂ] H) =
        (c : H →L[ℂ] H) * (b : H →L[ℂ] H) :=
    (VonNeumannAlgebra.mem_commutant_iff.mp (hC c.property)) b (hB b.property)
  have hfactor := ae_common_fiber_scalar_center π D B C hBC hSgen' s hs hnull ρ hρ
  exact ⟨publishedSeparableModel_of_central_factors P (cyclicCommonBaseMeasure π D)
    (conullProjectionFiber s ρB) DC hfactor⟩

/-- Every separable represented von Neumann algebra admits the central
factor decomposition used in the uniform commutator estimate. -/
theorem publishedUniformInputs_oai : PublishedUniformInputs.{u} :=
  ⟨fun _ _ _ _ _ P => exists_publishedSeparableModel P⟩

end KadisonSimilarity

end

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonSimilarity.publishedUniformInputs_oai.{u} := @OAI.KadisonSimilarity.publishedUniformInputs_oai.{u}
