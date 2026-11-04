-- Prove2me | solution 1 for OAI.KadisonSimilarity.original_symmetry_bound_of_free_corner
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T15:06:56.429965+00:00
-- url     : https://prove2.me/submissions/01234449-efb0-46a4-8e8f-c022799f55f1

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A036
import Theorems.Thm_OAI_KadisonSimilarity_canonical_free_corner_bound

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialBaseSpace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The completed base Hilbert space of a represented tracial star algebra,
its actual inclusion, and compression of the ambient left action. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

theorem baseInclusion_intertwines (a : A) :
    (G.left (a : P)).comp (G.baseInclusion A).toContinuousLinearMap =
      (G.baseInclusion A).toContinuousLinearMap.comp (G.baseRepresentation A a) := rfl

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_BaseCommutatorCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compression of commutators with base-algebra elements needs no invariance
hypothesis on the other operator. This also restores the original operator
after the free-product symmetrization. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

/-- The adjoint base inclusion intertwines every base-algebra element. -/
theorem baseInclusion_adjoint_intertwines (a : A) :
    (G.baseInclusion A).toContinuousLinearMap.adjoint.comp (G.left (a : P)) =
      (G.baseRepresentation A a).comp (G.baseInclusion A).toContinuousLinearMap.adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint (G.baseInclusion_intertwines A (star a))
  have hleft : (G.left ((star a : A) : P)).adjoint = G.left (a : P) := by
    change (G.left (star (a : P))).adjoint = G.left (a : P)
    rw [map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_adjoint]
  have hbase : (G.baseRepresentation A (star a)).adjoint = G.baseRepresentation A a := by
    rw [map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_adjoint]
  simpa only [ContinuousLinearMap.adjoint_comp, hleft, hbase] using h


/-- Compression commutes with the commutator against a base element. -/
theorem baseOperator_commutator_subalgebra (Y : H →L[ℂ] H) (a : A) :
    G.baseOperator A (commutator Y (G.left (a : P))) =
      commutator (G.baseOperator A Y) (G.baseRepresentation A a) := by
  unfold baseOperator commutator
  simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
  rw [G.baseInclusion_intertwines A a]
  simp only [← ContinuousLinearMap.comp_assoc]
  rw [G.baseInclusion_adjoint_intertwines A a]

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.NuclearUltrapower_HilbertUltraproduct
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
universe u v w
open Filter
open scoped Topology InnerProductSpace ENNReal

namespace NuclearUltrapower

namespace HilbertUltraproduct
variable {ι : Type u} {E : ι → Type v} {F : ι → Type w}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]
    (ω : Ultrafilter ι)

theorem map_norm_le (T : lp (fun i => E i →L[ℂ] F i) ∞) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ᶠ i in (ω : Filter ι), ‖T i‖ ≤ C) : ‖map ω T‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih x =>
    simpa only [map_coe, UniformSpace.Completion.norm_coe] using
      UltraPreHilbert.mapLinear_norm_le ω T C hT x

end HilbertUltraproduct

end NuclearUltrapower

end
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_UltrapowerCommutators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.vonNeumannInnerDerivation_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinatewise commutator estimates pass to the Hilbert ultrapower,
and then to any reducing closed subspace. -/

noncomputable section
namespace KadisonSimilarity

open NuclearUltrapower
open scoped ENNReal

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual operator map on the Hilbert ultrapower respects commutators. -/
theorem hilbertUltraproduct_commutator (ω : Ultrafilter ι)
    (T X : lp (fun _ : ι => H →L[ℂ] H) ∞) :
    commutator (HilbertUltraproduct.map ω T) (HilbertUltraproduct.map ω X) =
      HilbertUltraproduct.map ω (T * X - X * T) := by
  change commutator (HilbertUltraproduct.operatorRep ω T)
    (HilbertUltraproduct.operatorRep ω X) =
      HilbertUltraproduct.operatorRep ω (T * X - X * T)
  simp only [commutator, map_sub, map_mul]

/-- Only an eventual coordinate bound is required, exactly as in the
small-corner lifting argument. -/
theorem norm_hilbertUltraproduct_commutator_le (ω : Ultrafilter ι)
    (T X : lp (fun _ : ι => H →L[ℂ] H) ∞) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ᶠ i in (ω : Filter ι), ‖commutator (T i) (X i)‖ ≤ c) :
    ‖commutator (HilbertUltraproduct.map ω T) (HilbertUltraproduct.map ω X)‖ ≤ c := by
  rw [hilbertUltraproduct_commutator]
  apply HilbertUltraproduct.map_norm_le ω _ c hc
  exact hbound

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Compression to a reducing subspace preserves a commutator estimate.
The operator being tested need not preserve that subspace. -/
theorem norm_reducing_compression_commutator_le (V : K →ₗᵢ[ℂ] H)
    (T X : H →L[ℂ] H) (X₀ : K →L[ℂ] K)
    (hXV : X.comp V.toContinuousLinearMap = V.toContinuousLinearMap.comp X₀)
    (hXVstar : X.adjoint.comp V.toContinuousLinearMap =
      V.toContinuousLinearMap.comp X₀.adjoint)
    {c : ℝ} (hbound : ‖commutator T X‖ ≤ c) :
    ‖commutator (V.toContinuousLinearMap.adjoint.comp (T.comp V.toContinuousLinearMap)) X₀‖
      ≤ c := by
  have hAdj : V.toContinuousLinearMap.adjoint.comp X =
      X₀.comp V.toContinuousLinearMap.adjoint := by
    have h := congrArg ContinuousLinearMap.adjoint hXVstar
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint] using h
  have heq : commutator
      (V.toContinuousLinearMap.adjoint.comp (T.comp V.toContinuousLinearMap)) X₀ =
      V.toContinuousLinearMap.adjoint.comp ((commutator T X).comp V.toContinuousLinearMap) := by
    symm
    simp only [commutator, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_assoc]
    rw [hXV]
    simp only [← ContinuousLinearMap.comp_assoc]
    rw [hAdj]
  rw [heq]
  calc
    ‖V.toContinuousLinearMap.adjoint.comp ((commutator T X).comp V.toContinuousLinearMap)‖
        ≤ ‖V.toContinuousLinearMap.adjoint‖ *
          (‖commutator T X‖ * ‖V.toContinuousLinearMap‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖commutator T X‖ * 1) := by
      apply mul_le_mul
      · simpa only [ContinuousLinearMap.adjoint.norm_map] using V.norm_toContinuousLinearMap_le
      · exact mul_le_mul_of_nonneg_left V.norm_toContinuousLinearMap_le (norm_nonneg _)
      · positivity
      · norm_num
    _ ≤ c := by simpa only [one_mul, mul_one] using hbound

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_UltrapowerConstants
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constant Hilbert vectors retain both their norm and the action of every
constant bounded operator inside the actual Hilbert ultrapower. -/

noncomputable section
namespace KadisonSimilarity

open NuclearUltrapower
open scoped ENNReal Topology

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The coordinatewise action of a fixed operator preserves the constant subspace. -/
theorem map_constant_operator (ω : Ultrafilter ι) (T : H →L[ℂ] H) (x : H) :
    HilbertUltraproduct.map ω (boundedConstant T) (constantHilbertInclusion ω x) =
      constantHilbertInclusion ω (T x) := by
  rw [constantHilbertInclusion_apply, HilbertUltraproduct.map_coe,
    constantHilbertInclusion_apply]
  congr 1

/-- Compressing the ultrapower operator back to the constant subspace
recovers the original operator exactly. -/
theorem compression_map_constant_operator (ω : Ultrafilter ι) (T : H →L[ℂ] H) :
    (constantHilbertInclusion (H := H) ω).toContinuousLinearMap.adjoint.comp
      ((HilbertUltraproduct.map ω (boundedConstant T)).comp
        (constantHilbertInclusion ω).toContinuousLinearMap) = T := by
  ext x
  change (constantHilbertInclusion ω).toContinuousLinearMap.adjoint
    (HilbertUltraproduct.map ω (boundedConstant T) (constantHilbertInclusion ω x)) = T x
  rw [map_constant_operator]
  exact congrArg (fun L : H →L[ℂ] H => L (T x))
    (constantHilbertInclusion ω).adjoint_comp_self

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialUltrapowerActions
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.HochschildUltrapower.quotientUnitary_coe _root_.OAI.KadisonSimilarity.grothendieckFamilyLinear_apply _root_.OAI.KadisonSimilarity.grothendieckFamilyMap_apply _root_.OAI.KadisonSimilarity.tracialUltrapowerMap_mk _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded left-multiplier sequences reduce the tracial GNS subspace of
the Hilbert ultrapower. The compressed operator therefore inherits every
eventual coordinate commutator estimate. -/

noncomputable section
namespace KadisonSimilarity

open NuclearUltrapower HochschildUltrapower
open scoped ENNReal Topology BoundedContinuousFunction ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a * b) = τ (b * a))

theorem gnsLeftSequence_vector (x y : ℕ →ᵇ A) :
    HilbertUltraproduct.map ω (gnsLeftSequence τ x)
      (algebraSequenceVectorLinear τ h1 ω y) =
      algebraSequenceVectorLinear τ h1 ω (x * y) := by
  change HilbertUltraproduct.map ω (gnsLeftSequence τ x)
    (algebraSequenceVector τ h1 ω y : HilbertUltraproduct (fun _ : ℕ => τ.GNS) ω) = _
  rw [HilbertUltraproduct.map_coe]
  congr 1
  apply Subtype.ext
  funext i
  change τ.gnsStarAlgHom (x i) (τ.toPreGNS (y i) : τ.GNS) =
    (τ.toPreGNS (x i * y i) : τ.GNS)
  simp [PositiveLinearMap.gnsStarAlgHom]

/-- The inclusion intertwines the quotient's left action and the coordinate action. -/
theorem tracialUltrapowerGNSInclusion_intertwines (x : ℕ →ᵇ A) :
    (HilbertUltraproduct.map ω (gnsLeftSequence τ x)).comp
      (tracialUltrapowerGNSInclusion τ h1 ω htr).toContinuousLinearMap =
    (tracialUltrapowerGNSInclusion τ h1 ω htr).toContinuousLinearMap.comp
      ((quotientTrace τ h1 ω htr).gnsStarAlgHom (quotientHom τ h1 ω htr x)) := by
  ext v
  induction v using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih v =>
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective
      ((quotientTrace τ h1 ω htr).ofPreGNS v)
    have hv : v = (quotientTrace τ h1 ω htr).toPreGNS
        (quotientHom τ h1 ω htr y) := by
      apply (quotientTrace τ h1 ω htr).ofPreGNS.injective
      exact hy.symm
    rw [hv]
    simpa [PositiveLinearMap.gnsStarAlgHom, ← map_mul] using
      gnsLeftSequence_vector τ h1 ω x y

/-- Eventual coordinate bounds survive the two constructions exactly. -/
theorem norm_tracialUltrapowerCompression_commutator_le
    (T : τ.GNS →L[ℂ] τ.GNS) (x : ℕ →ᵇ A) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ᶠ i in (ω : Filter ℕ), ‖commutator T (τ.gnsStarAlgHom (x i))‖ ≤ c) :
    ‖commutator (tracialUltrapowerCompression τ h1 ω htr T)
      ((quotientTrace τ h1 ω htr).gnsStarAlgHom (quotientHom τ h1 ω htr x))‖ ≤ c := by
  apply norm_reducing_compression_commutator_le
    (tracialUltrapowerGNSInclusion τ h1 ω htr)
    (HilbertUltraproduct.map ω (boundedConstant T))
    (HilbertUltraproduct.map ω (gnsLeftSequence τ x))
  · exact tracialUltrapowerGNSInclusion_intertwines τ h1 ω htr x
  · simpa only [← ContinuousLinearMap.star_eq_adjoint, gnsLeftSequence_star,
      HilbertUltraproduct.map_star, map_star] using
      tracialUltrapowerGNSInclusion_intertwines τ h1 ω htr (star x)
  · exact norm_hilbertUltraproduct_commutator_le ω _ _ hc hbound

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialUltrapowerConstants
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both ultrapower constructions preserve the original constant Hilbert
space exactly. Compression back to that space recovers the original operator. -/

noncomputable section
namespace KadisonSimilarity

open HochschildUltrapower NuclearUltrapower
open scoped ComplexOrder Topology BoundedContinuousFunction

theorem compression_through_composite
    {E F K : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (V : F →L[ℂ] K) (J : E →L[ℂ] F) (T : K →L[ℂ] K) :
    J.adjoint.comp ((V.adjoint.comp (T.comp V)).comp J) =
      (V.comp J).adjoint.comp (T.comp (V.comp J)) := by
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a * b) = τ (b * a))

/-- Going through the tracial quotient agrees with the constant Hilbert
ultrapower inclusion on the entire completed Hilbert space. -/
theorem tracialUltrapower_constant_inclusion :
    (tracialUltrapowerGNSInclusion τ h1 ω htr).toContinuousLinearMap.comp
      (constantTracialGNSInclusion τ h1 ω htr).toContinuousLinearMap =
      (constantHilbertInclusion (H := τ.GNS) ω).toContinuousLinearMap := by
  ext ξ
  refine (gnsTracialVector_dense τ).induction_on ξ
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  change tracialUltrapowerGNSInclusion τ h1 ω htr
    (gnsTracialHomIsometry τ (quotientTrace τ h1 ω htr) (constant τ h1 ω htr)
      (quotientTrace_constant τ h1 ω htr) (gnsTracialVector τ a)) = _
  rw [gnsTracialHomIsometry_vector]
  change tracialUltrapowerGNSInclusion τ h1 ω htr
    ((quotientTrace τ h1 ω htr).toPreGNS
      (quotientHom τ h1 ω htr (constantSequence a))) = _
  rw [tracialUltrapowerGNSInclusion_mk]
  change algebraSequenceVectorLinear τ h1 ω (constantSequence a) =
    constantHilbertInclusion ω (gnsTracialVector τ a)
  rw [constantHilbertInclusion_apply]
  change (algebraSequenceVector τ h1 ω (constantSequence a) :
    HilbertUltraproduct (fun _ : ℕ => τ.GNS) ω) =
    (constantPreHilbert ω (gnsTracialVector τ a) :
      HilbertUltraproduct (fun _ : ℕ => τ.GNS) ω)
  congr 1

/-- The compressed ultrapower operator agrees with the original operator
after compression to the constant tracial subspace. -/
theorem constant_compression_tracialUltrapower (T : τ.GNS →L[ℂ] τ.GNS) :
    (constantTracialGNSInclusion τ h1 ω htr).toContinuousLinearMap.adjoint.comp
      ((tracialUltrapowerCompression τ h1 ω htr T).comp
        (constantTracialGNSInclusion τ h1 ω htr).toContinuousLinearMap) = T := by
  let V := (tracialUltrapowerGNSInclusion τ h1 ω htr).toContinuousLinearMap
  let J := (constantTracialGNSInclusion τ h1 ω htr).toContinuousLinearMap
  let C := (constantHilbertInclusion (H := τ.GNS) ω).toContinuousLinearMap
  have hVJ : V.comp J = C := tracialUltrapower_constant_inclusion τ h1 ω htr
  change J.adjoint.comp ((V.adjoint.comp
    ((HilbertUltraproduct.map ω (boundedConstant T)).comp V)).comp J) = T
  rw [compression_through_composite, hVJ]
  exact compression_map_constant_operator ω T

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialHomCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact recovery of a commutator through trace-preserving embeddings.
This is the final direction of the ultrapower transfer: a bound on the
constant subalgebra's compressed commutator bounds the original operator. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)

local notation "G" => gnsTracialGeometry τB trB
local notation "V" => TracialCornerGeometry.baseInclusion (gnsTracialGeometry τB trB) φ.range

local notation "U" => tracialRangeIsometry τA (gnsTracialGeometry τB trB) φ
  (gnsGeometry_preserves_trace τA τB trB φ hφ)
local notation "J" => gnsTracialHomIsometry τA τB φ hφ

/-- Factoring the GNS embedding through the completed range is exact. -/
theorem tracialRangeIsometry_inclusion :
    (V).toContinuousLinearMap.comp (U).toContinuousLinearMap = (J).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro ξ
  refine (gnsTracialVector_dense τA).induction_on ξ
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  change V (U (gnsTracialVector τA a)) = J (gnsTracialVector τA a)
  rw [tracialRangeIsometry_vector, gnsTracialHomIsometry_vector]
  rfl

/-- The range-space isometry intertwines the actual left representations. -/
theorem tracialRangeIsometry_left (a : A) :
    ((G).baseRepresentation φ.range (φ.rangeRestrict a)).comp (U).toContinuousLinearMap =
      (U).toContinuousLinearMap.comp (τA.gnsStarAlgHom a) := by
  apply ContinuousLinearMap.ext
  intro ξ
  refine (gnsTracialVector_dense τA).induction_on ξ
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  change (G).baseRepresentation φ.range (φ.rangeRestrict a) (U (gnsTracialVector τA b)) =
    U (τA.gnsStarAlgHom a (gnsTracialVector τA b))
  rw [gnsTracialVector_left, tracialRangeIsometry_vector, tracialRangeIsometry_vector]
  apply Subtype.ext
  change (G).left (φ a) ((G).vector (φ b)) = (G).vector (φ (a * b))
  rw [(G).left_vector, map_mul φ a b]

/-- No norm is lost when using a bound on the compressed constant algebra
to recover the original commutator. Only compression equality is needed. -/
theorem norm_commutator_le_tracial_range_compression
    (T : τA.GNS →L[ℂ] τA.GNS) (S : τB.GNS →L[ℂ] τB.GNS)
    (hT : (J).toContinuousLinearMap.adjoint.comp (S.comp (J).toContinuousLinearMap) = T)
    (a : A) :
    ‖commutator T (τA.gnsStarAlgHom a)‖ ≤
      ‖(G).baseOperator φ.range (commutator S (τB.gnsStarAlgHom (φ a)))‖ := by
  have hc : (U).toContinuousLinearMap.adjoint.comp
      (((G).baseOperator φ.range S).comp (U).toContinuousLinearMap) = T := by
    change (U).toContinuousLinearMap.adjoint.comp
      (((V).toContinuousLinearMap.adjoint.comp (S.comp (V).toContinuousLinearMap)).comp
        (U).toContinuousLinearMap) = T
    rw [compression_through_composite, tracialRangeIsometry_inclusion τA τB trB φ hφ, hT]
  have hb := norm_reducing_compression_commutator_le U ((G).baseOperator φ.range S)
    ((G).baseRepresentation φ.range (φ.rangeRestrict a)) (τA.gnsStarAlgHom a)
    (tracialRangeIsometry_left τA τB trB φ hφ a) (by
      simpa only [map_star, ContinuousLinearMap.star_eq_adjoint] using
        tracialRangeIsometry_left τA τB trB φ hφ (star a))
    (le_refl ‖commutator ((G).baseOperator φ.range S)
      ((G).baseRepresentation φ.range (φ.rangeRestrict a))‖)
  rw [hc] at hb
  rwa [← (G).baseOperator_commutator_subalgebra φ.range S (φ.rangeRestrict a)] at hb

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialSubalgebraModels
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal algebra generated inside the ultrapower is represented on
its own tracial GNS space. Restriction of the positive trace and its exact
Hilbert-space identification require no further analytic input. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {P : Type*} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P]
  (τ : P →ₚ[ℂ] ℂ) (L : StarSubalgebra ℂ P) [IsClosed (L : Set P)]

/-- Its range is exactly the completed algebra-vector subspace. -/
theorem restrictedTracialGNSInclusion_range
    (htr : ∀ a b : P, τ (a * b) = τ (b * a)) :
    Set.range (restrictedTracialGNSInclusion τ L) =
      ((gnsTracialGeometry τ htr).baseSpace L : Set τ.GNS) := by
  let J := restrictedTracialGNSInclusion τ L
  have hc : IsClosed (Set.range J) := J.isometry.isClosedEmbedding.isClosed_range
  apply Set.Subset.antisymm
  · rintro _ ⟨ξ, rfl⟩
    refine (gnsTracialVector_dense (restrictedPositiveTrace τ L)).induction_on ξ
      (((gnsTracialGeometry τ htr).baseSpace L).isClosed.preimage J.continuous) ?_
    intro a
    rw [restrictedTracialGNSInclusion_vector]
    exact ((gnsTracialGeometry τ htr).baseVector L a).property
  · change closure (Set.range ((gnsTracialGeometry τ htr).baseAlgebraVectors L)) ⊆ _
    apply closure_minimal _ hc
    rintro _ ⟨a, rfl⟩
    exact ⟨gnsTracialVector (restrictedPositiveTrace τ L) a,
      restrictedTracialGNSInclusion_vector τ L a⟩

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialL2Closure
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded elements in the L² closure of a star subalgebra form an
actual norm-closed star subalgebra. Multiplication is obtained from the
commuting left and right tracial actions, rather than assumed as a property
of a proposed generated algebra. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

open scoped CStarAlgebra ComplexOrder

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

/-- Inclusion of algebras induces inclusion of their closed Hilbert spans. -/
theorem baseSpace_mono {S T : StarSubalgebra ℂ P} (hST : S ≤ T) :
    G.baseSpace S ≤ G.baseSpace T := by
  change closure (Set.range (G.baseAlgebraVectors S)) ⊆
    closure (Set.range (G.baseAlgebraVectors T))
  apply closure_mono
  rintro x ⟨a, rfl⟩
  exact ⟨⟨(a : P), hST a.property⟩, rfl⟩

/-- Taking the norm closure of the algebra does not change its L² span. -/
theorem baseSpace_topologicalClosure (S : StarSubalgebra ℂ P) :
    G.baseSpace S.topologicalClosure = G.baseSpace S := by
  apply le_antisymm
  · change closure (Set.range (G.baseAlgebraVectors S.topologicalClosure)) ⊆
      (G.baseSpace S : Set H)
    apply closure_minimal _ (G.baseSpace S).isClosed
    rintro x ⟨a, rfl⟩
    have hc : closure (S : Set P) ⊆ G.vector ⁻¹' (G.baseSpace S : Set H) := by
      apply closure_minimal _ ((G.baseSpace S).isClosed.preimage G.vector_continuous)
      intro b hb
      exact (G.baseVector S ⟨b, hb⟩).property
    exact hc a.property
  · exact G.baseSpace_mono S.le_topologicalClosure

section ClosedSeed

variable (S : StarSubalgebra ℂ P) [hSclosed : IsClosed (S : Set P)]

/-- Passing to the constructed bounded algebra leaves the Hilbert space
unchanged. -/
theorem baseSpace_l2ClosureAlgebra : G.baseSpace (G.l2ClosureAlgebra S) = G.baseSpace S := by
  apply le_antisymm
  · change closure (Set.range (G.baseAlgebraVectors (G.l2ClosureAlgebra S))) ⊆
      (G.baseSpace S : Set H)
    apply closure_minimal _ (G.baseSpace S).isClosed
    rintro x ⟨a, rfl⟩
    exact a.property
  · exact G.baseSpace_mono (G.le_l2ClosureAlgebra S)

end ClosedSeed

/-- The generated algebra has precisely the original seed's Hilbert span. -/
theorem baseSpace_l2GeneratedAlgebra (S : StarSubalgebra ℂ P) :
    G.baseSpace (G.l2GeneratedAlgebra S) = G.baseSpace S := by
  have : IsClosed (S.topologicalClosure : Set P) := S.isClosed_topologicalClosure
  exact (G.baseSpace_l2ClosureAlgebra S.topologicalClosure).trans
    (G.baseSpace_topologicalClosure S)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialSmallCornerTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A small-corner commutator estimate transports along a partial isometry
in the algebra commuting with the implementing operator. Projection
comparison then supplies that partial isometry in the prescribed factor. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

/-- A partial isometry is contractive, including when its initial projection
is zero. -/
theorem norm_le_one_of_initial_projection (v f : P) (hf : IsStarProjection f)
    (hv : star v * v = f) : ‖v‖ ≤ 1 := by
  have hfn : ‖f‖ * ‖f‖ = ‖f‖ := by
    rw [← CStarRing.norm_star_mul_self, hf.isSelfAdjoint.star_eq, hf.isIdempotentElem.eq]
  have hfn' : ‖f‖ ≤ 1 := by nlinarith [norm_nonneg f]
  have hvn : ‖v‖ * ‖v‖ = ‖f‖ := by rw [← CStarRing.norm_star_mul_self, hv]
  nlinarith [norm_nonneg v]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialProjectionLifting
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.HochschildUltrapower.quotientUnitary_coe _root_.OAI.KadisonSimilarity.tracialUltrapowerMap_mk _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projection lifting in a tracial ultrapower, using only the scalar
spectral rounding estimate. The subsequent trace cutoff uses the strict
gap between the desired trace and the coordinate trace bound. -/

noncomputable section
namespace KadisonSimilarity

open HochschildUltrapower TracialUltrapower Filter
open scoped ComplexOrder Topology BoundedContinuousFunction

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a * b) = τ (b * a))

omit h1 ω htr [PartialOrder A] [StarOrderedRing A] in
theorem norm_le_one_of_star_projection (p : A) (hp : IsStarProjection p) : ‖p‖ ≤ 1 :=
  norm_le_one_of_initial_projection p p hp (by
    rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq])

/-- Every quotient projection has a representative consisting of actual
projections. Rounding is the sole spectral-calculus prerequisite. -/
theorem exists_projection_representative (rounding : SpectralProjectionRoundingInput τ)
    (e : Ultrapower τ h1 ω htr) (he : IsStarProjection e) :
    ∃ p : ℕ →ᵇ A, (∀ i, IsStarProjection (p i)) ∧ quotientHom τ h1 ω htr p = e := by
  classical
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective e
  let b : ℕ →ᵇ A := (1 / 2 : ℂ) • (a + star a)
  have hb : ∀ i, IsSelfAdjoint (b i) := by
    intro i
    change star (b i) = b i
    simp [b, star_smul, star_add, add_comm]
  have hbe : quotientHom τ h1 ω htr b = e := by
    change quotientHom τ h1 ω htr ((1 / 2 : ℂ) • (a + star a)) = e
    have ha' : quotientHom τ h1 ω htr a = e := ha
    simp only [map_smul, map_add, map_star, ha', he.isSelfAdjoint.star_eq]
    module
  choose p hp hpa using fun i => rounding (b i) (hb i)
  let p' : ℕ →ᵇ A := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete p 1
    (fun i => norm_le_one_of_star_projection (p i) (hp i))
  have hdefect : Tendsto (fun i => ‖τ.toPreGNS ((b i) * (b i) - b i)‖)
      (ω : Filter ℕ) (𝓝 0) := by
    have hzero : quotientHom τ h1 ω htr (b * b - b) = 0 := by
      rw [map_sub, map_mul, hbe, he.isIdempotentElem.eq, sub_self]
    have hmem : b * b - b ∈ ideal τ h1 ω htr :=
      (Ideal.Quotient.eq_zero_iff_mem).mp hzero
    exact (mem_nullSubmodule _ _ _).mp hmem
  have hnull : p' - b ∈ ideal τ h1 ω htr := by
    apply (mem_nullSubmodule _ _ _).mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun i => hpa i)
    simpa using hdefect.const_mul 2
  refine ⟨p', hp, ?_⟩
  have hzero : quotientHom τ h1 ω htr (p' - b) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr hnull
  rw [map_sub, hbe, sub_eq_zero] at hzero
  exact hzero

/-- A strict trace gap permits uniform coordinate bounds after changing a
representative on a set outside the ultrafilter. -/
theorem exists_projection_representative_trace_le
    (rounding : SpectralProjectionRoundingInput τ)
    (e : Ultrapower τ h1 ω htr) (he : IsStarProjection e)
    {s : ℝ} (hs : (quotientTrace τ h1 ω htr e).re < s) :
    ∃ p : ℕ →ᵇ A, (∀ i, IsStarProjection (p i)) ∧
      (∀ i, (τ (p i)).re ≤ s) ∧ quotientHom τ h1 ω htr p = e := by
  classical
  obtain ⟨p, hp, hpe⟩ := exists_projection_representative τ h1 ω htr rounding e he
  have ht : Tendsto (fun i => (τ (p i)).re) (ω : Filter ℕ)
      (𝓝 (quotientTrace τ h1 ω htr e).re) := by
    have h := (Complex.continuous_re.tendsto _).comp (tendsto_sequenceTrace τ h1 ω p)
    rw [← hpe]
    exact h
  have hgood : ∀ᶠ i in (ω : Filter ℕ), (τ (p i)).re ≤ s :=
    (ht.eventually_lt_const hs).mono (fun _ hi => hi.le)
  have hs0 : 0 ≤ s := by
    have hepos : 0 ≤ quotientTrace τ h1 ω htr e :=
      (quotientTrace τ h1 ω htr).map_nonneg he.nonneg
    exact (show 0 ≤ (quotientTrace τ h1 ω htr e).re from hepos.1).trans hs.le
  let q : ℕ →ᵇ A := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun i => if (τ (p i)).re ≤ s then p i else 0) 1 (by
      intro i
      split_ifs
      · exact norm_le_one_of_star_projection (p i) (hp i)
      · simp)
  have heq : ∀ᶠ i in (ω : Filter ℕ), q i = p i := by
    filter_upwards [hgood] with i hi
    change (if (τ (p i)).re ≤ s then p i else 0) = p i
    simp only [hi, ↓reduceIte]
  refine ⟨q, ?_, ?_, ?_⟩
  · intro i
    change IsStarProjection (if (τ (p i)).re ≤ s then p i else 0)
    split_ifs
    · exact hp i
    · exact IsStarProjection.zero A
  · intro i
    change (τ (if (τ (p i)).re ≤ s then p i else 0)).re ≤ s
    split_ifs with hi
    · exact hi
    · simpa using hs0
  · have hnull : q - p ∈ ideal τ h1 ω htr := by
      apply (mem_nullSubmodule _ _ _).mpr
      apply tendsto_const_nhds.congr'
      filter_upwards [heq] with i hi
      simp only [BoundedContinuousFunction.sub_apply, hi, sub_self, map_zero, norm_zero]
    have hzero : quotientHom τ h1 ω htr (q - p) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr hnull
    rwa [map_sub, hpe, sub_eq_zero] at hzero

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_NormalTracialExpectations
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace-preserving expectations on the actual normal subalgebras of a
faithful tracial geometry, including its constructed L²-generated algebras. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
namespace TracialCornerGeometry

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry A H)

theorem tracialExpectation_of_normal_range
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (M : VonNeumannAlgebra H) (hrange : G.left.range = M.toStarSubalgebra)
    (S : StarSubalgebra ℂ A) (N : VonNeumannAlgebra H)
    (hSrange : S.map G.left = N.toStarSubalgebra) :
    Nonempty (TracialExpectation G.trace S) := by
  let e := equivalenceOfConcreteRange M G.left (G.left_injective hf) hrange
  let τ := G.normalTracialRepresentation h1 hf M hrange
  have hNM : N ≤ M := by
    intro T hT
    change T ∈ M.toStarSubalgebra
    rw [← hrange]
    change T ∈ N.toStarSubalgebra at hT
    rw [← hSrange] at hT
    obtain ⟨a, _, rfl⟩ := hT
    exact ⟨a, rfl⟩
  have he : (insideAlgebra (M := M) (P := N)).comap e.toStarAlgHom = S := by
    ext a
    change G.left a ∈ N.toStarSubalgebra ↔ a ∈ S
    rw [← hSrange]
    constructor
    · rintro ⟨b, hb, heq⟩
      exact (G.left_injective hf heq) ▸ hb
    · intro ha
      exact ⟨a, ha, rfl⟩
  have E := (concreteTracialExpectation τ hNM).comapEquiv e
    (fun a => G.normalTracialRepresentation_trace h1 hf M hrange a)
  rw [he] at E
  exact ⟨E⟩

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_GeneratedGNSRecovery
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recovery through an intermediate generated algebra. The free-corner
argument is carried out on that algebra's own GNS space; its compression
still recovers the original operator with no change in the bound. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A P : Type*} [CStarAlgebra A] [CStarAlgebra P]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder P] [StarOrderedRing P]
  (τA : A →ₚ[ℂ] ℂ) (τP : P →ₚ[ℂ] ℂ)
  (L : StarSubalgebra ℂ P) [IsClosed (L : Set P)]
  (φ : A →⋆ₐ[ℂ] P) (hmem : ∀ a, φ a ∈ L) (hφ : ∀ a, τP (φ a) = τA a)

/-- The intermediate GNS embedding followed by its inclusion is the
original GNS embedding, on all completed vectors. -/
theorem generatedGNSInclusion_comp :
    (restrictedTracialGNSInclusion τP L).toContinuousLinearMap.comp
      (generatedGNSInclusion τA τP L φ hmem hφ).toContinuousLinearMap =
    (gnsTracialHomIsometry τA τP φ hφ).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro ξ
  refine (gnsTracialVector_dense τA).induction_on ξ
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  change restrictedTracialGNSInclusion τP L
    (generatedGNSInclusion τA τP L φ hmem hφ (gnsTracialVector τA a)) =
    gnsTracialHomIsometry τA τP φ hφ (gnsTracialVector τA a)
  rw [generatedGNSInclusion_vector, restrictedTracialGNSInclusion_vector,
    gnsTracialHomIsometry_vector]
  rfl

/-- The original compression identity survives insertion of the generated
algebra between the two Hilbert spaces. -/
theorem generatedGNSCompression_recover
    (T : τA.GNS →L[ℂ] τA.GNS) (S : τP.GNS →L[ℂ] τP.GNS)
    (hT : (gnsTracialHomIsometry τA τP φ hφ).toContinuousLinearMap.adjoint.comp
      (S.comp (gnsTracialHomIsometry τA τP φ hφ).toContinuousLinearMap) = T) :
    (generatedGNSInclusion τA τP L φ hmem hφ).toContinuousLinearMap.adjoint.comp
      ((generatedGNSCompression τP L S).comp
        (generatedGNSInclusion τA τP L φ hmem hφ).toContinuousLinearMap) = T := by
  unfold generatedGNSCompression
  rw [compression_through_composite, generatedGNSInclusion_comp τA τP L φ hmem hφ, hT]

/-- A free-corner bound on the intermediate algebra bounds the original
commutator, using the same constant. -/
theorem norm_commutator_le_generated_GNS_compression
    (trP : ∀ a b : P, τP (a * b) = τP (b * a))
    (T : τA.GNS →L[ℂ] τA.GNS) (S : τP.GNS →L[ℂ] τP.GNS)
    (hT : (gnsTracialHomIsometry τA τP φ hφ).toContinuousLinearMap.adjoint.comp
      (S.comp (gnsTracialHomIsometry τA τP φ hφ).toContinuousLinearMap) = T)
    (a : A) :
    ‖commutator T (τA.gnsStarAlgHom a)‖ ≤
      ‖(gnsTracialGeometry (restrictedPositiveTrace τP L)
          (restrictedPositiveTrace_tracial τP L trP)).baseOperator
        (φ.codRestrict L hmem).range
        (commutator (generatedGNSCompression τP L S)
          ((restrictedPositiveTrace τP L).gnsStarAlgHom (φ.codRestrict L hmem a)))‖ :=
  norm_commutator_le_tracial_range_compression τA (restrictedPositiveTrace τP L)
    (restrictedPositiveTrace_tracial τP L trP) (φ.codRestrict L hmem)
    (restrictedHom_preserves_trace τA τP L φ hmem hφ) T (generatedGNSCompression τP L S)
    (generatedGNSCompression_recover τA τP L φ hmem hφ T S hT) a

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SubalgebraNormality
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normality of a represented subalgebra follows from closed bounded
trace-vector sets, using the original ambient tracial geometry for totality. -/

noncomputable section
namespace KadisonSimilarity.TracialCornerGeometry
open scoped CStarAlgebra

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (S : StarSubalgebra ℂ P) [IsClosed (S : Set P)]

theorem subalgebra_normal_range_of_closed_trace_balls
    (hclosed : ∀ C : ℝ, IsClosed ((G.vector.comp S.subtype.toLinearMap) ''
      Metric.closedBall (0 : S) C)) :
    S.map G.left = (representationVonNeumannAlgebra (G.left.comp S.subtype)).toStarSubalgebra := by
  let σ := G.left.comp S.subtype
  ext T
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact mem_representationVonNeumannAlgebra σ ⟨a, ha⟩
  · intro hT
    have hv : T (G.vector 1) ∈ (G.vector.comp S.subtype.toLinearMap) ''
        Metric.closedBall (0 : S) (‖T‖ + 1) := by
      apply (hclosed _).closure_subset
      apply Metric.mem_closure_iff.mpr
      intro ε hε
      let δ := min (ε / 2) 1
      have hδ : 0 < δ := lt_min (by positivity) zero_lt_one
      obtain ⟨a, ha, happrox, _⟩ := twoVectorKaplanskyInput σ T hT
        (G.vector 1) (G.vector 1) δ hδ
      refine ⟨G.vector (a : P), ⟨a, ?_, rfl⟩, ?_⟩
      · simpa only [Metric.mem_closedBall, dist_zero_right] using
          ha.trans (add_le_add le_rfl (min_le_right (ε / 2) 1))
      · rw [dist_eq_norm]
        change ‖T (G.vector 1) - G.vector (a : P)‖ < ε
        have hv : σ a (G.vector 1) = G.vector (a : P) := by
          change G.left (a : P) (G.vector 1) = _
          rw [G.left_vector, mul_one]
        rw [← hv, norm_sub_rev]
        exact happrox.trans_lt ((min_le_left (ε / 2) 1).trans_lt (by linarith))
    obtain ⟨a, _, ha⟩ := hv
    refine ⟨(a : P), a.property, ?_⟩
    ext ξ
    refine G.dense_vector.induction_on ξ (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro b
    have hTc : T ∈ Set.centralizer (Set.centralizer (Set.range σ)) := by
      change T ∈ representationVonNeumannAlgebra σ at hT
      rwa [← SetLike.mem_coe, coe_representationVonNeumannAlgebra] at hT
    have hc : G.right b * T = T * G.right b := hTc (G.right b) (by
      rintro _ ⟨c, rfl⟩
      exact (G.right_left (c : P) b).symm)
    have hcv := congrArg (fun R : H →L[ℂ] H => R (G.vector 1)) hc
    change G.right b (T (G.vector 1)) = T (G.right b (G.vector 1)) at hcv
    change G.vector (a : P) = T (G.vector 1) at ha
    rw [G.right_vector, one_mul, ← ha, G.right_vector] at hcv
    exact (G.left_vector (a : P) b).trans hcv

end KadisonSimilarity.TracialCornerGeometry

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialEmbeddingBalls
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed bounded trace-vector sets transfer through a trace-preserving
embedding, giving normality and expectation onto its actual range. -/

noncomputable section
namespace KadisonSimilarity
open TracialCornerGeometry
open scoped CStarAlgebra ComplexOrder

variable {R P H : Type*} [CStarAlgebra R] [CStarAlgebra P]
  [PartialOrder R] [StarOrderedRing R]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (τ : R →ₚ[ℂ] ℂ) (G : TracialCornerGeometry P H)
  (φ : R →⋆ₐ[ℂ] P) (hφ : ∀ a, G.trace (φ a) = τ a)
  (hi : Function.Injective φ)

include hφ hi in
theorem tracialRange_trace_balls_closed
    (hc : ∀ C : ℝ, IsClosed (gnsTracialVector τ '' Metric.closedBall (0 : R) C))
    (C : ℝ) : IsClosed ((G.vector.comp φ.range.subtype.toLinearMap) ''
      Metric.closedBall (0 : φ.range) C) := by
  let j := (G.baseInclusion φ.range).comp (tracialRangeIsometry τ G φ hφ)
  have hj (a : R) : j (gnsTracialVector τ a) = G.vector (φ a) := by
    change (G.baseInclusion φ.range) (tracialRangeIsometry τ G φ hφ (gnsTracialVector τ a)) = _
    rw [tracialRangeIsometry_vector]
    rfl
  have hn (a : R) : ‖φ a‖ = ‖a‖ := (NonUnitalStarAlgHom.isometry φ hi).norm_map_of_map_zero
    (map_zero φ) a
  have heq : (G.vector.comp φ.range.subtype.toLinearMap) ''
      Metric.closedBall (0 : φ.range) C =
      j '' (gnsTracialVector τ '' Metric.closedBall (0 : R) C) := by
    ext ξ
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨b, hb⟩ := a.property
      change φ b = (a : P) at hb
      refine ⟨gnsTracialVector τ b, ⟨b, ?_, rfl⟩, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right] at ha ⊢
        rw [← hn, hb]
        exact ha
      · rw [hj, hb]
        rfl
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨φ.rangeRestrict a, ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right] at ha ⊢
        change ‖φ a‖ ≤ C
        rwa [hn]
      · exact (hj a).symm
  rw [heq]
  exact j.isometry.isClosedEmbedding.isClosedMap _ (hc C)

include hφ hi in
theorem tracialRange_normal [IsClosed (φ.range : Set P)]
    (hc : ∀ C : ℝ, IsClosed (gnsTracialVector τ '' Metric.closedBall (0 : R) C)) :
    φ.range.map G.left =
      (representationVonNeumannAlgebra (G.left.comp φ.range.subtype)).toStarSubalgebra := by
  exact G.subalgebra_normal_range_of_closed_trace_balls φ.range
    (tracialRange_trace_balls_closed τ G φ hφ hi hc)

include hφ hi in
theorem tracialRange_expectation
    (hc : ∀ C : ℝ, IsClosed (gnsTracialVector τ '' Metric.closedBall (0 : R) C))
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (M : VonNeumannAlgebra H) (hrange : G.left.range = M.toStarSubalgebra) :
    Nonempty (TracialExpectation G.trace φ.range) := by
  let : IsClosed (φ.range : Set P) := (NonUnitalStarAlgHom.isometry φ hi).isClosedEmbedding.isClosed_range
  exact G.tracialExpectation_of_normal_range h1 hf M hrange φ.range _
    (tracialRange_normal τ G φ hφ hi hc)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_CanonicalBaseExpectation
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first-factor expectation in the canonical generated algebra follows
from bounded trace-vector closure in the original factor. -/

noncomputable section
namespace KadisonSimilarity
open TracialCornerGeometry
open scoped ComplexOrder

variable {A R P : Type*} [CStarAlgebra A] [CStarAlgebra R] [CStarAlgebra P]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder P] [StarOrderedRing P]
  (τ : P →ₚ[ℂ] ℂ) (htr : ∀ a b : P, τ (a * b) = τ (b * a))
  (φ : A →⋆ₐ[ℂ] P) (ψ : R →⋆ₐ[ℂ] P)
  (τA : A →ₚ[ℂ] ℂ) (hφτ : ∀ a, τ (φ a) = τA a)
  (hi : Function.Injective φ)

local notation "G" => canonicalGeneratedGeometry τ htr φ ψ

include hi hφτ in
theorem canonicalFirstRange_expectation
    (hc : ∀ C : ℝ, IsClosed (gnsTracialVector τA '' Metric.closedBall (0 : A) C))
    (h1 : τ 1 = 1) (hf : ∀ a : P, τ (star a * a) = 0 → a = 0)
    (hnormal : ∃ N : VonNeumannAlgebra (canonicalGeneratedTrace τ htr φ ψ).GNS,
      (G).left.range = N.toStarSubalgebra) :
    Nonempty (TracialExpectation (G).trace (canonicalGeneratedFirst τ htr φ ψ).range) := by
  obtain ⟨N, hN⟩ := hnormal
  have hi' : Function.Injective (canonicalGeneratedFirst τ htr φ ψ) := by
    intro a b h
    exact hi (congrArg (fun x : canonicalGeneratedAlgebra τ htr φ ψ => (x : P)) h)
  exact tracialRange_expectation τA (G) (canonicalGeneratedFirst τ htr φ ψ)
    hφτ hi' hc h1 (canonicalGenerated_faithful τ htr φ ψ hf) N hN

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_RestrictedNormality
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The canonical GNS model of a bounded L²-generated algebra is normal.
The proof uses the actual inclusion of its trace vectors in the ambient
GNS space. -/

noncomputable section
namespace KadisonSimilarity
open TracialCornerGeometry
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (htr : ∀ a b : A, τ (a * b) = τ (b * a))

theorem restricted_generated_trace_balls_closed
    (hc : ∀ C : ℝ, IsClosed (gnsTracialVector τ '' Metric.closedBall (0 : A) C))
    (S : StarSubalgebra ℂ A) (C : ℝ) :
    let L := (gnsTracialGeometry τ htr).l2GeneratedAlgebra S
    IsClosed (gnsTracialVector (restrictedPositiveTrace τ L) '' Metric.closedBall (0 : L) C) := by
  let G := gnsTracialGeometry τ htr
  let L := G.l2GeneratedAlgebra S
  let J := restrictedTracialGNSInclusion τ L
  change IsClosed (gnsTracialVector (restrictedPositiveTrace τ L) '' Metric.closedBall (0 : L) C)
  have heq : gnsTracialVector (restrictedPositiveTrace τ L) '' Metric.closedBall (0 : L) C =
      J ⁻¹' (gnsTracialVector τ '' Metric.closedBall (0 : A) C) := by
    ext ξ
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(a : A), ha, (restrictedTracialGNSInclusion_vector τ L a).symm⟩
    · rintro ⟨a, ha, hξ⟩
      have hJξ : J ξ ∈ G.baseSpace L := by
        change J ξ ∈ ((gnsTracialGeometry τ htr).baseSpace L : Set τ.GNS)
        rw [← restrictedTracialGNSInclusion_range τ L htr]
        exact ⟨ξ, rfl⟩
      have hmem : a ∈ L := by
        change G.vector a ∈ G.baseSpace S.topologicalClosure
        change G.vector a = J ξ at hξ
        rw [hξ, G.baseSpace_topologicalClosure]
        exact (le_of_eq (G.baseSpace_l2GeneratedAlgebra S)) hJξ
      refine ⟨⟨a, hmem⟩, ha, ?_⟩
      apply J.injective
      exact (restrictedTracialGNSInclusion_vector τ L ⟨a, hmem⟩).trans hξ
  rw [heq]
  exact (hc C).preimage J.continuous

theorem restricted_generated_normal_range
    (hc : ∀ C : ℝ, IsClosed (gnsTracialVector τ '' Metric.closedBall (0 : A) C))
    (S : StarSubalgebra ℂ A) :
    let L := (gnsTracialGeometry τ htr).l2GeneratedAlgebra S
    (restrictedPositiveTrace τ L).gnsStarAlgHom.range =
      (representationVonNeumannAlgebra (restrictedPositiveTrace τ L).gnsStarAlgHom).toStarSubalgebra := by
  dsimp only
  exact (gnsTracialGeometry _ (restrictedPositiveTrace_tracial τ _ htr)).normal_range_of_closed_trace_balls
    (restricted_generated_trace_balls_closed τ htr hc S)

variable {B R : Type*} [CStarAlgebra B] [CStarAlgebra R]

theorem canonicalGenerated_normal_range
    (hc : ∀ C : ℝ, IsClosed (gnsTracialVector τ '' Metric.closedBall (0 : A) C))
    (φ : B →⋆ₐ[ℂ] A) (ψ : R →⋆ₐ[ℂ] A) :
    (canonicalGeneratedGeometry τ htr φ ψ).left.range =
      (representationVonNeumannAlgebra (canonicalGeneratedGeometry τ htr φ ψ).left).toStarSubalgebra :=
  restricted_generated_normal_range τ htr hc (factorAlgebra φ.range ψ.range)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialUltrapowerCorners
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.BoundedHochschild.WeakSubspace.preannihilator_closed_instance _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.corner_closed _root_.OAI.HochschildMatrixSystems.MatrixSystem.commutant_closed _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.canonicalGeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerClosed _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.PopaCorner.algebra_closed _root_.OAI.PopaCorner.instNormedRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small-corner estimate passes from coordinate projections to the
actual tracial ultrapower. Norm lifting and compression are constructed. -/

noncomputable section
namespace KadisonSimilarity

open HochschildUltrapower Filter
open scoped ComplexOrder Topology BoundedContinuousFunction

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a * b) = τ (b * a))

/-- An actual lifted projection transfers every coordinate corner bound.
No action of a null algebra sequence on the whole Hilbert ultrapower is asserted. -/
theorem tracialUltrapower_corner_bound_of_projection_lift
    (T : τ.GNS →L[ℂ] τ.GNS) (p : ℕ →ᵇ A) (hp : ∀ i, IsStarProjection (p i))
    (e : Ultrapower τ h1 ω htr) (he : IsStarProjection e)
    (hpe : quotientHom τ h1 ω htr p = e)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcorner : ∀ i, ∀ z : CStarCorner (p i) (hp i),
      ‖commutator T (τ.gnsStarAlgHom (z : A))‖ ≤ ε * ‖z‖)
    (z : CStarCorner e he) :
    ‖commutator (tracialUltrapowerCompression τ h1 ω htr T)
      ((quotientTrace τ h1 ω htr).gnsStarAlgHom (z : Ultrapower τ h1 ω htr))‖ ≤ ε * ‖z‖ := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  let η := δ / (ε + 1)
  have hη : 0 < η := div_pos hδ (by positivity)
  obtain ⟨b, hb, hbn⟩ := HochschildCStarQuotient.norm_mk_lt
    (ideal τ h1 ω htr) (z : Ultrapower τ h1 ω htr) hη
  let a : ℕ →ᵇ A := p * b * p
  have haq : quotientHom τ h1 ω htr a = (z : Ultrapower τ h1 ω htr) := by
    change quotientHom τ h1 ω htr (p * b * p) = _
    have hb' : quotientHom τ h1 ω htr b = (z : Ultrapower τ h1 ω htr) := hb
    rw [map_mul, map_mul, hpe, hb', z.property.1, z.property.2]
  have ha (i : ℕ) : ‖commutator T (τ.gnsStarAlgHom (a i))‖ ≤
      ε * (‖z‖ + η) := by
    let zi : CStarCorner (p i) (hp i) := ⟨a i, by
      change p i * (p i * b i * p i) = p i * b i * p i ∧
        (p i * b i * p i) * p i = p i * b i * p i
      constructor
      · rw [← mul_assoc, ← mul_assoc, (hp i).isIdempotentElem.eq]
      · rw [mul_assoc, (hp i).isIdempotentElem.eq]⟩
    have hpn : ‖p i‖ ≤ 1 := norm_le_one_of_star_projection (p i) (hp i)
    have hzi : ‖zi‖ ≤ ‖z‖ + η := by
      change ‖p i * b i * p i‖ ≤ ‖z‖ + η
      calc
        _ ≤ (‖p i‖ * ‖b i‖) * ‖p i‖ :=
          (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ (1 * ‖b i‖) * 1 := by gcongr
        _ = ‖b i‖ := by ring
        _ ≤ ‖b‖ := b.norm_coe_le_norm i
        _ ≤ ‖z‖ + η := hbn.le
    exact (hcorner i zi).trans (mul_le_mul_of_nonneg_left hzi hε)
  have hbnd := norm_tracialUltrapowerCompression_commutator_le τ h1 ω htr T a
    (mul_nonneg hε (by positivity : 0 ≤ ‖z‖ + η))
    (Filter.Eventually.of_forall ha)
  rw [haq] at hbnd
  have hcancel : η * (ε + 1) = δ := div_mul_cancel₀ δ (by positivity)
  nlinarith [hη]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialIncludedCorners
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small-corner bounds from Q inside P pass to the included tracial
ultrapower Q^ω inside P^ω. The strict trace gap is explicit. -/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open scoped ComplexOrder Topology BoundedContinuousFunction

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b : A, τA (a * b) = τA (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)

local notation "Φ" => tracialUltrapowerMap τA τB hA hB ω trA trB φ hφ

/-- The full small-corner transfer, including lifting inside the prescribed
subalgebra, near-minimal quotient lifts, and Hilbert compression. -/
theorem included_ultrapower_corner_bound
    (rounding : SpectralProjectionRoundingInput τA)
    (T : τB.GNS →L[ℂ] τB.GNS) {ε s : ℝ} (hε : 0 ≤ ε)
    (hcorner : ∀ (q : A) (hq : IsStarProjection q), (τA q).re ≤ s →
      ∀ z : CStarCorner (φ q) (hq.map φ),
        ‖commutator T (τB.gnsStarAlgHom (z : B))‖ ≤ ε * ‖z‖)
    (e : Ultrapower τA hA ω trA) (he : IsStarProjection e)
    (hte : (quotientTrace τA hA ω trA e).re < s)
    (z : CStarCorner (Φ e) (he.map Φ)) :
    ‖commutator (tracialUltrapowerCompression τB hB ω trB T)
      ((quotientTrace τB hB ω trB).gnsStarAlgHom
        (z : Ultrapower τB hB ω trB))‖ ≤ ε * ‖z‖ := by
  obtain ⟨p, hp, hpt, hpe⟩ := exists_projection_representative_trace_le
    τA hA ω trA rounding e he hte
  let pB := boundedSequenceStarHom φ p
  have hpB (i : ℕ) : IsStarProjection (pB i) := (hp i).map φ
  have hpBe : quotientHom τB hB ω trB pB = Φ e := by
    rw [← hpe, tracialUltrapowerMap_mk]
  exact tracialUltrapower_corner_bound_of_projection_lift τB hB ω trB T pB hpB
    (Φ e) (he.map Φ) hpBe hε (fun i => hcorner (p i) (hp i) (hpt i)) z

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_UltrapowerFreePositionTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Commutation and small-corner estimates pass to the concrete free copy
inside the prescribed subfactor ultrapower. Recovery of the original
commutator uses the exact constant GNS embedding. -/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open scoped ComplexOrder Topology BoundedContinuousFunction

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b : A, τA (a * b) = τA (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)

local notation "Φ" => tracialUltrapowerMap τA τB hA hB ω trA trB φ hφ
local notation "τQ" => quotientTrace τB hB ω trB
local notation "G" => gnsTracialGeometry τQ (quotientTrace_tracial τB hB ω trB)

/-- An operator commuting with the original subfactor commutes with its
entire included ultrapower after the actual Hilbert compression. -/
theorem tracialUltrapowerCompression_commutes_range
    (T : τB.GNS →L[ℂ] τB.GNS)
    (hcomm : ∀ a, T.comp (τB.gnsStarAlgHom (φ a)) =
      (τB.gnsStarAlgHom (φ a)).comp T) :
    ∀ x : (Φ).range,
      (tracialUltrapowerCompression τB hB ω trB T).comp ((τQ).gnsStarAlgHom (x : _)) =
        ((τQ).gnsStarAlgHom (x : _)).comp (tracialUltrapowerCompression τB hB ω trB T) := by
  rintro ⟨_, a, rfl⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  change (tracialUltrapowerCompression τB hB ω trB T).comp
    ((τQ).gnsStarAlgHom (Φ (quotientHom τA hA ω trA x))) =
    ((τQ).gnsStarAlgHom (Φ (quotientHom τA hA ω trA x))).comp
      (tracialUltrapowerCompression τB hB ω trB T)
  rw [tracialUltrapowerMap_mk]
  have hb := norm_tracialUltrapowerCompression_commutator_le τB hB ω trB T
    (boundedSequenceStarHom φ x) (c := 0) le_rfl
    (Filter.Eventually.of_forall (fun i => by
      have hz : commutator T (τB.gnsStarAlgHom (φ (x i))) = 0 := sub_eq_zero.mpr (hcomm (x i))
      change ‖commutator T (τB.gnsStarAlgHom (φ (x i)))‖ ≤ 0
      rw [hz, norm_zero]))
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hb)

/-- Every smaller subalgebra of the included ultrapower inherits commutation. -/
theorem tracialUltrapowerCompression_commutes_subalgebra
    (D : StarSubalgebra ℂ (Ultrapower τB hB ω trB)) (hD : D ≤ (Φ).range)
    (T : τB.GNS →L[ℂ] τB.GNS)
    (hcomm : ∀ a, T.comp (τB.gnsStarAlgHom (φ a)) =
      (τB.gnsStarAlgHom (φ a)).comp T) :
    ∀ x : D,
      (tracialUltrapowerCompression τB hB ω trB T).comp ((τQ).gnsStarAlgHom (x : _)) =
        ((τQ).gnsStarAlgHom (x : _)).comp (tracialUltrapowerCompression τB hB ω trB T) :=
  fun x => tracialUltrapowerCompression_commutes_range τA τB hA hB ω trA trB φ hφ
    T hcomm ⟨x, hD x.property⟩

/-- The exact strict trace gap gives the small-corner predicate consumed
by the original free-corner theorem on any contained free subfactor. -/
theorem included_ultrapower_traceCornerBound
    (rounding : SpectralProjectionRoundingInput τA)
    (D : StarSubalgebra ℂ (Ultrapower τB hB ω trB)) (hD : D ≤ (Φ).range)
    (T : τB.GNS →L[ℂ] τB.GNS) {ε s t : ℝ} (hε : 0 ≤ ε) (hts : t < s)
    (hcorner : ∀ (q : A) (hq : IsStarProjection q), (τA q).re ≤ s →
      ∀ z : CStarCorner (φ q) (hq.map φ),
        ‖commutator T (τB.gnsStarAlgHom (z : B))‖ ≤ ε * ‖z‖) :
    (G).TraceCornerBound D (tracialUltrapowerCompression τB hB ω trB T) t ε := by
  intro e he heD hte z
  obtain ⟨a, ha⟩ := hD heD
  subst e
  change IsStarProjection (Φ a) at he
  change (G).trace (Φ a) = (t : ℂ) at hte
  change CStarCorner (Φ a) he at z
  have hi := tracialUltrapowerMap_injective τA τB hA hB ω trA trB φ hφ
  have hp : IsStarProjection a := by
    constructor
    · apply hi
      simpa only [map_mul] using he.isIdempotentElem.eq
    · apply hi
      simpa only [map_star] using he.isSelfAdjoint.star_eq
  have ht : (quotientTrace τA hA ω trA a).re < s := by
    rw [← tracialUltrapowerMap_trace τA τB hA hB ω trA trB φ hφ]
    change ((G).trace (Φ a)).re < s
    rw [hte, Complex.ofReal_re]
    exact hts
  exact included_ultrapower_corner_bound τA τB hA hB ω trA trB φ hφ
    rounding T hε hcorner a hp ht z

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_UltrapowerGeneratedTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two compressions used in the finite-factor argument are combined
here. The resulting operator on the generated algebra retains commutation,
all prescribed small-corner bounds, and the original commutator norm. -/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open scoped ComplexOrder

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b : A, τA (a * b) = τA (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)

local notation "τQ" => quotientTrace τB hB ω trB

variable (L D : StarSubalgebra ℂ (Ultrapower τB hB ω trB))
  [IsClosed (L : Set (Ultrapower τB hB ω trB))]

attribute [local instance] OAI.KadisonSimilarity.generatedAlgebraCStar
attribute [local instance] OAI.KadisonSimilarity.generatedAlgebraOrder
attribute [local instance] OAI.KadisonSimilarity.generatedAlgebraStarOrder
attribute [local instance] OAI.KadisonSimilarity.generatedPreGNSNorm
attribute [local instance] OAI.KadisonSimilarity.generatedGNSNorm
local instance generatedGNSInner_r1597fb_1 :
    InnerProductSpace ℂ (restrictedPositiveTrace (quotientTrace τB hB ω trB) L).GNS :=
  inferInstance
/-- A bound from the free-corner theorem on this generated algebra controls
the original operator on its original GNS space, with the identical constant. -/
theorem norm_commutator_le_generatedUltrapowerOperator
    (hconst : ∀ b, constant τB hB ω trB b ∈ L)
    (T : τB.GNS →L[ℂ] τB.GNS) (b : B) :
    ‖commutator T (τB.gnsStarAlgHom b)‖ ≤
      ‖(gnsTracialGeometry (restrictedPositiveTrace τQ L)
          (restrictedPositiveTrace_tracial τQ L (quotientTrace_tracial τB hB ω trB))).baseOperator
        ((constant τB hB ω trB).codRestrict L hconst).range
        (commutator (generatedUltrapowerOperator τB hB ω trB L T)
          ((restrictedPositiveTrace τQ L).gnsStarAlgHom
            ((constant τB hB ω trB).codRestrict L hconst b)))‖ :=
  norm_commutator_le_generated_GNS_compression τB τQ L (constant τB hB ω trB)
    hconst (quotientTrace_constant τB hB ω trB) (quotientTrace_tracial τB hB ω trB)
    T (tracialUltrapowerCompression τB hB ω trB T)
    (constant_compression_tracialUltrapower τB hB ω trB T) b

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_UltrapowerTraceBalls
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.generatedGNSInclusion_vector _root_.OAI.KadisonSimilarity.matrixGNSArrayLinear_apply _root_.OAI.KadisonSimilarity.matrixGNSIsometry_vector _root_.OAI.KadisonSimilarity.matrixGNSUnitary_vector _root_.OAI.KadisonSimilarity.matrixGNSVector_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.KadisonSimilarity.tracialUltrapowerMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal bounded representatives in the tracial ultrapower. -/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower TracialUltrapower Filter
open scoped Topology BoundedContinuousFunction ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
  (htr : ∀ a b : A, τ (a * b) = τ (b * a))

private theorem trace_sequence_norm_tendsto (z : ℕ →ᵇ A) :
    Tendsto (fun i => ‖τ.toPreGNS (z i)‖) (ω : Filter ℕ)
      (𝓝 ‖gnsTracialVector (quotientTrace τ h1 ω htr) (quotientHom τ h1 ω htr z)‖) := by
  rw [gnsTracialVector_apply, UniformSpace.Completion.norm_coe, quotientTrace_preGNS_norm]
  change Tendsto (fun i => ‖τ.toPreGNS (z i)‖) (ω : Filter ℕ)
    (𝓝 (sequenceTwoNorm (traceHilbertMap τ h1) ω z))
  simpa only [traceHilbertMap_apply] using
    tendsto_sequenceTwoNorm (traceHilbertMap τ h1) ω z

/-- A rapidly converging sequence of uniformly bounded representatives has
one bounded diagonal representative for its Hilbert-space limit. -/
theorem exists_bounded_diagonal_trace_limit
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (x : ℕ → (ℕ →ᵇ A)) (C : ℝ) (hC : 0 ≤ C) (hx : ∀ n, ‖x n‖ ≤ C)
    (ξ : (quotientTrace τ h1 ω htr).GNS)
    (hξ : ∀ n, dist (gnsTracialVector (quotientTrace τ h1 ω htr)
      (quotientHom τ h1 ω htr (x n))) ξ ≤ (1 / 2 : ℝ) ^ n) :
    ∃ y : ℕ →ᵇ A, ‖y‖ ≤ C ∧
      gnsTracialVector (quotientTrace τ h1 ω htr) (quotientHom τ h1 ω htr y) = ξ := by
  classical
  let V := gnsTracialVector (quotientTrace τ h1 ω htr)
  let q := quotientHom τ h1 ω htr
  let r : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n
  have hr (n : ℕ) : 0 < r n := pow_pos (by norm_num) _
  let P : ℕ → ℕ → Prop := fun i n => ∀ j ≤ n,
    ‖τ.toPreGNS (x n i - x j i)‖ ≤ 3 * r j
  have hP (n : ℕ) : ∀ᶠ i in (ω : Filter ℕ), P i n := by
    have hb (j : ℕ) (hjn : j ≤ n) : ‖V (q (x n - x j))‖ < 3 * r j := by
      have hn : r n ≤ r j := pow_le_pow_of_le_one (by norm_num) (by norm_num) hjn
      calc
        ‖V (q (x n - x j))‖ = dist (V (q (x n))) (V (q (x j))) := by
          rw [dist_eq_norm, map_sub, map_sub]
        _ ≤ dist (V (q (x n))) ξ + dist ξ (V (q (x j))) := dist_triangle _ _ _
        _ ≤ r n + r j := add_le_add (hξ n) (by simpa only [dist_comm] using hξ j)
        _ < 3 * r j := by linarith [hr j]
    have hall : ∀ᶠ i in (ω : Filter ℕ), ∀ j ∈ Finset.range (n + 1),
        ‖τ.toPreGNS (x n i - x j i)‖ ≤ 3 * r j := by
      rw [eventually_all_finset]
      intro j hj
      have ht := (trace_sequence_norm_tendsto τ h1 ω htr (x n - x j)).eventually_lt_const
        (hb j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      exact ht.mono fun i hi => hi.le
    filter_upwards [hall] with i hi j hj
    exact hi j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have hP0 (i : ℕ) : P i 0 := by
    intro j hj
    have : j = 0 := by omega
    subst j
    simp only [sub_self, map_zero, norm_zero]
    positivity
  let k : ℕ → ℕ := fun i => Nat.findGreatest (P i) i
  have hkP (i : ℕ) : P i (k i) := Nat.findGreatest_spec (Nat.zero_le i) (hP0 i)
  have hk (j : ℕ) : ∀ᶠ i in (ω : Filter ℕ), j ≤ k i := by
    have hji : ∀ᶠ i in (ω : Filter ℕ), j ≤ i :=
      (eventually_ge_atTop j).filter_mono (hω.trans_eq Nat.cofinite_eq_atTop)
    filter_upwards [hji, hP j] with i hji hi
    exact Nat.le_findGreatest hji hi
  let y : ℕ →ᵇ A := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun i => x (k i) i) C (fun i => (x (k i)).norm_coe_le_norm i |>.trans (hx (k i)))
  have hy : ‖y‖ ≤ C := (BoundedContinuousFunction.norm_le hC).mpr
    (fun i => (x (k i)).norm_coe_le_norm i |>.trans (hx (k i)))
  refine ⟨y, hy, ?_⟩
  have hdist (j : ℕ) : dist (V (q y)) ξ ≤ 4 * r j := by
    have hj : ‖V (q (y - x j))‖ ≤ 3 * r j := by
      apply le_of_tendsto (trace_sequence_norm_tendsto τ h1 ω htr (y - x j))
      filter_upwards [hk j] with i hi
      exact hkP i j hi
    calc
      dist (V (q y)) ξ ≤ dist (V (q y)) (V (q (x j))) + dist (V (q (x j))) ξ :=
        dist_triangle _ _ _
      _ ≤ 3 * r j + r j := by
        apply add_le_add _ (hξ j)
        simpa only [dist_eq_norm, map_sub] using hj
      _ = 4 * r j := by ring
  apply dist_eq_zero.mp
  apply le_antisymm _ dist_nonneg
  have ht : Tendsto (fun j => 4 * r j) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul 4
  exact ge_of_tendsto ht (Eventually.of_forall hdist)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_UltrapowerNormality
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.canonicalGeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.generatedGNSInclusion_vector _root_.OAI.KadisonSimilarity.matrixGNSArrayLinear_apply _root_.OAI.KadisonSimilarity.matrixGNSIsometry_vector _root_.OAI.KadisonSimilarity.matrixGNSUnitary_vector _root_.OAI.KadisonSimilarity.matrixGNSVector_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector _root_.OAI.KadisonSimilarity.tracialUltrapowerMap_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual tracial ultrapower has closed bounded trace-vector balls,
hence its faithful GNS representation is a von Neumann algebra. -/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower TracialUltrapower Filter
open scoped Topology BoundedContinuousFunction ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
  (htr : ∀ a b : A, τ (a * b) = τ (b * a))
  (hω : (ω : Filter ℕ) ≤ Filter.cofinite)

include hω in
theorem ultrapower_trace_balls_closed (C : ℝ) :
    IsClosed (gnsTracialVector (quotientTrace τ h1 ω htr) ''
      Metric.closedBall (0 : Ultrapower τ h1 ω htr) C) := by
  classical
  let V := gnsTracialVector (quotientTrace τ h1 ω htr)
  let q := quotientHom τ h1 ω htr
  apply IsSeqClosed.isClosed
  intro u ξ hu hlim
  choose X hX hXu using hu
  have hXC (n : ℕ) : ‖X n‖ ≤ C := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hX n
  have hC : 0 ≤ C := (norm_nonneg (X 0)).trans (hXC 0)
  have happrox (k : ℕ) : ∃ n, dist (u n) ξ ≤ (1 / 2 : ℝ) ^ k := by
    have hk : 0 < (1 / 2 : ℝ) ^ k := pow_pos (by norm_num) _
    obtain ⟨n, hn⟩ := (hlim.eventually (Metric.ball_mem_nhds ξ hk)).exists
    exact ⟨n, hn.le⟩
  choose n hn using happrox
  have hrep (ε : ℝ) (hε : 0 < ε) :
      ∃ a : Ultrapower τ h1 ω htr, ‖a‖ ≤ C + ε ∧ V a = ξ := by
    choose x hx hxn using fun k =>
      HochschildCStarQuotient.norm_mk_lt (ideal τ h1 ω htr) (X (n k)) hε
    have hxC (k : ℕ) : ‖x k‖ ≤ C + ε := (hxn k).le.trans (add_le_add (hXC _) le_rfl)
    have htrace (k : ℕ) : V (q (x k)) = u (n k) := by
      change V (Ideal.Quotient.mk (ideal τ h1 ω htr) (x k)) = _
      rw [hx k]
      exact hXu _
    obtain ⟨y, hy, hlimit⟩ := exists_bounded_diagonal_trace_limit τ h1 ω htr hω x
      (C + ε) (by positivity) hxC ξ (fun k => by rw [htrace]; exact hn k)
    exact ⟨q y, (NonUnitalStarAlgHom.norm_apply_le q y).trans hy, hlimit⟩
  obtain ⟨a, _, ha⟩ := hrep 1 zero_lt_one
  refine ⟨a, ?_, ha⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨b, hb, hbeq⟩ := hrep ε hε
  have hab : a = b := gnsTracialVector_injective (quotientTrace τ h1 ω htr)
    (quotientTrace_faithful τ h1 ω htr) (ha.trans hbeq.symm)
  simpa only [hab] using hb

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_CanonicalFreeCornerEstimate
attribute [-instance] _root_.OAI.KadisonSimilarity.jointCStarSource_isClosed _root_.OAI.KadisonSimilarity.sequenceGeneratedCStarAlgebra_isClosed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original operator is recovered after applying the local free-corner
argument in the actual generated GNS model. All generation, faithfulness,
and compression requirements are proved here; the remaining local hypotheses
are the explicitly cited published structural inputs. -/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open TracialCornerGeometry
open scoped ComplexOrder

variable {A B R : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra R]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder R] [StarOrderedRing R]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ) (τR : R →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b : A, τA (a * b) = τA (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)

local notation "τQ" => quotientTrace τB hB ω trB
local notation "trQ" => quotientTrace_tracial τB hB ω trB
local notation "ι" => constant τB hB ω trB
local notation "Φ" => tracialUltrapowerMap τA τB hA hB ω trA trB φ hφ

variable (ψ : R →⋆ₐ[ℂ] Ultrapower τB hB ω trB)
  (hψτ : ∀ r, quotientTrace τB hB ω trB (ψ r) = τR r)
  (hfB : ∀ a : B, τB (star a * a) = 0 → a = 0)
  (hψ : Function.Injective ψ)

local notation "L" => canonicalGeneratedAlgebra τQ trQ ι ψ
local notation "D₀" => StarAlgHom.range (canonicalGeneratedSecond τQ trQ ι ψ)

variable {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) τR.toLinearMap (gnsTracialVector τR))

include hfB in
/-- A centered symmetry in the original finite algebra obeys the free-corner
bound. The tested operator is the original GNS operator, not a separately
chosen operator on a model. -/
theorem original_symmetry_bound_of_free_corner_oai
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (hD : ψ.range ≤ (Φ).range)
    (hf : ScalarFree (quotientTrace τB hB ω trB).toLinearMap
      (constant τB hB ω trB).range ψ.range)
    (S : RealTracialSequence τR.toLinearMap)
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    {b : ℝ} (Q : CanonicalSecondFrame τB hB ω trB ψ hψ b)
    (x : B) (hxstar : star x = x) (hxsq : x * x = 1) (hx0 : τB x = 0)
    (source_balls : ∀ C : ℝ, IsClosed (gnsTracialVector τB '' Metric.closedBall (0 : B) C))
    (published : CanonicalFreeCornerInput τB τR hB ω trB ψ hψτ hψ M Q x hxsq)
    (rounding : SpectralProjectionRoundingInput τA)
    (T : τB.GNS →L[ℂ] τB.GNS)
    (hcomm : ∀ a, T.comp (τB.gnsStarAlgHom (φ a)) =
      (τB.gnsStarAlgHom (φ a)).comp T)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcorner : ∀ (q : A) (hq : IsStarProjection q), (τA q).re ≤ b →
      ∀ z : CStarCorner (φ q) (hq.map φ),
        ‖commutator T (τB.gnsStarAlgHom (z : B))‖ ≤ ε * ‖z‖) :
    ‖commutator T (τB.gnsStarAlgHom x)‖ ≤ cornerConstant * ε := by
  have : IsClosed (D₀ : Set L) := canonicalSecondRange_closed τQ trQ ι ψ hψ
  have : IsClosed (StarAlgHom.range (canonicalGeneratedFirst τQ trQ ι ψ) : Set L) :=
    canonicalFirstRange_closed τQ trQ ι ψ (constant_injective τB hB ω trB hfB)
  have hxQ : τQ (ι x) = 0 := by rw [quotientTrace_constant, hx0]
  have hamb := included_ultrapower_traceCornerBound τA τB hA hB ω trA trB
    φ hφ rounding ψ.range hD T hε Q.trace_lt hcorner
  have hnativecomm := fun r =>
    tracialUltrapowerCompression_commutes_subalgebra τA τB hA hB ω trA trB
      φ hφ ψ.range hD T hcomm ⟨ψ r, ⟨r, rfl⟩⟩
  have hnormal := canonicalGenerated_normal_range τQ trQ
    (ultrapower_trace_balls_closed τB hB ω trB hω) ι ψ
  have hbase := canonicalFirstRange_expectation τQ trQ ι ψ τB
    (quotientTrace_constant τB hB ω trB) (constant_injective τB hB ω trB hfB)
    source_balls (quotientTrace_one τB hB ω trB)
    (quotientTrace_faithful τB hB ω trB) ⟨_, hnormal⟩
  have hlocal := canonical_free_corner_bound (τ := τQ) (htr := trQ)
    (φ := ι) (ψ := ψ)
    (τR := τR) (hψτ := hψτ) (M := M)
    (h1 := quotientTrace_one τB hB ω trB)
    (hfτ := quotientTrace_faithful τB hB ω trB)
    hf S hsize Q x hxstar hxsq hxQ published hbase ⟨_, hnormal⟩
    (tracialUltrapowerCompression τB hB ω trB T) hnativecomm hε hamb
  exact (norm_commutator_le_generatedUltrapowerOperator τB hB ω trB L
    (canonicalGenerated_first_mem τQ trQ ι ψ) T x).trans hlocal

end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.KadisonSimilarity.original_symmetry_bound_of_free_corner_oai.{u_1, u_2, u_3, u_4} := @OAI.KadisonSimilarity.original_symmetry_bound_of_free_corner_oai.{u_1, u_2, u_3, u_4}
