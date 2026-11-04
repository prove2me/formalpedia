-- Prove2me | solution 1 for OAI.KadisonSimilarity.TracialHeadCoordinates.vacuum_hasOrthogonalProjection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:30:29.319202+00:00
-- url     : https://prove2.me/submissions/46c47256-c2b1-4348-990e-24d2b2a09da3

import Mathlib
import Definitions.Def_OAIQ075A024

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorHeadSlices
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Vacuum coefficients of a head tensor action

The exceptional-projection formula in propagation follows from the actual
head action on the completed tensor product. It does not need to be assumed
separately for every vector or every term of the Haar sequence.
-/

noncomputable section
namespace KadisonSimilarity

open ContinuousLinearMap
open scoped TensorProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable [CompleteSpace E]

section Coordinates

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [CompleteSpace E] in
/-- The transported vacuum subspace also has its orthogonal projection. -/
theorem tracialVacuumSubspace_hasOrthogonalProjection
    (U : H ≃ₗᵢ[ℂ] HilbertTensor E F) (Ω : E) (hΩ : ‖Ω‖ = 1) :
    (tracialVacuumSubspace U Ω).HasOrthogonalProjection := by
  let := vacuumSubspace_hasOrthogonalProjection (F := F) Ω hΩ
  exact Submodule.HasOrthogonalProjection.map_linearIsometryEquiv'
    (vacuumSubspace (F := F) Ω) U.symm

end Coordinates
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialHeadCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exceptional projection in propagation, constructed from the tracial
head of the reduced-word decomposition and actual corner Haar powers. -/

noncomputable section
namespace KadisonSimilarity

variable {D P E H F : Type*} [CStarAlgebra D] [CStarAlgebra P]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

namespace TracialHeadCoordinates

variable {GD : TracialCornerGeometry D E} {G : TracialCornerGeometry P H}
  {ι : D →⋆ₐ[ℂ] P} (W : TracialHeadCoordinates GD G ι F)

/-- Orthogonal projection onto the exceptional subspace exists by the tensor
coordinates and trace normalization. -/
theorem vacuum_hasOrthogonalProjection_oai (hτ : GD.trace 1 = 1) :
    W.vacuum.HasOrthogonalProjection := by
  exact tracialVacuumSubspace_hasOrthogonalProjection W.unitary (GD.vector 1)
    (norm_tracialTraceVector GD.trace GD.vector GD.inner_vector hτ)

end TracialHeadCoordinates
end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.KadisonSimilarity.TracialHeadCoordinates.vacuum_hasOrthogonalProjection_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.KadisonSimilarity.TracialHeadCoordinates.vacuum_hasOrthogonalProjection_oai.{u_1, u_2, u_3, u_4, u_5}
