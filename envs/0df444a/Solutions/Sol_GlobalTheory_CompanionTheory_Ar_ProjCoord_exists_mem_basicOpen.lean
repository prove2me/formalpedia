-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.ProjCoord.exists_mem_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:41:12.381698+00:00
-- url     : https://prove2.me/submissions/c1b70964-86cb-4df4-89c1-73fbf094e078

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_ZarhinBundleKernelFirstCoordEquations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.ProjCoord
open MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
variable {o κ Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
namespace GlobalTheory.CompanionTheory.Ar.ProjCoord
theorem _root_.solution (q : Proj (homogeneousSubmodule κ o)) :
    ∃ c, q ∈ Proj.basicOpen (homogeneousSubmodule κ o) (X c) := by
  have h := Proj.iSup_basicOpen_eq_top' (homogeneousSubmodule κ o) (fun c : κ => X c)
    (fun c => ⟨1, X_mem c⟩) (by
      rw [eq_top_iff]
      rintro g -
      induction g using MvPolynomial.induction_on with
      | C r => exact Subalgebra.algebraMap_mem _ (⟨C r, isHomogeneous_C κ r⟩ : homogeneousSubmodule κ o 0)
      | add p q hp hq => exact add_mem hp hq
      | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩))
  exact TopologicalSpace.Opens.mem_iSup.1 (h.ge (Set.mem_univ q))
end GlobalTheory.CompanionTheory.Ar.ProjCoord
