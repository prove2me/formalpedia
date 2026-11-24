-- Prove2me | solution 1 for GlobalTheory.isZero_homology_extendScalars_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:11:33.908799+00:00
-- url     : https://prove2.me/submissions/d12bfbac-a9bc-4606-a830-768fb91013a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Function
open GlobalTheory
open CategoryTheory Category Limits
universe u w
variable {R : Type u} [CommRing R] {ι : Type*} {c : ComplexShape ι}
namespace GlobalTheory
theorem _root_.solution (S : Type w) [CommRing S] [inst : Algebra R S]
    (K : HomologicalComplex (ModuleCat.{u} R) c) {p q r : ι} (hp : c.prev q = p)
    (hr : c.next q = r) :
    IsZero ((((ModuleCat.extendScalars.{u, w, u} (algebraMap R S)).mapHomologicalComplex c).obj
        K).homology q) ↔
      Exact ((K.d p q).hom.lTensor S) ((K.d q r).hom.lTensor S) := by
  obtain ⟨φ, rfl⟩ : ∃ φ : R →+* S, φ.toAlgebra = inst := ⟨_, toAlgebra_algebraMap⟩
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ p q r hp hr,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  rfl
end GlobalTheory
