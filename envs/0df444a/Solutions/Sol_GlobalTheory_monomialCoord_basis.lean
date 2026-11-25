-- Prove2me | solution 1 for GlobalTheory.monomialCoord_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:49:46.547364+00:00
-- url     : https://prove2.me/submissions/c343c3eb-b5c4-48cc-8d64-c1378b89f88c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfMonomialBasis
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
noncomputable section
open GlobalTheory
variable {ι : Type} (R : Type) [CommRing R]
variable {R}
namespace GlobalTheory
theorem _root_.solution {κ : Type} [DecidableEq κ] (T : κ → Finset ι) {s : Finset ι} {M : Type}
    [AddCommGroup M] [Module R M] (b : Module.Basis {a : κ // T a ⊆ s} R M)
    (a : {a : κ // T a ⊆ s}) :
    monomialCoord T b (b a) =
      DirectSum.lof R κ (fun a => PLift (T a ⊆ s) →₀ R) a.1 (Finsupp.single ⟨a.2⟩ 1) := by
  simp only [monomialCoord, LinearEquiv.trans_apply, Module.Basis.repr_self, Finsupp.domLCongr_single]
  exact sigmaFinsuppEquivDFinsupp_single _ _
end GlobalTheory
