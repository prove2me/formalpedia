-- Prove2me | solution 1 for GlobalTheory.Cube.nonempty_extendScalars_iso_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:36.027141+00:00
-- url     : https://prove2.me/submissions/5443efaa-1613-4bcf-b4ec-168cc606c29e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexOfNoetherianModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory
namespace GlobalTheory
namespace Cube
theorem _root_.solution {ι : Type} {R₀ R : Type} [CommRing R₀]
    [CommRing R] [inst : Algebra R₀ R] (C : Cube.{0} ι R₀) :
    Nonempty (C ⋙ ModuleCat.extendScalars.{0, 0, 0} (algebraMap R₀ R) ≅ Cube.baseChange R C) := by
  obtain ⟨f, rfl⟩ : ∃ f : R₀ →+* R, inst = f.toAlgebra := ⟨_, toAlgebra_algebraMap.symm⟩
  exact ⟨NatIso.ofComponents (fun s => Iso.refl _) fun h => by
    rw [Iso.refl_hom, Iso.refl_hom]
    exact (Category.comp_id _).trans (Category.id_comp _).symm⟩
end Cube
end GlobalTheory
