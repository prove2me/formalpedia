-- Prove2me | solution 1 for GlobalTheory.cubeComplex_exactAt_of_monomialBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:58:43.794018+00:00
-- url     : https://prove2.me/submissions/3bcd63fb-a055-40a7-9b78-c61faa352c66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfMonomialBasis
import Theorems.Thm_GlobalTheory_cubeComplex_above_exactAt
import Theorems.Thm_GlobalTheory_monomialCoord_basis
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_cubeComplex_directSum_exactAt_iff
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
theorem _root_.solution (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (κ : Type) (T : κ → Finset ι) (A : Cube.{0} ι R)
    (b : ∀ s : Finset ι, Module.Basis {a : κ // T a ⊆ s} R (A.obj s))
    (hb : ∀ (s t : Finset ι) (h : s ⊆ t) (a : {a : κ // T a ⊆ s}),
      Cube.res A h (b s a) = b t ⟨a.1, a.2.trans h⟩)
    (p : ℕ) (hp : p ≠ Fintype.card ι) : (cubeComplex A).ExactAt p := by
  classical
  let e : A ≅ Cube.directSum fun a => Cube.above R (T a) :=
    Cube.isoMk (fun s => monomialCoord T (b s)) fun {s t} h x => by
      have : (monomialCoord T (b t)).toLinearMap ∘ₗ Cube.res A h =
          (DirectSum.lmap fun a => Finsupp.lmapDomain R R
            fun x : PLift (T a ⊆ s) => (⟨x.down.trans h⟩ : PLift (T a ⊆ t))) ∘ₗ
            (monomialCoord T (b s)).toLinearMap := by
        refine (b s).ext fun a => ?_
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hb, monomialCoord_basis,
          DirectSum.lmap_lof, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      exact congr($this x)
  exact (exactAt_iff_of_quasiIsoAt ((cubeFunctor ι R).mapIso e).hom p).2
    ((cubeComplex_directSum_exactAt_iff _ p).2 fun a => cubeComplex_above_exactAt R (T a) hp)
end GlobalTheory
