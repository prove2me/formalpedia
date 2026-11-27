-- Prove2me | solution 1 for GlobalTheory.cube_cone_of_faces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:36:49.346889+00:00
-- url     : https://prove2.me/submissions/ca96bd9a-0e76-4632-8fbb-ca7ecb93f62c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Theorems.Thm_P2M_GlobalTheory_cubeFaceSequence___7c5bb83f318b
import Theorems.Thm_GlobalTheory_quasiIso_cubeComplexMap_of_faces
import Theorems.Thm_GlobalTheory_cubeComplex_acyclic_of_bijective
import Theorems.Thm_GlobalTheory_cubeComplex_acyclic_iff_cech

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex
universe v u
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
namespace GlobalTheory
theorem _root_.solution {κ : Type} [LinearOrder κ] {e : κ ↪o ι} {i : ι}
    (he : Set.range e = {i}ᶜ) (A : Cube.{v} ι R) :
    (∃ hS : (ShortComplex.mk (cubeUpperIncl he A) (cubeLowerProj e A)
        (cubeFaceSequence he A).zero).ShortExact,
      (∀ p, Nonempty ((cubeFaceSequence he A).map (eval _ _ p)).Splitting) ∧
      ∀ p, hS.δ p (p + 1) rfl ≫
          (shiftSuccHomologyIso (cubeComplex (Cube.upperFace e i A)) p).hom =
        (-1 : ℤ) ^ p • homologyMap (cubeComplexMap (Cube.faceMap e i A)) p) ∧
    ((∀ s : Finset ι, i ∉ s → Function.Bijective (Cube.res A (Finset.subset_insert i s))) →
      (cubeComplex A).Acyclic) ∧
    (∀ (B : Cube.{v} ι R) (φ : A ⟶ B), QuasiIso (cubeComplexMap (Cube.lowerFaceMap e φ)) →
      QuasiIso (cubeComplexMap (Cube.upperFaceMap e i φ)) → QuasiIso (cubeComplexMap φ)) ∧
    ((cubeComplex A).Acyclic ↔
      IsIso (cechAugHomology A) ∧ ∀ p, IsZero ((cechComplex A).homology (p + 1))) :=
  ⟨⟨cubeFaceSequence_shortExact he A, fun p => ⟨cubeFaceSplitting he A p⟩,
      cubeFaceSequence_δ he A⟩,
    cubeComplex_acyclic_of_bijective A i, fun _ φ => quasiIso_cubeComplexMap_of_faces he φ,
    cubeComplex_acyclic_iff_cech A⟩
end GlobalTheory
