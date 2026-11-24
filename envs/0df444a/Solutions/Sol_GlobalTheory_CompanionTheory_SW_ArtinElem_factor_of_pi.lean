-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ArtinElem.factor_of_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:03:45.835919+00:00
-- url     : https://prove2.me/submissions/cbde6b02-38e7-43fa-8a2c-b62c47a15a72

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixTransvectionDiagonalDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArtinElem_mapMatrix_big
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArtinElem_matrix_ext_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ArtinElem
variable {K K' : Type*} [CommRing K] [CommRing K'] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : Type*} [DecidableEq M] {F : M → Type*} [∀ m, CommRing (F m)]
namespace GlobalTheory.CompanionTheory.SW.ArtinElem
theorem _root_.solution [Fintype M] (e : K ≃+* ∀ m, F m)
    (hF : ∀ (m : M) (A : Matrix ι ι (F m)),
      ∃ (L L' : List (TransvectionStruct ι (F m))) (D : ι → F m),
        A = (L.map TransvectionStruct.toMatrix).prod * diagonal D *
          (L'.map TransvectionStruct.toMatrix).prod)
    (A : Matrix ι ι K) :
    ∃ (L L' : List (TransvectionStruct ι K)) (D : ι → K),
      A = (L.map TransvectionStruct.toMatrix).prod * diagonal D *
        (L'.map TransvectionStruct.toMatrix).prod := by
  choose L L' D hD using fun m => hF m ((coord e m).mapMatrix A)
  refine ⟨big e L Finset.univ.toList, big e L' Finset.univ.toList,
    fun i => e.symm (fun m => D m i), matrix_ext_coord e fun m => ?_⟩
  have hnd := Finset.nodup_toList (Finset.univ : Finset M)
  have hdiag : (coord e m).mapMatrix (diagonal fun i => e.symm (fun m => D m i)) =
      diagonal (D m) := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [coord]
    · simp [hab]
  rw [map_mul, map_mul, mapMatrix_big e L m _ hnd, mapMatrix_big e L' m _ hnd, hdiag]
  simpa using hD m
end GlobalTheory.CompanionTheory.SW.ArtinElem
