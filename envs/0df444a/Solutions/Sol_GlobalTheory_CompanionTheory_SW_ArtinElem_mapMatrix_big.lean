-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ArtinElem.mapMatrix_big
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:44:14.246316+00:00
-- url     : https://prove2.me/submissions/4d18cafc-3910-4f52-8a21-787ba09282d7

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixTransvectionDiagonalDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArtinElem_mapMatrix_prod_same
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArtinElem_mapMatrix_prod_ne

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
theorem _root_.solution (e : K ≃+* ∀ m, F m) (T : ∀ m, List (TransvectionStruct ι (F m)))
    (m' : M) (l : List M) (hl : l.Nodup) :
    (coord e m').mapMatrix (((big e T l).map TransvectionStruct.toMatrix).prod) =
      if m' ∈ l then ((T m').map TransvectionStruct.toMatrix).prod else 1 := by
  induction l with
  | nil => simp [big]
  | cons m l ih =>
    have ih' := ih (List.nodup_cons.mp hl).2
    have hm : m ∉ l := (List.nodup_cons.mp hl).1
    have hb : big e T (m :: l) = (T m).map (liftT e m) ++ big e T l := by simp [big]
    rw [hb, List.map_append, List.prod_append, map_mul, ih']
    by_cases h : m' = m
    · subst h
      rw [mapMatrix_prod_same]
      simp [hm]
    · rw [mapMatrix_prod_ne e h, one_mul]
      simp [h]
end GlobalTheory.CompanionTheory.SW.ArtinElem
