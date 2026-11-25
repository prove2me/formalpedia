-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.cellJacquetMap_parabolicInd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:26:21.481424+00:00
-- url     : https://prove2.me/submissions/30e0a7d3-28fd-4dc2-8cef-c6a20ccdb4d4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellSurjective
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellJacquet_parabolicInd
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_coe_cellJacquetMap_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_supportedIn_le_comap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}
variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
  (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y)
include hYo hCY hYQ
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (f : supportedIn σ Y) (m : levi F n γ) :
    cellJacquetMap γ w σ hYo hCY ⟨parabolicInd F n β σ m f,
      supportedIn_le_comap γ hYQ (levi_le_blockUpper m.2) f.2⟩ =
      indRep (cellLeviSub F β γ w) (cellInducing β γ w σ) m (cellJacquetMap γ w σ hYo hCY f) := by
  apply Subtype.ext
  funext x
  rw [coe_indRep_apply, coe_cellJacquetMap_apply, coe_cellJacquetMap_apply]
  exact cellJacquet_parabolicInd σ f m x
end GroundTheory.Automorphic.Parabolic
