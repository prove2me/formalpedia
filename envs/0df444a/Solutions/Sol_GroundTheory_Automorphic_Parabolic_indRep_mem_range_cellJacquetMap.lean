-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.indRep_mem_range_cellJacquetMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:32:16.174418+00:00
-- url     : https://prove2.me/submissions/18ed8b10-044e-47df-bcd6-3fe7187bb54b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellSurjective
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellJacquetMap_parabolicInd

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
theorem _root_.solution (m : levi F n γ)
    {ψ : indSpace (cellLeviSub F β γ w) (cellInducing β γ w σ)}
    (hψ : ψ ∈ LinearMap.range (cellJacquetMap γ w σ hYo hCY)) :
    indRep (cellLeviSub F β γ w) (cellInducing β γ w σ) m ψ ∈
      LinearMap.range (cellJacquetMap γ w σ hYo hCY) := by
  obtain ⟨f, rfl⟩ := hψ
  exact ⟨_, cellJacquetMap_parabolicInd hYo hCY hYQ f m⟩
end GroundTheory.Automorphic.Parabolic
