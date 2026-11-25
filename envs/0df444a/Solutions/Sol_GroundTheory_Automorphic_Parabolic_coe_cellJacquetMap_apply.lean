-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.coe_cellJacquetMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:01:08.656332+00:00
-- url     : https://prove2.me/submissions/2fc02732-d88e-49b7-9d88-5b2dd3feb8c2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCount
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell

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
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)}
variable {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
include hYo hCY
variable (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (f : supportedIn σ Y) (m : levi F n γ) :
    (cellJacquetMap γ w σ hYo hCY f : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) m =
      cellJacquet γ w σ (f : parabolicIndSpace F n β σ) m := rfl
end GroundTheory.Automorphic.Parabolic
