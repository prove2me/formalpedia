-- Prove2me | solution 1 for GlobalTheory.Doubling.mem_sumLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:46.33799+00:00
-- url     : https://prove2.me/submissions/d365e180-c198-4b6a-ab29-b93525c3dbb4

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : m ⊕ n ≃ ι)
variable [Fintype m] [Fintype n] [Fintype ι]
variable [DecidableEq m] [DecidableEq n] [DecidableEq ι]
omit [Fintype m] [Fintype n] [Fintype ι] [DecidableEq m] [DecidableEq n] [DecidableEq ι]
namespace GlobalTheory.Doubling
theorem _root_.solution {O X : Type} [CommRing O] [AddCommGroup X] [Module O X] {L : Submodule O (m → X)}
    {L' : Submodule O (n → X)} {w : ι → X} :
    w ∈ sumLat e L L' ↔ (fun i => w (e (.inl i))) ∈ L ∧ (fun i => w (e (.inr i))) ∈ L' := Iff.rfl
end GlobalTheory.Doubling
