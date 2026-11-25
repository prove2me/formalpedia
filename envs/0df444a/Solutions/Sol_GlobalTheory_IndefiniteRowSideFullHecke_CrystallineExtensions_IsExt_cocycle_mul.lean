-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.IsExt.cocycle_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:53:04.117642+00:00
-- url     : https://prove2.me/submissions/98bc1b41-df32-42b1-a8ff-ac6107304bce

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineExtensions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct
variable {G : Type} [Group G] {LL : Type} [Field LL] {V W : Type} [AddCommGroup V] [Module LL V]
  [AddCommGroup W] [Module LL W]
namespace GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions
namespace IsExt
theorem _root_.solution {ρ : Representation LL G V} {ρ' : Representation LL G W} {i : V →ₗ[LL] W}
    {p : W →ₗ[LL] LL} (h : IsExt ρ ρ' i p) {c : G → V} (hc : IsCocycleOf ρ' i p c) (g k : G) :
    c (g * k) = c g + ρ g (c k) := by
  obtain ⟨e, -, he⟩ := hc
  apply h.1
  have h1 := he (g * k)
  rw [map_mul, Module.End.mul_apply, he k, map_add, he g, ← h.2.2.2.1, add_assoc] at h1
  rw [map_add]
  exact (add_left_cancel h1).symm
end IsExt
end GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions
