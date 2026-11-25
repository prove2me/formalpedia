-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.IsExt.exists_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:58:57.937045+00:00
-- url     : https://prove2.me/submissions/f19b1ec8-e8d7-4fa6-95d5-46569879e2a9

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
    {p : W →ₗ[LL] LL} (h : IsExt ρ ρ' i p) : ∃ c : G → V, IsCocycleOf ρ' i p c := by
  obtain ⟨-, hex, hs, -, hp⟩ := h
  obtain ⟨e, he⟩ := hs 1
  have : ∀ g, ∃ x, i x = ρ' g e - e := fun g => (hex _).mp (by rw [map_sub, hp, sub_self])
  choose c hc using this
  exact ⟨c, e, he, fun g => by rw [hc]; abel⟩
end IsExt
end GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions
