-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.IsExt.cocycle_sub_mem_coboundaries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:05:17.373211+00:00
-- url     : https://prove2.me/submissions/a46f3788-97e3-4fc0-ac35-59979c4bf5f0

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
    {p : W →ₗ[LL] LL} (h : IsExt ρ ρ' i p) {c c' : G → V} (hc : IsCocycleOf ρ' i p c)
    (hc' : IsCocycleOf ρ' i p c') : c - c' ∈ B1 ρ := by
  obtain ⟨e, h1, he⟩ := hc
  obtain ⟨e', h1', he'⟩ := hc'
  obtain ⟨x, hx⟩ := (h.2.1 (e - e')).mp (by rw [map_sub, h1, h1', sub_self])
  refine ⟨x, funext fun g => h.1 ?_⟩
  change i (ρ g x - x) = i (c g - c' g)
  rw [map_sub, map_sub, h.2.2.2.1, hx, map_sub, he, he']
  abel
end IsExt
end GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions
