-- Prove2me | solution 1 for GroundTheory.GroupCoh.homologyMap_tateZeroClass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:01:52.43051+00:00
-- url     : https://prove2.me/submissions/60acca81-9de2-42d8-9ba6-60e7b6df0d54

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_TateZeroClass
import Theorems.Thm_P2M_GroundTheory_GroupCoh_tateZeroClass_eq_homology__afc98be0d3f9
import Theorems.Thm_GroundTheory_GroupCoh_exists_tateComplex_cycles_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution {H : Type u} [Group H] [Fintype H] {M : Rep.{u} k G}
    {N : Rep.{u} k H} (f : tateComplex M ⟶ tateComplex N) (x : M.ρ.invariants)
    (y : N.ρ.invariants)
    (h : (f.f 0).hom ((cochainsIso₀ M).inv.hom x) = (cochainsIso₀ N).inv.hom y) :
    (HomologicalComplex.homologyMap f 0).hom (tateZeroClass M x) = tateZeroClass N y := by
  obtain ⟨z, hz⟩ := exists_tateComplex_cycles_zero M x
  rw [tateZeroClass_eq_homologyπ M z x hz.symm]
  have e1 := congr(($(HomologicalComplex.homologyπ_naturality f 0)).hom z)
  have e2 := congr(($(HomologicalComplex.cyclesMap_i f 0)).hom z)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e1 e2
  rw [e1]
  refine (tateZeroClass_eq_homologyπ N _ y ?_).symm
  rw [e2, hz, h]
end GroundTheory.GroupCoh
