-- Prove2me | solution 1 for GroundTheory.GroupCoh.exists_cycles_of_moduleLeftHomologyData
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:09:57.252495+00:00
-- url     : https://prove2.me/submissions/49c6f1ef-18c1-4a60-8392-d02b16046a2c

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ModuleHomologyData

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
open CategoryTheory Limits
universe u
variable {R : Type u} [CommRing R]
namespace GroundTheory.GroupCoh
theorem _root_.solution {ιc : Type*} {c : ComplexShape ιc}
    (C : HomologicalComplex (ModuleCat.{u} R) c) (i j k : ιc) (hi : c.prev j = i)
    (hk : c.next j = k) (K : Type u) [AddCommGroup K] [Module R K]
    (ι : K →ₗ[R] (C.sc' i j k).X₂) (hι : Function.Injective ι)
    (hrange : LinearMap.range ι = LinearMap.ker (C.sc' i j k).g.hom) (N : Submodule R K)
    (hN : ∀ x, x ∈ N ↔ ι x ∈ LinearMap.range (C.sc' i j k).f.hom) (x : K) :
    ∃ z : C.cycles j, (C.iCycles j).hom z = ι x := by
  set e := (HomologicalComplex.natIsoSc' (ModuleCat.{u} R) c i j k hi hk).inv.app C
  set h := moduleLeftHomologyData _ K ι hι hrange N hN
  refine ⟨(ShortComplex.cyclesMap e).hom (h.cyclesIso.inv.hom x), ?_⟩
  have h3 : (C.sc j).iCycles.hom ((ShortComplex.cyclesMap e).hom (h.cyclesIso.inv.hom x)) =
      e.τ₂.hom ((C.sc' i j k).iCycles.hom (h.cyclesIso.inv.hom x)) :=
    congr(($(ShortComplex.cyclesMap_i e)).hom (h.cyclesIso.inv.hom x))
  have h4 : (C.sc' i j k).iCycles.hom (h.cyclesIso.inv.hom x) = ι x :=
    congr(($(h.cyclesIso_inv_comp_iCycles)).hom x)
  refine h3.trans ?_
  rw [h4]
  simp [e]
  rfl
end GroundTheory.GroupCoh
