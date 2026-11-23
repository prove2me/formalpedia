-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgFl.MaxLat.herm_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:59.235501+00:00
-- url     : https://prove2.me/submissions/4529f23f-b592-47f0-b74d-20e7ee2c9dc5

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistenceOfSandwichStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgFl GlobalTheory.CompanionTheory.RgFl.MaxLat
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
  {V : Type} [AddCommGroup V] [Module L V]
namespace GlobalTheory.CompanionTheory.RgFl.MaxLat
theorem _root_.solution {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) {ι : Type} [Fintype ι]
    (b : Module.Basis ι L V) (z y : V) : h z y = ∑ j, b.repr y j * h z (b j) := by
  calc h z y = hLin hh z y := rfl
    _ = hLin hh z (∑ j, b.repr y j • b j) := by rw [b.sum_repr]
    _ = ∑ j, b.repr y j * h z (b j) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul]
      rfl
end GlobalTheory.CompanionTheory.RgFl.MaxLat
