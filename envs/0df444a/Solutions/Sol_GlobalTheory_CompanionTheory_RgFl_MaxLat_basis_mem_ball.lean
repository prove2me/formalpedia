-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgFl.MaxLat.basis_mem_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:08:28.190184+00:00
-- url     : https://prove2.me/submissions/6c04331b-1839-4f83-8b4f-de65f89c920a

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
theorem _root_.solution {ι : Type} [DecidableEq ι] (b : Module.Basis ι L V) (j : ι) :
    b j ∈ ball b := by
  intro i
  rw [b.repr_self, Finsupp.single_apply]
  split_ifs <;> simp
end GlobalTheory.CompanionTheory.RgFl.MaxLat
