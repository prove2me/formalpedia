-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.CongUnit.eq_zero_of_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:13:59.28811+00:00
-- url     : https://prove2.me/submissions/989d06d6-bd51-442c-843f-e775da355ab6

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceEndomorphismInverseExists
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_CongUnit_exists_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori GlobalTheory.CompanionTheory.Iwahori.CongUnit
variable {L V : Type} [NontriviallyNormedField L] [IsUltrametricDist L] [AddCommGroup V]
  [Module L V]
namespace GlobalTheory.CompanionTheory.Iwahori.CongUnit
theorem _root_.solution {m : ℕ} (b : Module.Basis (Fin m) L V) {Λ : AddSubgroup V}
    (hb : ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {π : L} (hπ : ‖π‖ < 1)
    {g : Module.End L V} (hg : g ∈ congJ Λ π) {x : V} (h0 : (1 + g) x = 0) : x = 0 := by
  by_contra hx
  obtain ⟨i, -, hc, hn⟩ := exists_coord b hb hπ hg hx
  rw [h0, map_zero, Finsupp.zero_apply, norm_zero] at hn
  exact hc (norm_eq_zero.mp hn.symm)
end GlobalTheory.CompanionTheory.Iwahori.CongUnit
