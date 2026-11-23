-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlWitt.h_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:42.809138+00:00
-- url     : https://prove2.me/submissions/8b0f0948-64e4-4562-a36e-821952974b79

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittExtensionTheorem
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WittStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_h_zero_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FlWitt
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L} {δ : L} {l : ℕ}
namespace GlobalTheory.CompanionTheory.FlWitt
theorem _root_.solution (hh : IsHerm s h) {ι : Type} (t : Finset ι) (x : V) (c : ι → L) (v : ι → V) :
    h x (∑ i ∈ t, c i • v i) = ∑ i ∈ t, c i * h x (v i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using h_zero_right hh x
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hh.1, hh.2.1, ih]
end GlobalTheory.CompanionTheory.FlWitt
