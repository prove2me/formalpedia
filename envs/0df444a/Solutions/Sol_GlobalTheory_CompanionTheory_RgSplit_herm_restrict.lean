-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgSplit.herm_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:09:40.503811+00:00
-- url     : https://prove2.me/submissions/5dc51c17-53ee-4781-911b-7a690c217f5d

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SplittingOfSandwichAndPairing
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_decomp

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgSplit
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
  {V : Type} [AddCommGroup V] [Module L V] {s : L →+* L} {h : V → V → L} {δ : L} {e f : V}
variable {U : Submodule L V}
namespace GlobalTheory.CompanionTheory.RgSplit
theorem _root_.solution (hh : IsHerm s h) (hδ : δ ≠ 0) (he : h e e = 0) (hf : h f f = 0)
    (hef : h e f = δ) (hU : ∀ x, x ∈ U ↔ h e x = 0 ∧ h f x = 0) :
    IsHerm s (fun x y : U => h x y) := by
  refine ⟨fun x y z => hh.1 _ _ _, fun a x y => hh.2.1 a _ _, fun x y => hh.2.2.1 _ _,
    fun x hx => Subtype.ext (hh.2.2.2 _ fun y => ?_)⟩
  have hx' := (hU x).1 x.2
  have hxe : h x e = 0 := by rw [hh.2.2.1 e x, hx'.1, map_zero]
  have hxf : h x f = 0 := by rw [hh.2.2.1 f x, hx'.2, map_zero]
  have hxp : h x (pr hh δ e f y) = 0 := hx ⟨_, (hU _).2 (pr_orth hh hδ he hf hef y)⟩
  rw [decomp hh δ e f y, hh.1, hh.1, hh.2.1, hh.2.1, hxe, hxf, hxp]
  simp
end GlobalTheory.CompanionTheory.RgSplit
