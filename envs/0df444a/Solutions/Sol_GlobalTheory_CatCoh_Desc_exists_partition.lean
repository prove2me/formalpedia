-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.exists_partition
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:37.750619+00:00
-- url     : https://prove2.me/submissions/a384363b-a262-4fa7-ac5a-7f506611c455

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Filter
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.Desc
universe v u w
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F} (H : HasLoc F) {T : C} {ι : Type} [Fintype ι] {b : ι → F.obj T}
  (hb : Ideal.span (Set.range b) = ⊤)
include hb
namespace GlobalTheory.CatCoh.Desc
theorem _root_.solution (N : ℕ) : ∃ r : ι → F.obj T, ∀ S (u : T ⟶ S),
    ∑ l, mp F u (r l) * mp F u (b l) ^ N = 1 := by
  have := Ideal.span_pow_eq_top _ hb N
  rw [← Set.range_comp, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun] at this
  obtain ⟨r, hr⟩ := this
  refine ⟨r, fun S u ↦ ?_⟩
  simpa using congrArg (mp F u) hr
end GlobalTheory.CatCoh.Desc
