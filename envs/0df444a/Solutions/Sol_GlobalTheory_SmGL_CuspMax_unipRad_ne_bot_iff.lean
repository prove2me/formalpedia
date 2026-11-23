-- Prove2me | solution 1 for GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:39.434318+00:00
-- url     : https://prove2.me/submissions/6a8a4a19-33a1-4a04-ba73-b32f2a043c37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubsingletonJacquetOfPerm
import Theorems.Thm_GlobalTheory_SmGL_CuspMax_mem_unipRad_iff_entries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.CuspMax
variable {R : Type} [CommRing R] {α β n : Type} {m : α → Type} {m' : β → Type}
  [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype β] [LinearOrder β] [∀ a, Fintype (m' a)] [∀ a, DecidableEq (m' a)]
  [Fintype n] [DecidableEq n]
namespace GlobalTheory.SmGL.CuspMax
theorem _root_.solution [Nontrivial R] {e : (Σ a, m a) ≃ n} :
    unipRad R e ≠ ⊥ ↔ ∃ i j, blk e i < blk e j := by
  constructor
  · intro h
    by_contra hc
    refine h ((Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_)
    ext i j
    exact mem_unipRad_iff_entries.1 hu i j fun hij => hc ⟨i, j, hij⟩
  · rintro ⟨i, j, hij⟩ hb
    have hne : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hij
    let u : GL n R := ⟨Matrix.transvection i j 1, Matrix.transvection i j (-1),
      by rw [Matrix.transvection_mul_transvection_same _ _ hne]; simp,
      by rw [Matrix.transvection_mul_transvection_same _ _ hne]; simp⟩
    have hu : u ∈ unipRad R e := mem_unipRad_iff_entries.2 fun a b hab => by
      show Matrix.transvection i j (1 : R) a b = _
      rw [Matrix.transvection, Matrix.add_apply, Matrix.single_apply_of_ne, add_zero]
      rintro ⟨rfl, rfl⟩
      exact hab hij
    rw [hb, Subgroup.mem_bot] at hu
    have : Matrix.transvection i j (1 : R) i j = (1 : Matrix n n R) i j :=
      congrArg (fun g : GL n R => (g : Matrix n n R) i j) hu
    simp [Matrix.transvection] at this
end GlobalTheory.SmGL.CuspMax
