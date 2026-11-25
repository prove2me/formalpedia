-- Prove2me | solution 1 for GlobalTheory.AbLaw.CechOne.exists_triple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:37:57.902826+00:00
-- url     : https://prove2.me/submissions/dcfdd1a8-378e-4837-9148-ce7bf02b5684

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CechOne
open SecOn
variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable {M : LB X}
namespace GlobalTheory.AbLaw.CechOne
theorem _root_.solution {κ : Type} [LinearOrder κ] {t : Finset κ} (ht : t.card = 3) :
    ∃ i j k, i < j ∧ j < k ∧ t = {i, j, k} := by
  refine ⟨t.orderEmbOfFin ht 0, t.orderEmbOfFin ht 1, t.orderEmbOfFin ht 2,
    (t.orderEmbOfFin ht).strictMono (by decide), (t.orderEmbOfFin ht).strictMono (by decide), ?_⟩
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨n, rfl⟩ := (Finset.range_orderEmbOfFin t ht).ge (Finset.mem_coe.2 hx)
    fin_cases n <;> simp
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> exact Finset.orderEmbOfFin_mem _ _ _
end GlobalTheory.AbLaw.CechOne
