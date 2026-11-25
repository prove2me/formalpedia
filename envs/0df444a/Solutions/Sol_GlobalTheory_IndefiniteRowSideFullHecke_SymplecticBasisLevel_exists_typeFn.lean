-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel.exists_typeFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:53:51.967028+00:00
-- url     : https://prove2.me/submissions/f3d60ee4-14f3-4370-93ac-37690e9591c1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_SymplecticBasisLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel
theorem _root_.solution (D : Datum H) : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn D ty := by
  classical
  let S := Σ τ : E →+* ℂ, Fin (sigMult D τ)
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  refine ⟨Fintype.card S, fun i => (e i).1, fun τ => ?_⟩
  have e₁ : {i : Fin (Fintype.card S) // (e i).1 = τ} ≃ {s : S // s.1 = τ} :=
    e.subtypeEquiv (fun _ => Iff.rfl)
  have e₂ : {s : S // s.1 = τ} ≃ Fin (sigMult D τ) := Equiv.sigmaSubtype τ
  rw [Nat.card_congr (e₁.trans e₂)]
  simp
end GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel
