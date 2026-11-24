-- Prove2me | solution 1 for GlobalTheory.PeriodCompare.isTypeFn_of_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:24:28.603197+00:00
-- url     : https://prove2.me/submissions/75bdb19e-810f-479c-bc04-6ec378fcb92e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDerivAt0NotIsDerivAlong
import Theorems.Thm_GlobalTheory_PeriodCompare_isTypeFn_iff
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_PeriodNonempty_exists_equiv_of_sum_eq
import Theorems.Thm_GlobalTheory_PeriodNonempty_sum_type
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PeriodCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation hiding IsTypeFn IsThetaFrame
open scoped TensorProduct Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.PeriodCompare
theorem _root_.solution (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (h : ∀ a : 𝓞 E, ∑ i, ty i (a : E) = sigTrace D a) : IndefiniteRowSideFullHecke.PeriodMapPresentation.IsTypeFn D ty := by
  classical
  let κ := Σ τ : E →+* ℂ, Fin (sigMult D τ)
  let ε := Fintype.equivFin κ
  have h0 : IndefiniteRowSideFullHecke.PeriodMapPresentation.IsTypeFn D (fun k => (ε.symm k).1) := fun τ => by
    rw [Nat.card_congr (ε.symm.subtypeEquiv (q := fun x : κ => x.1 = τ) fun _ => Iff.rfl),
      Nat.card_congr (Equiv.sigmaSubtype τ)]
    simp
  obtain ⟨e, he⟩ := PeriodNonempty.exists_equiv_of_sum_eq ty (fun k => (ε.symm k).1) fun a => by
    rw [h, PeriodNonempty.sum_type H ((isTypeFn_iff D _).2 h0)]
    rfl
  intro τ
  rw [← h0 τ]
  exact Nat.card_congr (e.subtypeEquiv fun i => by rw [← he i])
end GlobalTheory.PeriodCompare
