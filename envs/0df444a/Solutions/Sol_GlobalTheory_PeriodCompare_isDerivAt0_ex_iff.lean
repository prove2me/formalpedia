-- Prove2me | solution 1 for GlobalTheory.PeriodCompare.isDerivAt0_ex_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:07:07.486145+00:00
-- url     : https://prove2.me/submissions/253e5ea4-8f46-4ab7-a80c-9ae7c4e323ad

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDerivAt0NotIsDerivAlong
import Theorems.Thm_GlobalTheory_PeriodCompare_isHolTo_iff
import Theorems.Thm_GlobalTheory_PeriodCompare_isDerivAt0_iff
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n)
namespace GlobalTheory.PeriodCompare
theorem _root_.solution {P : (Fu.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (Fu.Di i) ty P) (w : Fin g → ℂ)
    (v : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left) :
    IsDerivAt0 (fun z => (Fu.ex i P z).left) w v ↔ IsDerivAlong (fun z => (Fu.ex i P z).left) w v := by
  have h := (Fu.hol i 0 Set.univ (fun _ => P) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  refine isDerivAt0_iff Filter.univ_mem ((isHolTo_iff _ _).1 fun U f => ⟨?_, ?_⟩).2 w v
  · simpa using (h U f).1.preimage (f := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
  · exact (h U f).2.comp (f := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
      fun z hz => ⟨⟨trivial, trivial⟩, hz.2⟩
end GlobalTheory.PeriodCompare
