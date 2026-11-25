-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient.phiDelta_transform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:55:37.479488+00:00
-- url     : https://prove2.me/submissions/c69e36ff-2aef-43ac-8dd4-8ece244ddc4c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelIndexFourierCharacter
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NsmulMemSmulTop
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_DeltaDatumCombinedCoefficient

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
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {a : IsAuxiliarySplitSquarefreeLevel l}
variable {F : Type} [Field F]
namespace GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient
theorem _root_.solution (δ : DeltaChar a F) (v : Vol D a) {n : ℕ} (k : D.La →ₗ[𝓞 E] D.La) (d : (𝓞 E ⧸ a.conj)ˣ)
    (hd : IsDetMod D a.conj k d) (u : Fin n → D.La) :
    phiDelta δ v (fun b => Submodule.Quotient.mk (u b)) =
      δ.loc (a.barQuot d) * phiDelta δ v (fun b => Submodule.Quotient.mk (k (u b))) := by
  have h : v.det₁ (fun b => (Submodule.Quotient.mk (k (u b)) : ConjCl D a.l₂)) =
      d * v.det₁ (fun b => (Submodule.Quotient.mk (u b) : ConjCl D a.l₂)) := by
    unfold Vol.det₁
    split_ifs with h
    · exact hd (v.ω.compLinearMap (Submodule.mkQ _)) fun i => u (Fin.castLE h i)
    · rw [mul_zero]
  have hu : IsUnit (a.barQuot d) := d.isUnit.map _
  rw [phiDelta, phiDelta, h, map_mul, map_mul, ← _root_.mul_assoc, ← MulChar.mul_apply, mul_inv_cancel,
    MulChar.one_apply hu, _root_.one_mul]
end GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient
