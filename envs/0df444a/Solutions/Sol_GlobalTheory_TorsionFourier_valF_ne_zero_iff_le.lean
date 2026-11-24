-- Prove2me | solution 1 for GlobalTheory.TorsionFourier.valF_ne_zero_iff_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:38:51.481874+00:00
-- url     : https://prove2.me/submissions/159bd049-91ac-4ae0-a4c1-bfdac0e697a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsPartPartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPointTranslatePure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinsuppEqZeroOfSumTorsionCharactersEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PartVanishesOnTorusTorsionFourier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.TorsionFourier
variable {F : Type} [Field F] {X : Scheme.{0}} {x : Sp F ⟶ X} {U : X.Opens}
namespace GlobalTheory.TorsionFourier
theorem _root_.solution (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) :
    valF x U a ≠ 0 ↔ ⊤ ≤ x ⁻¹ᵁ X.basicOpen a := by
  have e1 := Scheme.basicOpen_appLE x ⊤ U h a
  rw [top_inf_eq] at e1
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a) = (x.appLE U ⊤ h).hom a := by
    rw [valF, dif_pos h]
    exact (Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply _
  have e3 : x ⁻¹ᵁ X.basicOpen a =
      (Sp F).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a)) := by
    rw [e2]; exact e1.symm
  rw [e3]
  constructor
  · intro hne
    exact (Scheme.basicOpen_of_isUnit _ ((Ne.isUnit hne).map _)).ge
  · intro hle h0
    rw [h0, map_zero, Scheme.basicOpen_zero] at hle
    exact hle (show (IsLocalRing.closedPoint F : Sp F) ∈ (⊤ : (Sp F).Opens) from trivial)
end GlobalTheory.TorsionFourier
