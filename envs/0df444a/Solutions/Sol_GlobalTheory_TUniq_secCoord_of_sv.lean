-- Prove2me | solution 1 for GlobalTheory.TUniq.secCoord_of_sv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:06:34.420561+00:00
-- url     : https://prove2.me/submissions/701c61b4-71ab-4128-8ec5-8f4c9a586a34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCompatOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSegreCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordOfRatio
import Theorems.Thm_GlobalTheory_TUniq_secCoord_of_ratio
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_linComb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.TUniq
open GlobalTheory.SegreCoord ReciprocityTheory.ChartRestriction.G.Out
variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {S S' : Scheme.{0}} {s : S ⟶ Sp o}
  {s' : S' ⟶ Sp o}
namespace GlobalTheory.TUniq
theorem _root_.solution {A : Over S} [GrpObj A] {A' : Over S'} [GrpObj A'] {L : LB A.left} {L' : LB A'.left}
    (hL' : L'.IsLB) {a a' : ℤ} {T : Over S} {T' : Over S'} {σ : Type} {th : σ → LB.Sec (LPow A L a T)}
    {th' : σ → LB.Sec (LPow A' L' a' T')} {B : Type} [Field B] {x : Sp B ⟶ (T ⊗ A).left}
    {x' : Sp B ⟶ (T' ⊗ A').left} (p : Sp B) {I I'} (hI : Good L p I) (hI' : Good L' p I')
    (c : ((Sp B).presheaf.stalk p)ˣ)
    (h : ∀ i, VVRank.sv A' (th' i) x' p I' = c * VVRank.sv A (th i) x p I) {v : σ → B}
    (H : SecCoord _ th x v) : SecCoord _ th' x' v :=
  secCoord_of_ratio (LB.isLB_linComb hL' _ _) p (hI.mem (fun _ : Fin 1 => (snd T A).left) x)
    (hI'.mem (fun _ : Fin 1 => (snd T' A').left) x') c h H
end GlobalTheory.TUniq
