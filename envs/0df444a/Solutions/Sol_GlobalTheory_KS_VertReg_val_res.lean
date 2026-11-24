-- Prove2me | solution 1 for GlobalTheory.KS.VertReg.val_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:34:17.484736+00:00
-- url     : https://prove2.me/submissions/449d9df2-214e-469a-a9dc-824ef6413fa5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueUniformisingVectorVerticalTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFibreCoordsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldAbelianVarietyAlgebraicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSectionOfLocallyRegularStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LocDerRegularCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.VertReg
private theorem valAt'_resG_of_le {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) {U V : Y.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V)
    (f : Γ(Y, U)) : valAt' x V (resG Y hVU f) = valAt' x U f := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := fun _ ha => hVU (h ha)
  unfold valAt'
  rw [dif_pos h, dif_pos h']
  unfold valAt
  exact congrArg (fun s => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom s)
    (congrArg (fun φ => CommRingCat.Hom.hom φ f) (Scheme.Hom.map_appLE x h (homOfLE hVU).op))
variable {R : Type} [CommRing R] {Y X : Scheme.{0}} {q : Y ⟶ Sp ℂ} {p : X ⟶ Sp R} {m : Y ⟶ X}
  {W₀ : X.Opens} {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}
end GlobalTheory.KS.VertReg
namespace GlobalTheory.KS
open VertReg
end GlobalTheory.KS
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.VertReg
variable {R : Type} [CommRing R] {Y X : Scheme.{0}} {q : Y ⟶ Sp ℂ} {p : X ⟶ Sp R} {m : Y ⟶ X}
  {W₀ : X.Opens} {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}
namespace GlobalTheory.KS.VertReg
theorem _root_.solution {D : R → ℂ} (h : LocDer q p m D W₀ d) (y : Sp ℂ ⟶ Y) {W W' : X.Opens} (hW : W' ≤ W) (h0 : W ≤ W₀)
    (hy : ⊤ ≤ (y ≫ m) ⁻¹ᵁ W') (f : Γ(X, W)) :
    valAt' y (m ⁻¹ᵁ W') (d W' (resG X hW f)) = valAt' y (m ⁻¹ᵁ W) (d W f) := by
  have hy1 : ⊤ ≤ y ⁻¹ᵁ m ⁻¹ᵁ W' := hy
  rw [h.res W W' hW h0 f]
  exact valAt'_resG_of_le y (fun _ hx => hW hx) hy1 (d W f)
end GlobalTheory.KS.VertReg
