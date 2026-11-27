-- Prove2me | solution 1 for GlobalTheory.HostModel.exists_witData_levelAgree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:17:19.712366+00:00
-- url     : https://prove2.me/submissions/7b2f4264-a152-4d7c-87d0-f032f8026e9d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsWitDataLevelAgree
import Theorems.Thm_GlobalTheory_HostModel_witData_refl
import Theorems.Thm_GlobalTheory_HostModel_levelAgree_refl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HostModel
open ToricData
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {l : Level H} (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k)
namespace GlobalTheory.HostModel
theorem _root_.solution : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E)
    (D : Datum H) (l : Level H) (c : Coeff l) (k : Type) (_ : Field k) (bF : c.F →+* k)
    (a : ArcIn D l (RingHom.id c.F) k bF)
    (P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) (_ : Module (𝓞 E) P.toPre.X)
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X),
    WitData a P oP φ₁ he₁ w₁ e₁ ∧ WitData a P oP φ₂ he₂ w₂ e₂ ∧ LevelAgree a P w₁ w₂ e₁ e₂ :=
  ⟨_, _, _, _, host, _, level host 5 (by norm_num), coeff _, (coeff _).F, _, RingHom.id _, arcIn _ _ _, witP _ _ _, _,
    witAct _ _ _, _, _, witMap_eSec _ _ _, witMap_eSec _ _ _, witIso _ _ _, witIso _ _ _, _, _, witData_refl _ _ _,
    witData_refl _ _ _, levelAgree_refl _ _ _⟩
end GlobalTheory.HostModel
