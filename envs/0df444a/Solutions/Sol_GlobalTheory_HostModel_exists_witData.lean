-- Prove2me | solution 1 for GlobalTheory.HostModel.exists_witData
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:21:04.311214+00:00
-- url     : https://prove2.me/submissions/8ca0cfcf-ca12-4c5d-8ecf-7ffce27c28bf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsWitDataLevelAgree
import Theorems.Thm_GlobalTheory_HostModel_witData_refl
import Theorems.Thm_GlobalTheory_HostModel_witData_neg
import Theorems.Thm_GlobalTheory_HostModel_refl_ne_neg

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
theorem _root_.solution : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E) (D : Datum H)
    (l : Level H) (c : Coeff l) (k : Type) (_ : Field k) (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) (_ : Module (𝓞 E) P.toPre.X)
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)) (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X),
    e₁ ≠ e₂ ∧ WitData a P oP φ he w e₁ ∧ WitData a P oP φ he w e₂ :=
  ⟨_, _, _, _, host, _, level host 5 (by norm_num), coeff _, (coeff _).F, _, RingHom.id _, arcIn _ _ _, witP _ _ _, _,
    witAct _ _ _, witMap _ _ _, witMap_eSec _ _ _, witIso _ _ _, _, _, refl_ne_neg, witData_refl _ _ _,
    witData_neg _ _ _⟩
end GlobalTheory.HostModel
