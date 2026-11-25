-- Prove2me | solution 1 for GlobalTheory.HostModel.arcIn_be_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:52:23.900819+00:00
-- url     : https://prove2.me/submissions/d38a5025-e8a2-497d-80ad-2f4fb6a1771b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ToMatrixTrFormBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_TrFormBaseChangeNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_SqrtNegDiscMemCoeffField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ZeroFLeftExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_PullTopZFConstUnit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HostModel
open ToricData ConjDual
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {H : Host E} {l : Level H} (c : Coeff l) (k : Type) [CommRing k] [IsDomain k] (bF : c.F →+* k)
namespace GlobalTheory.HostModel
theorem _root_.solution (y : 𝓞 E) : (2 : ℤ) ∣ (arcIn c k bF).be y y :=
  (dvd_mul_right 2 _).trans ((arcIn c k bF).be_dvd y y)
end GlobalTheory.HostModel
