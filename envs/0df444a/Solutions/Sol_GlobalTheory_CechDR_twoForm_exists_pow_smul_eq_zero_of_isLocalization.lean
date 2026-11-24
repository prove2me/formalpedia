-- Prove2me | solution 1 for GlobalTheory.CechDR.twoForm_exists_pow_smul_eq_zero_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:41:22.132156+00:00
-- url     : https://prove2.me/submissions/ef664bd4-6701-4081-8ad7-10c3f1642244

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwoFormExistsPowSmulEqZeroOfIsLocalization
import Theorems.Thm_GlobalTheory_CechDR_mOm_two_eq_exteriorPowerMapOver
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_of_algHom
import Theorems.Thm_GlobalTheory_TopForm_isBaseChange_exteriorPower


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CechDR
namespace GlobalTheory.CechDR
theorem _root_.solution {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] (c : A)
    [IsLocalization.Away c B] (x : Om R A 2)
    (hx : (SemiHom.of_algHom (IsScalarTower.toAlgHom R A B)).mOm 2 x = 0) :
    ∃ n : ℕ, c ^ n • x = 0 := by
  haveI : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers c)
  have hb := GlobalTheory.TopForm.isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale R A B) 2
  haveI := (isLocalizedModule_iff_isBaseChange (Submonoid.powers c) B _).2 hb
  rw [mOm_two_eq_exteriorPowerMapOver, ← map_zero (GlobalTheory.exteriorPowerMapOver B 2 (KaehlerDifferential.map R R A B))] at hx
  obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (r := c) hx
  exact ⟨n, hn.trans (smul_zero _)⟩
end GlobalTheory.CechDR
