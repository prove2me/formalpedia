-- Prove2me | solution 1 for GlobalTheory.LocalInv.galPol_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:38:51.187948+00:00
-- url     : https://prove2.me/submissions/bc4e03f2-7d35-4090-ad6e-a85d2ab6a927

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_NoLocalInvariants
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_TemperedRepresentations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeightRegularOfExt
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LocalInv
open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace GlobalTheory.LocalInv
theorem _root_.solution (i : N.Loc) {w : PlE H} (hw : SplitOut N i w) {B : ValuationSubring N.Om}
    {σ : G H.E N.Om} (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) (u : ℝ) :
    galPol A (A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w)
      (((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 + u)) =
      X - C (iotaO N A i ((N.chi i 1 σ : (N.O i)ˣ) : N.O i) * ((normV w : ℕ) : ℂ) ^ ((u : ℝ) : ℂ)) := by
  obtain ⟨h1, h2⟩ := A.chi_mu i w hw
  unfold galPol
  rw [← A.lpTw_add, A.frobEig_tw _ _ ((A.unr_tw _ _).2 h1), h2 B σ hB hσ]
  simp [iotaO]
end GlobalTheory.LocalInv
