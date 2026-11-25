-- Prove2me | solution 1 for GlobalTheory.Proof.SplitPlaceGoodSignature.goodPart_of_lifts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:10:30.510564+00:00
-- url     : https://prove2.me/submissions/480a2a21-e9e9-4d76-a5f6-661eeaf821f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_ThetaLiftOfEachRow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_HeckeSplitOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_SplitLiftOfLiftParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SplitPlaceGoodSignature
import Theorems.Thm_GlobalTheory_Proof_SplitPlaceGoodSignature_isoLoc_lift
import Theorems.Thm_GlobalTheory_Proof_SplitPlaceGoodSignature_goodRow_iff_goodSig
import Theorems.Thm_GlobalTheory_Proof_SplitPlaceGoodSignature_isoLoc_eq_of_hasParamX
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
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.SplitPlaceGoodSignature
open NumberField Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.ThetaExh
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
variable (N : NData R H what₂) (A : NAut N)
namespace GlobalTheory.Proof.SplitPlaceGoodSignature
theorem _root_.solution (i : N.Loc) (h1 : ThetaOne N A) (hL : ParamLaws N A)
    (hlift : LiftParam N A i) (hpt : PtLocal N A i) (hloc : LocOfPt N A i) : GoodPart N A i := by
  unfold GoodPart goodPartM
  apply le_antisymm
  · refine iSup₂_le fun σ hσ => ?_
    obtain ⟨hg, Sig₀, hW₀, x₀, hx₀⟩ := hσ
    by_cases hb : what₂.isot (N.j i) σ = ⊥
    · rw [hb]; exact bot_le
    obtain ⟨P, hP⟩ := h1 i σ hb
    obtain ⟨Sig, hW, hB⟩ := hlift σ P hP
    obtain ⟨y, hy⟩ := hpt P x₀ fun w hw => by
      obtain ⟨p, hp, hp'⟩ := hx₀ w hw
      refine ⟨p, ?_, hp'⟩
      rw [hp, ← hB.2.2.2.1 w hw.1, isoLoc_lift N A hL, isoLoc_lift N A hL, hW₀.2.2 w hw.1,
        hW.2.2 w hw.1]
    have hX : HasParamX N A i y Sig := ⟨P, hy, hB⟩
    have hZ : y ∈ ZgoodN N A i := by
      refine ⟨⟨P, hy, _, hB, ?_⟩, Sig, hX, (goodRow_iff_goodSig N A hW.2.2).1 hg⟩
      exact List.mem_map.2 ⟨muPart N A i, by simp, rfl⟩
    refine le_iSup₂_of_le y hZ (le_iSup₂_of_le Sig hX ?_)
    exact le_iSup₂_of_le (f := fun σ (_ : σ ∈ {σ | HasParamW N A i σ Sig}) =>
      what₂.isot (N.j i) σ) σ hW le_rfl
  · refine iSup₂_le fun x hx => iSup₂_le fun Sig hX => ?_
    unfold MjSig
    refine iSup₂_le fun σ hW => ?_
    obtain ⟨-, Sig', hX', hg⟩ := hx
    have hgood : N.goodRow σ := (goodRow_iff_goodSig N A (i := i) fun w hw =>
      (isoLoc_eq_of_hasParamX N A hL hloc hX' hX w hw).trans (hW.2.2 w hw)).2 hg
    have hat : AtM N A i σ := by
      obtain ⟨P, hP, hB⟩ := hX
      refine ⟨Sig, hW, x, fun w hw => ⟨heckePol N i x w, ?_, rfl⟩⟩
      rw [hB.2.2.2.1 w hw.1]
      exact A.pt_loc i P x hP w hw
    exact le_iSup₂_of_le (f := fun σ (_ : σ ∈ {σ | N.goodRow σ ∧ AtM N A i σ}) =>
      what₂.isot (N.j i) σ) σ ⟨hgood, hat⟩ le_rfl
end GlobalTheory.Proof.SplitPlaceGoodSignature
