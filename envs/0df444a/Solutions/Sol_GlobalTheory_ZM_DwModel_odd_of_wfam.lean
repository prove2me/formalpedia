-- Prove2me | solution 1 for GlobalTheory.ZM.DwModel.odd_of_wfam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:35:54.010563+00:00
-- url     : https://prove2.me/submissions/cdca22f1-17c0-41cb-ba8b-0b1903d4325c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_NotIsGaloisCoverTrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.DwModel
namespace GlobalTheory.ZM.DwModel
theorem _root_.solution {o : Type} [CommRing o] {g : ℕ} {J : Type} {n N' : ℕ} {b : TBase o (N' ^ 2)} {em : o →+* ℂ}
    {C : TObj g (N' ^ 2) J b (spMap em) → Prop} {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ}
    (W : WFam n em C Mat κ) : Odd N' := by
  obtain ⟨x, ⟨-, hx⟩, -⟩ := W.Y.pts PUnit (algebraMap o PUnit) (fun _ => 0) (by
    unfold InMM
    exact ⟨fun _ _ => Subsingleton.elim _ _, fun q hq => absurd (Subsingleton.elim q ⊤) hq.ne_top⟩)
  let x' : Sp PUnit ⟶ W.U.toScheme := specPUnitIsInitial.to _
  have hx' : x' ≫ W.U.ι = x := specPUnitIsInitial.hom_ext _ _
  have h := (W.th PUnit x' (fun _ => 0)).2 (hx' ▸ hx)
  unfold TObj.HasTh Out.IsThetaPt at h
  exact h.1
end GlobalTheory.ZM.DwModel
