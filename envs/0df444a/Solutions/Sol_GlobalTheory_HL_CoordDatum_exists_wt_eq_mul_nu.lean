-- Prove2me | solution 1 for GlobalTheory.HL.CoordDatum.exists_wt_eq_mul_nu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:10:16.965172+00:00
-- url     : https://prove2.me/submissions/69647baf-68c9-4de8-8566-eddcaf0d2165

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramePairCoordinatesTransportInnerData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StabilizerCommensurableInvVolumeSmulComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsWtEqMulNu
import Theorems.Thm_GlobalTheory_HL_CoordDatum_exists_invVol_eq_mul
import Theorems.Thm_GlobalTheory_HL_CoordDatum_transport
import Theorems.Thm_GlobalTheory_HL_Frames_stab_commensurable_invVol_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordDatum
namespace GlobalTheory.HL.CoordDatum
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ d0 : LocNG.Datum P, ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (d : LocNG.Datum P) Λ, S.IsTerm (c.dat d) Λ → LocNG.Datum.wt d0 d = κ * S.nu (c.dat d) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c d0
  have := hM.loc
  have := hM.char0
  obtain ⟨κ, hκ, hK⟩ :=
    exists_invVol_eq_mul (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d0)) S.complementReferenceCompactSubgroup
  refine ⟨κ, hκ, fun d Λ hT => ?_⟩
  obtain ⟨h1, h2⟩ := (Frames.stab_commensurable_invVol_smul M.L r k S).2 (c.dat d) Λ hT
  rw [(transport M hM H r k P S c).2.2.2.2 d0 d]
  exact hK _ h1 h2
end GlobalTheory.HL.CoordDatum
