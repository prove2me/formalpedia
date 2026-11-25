-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.resAlg_split_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:35:21.647632+00:00
-- url     : https://prove2.me/submissions/57c5191e-4ab9-4687-9567-1e6b4d4be3e8

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens
namespace GlobalTheory.CompanionTheory.UnrDens
theorem _root_.solution :
    ResAlg (ZMod 2 × ZMod 2) (RingEquiv.prodComm : ZMod 2 × ZMod 2 ≃+* ZMod 2 × ZMod 2).toRingHom 2 1 := by
  refine ⟨fun a => ?_, ?_, ?_, by norm_num, ?_, ?_⟩
  · first
      | rfl
      | simp
      | (ext <;> rfl)
  · rintro ⟨x, y⟩ h hne
    fin_cases x <;> fin_cases y
    all_goals first
      | exact (hne rfl).elim
      | exact absurd h (by decide)
      | exact isUnit_one
      | (convert isUnit_one using 1; decide)
  · refine ⟨(1, 0), ?_, ?_⟩
    · convert isUnit_one using 1
      decide
    · rintro ⟨p, r⟩
      refine ⟨(r, r), (p - r, p - r), rfl, rfl, ?_⟩
      ext <;> first | simp | (simp; ring) | ring
  · first
      | simp
      | (rw [Nat.card_eq_fintype_card]; rfl)
      | decide
  · right
    refine ⟨rfl, fun hF => ?_⟩
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel (a := ((1, 0) : ZMod 2 × ZMod 2)) (by decide)
    have h2 := congrArg Prod.snd hb
    simp at h2
end GlobalTheory.CompanionTheory.UnrDens
