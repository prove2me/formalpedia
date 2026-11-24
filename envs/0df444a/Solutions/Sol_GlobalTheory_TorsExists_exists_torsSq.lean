-- Prove2me | solution 1 for GlobalTheory.TorsExists.exists_torsSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:10:22.347868+00:00
-- url     : https://prove2.me/submissions/eed448da-f12c-4898-8807-0cbc2f275a94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsIsUnitField
import Theorems.Thm_GlobalTheory_TorsExists_exists_contraction
import Theorems.Thm_GlobalTheory_TorsExists_exists_homogeneous
import Theorems.Thm_GlobalTheory_TorsExists_nonempty_equiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.TorsExists
variable {Ix : Type} [Fintype Ix] [DecidableEq Ix]
namespace GlobalTheory.TorsExists
theorem _root_.solution : ∀ (R Ix : Type) [CommRing R] [Fintype Ix] [DecidableEq Ix] (deg : Ix → ℕ) (D : Matrix Ix Ix R) [IsLocalRing R], IsCx deg D → (∀ v : Ix → IsLocalRing.ResidueField R, (D.map (IsLocalRing.residue R)).mulVec v = 0 → ∃ w, (D.map (IsLocalRing.residue R)).mulVec w = v) → ∃ t, TorsSq deg D t := by
  intro R Ix _ _ _ deg D _ hD hex
  obtain ⟨h0, hh0⟩ := exists_contraction D hD.2 hex
  obtain ⟨h, hdeg, hh⟩ := exists_homogeneous deg D h0 hD.1 hh0
  obtain ⟨e⟩ := nonempty_equiv deg D h hD hdeg hh
  exact ⟨_, h, hdeg, hh, e, rfl⟩
end GlobalTheory.TorsExists
