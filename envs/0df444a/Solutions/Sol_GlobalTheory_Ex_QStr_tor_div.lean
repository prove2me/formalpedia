-- Prove2me | solution 1 for GlobalTheory.Ex.QStr.tor_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:11:58.235012+00:00
-- url     : https://prove2.me/submissions/d8b6653b-d6fb-4bf0-88d5-41ac4082c1d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Theorems.Thm_GlobalTheory_Ex_QStr_chr_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.QStr
variable {C : Type} [Field C] [IsAlgClosed C] (N : NumD C) {k : ℕ}
namespace GlobalTheory.Ex.QStr
theorem _root_.solution (hk : k ≠ 0) (t : Multiplicative N.X →* Cˣ) : ∃ t' : Multiplicative N.X →* Cˣ, t' ^ k = t := by
  let v := Module.finBasis ℤ N.X
  have h : ∀ u : Cˣ, ∃ w : Cˣ, w ^ k = u := fun u => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : C) (Nat.pos_of_ne_zero hk)
    have h0 : z ≠ 0 := by
      rintro rfl
      exact u.ne_zero (by rw [← hz, zero_pow hk])
    exact ⟨Units.mk0 z h0, Units.ext (by simpa using hz)⟩
  choose w hw using h
  refine ⟨chr v fun i => w (t (Multiplicative.ofAdd (v i))), ?_⟩
  rw [← map_pow]
  conv_rhs => rw [← chr_eq v t]
  congr 1
  funext i
  exact hw _
end GlobalTheory.Ex.QStr
