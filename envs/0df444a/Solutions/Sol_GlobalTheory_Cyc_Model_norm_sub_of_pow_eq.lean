-- Prove2me | solution 1 for GlobalTheory.Cyc.Model.norm_sub_of_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:52.336653+00:00
-- url     : https://prove2.me/submissions/e9f69891-3284-4b1c-b09f-86ee1fbacdf9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_PowLtFirstRadius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.Model
theorem _root_.solution {ζ : Om l} {m a b : ℕ} (hζ : IsPrimitiveRoot ζ (l ^ m)) (h : ζ ^ a = ζ ^ b) :
    ‖(a : ℚ_[l]) - (b : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
  have hl : l.Prime := Fact.out
  have hu := hζ.isUnit (pow_pos hl.pos m).ne'
  have h1 : a ≡ b [MOD l ^ m] := by
    rw [hζ.eq_orderOf]
    obtain ⟨u, rfl⟩ := hu
    rw [orderOf_units, ← pow_eq_pow_iff_modEq]
    ext; simpa using h
  have h2 : ((l : ℤ) ^ m) ∣ ((a : ℤ) - b) := by
    have := (Nat.modEq_iff_dvd.mp h1.symm); exact_mod_cast this
  have := (Padic.norm_int_le_pow_iff_dvd (p := l) ((a : ℤ) - b) m).mpr h2
  simpa using this
end GlobalTheory.Cyc.Model
