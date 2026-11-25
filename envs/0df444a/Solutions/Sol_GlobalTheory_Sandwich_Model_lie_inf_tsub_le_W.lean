-- Prove2me | solution 1 for GlobalTheory.Sandwich.Model.lie_inf_tsub_le_W
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:16:02.457712+00:00
-- url     : https://prove2.me/submissions/42c9f126-4fb2-431c-a94f-a1c1e13b3a8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_MemMixedTsub
import Theorems.Thm_GlobalTheory_Sandwich_Model_al_bb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal Matrix
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.Sandwich.Model
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
variable {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} [Algebra O C]
  (hv : v.Integers O) {ε : PreTilt O p}
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε
variable {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ] (D : Datum ε h Λ)
namespace GlobalTheory.Sandwich.Model
theorem _root_.solution (τ : Λ →+* O) : D.Lie ⊓ D.Tsub τ ≤ D.W τ := by
  rintro x ⟨⟨y, rfl⟩, hx⟩
  exact ⟨hx, al_bb hv hε D y⟩
end GlobalTheory.Sandwich.Model
