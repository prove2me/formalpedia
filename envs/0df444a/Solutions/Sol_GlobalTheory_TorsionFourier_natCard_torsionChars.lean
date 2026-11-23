-- Prove2me | solution 1 for GlobalTheory.TorsionFourier.natCard_torsionChars
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:39.824057+00:00
-- url     : https://prove2.me/submissions/fb46bb71-1b25-485c-bc80-12526afa07cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
open GlobalTheory.TorsionFourier
variable {K X : Type} [Field K] [AddCommGroup X]
variable [Module.Free ℤ X] [Module.Finite ℤ X]
open Module
variable {K X : Type} [Field K] [AddCommGroup X]
variable [Module.Free ℤ X] [Module.Finite ℤ X]
namespace GlobalTheory.TorsionFourier
namespace _root_.GlobalTheory.TorsionFourier
theorem _root_.solution {N : ℕ} {ζ : K} (hN : 0 < N)
    (hζ : IsPrimitiveRoot ζ N) :
    Nat.card (_root_.GlobalTheory.TorsionFourier.torsionChars K X N) = N ^ finrank ℤ X := by
  haveI : NeZero N := ⟨hN.ne'⟩
  let b := Module.Free.chooseBasis ℤ X
  rw [Nat.card_congr (_root_.GlobalTheory.TorsionFourier.torsionCharsEquiv (K := K) (X := X) b N), Nat.card_fun,
    hζ.card_rootsOfUnity, Module.finrank_eq_card_basis b, Nat.card_eq_fintype_card]
end _root_.GlobalTheory.TorsionFourier
end GlobalTheory.TorsionFourier
