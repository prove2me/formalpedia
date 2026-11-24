-- Prove2me | solution 1 for GlobalTheory.DI.frobLiftPsi_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:09:21.925982+00:00
-- url     : https://prove2.me/submissions/9e81c343-4181-4c11-bdce-366c95945230

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusDerivationFactorsThroughKaehlerStatement
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_FrobLiftPsiNatCastMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.DI
variable {K : Type} [CommRing K]
variable {Kt : Type} [CommRing Kt] (p : ℕ) [hp : Fact p.Prime] [CharP K p] (π : Kt →+* K) (F : Kt →+* Kt)
variable {p π F}
namespace GlobalTheory.DI
theorem _root_.solution (hL : IsFlatLift p π) (hF : IsFrob p π F) (z z' : Kt) :
    frobLiftPsi p π F hL hF (z * z') =
      π z ^ p • frobLiftPsi p π F hL hF z' + π z' ^ p • frobLiftPsi p π F hL hF z := by
  obtain ⟨w, hw⟩ := frobLift_exists_w p π F hL hF z
  obtain ⟨w', hw'⟩ := frobLift_exists_w p π F hL hF z'
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hpK : (p : K) = 0 := CharP.cast_eq_zero K p
  rw [frobLiftPsi_spec hL hF hw, frobLiftPsi_spec hL hF hw',
    frobLiftPsi_spec hL hF (w := w * z' ^ p + z ^ p * w' + p * w * w')
      (by rw [map_mul, hw, hw']; ring)]
  simp only [map_add, map_mul, map_pow, map_natCast, hpK, zero_mul, add_zero, Derivation.leibniz,
    kaehlerD_pow_char p, smul_zero, zero_add]
  have e1 : (π z * π z') ^ (p - 1) * π z = π z ^ p * π z' ^ (p - 1) := by
    rw [mul_pow, mul_right_comm, ← pow_succ, Nat.sub_add_cancel hp1]
  have e2 : (π z * π z') ^ (p - 1) * π z' = π z' ^ p * π z ^ (p - 1) := by
    rw [mul_pow, mul_assoc, ← pow_succ, Nat.sub_add_cancel hp1, mul_comm]
  simp only [smul_add, smul_smul, e1, e2]
  abel
end GlobalTheory.DI
