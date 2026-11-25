-- Prove2me | solution 1 for GlobalTheory.ProjCoh.card_natVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:36:01.660149+00:00
-- url     : https://prove2.me/submissions/3fdafd5e-3bf9-4082-a965-cdb8c6d10dd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfMonomialBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMonomialBasisCechCubePolynomialGrading
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexPolyGradingFiniteExact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NonemptyBasisPolyGrading

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.ProjCoh
namespace GlobalTheory.ProjCoh
theorem _root_.solution (N : ℕ) (hN : 1 ≤ N) (m : ℤ) :
    Nat.card {a : Fin (N + 1) → ℕ // ∑ i, (a i : ℤ) = m} = (m + N).toNat.choose N := by
  rcases lt_or_ge m 0 with h | h
  · have : IsEmpty {a : Fin (N + 1) → ℕ // ∑ i, (a i : ℤ) = m} := ⟨fun a =>
      absurd (a.2 ▸ Finset.sum_nonneg fun i _ => Int.natCast_nonneg (a.1 i)) h.not_ge⟩
    rw [Nat.card_of_isEmpty, Nat.choose_eq_zero_of_lt (by omega)]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [Nat.card_congr (Equiv.subtypeEquivRight (q := fun a => ∑ i, a i = m) fun a => by
      norm_cast), ← Nat.card_congr (Sym.equivNatSumOfFintype _ m), Nat.card_eq_fintype_card,
      Sym.card_sym_eq_choose, Fintype.card_fin, show ((m : ℤ) + N).toNat = m + N by omega,
      show N + 1 + m - 1 = m + N by omega, Nat.choose_symm_add]
end GlobalTheory.ProjCoh
