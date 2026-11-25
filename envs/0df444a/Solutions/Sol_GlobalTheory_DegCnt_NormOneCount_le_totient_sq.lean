-- Prove2me | solution 1 for GlobalTheory.DegCnt.NormOneCount.le_totient_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:28:03.706318+00:00
-- url     : https://prove2.me/submissions/a097944f-5301-4d97-ab7e-f4ddb1c8ba04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IdealsOfNormEqIndexSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfMulMem
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.NormOneCount
namespace GlobalTheory.DegCnt.NormOneCount
theorem _root_.solution (n : ℕ) : n ≤ 2 * n.totient ^ 2 ∧ (Odd n → n ≤ n.totient ^ 2) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.totient_prime_pow_succ hp]
    have h2 := hp.two_le
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have hq : 1 ≤ q := by omega
    have hP : 1 ≤ (q + 1) ^ k := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ, Nat.add_sub_cancel]
    generalize (q + 1) ^ k = P at hP ⊢
    have hPP : P ≤ P ^ 2 := by nlinarith
    refine ⟨?_, fun ho => ?_⟩
    · have h1 : q + 1 ≤ 2 * q ^ 2 := by nlinarith
      calc P * (q + 1) ≤ P ^ 2 * (2 * q ^ 2) := Nat.mul_le_mul hPP h1
        _ = _ := by ring
    · have ho' : Odd (q + 1) := (Nat.odd_mul.1 ho).2
      have hq2 : 2 ≤ q := by
        obtain ⟨m, hm⟩ := ho'
        omega
      have h1 : q + 1 ≤ q ^ 2 := by nlinarith
      calc P * (q + 1) ≤ P ^ 2 * q ^ 2 := Nat.mul_le_mul hPP h1
        _ = _ := by ring
  | zero => simp
  | one => simp
  | coprime a b ha hb hab iha ihb =>
    rw [Nat.totient_mul hab]
    refine ⟨?_, fun ho => ?_⟩
    · rcases Nat.even_or_odd a with hea | hoa
      · have hob : Odd b := by
          rcases Nat.even_or_odd b with heb | hob
          · have := Nat.dvd_gcd hea.two_dvd heb.two_dvd
            rw [hab.gcd_eq_one] at this
            omega
          · exact hob
        calc a * b ≤ (2 * a.totient ^ 2) * b.totient ^ 2 := Nat.mul_le_mul iha.1 (ihb.2 hob)
          _ = _ := by ring
      · calc a * b ≤ a.totient ^ 2 * (2 * b.totient ^ 2) := Nat.mul_le_mul (iha.2 hoa) ihb.1
          _ = _ := by ring
    · obtain ⟨h1, h2⟩ := Nat.odd_mul.1 ho
      calc a * b ≤ a.totient ^ 2 * b.totient ^ 2 := Nat.mul_le_mul (iha.2 h1) (ihb.2 h2)
        _ = _ := by ring
end GlobalTheory.DegCnt.NormOneCount
