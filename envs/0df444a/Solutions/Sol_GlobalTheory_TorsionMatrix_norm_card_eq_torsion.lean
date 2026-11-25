-- Prove2me | solution 1 for GlobalTheory.TorsionMatrix.norm_card_eq_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:18:20.463844+00:00
-- url     : https://prove2.me/submissions/b227d7be-5f78-4da2-9c47-1843f9af3497

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateBasisMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NormCardQuotientSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MatrixPolynomialDetNormFixedPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.TorsionMatrix
open Matrix
namespace GlobalTheory.TorsionMatrix
theorem _root_.solution (l : ℕ) [hl : Fact l.Prime] (K : Type) [AddCommGroup K] [Finite K]
    (N : ℕ) (hN : Nat.card K ≤ N) :
    ‖((Nat.card K : ℕ) : ℚ_[l])‖ = ‖((Nat.card {x : K // l ^ N • x = 0} : ℕ) : ℚ_[l])‖ := by
  let T : AddSubgroup K := (nsmulAddMonoidHom (α := K) (l ^ N)).ker
  have hT : ∀ x, x ∈ T ↔ l ^ N • x = 0 := fun x => Iff.rfl
  have h1 : Nat.card K = Nat.card (K ⧸ T) * Nat.card {x : K // l ^ N • x = 0} :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup T
  have h2 : ¬ l ∣ Nat.card (K ⧸ T) := by
    intro hd
    obtain ⟨y, hy⟩ := exists_prime_addOrderOf_dvd_card' l hd
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    have h3 : l • x ∈ T := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul,
        ← addOrderOf_dvd_iff_nsmul_eq_zero, hy]
    rw [hT, smul_smul, ← pow_succ, ← addOrderOf_dvd_iff_nsmul_eq_zero,
      Nat.dvd_prime_pow hl.out] at h3
    obtain ⟨k, -, hk⟩ := h3
    have h4 : k ≤ N := by
      have := addOrderOf_le_card (x := x)
      have := Nat.lt_pow_self (n := k) hl.out.one_lt
      omega
    have h5 : x ∈ T := by
      rw [hT, ← addOrderOf_dvd_iff_nsmul_eq_zero, hk]
      exact pow_dvd_pow _ h4
    rw [(QuotientAddGroup.eq_zero_iff x).2 h5, addOrderOf_zero] at hy
    exact hl.out.one_lt.ne hy
  rw [h1, Nat.cast_mul, norm_mul, Padic.norm_natCast_eq_one_iff.2
    ((Nat.Prime.coprime_iff_not_dvd hl.out).2 h2), one_mul]
end GlobalTheory.TorsionMatrix
