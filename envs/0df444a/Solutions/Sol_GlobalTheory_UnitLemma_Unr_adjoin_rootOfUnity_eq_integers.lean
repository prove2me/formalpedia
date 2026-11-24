-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.adjoin_rootOfUnity_eq_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:13:19.222039+00:00
-- url     : https://prove2.me/submissions/d83c83aa-8239-4c18-98df-e2bc427192fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinPrimitiveRootEqIntegersUnramifiedQuadratic
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_mem_adjoin_of_pow_eq_one_of_isUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial IsLocalRing
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → d ≠ 0 → ∀ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) → @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤ → ∀ y : K'.E, @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra y → y ∈ @Algebra.adjoin K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra {z} := by
  intro K K' d φ hφ hd z hz hadj y hy
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional K.E K'.E :=
    Module.finite_of_finrank_pos (by rw [hφ.2.2.2.2]; exact Nat.pos_of_ne_zero hd)
  have hN : IsUnit (((K'.q ^ 2 - 1 : ℕ)) : K.O) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast]
    haveI := Fintype.ofFinite (ResidueField K.O)
    have hcard : ((K.q ^ 2 : ℕ) : ResidueField K.O) = 0 := by
      rw [← K.card_res, Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _
    have hq : 1 ≤ K'.q ^ 2 := by
      rw [hφ.1, ← pow_mul, mul_comm, pow_mul]
      apply Nat.one_le_pow
      rw [← K.card_res]; exact Nat.card_pos
    rw [Nat.cast_sub hq, hφ.1, ← pow_mul, mul_comm, pow_mul, Nat.cast_pow, hcard, zero_pow hd, Nat.cast_one,
      zero_sub]
    exact neg_ne_zero.2 one_ne_zero
  exact mem_adjoin_of_pow_eq_one_of_isUnit hN hz.pow_eq_one hadj hy
end GlobalTheory.UnitLemma.Unr
