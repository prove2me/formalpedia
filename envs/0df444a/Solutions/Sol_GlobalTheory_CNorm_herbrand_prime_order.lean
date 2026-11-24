-- Prove2me | solution 1 for GlobalTheory.CNorm.herbrand_prime_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:49:58.102587+00:00
-- url     : https://prove2.me/submissions/86992b39-78e5-4b66-82f4-fb631fb8b4b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowPrimeRangeEqIteratedDifferenceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionKerRangeMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionFiniteKerRangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormDifferenceIndexIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexRangeKerIterateEndomorphismStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HerbrandPrimeOrder
import Theorems.Thm_GlobalTheory_CNorm_herbPhi_arith
import Theorems.Thm_GlobalTheory_CNorm_herbPhi_nrm_dif
import Theorems.Thm_GlobalTheory_CNorm_herbPhi_stable
import Theorems.Thm_GlobalTheory_CNorm_dif_apply
import Theorems.Thm_GlobalTheory_CNorm_mem_fix
import Theorems.Thm_GlobalTheory_CNorm_nrm_apply
import Theorems.Thm_GlobalTheory_T_norm_difference_index_identity
import Theorems.Thm_GlobalTheory_T_powIndex_torsion_finite_ker_range
import Theorems.Thm_GlobalTheory_T_powIndex_torsion_ker_range_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
namespace GlobalTheory.CNorm
theorem _root_.solution : ∀ (p : ℕ) (A : Type) [CommGroup A] (σ : A →* A), p.Prime → (∀ a, σ^[p] a = a) → pIdx p (⊤ : Subgroup A) ≠ 0 → pTor p (⊤ : Subgroup A) ≠ 0 → (nrm σ p).range.relIndex (fix σ) ≠ 0 ∧ (dif σ).range.relIndex (nrm σ p).ker ≠ 0 ∧ pIdx p (fix σ) ≠ 0 ∧ pTor p (fix σ) ≠ 0 ∧ (nrm σ p).range.relIndex (fix σ) ^ (p - 1) * pIdx p (⊤ : Subgroup A) * pTor p (fix σ) ^ p = (dif σ).range.relIndex (nrm σ p).ker ^ (p - 1) * pTor p (⊤ : Subgroup A) * pIdx p (fix σ) ^ p := by
  intro p A _ σ hp hσ ha ht
  have hker : (dif σ).ker = fix σ := by
    ext x
    rw [MonoidHom.mem_ker, dif_apply, div_eq_one, mem_fix]
  have hcT : pTor p (dif σ).range ≠ 0 := by
    unfold pTor at ht ⊢
    have hfin : Finite {x : A // x ∈ (⊤ : Subgroup A) ∧ x ^ p = 1} := Nat.finite_of_card_ne_zero ht
    have : Finite {x : A // x ∈ (dif σ).range ∧ x ^ p = 1} :=
      Finite.of_injective (β := {x : A // x ∈ (⊤ : Subgroup A) ∧ x ^ p = 1})
        (fun x => ⟨x.1, trivial, x.2.2⟩) (fun x y h => Subtype.ext (by simpa using h))
    have : Nonempty {x : A // x ∈ (dif σ).range ∧ x ^ p = 1} := ⟨⟨1, one_mem _, one_pow _⟩⟩
    exact Nat.card_pos.ne'
  obtain ⟨hbI, hbT, hcI⟩ := GlobalTheory.T.powIndex_torsion_finite_ker_range p A A (dif σ) ha ht hcT
  obtain ⟨-, -, e1⟩ := GlobalTheory.T.powIndex_torsion_ker_range_mul p A A (dif σ) hbI hbT hcI hcT
  rw [hker] at hbI hbT e1
  obtain ⟨hi, hc, e2⟩ := herbPhi_stable p A σ hp (dif σ).range
    (by rintro _ ⟨y, rfl⟩; exact ⟨σ y, by rw [dif_apply, dif_apply, _root_.map_div]⟩)
    (by rintro _ ⟨y, rfl⟩; rw [herbPhi_nrm_dif, hσ, div_self']) hcI hcT
  have e3 := GlobalTheory.T.norm_difference_index_identity p A σ hσ
  have hle : pows p (fix σ) ≤ (nrm σ p).range := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y, ?_⟩
    have hy' : σ y = y := hy
    rw [nrm_apply, Finset.prod_congr rfl (fun i _ => Function.iterate_fixed hy' i)]
    simp
  have h0 : (nrm σ p).range.relIndex (fix σ) ≠ 0 :=
    ne_zero_of_dvd_ne_zero hbI (Subgroup.relIndex_dvd_of_le_left _ hle)
  have h1 : (dif σ).range.relIndex (nrm σ p).ker ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_mul] at e3
    exact mul_ne_zero (mul_ne_zero h0 hi) hbT e3
  refine ⟨h0, h1, hbI, hbT, ?_⟩
  have := herbPhi_arith (p - 1) _ _ _ _ _ _ _ _ _ _ hi hcT e1 e2 e3
  rwa [Nat.sub_add_cancel hp.one_le] at this
end GlobalTheory.CNorm
