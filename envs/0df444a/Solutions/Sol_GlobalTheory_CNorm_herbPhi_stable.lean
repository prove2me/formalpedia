-- Prove2me | solution 1 for GlobalTheory.CNorm.herbPhi_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:35:11.111155+00:00
-- url     : https://prove2.me/submissions/b7a159a6-2904-48fd-b9eb-cb98c62da0b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowPrimeRangeEqIteratedDifferenceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionKerRangeMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionFiniteKerRangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormDifferenceIndexIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexRangeKerIterateEndomorphismStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HerbrandPrimeOrder
import Theorems.Thm_GlobalTheory_CNorm_nrm_apply
import Theorems.Thm_GlobalTheory_T_index_range_ker_iterate_endomorphism
import Theorems.Thm_GlobalTheory_T_pow_prime_range_eq_iterated_difference


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
theorem _root_.solution (p : ℕ) (A : Type) [CommGroup A] (σ : A →* A) (hp : p.Prime)
    (C : Subgroup A) (hst : ∀ x ∈ C, σ x ∈ C) (hn : ∀ x ∈ C, nrm σ p x = 1)
    (hI : pIdx p C ≠ 0) (hT : pTor p C ≠ 0) :
    (C.map (dif σ)).relIndex C ≠ 0 ∧ Nat.card ↥(C ⊓ fix σ) ≠ 0 ∧
      pIdx p C * Nat.card ↥(C ⊓ fix σ) ^ (p - 1) =
        (C.map (dif σ)).relIndex C ^ (p - 1) * pTor p C := by
  let τ : C →* C := (σ.comp C.subtype).codRestrict C (fun x => hst x x.2)
  have hτ : ∀ x : C, (τ x : A) = σ x := fun x => rfl
  have hit : ∀ (k : ℕ) (x : C), ((τ^[k] x : C) : A) = σ^[k] x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hτ, ih]
  let lam : Monoid.End C := dif τ
  have hnτ : ∀ a, nrm τ p a = 1 := by
    intro a
    apply Subtype.ext
    have := hn a a.2
    rw [nrm_apply] at this ⊢
    rw [SubmonoidClass.coe_finset_prod]
    simp only [hit]
    exact this
  obtain ⟨h1, h2⟩ := GlobalTheory.T.pow_prime_range_eq_iterated_difference p C τ lam hp (fun _ => rfl) hnτ
  obtain ⟨k, hk⟩ : ∃ k, p - 1 = k + 1 := ⟨p - 2, by have := hp.two_le; omega⟩
  rw [hk] at h1 h2 ⊢
  have eI : pIdx p C = (MonoidHom.range (lam ^ (k + 1) : Monoid.End C)).index := by
    rw [← h1, pIdx, Subgroup.relIndex]
    congr 1
    ext x
    simp only [pows, Subgroup.mem_subgroupOf, Subgroup.mem_map, powMonoidHom_apply]
    constructor
    · rintro ⟨y, hy, e⟩
      exact ⟨⟨y, hy⟩, trivial, Subtype.ext e⟩
    · rintro ⟨y, -, e⟩
      exact ⟨y, y.2, congrArg Subtype.val e⟩
  have eT : pTor p C = Nat.card (MonoidHom.ker (lam ^ (k + 1) : Monoid.End C)) := by
    rw [pTor]
    refine Nat.card_congr ⟨fun x => ⟨⟨x.1, x.2.1⟩, (h2 _).1 (Subtype.ext x.2.2)⟩,
      fun y => ⟨y.1.1, y.1.2, congrArg Subtype.val ((h2 _).2 y.2)⟩, fun _ => rfl, fun _ => rfl⟩
  have ei : (C.map (dif σ)).relIndex C = (MonoidHom.range lam).index := by
    rw [Subgroup.relIndex]
    congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, MonoidHom.mem_range]
    constructor
    · rintro ⟨y, hy, e⟩
      exact ⟨⟨y, hy⟩, Subtype.ext e⟩
    · rintro ⟨y, e⟩
      exact ⟨y, y.2, congrArg Subtype.val e⟩
  have ec : Nat.card ↥(C ⊓ fix σ) = Nat.card (MonoidHom.ker lam) := by
    refine Nat.card_congr ⟨fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext (div_eq_one.2 x.2.2)⟩,
      fun y => ⟨y.1.1, y.1.2, div_eq_one.1 (congrArg Subtype.val y.2)⟩, fun _ => rfl, fun _ => rfl⟩
  rw [eI] at hI ⊢
  rw [eT] at hT ⊢
  rw [ei, ec]
  exact GlobalTheory.T.index_range_ker_iterate_endomorphism C lam k hI hT
end GlobalTheory.CNorm
