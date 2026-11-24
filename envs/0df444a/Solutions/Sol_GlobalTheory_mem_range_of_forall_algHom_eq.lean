-- Prove2me | solution 1 for GlobalTheory.mem_range_of_forall_algHom_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:21:10.241021+00:00
-- url     : https://prove2.me/submissions/ace08a6b-fa2f-4763-9360-3a424341207e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemRangeOfForallAlgHomEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open Polynomial
namespace GlobalTheory
theorem _root_.solution :
    ∀ (F K₀ : Type) [Field F] [CharZero F] [Field K₀] [Algebra F K₀], Algebra.IsAlgebraic F K₀ →
      ∀ t : K₀, (∀ (Ω : Type) [Field Ω] [Algebra F Ω] (φ₁ φ₂ : K₀ →ₐ[F] Ω), φ₁ t = φ₂ t) →
        t ∈ Set.range (algebraMap F K₀) := by
  intro F K₀ _ _ _ _ halg t ht
  classical
  have hint : IsIntegral F t := (Algebra.IsAlgebraic.isAlgebraic t).isIntegral
  set Ω := AlgebraicClosure K₀
  have hsep : (minpoly F t).Separable := (minpoly.irreducible hint).separable
  have hsplit : Splits ((minpoly F t).map (algebraMap F Ω)) := IsAlgClosed.splits _
  have hcard := card_rootSet_eq_natDegree (K := Ω) hsep hsplit
  by_contra hnot
  have h1 : (minpoly F t).natDegree ≠ 1 := fun h => by
    obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.mp h
    exact hnot ⟨c, hc⟩
  have hpos := minpoly.natDegree_pos hint
  have hlt : 1 < Fintype.card ((minpoly F t).rootSet Ω) := by omega
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card hlt
  have hK' : ∀ s : K₀, IsIntegral F s ∧ Splits ((minpoly F s).map (algebraMap F Ω)) :=
    fun s => ⟨(Algebra.IsAlgebraic.isAlgebraic s).isIntegral, IsAlgClosed.splits _⟩
  have ha : aeval (a : Ω) (minpoly F t) = 0 :=
    (mem_rootSet.mp a.2).2
  have hb : aeval (b : Ω) (minpoly F t) = 0 :=
    (mem_rootSet.mp b.2).2
  obtain ⟨φa, hφa⟩ := IntermediateField.exists_algHom_of_splits_of_aeval hK' ha
  obtain ⟨φb, hφb⟩ := IntermediateField.exists_algHom_of_splits_of_aeval hK' hb
  apply hab
  apply Subtype.ext
  rw [← hφa, ← hφb]
  exact ht Ω φa φb
end GlobalTheory
