-- Prove2me | solution 1 for GlobalTheory.exists_sum_mul_pow_div_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:15:13.356644+00:00
-- url     : https://prove2.me/submissions/02dfda59-b7f7-4634-bb28-da009e9fdec6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsIntegralMulPowOfSubalgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial
variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {J : Type*}
namespace GlobalTheory
theorem _root_.solution [Fintype J] (t : J → Ω) (ht : ∃ i, t i ≠ 0) (e : ℕ) {w : Ω}
    (hw0 : w ≠ 0) (hw : ∀ i, t i ≠ 0 →
      IsIntegral (Algebra.adjoin o (Set.range fun j => t j / t i)) (w / t i ^ e))
    (C : Subalgebra o Ω) (hC : ∀ i, t i ^ e / w ∈ C) :
    ∃ c : J → C, ∑ i, (c i : Ω) * (t i ^ e / w) = 1 := by
  let y : J → C.toSubring := fun i => ⟨_, hC i⟩
  by_cases hI : Ideal.span (Set.range y) = ⊤
  · obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp ((Ideal.eq_top_iff_one _).mp hI)
    refine ⟨fun i => ⟨c i, (c i).2⟩, ?_⟩
    have h := congrArg C.toSubring.subtype hc
    rw [map_sum, map_one] at h
    exact h
  exfalso
  obtain ⟨V, hV, hV'⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  obtain ⟨i₀, hi₀⟩ := ht
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => V.valuation (t j))
    ⟨i₀, Finset.mem_univ _⟩
  have hv : 0 < V.valuation (t i) :=
    ((V.valuation.pos_iff).mpr hi₀).trans_le (hi _ (Finset.mem_univ _))
  have hti : t i ≠ 0 := (V.valuation.pos_iff).mp hv
  have hle : ∀ x ∈ Algebra.adjoin o (Set.range fun j => t j / t i), x ∈ V := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [← V.valuation_le_one_iff, map_div₀, div_le_one₀ hv]
      exact hi _ (Finset.mem_univ _)
    | algebraMap a => exact hV (C.algebraMap_mem a)
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  have h1 : IsIntegral V (w / t i ^ e) :=
    (hw i hti).map_of_comp_eq (T := V)
      ((Algebra.adjoin o (Set.range fun j => t j / t i)).val.toRingHom.codRestrict V
        fun x => hle x x.2) (RingHom.id Ω) rfl
  obtain ⟨v, hv1⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  have h2 : V.valuation (w / t i ^ e) ≤ 1 := by
    rw [V.valuation_le_one_iff, ← hv1]
    exact v.2
  have h3 : V.valuation (t i ^ e / w) < 1 :=
    V.mem_nonunits_iff.mp (hV' ⟨y i, Ideal.subset_span ⟨i, rfl⟩, rfl⟩)
  have h4 : V.valuation (t i ^ e / w) * V.valuation (w / t i ^ e) = 1 := by
    rw [← map_mul, div_mul_div_cancel₀ hw0, div_self (pow_ne_zero _ hti), map_one]
  exact (mul_lt_one_of_lt_of_le h3 h2).ne h4
end GlobalTheory
