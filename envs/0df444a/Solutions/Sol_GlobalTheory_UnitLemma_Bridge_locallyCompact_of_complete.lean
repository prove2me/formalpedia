-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Bridge.locallyCompact_of_complete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:51:58.233942+00:00
-- url     : https://prove2.me/submissions/1110ff3b-19b0-4e29-b4b8-2c447248a77f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyCompactOfComplete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Bridge
namespace GlobalTheory.UnitLemma.Bridge
theorem _root_.solution {O E : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [NormedField E] [Algebra O E] (hinj : Function.Injective (algebraMap O E))
    (hball : ∀ y : E, ‖y‖ ≤ 1 ↔ y ∈ (algebraMap O E).range) : LocallyCompactSpace E := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπ0 : algebraMap O E π ≠ 0 := fun h => hπ.ne_zero (hinj (by rw [h, map_zero]))
  have hpos : 0 < ‖algebraMap O E π‖ := norm_pos_iff.2 hπ0
  have hlt : ‖algebraMap O E π‖ < 1 := by
    by_contra h
    have : ‖(algebraMap O E π)⁻¹‖ ≤ 1 := by
      rw [norm_inv]; exact inv_le_one_of_one_le₀ (not_lt.1 h)
    obtain ⟨z, hz⟩ := (hball _).1 this
    apply hπ.not_isUnit
    refine IsUnit.of_mul_eq_one z (hinj ?_)
    rw [map_mul, hz, map_one, mul_inv_cancel₀ hπ0]
  have hmem : ∀ (n : ℕ) (x : O), x ∈ IsLocalRing.maximalIdeal O ^ n ↔
      ‖algebraMap O E x‖ ≤ ‖algebraMap O E π‖ ^ n := by
    intro n x
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨a, rfl⟩
      rw [map_mul, map_pow, norm_mul, norm_pow]
      exact mul_le_of_le_one_left (by positivity) ((hball _).2 ⟨a, rfl⟩)
    · intro h
      have : ‖algebraMap O E x / algebraMap O E π ^ n‖ ≤ 1 := by
        rw [norm_div, norm_pow]; exact div_le_one_of_le₀ h (by positivity)
      obtain ⟨z, hz⟩ := (hball _).1 this
      refine ⟨z, hinj ?_⟩
      rw [map_mul, map_pow, hz, div_mul_cancel₀ _ (pow_ne_zero _ hπ0)]
  letI : MetricSpace O := MetricSpace.induced (algebraMap O E) hinj inferInstance
  have hdist : ∀ a b : O, dist a b = ‖algebraMap O E (a - b)‖ := by
    intro a b
    rw [map_sub, ← dist_eq_norm]; rfl
  have hcomp : CompleteSpace O := by
    refine Metric.complete_of_convergent_controlled_sequences (fun N => ‖algebraMap O E π‖ ^ N)
      (fun n => by positivity) fun u hu => ?_
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := IsLocalRing.maximalIdeal O) (M := O) inferInstance (f := u) (by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hmem, ← hdist]
      exact (hu m m n le_rfl hmn).le)
    refine ⟨L, tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hlt))⟩
    have := hL n
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hmem, ← hdist] at this
  have htb : TotallyBounded (Set.univ : Set O) := by
    refine Metric.totallyBounded_iff.2 fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hlt
    haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) := ‹Finite (IsLocalRing.ResidueField O)›
    haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O ^ n) :=
      Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
    refine ⟨Set.range (Quotient.out : O ⧸ IsLocalRing.maximalIdeal O ^ n → O), Set.finite_range _, fun x _ => ?_⟩
    refine Set.mem_biUnion (Set.mem_range_self (Ideal.Quotient.mk _ x)) ?_
    rw [Metric.mem_ball, hdist]
    refine lt_of_le_of_lt ((hmem n _).1 ?_) hn
    rw [← Ideal.Quotient.eq]
    exact (Ideal.Quotient.mk_out _).symm
  have hcpt : IsCompact (Set.univ : Set O) := isCompact_iff_totallyBounded_isComplete.2 ⟨htb, complete_univ⟩
  have hcont : Continuous (algebraMap O E) := continuous_induced_dom
  refine (hcpt.image hcont).locallyCompactSpace_of_mem_nhds_of_addGroup (x := 0) ?_
  refine Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos) fun y hy => ?_
  obtain ⟨z, hz⟩ := (hball y).1 (by simpa using hy)
  exact ⟨z, trivial, hz⟩
end GlobalTheory.UnitLemma.Bridge
