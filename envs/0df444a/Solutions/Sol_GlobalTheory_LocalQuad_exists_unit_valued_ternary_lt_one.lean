-- Prove2me | solution 1 for GlobalTheory.LocalQuad.exists_unit_valued_ternary_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:06:00.330927+00:00
-- url     : https://prove2.me/submissions/d20b1451-93fe-4861-ba52-8670907ea850

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNonzeroIsotropic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitValuedTernaryLtOne
import Theorems.Thm_GlobalTheory_LocalQuad_TernaryResidue_exists_ne_zero_sum_eq_zero
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
namespace GlobalTheory.LocalQuad
theorem _root_.solution (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (c : Fin 3 → Fin 3 → v.adicCompletion F)
    (hc : ∀ i j, Valued.v (c i j) ≤ 1) :
    ∃ x : Fin 3 → v.adicCompletion F, (∀ i, Valued.v (x i) ≤ 1) ∧ (∃ i, Valued.v (x i) = 1) ∧
      Valued.v (∑ i, ∑ j, c i j * x i * x j) < 1 := by
  classical
  choose r hr using fun i j => GlobalTheory.Idele.exists_valued_sub_le v (hc i j) 1
  let ι : 𝓞 F →+* v.adicCompletion F :=
    (algebraMap F (v.adicCompletion F)).comp (algebraMap (𝓞 F) F)
  have hι : ∀ y : 𝓞 F, Valued.v (ι y) = v.valuation F (algebraMap (𝓞 F) F y) := fun y =>
    GlobalTheory.Idele.valued_algebraMap v _
  have hle : ∀ y : 𝓞 F, Valued.v (ι y) ≤ 1 := fun y => by
    rw [hι]; exact v.valuation_le_one y
  have hlt : ∀ y : 𝓞 F, Valued.v (ι y) < 1 ↔ y ∈ v.asIdeal := fun y => by
    rw [hι]; exact v.valuation_lt_one_iff_mem y
  have hr' : ∀ i j, Valued.v (c i j - ι (r i j)) < 1 := fun i j => by
    refine (hr i j).trans_lt ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  obtain ⟨x, hx0, hx⟩ := TernaryResidue.exists_ne_zero_sum_eq_zero
    (k := 𝓞 F ⧸ v.asIdeal) fun i j => Ideal.Quotient.mk v.asIdeal (r i j)
  choose y hy using fun i => Ideal.Quotient.mk_surjective (x i)
  refine ⟨fun i => ι (y i), fun i => hle _, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hx0
    refine ⟨i, le_antisymm (hle _) (not_lt.1 fun h => hi ?_)⟩
    rw [← hy i]
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hlt _).1 h)
  · have hmem : (∑ i, ∑ j, r i j * y i * y j) ∈ v.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hx]
      simp only [map_sum, map_mul, hy]
    have hsplit : ∑ i, ∑ j, c i j * ι (y i) * ι (y j) =
        ι (∑ i, ∑ j, r i j * y i * y j) +
          ∑ i, ∑ j, (c i j - ι (r i j)) * ι (y i) * ι (y j) := by
      simp only [map_sum, map_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsplit]
    refine Valuation.map_add_lt _ ((hlt _).2 hmem) ?_
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => Valuation.map_sum_lt _ one_ne_zero
      fun j _ => ?_
    rw [map_mul, map_mul]
    exact (mul_le_of_le_one_right' (hle _)).trans_lt
      ((mul_le_of_le_one_right' (hle _)).trans_lt (hr' i j))
end GlobalTheory.LocalQuad
