-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_forall_mem_asIdeal_iff_norm_padicEmbedding_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/bd90ca84-7a57-5cc5-a121-ef46993d29b5

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_exists_forall_mem_asIdeal_iff_norm_padicEmbedding_lt_one
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

namespace PBCutout

variable (q : ℕ) [Fact q.Prime] (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F]
  (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem norm_le_one (x : 𝓞 ↥F) : ‖padicEmbedding q (σ ((x : ↥F) : AlgebraicClosure ℚ))‖ ≤ 1 := by
  have hint : IsIntegral ℤ (σ ((x : ↥F) : AlgebraicClosure ℚ)) :=
    map_isIntegral_int σ (map_isIntegral_int (algebraMap ↥F (AlgebraicClosure ℚ)) x.isIntegral_coe)
  let A : ValuationSubring (AlgebraicClosure ℚ) := padicPlace q
  have hO : IsIntegral ↥(A.valuation.integer) (σ ((x : ↥F) : AlgebraicClosure ℚ)) := by
    obtain ⟨p, hp, hpx⟩ := hint
    refine ⟨p.map (algebraMap ℤ ↥(A.valuation.integer)), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, Subsingleton.elim ((algebraMap ↥(A.valuation.integer) (AlgebraicClosure ℚ)).comp (algebraMap ℤ ↥(A.valuation.integer))) (algebraMap ℤ (AlgebraicClosure ℚ))]
    exact hpx
  have hmemI : σ ((x : ↥F) : AlgebraicClosure ℚ) ∈ A.valuation.integer :=
    Valuation.Integers.mem_of_integral (Valuation.integer.integers A.valuation) hO
  have hmem : σ ((x : ↥F) : AlgebraicClosure ℚ) ∈ A := (A.valuation_le_one_iff _).1 ((Valuation.mem_integer_iff _ _).1 hmemI)
  have h := (mem_padicPlace_iff q).1 hmem
  exact_mod_cast h

def cutIdeal : Ideal (𝓞 ↥F) where
  carrier := {x | ‖padicEmbedding q (σ ((x : ↥F) : AlgebraicClosure ℚ))‖ < 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    push_cast
    rw [map_add, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' c x hx := by
    simp only [Set.mem_setOf_eq, smul_eq_mul] at hx ⊢
    push_cast
    rw [map_mul, map_mul, norm_mul]
    calc ‖padicEmbedding q (σ ((c : ↥F) : AlgebraicClosure ℚ))‖ * ‖padicEmbedding q (σ ((x : ↥F) : AlgebraicClosure ℚ))‖
        ≤ 1 * ‖padicEmbedding q (σ ((x : ↥F) : AlgebraicClosure ℚ))‖ := by gcongr; exact norm_le_one q F σ c
      _ < 1 := by rw [one_mul]; exact hx

theorem mem_cutIdeal_iff (x : 𝓞 ↥F) : x ∈ cutIdeal q F σ ↔ ‖padicEmbedding q (σ ((x : ↥F) : AlgebraicClosure ℚ))‖ < 1 := Iff.rfl

theorem one_not_mem : (1 : 𝓞 ↥F) ∉ cutIdeal q F σ := by
  rw [mem_cutIdeal_iff]
  push_cast
  rw [map_one, map_one, norm_one]
  exact lt_irrefl 1

theorem cutIdeal_isPrime : (cutIdeal q F σ).IsPrime := by
  refine ⟨(Ideal.ne_top_iff_one _).2 (one_not_mem q F σ), fun {x y} hxy => ?_⟩
  rw [mem_cutIdeal_iff] at hxy
  push_cast at hxy
  rw [map_mul, map_mul, norm_mul] at hxy
  by_contra h
  rw [not_or, mem_cutIdeal_iff, mem_cutIdeal_iff, not_lt, not_lt] at h
  have h1 : (1 : ℝ) * 1 ≤ ‖padicEmbedding q (σ ((x : ↥F) : AlgebraicClosure ℚ))‖ * ‖padicEmbedding q (σ ((y : ↥F) : AlgebraicClosure ℚ))‖ :=
    mul_le_mul h.1 h.2 zero_le_one (norm_nonneg _)
  rw [one_mul] at h1
  exact lt_irrefl _ (h1.trans_lt hxy)

theorem natCast_mem : ((q : ℕ) : 𝓞 ↥F) ∈ cutIdeal q F σ := by
  rw [mem_cutIdeal_iff]
  push_cast
  rw [map_natCast, map_natCast]
  have : ((q : ℕ) : PadicAlgCl q) = algebraMap ℚ_[q] (PadicAlgCl q) (q : ℚ_[q]) := by rw [map_natCast]
  rw [this, norm_algebraMap']
  rw [Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : q.Prime).one_lt)

theorem cutIdeal_ne_bot : cutIdeal q F σ ≠ ⊥ := fun h => by
  have h1 := natCast_mem q F σ
  rw [h, Ideal.mem_bot] at h1
  exact (Nat.cast_ne_zero.2 (Fact.out : q.Prime).ne_zero) h1

def cutPlace : HeightOneSpectrum (𝓞 ↥F) := ⟨cutIdeal q F σ, cutIdeal_isPrime q F σ, cutIdeal_ne_bot q F σ⟩

end PBCutout

theorem solution
    (q : ℕ) [Fact q.Prime]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ w : HeightOneSpectrum (𝓞 ↥F),
      (∀ x : 𝓞 ↥F, x ∈ w.asIdeal ↔ ‖padicEmbedding q (σ ((x : ↥F) : AlgebraicClosure ℚ))‖ < 1) ∧ ((q : ℕ) : 𝓞 ↥F) ∈ w.asIdeal :=
  ⟨PBCutout.cutPlace q F σ, fun _ => Iff.rfl, PBCutout.natCast_mem q F σ⟩

end S_NumberField_PlaceDecomp_exists_forall_mem_asIdeal_iff_norm_padicEmbedding_lt_one
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_forall_mem_asIdeal_iff_norm_padicEmbedding_lt_one (solution)
