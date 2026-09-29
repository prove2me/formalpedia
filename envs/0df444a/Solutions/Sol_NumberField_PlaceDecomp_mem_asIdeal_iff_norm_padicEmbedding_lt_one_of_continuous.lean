-- Prove2me | solution 1 for NumberField.PlaceDecomp.mem_asIdeal_iff_norm_padicEmbedding_lt_one_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c2fb4d80-c85a-5c7a-aad0-de947099c444

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

namespace P2MW.S_NumberField_PlaceDecomp_mem_asIdeal_iff_norm_padicEmbedding_lt_one_of_continuous
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

namespace PBCut

variable (q : ℕ) [Fact q.Prime] (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F]
  (w : HeightOneSpectrum (𝓞 ↥F)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
  (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
  (hΦF : ∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ)))
  (hcont : Continuous Φ)

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

include hΦF hcont

theorem norm_lt_one_of_mem (x : 𝓞 ↥F) (hx : x ∈ w.asIdeal) :
    ‖padicEmbedding q (σ ((x : ↥F) : AlgebraicClosure ℚ))‖ < 1 := by
  have hv : Valued.v ((((WithVal.equiv (w.valuation ↥F)).symm (x : ↥F)) : w.adicCompletion ↥F)) < 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem w x).2 hx
  have ht := Valued.tendsto_zero_pow_of_v_lt_one hv
  have ht' : Filter.Tendsto (fun n : ℕ => (padicEmbedding q (σ ((x : ↥F) : AlgebraicClosure ℚ))) ^ n) Filter.atTop (nhds 0) := by
    have h2 := (hcont.tendsto 0).comp ht
    rw [map_zero] at h2
    refine h2.congr (fun n => ?_)
    change Φ ((algebraMap ↥F (w.adicCompletion ↥F) (x : ↥F)) ^ n) = _
    rw [map_pow, hΦF]
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 ht'

theorem mem_asIdeal_iff (x : 𝓞 ↥F) : x ∈ w.asIdeal ↔ ‖padicEmbedding q (σ ((x : ↥F) : AlgebraicClosure ℚ))‖ < 1 := by
  refine ⟨norm_lt_one_of_mem q F w σ Φ hΦF hcont x, fun h => ?_⟩
  by_contra hx
  obtain ⟨y, i, hi, hyxi⟩ := w.isMaximal.exists_inv hx
  let f : 𝓞 ↥F → PadicAlgCl q := fun z => padicEmbedding q (σ ((z : ↥F) : AlgebraicClosure ℚ))
  have hf1 : f y * f x + f i = 1 := by
    have := congrArg f hyxi
    simp only [f] at this ⊢
    push_cast at this
    rw [map_add, map_mul, map_add, map_mul] at this
    simpa using this
  have hlt : ‖f y * f x + f i‖ < 1 := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ (norm_lt_one_of_mem q F w σ Φ hΦF hcont i hi))
    rw [norm_mul]
    calc ‖f y‖ * ‖f x‖ ≤ 1 * ‖f x‖ := by gcongr; exact norm_le_one q F σ y
      _ < 1 := by rw [one_mul]; exact h
  rw [hf1, norm_one] at hlt
  exact lt_irrefl _ hlt

end PBCut

theorem solution
    (q : ℕ) [Fact q.Prime]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (hΦF : ∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ)))
    (hcont : Continuous Φ) :
    ∀ x : 𝓞 ↥F, x ∈ w.asIdeal ↔ ‖padicEmbedding q (σ ((x : ↥F) : AlgebraicClosure ℚ))‖ < 1 :=
  fun x => PBCut.mem_asIdeal_iff q F w σ Φ hΦF hcont x

end S_NumberField_PlaceDecomp_mem_asIdeal_iff_norm_padicEmbedding_lt_one_of_continuous
end P2MW
export P2MW.S_NumberField_PlaceDecomp_mem_asIdeal_iff_norm_padicEmbedding_lt_one_of_continuous (solution)
