-- Prove2me | solution 1 for LocalLemma.coin_const_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:21:18.237145+00:00
-- url     : https://prove2.me/submissions/1583d11f-ed50-4d3d-9574-598d6937e2ab

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma
namespace LocalLemma
theorem _root_.solution {ι : Type*} [Fintype ι] (E : Finset ι) (b : Bool) :
    coinMeasure ι {ω | ∀ i ∈ E, ω i = b} = (2⁻¹ : ENNReal) ^ E.card := by
  classical
  have hs : {ω : ι → Bool | ∀ i ∈ E, ω i = b} =
      Set.univ.pi fun i => if i ∈ E then {b} else Set.univ := by
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    refine forall_congr' fun i => ?_
    split_ifs <;> simp_all
  rw [hs, coinMeasure, Measure.pi_pi]
  have : ∀ i, (PMF.uniformOfFintype Bool).toMeasure (if i ∈ E then {b} else Set.univ) =
      if i ∈ E then (2⁻¹ : ENNReal) else 1 := by
    intro i
    split_ifs
    · rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
      simp [PMF.uniformOfFintype_apply]
    · exact measure_univ
  simp_rw [this]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
end LocalLemma
