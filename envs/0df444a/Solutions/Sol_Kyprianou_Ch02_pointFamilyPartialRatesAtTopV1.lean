-- Prove2me | solution 1 for Kyprianou.Ch02.pointFamilyPartialRatesAtTopV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T08:08:11.008457+00:00
-- url     : https://prove2.me/submissions/3853fc9c-32e6-468f-938c-ae4b0d278f28

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PrMPartialCount
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

theorem solution
    {E : Type} [MeasurableSpace E] (m : Measure E)
    [SigmaFinite m] [Nonempty E]
    (A : Set E) (hA : MeasurableSet A) (hInf : m A = ⊤) :
    Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range (n + 1),
        (m (ProbabilityTheory.prmPiece m k ∩ A)).toNNReal)
      atTop atTop := by
  classical
  have hsum : ∑' k, m (ProbabilityTheory.prmPiece m k ∩ A) = m A := by
    rw [← measure_iUnion
      (fun i j hij =>
        (ProbabilityTheory.pairwise_disjoint_prmPiece hij).mono
          Set.inter_subset_left Set.inter_subset_left)
      (fun k => ProbabilityTheory.measurableSet_prmPiece.inter hA),
      ← Set.iUnion_inter, ProbabilityTheory.iUnion_prmPiece, Set.univ_inter]
  have hfin (k : ℕ) :
      m (ProbabilityTheory.prmPiece m k ∩ A) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.inter_subset_left)
      ProbabilityTheory.measure_prmPiece_lt_top
  have hcast (k : ℕ) :
      ((m (ProbabilityTheory.prmPiece m k ∩ A)).toNNReal : ENNReal) =
        m (ProbabilityTheory.prmPiece m k ∩ A) :=
    ENNReal.coe_toNNReal (hfin k).ne
  have hsumTop :
      (∑' k : ℕ, ((m (ProbabilityTheory.prmPiece m k ∩ A)).toNNReal : ENNReal)) =
        ⊤ := by
    simp_rw [hcast]
    exact hsum.trans hInf
  have hns : ¬Summable
      (fun k : ℕ => (m (ProbabilityTheory.prmPiece m k ∩ A)).toNNReal) :=
    fun hs => (ENNReal.tsum_coe_ne_top_iff_summable.mpr hs) hsumTop
  exact (NNReal.not_summable_iff_tendsto_nat_atTop.mp hns).comp
    (tendsto_add_atTop_nat 1)
