-- Prove2me | solution 1 for MultiwayGap2325.Main.Supplement.cell_flow_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:55:20.335225+00:00
-- url     : https://prove2.me/submissions/db671e0e-870c-436f-b016-75062d245259

import Definitions.Def_MultiwayGap2325_Main_Supplement_Flows

open MultiwayGap2325.Main MultiwayGap2325.Main.Supplement

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open MultiwayGap2325.Main

namespace MultiwayGap2325.Main.Supplement

attribute [local instance] Classical.propDecidable

private lemma continuous_drop {q : ℕ} (S : Face q) : Continuous (drop S) := by
  unfold drop
  fun_prop

private lemma continuous_lift {q : ℕ} (S : Face q) : Continuous (lift S) := by
  apply continuous_pi
  intro i
  simp only [lift]
  split_ifs <;> fun_prop

private lemma drop_lift {q : ℕ} (S : Face q) : Function.LeftInverse (drop S) (lift S) := by
  intro y
  ext j
  simp [drop, lift, j.property.1, j.property.2]

private lemma pivot_mem {q : ℕ} (S : Face q) :
    pivot S ∈ (S : Finset (Fin q)) :=
  Finset.min'_mem _ _

private lemma drop_sum {q : ℕ} (S : Face q) (x : Vec q) :
    (∑ j, drop S x j) = ∑ i ∈ (S : Finset (Fin q)).erase (pivot S), x i := by
  rw [Finset.sum_subtype (p := fun i => i ∈ (S : Finset (Fin q)) ∧ i ≠ pivot S)
    ((S : Finset (Fin q)).erase (pivot S))
    (by intro i; simp [Finset.mem_erase, and_comm]) (fun i => x i)]
  rfl

private lemma lift_drop_on_hull {q : ℕ} {S : Face q} {x : Vec q} (hx : x ∈ hull S) :
    lift S (drop S x) = x := by
  have hsum : (∑ j, drop S x j) + x (pivot S) = 1 := by
    rw [drop_sum, Finset.sum_erase_add _ _ (pivot_mem S)]
    exact hx.2
  ext i
  by_cases hip : i = pivot S
  · subst i
    simp only [lift, ↓reduceIte]
    linarith
  · by_cases his : i ∈ (S : Finset (Fin q))
    · simp [lift, drop, hip, his]
    · simpa [lift, hip, his] using (hx.1 i his).symm

private lemma isClosedEmbedding_lift {q : ℕ} (S : Face q) :
    Topology.IsClosedEmbedding (lift S) :=
  (drop_lift S).isClosedEmbedding (continuous_drop S) (continuous_lift S)

instance isFiniteMeasureOnCompacts_map_lift {q : ℕ} (S : Face q) :
    IsFiniteMeasureOnCompacts (Measure.map (lift S)
      (volume : Measure (Coordinates S → ℝ))) := by
  constructor
  intro K hK
  rw [Measure.map_apply (continuous_lift S).measurable hK.measurableSet]
  exact (isClosedEmbedding_lift S).isCompact_preimage hK |>.measure_lt_top

instance isFiniteMeasureOnCompacts_faceVolume {q : ℕ} (T : ℝ) (S : Face q) :
    IsFiniteMeasureOnCompacts (faceVolume T S) := by
  constructor
  intro K hK
  change ((Measure.map (lift S) (volume : Measure (Coordinates S → ℝ))).restrict
    (omega T S)) K < ⊤
  calc
    _ ≤ (Measure.map (lift S) (volume : Measure (Coordinates S → ℝ))) K :=
      Measure.restrict_le_self K
    _ < ⊤ := hK.measure_lt_top

private lemma isCell_hull {q : ℕ} (T : ℝ) (D : FlowData q) (S : Face q)
    (hD : IsFlowInstance T D) {P : Set (Vec q)} (hP : P ∈ D.weighting.cells S) :
    P ⊆ hull S :=
  (hD.1.1.1 S).1 P hP |>.1

private lemma continuousOn_cell_flow {q : ℕ} (T : ℝ) (D : FlowData q)
    (S : Face q) (hD : IsFlowInstance T D) {P : Set (Vec q)}
    (hP : P ∈ D.weighting.cells S) {l : CutLabel q} (hl : Allowed S l) :
    ContinuousOn (D.field S P l) P := by
  have hcont := (hD.1.2.1 S P hP l hl).1.continuousOn
  have hcomp : ContinuousOn
      ((fun y : Coordinates S → ℝ => D.field S P l (lift S y)) ∘ drop S) P := by
    apply hcont.comp (continuous_drop S).continuousOn
    intro x hx
    change lift S (drop S x) ∈ P
    rwa [lift_drop_on_hull (isCell_hull T D S hD hP hx)]
  apply hcomp.congr
  intro x hx
  simp only [Function.comp_apply]
  rw [lift_drop_on_hull (isCell_hull T D S hD hP hx)]

end MultiwayGap2325.Main.Supplement

theorem solution (q : ℕ) (T : ℝ) (D : FlowData q) (S : Face q)
    (hD : IsFlowInstance T D) (P : Set (Vec q))
    (hP : P ∈ D.weighting.cells S) (l : CutLabel q) (hl : Allowed S l) :
    MeasureTheory.IntegrableOn (D.field S P l) P (faceVolume T S) := by
  have hcompact : IsCompact P := ((hD.1.1.1 S).1 P hP).2.1
  exact (MultiwayGap2325.Main.Supplement.continuousOn_cell_flow
    T D S hD hP hl).integrableOn_compact hcompact
