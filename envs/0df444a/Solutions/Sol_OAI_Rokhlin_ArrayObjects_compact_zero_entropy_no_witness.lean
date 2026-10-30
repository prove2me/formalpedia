-- Prove2me | solution 1 for OAI.Rokhlin.ArrayObjects.compact_zero_entropy_no_witness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:59:35.773033+00:00
-- url     : https://prove2.me/submissions/dc133394-9a3e-44ac-b65c-9c4436dcfcb8

import Mathlib
import Definitions.Def_OAIQ3Ro002
import Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_saturated_correlation_zero

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Arrays
attribute [-instance] _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.columnGroupKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.columnPairKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunArrαYOfNatNatComplexMemAddSubgroupLpENNRealSubmoduleRawSlotActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunCellComplexMemAddSubgroupLpOfNatENNRealSubmoduleSlotActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleColumnActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleCommonActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleRowActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatCellSlotLocal _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatForallCellSlotTupleKernel _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatForallYRawTupleKernel _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsProbabilityMeasureForallSubtypeMemFinsetArrαYColumnCellLaw _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsProbabilityMeasureForallSubtypeMemFinsetArrαYRowCellLaw _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.rowPairKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.splitRowKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Saturating.instNonemptyDataKind _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.arrayLaw_probability _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.localLaw_probability _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section

open MeasureTheory ProbabilityTheory
universe u
namespace ArrayObjects

section

attribute [instance] InitialLaws.probability

attribute [instance] Object.probability

end


end ArrayObjects

open scoped InnerProductSpace

namespace Saturation

variable {𝕜 E H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

theorem projection_difference_inner (J : E →ₗᵢ[𝕜] H)
    (P : Submodule 𝕜 E) (Q : Submodule 𝕜 H)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPQ : ∀ x ∈ P, J x ∈ Q) (v : E) :
    ⟪Q.starProjection (J v) - J (P.starProjection v), J (P.starProjection v)⟫_𝕜 = 0 := by
  have h₁ := Q.starProjection_inner_eq_zero (J v) (J (P.starProjection v))
    (hPQ _ (P.starProjection_apply_mem v))
  have h₂ := P.starProjection_inner_eq_zero v (P.starProjection v)
    (P.starProjection_apply_mem v)
  rw [inner_sub_left] at h₁ h₂ ⊢
  rw [J.inner_map_map] at h₁
  rw [J.inner_map_map, sub_eq_zero] at ⊢
  exact (sub_eq_zero.mp h₁).symm.trans (sub_eq_zero.mp h₂)

theorem projection_norm_difference (J : E →ₗᵢ[𝕜] H)
    (P : Submodule 𝕜 E) (Q : Submodule 𝕜 H)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPQ : ∀ x ∈ P, J x ∈ Q) (v : E) :
    ‖Q.starProjection (J v)‖ ^ 2 - ‖P.starProjection v‖ ^ 2 =
      ‖Q.starProjection (J v) - J (P.starProjection v)‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (Q.starProjection (J v) - J (P.starProjection v)) (J (P.starProjection v))
    (projection_difference_inner J P Q hPQ v)
  simp only [sub_add_cancel, J.norm_map] at h
  nlinarith

theorem projection_eq_of_norm_eq (J : E →ₗᵢ[𝕜] H)
    (P : Submodule 𝕜 E) (Q : Submodule 𝕜 H)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPQ : ∀ x ∈ P, J x ∈ Q) (v : E)
    (h : ‖Q.starProjection (J v)‖ = ‖P.starProjection v‖) :
    Q.starProjection (J v) = J (P.starProjection v) := by
  have he := projection_norm_difference J P Q hPQ v
  rw [h, sub_self] at he
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp he.symm))

theorem projection_norm_mono (J : E →ₗᵢ[𝕜] H)
    (P : Submodule 𝕜 E) (Q : Submodule 𝕜 H)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPQ : ∀ x ∈ P, J x ∈ Q) (v : E) :
    ‖P.starProjection v‖ ≤ ‖Q.starProjection (J v)‖ := by
  have he := projection_norm_difference J P Q hPQ v
  nlinarith [sq_nonneg ‖Q.starProjection (J v) - J (P.starProjection v)‖,
    norm_nonneg (P.starProjection v), norm_nonneg (Q.starProjection (J v))]

end Saturation

namespace ArrayObjects

namespace Object
open scoped ENNReal
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
  {base : InitialLaws I X T}

namespace Extension
variable {M N P : Object I base}

lemma data_comap_le (e : Extension M N) (n : ℕ) (d : DataKind I) :
    MeasurableSpace.comap (amap e.state (n + 1)) (M.data n d) ≤ N.data n d := by
  classical
  have hp : MeasurableSpace.comap (amap e.state (n + 1)) (M.data n .parameter) ≤
      N.data n .parameter := by
    change MeasurableSpace.comap (amap e.state (n + 1))
      (MeasurableSpace.comap (amap M.par (n + 1)) inferInstance) ≤ _
    rw [MeasurableSpace.comap_comp, ← amap_comp, e.state_par, amap_comp]
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_amap e.measurable_parameter _).comap_le
  have ho (j : I) : MeasurableSpace.comap (amap e.state (n + 1)) (M.data n (.outside j)) ≤
      N.data n (.outside j) := by
    change MeasurableSpace.comap (amap e.state (n + 1))
      (MeasurableSpace.comap (planes n (Finset.univ.erase j)) inferInstance) ≤ _
    rw [MeasurableSpace.comap_comp]
    have he : planes n (Finset.univ.erase j) ∘ amap e.state (n + 1) =
        (fun (z : (i : Finset.univ.erase j) → Arr I N.Y n) i => amap e.state n (z i)) ∘
          planes n (Finset.univ.erase j) := rfl
    rw [he, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (Measurable.of_eval (fun i =>
      (measurable_amap e.measurable_state n).comp (measurable_pi_apply i))).comap_le
  cases d with
  | parameter => exact hp
  | outside j => exact ho j
  | enlarged j =>
    change MeasurableSpace.comap (amap e.state (n + 1))
      (M.data n .parameter ⊔ M.data n (.outside j)) ≤
        N.data n .parameter ⊔ N.data n (.outside j)
    rw [MeasurableSpace.comap_sup]
    exact sup_le_sup hp (ho j)

lemma pull_comp (e : Extension M N) (f : Extension N P) (n : ℕ) (F : Lp ℂ 2 (M.law n)) :
    (e.comp f).pull n F = f.pull n (e.pull n F) :=
  Lp.compMeasurePreserving_comp_apply F (e.measurePreserving n) (f.measurePreserving n)

lemma pull_data_mem (e : Extension M N) (n : ℕ) (d : DataKind I)
    (F : Lp ℂ 2 (M.law (n + 1))) (hF : F ∈ lpMeas ℂ ℂ (M.data n d) 2 (M.law (n + 1))) :
    e.pull (n + 1) F ∈ lpMeas ℂ ℂ (N.data n d) 2 (N.law (n + 1)) := by
  have hFm := lpMeas.aestronglyMeasurable (⟨F, hF⟩ : lpMeas ℂ ℂ (M.data n d) 2 (M.law (n + 1)))
  have hm : @Measurable _ _ (N.data n d) (M.data n d) (amap e.state (n + 1)) :=
    measurable_iff_comap_le.mpr (e.data_comap_le n d)
  have hg := hFm.stronglyMeasurable_mk.comp_measurable hm
  have he := (e.measurePreserving (n + 1)).quasiMeasurePreserving.ae_eq_comp hFm.ae_eq_mk
  have hp := Lp.coeFn_compMeasurePreserving F (e.measurePreserving (n + 1))
  exact ⟨hFm.mk F ∘ amap e.state (n + 1), hg, hp.trans he⟩

end Extension
end Object
end ArrayObjects

namespace ArrayObjects.Object
open scoped ENNReal
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
  {base : InitialLaws I X T}

namespace Extension
variable {M N : Object I base}

lemma project_norm_mono (e : Extension M N) (n : ℕ) (d : DataKind I)
    (F : Lp ℂ 2 (M.law (n + 1))) :
    ‖M.project n d F‖ ≤ ‖N.project n d (e.pull (n + 1) F)‖ := by
  let : Fact (M.data n d ≤ (inferInstance : MeasurableSpace (Arr I M.Y (n + 1)))) :=
    ⟨M.data_le n d⟩
  let : Fact (N.data n d ≤ (inferInstance : MeasurableSpace (Arr I N.Y (n + 1)))) :=
    ⟨N.data_le n d⟩
  exact Saturation.projection_norm_mono (e.pull (n + 1))
    (lpMeas ℂ ℂ (M.data n d) 2 (M.law (n + 1)))
    (lpMeas ℂ ℂ (N.data n d) 2 (N.law (n + 1))) (e.pull_data_mem n d) F

lemma project_eq_of_norm_le (e : Extension M N) (n : ℕ) (d : DataKind I)
    (F : Lp ℂ 2 (M.law (n + 1)))
    (h : ‖N.project n d (e.pull (n + 1) F)‖ ≤ ‖M.project n d F‖) :
    N.project n d (e.pull (n + 1) F) = e.pull (n + 1) (M.project n d F) := by
  let : Fact (M.data n d ≤ (inferInstance : MeasurableSpace (Arr I M.Y (n + 1)))) :=
    ⟨M.data_le n d⟩
  let : Fact (N.data n d ≤ (inferInstance : MeasurableSpace (Arr I N.Y (n + 1)))) :=
    ⟨N.data_le n d⟩
  exact Saturation.projection_eq_of_norm_eq (e.pull (n + 1))
    (lpMeas ℂ ℂ (M.data n d) 2 (M.law (n + 1)))
    (lpMeas ℂ ℂ (N.data n d) 2 (N.law (n + 1))) (e.pull_data_mem n d) F
    (le_antisymm h (e.project_norm_mono n d F))

end Extension

end ArrayObjects.Object

open MeasureTheory ProbabilityTheory
open scoped ENNReal

open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory

end

open MeasureTheory ProbabilityTheory

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Saturation
attribute [-instance] _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.columnGroupKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.columnPairKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunArrαYOfNatNatComplexMemAddSubgroupLpENNRealSubmoduleRawSlotActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunCellComplexMemAddSubgroupLpOfNatENNRealSubmoduleSlotActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleColumnActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleCommonActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleRowActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatCellSlotLocal _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatForallCellSlotTupleKernel _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatForallYRawTupleKernel _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsProbabilityMeasureForallSubtypeMemFinsetArrαYColumnCellLaw _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsProbabilityMeasureForallSubtypeMemFinsetArrαYRowCellLaw _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.rowPairKernel_markov _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.splitRowKernel_markov _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Rokhlin

open MeasureTheory ProbabilityTheory
universe u

open MeasureTheory ProbabilityTheory Finset Function Filter Preorder
open scoped ENNReal

open MeasureTheory Filter
open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory

namespace ArrayObjects.Object
open scoped ENNReal
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
  {base : InitialLaws I X T}

namespace Test
variable {M N P : Object I base}

lemma energy_mono (F : Test M) (e : Extension M N) : F.energy ≤ (F.pull e).energy :=
  e.project_norm_mono _ _ _

lemma pull_comp (F : Test M) (e : Extension M N) (f : Extension N P) :
    F.pull (e.comp f) = (F.pull e).pull f := by
  simp only [pull, Extension.pull_comp]
  rfl

end Test
end ArrayObjects.Object

open MeasureTheory
open scoped ENNReal
section

lemma eq_of_finite_stage_Lp {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (ν : ∀ n, Measure (X n)) [∀ n, IsFiniteMeasure (ν n)]
    (π : ∀ n, Ω → X n) (hπ : ∀ n, MeasurePreserving (π n) μ (ν n))
    (hmono : Monotone (fun n => MeasurableSpace.comap (π n) inferInstance))
    (hgen : mΩ = ⨆ n, MeasurableSpace.comap (π n) inferInstance)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B : Lp ℂ 2 μ →L[ℂ] E)
    (hAB : ∀ n F, A (Lp.compMeasurePreserving (π n) (hπ n) F) =
      B (Lp.compMeasurePreserving (π n) (hπ n) F)) : A = B := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let C : Set (Set Ω) := {s | ∃ n, MeasurableSet[MeasurableSpace.comap (π n) inferInstance] s}
  have hCalg : IsSetAlgebra C := by
    refine ⟨⟨0, @MeasurableSet.empty Ω (MeasurableSpace.comap (π 0) inferInstance)⟩, ?_, ?_⟩
    · rintro s ⟨n, hs⟩; exact ⟨n, hs.compl⟩
    · rintro s t ⟨n, hs⟩ ⟨k, ht⟩
      exact ⟨max n k, ((hmono (le_max_left n k)) _ hs).union
        ((hmono (le_max_right n k)) _ ht)⟩
  have hCgen : mΩ = MeasurableSpace.generateFrom C := by
    apply le_antisymm
    · rw [hgen]
      refine iSup_le fun n => ?_
      intro s hs
      exact MeasurableSpace.measurableSet_generateFrom ⟨n, hs⟩
    · apply MeasurableSpace.generateFrom_le
      rintro s ⟨n, hs⟩
      exact (hπ n).measurable.comap_le _ hs
  have hCdense := Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite μ hCalg hCgen
  have hclosed : IsClosed {F : Lp ℂ 2 μ | A F = B F} :=
    isClosed_eq A.continuous B.continuous
  have hCeq (c : ℂ) :
      {indicatorConstLp 2 (hCdense.measurable s hs) hμs c |
        (s : Set Ω) (hs : s ∈ C) (hμs : μ s ≠ ∞)} ⊆ {F | A F = B F} := by
    rintro _ ⟨s, ⟨n, t, ht, rfl⟩, hμs, rfl⟩
    exact hAB n (indicatorConstLp 2 ht (measure_ne_top (ν n) t) c)
  have hall (F : Lp ℂ 2 μ) : A F = B F := by
    apply Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (fun F => A F = B F)
    · intro c s hs hμs
      have hmem := hCdense.indicatorConstLp_subset_closure (p := 2) c ⟨s, hs, hμs.ne, rfl⟩
      exact (closure_minimal (hCeq c) hclosed) hmem
    · intro f g hf hg hfg hF hG
      simp only [map_add, hF, hG]
    · exact hclosed
  exact ContinuousLinearMap.ext hall
end

namespace ArrayObjects.Object
open scoped ENNReal Topology
open Filter
variable {I : Type u} [Fintype I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
  {base : InitialLaws I X T}

namespace Tower
lemma projection_step (D : Tower base) (n : ℕ) :
    (D.step n).comp (D.projection (n + 1)) = D.projection n := by
  apply Extension.ext
  · funext y; exact y.property n
  · funext p; exact p.property n

lemma projection_fields_mono (D : Tower base) (n : ℕ) :
    Monotone (fun i => MeasurableSpace.comap (amap (D.projection i).state n)
      (inferInstance : MeasurableSpace (Arr I (D.stage i).Y n))) := by
  exact InverseSystems.comap_array_path_mono (X := fun i => (D.stage i).Y)
    D.yBond (id : Arr I D.stateSpace n → Arr I D.stateSpace n) D.measurable_yBond

lemma projection_fields_generate (D : Tower base) (n : ℕ) :
    (inferInstance : MeasurableSpace (Arr I D.limit.Y n)) =
      ⨆ i, MeasurableSpace.comap (amap (D.projection i).state n)
        (inferInstance : MeasurableSpace (Arr I (D.stage i).Y n)) := by
  have h := (InverseSystems.comap_array_path (X := fun i => (D.stage i).Y)
      D.yBond (id : Arr I D.stateSpace n → Arr I D.stateSpace n))
  rw [MeasurableSpace.comap_id] at h
  exact h
end Tower

namespace Saturating

lemma origin_le (n : ℕ) : origin n ≤ n :=
  (Nat.unpair_left_le _).trans (Nat.unpair_left_le n)
lemma keys_surjective : Function.Surjective (keys (I := I)) :=
  (exists_surjective_nat (ℕ × DataKind I × ℕ)).choose_spec

attribute [local instance] OAI.Rokhlin.ArrayObjects.Object.Saturating.instFactNeENNRealOfNatTop
lemma dense_range (M : Object I base) (n : ℕ) : DenseRange (dense M n) :=
  TopologicalSpace.denseRange_denseSeq _

lemma listed_key (M : Object I base) (n : ℕ) (d : DataKind I) (r j : ℕ)
    (hj : keys j = (n, d, r)) :
    listed M j = ⟨n, d, dense M n r⟩ := by
  unfold listed
  rw [hj]

namespace Bank

lemma near (b : Bank (base := base)) (n : ℕ) (P : Object I base) (f : Extension b.obj P) :
    ((b.focus n).pull f).energy < ((b.focus n).pull (b.nextMap n)).energy +
      1 / ((n : ℝ) + 1) :=
  (b.focus n |>.exists_near_max (1 / ((n : ℝ) + 1)) (by positivity)).choose_spec.choose_spec P f

end Bank

lemma tests_birth (M : Object I base) (i j : ℕ) :
    (sequence M i).tests i j = listed ((tower M).stage i) j := by
  cases i with
  | zero => rfl
  | succ i => simp [sequence, Bank.next, tower]

lemma tests_transport (M : Object I base) {i n : ℕ} (hi : i ≤ n) (j : ℕ) :
    (sequence M (n + 1)).tests i j =
      ((sequence M n).tests i j).pull ((tower M).step n) := by
  simp [sequence, Bank.next, show i ≠ n + 1 by omega, tower]

lemma tests_limit (M : Object I base) {i n : ℕ} (hi : i ≤ n) (j : ℕ) :
    ((sequence M n).tests i j).pull ((tower M).projection n) =
      (listed ((tower M).stage i) j).pull ((tower M).projection i) := by
  induction n, hi using Nat.le_induction with
  | base => rw [tests_birth]
  | succ n hn ih =>
    rw [tests_transport M hn, ← Test.pull_comp, Tower.projection_step, ih]

lemma listed_maximal (M : Object I base) (i j : ℕ) (P : Object I base)
    (f : Extension (tower M).limit P) :
    (((listed ((tower M).stage i) j).pull ((tower M).projection i)).pull f).energy ≤
      ((listed ((tower M).stage i) j).pull ((tower M).projection i)).energy := by
  let E := (listed ((tower M).stage i) j).pull ((tower M).projection i)
  have h (r : ℕ) : (E.pull f).energy ≤ E.energy + 1 / ((r : ℝ) + 1) := by
    let n := Nat.pair (Nat.pair i j) r
    have hi : i ≤ n := by simpa [n] using origin_le (Nat.pair (Nat.pair i j) r)
    have hn : r ≤ n := Nat.right_le_pair _ _
    have hnear := (sequence M n).near n P (((tower M).projection n).comp f)
    have hfocus : (sequence M n).focus n = (sequence M n).tests i j := by
      simp [Bank.focus, n]
    rw [hfocus, Test.pull_comp, tests_limit M hi j] at hnear
    have hmono := (Test.energy_mono ((sequence M n).tests i j |>.pull ((tower M).step n))
      ((tower M).projection (n + 1)))
    rw [← Test.pull_comp, Tower.projection_step, tests_limit M hi j] at hmono
    have hε : 1 / ((n : ℝ) + 1) ≤ 1 / ((r : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hn)
    change (E.pull f).energy < _ at hnear
    change _ ≤ E.energy at hmono
    change (E.pull f).energy ≤ _
    have heq : (sequence M n).nextMap n = (tower M).step n := rfl
    rw [heq] at hnear
    exact hnear.le.trans (add_le_add hmono hε)
  exact ge_of_tendsto (by simpa using
    (tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) :
      Tendsto (fun r : ℕ => E.energy + 1 / ((r : ℝ) + 1)) atTop (𝓝 (E.energy + 0))))
    (Eventually.of_forall h)

lemma listed_project_eq (M : Object I base) (i j : ℕ) (P : Object I base)
    (f : Extension (tower M).limit P) :
    let G := (listed ((tower M).stage i) j).pull ((tower M).projection i)
    P.project G.level G.kind (f.pull (G.level + 1) G.vector) =
      f.pull (G.level + 1) ((tower M).limit.project G.level G.kind G.vector) := by
  intro G
  apply f.project_eq_of_norm_le
  exact listed_maximal M i j P f

lemma finite_stage_project_eq (M : Object I base) (i n : ℕ) (d : DataKind I)
    (P : Object I base) (f : Extension (tower M).limit P)
    (F : Lp ℂ 2 (((tower M).stage i).law (n + 1))) :
    P.project n d (f.pull (n + 1) (((tower M).projection i).pull (n + 1) F)) =
      f.pull (n + 1) ((tower M).limit.project n d
        (((tower M).projection i).pull (n + 1) F)) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  refine (dense_range _ n).induction_on F
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro r
  obtain ⟨j, hj⟩ := keys_surjective (I := I) (n, d, r)
  have h := listed_project_eq M i j P f
  rw [listed_key _ n d r j hj] at h
  exact h

lemma tower_saturated (M : Object I base) : (tower M).limit.IsSaturated := by
  intro P f n d F
  let A : Lp ℂ 2 ((tower M).limit.law (n + 1)) →L[ℂ] Lp ℂ 2 (P.law (n + 1)) :=
    (P.project n d).comp (f.pull (n + 1)).toContinuousLinearMap
  let B : Lp ℂ 2 ((tower M).limit.law (n + 1)) →L[ℂ] Lp ℂ 2 (P.law (n + 1)) :=
    (f.pull (n + 1)).toContinuousLinearMap.comp ((tower M).limit.project n d)
  have heq : A = B := eq_of_finite_stage_Lp ((tower M).limit.law (n + 1))
    (fun i => ((tower M).stage i).law (n + 1))
    (fun i => amap ((tower M).projection i).state (n + 1))
    (fun i => ((tower M).projection i).measurePreserving (n + 1))
    ((tower M).projection_fields_mono (n + 1))
    ((tower M).projection_fields_generate (n + 1))
    A B (fun i v => finite_stage_project_eq M i n d P f v)
  exact DFunLike.congr_fun heq F

theorem exists_saturated_extension (M : Object I base) :
    ∃ (N : Object I base), Nonempty (Extension M N) ∧ N.IsSaturated :=
  ⟨(tower M).limit, ⟨(tower M).projection 0⟩, tower_saturated M⟩

end Saturating
end ArrayObjects.Object

end Rokhlin

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_WeakLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

namespace ArrayObjects

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology

section InitialCorrelations
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    (base : InitialLaws I X T) (hk : 3 ≤ Fintype.card I)
    {μ : Measure X} [IsProbabilityMeasure μ] (hμ : (base.law 0).map (zeroEquiv I X) = μ)
    (hT : MeasurePreserving T μ μ)
    (hmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun n => μ (A ∩ (T^[n]) ⁻¹' B)) atTop (𝓝 (μ A * μ B)))
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (α : X → A) (hα : Measurable α) (v : A → ℂ)
    (hcenter : ∫ z, v (α z) ∂μ = 0)
    (hH : Tendsto (fun n : ℕ => Rokhlin.wordEntropy (η := μ) (fun m z => α ((T^[m]) z)) n / n)
      atTop (𝓝 0))
include hk hμ hT hmix hα hcenter hH in
lemma initial_correlation_zero (i : I) (f : I → X → ℂ)
    (hf : ∀ j, Measurable (f j)) (hb : ∀ j y, ‖f j y‖ ≤ 1)
    (hi : ∀ y, f i y = v (α y)) :
    (∫ y, ∏ j, f j (zeroEquiv I X (plane 0 0 j y)) ∂base.law 1) = 0 := by
  obtain ⟨M,he,hM⟩ := Object.Saturating.exists_saturated_extension (initialObject base)
  have hμM : M.localLaw.map M.x = μ := by
    rw [Object.localLaw,Measure.map_map M.measurable_x (zeroEquiv I M.Y).measurable]
    have he : M.x ∘ zeroEquiv I M.Y = zeroEquiv I X ∘ amap M.x 0 := rfl
    rw [he,←Measure.map_map (zeroEquiv I X).measurable (measurable_amap M.measurable_x 0),M.over_base,hμ]
  have h := Object.Rolled.saturated_correlation_zero M hM hk hμM hT hmix α hα v hcenter hH i
    (fun j => f j ∘ M.x ∘ zeroEquiv I M.Y)
    (fun j => (hf j).comp (M.measurable_x.comp (zeroEquiv I M.Y).measurable))
    (fun j y => hb j _) (fun y => hi _)
  rw [←M.over_base 1,integral_map (measurable_amap M.measurable_x 1).aemeasurable
    (show AEStronglyMeasurable (fun y : Arr I X 1 => ∏ j, f j (zeroEquiv I X (plane 0 0 j y)))
      ((M.law 1).map (amap M.x 1)) from
      (Finset.measurable_prod _ (fun j _ => (hf j).comp ((zeroEquiv I X).measurable.comp
        (measurable_plane _ _ _)))).aestronglyMeasurable)]
  exact h
end InitialCorrelations


universe u

end ArrayObjects

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped Topology BigOperators
namespace ArrayObjects
universe u
variable {I : Type u} [Fintype I] [retained15 : DecidableEq I]
    {X : StandardSpace.{u}} [TopologicalSpace X] [retained16 : CompactSpace X] [retained17 : T2Space X]
    [SecondCountableTopology X] [retained18 : MetrizableSpace X] [BorelSpace X]
    (T : X ≃ₜ X) (d : ℕ → I → ℕ) (μ : ProbabilityMeasure X)

variable (hμ : MeasurePreserving T μ μ)
    (hrect : ∀ J : Finset I, J ≠ Finset.univ → ∀ s : J → Set X,
      (∀ j, MeasurableSet (s j)) → Tendsto
        (fun b => (μ : Measure X) (⋂ j : J, (T^[d b j]) ⁻¹' s j)) atTop
        (𝓝 (∏ j : J, (μ : Measure X) (s j))))

lemma weakInitialLaws_zero : ((weakInitialLaws T d μ hμ hrect).law 0).map (zeroEquiv I X) = μ := by
  change ((μ : Measure X).map (fun x _ => x)).map (zeroEquiv I X) = μ
  rw [Measure.map_map (zeroEquiv I X).measurable (show Measurable (fun x : X => fun _ : Index I 0 => x) from Measurable.of_eval fun _ => measurable_id)]
  exact Measure.map_id

lemma weakInitialLaws_correlation (f : I → C(X,ℝ)) (δ : ℝ)
    (hc : ∀ b, δ ≤ ∫ x, ∏ i, f i ((T^[d b i]) x) ∂(μ : Measure X)) :
    δ ≤ ∫ y, ∏ i, f i (zeroEquiv I X (plane 0 0 i y))
      ∂(weakInitialLaws T d μ hμ hrect).law 1 := by
  let F : C(Arr I X 1,ℝ) := ⟨fun y => ∏ i, f i (zeroEquiv I X (plane 0 0 i y)),
    continuous_finsetProd _ (fun i _ => (f i).continuous.comp (continuous_apply _))⟩
  have h := (ProbabilityMeasure.continuous_integral_continuousMap F).tendsto
    (weakArrayLaw T d (Ultrafilter.of atTop) μ 1) |>.comp
      (weakArrayLaw_tendsto T d (Ultrafilter.of atTop) μ 0)
  apply ge_of_tendsto h
  apply Eventually.of_forall
  intro b
  change δ ≤ ∫ y, F y ∂(((μ : Measure X).map (fun x _ => x)).map (firstDuplicate T (d b) 0))
  rw [Measure.map_map (continuous_firstDuplicate T (d b) 0).measurable
    (show Measurable (fun x : X => fun _ : Index I 0 => x) from Measurable.of_eval fun _ => measurable_id),
    integral_map ((continuous_firstDuplicate T (d b) 0).measurable.comp
      (show Measurable (fun x : X => fun _ : Index I 0 => x) from Measurable.of_eval fun _ => measurable_id)).aemeasurable F.continuous.measurable.aestronglyMeasurable]
  exact hc b

include hμ hrect in

lemma compact_zero_entropy_no_witness_oai (hk : 3 ≤ Fintype.card I)
    (hmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun n => (μ : Measure X) (A ∩ (T^[n]) ⁻¹' B)) atTop
        (𝓝 ((μ : Measure X) A * (μ : Measure X) B)))
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (α : X → A) (hα : Measurable α) (v : A → ℝ)
    (hcenter : ∫ x, v (α x) ∂(μ : Measure X) = 0)
    (hH : Tendsto (fun n : ℕ => Rokhlin.wordEntropy (η := (μ : Measure X))
      (fun m x => α ((T^[m]) x)) n / n) atTop (𝓝 0))
    (i : I) (f : I → C(X,ℝ)) (hb : ∀ j x, |f j x| ≤ 1)
    (hi : ∀ x, f i x = v (α x)) (δ : ℝ) (hδ : 0 < δ)
    (hc : ∀ b, δ ≤ ∫ x, ∏ j, f j ((T^[d b j]) x) ∂(μ : Measure X)) : False := by
  let base := weakInitialLaws T d μ hμ hrect
  have hz := initial_correlation_zero base hk (weakInitialLaws_zero T d μ hμ hrect) hμ hmix
    α hα (fun a => (v a : ℂ)) (by rw [integral_complex_ofReal,hcenter,Complex.ofReal_zero]) hH i
    (fun j x => (f j x : ℂ))
    (fun j => Complex.continuous_ofReal.measurable.comp (f j).continuous.measurable)
    (fun j x => by simpa only [Complex.norm_real,Real.norm_eq_abs] using hb j x)
    (fun x => congrArg Complex.ofReal (hi x))
  have hzR : (∫ y, ∏ j, f j (zeroEquiv I X (plane 0 0 j y)) ∂base.law 1) = 0 := by
    have hh := congrArg Complex.re hz
    simpa only [←Complex.ofReal_prod,integral_complex_ofReal,Complex.ofReal_re,Complex.zero_re] using hh
  have hpos := weakInitialLaws_correlation T d μ hμ hrect f δ hc
  rw [show (weakInitialLaws T d μ hμ hrect) = base from rfl,hzR] at hpos
  exact (not_le_of_gt hδ) hpos
end ArrayObjects

end Rokhlin

end

end OAI
end

theorem solution.{u, u_1} : type_of% @OAI.Rokhlin.ArrayObjects.compact_zero_entropy_no_witness_oai.{u, u_1} := @OAI.Rokhlin.ArrayObjects.compact_zero_entropy_no_witness_oai.{u, u_1}
