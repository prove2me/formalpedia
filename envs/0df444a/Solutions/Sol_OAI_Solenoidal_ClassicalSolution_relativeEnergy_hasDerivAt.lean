-- Prove2me | solution 1 for OAI.Solenoidal.ClassicalSolution.relativeEnergy_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:09:10.416226+00:00
-- url     : https://prove2.me/submissions/97bd9d8d-b17d-473e-9ae9-2c222eac7b69

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/EnergyIdentities.lean:L265-L280
-- (upload_full_project.md Phase 4): solution for node OAI.Solenoidal.ClassicalSolution.relativeEnergy_hasDerivAt. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EnergyIdentities

-- ---- from OAI.MathematicalPhysics.SheetFlows.Differential ----
namespace OAI

/-! SheetFlows differential. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

theorem continuous_integrableOn_cell {E : Type*} [NormedAddCommGroup E]
    {g : Space → E} (hg : Continuous g) : IntegrableOn g fundamentalCell := by
  apply (hg.integrableOn_Icc (a := (0 : Space)) (b := fun _ => 10)).mono_set
  intro x hx
  constructor
  · intro j
    exact (hx j (Set.mem_univ j)).1
  · intro j
    exact (hx j (Set.mem_univ j)).2.le

section DirectionalCalculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end DirectionalCalculus

end Solenoidal
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.ClassicalRegularity ----
namespace OAI

/-! SheetFlows classical regularity. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Solenoidal

theorem cylinder_spatial_slice {E : Type*} [TopologicalSpace E]
    {g : ℝ → Space → E} {T t : ℝ}
    (hg : ContinuousOn (fun z : SpaceTime => g z.1 z.2) (cylinder T))
    (ht : t ∈ Set.Icc 0 T) : Continuous (g t) := by
  simpa only [Function.comp_def, id_eq] using hg.comp_continuous
    (continuous_const.prodMk continuous_id) (fun x => ⟨ht, Set.mem_univ x⟩)

theorem kineticDensity_continuous : Continuous kineticDensity := by
  unfold kineticDensity
  exact continuous_finsetSum Finset.univ (fun i _ =>
    ((continuous_apply i).fun_mul (continuous_apply i)).div_const 2)

end Solenoidal
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.EnergyIdentities ----
namespace OAI

/-! SheetFlows energy identities. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Solenoidal

theorem measurableSet_fundamentalCell : MeasurableSet fundamentalCell :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ico)

theorem fundamentalCell_subset_cube : fundamentalCell ⊆ Set.Icc (0 : Space) (fun _ => 10) := by
  intro x hx
  exact ⟨fun j => (hx j (Set.mem_univ j)).1, fun j => (hx j (Set.mem_univ j)).2.le⟩

theorem cylinder_uniform_bound {E : Type*} [NormedAddCommGroup E]
    {g : ℝ → Space → E} {T : ℝ}
    (hc : ContinuousOn (fun z : SpaceTime => g z.1 z.2) (cylinder T)) :
    ∃ B : ℝ, ∀ t ∈ Set.Icc 0 T, ∀ x ∈ fundamentalCell, ‖g t x‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod (isCompact_Icc (a := (0 : Space))
    (b := fun _ => 10))).exists_bound_of_continuousOn
      (hc.mono (fun z hz => ⟨hz.1, Set.mem_univ z.2⟩))
  exact ⟨B, fun t ht x hx => hB (t, x) ⟨ht, fundamentalCell_subset_cube hx⟩⟩

theorem cylinder_integral_hasDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g g' : ℝ → Space → E}
    (hc : ∀ T, 0 ≤ T → ContinuousOn (fun z : SpaceTime => g z.1 z.2) (cylinder T))
    (hc' : ∀ T, 0 ≤ T → ContinuousOn (fun z : SpaceTime => g' z.1 z.2) (cylinder T))
    (hd : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => g s x) (g' t x) t)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x in fundamentalCell, g s x)
      (∫ x in fundamentalCell, g' t x) t := by
  have hT : 0 ≤ t + 1 := by linarith
  have htT : t ∈ Set.Icc 0 (t + 1) := ⟨ht.le, by linarith⟩
  have hn : Set.Ioo 0 (t + 1) ∈ 𝓝 t := isOpen_Ioo.mem_nhds ⟨ht, by linarith⟩
  obtain ⟨B, hB⟩ := cylinder_uniform_bound (hc' (t+1) hT)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun _ : Space => B) (s := Set.Ioo 0 (t+1)) hn ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hn] with s hs
    exact (continuous_integrableOn_cell (cylinder_spatial_slice (hc (t+1) hT)
      ⟨hs.1.le, hs.2.le⟩)).aestronglyMeasurable
  · exact continuous_integrableOn_cell (cylinder_spatial_slice (hc (t+1) hT) htT)
  · exact (continuous_integrableOn_cell (cylinder_spatial_slice (hc' (t+1) hT) htT)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_fundamentalCell] with x hx
    exact fun s hs => hB s ⟨hs.1.le, hs.2.le⟩ x hx
  · exact continuous_integrableOn_cell continuous_const
  · exact Filter.Eventually.of_forall (fun x s hs => hd s hs.1 x)

theorem hasDerivAt_kineticDensity {w : ℝ → Space} {w' : Space} {t : ℝ}
    (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => kineticDensity (w s))
      (∑ i : Fin 3, w t i * w' i) t := by
  have hi (i : Fin 3) : HasDerivAt (fun s => w s i) (w' i) t :=
    (ContinuousLinearMap.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hw
  have hf : HasDerivAt (fun s => ∑ i : Fin 3, w s i * w s i / 2)
      (∑ i : Fin 3, (w' i * w t i + w t i * w' i) / 2) t := by
    exact HasDerivAt.fun_sum (fun i _ => ((hi i).fun_mul (hi i)).div_const 2)
  have he : (∑ i : Fin 3, (w' i * w t i + w t i * w' i) / 2) =
      ∑ i : Fin 3, w t i * w' i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa only [he, kineticDensity] using hf

theorem ClassicalSolution.hasDerivAt {ν : ℝ} {f u : Field} {p : Pressure}
    (h : ClassicalSolution ν f u p) {t : ℝ} (ht : 0 < t) (x : Space) :
    HasDerivAt (fun s => u s x) (timePartial u t x) t :=
  (h.differentiable_t t ht.le x).hasDerivWithinAt.hasDerivAt (Ici_mem_nhds ht)

theorem continuousOn_euclidDot {A : Type*} [TopologicalSpace A] {s : Set A}
    {a b : A → Space} (ha : ContinuousOn a s) (hb : ContinuousOn b s) :
    ContinuousOn (fun x => euclidDot (a x) (b x)) s := by
  unfold euclidDot
  exact continuousOn_finsetSum _ (fun i _ =>
    ((continuous_apply i).comp_continuousOn ha).fun_mul ((continuous_apply i).comp_continuousOn hb))

theorem ClassicalSolution.relativeEnergy_hasDerivAt {ν : ℝ} {f u v : Field} {p r : Pressure}
    (hu : ClassicalSolution ν f u r) (hv : ClassicalSolution ν f v p) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (relativeEnergy u v)
      (∫ x in fundamentalCell, euclidDot (v t x-u t x) (timePartial v t x-timePartial u t x)) t := by
  apply cylinder_integral_hasDerivAt
    (g := fun t x => kineticDensity (v t x-u t x))
    (g' := fun t x => euclidDot (v t x-u t x) (timePartial v t x-timePartial u t x))
  · intro T hT
    exact kineticDensity_continuous.comp_continuousOn
      ((hv.continuous_u T hT).sub (hu.continuous_u T hT))
  · intro T hT
    exact continuousOn_euclidDot ((hv.continuous_u T hT).sub (hu.continuous_u T hT))
      ((hv.continuous_t T hT).sub (hu.continuous_t T hT))
  · intro s hs x
    exact hasDerivAt_kineticDensity ((hv.hasDerivAt hs x).fun_sub (hu.hasDerivAt hs x))
  · exact ht

end Solenoidal
end

end OAI

-- ---- platform node ----
open OAI OAI.Solenoidal
open Set MeasureTheory
open scoped BigOperators
open Set MeasureTheory Filter
open scoped BigOperators Topology


theorem solution : type_of% @_root_.OAI.Solenoidal.ClassicalSolution.relativeEnergy_hasDerivAt := @_root_.OAI.Solenoidal.ClassicalSolution.relativeEnergy_hasDerivAt
