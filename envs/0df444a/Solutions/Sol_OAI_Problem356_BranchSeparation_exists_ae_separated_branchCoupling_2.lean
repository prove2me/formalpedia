-- Prove2me | solution 2 for OAI.Problem356.BranchSeparation.exists_ae_separated_branchCoupling
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:14:35.57096+00:00
-- url     : https://prove2.me/submissions/31748423-a008-4644-84ed-793a9ccd65ea

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/BranchSeparation.lean:L35-L61
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.BranchSeparation.exists_ae_separated_branchCoupling. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Theorems.Thm_OAI_Problem356_ae_branchCoupling
import Theorems.Thm_OAI_Problem356_exists_uniform_compact_separation

-- ---- from OAI.Analysis.CoulombTransport.BranchSeparation ----
namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.BranchSeparation

lemma compact_components {K : Set E3} (hK : IsCompact K)
    {H : Fin 4 → E3 → E3} (hH : ∀ i, ContinuousOn (H i) K) :
    ∀ i, IsCompact (components K H i) := by
  intro i
  exact Fin.cases hK (fun j => hK.image_of_continuousOn (hH j)) i

lemma measurableSet_separated (eta : ℝ) :
    MeasurableSet {t : Triple | CoulombEstimates.Separated eta t} := by
  have h12 : Measurable (fun t : Triple => dist t.1 t.2.1) :=
    measurable_fst.dist (measurable_fst.comp measurable_snd)
  have h13 : Measurable (fun t : Triple => dist t.1 t.2.2) :=
    measurable_fst.dist (measurable_snd.comp measurable_snd)
  have h23 : Measurable (fun t : Triple => dist t.2.1 t.2.2) :=
    (measurable_fst.comp measurable_snd).dist (measurable_snd.comp measurable_snd)
  exact (measurableSet_le measurable_const h12).inter
    ((measurableSet_le measurable_const h13).inter (measurableSet_le measurable_const h23))

/-- Uniform separation for the actual cyclic two-branch coupling follows from
compactness and disjointness of its five component sets. -/
theorem exists_ae_separated_branchCoupling
    {nu : Measure E3} {K : Set E3} (hK : IsCompact K)
    (hnu : ∀ᵐ x ∂nu, x ∈ K) {H : Fin 4 → E3 → E3}
    (hH : ∀ i, Measurable (H i)) (hcont : ∀ i, ContinuousOn (H i) K)
    (hdisjoint : Pairwise (fun i j => Disjoint (components K H i) (components K H j))) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ᵐ t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3),
        CoulombEstimates.Separated eta t := by
  obtain ⟨eta, heta, hsep⟩ := exists_uniform_compact_separation
    (components K H) (compact_components hK hcont) hdisjoint
  have hcentral (i : Fin 4) {x : E3} (hx : x ∈ K) : eta ≤ dist x (H i x) := by
    exact hsep 0 i.succ (Fin.succ_ne_zero i).symm x hx (H i x) (mem_image_of_mem _ hx)
  have houter (i j : Fin 4) (hij : i ≠ j) {x : E3} (hx : x ∈ K) :
      eta ≤ dist (H i x) (H j x) := by
    exact hsep i.succ j.succ (by simpa using hij) (H i x) (mem_image_of_mem _ hx)
      (H j x) (mem_image_of_mem _ hx)
  refine ⟨eta, heta, ae_branchCoupling nu (hH 0) (hH 1) (hH 2) (hH 3)
    (measurableSet_separated eta) ?_ ?_ ?_⟩
  · intro x y z h
    exact ⟨h.2.2, by simpa only [dist_comm] using h.1,
      by simpa only [dist_comm] using h.2.1⟩
  · filter_upwards [hnu] with x hx
    exact ⟨hcentral 0 hx, hcentral 1 hx, houter 0 1 (by decide) hx⟩
  · filter_upwards [hnu] with x hx
    exact ⟨hcentral 2 hx, hcentral 3 hx, houter 2 3 (by decide) hx⟩

end Problem356.BranchSeparation

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.BranchSeparation
open MeasureTheory Set
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.Problem356.BranchSeparation.exists_ae_separated_branchCoupling := @_root_.OAI.Problem356.BranchSeparation.exists_ae_separated_branchCoupling
