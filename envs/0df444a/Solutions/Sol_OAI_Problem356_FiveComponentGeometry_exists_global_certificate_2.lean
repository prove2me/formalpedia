-- Prove2me | solution 2 for OAI.Problem356.FiveComponentGeometry.exists_global_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:08:26.708864+00:00
-- url     : https://prove2.me/submissions/9383f03f-c673-4d63-8579-1e477cc21088

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/FiveComponentGlobal.lean:L103-L128
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.FiveComponentGeometry.exists_global_certificate. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryMap
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalBranchMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothPushforward
import Definitions.Def_OAI_Analysis_CoulombTransport_GluedCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_GoodTypePermutation
import Definitions.Def_OAI_Analysis_CoulombTransport_IsometryTransport
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothBranchMarginal
import Definitions.Def_OAI_Analysis_CoulombTransport_StateDual
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombSupportExistence
import Definitions.Def_OAI_Analysis_CoulombTransport_FiveComponentGeometry
import Theorems.Thm_OAI_Problem356_FiveComponentGeometry_exists_canonical_neighborhoods
import Theorems.Thm_OAI_Problem356_FiveComponentGeometry_strict_center_gap
import Theorems.Thm_OAI_Problem356_GoodTypePermutation_certificate_of_good
import Theorems.Thm_OAI_Problem356_exists_glued_component_certificate_forward

-- ---- from OAI.Analysis.CoulombTransport.CenterCertificate ----
namespace OAI

noncomputable section
open scoped ENNReal

namespace Problem356.CenterCertificate

theorem point_injective : Function.Injective point := by
  intro i j h
  have h0 := congrArg (fun x : E3 => x 0) h
  have h1 := congrArg (fun x : E3 => x 1) h
  clear h
  fin_cases i <;> fin_cases j
  all_goals norm_num [point] at h0
  all_goals norm_num [point] at h1
  all_goals rfl

end Problem356.CenterCertificate

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.GoodTypePermutation ----
namespace OAI

noncomputable section
open scoped ENNReal

namespace Problem356.GoodTypePermutation

variable {U : Fin 5 → Set E3} {v : Fin 5 → E3 → ℝ}
  {Contact : Triple → Prop}

/-- Neighborhood form directly usable by a finite component gluing argument. -/
theorem eventually_certificate_of_good
    (p : Fin 5 → E3) (hU : ∀ i, U i ∈ nhds (p i))
    (hperm : ∀ {x y z a b c : E3}, List.Perm [x, y, z] [a, b, c] →
      Contact (x, (y, z)) → Contact (a, (b, c)))
    (h012 : LocalTypeCertificate U v Contact 0 1 2)
    (h034 : LocalTypeCertificate U v Contact 0 3 4)
    (i j k : Fin 5) (hgood : CenterCertificate.Good i j k) :
    ∀ᶠ t : Triple in nhds (p i, (p j, p k)),
      ENNReal.ofReal (v i t.1 + v j t.2.1 + v k t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v i t.1 + v j t.2.1 + v k t.2.2) = coulombCost t →
        Contact t) := by
  have h1 : ∀ᶠ t : Triple in nhds (p i, (p j, p k)), t.1 ∈ U i :=
    (continuous_fst.tendsto _).eventually (hU i)
  have h2 : ∀ᶠ t : Triple in nhds (p i, (p j, p k)), t.2.1 ∈ U j :=
    ((continuous_fst.comp continuous_snd).tendsto _).eventually (hU j)
  have h3 : ∀ᶠ t : Triple in nhds (p i, (p j, p k)), t.2.2 ∈ U k :=
    ((continuous_snd.comp continuous_snd).tendsto _).eventually (hU k)
  filter_upwards [h1, h2, h3] with t ht1 ht2 ht3
  exact certificate_of_good hperm h012 h034 i j k hgood
    t.1 ht1 t.2.1 ht2 t.2.2 ht3

end Problem356.GoodTypePermutation

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.FiveComponentGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open Set Filter Metric
open scoped ENNReal InnerProductSpace

namespace Problem356.FiveComponentGeometry

open LocalGeometry StationaryMap CenterCertificate

lemma domains_open (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    ∀ i, IsOpen (domains C₁ C₂ i) := by
  intro i
  fin_cases i
  · exact isOpen_univ
  · exact C₁.charts.central.open_source
  · exact isOpen_univ
  · exact C₂.charts.central.open_source
  · exact isOpen_univ

lemma point_mem_domains (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    ∀ i, point i ∈ domains C₁ C₂ i := by
  intro i
  fin_cases i
  · exact mem_univ _
  · exact C₁.charts.point_mem
  · exact mem_univ _
  · exact C₂.charts.point_mem
  · exact mem_univ _

lemma continuousOn_potentials (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    ∀ i, ContinuousOn (potentials C₁ C₂ i) (domains C₁ C₂ i) := by
  intro i
  fin_cases i
  · exact (by fun_prop : Continuous (fun x : E3 => (5 : ℝ) / 2 - 10 * ‖x‖ ^ 2)).continuousOn
  · exact C₁.value_analytic.continuousOn
  · exact (by fun_prop : Continuous (fun z : E3 =>
      (5 : ℝ) / 4 * ⟪point 1, z + point 1⟫_ℝ - 10 * ‖z + point 1‖ ^ 2)).continuousOn
  · exact C₂.value_analytic.continuousOn
  · exact (by fun_prop : Continuous (fun z : E3 =>
      (5 : ℝ) / 4 * ⟪point 3, z + point 3⟫_ℝ - 10 * ‖z + point 3‖ ^ 2)).continuousOn

lemma branchContact_perm (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3))
    {x y z x' y' z' : E3} (hp : List.Perm [x, y, z] [x', y', z']) :
    branchContact C₁ C₂ (x, (y, z)) ↔ branchContact C₁ C₂ (x', (y', z')) := by
  constructor
  · intro h
    rcases h with ⟨w, hw, hperm⟩ | ⟨w, hw, hperm⟩
    · exact Or.inl ⟨w, hw, hp.symm.trans hperm⟩
    · exact Or.inr ⟨w, hw, hp.symm.trans hperm⟩
  · intro h
    rcases h with ⟨w, hw, hperm⟩ | ⟨w, hw, hperm⟩
    · exact Or.inl ⟨w, hw, hp.trans hperm⟩
    · exact Or.inr ⟨w, hw, hp.trans hperm⟩

end Problem356.FiveComponentGeometry

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.FiveComponentGlobal ----
namespace OAI

noncomputable section
open Set Filter Metric
open scoped ENNReal InnerProductSpace

namespace Problem356.FiveComponentGeometry
open CenterCertificate GoodTypePermutation

/-- The concrete two Coulomb charts admit a globally bounded measurable
certificate on five disjoint component balls, with contact only on their
actual symmetric graph union. -/
theorem exists_global_certificate
    (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧
      let U := fun i => ball (point i) r
      let u := ComponentPotential.glue U (potentials C₁ C₂)
      (∀ i, U i ⊆ domains C₁ C₂ i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      Measurable u ∧ ContinuousOn u (⋃ i, U i) ∧ (∀ x, |u x| ≤ M) ∧
      (∀ x ∈ ⋃ i, U i, ∀ y ∈ ⋃ i, U i, ∀ z ∈ ⋃ i, U i,
        ENNReal.ofReal (u x + u y + u z) ≤ coulombCost (x, (y, z)) ∧
        (ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) →
          branchContact C₁ C₂ (x, (y, z)))) := by
  obtain ⟨W, hW, h012, h034⟩ := exists_canonical_neighborhoods C₁ C₂
  apply exists_glued_component_certificate_forward point point_injective
    (domains C₁ C₂) (domains_open C₁ C₂) (point_mem_domains C₁ C₂)
    (potentials C₁ C₂) (continuousOn_potentials C₁ C₂)
    (fun a => Good a.1 a.2.1 a.2.2) (branchContact C₁ C₂)
  · intro a ha
    exact eventually_certificate_of_good point hW
      (fun hp hc => (branchContact_perm C₁ C₂ hp).mp hc)
      h012 h034 a.1 a.2.1 a.2.2 ha
  · intro a ha
    exact strict_center_gap C₁ C₂ a.1 a.2.1 a.2.2 ha

end Problem356.FiveComponentGeometry

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.FiveComponentGeometry
open Set Filter Metric
open scoped ENNReal InnerProductSpace
open CenterCertificate GoodTypePermutation


theorem solution : type_of% @_root_.OAI.Problem356.FiveComponentGeometry.exists_global_certificate := @_root_.OAI.Problem356.FiveComponentGeometry.exists_global_certificate
