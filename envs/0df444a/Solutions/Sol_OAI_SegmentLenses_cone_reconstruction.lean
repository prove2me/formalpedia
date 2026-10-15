-- Prove2me | solution 1 for OAI.SegmentLenses.cone_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:38:24.256266+00:00
-- url     : https://prove2.me/submissions/82d1c217-bdfb-44c6-b438-4c76d7c5cc7c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/HeadTests.lean:L157-L216
-- (upload_full_project.md Phase 4): solution for node OAI.SegmentLenses.cone_reconstruction. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws
import Definitions.Def_OAI_Analysis_SegmentLenses_Pairing
import Definitions.Def_OAI_Analysis_SegmentLenses_AtomicBalls
import Definitions.Def_OAI_Analysis_SegmentLenses_LawRecovery
import Definitions.Def_OAI_Analysis_SegmentLenses_HeadTests

-- ---- from OAI.Analysis.SegmentLenses.TreeGeometry ----
namespace OAI

/-!
# Ancestry, segment splitting, and opposite crossings
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section TreeGeometry
variable {V : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [segmentSystemV : SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

theorem gates_incomparable {H : Finset V} {g g' : V}
    (hg : Gate H g) (hg' : Gate H g') (h : g ≤ g') : g = g' := by
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := segmentSystemV
  have _ := intervalSegmentsV
  by_contra hne
  exact hg.1 (hg'.2 g (lt_of_le_of_ne h hne))

namespace SegmentFamily

end SegmentFamily

end TreeGeometry

end SegmentLenses

end

end OAI

-- ---- from OAI.Analysis.SegmentLenses.FiniteLaws ----
namespace OAI

/-!
# Finite probability laws and joint square-root budgets
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem mean_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    μ.mean f ≤ μ.mean g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (μ.nonneg ω)

end FiniteLaw

end SegmentLenses

end

end OAI

-- ---- from OAI.Analysis.SegmentLenses.LawRecovery ----
namespace OAI

/-!
# Exact finite-law recovery and coefficient representations
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem norm_expect_le (μ : FiniteLaw Ω) {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (f : Ω → E) : ‖μ.expect f‖ ≤ μ.mean (fun ω => ‖f ω‖) := by
  calc
    ‖μ.expect f‖ ≤ ∑ ω, ‖μ.weight ω • f ω‖ := norm_sum_le _ _
    _ = μ.mean (fun ω => ‖f ω‖) := by
      simp only [mean, norm_smul, Real.norm_eq_abs, abs_of_nonneg (μ.nonneg _)]

end FiniteLaw

section LawRecovery
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

end LawRecovery

namespace FiniteLaw
variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

end FiniteLaw

section RepresentationGates
variable {V : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

end RepresentationGates

end SegmentLenses

end

end OAI

-- ---- from OAI.Analysis.SegmentLenses.HeadTests ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Common finite norming tests and head localization
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section HeadTests
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

end HeadTests

section NormingTest
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

end NormingTest

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem nonempty (μ : FiniteLaw Ω) : Nonempty Ω := by
  by_contra hn
  let : IsEmpty Ω := ⟨fun ω => hn ⟨ω⟩⟩
  have ht := μ.total
  simp at ht

theorem abs_mean_le (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    |μ.mean f| ≤ μ.mean (fun ω => |f ω|) := by
  simpa only [expect_scalar, Real.norm_eq_abs] using μ.norm_expect_le f

theorem mean_mul_right (μ : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.mean (fun ω => f ω * c) = μ.mean f * c := by
  simpa only [mul_comm] using μ.mean_mul c f

end FiniteLaw

section ConeReconstruction
variable {V Ω : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V] [Fintype Ω]

theorem cone_reconstruction {H : Finset V} (G : Finset V) (hG : ∀ g ∈ G, Gate H g)
    (μ : FiniteLaw Ω) (σ : Ω → ℝ) (hσ : ∀ ω, |σ ω| ≤ 1)
    (b : Ω → G → ℝ) (J : G → Ω → Finset V)
    (hJ : ∀ g ω, J g ω = ∅ ∨ SegmentSystem.isSegment (J g ω))
    (hcone : ∀ g ω v, v ∈ J g ω → g.val ≤ v) :
    ‖∑ g : G, μ.expect (fun ω => (σ ω * b ω g) • segmentFunctional (J g ω))‖ ≤
      Real.sqrt (∑ g : G, μ.mean (fun ω => |b ω g|) ^ 2) := by
  classical
  let : Nonempty Ω := μ.nonempty
  apply dual_norm_le _ (Real.sqrt_nonneg _)
  intro u
  have hmax : ∀ g : G, ∃ w : Ω, ∀ ω, |∑ v ∈ J g ω, u.coeff v| ≤
      |∑ v ∈ J g w, u.coeff v| := by
    intro g
    obtain ⟨w, hw, hm⟩ := Finset.exists_max_image Finset.univ
      (fun ω => |∑ v ∈ J g ω, u.coeff v|) Finset.univ_nonempty
    exact ⟨w, fun ω => hm ω (Finset.mem_univ _)⟩
  choose choice hc using hmax
  let M : G → ℝ := fun g => |∑ v ∈ J g (choice g), u.coeff v|
  have hd : Pairwise fun g g' : G => Disjoint (J g (choice g)) (J g' (choice g')) := by
    intro g g' hne
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    rcases TreeOrder.lower_chain (hcone g (choice g) v hv) (hcone g' (choice g') v hv') with h | h
    · exact hne (Subtype.ext (gates_incomparable (hG _ g.property) (hG _ g'.property) h))
    · exact hne (Subtype.ext (gates_incomparable (hG _ g'.property) (hG _ g.property) h).symm)
  have hsq : (∑ g : G, M g ^ 2) ≤ ‖u‖ ^ 2 := by
    change (∑ g : G, M g ^ 2) ≤ segmentSeminorm V u.coeff ^ 2
    simpa only [M, sq_abs] using indexed_test_bound u.coeff
      (fun g => J g (choice g)) (fun g => hJ g (choice g)) hd
  have hM : Real.sqrt (∑ g : G, M g ^ 2) ≤ ‖u‖ := by
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _)] at h
  have he : (∑ g : G, μ.expect (fun ω => (σ ω * b ω g) • segmentFunctional (J g ω)))
      (u : Primal V) = ∑ g : G, μ.mean (fun ω => σ ω * b ω g * ∑ v ∈ J g ω, u.coeff v) := by
    simp only [_root_.sum_apply, FiniteLaw.expect, FiniteLaw.mean, _root_.smul_apply,
      smul_eq_mul, segmentFunctional_apply, mul_assoc]
  rw [he]
  calc
    |∑ g : G, μ.mean (fun ω => σ ω * b ω g * ∑ v ∈ J g ω, u.coeff v)| ≤
        ∑ g : G, |μ.mean (fun ω => σ ω * b ω g * ∑ v ∈ J g ω, u.coeff v)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ g : G, μ.mean (fun ω => |b ω g|) * M g := by
      apply Finset.sum_le_sum
      intro g hg
      calc
        |μ.mean (fun ω => σ ω * b ω g * ∑ v ∈ J g ω, u.coeff v)| ≤
            μ.mean (fun ω => |σ ω * b ω g * ∑ v ∈ J g ω, u.coeff v|) := μ.abs_mean_le _
        _ ≤ μ.mean (fun ω => |b ω g| * M g) := by
          apply μ.mean_mono
          intro ω
          simp only [abs_mul]
          have hsb : |σ ω| * |b ω g| ≤ |b ω g| :=
            mul_le_of_le_one_left (abs_nonneg _) (hσ ω)
          exact mul_le_mul hsb (hc g ω) (abs_nonneg _) (abs_nonneg _)
        _ = μ.mean (fun ω => |b ω g|) * M g := μ.mean_mul_right _ _
    _ ≤ Real.sqrt (∑ g : G, μ.mean (fun ω => |b ω g|) ^ 2) *
        Real.sqrt (∑ g : G, M g ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ Real.sqrt (∑ g : G, μ.mean (fun ω => |b ω g|) ^ 2) * ‖u‖ :=
      mul_le_mul_of_nonneg_left hM (Real.sqrt_nonneg _)

end ConeReconstruction

end SegmentLenses

end

end OAI

-- ---- platform node ----
open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset
variable {V Ω : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V] [Fintype Ω]

theorem solution {H : Finset V} (G : Finset V) (hG : ∀ g ∈ G, Gate H g)
    (μ : FiniteLaw Ω) (σ : Ω → ℝ) (hσ : ∀ ω, |σ ω| ≤ 1)
    (b : Ω → G → ℝ) (J : G → Ω → Finset V)
    (hJ : ∀ g ω, J g ω = ∅ ∨ SegmentSystem.isSegment (J g ω))
    (hcone : ∀ g ω v, v ∈ J g ω → g.val ≤ v) :
    ‖∑ g : G, μ.expect (fun ω => (σ ω * b ω g) • segmentFunctional (J g ω))‖ ≤
      Real.sqrt (∑ g : G, μ.mean (fun ω => |b ω g|) ^ 2) := by
  first
    | exact OAI.SegmentLenses.cone_reconstruction G hG μ σ hσ b J hJ hcone
    | exact OAI.SegmentLenses.cone_reconstruction
    | (apply OAI.SegmentLenses.cone_reconstruction <;> assumption)
    | (intros; apply OAI.SegmentLenses.cone_reconstruction <;> assumption)
