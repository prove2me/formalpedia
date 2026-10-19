-- Prove2me | solution 1 for OAI.Release075.Discrete.Path.integral_form_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:02:47.986879+00:00
-- url     : https://prove2.me/submissions/b557d963-bf08-4b52-a46f-a731ed90e0e4

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/DiscreteMetric.lean:L398-L441
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.Discrete.Path.integral_form_quadratic. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Spheres
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullGluing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Chains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_CyclicAction
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullChains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_BasedWords
import Definitions.Def_OAI_GroupTheory_Hyperbolic_DiscreteMetric

-- ---- from OAI.GroupTheory.Hyperbolic.DiscreteMetric ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075.Discrete

variable {V : Type} (M : Metric V)

namespace Path
variable {M} {a b c : V}

theorem dist_at_le (p : Path M a b) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) :
    M.dist (p.point i) (p.point j) ≤ j-i := by
  induction j, hij using Nat.le_induction with
  | base => simp only [M.self,Nat.sub_self,le_refl]
  | succ j hij ih =>
    have h := M.triangle (p.point i) (p.point j) (p.point (j+1))
    have h' := p.step j (by omega)
    have hh := ih (by omega)
    omega

theorem geodesic_dist_at (p : Path M a b) (hp : p.Geodesic)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) :
    M.dist (p.point i) (p.point j) = j-i := by
  have h₁ := p.dist_at_le (i:=0) (j:=i) (Nat.zero_le _) (hij.trans hj)
  have h₂ := p.dist_at_le (i:=j) (j:=p.length) hj le_rfl
  have h₃ := p.dist_at_le hij hj
  rw [p.zero,Nat.sub_zero] at h₁
  rw [p.last] at h₂
  have h₄ := M.triangle a (p.point i) b
  have h₅ := M.triangle (p.point i) (p.point j) b
  change p.length = M.dist a b at hp
  omega

theorem geodesic_start_dist (p : Path M a b) (hp : p.Geodesic) {i : ℕ} (hi : i ≤ p.length) :
    M.dist a (p.point i) = i := by
  simpa only [p.zero,Nat.sub_zero] using p.geodesic_dist_at hp (Nat.zero_le _) hi

theorem geodesic_end_dist (p : Path M a b) (hp : p.Geodesic) {i : ℕ} (hi : i ≤ p.length) :
    M.dist (p.point i) b = p.length-i := by
  simpa only [p.last] using p.geodesic_dist_at hp hi le_rfl

end Path

namespace Metric
variable {M}

theorem tent_nonneg (o : V) (R : ℕ) (x : V) : 0 ≤ M.tent o R x := le_max_left _ _

end Metric
end Release075.Discrete

namespace Release075.Discrete
variable {V : Type} {M : Metric V}

namespace Path
variable {a b c d e f : V}

theorem integral_form_quadratic (p : Path M a b) (hp : p.Geodesic) {t T : ℕ}
    (ht : t ≤ p.length) (hend : T ≤ M.dist (p.point t) b) :
    ((T/2:ℕ):ℤ)^2 ≤ p.integral (M.form (p.point t) a T) := by
  let k := T/2
  have htk : t+k ≤ p.length := by
    rw [p.geodesic_end_dist hp ht] at hend
    dsimp [k]
    omega
  have hnneg : ∀ i ∈ Finset.range p.length,
      0 ≤ M.form (p.point t) a T (p.point i) (p.point (i+1)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [Metric.form,p.geodesic_start_dist hp (by omega : i+1 ≤ p.length),
      p.geodesic_start_dist hp (by omega : i ≤ p.length)]
    have h₁ := M.tent_nonneg (p.point t) T (p.point i)
    have h₂ := M.tent_nonneg (p.point t) T (p.point (i+1))
    push_cast
    nlinarith
  have hsub : Finset.Ico t (t+k) ⊆ Finset.range p.length := by
    intro i hi
    simp only [Finset.mem_Ico,Finset.mem_range] at *
    omega
  have hlarge : ∀ i ∈ Finset.Ico t (t+k),
      (k:ℤ) ≤ M.form (p.point t) a T (p.point i) (p.point (i+1)) := by
    intro i hi
    obtain ⟨hti,hit⟩ := Finset.mem_Ico.mp hi
    have hiA : i+1 ≤ p.length := by omega
    have hdi := p.geodesic_dist_at hp hti (by omega : i ≤ p.length)
    rw [Metric.form,p.geodesic_start_dist hp hiA,
      p.geodesic_start_dist hp (by omega : i ≤ p.length)]
    have h₁ : (k:ℤ) ≤ M.tent (p.point t) T (p.point i) := by
      rw [Metric.tent,hdi]
      dsimp [k] at *
      omega
    have h₂ := M.tent_nonneg (p.point t) T (p.point (i+1))
    push_cast
    nlinarith
  calc
    ((T/2:ℕ):ℤ)^2 = ∑ _i ∈ Finset.Ico t (t+k), (k:ℤ) := by
      simp [Nat.card_Ico,k,pow_two]
    _ ≤ ∑ i ∈ Finset.Ico t (t+k), M.form (p.point t) a T (p.point i) (p.point (i+1)) :=
      Finset.sum_le_sum hlarge
    _ ≤ p.integral (M.form (p.point t) a T) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hnneg i hi)

end Path

end Release075.Discrete

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.Discrete OAI.Release075.Discrete.Path


theorem solution : type_of% @_root_.OAI.Release075.Discrete.Path.integral_form_quadratic := @_root_.OAI.Release075.Discrete.Path.integral_form_quadratic
