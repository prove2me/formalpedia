-- Prove2me | solution 1 for OAI.Release075.Discrete.Path.synchronous
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:01:09.972029+00:00
-- url     : https://prove2.me/submissions/10e23b49-12df-492f-bef2-dc2a48ec57a9

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/DiscreteMetric.lean:L323-L384
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.Discrete.Path.synchronous. The node keeps its source
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

end Metric
end Release075.Discrete

namespace Release075.Discrete
variable {V : Type} {M : Metric V}

namespace Path
variable {a b c d e f : V}

theorem synchronous_of_near {p : Path M a b} {s : Path M a c}
    (hp : p.Geodesic) (hs : s.Geodesic) {i j T : ℕ}
    (hi : i ≤ p.length) (hi' : i ≤ s.length) (hj : j ≤ s.length)
    (h : M.dist (p.point i) (s.point j) ≤ T) :
    M.dist (p.point i) (s.point i) ≤ 2*T := by
  have h₁ := M.triangle a (p.point i) (s.point j)
  have h₂ := M.triangle a (s.point j) (p.point i)
  rw [p.geodesic_start_dist hp hi,s.geodesic_start_dist hs hj] at h₁ h₂
  rw [M.symm (s.point j) (p.point i)] at h₂
  have h₃ := M.triangle (p.point i) (s.point j) (s.point i)
  by_cases hij : i ≤ j
  · rw [M.symm (s.point j) (s.point i),s.geodesic_dist_at hs hij hj] at h₃
    omega
  · rw [s.geodesic_dist_at hs (by omega : j ≤ i) hi'] at h₃
    omega

/-- The elementary tripod comparison: synchronous precentral points have width O(T). -/
theorem synchronous {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic) {T i : ℕ}
    (hthin : SideNear T p q s) (hi : i ≤ (p.length+s.length-q.length)/2) :
    M.dist (p.point i) (s.point i) ≤ 4*T+2 := by
  have hA : p.length ≤ q.length+s.length := by
    have h := M.triangle a c b
    change p.length = M.dist a b at hp
    change q.length = M.dist b c at hq
    change s.length = M.dist a c at hs
    rw [M.symm c b] at h
    omega
  have hC : s.length ≤ p.length+q.length := by
    have h := M.triangle a b c
    change p.length = M.dist a b at hp
    change q.length = M.dist b c at hq
    change s.length = M.dist a c at hs
    omega
  have hB : q.length ≤ p.length+s.length := by
    have h := M.triangle b a c
    change p.length = M.dist a b at hp
    change q.length = M.dist b c at hq
    change s.length = M.dist a c at hs
    rw [M.symm b a] at h
    omega
  let α := (p.length+s.length-q.length)/2
  have hiA : i ≤ p.length := by omega
  have hiC : i ≤ s.length := by omega
  by_cases hsmall : α ≤ T
  · have h := M.triangle (p.point i) a (s.point i)
    rw [M.symm (p.point i) a,p.geodesic_start_dist hp hiA,
      s.geodesic_start_dist hs hiC] at h
    change i ≤ α at hi
    omega
  · let k := min i (α-(T+1))
    have hki : k ≤ i := min_le_left _ _
    have hkA : k ≤ p.length := hki.trans hiA
    have hkC : k ≤ s.length := hki.trans hiC
    obtain ⟨x,hx,hd⟩ := hthin (p.point k) ⟨k,hkA,rfl⟩
    have hnq : ¬ q.Mem x := by
      rintro ⟨j,hj,rfl⟩
      have h₁ := M.triangle a (p.point k) b
      have h₂ := M.triangle (p.point k) (q.point j) b
      have h₃ := M.triangle a (p.point k) c
      have h₄ := M.triangle (p.point k) (q.point j) c
      rw [p.geodesic_start_dist hp hkA] at h₁ h₃
      rw [M.symm (q.point j) b,q.geodesic_start_dist hq hj] at h₂
      rw [q.geodesic_end_dist hq hj] at h₄
      change p.length = M.dist a b at hp
      change s.length = M.dist a c at hs
      dsimp [k,α] at *
      omega
    obtain ⟨j,hj,hjx⟩ := hx.resolve_left hnq
    rw [←hjx] at hd
    have hsync := synchronous_of_near hp hs hkA hkC hj hd
    have h₁ := M.triangle (p.point i) (p.point k) (s.point i)
    have h₂ := M.triangle (p.point k) (s.point k) (s.point i)
    rw [M.symm (p.point i) (p.point k),p.geodesic_dist_at hp hki hiA] at h₁
    rw [s.geodesic_dist_at hs hki hiC] at h₂
    change i ≤ α at hi
    dsimp [k] at *
    omega

end Path

end Release075.Discrete

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.Discrete OAI.Release075.Discrete.Path


theorem solution : type_of% @_root_.OAI.Release075.Discrete.Path.synchronous := @_root_.OAI.Release075.Discrete.Path.synchronous
