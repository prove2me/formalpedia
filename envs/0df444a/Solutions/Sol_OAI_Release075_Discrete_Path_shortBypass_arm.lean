-- Prove2me | solution 1 for OAI.Release075.Discrete.Path.shortBypass_arm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:06:05.03264+00:00
-- url     : https://prove2.me/submissions/b275f1de-e6bb-4c2c-8c65-10819bf0dab5

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/ThinTriangles.lean:L71-L128
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.Discrete.Path.shortBypass_arm. The node keeps its source
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
import Definitions.Def_OAI_GroupTheory_Hyperbolic_ThinTriangles
import Theorems.Thm_OAI_Release075_Discrete_Path_mem_append_iff
import Theorems.Thm_OAI_Release075_Discrete_Path_synchronous

-- ---- from OAI.GroupTheory.Hyperbolic.DiscreteMetric ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075.Discrete

variable {V : Type} (M : Metric V)

namespace Path
variable {M} {a b c : V}

theorem mem_reverse_iff (p : Path M a b) (x : V) : p.reverse.Mem x ↔ p.Mem x := by
  constructor
  · rintro ⟨i,hi,hx⟩; exact ⟨p.length-i,Nat.sub_le _ _,hx⟩
  · rintro ⟨i,hi,hx⟩
    exact ⟨p.length-i,Nat.sub_le _ _,by simpa only [reverse,Nat.sub_sub_self hi] using hx⟩

theorem mem_sub (p : Path M a b) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length)
    {x : V} (hx : (p.sub i j hij hj).Mem x) : p.Mem x := by
  obtain ⟨k,hk,hx⟩ := hx
  exact ⟨i+k,by change k ≤ j-i at hk; omega,(p.sub_at hij hj hk).symm.trans hx⟩

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

theorem geodesic_sub (p : Path M a b) (hp : p.Geodesic)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) : (p.sub i j hij hj).Geodesic :=
  (p.geodesic_dist_at hp hij hj).symm

end Path

namespace Metric
variable {M}

end Metric
end Release075.Discrete

namespace Release075.Discrete
variable {V : Type} {M : Metric V}

namespace Path
variable {a b c d e f : V}

theorem dist_start_mem (p : Path M a b) {x : V} (hx : p.Mem x) : M.dist a x ≤ p.length := by
  obtain ⟨i,hi,rfl⟩ := hx
  have h := p.dist_at_le (Nat.zero_le i) hi
  rw [p.zero,Nat.sub_zero] at h
  omega

theorem dist_end_mem (p : Path M a b) {x : V} (hx : p.Mem x) : M.dist b x ≤ p.length := by
  exact p.reverse.dist_start_mem ((p.mem_reverse_iff x).mpr hx)

end Path

end Release075.Discrete

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.ThinTriangles ----
namespace OAI

namespace Release075.Discrete
variable {V : Type} {M : Metric V}

namespace Path
variable {a b c : V}

theorem Outside.append {p : Path M a b} {q : Path M b c} {o : V} {T : ℕ}
    (hp : p.Outside o T) (hq : q.Outside o T) : (p.append q).Outside o T := by
  intro x hx
  rcases (p.mem_append_iff q x).mp hx with hx | hx
  · exact hp x hx
  · exact hq x hx

theorem Outside.reverse {p : Path M a b} {o : V} {T : ℕ}
    (hp : p.Outside o T) : p.reverse.Outside o T := by
  intro x hx
  exact hp x ((p.mem_reverse_iff x).mp hx)

theorem Outside.sub {p : Path M a b} {o : V} {T i j : ℕ}
    (hp : p.Outside o T) (hij : i ≤ j) (hj : j ≤ p.length) :
    (p.sub i j hij hj).Outside o T := by
  intro x hx
  exact hp x (p.mem_sub hij hj hx)

theorem outside_of_start (p : Path M a b) {o : V} {T : ℕ}
    (h : T+p.length ≤ M.dist o a) : p.Outside o T := by
  intro x hx
  have h₁ := p.dist_start_mem hx
  have h₂ := M.triangle o x a
  rw [M.symm x a] at h₂
  omega

theorem outside_of_end (p : Path M a b) {o : V} {T : ℕ}
    (h : T+p.length ≤ M.dist o b) : p.Outside o T := by
  intro x hx
  have h₁ := p.dist_end_mem hx
  have h₂ := M.triangle o x b
  rw [M.symm x b] at h₂
  omega

theorem triangle_lengths {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic) :
    p.length ≤ q.length+s.length ∧ q.length ≤ p.length+s.length ∧
      s.length ≤ p.length+q.length := by
  have h₁ := M.triangle a c b
  have h₂ := M.triangle b a c
  have h₃ := M.triangle a b c
  rw [M.symm c b] at h₁
  rw [M.symm b a] at h₂
  change p.length = M.dist a b at hp
  change q.length = M.dist b c at hq
  change s.length = M.dist a c at hs
  omega

/-- Localization in a long arm of the comparison tripod. -/
theorem shortBypass_arm (hgeo : GeodesicSpace M)
    {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic)
    {T R t : ℕ} (hR : 4*T+2 ≤ R) (ht : t ≤ p.length)
    (hthin : SideNear T p q s)
    (hfar : ∀ x, q.Mem x ∨ s.Mem x → T ≤ M.dist (p.point t) x)
    (harm : t+4*R < (p.length+s.length-q.length)/2) :
    ShortBypass M T (p.point t) (10*R) := by
  obtain ⟨hA,hB,hC⟩ := triangle_lengths hp hq hs
  let l := t-2*R
  let u := t+2*R
  have hlu : l ≤ u := by dsimp [l,u]; omega
  have huα : u ≤ (p.length+s.length-q.length)/2 := by dsimp [u]; omega
  have hlα : l ≤ (p.length+s.length-q.length)/2 := hlu.trans huα
  have huA : u ≤ p.length := by omega
  have huC : u ≤ s.length := by omega
  have hlt : l ≤ t := Nat.sub_le _ _
  have htu : t ≤ u := by dsimp [u]; omega
  let A := p.sub l u hlu huA
  let S := s.sub l u hlu huC
  let U := shortPath hgeo (p.point u) (s.point u)
  let L := shortPath hgeo (s.point l) (p.point l)
  have hU : U.length ≤ R := by
    rw [show U.length = M.dist (p.point u) (s.point u) from shortPath_length hgeo _ _]
    exact (synchronous hp hq hs hthin huα).trans hR
  have hL : L.length ≤ R := by
    rw [show L.length = M.dist (s.point l) (p.point l) from shortPath_length hgeo _ _,M.symm]
    exact (synchronous hp hq hs hthin hlα).trans hR
  have outU : U.Outside (p.point t) T := by
    apply U.outside_of_start
    rw [p.geodesic_dist_at hp htu huA]
    dsimp [u]
    omega
  have outL : L.Outside (p.point t) T := by
    apply L.outside_of_end
    by_cases hl : l = 0
    · have hL0 : L.length = 0 := by
        change (shortPath hgeo (s.point l) (p.point l)).length = 0
        rw [shortPath_length,hl,p.zero,s.zero,M.self]
      have h := hfar a (Or.inr s.start_mem)
      simpa only [hL0,Nat.add_zero,hl,p.zero] using h
    · rw [M.symm (p.point t) (p.point l),p.geodesic_dist_at hp hlt ht]
      dsimp [l] at *
      omega
  have outS : S.reverse.Outside (p.point t) T := by
    apply Outside.reverse
    exact (show s.Outside (p.point t) T from fun x hx => hfar x (Or.inr hx)).sub hlu huC
  refine ⟨p.point l,p.point u,A,(U.append S.reverse).append L,
    p.geodesic_sub hp hlu huA,?_,(outU.append outS).append outL,?_⟩
  · refine ⟨t-l,?_,?_⟩
    · change t-l ≤ u-l
      omega
    · rw [show A.point (t-l) = p.point (l+(t-l)) from p.sub_at hlu huA (by omega)]
      rw [Nat.add_sub_of_le hlt]
  · change (u-l)+(U.length+(u-l)+L.length) ≤ 10*R
    dsimp [u,l]
    omega

end Path

namespace Path
variable {a b c : V}

end Path
end Release075.Discrete

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.Discrete OAI.Release075.Discrete.Path


theorem solution : type_of% @_root_.OAI.Release075.Discrete.Path.shortBypass_arm := @_root_.OAI.Release075.Discrete.Path.shortBypass_arm
