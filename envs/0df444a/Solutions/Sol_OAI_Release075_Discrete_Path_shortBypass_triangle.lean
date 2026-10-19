-- Prove2me | solution 1 for OAI.Release075.Discrete.Path.shortBypass_triangle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:11:38.240636+00:00
-- url     : https://prove2.me/submissions/32d99934-ea65-4a93-8019-5433a961d251

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/ThinTriangles.lean:L243-L272
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.Discrete.Path.shortBypass_triangle. The node keeps its source
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
import Theorems.Thm_OAI_Release075_Discrete_Path_shortBypass_arm
import Theorems.Thm_OAI_Release075_Discrete_Path_shortBypass_center

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

theorem geodesic_reverse (p : Path M a b) (hp : p.Geodesic) : p.reverse.Geodesic := by
  change p.length = M.dist b a
  rw [M.symm]
  exact hp

end Path

namespace Metric
variable {M}

end Metric
end Release075.Discrete

namespace Release075.Discrete
variable {V : Type} {M : Metric V}

namespace Path
variable {a b c d e f : V}

theorem SideNear.reverse (T : ℕ) {p : Path M a b} {q : Path M c d} {s : Path M e f}
    (h : SideNear T p q s) : SideNear T p.reverse q s := by
  intro x hx
  exact h x ((p.mem_reverse_iff x).mp hx)

theorem SideNear.swap (T : ℕ) {p : Path M a b} {q : Path M c d} {s : Path M e f}
    (h : SideNear T p q s) : SideNear T p s q := by
  intro x hx
  obtain ⟨y,hy,hd⟩ := h x hx
  exact ⟨y,hy.symm,hd⟩

end Path

end Release075.Discrete

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.ThinTriangles ----
namespace OAI

namespace Release075.Discrete
variable {V : Type} {M : Metric V}

namespace Path
variable {a b c : V}

/-- A maximally fat point of a T-thin triangle has a bypass of length at most 1000(T+1). -/
theorem shortBypass_triangle (hgeo : GeodesicSpace M)
    {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic)
    {T : ℕ} (hthin : TriangleNear T p q s) {o : V} (ho : p.Mem o)
    (hfar : ∀ x, q.Mem x ∨ s.Mem x → T ≤ M.dist o x) :
    ShortBypass M T o (1000*(T+1)) := by
  obtain ⟨t,ht,rfl⟩ := ho
  let R := 4*T+4
  have hR : 4*T+2 ≤ R := by dsimp [R]; omega
  have enlarge {K : ℕ} (hK : K ≤ 1000*(T+1))
      (h : ShortBypass M T (p.point t) K) : ShortBypass M T (p.point t) (1000*(T+1)) := by
    obtain ⟨a,b,A,Q,hA,ho,hfar,hlen⟩ := h
    exact ⟨a,b,A,Q,hA,ho,hfar,hlen.trans hK⟩
  by_cases hleft : t+4*R < (p.length+s.length-q.length)/2
  · apply enlarge (K:=10*R) (by dsimp [R]; omega)
    exact shortBypass_arm hgeo hp hq hs hR ht hthin.1 hfar hleft
  by_cases hright : p.length-t+4*R < (p.length+q.length-s.length)/2
  · have hn : SideNear T p.reverse s q := (hthin.1.reverse T).swap T
    have hr := shortBypass_arm hgeo (p.geodesic_reverse hp) hs hq hR
      (t:=p.length-t) (Nat.sub_le _ _) hn
      (fun x hx => by
        change T ≤ M.dist (p.point (p.length-(p.length-t))) x
        rw [Nat.sub_sub_self ht]
        exact hfar x hx.symm) hright
    change ShortBypass M T (p.point (p.length-(p.length-t))) (10*R) at hr
    rw [Nat.sub_sub_self ht] at hr
    exact enlarge (by dsimp [R]; omega) hr
  · apply enlarge (K:=60*R) (by dsimp [R]; omega)
    exact shortBypass_center hgeo hp hq hs hR ht hthin hfar (by omega) (by omega)

end Path

namespace Path
variable {a b c : V}

end Path
end Release075.Discrete

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.Discrete OAI.Release075.Discrete.Path


theorem solution : type_of% @_root_.OAI.Release075.Discrete.Path.shortBypass_triangle := @_root_.OAI.Release075.Discrete.Path.shortBypass_triangle
