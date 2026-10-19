-- Prove2me | solution 1 for OAI.Release075.Discrete.Path.shortBypass_center
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:09:25.000984+00:00
-- url     : https://prove2.me/submissions/0467a4b9-da63-47aa-b028-5ab08d649bad

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/ThinTriangles.lean:L130-L241
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.Discrete.Path.shortBypass_center. The node keeps its source
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

theorem geodesic_start_dist (p : Path M a b) (hp : p.Geodesic) {i : ℕ} (hi : i ≤ p.length) :
    M.dist a (p.point i) = i := by
  simpa only [p.zero,Nat.sub_zero] using p.geodesic_dist_at hp (Nat.zero_le _) hi

theorem geodesic_end_dist (p : Path M a b) (hp : p.Geodesic) {i : ℕ} (hi : i ≤ p.length) :
    M.dist (p.point i) b = p.length-i := by
  simpa only [p.last] using p.geodesic_dist_at hp hi le_rfl

theorem geodesic_reverse (p : Path M a b) (hp : p.Geodesic) : p.reverse.Geodesic := by
  change p.length = M.dist b a
  rw [M.symm]
  exact hp

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

theorem SideNear.reverse (T : ℕ) {p : Path M a b} {q : Path M c d} {s : Path M e f}
    (h : SideNear T p q s) : SideNear T p.reverse q s := by
  intro x hx
  exact h x ((p.mem_reverse_iff x).mp hx)

theorem SideNear.swap (T : ℕ) {p : Path M a b} {q : Path M c d} {s : Path M e f}
    (h : SideNear T p q s) : SideNear T p s q := by
  intro x hx
  obtain ⟨y,hy,hd⟩ := h x hx
  exact ⟨y,hy.symm,hd⟩

theorem SideNear.reverse_left (T : ℕ) {p : Path M a b} {q : Path M c d} {s : Path M e f}
    (h : SideNear T p q s) : SideNear T p q.reverse s := by
  intro x hx
  obtain ⟨y,hy,hd⟩ := h x hx
  exact ⟨y,hy.imp ((q.mem_reverse_iff y).mpr) id,hd⟩

theorem SideNear.reverse_right (T : ℕ) {p : Path M a b} {q : Path M c d} {s : Path M e f}
    (h : SideNear T p q s) : SideNear T p q s.reverse := by
  exact ((h.swap T).reverse_left T).swap T

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

/-- Localization near the three-pronged center of the comparison tripod. -/
theorem shortBypass_center (hgeo : GeodesicSpace M)
    {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic)
    {T R t : ℕ} (hR : 4*T+2 ≤ R) (ht : t ≤ p.length)
    (hthin : TriangleNear T p q s)
    (hfar : ∀ x, q.Mem x ∨ s.Mem x → T ≤ M.dist (p.point t) x)
    (hcenter₁ : (p.length+s.length-q.length)/2 ≤ t+4*R)
    (hcenter₂ : (p.length+q.length-s.length)/2 ≤ p.length-t+4*R) :
    ShortBypass M T (p.point t) (60*R) := by
  obtain ⟨hA,hB,hC⟩ := triangle_lengths hp hq hs
  let α := (p.length+s.length-q.length)/2
  let β := (p.length+q.length-s.length)/2
  let γ := (q.length+s.length-p.length)/2
  have hcoords : α+β ≤ p.length ∧ p.length ≤ α+β+1 ∧
      β+γ ≤ q.length ∧ q.length ≤ β+γ+1 ∧
      α+γ ≤ s.length ∧ s.length ≤ α+γ+1 := by
    dsimp [α,β,γ]
    omega
  change α ≤ t+4*R at hcenter₁
  change β ≤ p.length-t+4*R at hcenter₂
  let x := α-8*R
  let y := β-8*R
  let z := γ-8*R
  have hxα : x ≤ α := Nat.sub_le _ _
  have hyβ : y ≤ β := Nat.sub_le _ _
  have hzγ : z ≤ γ := Nat.sub_le _ _
  have hxt : x ≤ t := by dsimp [x]; omega
  have hty : t ≤ p.length-y := by dsimp [y]; omega
  have hxp : x ≤ p.length-y := hxt.trans hty
  have hyp : p.length-y ≤ p.length := Nat.sub_le _ _
  have hyq : y ≤ q.length-z := by omega
  have hzq : q.length-z ≤ q.length := Nat.sub_le _ _
  have hxs : x ≤ s.length-z := by omega
  have hzs : s.length-z ≤ s.length := Nat.sub_le _ _
  let P := p.sub x (p.length-y) hxp hyp
  let Q := q.sub y (q.length-z) hyq hzq
  let S := s.sub x (s.length-z) hxs hzs
  let X := shortPath hgeo (s.point x) (p.point x)
  let Y := shortPath hgeo (p.point (p.length-y)) (q.point y)
  let Z := shortPath hgeo (q.point (q.length-z)) (s.point (s.length-z))
  have hX : X.length ≤ R := by
    rw [show X.length = M.dist (s.point x) (p.point x) from shortPath_length hgeo _ _,M.symm]
    exact (synchronous hp hq hs hthin.1 hxα).trans hR
  have hY : Y.length ≤ R := by
    have hn : SideNear T p.reverse s q := (hthin.1.reverse T).swap T
    have hd := synchronous (p.geodesic_reverse hp) hs hq hn hyβ
    change M.dist (p.point (p.length-y)) (q.point y) ≤ 4*T+2 at hd
    rw [show Y.length = M.dist (p.point (p.length-y)) (q.point y) from shortPath_length hgeo _ _]
    exact hd.trans hR
  have hZ : Z.length ≤ R := by
    have hn : SideNear T q.reverse p.reverse s.reverse :=
      (((hthin.2.1.swap T).reverse_left T).reverse_right T).reverse T
    have hd := synchronous (q.geodesic_reverse hq) (p.geodesic_reverse hp)
      (s.geodesic_reverse hs) hn hzγ
    change M.dist (q.point (q.length-z)) (s.point (s.length-z)) ≤ 4*T+2 at hd
    rw [show Z.length = M.dist (q.point (q.length-z)) (s.point (s.length-z))
      from shortPath_length hgeo _ _]
    exact hd.trans hR
  have outX : X.Outside (p.point t) T := by
    apply X.outside_of_end
    by_cases hx : x = 0
    · have hl : X.length = 0 := by
        change (shortPath hgeo (s.point x) (p.point x)).length = 0
        rw [shortPath_length,hx,p.zero,s.zero,M.self]
      have hf := hfar a (Or.inr s.start_mem)
      simpa only [hl,Nat.add_zero,hx,p.zero] using hf
    · rw [M.symm (p.point t) (p.point x),p.geodesic_dist_at hp hxt ht]
      dsimp [x] at *
      omega
  have outY : Y.Outside (p.point t) T := by
    apply Y.outside_of_start
    by_cases hy : y = 0
    · have hl : Y.length = 0 := by
        change (shortPath hgeo (p.point (p.length-y)) (q.point y)).length = 0
        rw [shortPath_length,hy,Nat.sub_zero,p.last,q.zero,M.self]
      have hf := hfar b (Or.inl q.start_mem)
      simpa only [hl,Nat.add_zero,hy,Nat.sub_zero,p.last] using hf
    · rw [p.geodesic_dist_at hp hty hyp]
      dsimp [y] at *
      omega
  have outZ : Z.Outside (p.point t) T := by
    apply Z.outside_of_start
    by_cases hz : z = 0
    · have hl : Z.length = 0 := by
        change (shortPath hgeo (q.point (q.length-z)) (s.point (s.length-z))).length = 0
        simp only [shortPath_length,hz,Nat.sub_zero,q.last,s.last,M.self]
      have hf := hfar c (Or.inl q.end_mem)
      simpa only [hl,Nat.add_zero,hz,Nat.sub_zero,q.last] using hf
    · have ha := M.triangle a (p.point t) c
      rw [p.geodesic_start_dist hp ht] at ha
      have hc := M.triangle (p.point t) (q.point (q.length-z)) c
      rw [q.geodesic_end_dist hq hzq] at hc
      have hzz : z ≤ q.length := by omega
      rw [Nat.sub_sub_self hzz] at hc
      change s.length = M.dist a c at hs
      dsimp [z] at *
      omega
  have outQ : Q.Outside (p.point t) T :=
    (show q.Outside (p.point t) T from fun v hv => hfar v (Or.inl hv)).sub hyq hzq
  have outS : S.reverse.Outside (p.point t) T :=
    ((show s.Outside (p.point t) T from fun v hv => hfar v (Or.inr hv)).sub hxs hzs).reverse
  refine ⟨p.point x,p.point (p.length-y),P,(((Y.append Q).append Z).append S.reverse).append X,
    p.geodesic_sub hp hxp hyp,?_,(((outY.append outQ).append outZ).append outS).append outX,?_⟩
  · refine ⟨t-x,?_,?_⟩
    · change t-x ≤ p.length-y-x
      omega
    · rw [show P.point (t-x) = p.point (x+(t-x)) from p.sub_at hxp hyp (by omega)]
      rw [Nat.add_sub_of_le hxt]
  · change (p.length-y-x)+(Y.length+(q.length-z-y)+Z.length+(s.length-z-x)+X.length) ≤ 60*R
    dsimp [x,y,z] at *
    omega

end Path

namespace Path
variable {a b c : V}

end Path
end Release075.Discrete

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.Discrete OAI.Release075.Discrete.Path


theorem solution : type_of% @_root_.OAI.Release075.Discrete.Path.shortBypass_center := @_root_.OAI.Release075.Discrete.Path.shortBypass_center
