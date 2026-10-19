-- Prove2me | solution 1 for OAI.Release075.Discrete.Path.triangleNear_of_cochainBound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:13:23.312086+00:00
-- url     : https://prove2.me/submissions/6fa50460-a60c-4032-b170-632253d255d9

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/ThinTriangles.lean:L340-L374
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.Discrete.Path.triangleNear_of_cochainBound. The node keeps its source
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
import Theorems.Thm_OAI_Release075_Discrete_Path_integral_form_quadratic
import Theorems.Thm_OAI_Release075_Discrete_Path_shortBypass_triangle

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

theorem dist_at_le (p : Path M a b) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) :
    M.dist (p.point i) (p.point j) ≤ j-i := by
  induction j, hij using Nat.le_induction with
  | base => simp only [M.self,Nat.sub_self,le_refl]
  | succ j hij ih =>
    have h := M.triangle (p.point i) (p.point j) (p.point (j+1))
    have h' := p.step j (by omega)
    have hh := ih (by omega)
    omega

theorem geodesic_reverse (p : Path M a b) (hp : p.Geodesic) : p.reverse.Geodesic := by
  change p.length = M.dist b a
  rw [M.symm]
  exact hp

theorem integral_append (p : Path M a b) (q : Path M b c) (F : V → V → ℤ) :
    (p.append q).integral F = p.integral F+q.integral F := by
  unfold integral
  rw [length_append,Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [p.append_at_left q (by have := Finset.mem_range.mp hi; omega),
      p.append_at_left q (by have := Finset.mem_range.mp hi; omega)]
  · apply Finset.sum_congr rfl
    intro i _
    rw [p.append_at_right q i,show p.length+i+1 = p.length+(i+1) by omega,p.append_at_right]

end Path

namespace Metric
variable {M}

theorem tent_zero {o x : V} {R : ℕ} (h : R ≤ M.dist o x) : M.tent o R x = 0 := by
  unfold tent
  omega

theorem form_zero {o a x y : V} {R : ℕ} (hx : R ≤ M.dist o x) (hy : R ≤ M.dist o y) :
    M.form o a R x y = 0 := by rw [form,M.tent_zero hx,M.tent_zero hy,zero_add,zero_mul]

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

theorem integral_form_zero (p : Path M a b) {o z : V} {T : ℕ}
    (hfar : ∀ x, p.Mem x → T ≤ M.dist o x) : p.integral (M.form o z T) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hi' := Finset.mem_range.mp hi
  exact M.form_zero (hfar _ ⟨i,by omega,rfl⟩) (hfar _ ⟨i+1,by omega,rfl⟩)

end Path

theorem shortBypass_quadratic {B T K : ℕ} {o : V}
    (hB : CochainBound M B) (h : ShortBypass M T o K) :
    ((T/2:ℕ):ℤ)^2 ≤ (B:ℤ)*K := by
  obtain ⟨a,b,p,q,hp,⟨t,ht,rfl⟩,hfar,hK⟩ := h
  have h₁ := p.integral_form_quadratic hp ht (hfar b q.start_mem)
  have h₂ := hB (p.point t) a a T (p.append q)
  rw [p.integral_append,q.integral_form_zero hfar,add_zero] at h₂
  have h₃ := le_abs_self (p.integral (M.form (p.point t) a T))
  have hlen : ((p.append q).length:ℤ) ≤ K := by exact_mod_cast hK
  have hmul := mul_le_mul_of_nonneg_left hlen (Nat.cast_nonneg B : (0:ℤ) ≤ B)
  omega

end Release075.Discrete

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.ThinTriangles ----
namespace OAI

namespace Release075.Discrete
variable {V : Type} {M : Metric V}

namespace Path
variable {a b c : V}

end Path

theorem quadratic_bound {B T : ℕ}
    (h : ((T/2:ℕ):ℤ)^2 ≤ (B:ℤ)*(1000*(T+1))) : T ≤ 10000*(B+1) := by
  by_contra hn
  let k := T/2
  have hk : T ≤ 2*k+1 := by dsimp [k]; omega
  have hkT : k ≤ T := Nat.div_le_self _ _
  have hT : (8000:ℤ)*B+10000 ≤ T := by omega
  have hm := mul_nonneg (sub_nonneg.mpr hT) (show (0:ℤ) ≤ (T:ℤ)+1 by omega)
  have hs : (T:ℤ)^2 ≤ (2*(k:ℤ)+1)^2 := by
    apply sq_le_sq₀ (by positivity) (by positivity) |>.mpr
    exact_mod_cast hk
  change (k:ℤ)^2 ≤ (B:ℤ)*(1000*(T+1)) at h
  have hkt : (k:ℤ) ≤ T := by exact_mod_cast hkT
  nlinarith

namespace Path
variable {a b c : V}

theorem SideNear.mono {T U : ℕ} {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (h : SideNear T p q s) (hTU : T ≤ U) : SideNear U p q s := by
  intro x hx
  obtain ⟨y,hy,hd⟩ := h x hx
  exact ⟨y,hy,hd.trans hTU⟩

theorem sideNear_shrink (hgeo : GeodesicSpace M) {B T : ℕ}
    (hB : CochainBound M B) (hlarge : 10000*(B+1) < T)
    {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic)
    (hthin : TriangleNear T p q s) : SideNear (T-1) p q s := by
  classical
  intro o ho
  by_contra hn
  have hfar : ∀ x, q.Mem x ∨ s.Mem x → T ≤ M.dist o x := by
    intro x hx
    have hnot : ¬ M.dist o x ≤ T-1 := fun h => hn ⟨x,hx,h⟩
    omega
  have hb := shortBypass_triangle hgeo hp hq hs hthin ho hfar
  have hh := quadratic_bound (shortBypass_quadratic hB hb)
  omega

theorem triangleNear_shrink (hgeo : GeodesicSpace M) {B T : ℕ}
    (hB : CochainBound M B) (hlarge : 10000*(B+1) < T)
    {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic)
    (hthin : TriangleNear T p q s) : TriangleNear (T-1) p q s := by
  refine ⟨sideNear_shrink hgeo hB hlarge hp hq hs hthin,?_,?_⟩
  · have hn : TriangleNear T q s.reverse p.reverse :=
      ⟨(hthin.2.1.reverse_left T).reverse_right T,
        (hthin.2.2.reverse T).reverse_left T,
        (hthin.1.reverse T).reverse_right T⟩
    have hh := sideNear_shrink hgeo hB hlarge hq (s.geodesic_reverse hs)
      (p.geodesic_reverse hp) hn
    intro x hx
    obtain ⟨y,hy,hd⟩ := hh x hx
    exact ⟨y,hy.imp ((s.mem_reverse_iff y).mp) ((p.mem_reverse_iff y).mp),hd⟩
  · have hn : TriangleNear T s q.reverse p :=
      ⟨(hthin.2.2.swap T).reverse_left T,
        (hthin.2.1.swap T).reverse T,
        (hthin.1.swap T).reverse_right T⟩
    have hh := sideNear_shrink hgeo hB hlarge hs (q.geodesic_reverse hq) hp hn
    intro x hx
    obtain ⟨y,hy,hd⟩ := hh x hx
    exact ⟨y,(hy.imp ((q.mem_reverse_iff y).mp) id).symm,hd⟩

/-- Discrete linear filling implies genuine uniform thinness of geodesic triangles. -/
theorem triangleNear_of_cochainBound (hgeo : GeodesicSpace M) {B : ℕ}
    (hB : CochainBound M B) {p : Path M a b} {q : Path M b c} {s : Path M a c}
    (hp : p.Geodesic) (hq : q.Geodesic) (hs : s.Geodesic) :
    TriangleNear (10000*(B+1)) p q s := by
  classical
  have hex : ∃ T, TriangleNear T p q s := by
    refine ⟨p.length+q.length+s.length,?_,?_,?_⟩
    · intro x hx
      refine ⟨a,Or.inr s.start_mem,?_⟩
      rw [M.symm]
      exact (p.dist_start_mem hx).trans (by omega)
    · intro x hx
      refine ⟨b,Or.inr p.end_mem,?_⟩
      rw [M.symm]
      exact (q.dist_start_mem hx).trans (by omega)
    · intro x hx
      refine ⟨a,Or.inl p.start_mem,?_⟩
      rw [M.symm]
      exact (s.dist_start_mem hx).trans (by omega)
  let T := Nat.find hex
  have hthin : TriangleNear T p q s := Nat.find_spec hex
  have hT : T ≤ 10000*(B+1) := by
    by_contra hn
    have hshrink := triangleNear_shrink hgeo hB (by omega : 10000*(B+1) < T) hp hq hs hthin
    have hf := Nat.find_min' hex hshrink
    change T ≤ T-1 at hf
    omega
  exact ⟨hthin.1.mono hT,by
    intro x hx
    obtain ⟨y,hy,hd⟩ := hthin.2.1 x hx
    exact ⟨y,hy,hd.trans hT⟩,by
    intro x hx
    obtain ⟨y,hy,hd⟩ := hthin.2.2 x hx
    exact ⟨y,hy,hd.trans hT⟩⟩

end Path
end Release075.Discrete

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.Discrete OAI.Release075.Discrete.Path


theorem solution : type_of% @_root_.OAI.Release075.Discrete.Path.triangleNear_of_cochainBound := @_root_.OAI.Release075.Discrete.Path.triangleNear_of_cochainBound
