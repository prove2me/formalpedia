-- Prove2me | solution 1 for OAI.CriticalZ3.SignedSymmetry.siteSeedReaches_map
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:50:29.589997+00:00
-- url     : https://prove2.me/submissions/e9383d79-0d1c-4f4a-a3fc-ff2c9552b2fd

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces

open OAI OAI.CriticalZ3 OAI.CriticalZ3.SignedSymmetry
universe uE uI uV uW
open MeasureTheory ProbabilityTheory Classical
open Classical
theorem cz_nn_iff (x y : Vertex) :
    NearestNeighbor x y ↔ ∑ i, |x i - y i| = 1 := by
  rw [Fin.sum_univ_three]
  constructor
  · rintro ⟨i, h | h⟩ <;> subst h <;> fin_cases i <;> simp [step] <;> norm_num
  · intro h
    have h0 := abs_nonneg (x 0 - y 0)
    have h1 := abs_nonneg (x 1 - y 1)
    have h2 := abs_nonneg (x 2 - y 2)
    have t0 : x 0 - y 0 = -1 ∨ x 0 - y 0 = 0 ∨ x 0 - y 0 = 1 := by
      rcases abs_cases (x 0 - y 0) with ⟨a, _⟩ | ⟨a, _⟩ <;> omega
    have t1 : x 1 - y 1 = -1 ∨ x 1 - y 1 = 0 ∨ x 1 - y 1 = 1 := by
      rcases abs_cases (x 1 - y 1) with ⟨a, _⟩ | ⟨a, _⟩ <;> omega
    have t2 : x 2 - y 2 = -1 ∨ x 2 - y 2 = 0 ∨ x 2 - y 2 = 1 := by
      rcases abs_cases (x 2 - y 2) with ⟨a, _⟩ | ⟨a, _⟩ <;> omega
    rcases t0 with e0 | e0 | e0 <;> rcases t1 with e1 | e1 | e1 <;> rcases t2 with e2 | e2 | e2 <;>
    rw [e0, e1, e2] at h <;> norm_num at h <;>
    first
    | (refine ⟨0, Or.inl (funext fun j => ?_)⟩; fin_cases j <;> simp [step] <;> omega)
    | (refine ⟨0, Or.inr (funext fun j => ?_)⟩; fin_cases j <;> simp [step] <;> omega)
    | (refine ⟨1, Or.inl (funext fun j => ?_)⟩; fin_cases j <;> simp [step] <;> omega)
    | (refine ⟨1, Or.inr (funext fun j => ?_)⟩; fin_cases j <;> simp [step] <;> omega)
    | (refine ⟨2, Or.inl (funext fun j => ?_)⟩; fin_cases j <;> simp [step] <;> omega)
    | (refine ⟨2, Or.inr (funext fun j => ?_)⟩; fin_cases j <;> simp [step] <;> omega)

theorem cz_vertex_sub (S : SignedSymmetry) (x y : Vertex) (i : Fin 3) :
    |S.vertex x i - S.vertex y i| = |x (S.perm i) - y (S.perm i)| := by
  simp only [SignedSymmetry.vertex, Equiv.coe_fn_mk]
  split_ifs
  · congr 1; ring
  · rw [← abs_neg]; congr 1; ring

theorem cz_nn_map (S : SignedSymmetry) (x y : Vertex) :
    NearestNeighbor (S.vertex x) (S.vertex y) ↔ NearestNeighbor x y := by
  rw [cz_nn_iff, cz_nn_iff]
  simp only [cz_vertex_sub]
  rw [Equiv.sum_comp S.perm (fun i => |x i - y i|)]

theorem cz_cube_map (S : SignedSymmetry) (c x : Vertex) (n : ℕ) :
    S.vertex x ∈ cube (S.vertex c) n ↔ x ∈ cube c n := by
  have key : ∀ (a b : Vertex), (∀ i, |a i - b i| ≤ n) ↔ a ∈ cube b n := by
    intro a b
    rw [mem_cube]
    refine forall_congr' fun i => ?_
    rw [abs_le]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [← key, ← key]
  simp only [cz_vertex_sub]
  constructor
  · intro h i; simpa using h (S.perm.symm i)
  · intro h i; exact h _

theorem solution (S : SignedSymmetry) (ω : SiteConfig) (c : Vertex) (m n : ℕ)
    (T : Set Vertex) :
    (fun e => ω (S.vertex e)) ∈ siteSeedReaches c m n (S.vertex ⁻¹' T) ↔
      ω ∈ siteSeedReaches (S.vertex c) m n T := by
  have hopen : ∀ a b, SiteOpen (fun e => ω (S.vertex e)) a b ↔ SiteOpen ω (S.vertex a) (S.vertex b) := by
    intro a b
    simp only [SiteOpen, cz_nn_map]
  constructor
  · rintro ⟨x, hx, hωx, y, hy, hxy⟩
    refine ⟨S.vertex x, (cz_cube_map S c x m).mpr hx, hωx, S.vertex y, hy, ?_⟩
    refine hxy.lift S.vertex (fun a b hab => ?_)
    obtain ⟨ha, hb, hab⟩ := hab
    exact ⟨(cz_cube_map S c a n).mpr ha, (cz_cube_map S c b n).mpr hb, (hopen a b).mp hab⟩
  · rintro ⟨x', hx', hωx', y', hy', hxy'⟩
    refine ⟨S.vertex.symm x', ?_, by simpa using hωx', S.vertex.symm y', by simpa using hy', ?_⟩
    · rw [← cz_cube_map S]; simpa using hx'
    · refine hxy'.lift S.vertex.symm (fun a b hab => ?_)
      obtain ⟨ha, hb, hab⟩ := hab
      refine ⟨?_, ?_, ?_⟩
      · rw [← cz_cube_map S]; simpa using ha
      · rw [← cz_cube_map S]; simpa using hb
      · rw [hopen]; simpa using hab

