-- Prove2me | solution 1 for OAI.ComplexCancellation.GradedLND.component_locallyNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:43:54.395631+00:00
-- url     : https://prove2.me/submissions/37a066b2-cf2a-42b2-a5f9-53b87526a5d1

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/GradedLND.lean:L155-L184
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.GradedLND.component_locallyNilpotent. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND

-- ---- from OAI.Algebra.AffineCancellation.GradedLND ----
namespace OAI

noncomputable section

namespace ComplexCancellation.GradedLND
open DirectSum
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
variable (G : ℤ → Submodule k R) [GradedAlgebra G]

lemma proj_of_mem {r : R} {i : ℤ} (hr : r ∈ G i) : proj G i r = r :=
  decompose_of_mem_same G hr

lemma proj_of_mem_ne {r : R} {i j : ℤ} (hr : r ∈ G i) (hne : i ≠ j) :
    proj G j r = 0 := decompose_of_mem_ne G hr hne

lemma component_of_mem (D : Derivation k R R) (j : ℤ) {r : R} {i : ℤ}
    (hr : r ∈ G i) : component G D j r = proj G (i+j) (D r) :=
  componentLinear_of_mem G D.toLinearMap j hr

omit [GradedAlgebra G] in
lemma mem_filtration {r : R} {i d : ℤ} (hr : r ∈ G i) (hid : i ≤ d) :
    r ∈ filtration G d := Submodule.mem_iSup_of_mem ⟨i, hid⟩ hr

omit [GradedAlgebra G] in
lemma filtration_mono {d e : ℤ} (h : d ≤ e) : filtration G d ≤ filtration G e := by
  apply iSup_le
  intro i
  exact fun r hr => mem_filtration G hr (i.2.trans h)

lemma proj_filtration {r : R} {d i : ℤ} (hr : r ∈ filtration G d) (hdi : d < i) :
    proj G i r = 0 := by
  refine Submodule.iSup_induction (fun t : {i : ℤ // i ≤ d} => G t)
    (motive := fun r => proj G i r = 0) hr ?_ ?_ ?_
  · intro t r hr
    exact proj_of_mem_ne G hr (by have ht := t.2; omega)
  · exact map_zero _
  · intro a b ha hb
    rw [map_add, ha, hb, add_zero]

omit [GradedAlgebra G] in
lemma map_filtration {D : Derivation k R R} {j : ℤ} (hD : ShiftBound G D j)
    {r : R} {d : ℤ} (hr : r ∈ filtration G d) : D r ∈ filtration G (d+j) := by
  refine Submodule.iSup_induction (fun t : {i : ℤ // i ≤ d} => G t)
    (motive := fun r => D r ∈ filtration G (d+j)) hr ?_ ?_ ?_
  · intro i r hr
    exact filtration_mono G (by have ht := i.2; omega) (hD i r hr)
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b ha hb
    rw [map_add]; exact Submodule.add_mem _ ha hb

lemma top_map {D : Derivation k R R} {j : ℤ} (hD : ShiftBound G D j)
    {r : R} {d : ℤ} (hr : r ∈ filtration G d) :
    proj G (d+j) (D r) = component G D j (proj G d r) := by
  refine Submodule.iSup_induction (fun t : {i : ℤ // i ≤ d} => G t)
    (motive := fun r => proj G (d+j) (D r) = component G D j (proj G d r))
    hr ?_ ?_ ?_
  · intro i r hr
    by_cases hi : (i : ℤ) = d
    · have hr' : r ∈ G d := hi ▸ hr
      rw [proj_of_mem G hr', component_of_mem G D j hr']
    · have hid : (i : ℤ) < d := lt_of_le_of_ne i.2 hi
      rw [proj_of_mem_ne G hr hi, map_zero]
      exact proj_filtration G (hD i r hr) (by omega)
  · simp
  · intro a b ha hb
    simp only [map_add, ha, hb]

lemma iterate_top {D : Derivation k R R} {j : ℤ} (hD : ShiftBound G D j)
    {r : R} {i : ℤ} (hr : r ∈ G i) (n : ℕ) :
    (D : R → R)^[n] r ∈ filtration G (i+n*j) ∧
    proj G (i+n*j) ((D : R → R)^[n] r) = ((component G D j : R → R)^[n] r) := by
  induction n with
  | zero => simpa using And.intro (mem_filtration G hr le_rfl) (proj_of_mem G hr)
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hn : i+(↑(n+1) : ℤ)*j = (i+n*j)+j := by push_cast; ring
    rw [hn]
    exact ⟨map_filtration G hD ih.1, (top_map G hD ih.1).trans (congrArg _ ih.2)⟩

/-- Local nilpotence survives passage to the highest homogeneous component,
including for gradings with negative degrees. -/
lemma component_locallyNilpotent {D : Derivation k R R} {j : ℤ}
    (hD : ShiftBound G D j) (hln : ∀ r : R, ∃ n : ℕ, (D : R → R)^[n] r = 0) :
    ∀ r : R, ∃ n : ℕ, (component G D j : R → R)^[n] r = 0 := by
  intro r
  induction r using DirectSum.Decomposition.inductionOn G with
  | zero => exact ⟨0, rfl⟩
  | @homogeneous i r =>
    obtain ⟨n, hn⟩ := hln r
    refine ⟨n, ?_⟩
    have h := (iterate_top G hD r.2 n).2
    rw [hn, map_zero] at h
    exact h.symm
  | add r s hr hs =>
    obtain ⟨n, hn⟩ := hr
    obtain ⟨m, hm⟩ := hs
    let E := (component G D j).toLinearMap
    change (E : R → R)^[n] r = 0 at hn
    change (E : R → R)^[m] s = 0 at hm
    refine ⟨n+m, ?_⟩
    change (E : R → R)^[n+m] (r+s) = 0
    rw [← Module.End.pow_apply, map_add]
    have hnr : (E ^ (n+m)) r = 0 := by
      rw [Module.End.pow_apply, Nat.add_comm, Function.iterate_add_apply, hn]
      simpa only [Module.End.pow_apply] using (E ^ m).map_zero
    have hms : (E ^ (n+m)) s = 0 := by
      rw [Module.End.pow_apply, Function.iterate_add_apply, hm]
      simpa only [Module.End.pow_apply] using (E ^ n).map_zero
    rw [hnr, hms, add_zero]

end ComplexCancellation.GradedLND

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.GradedLND
open DirectSum


theorem solution : type_of% @_root_.OAI.ComplexCancellation.GradedLND.component_locallyNilpotent := @_root_.OAI.ComplexCancellation.GradedLND.component_locallyNilpotent
