-- Prove2me | solution 1 for Grunbaum2003.ray_oracle_face_lattice_reconstruction_one_dim
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T18:10:06.741252+00:00
-- url     : https://prove2.me/submissions/e5a8fec8-385c-46e6-8d7e-cebcdd3d857a

import Theorems.Thm_Grunbaum2003_rayMachine_constant_printer
import Definitions.Def_Grunbaum2003_IsRayFaceLatticeOutput
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_BoundaryRefines
import Definitions.Def_Grunbaum2003_PolytopeFace
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.DiscreteSubset
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace Grunbaum2003

private def coord : (Fin 1 → ℝ) ≃L[ℝ] ℝ := ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => ℝ)

private theorem coord_apply (x : Fin 1 → ℝ) : coord x = x 0 := rfl

private theorem exists_interval_of_isDPolytope (P : Set (Fin 1 → ℝ)) (hP : IsDPolytope P) :
    ∃ a b : ℝ, a < b ∧ P = coord ⁻¹' Set.Icc a b := by
  obtain ⟨⟨V, hVfin, hVne, hPhull⟩, hSpan⟩ := hP
  have hComp : IsCompact P := hPhull ▸ hVfin.isCompact_convexHull ℝ
  have hPne : P.Nonempty := hPhull ▸ hVne.convexHull
  obtain ⟨a, ha⟩ := (hComp.image coord.continuous).exists_isLeast (hPne.image coord)
  obtain ⟨b, hb⟩ := (hComp.image coord.continuous).exists_isGreatest (hPne.image coord)
  have hImage : coord '' P = Set.Icc a b := by
    apply Set.Subset.antisymm
    · exact fun x hx => ⟨ha.2 hx, hb.2 hx⟩
    · have hc : Convex ℝ (coord '' P) := by
        rw [hPhull]
        exact (convex_convexHull ℝ V).linear_image coord.toLinearMap
      exact hc.ordConnected.out ha.1 hb.1
  have hEq : P = coord ⁻¹' Set.Icc a b := by
    rw [← hImage, Set.preimage_image_eq _ coord.injective]
  refine ⟨a, b, ?_, hEq⟩
  have hab : a ≤ b := ha.2 hb.1
  apply lt_of_le_of_ne hab
  intro heq
  have hSub : P.Subsingleton := by
    intro x hx y hy
    apply coord.injective
    have hx' : a ≤ coord x ∧ coord x ≤ b := by rwa [hEq] at hx
    have hy' : a ≤ coord y ∧ coord y ≤ b := by rwa [hEq] at hy
    exact (le_antisymm (heq ▸ hx'.2) hx'.1).trans (le_antisymm (heq ▸ hy'.2) hy'.1).symm
  haveI : Subsingleton (Fin 1 → ℝ) := AffineSubspace.subsingleton_of_subsingleton_span_eq_top hSub hSpan
  have hz : (0 : Fin 1 → ℝ) = 1 := Subsingleton.elim _ _
  have : (0 : ℝ) = 1 := congrFun hz 0
  exact zero_ne_one this

private theorem linear_on_one (l : StrongDual ℝ (Fin 1 → ℝ)) (x : Fin 1 → ℝ) :
    l x = x 0 * l 1 := by
  have hx : x = x 0 • (1 : Fin 1 → ℝ) := by ext i; have hi : i = 0 := Subsingleton.elim _ _; subst hi; simp
  calc
    l x = l (x 0 • (1 : Fin 1 → ℝ)) := congrArg l hx
    _ = x 0 * l 1 := by simp

private theorem interval_faces (a b : ℝ) (hab : a < b) :
    boundaryFaces (coord ⁻¹' Set.Icc a b) =
      {∅, {coord.symm a}, {coord.symm b}} := by
  let P := coord ⁻¹' Set.Icc a b
  have haP : coord.symm a ∈ P := by simp [P, hab.le]
  have hbP : coord.symm b ∈ P := by simp [P, hab.le]
  have hane : coord.symm a ≠ coord.symm b := fun h => hab.ne (coord.symm.injective h)
  have haexp : IsExposed ℝ P {coord.symm a} := by
    intro _
    refine ⟨-coord.toContinuousLinearMap, ?_⟩
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq, neg_apply]
    constructor
    · rintro rfl
      exact ⟨haP, fun y hy => neg_le_neg hy.1⟩
    · intro hx
      apply coord.injective
      have ht := hx.2 (coord.symm a) haP
      have hca : coord x = a := by
        change -coord (coord.symm a) ≤ -coord x at ht
        rw [coord.apply_symm_apply] at ht
        linarith [hx.1.1]
      simpa using hca
  have hbexp : IsExposed ℝ P {coord.symm b} := by
    intro _
    refine ⟨coord.toContinuousLinearMap, ?_⟩
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq, ContinuousLinearEquiv.coe_coe]
    constructor
    · rintro rfl
      exact ⟨hbP, fun y hy => hy.2⟩
    · intro hx
      apply coord.injective
      have ht := hx.2 (coord.symm b) hbP
      have hcb : coord x = b := by simp only [coord.apply_symm_apply] at ht; linarith [hx.1.2]
      simpa using hcb
  ext F
  constructor
  · rintro ⟨hFe, hFne⟩
    by_cases hEmpty : F = ∅
    · simp [hEmpty]
    obtain ⟨l, hl⟩ := hFe (Set.nonempty_iff_ne_empty.mpr hEmpty)
    have hcne : l 1 ≠ 0 := by
      intro hc
      apply hFne
      rw [hl]
      ext x
      constructor
      · exact fun h => h.1
      · intro hx
        refine ⟨hx, fun y hy => ?_⟩
        simp [linear_on_one, hc]
    rcases lt_or_gt_of_ne hcne with hc | hc
    · have hFa : F = {coord.symm a} := by
        rw [hl]
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · intro hx
          apply coord.injective
          have ht := hx.2 (coord.symm a) haP
          simp only [linear_on_one l x, linear_on_one l (coord.symm a)] at ht
          have ha0 : (coord.symm a) 0 = a := coord.apply_symm_apply a
          rw [ha0] at ht
          have hxa : x 0 ≤ a := (mul_le_mul_right_of_neg hc).mp ht
          have hxa' : a ≤ x 0 := hx.1.1
          exact (le_antisymm hxa hxa').trans (coord.apply_symm_apply a).symm
        · rintro rfl
          exact ⟨haP, fun y hy => by
            simp only [linear_on_one l y, linear_on_one l (coord.symm a)]
            change y 0 * l 1 ≤ a * l 1
            exact mul_le_mul_of_nonpos_right hy.1 hc.le⟩
      simp [hFa]
    · have hFb : F = {coord.symm b} := by
        rw [hl]
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · intro hx
          apply coord.injective
          have ht := hx.2 (coord.symm b) hbP
          simp only [linear_on_one l x, linear_on_one l (coord.symm b)] at ht
          have hb0 : (coord.symm b) 0 = b := coord.apply_symm_apply b
          rw [hb0] at ht
          have hxb : b ≤ x 0 := (mul_le_mul_iff_left₀ hc).mp ht
          have hxb' : x 0 ≤ b := hx.1.2
          exact (le_antisymm hxb' hxb).trans (coord.apply_symm_apply b).symm
        · rintro rfl
          exact ⟨hbP, fun y hy => by
            simp only [linear_on_one l y, linear_on_one l (coord.symm b)]
            change y 0 * l 1 ≤ b * l 1
            exact mul_le_mul_of_nonneg_right hy.2 hc.le⟩
      simp [hFb]
  · intro hF
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hF
    rcases hF with rfl | rfl | rfl
    · refine ⟨isExposed_empty, ?_⟩
      intro h
      change ∅ = P at h
      have ht := haP
      rw [← h] at ht
      exact ht
    · refine ⟨haexp, ?_⟩
      intro h
      change {coord.symm a} = P at h
      have ht := hbP
      rw [← h] at ht
      have : coord.symm b = coord.symm a := ht
      exact hane this.symm
    · refine ⟨hbexp, ?_⟩
      intro h
      change {coord.symm b} = P at h
      have ht := haP
      rw [← h] at ht
      have : coord.symm a = coord.symm b := ht
      exact hane this


private theorem interval_face_equiv (a b : ℝ) (hab : a < b) :
    ∃ e : Fin 4 ≃ PolytopeFace (coord ⁻¹' Set.Icc a b),
      ∀ i j, e i ≤ e j ↔ i = 0 ∨ j = 3 ∨ i = j := by
  let P := coord ⁻¹' Set.Icc a b
  let lo := coord.symm a
  let hi := coord.symm b
  have hlo : lo ∈ P := by simp [lo, P, hab.le]
  have hhi : hi ∈ P := by simp [hi, P, hab.le]
  have hne : lo ≠ hi := fun h => hab.ne (coord.symm.injective h)
  have hNotEmpty : P ≠ ∅ := by intro h; simpa [h] using hlo
  have hloexp : IsExposed ℝ P {lo} := by
    have h := interval_faces a b hab
    have hm : {lo} ∈ boundaryFaces P := by rw [h]; simp [lo]
    exact hm.1
  have hhiexp : IsExposed ℝ P {hi} := by
    have h := interval_faces a b hab
    have hm : {hi} ∈ boundaryFaces P := by rw [h]; simp [hi]
    exact hm.1
  have hPlo : P ≠ {lo} := by intro h; have hx := hhi; rw [h, Set.mem_singleton_iff] at hx; exact hne hx.symm
  have hPhi : P ≠ {hi} := by intro h; have hx := hlo; rw [h, Set.mem_singleton_iff] at hx; exact hne hx
  let v : Fin 4 → PolytopeFace P :=
    ![⟨∅, isExposed_empty⟩, ⟨{lo}, hloexp⟩, ⟨{hi}, hhiexp⟩, ⟨P, IsExposed.refl P⟩]
  have hvInj : Function.Injective v := by
    intro i j hij
    have hval := congrArg (fun F : PolytopeFace P => F.val) hij
    fin_cases i <;> fin_cases j <;> simp_all [v]
  have hvSurj : Function.Surjective v := by
    intro F
    by_cases heq : F.val = P
    · refine ⟨3, ?_⟩; apply Subtype.ext; exact heq.symm
    · have hm : F.val ∈ boundaryFaces P := ⟨F.property, heq⟩
      rw [interval_faces a b hab] at hm
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with h | h | h
      · refine ⟨0, ?_⟩; apply Subtype.ext; exact h.symm
      · refine ⟨1, ?_⟩; apply Subtype.ext; exact h.symm
      · refine ⟨2, ?_⟩; apply Subtype.ext; exact h.symm
  let e := Equiv.ofBijective v ⟨hvInj, hvSurj⟩
  refine ⟨e, ?_⟩
  have hPnotlo : ¬ P ⊆ {lo} := fun h => hne (Set.mem_singleton_iff.mp (h hhi)).symm
  have hPnothi : ¬ P ⊆ {hi} := fun h => hne (Set.mem_singleton_iff.mp (h hlo))
  intro i j
  change (v i).val ⊆ (v j).val ↔ _
  fin_cases i <;> fin_cases j <;>
    simp [v, hne, hne.symm, hlo, hhi, hNotEmpty, hPnotlo, hPnothi]

theorem one_dimensional_face_equiv (P : Set (Fin 1 → ℝ)) (hP : IsDPolytope P) :
    ∃ e : Fin 4 ≃ PolytopeFace P,
      ∀ i j, e i ≤ e j ↔ i = 0 ∨ j = 3 ∨ i = j := by
  obtain ⟨a, b, hab, hPab⟩ := exists_interval_of_isDPolytope P hP
  rw [hPab]
  exact interval_face_equiv a b hab

end Grunbaum2003


namespace Grunbaum2003


theorem ray_oracle_face_lattice_reconstruction_one_dim :
    ∃ program : List RayInstruction,
      ∀ P : Set (Fin 1 → ℝ), IsDPolytope P →
        ∀ oracle : (Fin 1 → ℝ) → (Fin 1 → ℝ),
          ∃ (t : ℕ) (c : RayConfiguration),
            rayMachineRun program oracle t
              { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
            program[c.pc]? = some .halt ∧ c.queries = 0 ∧
            IsRayFaceLatticeOutput P c := by
  let cells : List ℚ := [1,1,1,1,0, 1,1,1,1, 0,1,0,1, 0,0,1,1, 0,0,0,1]
  obtain ⟨program, hprogram⟩ := rayMachine_constant_printer cells
  refine ⟨program, ?_⟩
  intro P hP oracle
  obtain ⟨c, hrun, hhalt, hhead, hqueries, htape⟩ := hprogram 1 oracle
  refine ⟨cells.length, c, hrun, hhalt, hqueries, ?_⟩
  obtain ⟨e, he⟩ := one_dimensional_face_equiv P hP
  refine ⟨4, ?_, ?_, e, ?_⟩
  · intro i
    have h := htape ⟨i.val, by dsimp [cells]; omega⟩
    fin_cases i <;> simpa [cells, hhead] using h
  · simpa [cells, hhead] using htape ⟨4, by decide⟩
  · intro i j
    have hbit := htape ⟨4 + 1 + i.val * 4 + j.val, by dsimp [cells]; omega⟩
    rw [he]
    fin_cases i <;> fin_cases j <;>
      norm_num [cells, hhead] at hbit ⊢ <;> simp_all


end Grunbaum2003

open Grunbaum2003
theorem solution :
    ∃ program : List RayInstruction,
      ∀ P : Set (Fin 1 → ℝ), IsDPolytope P →
        ∀ oracle : (Fin 1 → ℝ) → (Fin 1 → ℝ),
          ∃ (t : ℕ) (c : RayConfiguration),
            rayMachineRun program oracle t
              { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
            program[c.pc]? = some .halt ∧ c.queries = 0 ∧
            IsRayFaceLatticeOutput P c :=
  Grunbaum2003.ray_oracle_face_lattice_reconstruction_one_dim
