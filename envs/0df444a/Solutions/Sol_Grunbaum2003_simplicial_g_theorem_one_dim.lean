-- Prove2me | solution 1 for Grunbaum2003.simplicial_g_theorem_one_dim
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T07:15:57.115315+00:00
-- url     : https://prove2.me/submissions/448163b8-e6fb-4895-b32c-52072523d74d

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_BoundaryRefines
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.DiscreteSubset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped BigOperators

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




/-- Every face of a `d`-polytope (`d > 0`) either lies in the `(d - 2)`-skeleton,
equals the improper face `P` itself, or is a facet of dimension `d - 1`. -/
theorem polytopeFace_trichotomy_codim_two (d : ℕ) (hd : 0 < d)
    (P : Set (Fin d → ℝ)) (F : PolytopeFace P) :
    (F.val = ∅ ∨ Module.finrank ℝ (affineSpan ℝ F.val).direction ≤ d - 2) ∨
      F.val = P ∨
      (F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d - 1) := by
  rcases F.val.eq_empty_or_nonempty with hEmpty | hFne
  · exact Or.inl (Or.inl hEmpty)
  · have hle : Module.finrank ℝ (affineSpan ℝ F.val).direction ≤ d := by
      have h1 := Submodule.finrank_le (affineSpan ℝ F.val).direction
      simpa [Module.finrank_fin_fun] using h1
    rcases ( by omega :
        Module.finrank ℝ (affineSpan ℝ F.val).direction ≤ d - 2 ∨
        Module.finrank ℝ (affineSpan ℝ F.val).direction = d - 1 ∨
        Module.finrank ℝ (affineSpan ℝ F.val).direction = d ) with h2 | h1 | h0
    · exact Or.inl (Or.inr h2)
    · exact Or.inr (Or.inr ⟨hFne, h1⟩)
    · refine Or.inr (Or.inl ?_)
      obtain ⟨l, hl⟩ := F.2 hFne
      have hdir_top : (affineSpan ℝ F.val).direction = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        rw [h0, Module.finrank_fin_fun]
      have hker_top : (⊤ : Submodule ℝ (Fin d → ℝ)) ≤ LinearMap.ker l.toLinearMap := by
        rw [← hdir_top, direction_affineSpan, vectorSpan_def, Submodule.span_le]
        rintro v ⟨a, ha, b, hb, rfl⟩
        have haP : a ∈ P := by rw [hl] at ha; exact ha.1
        have hbP : b ∈ P := by rw [hl] at hb; exact hb.1
        have hamax : ∀ y ∈ P, l y ≤ l a := by rw [hl] at ha; exact ha.2
        have hbmax : ∀ y ∈ P, l y ≤ l b := by rw [hl] at hb; exact hb.2
        have hab : l a = l b := le_antisymm (hbmax a haP) (hamax b hbP)
        simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
          vsub_eq_sub, map_sub, hab, sub_self]
      have hl_eq : ∀ x y : Fin d → ℝ, l x = l y := by
        intro x y
        have hxy : x - y ∈ LinearMap.ker l.toLinearMap := hker_top trivial
        simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, sub_eq_zero] at hxy
        exact hxy
      rw [hl]
      ext x
      simp only [Set.mem_setOf_eq, and_iff_left_iff_imp]
      intro _ y _
      exact le_of_eq (hl_eq y x)




/-- The first positive Macaulay condition permits every natural first entry. -/
theorem isMSequence_one_iff (g : ℕ → ℕ) : IsMSequence 1 g ↔ g 0 = 1 := by
  constructor
  · exact fun h => h.1
  · intro hg₀
    refine ⟨hg₀, ?_⟩
    intro k hk₀ hk₁
    have hk : k = 1 := by omega
    subst k
    by_cases hz : g 1 = 0
    · exact Or.inl hz
    · refine Or.inr ⟨1, fun _ => g 1, by omega, le_refl _, ?_, ?_, ?_, ?_⟩
      · change 1 ≤ g 1
        omega
      · intro r s hr hrs hs
        omega
      · simp only [Finset.Icc_self, Finset.sum_singleton, Nat.choose_one_right]
      · simp only [Finset.Icc_self, Finset.sum_singleton, Nat.sub_self,
          Nat.choose_zero_right, hg₀, le_refl]

/-- In dimension one, the arithmetic side of the exact g-theorem prescribes two vertices. -/
theorem g_theorem_rhs_dim_one_iff (f : Fin 2 → ℤ) :
    (∃ g : ℕ → ℕ, IsMSequence (1 / 2) g ∧
      ∀ k : Fin 2, f k = ∑ j ∈ Finset.range (1 / 2 + 1),
        (g j : ℤ) * gTheoremMatrix 1 j k.val) ↔
      f 0 = 1 ∧ f 1 = 2 := by
  constructor
  · rintro ⟨g, hg, hf⟩
    have h₀ := hf 0
    have h₁ := hf 1
    norm_num [gTheoremMatrix, hg.1] at h₀ h₁
    exact ⟨h₀, h₁⟩
  · rintro ⟨h₀, h₁⟩
    refine ⟨fun _ => 1, ⟨rfl, ?_⟩, ?_⟩
    · intro k hk₀ hk₁
      omega
    · intro k
      fin_cases k <;> norm_num [gTheoremMatrix, h₀, h₁]

/-- Dimension two reduces to the face vector of a polygon with n+3 vertices. -/
theorem g_theorem_rhs_dim_two_iff (f : Fin 3 → ℤ) :
    (∃ g : ℕ → ℕ, IsMSequence (2 / 2) g ∧
      ∀ k : Fin 3, f k = ∑ j ∈ Finset.range (2 / 2 + 1),
        (g j : ℤ) * gTheoremMatrix 2 j k.val) ↔
      f 0 = 1 ∧ ∃ n : ℕ, f 1 = (n : ℤ) + 3 ∧ f 2 = (n : ℤ) + 3 := by
  constructor
  · rintro ⟨g, hg, hf⟩
    have h₀ := hf 0
    have h₁ := hf 1
    have h₂ := hf 2
    norm_num [gTheoremMatrix, Nat.choose, Finset.sum_range_succ, hg.1] at h₀ h₁ h₂
    refine ⟨h₀, g 1, ?_, ?_⟩ <;> omega
  · rintro ⟨h₀, n, h₁, h₂⟩
    let g : ℕ → ℕ := fun i => if i = 0 then 1 else n
    refine ⟨g, (isMSequence_one_iff g).mpr (by simp only [g, if_pos rfl]), ?_⟩
    intro k
    fin_cases k
    · change f 0 = _
      rw [h₀]
      norm_num [gTheoremMatrix, Nat.choose, Finset.sum_range_succ, g]
    · change f 1 = _
      rw [h₁]
      norm_num [gTheoremMatrix, Nat.choose, Finset.sum_range_succ, g]
      omega
    · change f 2 = _
      rw [h₂]
      norm_num [gTheoremMatrix, Nat.choose, Finset.sum_range_succ, g]
      omega

/-- Dimension three prescribes exactly the simplicial three-polytope face equations. -/
theorem g_theorem_rhs_dim_three_iff (f : Fin 4 → ℤ) :
    (∃ g : ℕ → ℕ, IsMSequence (3 / 2) g ∧
      ∀ k : Fin 4, f k = ∑ j ∈ Finset.range (3 / 2 + 1),
        (g j : ℤ) * gTheoremMatrix 3 j k.val) ↔
      f 0 = 1 ∧ ∃ n : ℕ,
        f 1 = (n : ℤ) + 4 ∧ f 2 = (n : ℤ) * 3 + 6 ∧ f 3 = (n : ℤ) * 2 + 4 := by
  constructor
  · rintro ⟨g, hg, hf⟩
    have h₀ := hf 0
    have h₁ := hf 1
    have h₂ := hf 2
    have h₃ := hf 3
    norm_num [gTheoremMatrix, Nat.choose, Finset.sum_range_succ, hg.1] at h₀ h₁ h₂ h₃
    refine ⟨h₀, g 1, ?_, ?_, ?_⟩ <;> omega
  · rintro ⟨h₀, n, h₁, h₂, h₃⟩
    let g : ℕ → ℕ := fun i => if i = 0 then 1 else n
    refine ⟨g, (isMSequence_one_iff g).mpr (by simp only [g, if_pos rfl]), ?_⟩
    intro k
    fin_cases k
    · change f 0 = _
      rw [h₀]
      norm_num [gTheoremMatrix, Nat.choose, Finset.sum_range_succ, g]
    · change f 1 = _
      rw [h₁]
      norm_num [gTheoremMatrix, Nat.choose, Finset.sum_range_succ, g]
      omega
    · change f 2 = _
      rw [h₂]
      norm_num [gTheoremMatrix, Nat.choose, Finset.sum_range_succ, g]
      omega
    · change f 3 = _
      rw [h₃]
      norm_num [gTheoremMatrix, Nat.choose, Finset.sum_range_succ, g]
      omega




/-- Every actual one-dimensional polytope has exactly two nonempty zero-dimensional faces. -/
theorem one_dimensional_faceCount_zero (P : Set (Fin 1 → ℝ)) (hP : IsDPolytope P) :
    faceCount P 0 = 2 := by
  classical
  obtain ⟨e, he⟩ := one_dimensional_face_equiv P hP
  have heVal : Function.Injective (fun i : Fin 4 => (e i).val) := by
    intro i j hij
    exact e.injective (Subtype.ext hij)
  have hBot (F : PolytopeFace P) : e 0 ≤ F := by
    obtain ⟨i, rfl⟩ := e.surjective F
    exact (he 0 i).mpr (Or.inl rfl)
  have hTop (F : PolytopeFace P) : F ≤ e 3 := by
    obtain ⟨i, rfl⟩ := e.surjective F
    exact (he i 3).mpr (Or.inr (Or.inl rfl))
  have he₀ : (e 0).val = ∅ :=
    Set.Subset.antisymm (hBot ⟨∅, isExposed_empty⟩) (Set.empty_subset _)
  have he₃ : (e 3).val = P :=
    Set.Subset.antisymm (e 3).property.subset (hTop ⟨P, IsExposed.refl P⟩)
  have hRankP : Module.finrank ℝ (affineSpan ℝ P).direction = 1 := by
    rw [hP.2, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun]
  have hProperRank (F : Set (Fin 1 → ℝ)) (hne : F.Nonempty)
      (hF : IsExposed ℝ P F) (hFP : F ≠ P) :
      Module.finrank ℝ (affineSpan ℝ F).direction = 0 := by
    rcases polytopeFace_trichotomy_codim_two 1 (by omega) P ⟨F, hF⟩ with
      (hEmpty | hLe) | hEq | ⟨_, hRank⟩
    · exact (hne.ne_empty hEmpty).elim
    · change Module.finrank ℝ (affineSpan ℝ F).direction ≤ 0 at hLe
      exact Nat.eq_zero_of_le_zero hLe
    · exact (hFP hEq).elim
    · exact hRank
  have hMid (i : Fin 4) (hi₀ : i ≠ 0) (hi₃ : i ≠ 3) :
      (e i).val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ (e i).val).direction = 0 := by
    have hEmpty : (e i).val ≠ ∅ := by
      intro h
      exact hi₀ (heVal (h.trans he₀.symm))
    have hFull : (e i).val ≠ P := by
      intro h
      exact hi₃ (heVal (h.trans he₃.symm))
    have hne := Set.nonempty_iff_ne_empty.mpr hEmpty
    exact ⟨hne, hProperRank (e i).val hne (e i).property hFull⟩
  have hSet : {F : Set (Fin 1 → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
      Module.finrank ℝ (affineSpan ℝ F).direction = 0} = {(e 1).val, (e 2).val} := by
    ext F
    constructor
    · rintro ⟨hne, hF, hRank⟩
      obtain ⟨i, hi⟩ := e.surjective ⟨F, hF⟩
      have hiVal : (e i).val = F := congrArg Subtype.val hi
      fin_cases i
      · exact (hne.ne_empty (hiVal.symm.trans he₀)).elim
      · exact Set.mem_insert_iff.mpr (Or.inl hiVal.symm)
      · exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr hiVal.symm)
      · have hFP : F = P := hiVal.symm.trans he₃
        rw [hFP, hRankP] at hRank
        omega
    · intro hF
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hF
      rcases hF with rfl | rfl
      · exact ⟨(hMid 1 (by decide) (by decide)).1, (e 1).property,
          (hMid 1 (by decide) (by decide)).2⟩
      · exact ⟨(hMid 2 (by decide) (by decide)).1, (e 2).property,
          (hMid 2 (by decide) (by decide)).2⟩
  unfold faceCount
  rw [hSet]
  exact Set.ncard_pair (fun h => by
    have h' : (1 : ℕ) = 2 := congrArg Fin.val (heVal h)
    omega)

/-- Every full-dimensional one-polytope is simplicial under the original facet predicate. -/
theorem isSimplicialDPolytope_one_of_isDPolytope
    (P : Set (Fin 1 → ℝ)) (hP : IsDPolytope P) : IsSimplicialDPolytope P := by
  refine ⟨hP, ?_⟩
  intro F hne _ hRank
  have hZero : Module.finrank ℝ (affineSpan ℝ F).direction = 0 := by omega
  have hDir : (affineSpan ℝ F).direction = ⊥ := Submodule.finrank_eq_zero.mp hZero
  have hSpan : vectorSpan ℝ F = ⊥ := by rwa [direction_affineSpan] at hDir
  have hSub : F.Subsingleton := (vectorSpan_eq_bot_iff_subsingleton ℝ).mp hSpan
  obtain ⟨x, hx⟩ := hne
  refine ⟨fun _ : Fin 1 => x, affineIndependent_of_subsingleton ℝ _, ?_⟩
  rw [Set.range_const, convexHull_singleton]
  exact hSub.eq_singleton_of_mem hx

/-- An actual simplicial segment, with the original face-count predicate. -/
theorem exists_simplicial_segment :
    ∃ P : Set (Fin 1 → ℝ), IsSimplicialDPolytope P ∧ faceCount P 0 = 2 := by
  let v : Fin 2 → (Fin 1 → ℝ) := ![0, 1]
  have hv : AffineIndependent ℝ v := affineIndependent_of_ne ℝ (by
    intro h
    have h₀ := congrFun h (0 : Fin 1)
    norm_num at h₀)
  let P := convexHull ℝ (Set.range v)
  have hP : IsDPolytope P := by
    refine ⟨⟨Set.range v, Set.finite_range v, Set.range_nonempty v, rfl⟩, ?_⟩
    rw [affineSpan_convexHull]
    exact hv.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)
  exact ⟨P, isSimplicialDPolytope_one_of_isDPolytope P hP,
    one_dimensional_faceCount_zero P hP⟩

/-- The exact original g-theorem specialization in dimension one. -/
theorem simplicial_g_theorem_one_dim (f : Fin (1 + 1) → ℤ) :
    (f 0 = 1 ∧ ∃ P : Set (Fin 1 → ℝ),
      IsSimplicialDPolytope P ∧
      ∀ j : Fin 1, f j.succ = (faceCount P j.val : ℤ)) ↔
    ∃ g : ℕ → ℕ, IsMSequence (1 / 2) g ∧
      ∀ k : Fin (1 + 1),
        f k = ∑ j ∈ Finset.range (1 / 2 + 1),
          (g j : ℤ) * gTheoremMatrix 1 j k.val := by
  rw [g_theorem_rhs_dim_one_iff]
  constructor
  · rintro ⟨hf₀, P, hP, hf⟩
    have hCount := one_dimensional_faceCount_zero P hP.1
    refine ⟨hf₀, ?_⟩
    have h := hf 0
    change f 1 = (faceCount P 0 : ℤ) at h
    rw [hCount] at h
    exact h
  · rintro ⟨hf₀, hf₁⟩
    obtain ⟨P, hP, hCount⟩ := exists_simplicial_segment
    refine ⟨hf₀, P, hP, ?_⟩
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change f 1 = (faceCount P 0 : ℤ)
    rw [hCount]
    exact hf₁


end Grunbaum2003

theorem solution (f : Fin (1 + 1) → ℤ) :
    (f 0 = 1 ∧ ∃ P : Set (Fin 1 → ℝ),
      Grunbaum2003.IsSimplicialDPolytope P ∧
      ∀ j : Fin 1, f j.succ = (Grunbaum2003.faceCount P j.val : ℤ)) ↔
    ∃ g : ℕ → ℕ, Grunbaum2003.IsMSequence (1 / 2) g ∧
      ∀ k : Fin (1 + 1),
        f k = ∑ j ∈ Finset.range (1 / 2 + 1),
          (g j : ℤ) * Grunbaum2003.gTheoremMatrix 1 j k.val :=
  Grunbaum2003.simplicial_g_theorem_one_dim f
