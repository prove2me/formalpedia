-- Prove2me | solution 1 for Grunbaum2003.boundary_refines_simplex_one_dim
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T18:04:05.094339+00:00
-- url     : https://prove2.me/submissions/340e6bf7-9c06-41e3-8cea-21874d2b015a

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_BoundaryRefines
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


private theorem interval_boundary_carrier (a b : ℝ) (hab : a < b) :
    ⋃₀ boundaryFaces (coord ⁻¹' Set.Icc a b) = {coord.symm a, coord.symm b} := by
  rw [interval_faces a b hab]
  ext x
  simp [or_comm]

private theorem singleton_subfaces {x : Fin 1 → ℝ} {G : Set (Fin 1 → ℝ)}
    (hG : IsExposed ℝ ({x} : Set (Fin 1 → ℝ)) G) : G = ∅ ∨ G = {x} := by
  by_cases h : G = ∅
  · exact Or.inl h
  · right
    obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr h
    have hyx : y = x := Set.mem_singleton_iff.mp (hG.subset hy)
    exact Set.Subset.antisymm hG.subset (Set.singleton_subset_iff.mpr (hyx ▸ hy))

private theorem interval_boundary_refines (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
    BoundaryRefines (coord ⁻¹' Set.Icc a b) (coord ⁻¹' Set.Icc c d) := by
  classical
  let P := coord ⁻¹' Set.Icc a b
  let Q := coord ⁻¹' Set.Icc c d
  have hPB : ⋃₀ boundaryFaces P = {coord.symm a, coord.symm b} := interval_boundary_carrier a b hab
  have hQB : ⋃₀ boundaryFaces Q = {coord.symm c, coord.symm d} := interval_boundary_carrier c d hcd
  have hane : coord.symm a ≠ coord.symm b := fun h => hab.ne (coord.symm.injective h)
  have hcne : coord.symm c ≠ coord.symm d := fun h => hcd.ne (coord.symm.injective h)
  have hPmem (x : ⋃₀ boundaryFaces P) : x.val = coord.symm a ∨ x.val = coord.symm b := by
    exact (Set.ext_iff.mp hPB x.val).mp x.property
  have hQmem (x : ⋃₀ boundaryFaces Q) : x.val = coord.symm c ∨ x.val = coord.symm d := by
    exact (Set.ext_iff.mp hQB x.val).mp x.property
  haveI : Finite (⋃₀ boundaryFaces P) := Set.finite_coe_iff.mpr (by rw [hPB]; exact (Set.finite_singleton _).insert _)
  haveI : Finite (⋃₀ boundaryFaces Q) := Set.finite_coe_iff.mpr (by rw [hQB]; exact (Set.finite_singleton _).insert _)
  let f : (⋃₀ boundaryFaces P) → (⋃₀ boundaryFaces Q) := fun x =>
    ⟨if x.val = coord.symm a then coord.symm c else coord.symm d, by rw [hQB]; split <;> simp⟩
  let g : (⋃₀ boundaryFaces Q) → (⋃₀ boundaryFaces P) := fun x =>
    ⟨if x.val = coord.symm c then coord.symm a else coord.symm b, by rw [hPB]; split <;> simp⟩
  let e : (⋃₀ boundaryFaces P) ≃ₜ (⋃₀ boundaryFaces Q) := {
    toFun := f
    invFun := g
    left_inv := by
      intro x
      apply Subtype.ext
      rcases hPmem x with hx | hx
      · simp [f, g, hx]
      · simp [f, g, hx, hane.symm, hcne.symm]
    right_inv := by
      intro x
      apply Subtype.ext
      rcases hQmem x with hx | hx
      · simp [f, g, hx]
      · simp [f, g, hx, hcne.symm, hane.symm]
    continuous_toFun := continuous_of_discreteTopology
    continuous_invFun := continuous_of_discreteTopology
  }
  refine ⟨e, ?_⟩
  intro K hK
  have hFacesP := interval_faces a b hab
  have hFacesQ := interval_faces c d hcd
  change K ∈ boundaryFaces Q at hK
  rw [hFacesQ] at hK
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK
  rcases hK with rfl | rfl | rfl
  · refine ⟨{∅}, Set.finite_singleton _, ?_, ?_, ?_⟩
    · intro F hF
      rw [hFacesP]
      have ht : F = ∅ := hF
      simp [ht]
    · intro F hF G hG
      have hF0 : F = ∅ := hF
      subst F
      exact Set.subset_empty_iff.mp hG.subset
    · intro x
      simp
  · refine ⟨{∅, {coord.symm a}}, (Set.finite_singleton _).insert _, ?_, ?_, ?_⟩
    · intro F hF
      rw [hFacesP]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hF ⊢
      exact hF.imp_right Or.inl
    · intro F hF G hG
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hF ⊢
      rcases hF with rfl | rfl
      · exact Or.inl (Set.subset_empty_iff.mp hG.subset)
      · exact singleton_subfaces hG
    · intro x
      change (f x).val ∈ ({coord.symm c} : Set (Fin 1 → ℝ)) ↔ _
      simp only [f, Set.mem_singleton_iff, Set.sUnion_pair, Set.empty_union]
      by_cases hx : x.val = coord.symm a
      · simp [hx]
      · simp [hx, hcne.symm]
  · refine ⟨{∅, {coord.symm b}}, (Set.finite_singleton _).insert _, ?_, ?_, ?_⟩
    · intro F hF
      rw [hFacesP]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hF ⊢
      exact hF.imp_right Or.inr
    · intro F hF G hG
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hF ⊢
      rcases hF with rfl | rfl
      · exact Or.inl (Set.subset_empty_iff.mp hG.subset)
      · exact singleton_subfaces hG
    · intro x
      change (f x).val ∈ ({coord.symm d} : Set (Fin 1 → ℝ)) ↔ _
      simp only [f, Set.mem_singleton_iff, Set.sUnion_pair, Set.empty_union]
      rcases hPmem x with hx | hx
      · simp [hx, hcne, hab.ne]
      · simp [hx, hane.symm]


theorem boundary_refines_simplex_one_dim
    (P : Set (Fin 1 → ℝ)) (hP : IsDPolytope P)
    (v : Fin 2 → (Fin 1 → ℝ)) (hv : AffineIndependent ℝ v) :
    BoundaryRefines P (convexHull ℝ (Set.range v)) := by
  obtain ⟨a, b, hab, hPab⟩ := exists_interval_of_isDPolytope P hP
  have hQ : IsDPolytope (convexHull ℝ (Set.range v)) := by
    refine ⟨⟨Set.range v, Set.finite_range v, Set.range_nonempty v, rfl⟩, ?_⟩
    rw [affineSpan_convexHull]
    exact hv.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)
  obtain ⟨c, d, hcd, hQcd⟩ := exists_interval_of_isDPolytope _ hQ
  rw [hPab, hQcd]
  exact interval_boundary_refines a b c d hab hcd

end Grunbaum2003

theorem solution
    (P : Set (Fin 1 → ℝ)) (hP : Grunbaum2003.IsDPolytope P)
    (v : Fin 2 → (Fin 1 → ℝ)) (hv : AffineIndependent ℝ v) :
    Grunbaum2003.BoundaryRefines P (convexHull ℝ (Set.range v)) :=
  Grunbaum2003.boundary_refines_simplex_one_dim P hP v hv

