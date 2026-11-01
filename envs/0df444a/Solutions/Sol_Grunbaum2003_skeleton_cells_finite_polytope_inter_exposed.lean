-- Prove2me | solution 1 for Grunbaum2003.skeleton_cells_finite_polytope_inter_exposed
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T22:17:24.316261+00:00
-- url     : https://prove2.me/submissions/d92b9e9c-3f2f-4419-92df-43495bd9d33c

import Definitions.Def_Grunbaum2003_IsPolytope
import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_SkeletonFace
import Definitions.Def_Grunbaum2003_skeletonCarrier
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

lemma extremePoints_eq_exposedSingletons_sc {d : ℕ} (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    P.extremePoints ℝ = {x : Fin d → ℝ | IsExposed ℝ P {x}} := by
  classical
  rcases hP.1 with ⟨V0, hV0_fin, _, hP_eq⟩
  apply Set.Subset.antisymm
  · intro x hx
    simp only [Set.mem_setOf_eq]
    have hx_in_P : x ∈ P := extremePoints_subset hx
    have hx_ext : IsExtreme ℝ P {x} := isExtreme_singleton.mpr hx
    have hx_not_in : x ∉ convexHull ℝ (V0 \ {x}) := by
      intro hx_in
      have h_sub : convexHull ℝ (V0 \ {x}) ⊆ P := by
        rw [hP_eq]
        exact convexHull_mono Set.diff_subset
      have hx_ext' : IsExtreme ℝ (convexHull ℝ (V0 \ {x})) {x} :=
        hx_ext.mono h_sub (Set.singleton_subset_iff.mpr hx_in)
      have hx_ep : x ∈ (convexHull ℝ (V0 \ {x})).extremePoints ℝ :=
        isExtreme_singleton.mp hx_ext'
      have hx_diff : x ∈ V0 \ {x} := extremePoints_convexHull_subset hx_ep
      exact hx_diff.2 rfl
    have hC_conv : Convex ℝ (convexHull ℝ (V0 \ {x})) := convex_convexHull ℝ _
    have hC_closed : IsClosed (convexHull ℝ (V0 \ {x})) :=
      ((hV0_fin.diff).isCompact_convexHull ℝ).isClosed
    obtain ⟨l, u, hlu, hux⟩ := geometric_hahn_banach_closed_point hC_conv hC_closed hx_not_in
    intro _
    refine ⟨l, ?_⟩
    apply Set.Subset.antisymm
    · rintro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      refine ⟨hx_in_P, ?_⟩
      have h_le : P ⊆ {z : Fin d → ℝ | l z ≤ l x} := by
        rw [hP_eq]
        refine convexHull_min ?_ ?_
        · intro s hs
          change l s ≤ l x
          by_cases hsx : s = x
          · rw [hsx]
          · have hs_diff : s ∈ V0 \ {x} := ⟨hs, hsx⟩
            exact le_of_lt ((hlu s (subset_convexHull ℝ _ hs_diff)).trans hux)
        · intro z1 hz1 z2 hz2 a b ha hb hab
          change l z1 ≤ l x at hz1
          change l z2 ≤ l x at hz2
          change l (a • z1 + b • z2) ≤ l x
          rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
          have hb_eq : b = 1 - a := by linarith
          subst hb_eq
          nlinarith
      intro z hz
      exact h_le hz
    · rintro y ⟨hyP, hymax⟩
      rw [Set.mem_singleton_iff]
      have hly : l x ≤ l y := hymax x hx_in_P
      rw [hP_eq] at hyP
      let Vfin := hV0_fin.toFinset
      have hVfin : (Vfin : Set (Fin d → ℝ)) = V0 := hV0_fin.coe_toFinset
      rw [← hVfin] at hyP
      obtain ⟨w, hw0, hw1, rfl⟩ := Finset.mem_convexHull'.mp hyP
      have h_sum_nonneg : ∀ s ∈ Vfin, 0 ≤ w s * (l x - l s) := by
        intro s hs
        refine mul_nonneg (hw0 s hs) ?_
        by_cases hsx : s = x
        · subst hsx; linarith
        · have hs_diff : s ∈ V0 \ {x} := ⟨hV0_fin.mem_toFinset.mp hs, hsx⟩
          have hls := hlu s (subset_convexHull ℝ _ hs_diff)
          linarith
      have h_sum_le : ∑ s ∈ Vfin, w s * (l x - l s) ≤ 0 := by
        have h_eq : ∑ s ∈ Vfin, w s * (l x - l s) = l x - l (∑ s ∈ Vfin, w s • s) := by
          rw [map_sum]
          simp_rw [map_smul, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
            hw1, one_mul]
        linarith
      have h_all_zero : ∀ s ∈ Vfin, w s * (l x - l s) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg h_sum_nonneg).mp
          (le_antisymm h_sum_le (Finset.sum_nonneg h_sum_nonneg))
      have hw_zero_of_ne : ∀ s ∈ Vfin, s ≠ x → w s = 0 := by
        intro s hs hsx
        have hs_diff : s ∈ V0 \ {x} := ⟨hV0_fin.mem_toFinset.mp hs, hsx⟩
        have hls := (hlu s (subset_convexHull ℝ _ hs_diff)).trans hux
        have h_z := h_all_zero s hs
        rcases mul_eq_zero.mp h_z with hw_z | hl_z
        · exact hw_z
        · linarith
      calc ∑ s ∈ Vfin, w s • s
          = ∑ s ∈ Vfin, w s • x := by
            refine Finset.sum_congr rfl (fun s hs => ?_)
            by_cases hsx : s = x
            · subst hsx; rfl
            · simp [hw_zero_of_ne s hs hsx]
        _ = (∑ s ∈ Vfin, w s) • x := (Finset.sum_smul).symm
        _ = x := by rw [hw1, one_smul]
  · intro x hx
    exact exposedPoints_subset_extremePoints (mem_exposedPoints_iff_exposed_singleton.mpr hx)

theorem isExposed_inter_of_isExposed {d : ℕ} {P F G : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ P F) (hG : IsExposed ℝ P G) :
    IsExposed ℝ F (F ∩ G) := by
  rintro ⟨x₀, hx₀F, hx₀G⟩
  obtain ⟨l, hlG⟩ := hG ⟨x₀, hx₀G⟩
  refine ⟨l, ?_⟩
  apply Set.Subset.antisymm
  · rintro x ⟨hxF, hxG⟩
    have hxG' := hxG
    rw [hlG] at hxG'
    exact ⟨hxF, fun y hyF => hxG'.2 y (hF.subset hyF)⟩
  · rintro x ⟨hxF, hxmax⟩
    refine ⟨hxF, ?_⟩
    have hx₀G' := hx₀G
    rw [hlG] at hx₀G' ⊢
    refine ⟨hF.subset hxF, fun y hyP => ?_⟩
    exact (hx₀G'.2 y hyP).trans (hxmax x₀ hx₀F)

/-- Grünbaum (2003), §11.1 (pp. 199–204): in the ambient space `ℝ^d`, the carrier of the
`k`-skeleton embeds homeomorphically into `ℝ^d`, and the family `C` of `k`-skeleton face sets
is finite, consists of `∅` and polytopes, satisfies the mutual exposed-intersection condition,
and is order-isomorphic to `SkeletonFace P k`. -/
theorem skeleton_cells_finite_polytope_inter_exposed (d k : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    (∃ S : Set (Fin d → ℝ), Nonempty ((skeletonCarrier P k) ≃ₜ S)) ∧
    (Set.range (fun F : SkeletonFace P k => F.val.val)).Finite ∧
    (∀ F ∈ Set.range (fun F : SkeletonFace P k => F.val.val), F = ∅ ∨ IsPolytope F) ∧
    (∀ F ∈ Set.range (fun F : SkeletonFace P k => F.val.val),
      ∀ G ∈ Set.range (fun F : SkeletonFace P k => F.val.val),
        IsExposed ℝ F (F ∩ G) ∧ IsExposed ℝ G (F ∩ G)) ∧
    Nonempty (SkeletonFace P k ≃o Set.range (fun F : SkeletonFace P k => F.val.val)) := by
  rcases hP.1 with ⟨V0, hV0_fin, _, hP_eq⟩
  have hExtEq : P.extremePoints ℝ = {x : Fin d → ℝ | IsExposed ℝ P {x}} :=
    extremePoints_eq_exposedSingletons_sc P hP
  have hVertFin : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite := by
    rw [← hExtEq, hP_eq]
    exact hV0_fin.subset extremePoints_convexHull_subset
  have hFaceHull : ∀ F : PolytopeFace P,
      F.val = convexHull ℝ (F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}) := by
    intro F
    have hP_comp : IsCompact P := hP_eq ▸ hV0_fin.isCompact_convexHull ℝ
    have hP_conv : Convex ℝ P := hP_eq ▸ convex_convexHull ℝ V0
    have hF_comp : IsCompact F.val := F.property.isCompact hP_comp
    have hF_conv : Convex ℝ F.val := F.property.convex hP_conv
    have hF_ext : F.val.extremePoints ℝ = F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} := by
      rw [F.property.isExtreme.extremePoints_eq, ← hExtEq]
    have h_km := closure_convexHull_extremePoints hF_comp hF_conv
    rw [hF_ext] at h_km
    have h_closed : IsClosed (convexHull ℝ (F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) :=
      ((hVertFin.subset Set.inter_subset_right).isCompact_convexHull ℝ).isClosed
    rw [h_closed.closure_eq] at h_km
    exact h_km.symm
  refine ⟨⟨skeletonCarrier P k, ⟨Homeomorph.refl _⟩⟩, ?_, ?_, ?_, ?_⟩
  · refine (hVertFin.powerset.image (convexHull ℝ)).subset ?_
    rintro _ ⟨F, rfl⟩
    exact ⟨F.val.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}},
      Set.inter_subset_right, (hFaceHull F.val).symm⟩
  · rintro _ ⟨F, rfl⟩
    rcases F.val.val.eq_empty_or_nonempty with hEmp | hNe
    · exact Or.inl hEmp
    · right
      have hSubNe : (F.val.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}).Nonempty := by
        by_contra hNotNe
        rw [Set.not_nonempty_iff_eq_empty] at hNotNe
        have hEmptyHull : F.val.val = ∅ := by
          rw [hFaceHull F.val, hNotNe, convexHull_empty]
        exact hNe.ne_empty hEmptyHull
      exact ⟨F.val.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}},
        hVertFin.subset Set.inter_subset_right, hSubNe, hFaceHull F.val⟩
  · rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩
    refine ⟨isExposed_inter_of_isExposed F.val.2 G.val.2, ?_⟩
    rw [Set.inter_comm]
    exact isExposed_inter_of_isExposed G.val.2 F.val.2
  · let toFun : SkeletonFace P k → Set.range (fun F : SkeletonFace P k => F.val.val) :=
      fun F => ⟨F.val.val, F, rfl⟩
    have hInj : Function.Injective toFun := by
      intro F₁ F₂ h
      exact Subtype.ext (Subtype.ext
        (congr_arg (fun x : Set.range (fun F : SkeletonFace P k => F.val.val) => x.val) h))
    have hSurj : Function.Surjective toFun := by
      rintro ⟨_, F, rfl⟩
      exact ⟨F, rfl⟩
    exact ⟨{
      toEquiv := Equiv.ofBijective toFun ⟨hInj, hSurj⟩
      map_rel_iff' := by
        intro F₁ F₂
        rfl
    }⟩

end Grunbaum2003

theorem solution (d k : ℕ)
    (P : Set (Fin d → ℝ)) (hP : Grunbaum2003.IsDPolytope P) :
    (∃ S : Set (Fin d → ℝ), Nonempty ((Grunbaum2003.skeletonCarrier P k) ≃ₜ S)) ∧
    (Set.range (fun F : Grunbaum2003.SkeletonFace P k => F.val.val)).Finite ∧
    (∀ F ∈ Set.range (fun F : Grunbaum2003.SkeletonFace P k => F.val.val),
      F = ∅ ∨ Grunbaum2003.IsPolytope F) ∧
    (∀ F ∈ Set.range (fun F : Grunbaum2003.SkeletonFace P k => F.val.val),
      ∀ G ∈ Set.range (fun F : Grunbaum2003.SkeletonFace P k => F.val.val),
        IsExposed ℝ F (F ∩ G) ∧ IsExposed ℝ G (F ∩ G)) ∧
    Nonempty (Grunbaum2003.SkeletonFace P k ≃o
      Set.range (fun F : Grunbaum2003.SkeletonFace P k => F.val.val)) :=
  Grunbaum2003.skeleton_cells_finite_polytope_inter_exposed d k P hP
