-- Prove2me | solution 1 for Grunbaum2003.skeleton_orderIso_extends_of_downSet_image
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T22:17:17.056192+00:00
-- url     : https://prove2.me/submissions/156e8274-1b2d-46b4-ac81-81ca96fff194

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SkeletonFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

lemma extremePoints_eq_exposedSingletons_sk {d : ℕ} (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
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

theorem polytopeFace_le_iff_forall_skeletonFace (d k : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (F₁ F₂ : PolytopeFace P) :
    F₁ ≤ F₂ ↔ ∀ S : SkeletonFace P k, S.val ≤ F₁ → S.val ≤ F₂ := by
  constructor
  · intro hle S hS
    exact le_trans hS hle
  · intro hS
    rcases hP.1 with ⟨V0, hV0_fin, _, hP_eq⟩
    have hExtEq : P.extremePoints ℝ = {x : Fin d → ℝ | IsExposed ℝ P {x}} :=
      extremePoints_eq_exposedSingletons_sk P hP
    have hVertFin : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite := by
      rw [← hExtEq, hP_eq]
      exact hV0_fin.subset extremePoints_convexHull_subset
    have hP_comp : IsCompact P := hP_eq ▸ hV0_fin.isCompact_convexHull ℝ
    have hP_conv : Convex ℝ P := hP_eq ▸ convex_convexHull ℝ V0
    have hF1_comp : IsCompact F₁.val := F₁.property.isCompact hP_comp
    have hF1_conv : Convex ℝ F₁.val := F₁.property.convex hP_conv
    have hF2_conv : Convex ℝ F₂.val := F₂.property.convex hP_conv
    have hF1_ext : F₁.val.extremePoints ℝ = F₁.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} := by
      rw [F₁.property.isExtreme.extremePoints_eq, ← hExtEq]
    have h_km := closure_convexHull_extremePoints hF1_comp hF1_conv
    rw [hF1_ext] at h_km
    have h_closed : IsClosed (convexHull ℝ (F₁.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) :=
      ((hVertFin.subset Set.inter_subset_right).isCompact_convexHull ℝ).isClosed
    rw [h_closed.closure_eq] at h_km
    change F₁.val ⊆ F₂.val
    rw [← h_km]
    refine convexHull_min ?_ hF2_conv
    rintro v ⟨hvF1, hv_exp⟩
    have hv_dim : Module.finrank ℝ (affineSpan ℝ ({v} : Set (Fin d → ℝ))).direction ≤ k := by
      rw [direction_affineSpan, vectorSpan_singleton, finrank_bot]
      exact Nat.zero_le k
    let Sv : SkeletonFace P k := ⟨⟨{v}, hv_exp⟩, Or.inr hv_dim⟩
    have hSv1 : Sv.val ≤ F₁ := Set.singleton_subset_iff.mpr hvF1
    have hSv2 : Sv.val ≤ F₂ := hS Sv hSv1
    exact Set.singleton_subset_iff.mp hSv2

/-- An order isomorphism of `k`-skeletons extends to an order isomorphism of the full
face lattices whenever the `k`-skeleton down-sets of faces correspond under `φ`. -/
theorem skeleton_orderIso_extends_of_downSet_image (d e k : ℕ)
    (P : Set (Fin d → ℝ)) (Q : Set (Fin e → ℝ))
    (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (φ : SkeletonFace P k ≃o SkeletonFace Q k)
    (hFwd : ∀ F : PolytopeFace P, ∃ G : PolytopeFace Q,
      ∀ T : SkeletonFace Q k, T.val ≤ G ↔ (φ.symm T).val ≤ F)
    (hBwd : ∀ G : PolytopeFace Q, ∃ F : PolytopeFace P,
      ∀ S : SkeletonFace P k, S.val ≤ F ↔ (φ S).val ≤ G) :
    ∃ Φ : PolytopeFace P ≃o PolytopeFace Q,
      ∀ F : SkeletonFace P k, Φ F.val = (φ F).val := by
  classical
  let toFun : PolytopeFace P → PolytopeFace Q := fun F => Classical.choose (hFwd F)
  have htoFun : ∀ (F : PolytopeFace P) (T : SkeletonFace Q k),
      T.val ≤ toFun F ↔ (φ.symm T).val ≤ F :=
    fun F => Classical.choose_spec (hFwd F)
  let invFun : PolytopeFace Q → PolytopeFace P := fun G => Classical.choose (hBwd G)
  have hinvFun : ∀ (G : PolytopeFace Q) (S : SkeletonFace P k),
      S.val ≤ invFun G ↔ (φ S).val ≤ G :=
    fun G => Classical.choose_spec (hBwd G)
  have hLeft : Function.LeftInverse invFun toFun := by
    intro F
    apply le_antisymm
    · rw [polytopeFace_le_iff_forall_skeletonFace d k P hP]
      intro S hS
      rw [hinvFun (toFun F) S, htoFun F (φ S), OrderIso.symm_apply_apply] at hS
      exact hS
    · rw [polytopeFace_le_iff_forall_skeletonFace d k P hP]
      intro S hS
      rw [hinvFun (toFun F) S, htoFun F (φ S), OrderIso.symm_apply_apply]
      exact hS
  have hRight : Function.RightInverse invFun toFun := by
    intro G
    apply le_antisymm
    · rw [polytopeFace_le_iff_forall_skeletonFace e k Q hQ]
      intro T hT
      rw [htoFun (invFun G) T, hinvFun G (φ.symm T), OrderIso.apply_symm_apply] at hT
      exact hT
    · rw [polytopeFace_le_iff_forall_skeletonFace e k Q hQ]
      intro T hT
      rw [htoFun (invFun G) T, hinvFun G (φ.symm T), OrderIso.apply_symm_apply]
      exact hT
  refine ⟨{
    toFun := toFun
    invFun := invFun
    left_inv := hLeft
    right_inv := hRight
    map_rel_iff' := by
      intro F₁ F₂
      rw [polytopeFace_le_iff_forall_skeletonFace e k Q hQ,
        polytopeFace_le_iff_forall_skeletonFace d k P hP]
      constructor
      · intro h S hS
        have h1 : (φ.symm (φ S)).val ≤ F₁ := by simpa using hS
        have h2 := h (φ S) ((htoFun F₁ (φ S)).mpr h1)
        have h3 := (htoFun F₂ (φ S)).mp h2
        simpa using h3
      · intro h T hT
        have h1 := (htoFun F₁ T).mp hT
        have h2 := h (φ.symm T) h1
        exact (htoFun F₂ T).mpr h2
  }, ?_⟩
  intro F
  apply le_antisymm
  · rw [polytopeFace_le_iff_forall_skeletonFace e k Q hQ]
    intro T hT
    have h1 : (φ.symm T).val ≤ F.val := (htoFun F.val T).mp hT
    have h2 : φ.symm T ≤ F := h1
    have h3 : T ≤ φ F := by
      rw [← φ.map_rel_iff] at h2
      simpa using h2
    exact h3
  · rw [polytopeFace_le_iff_forall_skeletonFace e k Q hQ]
    intro T hT
    have h1 : T ≤ φ F := hT
    have h2 : φ.symm T ≤ F := by
      rw [← φ.map_rel_iff]
      simpa using h1
    exact (htoFun F.val T).mpr h2

end Grunbaum2003

theorem solution (d e k : ℕ)
    (P : Set (Fin d → ℝ)) (Q : Set (Fin e → ℝ))
    (hP : Grunbaum2003.IsDPolytope P) (hQ : Grunbaum2003.IsDPolytope Q)
    (φ : Grunbaum2003.SkeletonFace P k ≃o Grunbaum2003.SkeletonFace Q k)
    (hFwd : ∀ F : Grunbaum2003.PolytopeFace P, ∃ G : Grunbaum2003.PolytopeFace Q,
      ∀ T : Grunbaum2003.SkeletonFace Q k, T.val ≤ G ↔ (φ.symm T).val ≤ F)
    (hBwd : ∀ G : Grunbaum2003.PolytopeFace Q, ∃ F : Grunbaum2003.PolytopeFace P,
      ∀ S : Grunbaum2003.SkeletonFace P k, S.val ≤ F ↔ (φ S).val ≤ G) :
    ∃ Φ : Grunbaum2003.PolytopeFace P ≃o Grunbaum2003.PolytopeFace Q,
      ∀ F : Grunbaum2003.SkeletonFace P k, Φ F.val = (φ F).val :=
  Grunbaum2003.skeleton_orderIso_extends_of_downSet_image d e k P Q hP hQ φ hFwd hBwd
