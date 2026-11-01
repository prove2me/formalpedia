-- Prove2me | solution 1 for Grunbaum2003.auto_GRU_M05_GALE_EQ_gale_combinatorial_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T20:03:24.64763+00:00
-- url     : https://prove2.me/submissions/6284b160-10ab-4b6c-800a-7f21522bd83e

import Definitions.Def_auto_GRU_M05_GALE_EQ_IsDPolytope
import Definitions.Def_auto_GRU_M05_GALE_EQ_PolytopeFace
import Definitions.Def_auto_GRU_M05_GALE_EQ_IsGaleTransform
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.Topology.MetricSpace.Basic

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

namespace GaleEquivalence

/-- Standard basis vector in `Fin m → ℝ`. -/
def stdBasis {m : ℕ} (a : Fin m) (b : Fin m) : ℝ :=
  if b = a then 1 else 0

@[simp]
lemma stdBasis_apply {m : ℕ} (a b : Fin m) :
    stdBasis a b = if b = a then 1 else 0 := rfl

lemma convexHull_image_eq_sum {m n : ℕ} (G : Fin n → (Fin m → ℝ)) (J : Set (Fin n)) :
    convexHull ℝ (G '' J) =
      {x : Fin m → ℝ | ∃ w : Fin n → ℝ,
        (∀ i ∈ J, 0 ≤ w i) ∧ (∀ i ∉ J, w i = 0) ∧
        (∑ i : Fin n, w i = 1) ∧ (∑ i : Fin n, w i • G i = x)} := by
  classical
  set S := {x : Fin m → ℝ | ∃ w : Fin n → ℝ,
    (∀ i ∈ J, 0 ≤ w i) ∧ (∀ i ∉ J, w i = 0) ∧
    (∑ i : Fin n, w i = 1) ∧ (∑ i : Fin n, w i • G i = x)}
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ ?_
    · rintro x ⟨j, hj, rfl⟩
      refine ⟨fun i => if i = j then 1 else 0, ?_, ?_, ?_, ?_⟩
      · intro i _; dsimp only; split_ifs <;> norm_num
      · intro i hi
        have hij : i ≠ j := fun h => hi (h ▸ hj)
        simp [hij]
      · simp
      · simp [ite_smul]
    · intro x hx y hy a b ha hb hab
      rcases hx with ⟨wx, hwx1, hwx2, hwx3, rfl⟩
      rcases hy with ⟨wy, hwy1, hwy2, hwy3, rfl⟩
      refine ⟨fun i => a * wx i + b * wy i, ?_, ?_, ?_, ?_⟩
      · intro i hi
        exact add_nonneg (mul_nonneg ha (hwx1 i hi)) (mul_nonneg hb (hwy1 i hi))
      · intro i hi
        simp [hwx2 i hi, hwy2 i hi]
      · calc ∑ i : Fin n, (a * wx i + b * wy i)
            = a * (∑ i : Fin n, wx i) + b * (∑ i : Fin n, wy i) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          _ = 1 := by rw [hwx3, hwy3]; linarith
      · simp_rw [add_smul, mul_smul]
        rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum]
  · rintro x ⟨w, hw1, hw2, hw3, rfl⟩
    set Jf : Finset (Fin n) := Finset.univ.filter (· ∈ J)
    have hw_sum_Jf : ∑ i ∈ Jf, w i = 1 := by
      rw [← hw3]
      refine Finset.sum_subset (Finset.subset_univ Jf) ?_
      intro i _ hiJf
      have hiJ : i ∉ J := by simpa [Jf] using hiJf
      exact hw2 i hiJ
    have hw_smul_Jf : ∑ i ∈ Jf, w i • G i = ∑ i : Fin n, w i • G i := by
      refine Finset.sum_subset (Finset.subset_univ Jf) ?_
      intro i _ hiJf
      have hiJ : i ∉ J := by simpa [Jf] using hiJf
      simp [hw2 i hiJ]
    rw [← hw_smul_Jf]
    have hcm := Finset.centerMass_mem_convexHull Jf (w := w) (z := G)
      (fun i hi => hw1 i ((Finset.mem_filter.mp hi).2))
      (by linarith)
      (fun i hi => Set.mem_image_of_mem G ((Finset.mem_filter.mp hi).2))
    unfold Finset.centerMass at hcm
    rwa [hw_sum_Jf, inv_one, one_smul] at hcm

/-- Every extreme point of a finite convex hull is an exposed singleton. -/
lemma extremePoints_eq_exposedSingletons {d : ℕ} (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
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

/-- Vertex index subset of a face `F`. -/
def vertIdx {d n : ℕ} (V : Fin n → (Fin d → ℝ)) (F : Set (Fin d → ℝ)) : Set (Fin n) :=
  {i : Fin n | V i ∈ F}

/-- Every exposed face `F` of `P` is the convex hull of its vertices `V '' vertIdx V F`. -/
lemma exposed_eq_convexHull_vertIdx {d n : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    {V : Fin n → (Fin d → ℝ)} (hV : Set.range V = {x | IsExposed ℝ P {x}})
    {F : Set (Fin d → ℝ)} (hF : IsExposed ℝ P F) :
    F = convexHull ℝ (V '' vertIdx V F) := by
  rcases hP.1 with ⟨V0, hV0_fin, _, hP_eq⟩
  have hP_comp : IsCompact P := hP_eq ▸ hV0_fin.isCompact_convexHull ℝ
  have hP_conv : Convex ℝ P := hP_eq ▸ convex_convexHull ℝ V0
  have hF_comp : IsCompact F := hF.isCompact hP_comp
  have hF_conv : Convex ℝ F := hF.convex hP_conv
  have hF_ext_eq : F.extremePoints ℝ = V '' vertIdx V F := by
    rw [hF.isExtreme.extremePoints_eq, extremePoints_eq_exposedSingletons P hP, ← hV]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_image, vertIdx, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hxF, i, rfl⟩
      exact ⟨i, hxF, rfl⟩
    · rintro ⟨i, hiF, rfl⟩
      exact ⟨hiF, i, rfl⟩
  have h_km := closure_convexHull_extremePoints hF_comp hF_conv
  rw [hF_ext_eq] at h_km
  have h_closed : IsClosed (convexHull ℝ (V '' vertIdx V F)) :=
    ((Set.toFinite _).isCompact_convexHull ℝ).isClosed
  rw [h_closed.closure_eq] at h_km
  exact h_km.symm

lemma P_eq_convexHull_range {d n : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    {V : Fin n → (Fin d → ℝ)} (hV : Set.range V = {x | IsExposed ℝ P {x}}) :
    P = convexHull ℝ (Set.range V) := by
  have h := exposed_eq_convexHull_vertIdx hP hV (IsExposed.refl P)
  have h_univ : vertIdx V P = Set.univ := by
    ext i
    simp only [vertIdx, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    have hi : V i ∈ {x | IsExposed ℝ P {x}} := hV ▸ Set.mem_range_self i
    exact Set.singleton_subset_iff.mp hi.subset
  rwa [h_univ, Set.image_univ] at h

lemma vertex_mem_P {d n : ℕ} {P : Set (Fin d → ℝ)}
    {V : Fin n → (Fin d → ℝ)} (hV : Set.range V = {x | IsExposed ℝ P {x}}) (i : Fin n) :
    V i ∈ P := by
  have hi : IsExposed ℝ P {V i} := by
    have : V i ∈ Set.range V := Set.mem_range_self i
    rwa [hV] at this
  exact Set.singleton_subset_iff.mp hi.subset

lemma exposed_singleton_vertex {d n : ℕ} {P : Set (Fin d → ℝ)}
    {V : Fin n → (Fin d → ℝ)} (hV : Set.range V = {x | IsExposed ℝ P {x}}) (i : Fin n) :
    IsExposed ℝ P {V i} := by
  have : V i ∈ Set.range V := Set.mem_range_self i
  rwa [hV] at this

lemma face_le_iff_vertIdx_subset {d n : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    {V : Fin n → (Fin d → ℝ)} (hV : Set.range V = {x | IsExposed ℝ P {x}})
    (F1 F2 : PolytopeFace P) :
    F1 ≤ F2 ↔ vertIdx V F1.val ⊆ vertIdx V F2.val := by
  constructor
  · intro h i hi
    exact h hi
  · intro h
    change F1.val ⊆ F2.val
    rw [exposed_eq_convexHull_vertIdx hP hV F1.property,
      exposed_eq_convexHull_vertIdx hP hV F2.property]
    exact convexHull_mono (Set.image_mono h)

lemma face_eq_iff_vertIdx_eq {d n : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    {V : Fin n → (Fin d → ℝ)} (hV : Set.range V = {x | IsExposed ℝ P {x}})
    (F1 F2 : PolytopeFace P) :
    F1 = F2 ↔ vertIdx V F1.val = vertIdx V F2.val := by
  rw [le_antisymm_iff, face_le_iff_vertIdx_subset hP hV, face_le_iff_vertIdx_subset hP hV,
    Set.Subset.antisymm_iff]

lemma vertIdx_singleton {d n : ℕ} {V : Fin n → (Fin d → ℝ)} (hVinj : Function.Injective V)
    (i : Fin n) :
    vertIdx V {V i} = {i} := by
  ext j
  simp [vertIdx, hVinj.eq_iff]

lemma vertIdx_eq_univ_iff {d n : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    {V : Fin n → (Fin d → ℝ)} (hV : Set.range V = {x | IsExposed ℝ P {x}})
    (F : PolytopeFace P) :
    vertIdx V F.val = Set.univ ↔ F.val = P := by
  constructor
  · intro h
    rw [exposed_eq_convexHull_vertIdx hP hV F.property, h, Set.image_univ,
      ← P_eq_convexHull_range hP hV]
  · intro h
    rw [h]
    ext i
    simp [vertIdx, vertex_mem_P hV i]

/-- Equivalence between vertex-preserving face-poset isomorphisms and matching proper face vertex sets. -/
lemma orderIso_iff_properFace_vertIdx {d n : ℕ}
    {P Q : Set (Fin d → ℝ)} (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    {V W : Fin n → (Fin d → ℝ)}
    (hVinj : Function.Injective V) (hWinj : Function.Injective W)
    (hV : Set.range V = {x | IsExposed ℝ P {x}})
    (hW : Set.range W = {x | IsExposed ℝ Q {x}})
    (θ : Equiv.Perm (Fin n)) :
    (∃ Φ : PolytopeFace P ≃o PolytopeFace Q,
      ∀ (i : Fin n) (F : PolytopeFace P),
        F.val = {V i} → (Φ F).val = {W (θ i)}) ↔
    (∀ I : Set (Fin n),
      (∃ F : PolytopeFace P, F.val ≠ P ∧ vertIdx V F.val = I) ↔
      (∃ F' : PolytopeFace Q, F'.val ≠ Q ∧ vertIdx W F'.val = θ '' I)) := by
  classical
  have h_all_iff_proper :
      (∀ I : Set (Fin n),
        (∃ F : PolytopeFace P, vertIdx V F.val = I) ↔
        (∃ F' : PolytopeFace Q, vertIdx W F'.val = θ '' I)) ↔
      (∀ I : Set (Fin n),
        (∃ F : PolytopeFace P, F.val ≠ P ∧ vertIdx V F.val = I) ↔
        (∃ F' : PolytopeFace Q, F'.val ≠ Q ∧ vertIdx W F'.val = θ '' I)) := by
    constructor
    · intro h I
      by_cases hI : I = Set.univ
      · subst hI
        have hθ_univ : (θ '' (Set.univ : Set (Fin n))) = Set.univ :=
          Set.image_univ.trans θ.surjective.range_eq
        constructor
        · rintro ⟨F, hne, heq⟩
          exact False.elim (hne ((vertIdx_eq_univ_iff hP hV F).mp heq))
        · rintro ⟨F', hne, heq⟩
          rw [hθ_univ] at heq
          exact False.elim (hne ((vertIdx_eq_univ_iff hQ hW F').mp heq))
      · have hθI : θ '' I ≠ Set.univ := by
          intro h_eq
          apply hI
          ext i
          simp only [Set.mem_univ, iff_true]
          have : θ i ∈ θ '' I := h_eq ▸ Set.mem_univ (θ i)
          rcases this with ⟨i', hi', hθ⟩
          exact θ.injective hθ ▸ hi'
        constructor
        · rintro ⟨F, _, rfl⟩
          obtain ⟨F', hF'⟩ := (h (vertIdx V F.val)).mp ⟨F, rfl⟩
          refine ⟨F', ?_, hF'⟩
          exact fun h_eq => hθI (hF'.symm.trans ((vertIdx_eq_univ_iff hQ hW F').mpr h_eq))
        · rintro ⟨F', _, hF'⟩
          obtain ⟨F, hF⟩ := (h I).mpr ⟨F', hF'⟩
          refine ⟨F, ?_, hF⟩
          exact fun h_eq => hI (hF.symm.trans ((vertIdx_eq_univ_iff hP hV F).mpr h_eq))
    · intro h I
      by_cases hI : I = Set.univ
      · subst hI
        have hθ_univ : (θ '' (Set.univ : Set (Fin n))) = Set.univ :=
          Set.image_univ.trans θ.surjective.range_eq
        constructor
        · intro _
          refine ⟨⟨Q, IsExposed.refl Q⟩, ?_⟩
          rw [hθ_univ, vertIdx_eq_univ_iff hQ hW]
        · intro _
          refine ⟨⟨P, IsExposed.refl P⟩, ?_⟩
          rw [vertIdx_eq_univ_iff hP hV]
      · have hθI : θ '' I ≠ Set.univ := by
          intro h_eq
          apply hI
          ext i
          simp only [Set.mem_univ, iff_true]
          have : θ i ∈ θ '' I := h_eq ▸ Set.mem_univ (θ i)
          rcases this with ⟨i', hi', hθ⟩
          exact θ.injective hθ ▸ hi'
        constructor
        · rintro ⟨F, rfl⟩
          have hFP : F.val ≠ P := fun h_eq => hI ((vertIdx_eq_univ_iff hP hV F).mpr h_eq)
          obtain ⟨F', _, hF'⟩ := (h (vertIdx V F.val)).mp ⟨F, hFP, rfl⟩
          exact ⟨F', hF'⟩
        · rintro ⟨F', hF'⟩
          have hF'Q : F'.val ≠ Q :=
            fun h_eq => hθI (hF'.symm.trans ((vertIdx_eq_univ_iff hQ hW F').mpr h_eq))
          obtain ⟨F, _, hF⟩ := (h I).mpr ⟨F', hF'Q, hF'⟩
          exact ⟨F, hF⟩
  rw [← h_all_iff_proper]
  constructor
  · rintro ⟨Φ, hΦ⟩ I
    have h_vert_Φ : ∀ F : PolytopeFace P, vertIdx W (Φ F).val = θ '' vertIdx V F.val := by
      intro F
      ext j
      obtain ⟨i, rfl⟩ := θ.surjective j
      simp only [Set.mem_image, θ.injective.eq_iff, exists_eq_right, vertIdx, Set.mem_setOf_eq]
      let sP : PolytopeFace P := ⟨{V i}, exposed_singleton_vertex hV i⟩
      let sQ : PolytopeFace Q := ⟨{W (θ i)}, exposed_singleton_vertex hW (θ i)⟩
      have hsP_eq : Φ sP = sQ := by
        ext x
        rw [hΦ i sP rfl]
      have h1 : V i ∈ F.val ↔ sP ≤ F := by
        change V i ∈ F.val ↔ {V i} ⊆ F.val
        exact Set.singleton_subset_iff.symm
      have h2 : W (θ i) ∈ (Φ F).val ↔ sQ ≤ Φ F := by
        change W (θ i) ∈ (Φ F).val ↔ {W (θ i)} ⊆ (Φ F).val
        exact Set.singleton_subset_iff.symm
      rw [h1, h2, ← hsP_eq, Φ.le_iff_le]
    constructor
    · rintro ⟨F, rfl⟩
      exact ⟨Φ F, h_vert_Φ F⟩
    · rintro ⟨F', hF'⟩
      refine ⟨Φ.symm F', ?_⟩
      have h_eq := h_vert_Φ (Φ.symm F')
      rw [Φ.apply_symm_apply, hF'] at h_eq
      exact (Set.image_injective.mpr θ.injective) h_eq.symm
  · intro h
    have h_fwd : ∀ F : PolytopeFace P, ∃ F' : PolytopeFace Q, vertIdx W F'.val = θ '' vertIdx V F.val :=
      fun F => (h (vertIdx V F.val)).mp ⟨F, rfl⟩
    have h_bwd : ∀ F' : PolytopeFace Q, ∃ F : PolytopeFace P, vertIdx V F.val = θ.symm '' vertIdx W F'.val := by
      intro F'
      have h_im : θ '' (θ.symm '' vertIdx W F'.val) = vertIdx W F'.val := by
        ext j; simp
      obtain ⟨F, hF⟩ := (h (θ.symm '' vertIdx W F'.val)).mpr ⟨F', h_im.symm⟩
      exact ⟨F, hF⟩
    let toFun : PolytopeFace P → PolytopeFace Q := fun F => Classical.choose (h_fwd F)
    have h_toFun : ∀ F, vertIdx W (toFun F).val = θ '' vertIdx V F.val :=
      fun F => Classical.choose_spec (h_fwd F)
    let invFun : PolytopeFace Q → PolytopeFace P := fun F' => Classical.choose (h_bwd F')
    have h_invFun : ∀ F', vertIdx V (invFun F').val = θ.symm '' vertIdx W F'.val :=
      fun F' => Classical.choose_spec (h_bwd F')
    refine ⟨{
      toFun := toFun
      invFun := invFun
      left_inv := fun F => by
        rw [face_eq_iff_vertIdx_eq hP hV, h_invFun, h_toFun]
        ext i; simp
      right_inv := fun F' => by
        rw [face_eq_iff_vertIdx_eq hQ hW, h_toFun, h_invFun]
        ext j; simp
      map_rel_iff' := fun {F1 F2} => by
        rw [face_le_iff_vertIdx_subset hQ hW, face_le_iff_vertIdx_subset hP hV]
        change vertIdx W (toFun F1).val ⊆ vertIdx W (toFun F2).val ↔
          vertIdx V F1.val ⊆ vertIdx V F2.val
        rw [h_toFun, h_toFun]
        exact Set.image_subset_image_iff θ.injective
    }, ?_⟩
    intro i F hF_eq
    have h_v : vertIdx V F.val = {i} := by
      rw [hF_eq, vertIdx_singleton hVinj]
    have h_w : vertIdx W (toFun F).val = {θ i} := by
      rw [h_toFun F, h_v, Set.image_singleton]
    have h_s : vertIdx W ({W (θ i)} : Set (Fin d → ℝ)) = {θ i} :=
      vertIdx_singleton hWinj (θ i)
    have h_face_eq : toFun F = ⟨{W (θ i)}, exposed_singleton_vertex hW (θ i)⟩ := by
      rw [face_eq_iff_vertIdx_eq hQ hW, h_w, h_s]
    exact congrArg Subtype.val h_face_eq

/-- Proper exposed face vertex-set characterization via affine functionals. -/
lemma properFace_iff_affineEval {d n : ℕ}
    {P : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    {V : Fin n → (Fin d → ℝ)} (hV : Set.range V = {x | IsExposed ℝ P {x}})
    (I : Set (Fin n)) :
    (∃ F : PolytopeFace P, F.val ≠ P ∧ vertIdx V F.val = I) ↔
      Iᶜ.Nonempty ∧ ∃ (u : Fin d → ℝ) (c : ℝ),
        (∀ i ∈ I, (∑ k : Fin d, u k * V i k) + c = 0) ∧
        (∀ i ∈ Iᶜ, 0 < (∑ k : Fin d, u k * V i k) + c) := by
  classical
  constructor
  · rintro ⟨F, hFP, rfl⟩
    have hJc : (vertIdx V F.val)ᶜ.Nonempty := by
      rw [Set.nonempty_compl, Ne.eq_def, vertIdx_eq_univ_iff hP hV]
      exact hFP
    refine ⟨hJc, ?_⟩
    rcases (vertIdx V F.val).eq_empty_or_nonempty with hI_empty | ⟨i0, hi0⟩
    · refine ⟨0, 1, ?_, ?_⟩
      · intro i hi
        rw [hI_empty] at hi
        exact False.elim hi
      · intro i _
        simp
    · have hF_ne : F.val.Nonempty := ⟨V i0, hi0⟩
      obtain ⟨l, hl_eq⟩ := F.property hF_ne
      have h_lin : ∀ x : Fin d → ℝ, (∑ k : Fin d, (- l (stdBasis k)) * x k) = - l x := by
        intro x
        have hx : x = ∑ k : Fin d, x k • stdBasis k := by
          ext k; simp [Finset.sum_apply, stdBasis_apply]
        conv_rhs => rw [hx, map_sum]
        simp_rw [map_smul, smul_eq_mul, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun k _ => by ring)
      refine ⟨fun k => - l (stdBasis k), l (V i0), ?_, ?_⟩
      · intro i hi
        dsimp only
        rw [h_lin]
        have hiF : V i ∈ F.val := hi
        have hi0F : V i0 ∈ F.val := hi0
        rw [hl_eq] at hiF hi0F
        have h1 := hiF.2 (V i0) (vertex_mem_P hV i0)
        have h2 := hi0F.2 (V i) (vertex_mem_P hV i)
        linarith
      · intro i hi_compl
        dsimp only
        rw [h_lin]
        have hi0F : V i0 ∈ F.val := hi0
        have hi_notF : V i ∉ F.val := hi_compl
        rw [hl_eq] at hi0F hi_notF
        have h_le : l (V i) ≤ l (V i0) := hi0F.2 (V i) (vertex_mem_P hV i)
        have h_ne : l (V i) ≠ l (V i0) := by
          intro h_eq
          apply hi_notF
          refine ⟨vertex_mem_P hV i, fun y hy => ?_⟩
          rw [h_eq]
          exact hi0F.2 y hy
        linarith [lt_of_le_of_ne h_le h_ne]
  · rintro ⟨⟨j0, hj0⟩, u, c, hI0, hJc_pos⟩
    rcases I.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩
    · refine ⟨⟨∅, isExposed_empty⟩, ?_, ?_⟩
      · intro h_empty_eq
        rcases hP.1 with ⟨V0, _, ⟨x0, hx0⟩, hP_eq⟩
        have hx0P : x0 ∈ P := hP_eq ▸ subset_convexHull ℝ V0 hx0
        rw [← h_empty_eq] at hx0P
        exact hx0P
      · ext i; simp [vertIdx]
    · let l_lin : (Fin d → ℝ) →ₗ[ℝ] ℝ := {
        toFun := fun x => - ∑ k : Fin d, u k * x k
        map_add' := fun x y => by
          simp_rw [Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring
        map_smul' := fun r x => by
          dsimp only [RingHom.id_apply]
          simp_rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm (u _) r, mul_assoc,
            ← Finset.mul_sum]; ring
      }
      let l : StrongDual ℝ (Fin d → ℝ) := l_lin.toContinuousLinearMap
      have hl_apply : ∀ x : Fin d → ℝ, l x = - ∑ k : Fin d, u k * x k := fun _ => rfl
      let F : PolytopeFace P := ⟨l.toExposed P, ContinuousLinearMap.toExposed.isExposed⟩
      have h_le_c : P ⊆ {y : Fin d → ℝ | l y ≤ c} := by
        rw [P_eq_convexHull_range hP hV]
        refine convexHull_min ?_ ?_
        · rintro y ⟨i, rfl⟩
          change l (V i) ≤ c
          rw [hl_apply]
          by_cases hi : i ∈ I
          · linarith [hI0 i hi]
          · linarith [hJc_pos i hi]
        · intro x hx y hy a b ha hb hab
          change l x ≤ c at hx
          change l y ≤ c at hy
          change l (a • x + b • y) ≤ c
          rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
          have hb_eq : b = 1 - a := by linarith
          subst hb_eq
          nlinarith
      have h_i0_eq : l (V i0) = c := by
        rw [hl_apply]
        linarith [hI0 i0 hi0]
      have h_vert : vertIdx V F.val = I := by
        ext i
        simp only [vertIdx, Set.mem_setOf_eq, F, ContinuousLinearMap.toExposed]
        constructor
        · rintro ⟨_, hmax⟩
          by_contra hi_notI
          have h_lt : l (V i) < c := by
            rw [hl_apply]
            linarith [hJc_pos i hi_notI]
          have h_ge : c ≤ l (V i) := by
            rw [← h_i0_eq]
            exact hmax (V i0) (vertex_mem_P hV i0)
          linarith
        · intro hi
          have h_eq : l (V i) = c := by
            rw [hl_apply]
            linarith [hI0 i hi]
          refine ⟨vertex_mem_P hV i, fun y hy => ?_⟩
          rw [h_eq]
          exact h_le_c hy
      refine ⟨F, ?_, h_vert⟩
      refine fun h_eq => ?_
      have h_univ : I = Set.univ := h_vert.symm.trans ((vertIdx_eq_univ_iff hP hV F).mpr h_eq)
      exact hj0 (h_univ ▸ Set.mem_univ j0)

/-- Orthogonal duality in `EuclideanSpace ℝ (Fin n)` between affine evaluations and Gale combinations. -/
lemma affineEval_iff_gale_sum_zero {d n : ℕ}
    {V : Fin n → (Fin d → ℝ)} {G : Fin n → (Fin (n - d - 1) → ℝ)}
    (hG : IsGaleTransform V G) (b : Fin n → ℝ) :
    (∃ (u : Fin d → ℝ) (c : ℝ), ∀ i : Fin n, b i = (∑ k : Fin d, u k * V i k) + c) ↔
      (∑ i : Fin n, b i • G i = 0) := by
  let e := (EuclideanSpace.equiv (Fin n) ℝ).symm
  have he_ofLp : ∀ (f : Fin n → ℝ) (i : Fin n), (e f).ofLp i = f i := fun _ _ => rfl
  let evalMap : ((Fin d → ℝ) × ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := {
    toFun := fun p => e (fun i => (∑ k : Fin d, p.1 k * V i k) + p.2)
    map_add' := fun p q => by
      ext i
      simp only [PiLp.add_apply, he_ofLp, Prod.fst_add, Prod.snd_add, Pi.add_apply,
        add_mul, Finset.sum_add_distrib]
      ring
    map_smul' := fun r p => by
      ext i
      simp only [PiLp.smul_apply, he_ofLp, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
        smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_add, RingHom.id_apply]
  }
  have hevalMap : ∀ (u : Fin d → ℝ) (c : ℝ) (i : Fin n),
      (evalMap (u, c)).ofLp i = (∑ k : Fin d, u k * V i k) + c := fun _ _ _ => rfl
  set U : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := LinearMap.range evalMap
  have hU_ortho : ∀ a : EuclideanSpace ℝ (Fin n),
      a ∈ Uᗮ ↔ (∑ i : Fin n, a.ofLp i = 0) ∧ (∑ i : Fin n, a.ofLp i • V i = 0) := by
    intro a
    rw [Submodule.mem_orthogonal]
    constructor
    · intro ha
      constructor
      · have h1 := ha (evalMap (0, 1)) ⟨(0, 1), rfl⟩
        rw [PiLp.inner_apply] at h1
        simpa [hevalMap] using h1
      · ext k
        have hk := ha (evalMap (stdBasis k, 0)) ⟨(stdBasis k, 0), rfl⟩
        rw [PiLp.inner_apply] at hk
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        simpa [hevalMap, stdBasis_apply, mul_comm] using hk
    · rintro ⟨ha1, haV⟩ w ⟨⟨u, c⟩, rfl⟩
      rw [PiLp.inner_apply]
      simp only [hevalMap, RCLike.inner_apply, conj_trivial]
      have h_expand : ∑ i : Fin n, a.ofLp i * ((∑ k : Fin d, u k * V i k) + c) =
          (∑ k : Fin d, u k * (∑ i : Fin n, a.ofLp i * V i k)) + c * (∑ i : Fin n, a.ofLp i) := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, mul_comm _ c]
        congr 1
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        refine Finset.sum_congr rfl (fun i _ => by ring)
      rw [h_expand, ha1, mul_zero, add_zero]
      have haV_k : ∀ k : Fin d, ∑ i : Fin n, a.ofLp i * V i k = 0 := by
        intro k
        have := congrFun haV k
        simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
      simp [haV_k]
  have hG_span := hG.2
  have hU_ortho_span : (Uᗮ : Set (EuclideanSpace ℝ (Fin n))) =
      e '' (Submodule.span ℝ (Set.range (fun j : Fin (n - d - 1) => fun i : Fin n => G i j)) :
        Set (Fin n → ℝ)) := by
    rw [hG_span]
    ext a
    constructor
    · intro ha
      refine ⟨a.ofLp, ?_, rfl⟩
      exact (hU_ortho a).mp ha
    · rintro ⟨a0, ha0, rfl⟩
      exact (hU_ortho (e a0)).mpr ha0
  have hb_in_U : (∃ (u : Fin d → ℝ) (c : ℝ), ∀ i : Fin n, b i = (∑ k : Fin d, u k * V i k) + c) ↔
      e b ∈ U := by
    constructor
    · rintro ⟨u, c, hbc⟩
      refine ⟨(u, c), ?_⟩
      ext i
      exact (hbc i).symm
    · rintro ⟨⟨u, c⟩, hbc⟩
      refine ⟨u, c, fun i => ?_⟩
      exact (congrFun (congrArg WithLp.ofLp hbc) i).symm
  rw [hb_in_U, ← U.orthogonal_orthogonal, Submodule.mem_orthogonal]
  constructor
  · intro hb_orth
    ext j
    have hgj_mem : e (fun i => G i j) ∈ Uᗮ := by
      change e (fun i => G i j) ∈ (Uᗮ : Set (EuclideanSpace ℝ (Fin n)))
      rw [hU_ortho_span]
      exact ⟨fun i => G i j, Submodule.subset_span ⟨j, rfl⟩, rfl⟩
    have h_in := hb_orth (e (fun i => G i j)) hgj_mem
    rw [PiLp.inner_apply] at h_in
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    simpa [he_ofLp, RCLike.inner_apply] using h_in
  · intro h_sum a ha
    have ha_mem : a ∈ (Uᗮ : Set (EuclideanSpace ℝ (Fin n))) := ha
    rw [hU_ortho_span] at ha_mem
    rcases ha_mem with ⟨a0, ha0_span, rfl⟩
    rw [PiLp.inner_apply]
    have h_span_zero : ∀ x ∈ Submodule.span ℝ
        (Set.range (fun j : Fin (n - d - 1) => fun i : Fin n => G i j)),
        ∑ i : Fin n, b i * x i = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        rcases hy with ⟨j, rfl⟩
        have hj := congrFun h_sum j
        simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hj
      | zero => simp
      | add x y _ _ ihx ihy =>
        simp_rw [Pi.add_apply, mul_add]
        rw [Finset.sum_add_distrib, ihx, ihy, add_zero]
      | smul r x _ ihx =>
        simp_rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm (b _), mul_assoc]
        rw [← Finset.mul_sum, ihx, mul_zero]
    have h0 := h_span_zero a0 ha0_span
    simpa [he_ofLp, RCLike.inner_apply, mul_comm] using h0

/-- Positive convex combination characterization of `0 ∈ intrinsicInterior ℝ (convexHull ℝ (G '' J))`. -/
lemma zero_mem_intrinsicInterior_convexHull_iff {m n : ℕ}
    (G : Fin n → (Fin m → ℝ)) (J : Set (Fin n)) :
    (0 : Fin m → ℝ) ∈ intrinsicInterior ℝ (convexHull ℝ (G '' J)) ↔
      J.Nonempty ∧ ∃ b : Fin n → ℝ,
        (∀ i ∉ J, b i = 0) ∧ (∀ i ∈ J, 0 < b i) ∧ (∑ i : Fin n, b i • G i = 0) := by
  classical
  set S := convexHull ℝ (G '' J)
  constructor
  · intro h0_ri
    have h0_S : (0 : Fin m → ℝ) ∈ S := intrinsicInterior_subset h0_ri
    have hJ_ne : J.Nonempty := by
      by_contra hJ_emp
      rw [Set.not_nonempty_iff_eq_empty] at hJ_emp
      subst hJ_emp
      simp [S] at h0_ri
    refine ⟨hJ_ne, ?_⟩
    rw [mem_intrinsicInterior] at h0_ri
    rcases h0_ri with ⟨y0, hy0_int, hy0_val⟩
    have h0_aff : (0 : Fin m → ℝ) ∈ affineSpan ℝ S := hy0_val ▸ y0.property
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hy0_int
    rcases hy0_int with ⟨ε, hε_pos, hε_ball⟩
    have h_neg_mem : ∀ j ∈ J, ∃ tj : ℝ, 0 < tj ∧ -tj • G j ∈ S := by
      intro j hj
      set tj : ℝ := ε / (2 * (‖G j‖ + 1))
      have h_denom : 0 < 2 * (‖G j‖ + 1) := by positivity
      have htj_pos : 0 < tj := div_pos hε_pos h_denom
      have hGj_aff : G j ∈ affineSpan ℝ S :=
        subset_affineSpan ℝ S (subset_convexHull ℝ (G '' J) ⟨j, hj, rfl⟩)
      have h_vsub : G j -ᵥ (0 : Fin m → ℝ) ∈ (affineSpan ℝ S).direction :=
        AffineSubspace.vsub_mem_direction hGj_aff h0_aff
      have h_smul : (-tj) • (G j -ᵥ (0 : Fin m → ℝ)) ∈ (affineSpan ℝ S).direction :=
        (affineSpan ℝ S).direction.smul_mem (-tj) h_vsub
      have h_vadd := AffineSubspace.vadd_mem_of_mem_direction h_smul h0_aff
      simp only [vsub_eq_sub, sub_zero, vadd_eq_add, add_zero] at h_vadd
      refine ⟨tj, htj_pos, ?_⟩
      have h_dist : dist (⟨-tj • G j, h_vadd⟩ : affineSpan ℝ S) y0 < ε := by
        change dist (-tj • G j) (y0 : Fin m → ℝ) < ε
        rw [hy0_val, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos htj_pos]
        rw [div_mul_eq_mul_div, div_lt_iff₀ h_denom]
        have h_norm_nonneg : 0 ≤ ‖G j‖ := norm_nonneg _
        nlinarith
      exact hε_ball h_dist
    let Jf : Finset (Fin n) := Finset.univ.filter (· ∈ J)
    have h_ex_w : ∀ j : Fin n, ∃ w : Fin n → ℝ,
        (j ∈ J → (∀ i ∈ J, 0 ≤ w i) ∧ (∀ i ∉ J, w i = 0) ∧
          0 < w j ∧ ∑ i : Fin n, w i • G i = 0) ∧
        (j ∉ J → w = 0) := by
      intro j
      by_cases hj : j ∈ J
      · obtain ⟨tj, htj_pos, h_mem⟩ := h_neg_mem j hj
        unfold S at h_mem
        rw [convexHull_image_eq_sum] at h_mem
        rcases h_mem with ⟨wj, hwj1, hwj2, _, hwj_sum⟩
        refine ⟨fun i => wj i + if i = j then tj else 0, ⟨fun _ => ⟨?_, ?_, ?_, ?_⟩, fun h => False.elim (h hj)⟩⟩
        · intro i hi
          dsimp only
          split_ifs
          · linarith [hwj1 i hi]
          · linarith [hwj1 i hi]
        · intro i hi
          have hij : i ≠ j := fun h => hi (h ▸ hj)
          simp [hwj2 i hi, hij]
        · dsimp only
          rw [if_pos rfl]
          linarith [hwj1 j hj]
        · simp_rw [add_smul, ite_smul, zero_smul]
          rw [Finset.sum_add_distrib, hwj_sum, Finset.sum_ite_eq', if_pos (Finset.mem_univ j),
            neg_smul, neg_add_cancel]
      · exact ⟨0, ⟨fun h => False.elim (hj h), fun _ => rfl⟩⟩
    choose Wf hWf using h_ex_w
    refine ⟨fun i => ∑ j ∈ Jf, Wf j i, ?_, ?_, ?_⟩
    · intro i hi
      refine Finset.sum_eq_zero (fun j hj => ?_)
      have hjJ : j ∈ J := (Finset.mem_filter.mp hj).2
      exact ((hWf j).1 hjJ).2.1 i hi
    · intro i hi
      have hiJf : i ∈ Jf := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      have h_nonneg : ∀ j ∈ Jf, 0 ≤ Wf j i := fun j hj =>
        ((hWf j).1 ((Finset.mem_filter.mp hj).2)).1 i hi
      have h_pos_i : 0 < Wf i i := ((hWf i).1 hi).2.2.1
      exact lt_of_lt_of_le h_pos_i (Finset.single_le_sum h_nonneg hiJf)
    · simp_rw [Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero (fun j hj => ?_)
      have hjJ : j ∈ J := (Finset.mem_filter.mp hj).2
      exact ((hWf j).1 hjJ).2.2.2
  · rintro ⟨⟨j0, hj0⟩, b0, hb0_out, hb0_pos, hb0_sum⟩
    let Jf : Finset (Fin n) := Finset.univ.filter (· ∈ J)
    have hj0_Jf : j0 ∈ Jf := Finset.mem_filter.mpr ⟨Finset.mem_univ j0, hj0⟩
    have hB_pos : 0 < ∑ i : Fin n, b0 i := by
      have h_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ b0 i := by
        intro i _
        by_cases hi : i ∈ J
        · exact (hb0_pos i hi).le
        · rw [hb0_out i hi]
      exact lt_of_lt_of_le (hb0_pos j0 hj0) (Finset.single_le_sum h_nonneg (Finset.mem_univ j0))
    set B : ℝ := ∑ i : Fin n, b0 i
    let b : Fin n → ℝ := fun i => b0 i / B
    have hb_out : ∀ i ∉ J, b i = 0 := fun i hi => by simp [b, hb0_out i hi]
    have hb_pos : ∀ i ∈ J, 0 < b i := fun i hi => div_pos (hb0_pos i hi) hB_pos
    have hb_sum1 : ∑ i : Fin n, b i = 1 := by
      simp_rw [b, div_eq_inv_mul, ← Finset.mul_sum]
      exact inv_mul_cancel₀ (ne_of_gt hB_pos)
    have hb_G : ∑ i : Fin n, b i • G i = 0 := by
      simp_rw [b, div_eq_inv_mul, mul_smul, ← Finset.smul_sum, hb0_sum, smul_zero]
    have h0_S : (0 : Fin m → ℝ) ∈ S := by
      change (0 : Fin m → ℝ) ∈ convexHull ℝ (G '' J)
      rw [convexHull_image_eq_sum]
      exact ⟨b, fun i hi => (hb_pos i hi).le, hb_out, hb_sum1, hb_G⟩
    have h0_aff : (0 : Fin m → ℝ) ∈ affineSpan ℝ S := subset_affineSpan ℝ S h0_S
    let WJ : Submodule ℝ (Fin n → ℝ) := {
      carrier := {c : Fin n → ℝ | ∀ i ∉ J, c i = 0}
      add_mem' := fun {a1 a2} ha hb i hi => by
        change a1 i + a2 i = 0
        rw [ha i hi, hb i hi, add_zero]
      zero_mem' := fun i _ => rfl
      smul_mem' := fun r {a1} ha i hi => by
        change r * a1 i = 0
        rw [ha i hi, mul_zero]
    }
    let T : WJ →ₗ[ℝ] (Fin m → ℝ) := {
      toFun := fun c => ∑ i : Fin n, c.val i • G i
      map_add' := fun c1 c2 => by
        simp_rw [Submodule.coe_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        simp_rw [Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul, mul_smul,
          ← Finset.smul_sum, RingHom.id_apply]
    }
    have h_aff_sub : (affineSpan ℝ S : Set (Fin m → ℝ)) ⊆ LinearMap.range T := by
      unfold S
      rw [affineSpan_convexHull]
      change (affineSpan ℝ (G '' J) : Set (Fin m → ℝ)) ⊆
        ((LinearMap.range T).toAffineSubspace : Set (Fin m → ℝ))
      exact affineSpan_le.mpr (by
        rintro x ⟨j, hj, rfl⟩
        refine ⟨⟨fun i => if i = j then 1 else 0, ?_⟩, ?_⟩
        · intro i hi
          have hij : i ≠ j := fun h => hi (h ▸ hj)
          simp [hij]
        · simp [T, ite_smul])
    obtain ⟨R, hR⟩ := T.rangeRestrict.exists_rightInverse_of_surjective T.range_rangeRestrict
    let mapC : LinearMap.range T →ₗ[ℝ] (Fin n → ℝ) := {
      toFun := fun z => (R z).val - (∑ k : Fin n, (R z).val k) • b
      map_add' := fun z1 z2 => by
        ext i
        simp only [map_add, Submodule.coe_add, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, Finset.sum_add_distrib]
        ring
      map_smul' := fun r z => by
        ext i
        simp only [map_smul, Submodule.coe_smul_of_tower, Pi.sub_apply, Pi.smul_apply,
          smul_eq_mul, ← Finset.mul_sum, RingHom.id_apply]
        ring
    }
    have hmapC_cont : Continuous mapC := mapC.continuous_of_finiteDimensional
    have hJf_ne : Jf.Nonempty := ⟨j0, hj0_Jf⟩
    set β : ℝ := Jf.inf' hJf_ne b
    have hβ_pos : 0 < β := by
      rw [Finset.lt_inf'_iff]
      intro i hi
      exact hb_pos i ((Finset.mem_filter.mp hi).2)
    have h_tendsto := Metric.tendsto_nhds_nhds.mp (hmapC_cont.tendsto 0) β hβ_pos
    rw [map_zero] at h_tendsto
    rcases h_tendsto with ⟨ε, hε_pos, hε_ball⟩
    rw [mem_intrinsicInterior]
    refine ⟨⟨0, h0_aff⟩, ?_, rfl⟩
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
    refine ⟨ε, hε_pos, ?_⟩
    intro z hz_dist
    have hz_range : (z : Fin m → ℝ) ∈ LinearMap.range T := h_aff_sub z.property
    let zT : LinearMap.range T := ⟨z.val, hz_range⟩
    have hzT_dist : dist zT 0 < ε := hz_dist
    have h_norm_lt : ‖mapC zT‖ < β := by
      simpa [dist_zero_right] using hε_ball hzT_dist
    have hzT_mem : zT.val ∈ convexHull ℝ (G '' J) := by
      rw [convexHull_image_eq_sum]
      refine ⟨b + mapC zT, ?_, ?_, ?_, ?_⟩
      · intro i hi
        have hiJf : i ∈ Jf := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
        have hbi_ge : β ≤ b i := Finset.inf'_le b hiJf
        have h_abs : |mapC zT i| < β := lt_of_le_of_lt (norm_le_pi_norm (mapC zT) i) h_norm_lt
        have h_lower : -β < mapC zT i := (abs_lt.mp h_abs).1
        change 0 ≤ b i + mapC zT i
        linarith
      · intro i hi
        have hR_out : (R zT).val i = 0 := (R zT).property i hi
        simp [mapC, hb_out i hi, hR_out]
      · simp only [Pi.add_apply, mapC, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply,
          Pi.smul_apply, smul_eq_mul]
        calc ∑ i : Fin n, (b i + ((R zT).val i - (∑ k : Fin n, (R zT).val k) * b i))
            = (∑ i : Fin n, b i) + (∑ i : Fin n, (R zT).val i) -
                (∑ k : Fin n, (R zT).val k) * (∑ i : Fin n, b i) := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
              ring
          _ = 1 := by rw [hb_sum1]; ring
      · simp only [Pi.add_apply, mapC, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply,
          Pi.smul_apply, smul_eq_mul]
        simp_rw [add_smul, sub_smul, mul_smul]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum,
          hb_G, zero_add, smul_zero, sub_zero]
        have hTR := congrArg Subtype.val (LinearMap.congr_fun hR zT)
        exact hTR
    exact hzT_mem

/-- Gale face criterion: `0 ∈ ri(conv(G '' J))` iff `Jᶜ` is the vertex set of a proper face of `P`. -/
lemma gale_properFace_iff {d n : ℕ}
    {P : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    {V : Fin n → (Fin d → ℝ)} (hV : Set.range V = {x | IsExposed ℝ P {x}})
    {G : Fin n → (Fin (n - d - 1) → ℝ)} (hG : IsGaleTransform V G)
    (J : Set (Fin n)) :
    (0 : Fin (n - d - 1) → ℝ) ∈ intrinsicInterior ℝ (convexHull ℝ (G '' J)) ↔
      ∃ F : PolytopeFace P, F.val ≠ P ∧ vertIdx V F.val = Jᶜ := by
  classical
  rw [properFace_iff_affineEval hP hV Jᶜ, compl_compl,
    zero_mem_intrinsicInterior_convexHull_iff G J]
  refine and_congr_right (fun _ => ?_)
  constructor
  · rintro ⟨b, hb_out, hb_pos, hb_sum⟩
    obtain ⟨u, c, huc⟩ := (affineEval_iff_gale_sum_zero hG b).mpr hb_sum
    refine ⟨u, c, ?_, ?_⟩
    · intro i hi
      have h0 : b i = 0 := hb_out i hi
      linarith [huc i]
    · intro i hi
      have hpos : 0 < b i := hb_pos i hi
      linarith [huc i]
  · rintro ⟨u, c, hI0, hJ_pos⟩
    refine ⟨fun i => (∑ k : Fin d, u k * V i k) + c, ?_, ?_, ?_⟩
    · intro i hi
      exact hI0 i hi
    · intro i hi
      exact hJ_pos i hi
    · exact (affineEval_iff_gale_sum_zero hG _).mp ⟨u, c, fun _ => rfl⟩

end GaleEquivalence

open GaleEquivalence in
theorem auto_GRU_M05_GALE_EQ_gale_combinatorial_equivalence (d n : ℕ)
    (P Q : Set (Fin d → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (V W : Fin n → (Fin d → ℝ))
    (hVinj : Function.Injective V) (hWinj : Function.Injective W)
    (hV : Set.range V = {x | IsExposed ℝ P {x}})
    (hW : Set.range W = {x | IsExposed ℝ Q {x}})
    (G H : Fin n → (Fin (n - d - 1) → ℝ))
    (hG : IsGaleTransform V G) (hH : IsGaleTransform W H)
    (θ : Equiv.Perm (Fin n)) :
    (∃ Φ : PolytopeFace P ≃o PolytopeFace Q,
      ∀ (i : Fin n) (F : PolytopeFace P),
        F.val = {V i} → (Φ F).val = {W (θ i)}) ↔
    (∀ J : Set (Fin n),
      (0 : Fin (n - d - 1) → ℝ) ∈ intrinsicInterior ℝ (convexHull ℝ (G '' J)) ↔
      (0 : Fin (n - d - 1) → ℝ) ∈
        intrinsicInterior ℝ (convexHull ℝ (H '' (θ '' J)))) := by
  rw [orderIso_iff_properFace_vertIdx hP hQ hVinj hWinj hV hW θ]
  constructor
  · intro h J
    have hθ_compl : (θ '' J)ᶜ = θ '' (Jᶜ) := (Set.image_compl_eq θ.bijective).symm
    rw [gale_properFace_iff hP hV hG J, gale_properFace_iff hQ hW hH (θ '' J), hθ_compl]
    exact h (Jᶜ)
  · intro h I
    have hθ_compl : (θ '' (Iᶜ))ᶜ = θ '' I := by
      rw [← Set.image_compl_eq θ.bijective, compl_compl]
    have hJ := h (Iᶜ)
    rw [gale_properFace_iff hP hV hG (Iᶜ), gale_properFace_iff hQ hW hH (θ '' (Iᶜ)),
      compl_compl, hθ_compl] at hJ
    exact hJ

end Grunbaum2003

theorem solution :
    ∀ (d n : ℕ)
    (P Q : Set (Fin d → ℝ)) (_hP : Grunbaum2003.IsDPolytope P) (_hQ : Grunbaum2003.IsDPolytope Q)
    (V W : Fin n → (Fin d → ℝ))
    (_hVinj : Function.Injective V) (_hWinj : Function.Injective W)
    (_hV : Set.range V = {x | IsExposed ℝ P {x}})
    (_hW : Set.range W = {x | IsExposed ℝ Q {x}})
    (G H : Fin n → (Fin (n - d - 1) → ℝ))
    (_hG : Grunbaum2003.IsGaleTransform V G) (_hH : Grunbaum2003.IsGaleTransform W H)
    (θ : Equiv.Perm (Fin n)),
    (∃ Φ : Grunbaum2003.PolytopeFace P ≃o Grunbaum2003.PolytopeFace Q,
      ∀ (i : Fin n) (F : Grunbaum2003.PolytopeFace P),
        F.val = {V i} → (Φ F).val = {W (θ i)}) ↔
    (∀ J : Set (Fin n),
      (0 : Fin (n - d - 1) → ℝ) ∈ intrinsicInterior ℝ (convexHull ℝ (G '' J)) ↔
      (0 : Fin (n - d - 1) → ℝ) ∈
        intrinsicInterior ℝ (convexHull ℝ (H '' (θ '' J)))) :=
  Grunbaum2003.auto_GRU_M05_GALE_EQ_gale_combinatorial_equivalence
