-- Prove2me | solution 1 for Grunbaum2003.neighborly_subpolytope_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T20:31:53.786206+00:00
-- url     : https://prove2.me/submissions/90db1c94-5caa-4992-b9da-4f6313f8db50

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_IsKNeighborly
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.LinearMap

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

namespace ShemerRigidity

/-- Standard basis vector in `Fin d → ℝ`. -/
def stdBasis {d : ℕ} (a : Fin d) (b : Fin d) : ℝ :=
  if b = a then 1 else 0

@[simp]
lemma stdBasis_apply {d : ℕ} (a b : Fin d) :
    stdBasis a b = if b = a then 1 else 0 := rfl

/-- A subset `S ⊆ I` of vertex indices is affine-exposed in `I` with respect to `V` if there is
an affine functional on `Fin d → ℝ` vanishing on `V '' S` and strictly positive on `V '' (I \ S)`. -/
def IsAffineExposed {d m : ℕ} (V : Fin m → (Fin d → ℝ)) (I S : Finset (Fin m)) : Prop :=
  S ⊆ I ∧ ∃ (u : Fin d → ℝ) (c : ℝ),
    (∀ i ∈ S, (∑ k : Fin d, u k * V i k) + c = 0) ∧
    (∀ j ∈ I \ S, 0 < (∑ k : Fin d, u k * V j k) + c)

lemma isAffineExposed_empty {d m : ℕ} (V : Fin m → (Fin d → ℝ)) (I : Finset (Fin m)) :
    IsAffineExposed V I ∅ := by
  refine ⟨Finset.empty_subset I, 0, 1, ?_, ?_⟩
  · intro i hi
    exact False.elim (Finset.notMem_empty i hi)
  · intro j _
    simp

lemma isAffineExposed_self {d m : ℕ} (V : Fin m → (Fin d → ℝ)) (I : Finset (Fin m)) :
    IsAffineExposed V I I := by
  refine ⟨Finset.Subset.refl I, 0, 0, ?_, ?_⟩
  · intro i _
    simp
  · intro j hj
    rw [Finset.sdiff_self] at hj
    exact False.elim (Finset.notMem_empty j hj)

lemma IsAffineExposed.mono {d m : ℕ} {V : Fin m → (Fin d → ℝ)} {I I' S : Finset (Fin m)}
    (h : IsAffineExposed V I S) (hSI' : S ⊆ I') (hI'I : I' ⊆ I) :
    IsAffineExposed V I' S := by
  rcases h with ⟨_, u, c, hS0, hpos⟩
  refine ⟨hSI', u, c, hS0, ?_⟩
  intro j hj
  rw [Finset.mem_sdiff] at hj
  exact hpos j (Finset.mem_sdiff.mpr ⟨hI'I hj.1, hj.2⟩)

lemma vertex_mem_P {d m : ℕ} {P : Set (Fin d → ℝ)}
    {V : Fin m → (Fin d → ℝ)} (hV : Set.range V = {x | IsExposed ℝ P {x}}) (i : Fin m) :
    V i ∈ P := by
  have hi : IsExposed ℝ P {V i} := by
    have : V i ∈ Set.range V := Set.mem_range_self i
    rwa [hV] at this
  exact Set.singleton_subset_iff.mp hi.subset

lemma exposed_singleton_vertex {d m : ℕ} {P : Set (Fin d → ℝ)}
    {V : Fin m → (Fin d → ℝ)} (hV : Set.range V = {x | IsExposed ℝ P {x}}) (i : Fin m) :
    IsExposed ℝ P {V i} := by
  have : V i ∈ Set.range V := Set.mem_range_self i
  rwa [hV] at this

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

/-- If `{x}` is exposed in `B`, `A ⊆ B`, and `x ∈ A`, then `{x}` is exposed in `A`. -/
lemma isExposed_singleton_mono {d : ℕ} {A B : Set (Fin d → ℝ)} {x : Fin d → ℝ}
    (hB : IsExposed ℝ B {x}) (hAB : A ⊆ B) (hxA : x ∈ A) :
    IsExposed ℝ A {x} := by
  intro _
  obtain ⟨l, hl⟩ := hB ⟨x, Set.mem_singleton x⟩
  refine ⟨l, ?_⟩
  apply Set.Subset.antisymm
  · rintro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hxB_exp : x ∈ {z ∈ B | ∀ w ∈ B, l w ≤ l z} := by
      rw [← hl]
      exact Set.mem_singleton x
    exact ⟨hxA, fun w hw => hxB_exp.2 w (hAB hw)⟩
  · rintro y ⟨hyA, hymax⟩
    have hxB_exp : x ∈ {z ∈ B | ∀ w ∈ B, l w ≤ l z} := by
      rw [← hl]
      exact Set.mem_singleton x
    have h2 : l x ≤ l y := hymax x hxA
    have hyB_exp : y ∈ {z ∈ B | ∀ w ∈ B, l w ≤ l z} := by
      refine ⟨hAB hyA, fun w hw => ?_⟩
      exact (hxB_exp.2 w hw).trans h2
    rw [← hl] at hyB_exp
    exact hyB_exp

lemma P_eq_convexHull_range {d m : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    {V : Fin m → (Fin d → ℝ)} (hV : Set.range V = {x | IsExposed ℝ P {x}}) :
    P = convexHull ℝ (Set.range V) := by
  rcases hP.1 with ⟨V0, hV0_fin, _, hP_eq⟩
  have hP_comp : IsCompact P := hP_eq ▸ hV0_fin.isCompact_convexHull ℝ
  have hP_conv : Convex ℝ P := hP_eq ▸ convex_convexHull ℝ V0
  have h_km := closure_convexHull_extremePoints hP_comp hP_conv
  rw [extremePoints_eq_exposedSingletons P hP, ← hV] at h_km
  have h_closed : IsClosed (convexHull ℝ (Set.range V)) :=
    ((Set.finite_range V).isCompact_convexHull ℝ).isClosed
  rw [h_closed.closure_eq] at h_km
  exact h_km.symm

lemma subpolytope_subset_P {d m : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    {V : Fin m → (Fin d → ℝ)} (hV : Set.range V = {x | IsExposed ℝ P {x}})
    (I : Set (Fin m)) :
    convexHull ℝ (V '' I) ⊆ P := by
  rw [P_eq_convexHull_range hP hV]
  exact convexHull_mono (Set.image_subset_range V I)

lemma exposed_singleton_subpolytope {d m : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    {V : Fin m → (Fin d → ℝ)} (hV : Set.range V = {x | IsExposed ℝ P {x}})
    {I : Set (Fin m)} {i : Fin m} (hi : i ∈ I) :
    IsExposed ℝ (convexHull ℝ (V '' I)) {V i} :=
  isExposed_singleton_mono (exposed_singleton_vertex hV i)
    (subpolytope_subset_P hP hV I)
    (subset_convexHull ℝ (V '' I) ⟨i, hi, rfl⟩)

lemma extremePoints_subpolytope {d m : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    {V : Fin m → (Fin d → ℝ)} (hV : Set.range V = {x | IsExposed ℝ P {x}})
    (I : Set (Fin m)) :
    (convexHull ℝ (V '' I)).extremePoints ℝ = V '' I := by
  apply Set.Subset.antisymm
  · exact extremePoints_convexHull_subset
  · rintro x ⟨i, hi, rfl⟩
    exact exposedPoints_subset_extremePoints
      (mem_exposedPoints_iff_exposed_singleton.mpr (exposed_singleton_subpolytope hP hV hi))

/-- Vertex index subset of a face `F` inside a subpolytope `I`. -/
noncomputable def vertFinset {d m : ℕ} (V : Fin m → (Fin d → ℝ)) (I : Finset (Fin m))
    (F : Set (Fin d → ℝ)) : Finset (Fin m) := by
  classical
  exact I.filter (fun i => V i ∈ F)

lemma mem_vertFinset {d m : ℕ} {V : Fin m → (Fin d → ℝ)} {I : Finset (Fin m)}
    {F : Set (Fin d → ℝ)} {i : Fin m} :
    i ∈ vertFinset V I F ↔ i ∈ I ∧ V i ∈ F := by
  classical
  simp [vertFinset]

lemma vertFinset_singleton {d m : ℕ} {V : Fin m → (Fin d → ℝ)} (hVinj : Function.Injective V)
    {I : Finset (Fin m)} {i : Fin m} (hi : i ∈ I) :
    vertFinset V I {V i} = {i} := by
  ext j
  rw [mem_vertFinset, Set.mem_singleton_iff, hVinj.eq_iff, Finset.mem_singleton]
  exact ⟨fun h => h.2, fun h => ⟨h ▸ hi, h⟩⟩

lemma subpolytope_face_eq_convexHull {d m : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    {V : Fin m → (Fin d → ℝ)} (hV : Set.range V = {x | IsExposed ℝ P {x}})
    (I : Finset (Fin m)) (F : PolytopeFace (convexHull ℝ (V '' (I : Set (Fin m))))) :
    F.val = convexHull ℝ (V '' (vertFinset V I F.val : Set (Fin m))) := by
  let P_I := convexHull ℝ (V '' (I : Set (Fin m)))
  have hPI_comp : IsCompact P_I := ((Set.toFinite _).isCompact_convexHull ℝ)
  have hPI_conv : Convex ℝ P_I := convex_convexHull ℝ _
  have hF_comp : IsCompact F.val := F.property.isCompact hPI_comp
  have hF_conv : Convex ℝ F.val := F.property.convex hPI_conv
  have hF_ext : F.val.extremePoints ℝ = V '' (vertFinset V I F.val : Set (Fin m)) := by
    rw [F.property.isExtreme.extremePoints_eq, extremePoints_subpolytope hP hV (I : Set (Fin m))]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_image, Finset.mem_coe, mem_vertFinset]
    constructor
    · rintro ⟨hxF, i, hiI, rfl⟩
      exact ⟨i, ⟨hiI, hxF⟩, rfl⟩
    · rintro ⟨i, ⟨hiI, hiF⟩, rfl⟩
      exact ⟨hiF, i, hiI, rfl⟩
  have h_km := closure_convexHull_extremePoints hF_comp hF_conv
  rw [hF_ext] at h_km
  have h_closed : IsClosed (convexHull ℝ (V '' (vertFinset V I F.val : Set (Fin m)))) :=
    ((Set.toFinite _).isCompact_convexHull ℝ).isClosed
  rw [h_closed.closure_eq] at h_km
  exact h_km.symm

lemma subpolytope_face_le_iff {d m : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    {V : Fin m → (Fin d → ℝ)} (hV : Set.range V = {x | IsExposed ℝ P {x}})
    (I : Finset (Fin m))
    (F1 F2 : PolytopeFace (convexHull ℝ (V '' (I : Set (Fin m))))) :
    F1 ≤ F2 ↔ vertFinset V I F1.val ⊆ vertFinset V I F2.val := by
  constructor
  · intro h i hi
    rw [mem_vertFinset] at hi ⊢
    exact ⟨hi.1, h hi.2⟩
  · intro h
    change F1.val ⊆ F2.val
    rw [subpolytope_face_eq_convexHull hP hV I F1, subpolytope_face_eq_convexHull hP hV I F2]
    exact convexHull_mono (Set.image_mono (Finset.coe_subset.mpr h))

lemma subpolytope_face_eq_iff {d m : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    {V : Fin m → (Fin d → ℝ)} (hV : Set.range V = {x | IsExposed ℝ P {x}})
    (I : Finset (Fin m))
    (F1 F2 : PolytopeFace (convexHull ℝ (V '' (I : Set (Fin m))))) :
    F1 = F2 ↔ vertFinset V I F1.val = vertFinset V I F2.val := by
  rw [le_antisymm_iff, subpolytope_face_le_iff hP hV I, subpolytope_face_le_iff hP hV I,
    Finset.Subset.antisymm_iff]

/-- Exposed faces of a subpolytope `convexHull ℝ (V '' I)` correspond via `vertFinset`
to subsets `S ⊆ I` satisfying `IsAffineExposed V I S`. -/
lemma subpolytope_face_iff_isAffineExposed {d m : ℕ}
    (V : Fin m → (Fin d → ℝ)) (I S : Finset (Fin m)) :
    (∃ F : PolytopeFace (convexHull ℝ (V '' (I : Set (Fin m)))),
      vertFinset V I F.val = S) ↔ IsAffineExposed V I S := by
  classical
  set P_I := convexHull ℝ (V '' (I : Set (Fin m)))
  constructor
  · rintro ⟨F, rfl⟩
    have h_sub : vertFinset V I F.val ⊆ I := fun i hi => (mem_vertFinset.mp hi).1
    rcases (vertFinset V I F.val).eq_empty_or_nonempty with h_empty | ⟨i0, hi0⟩
    · rw [h_empty]
      exact isAffineExposed_empty V I
    · refine ⟨h_sub, ?_⟩
      have hi0I : i0 ∈ I := (mem_vertFinset.mp hi0).1
      have hi0F : V i0 ∈ F.val := (mem_vertFinset.mp hi0).2
      obtain ⟨l, hl_eq⟩ := F.property ⟨V i0, hi0F⟩
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
        have hiI : i ∈ I := (mem_vertFinset.mp hi).1
        have hiF : V i ∈ F.val := (mem_vertFinset.mp hi).2
        have hVi_PI : V i ∈ P_I := subset_convexHull ℝ _ ⟨i, hiI, rfl⟩
        have hVi0_PI : V i0 ∈ P_I := subset_convexHull ℝ _ ⟨i0, hi0I, rfl⟩
        have hiF' : V i ∈ {x ∈ P_I | ∀ y ∈ P_I, l y ≤ l x} := hl_eq ▸ hiF
        have hi0F' : V i0 ∈ {x ∈ P_I | ∀ y ∈ P_I, l y ≤ l x} := hl_eq ▸ hi0F
        have h1 := hiF'.2 (V i0) hVi0_PI
        have h2 := hi0F'.2 (V i) hVi_PI
        linarith
      · intro j hj
        dsimp only
        rw [h_lin]
        rw [Finset.mem_sdiff, mem_vertFinset, not_and] at hj
        have hjI : j ∈ I := hj.1
        have hj_notF : V j ∉ F.val := hj.2 hjI
        have hVj_PI : V j ∈ P_I := subset_convexHull ℝ _ ⟨j, hjI, rfl⟩
        have hi0F' : V i0 ∈ {x ∈ P_I | ∀ y ∈ P_I, l y ≤ l x} := hl_eq ▸ hi0F
        have h_le : l (V j) ≤ l (V i0) := hi0F'.2 (V j) hVj_PI
        have h_ne : l (V j) ≠ l (V i0) := by
          intro h_eq
          apply hj_notF
          rw [hl_eq]
          refine ⟨hVj_PI, fun y hy => ?_⟩
          rw [h_eq]
          exact hi0F'.2 y hy
        linarith [lt_of_le_of_ne h_le h_ne]
  · rintro ⟨hSI, u, c, hS0, hpos⟩
    rcases S.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩
    · refine ⟨⟨∅, isExposed_empty⟩, ?_⟩
      ext i
      simp [mem_vertFinset]
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
      let F : PolytopeFace P_I := ⟨l.toExposed P_I, ContinuousLinearMap.toExposed.isExposed⟩
      have h_le_c : P_I ⊆ {y : Fin d → ℝ | l y ≤ c} := by
        refine convexHull_min ?_ ?_
        · rintro y ⟨i, hiI, rfl⟩
          change l (V i) ≤ c
          rw [hl_apply]
          by_cases hiS : i ∈ S
          · linarith [hS0 i hiS]
          · have hi_sdiff : i ∈ I \ S := Finset.mem_sdiff.mpr ⟨hiI, hiS⟩
            linarith [hpos i hi_sdiff]
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
        linarith [hS0 i0 hi0]
      have hVi0_PI : V i0 ∈ P_I := subset_convexHull ℝ _ ⟨i0, hSI hi0, rfl⟩
      refine ⟨F, ?_⟩
      ext i
      rw [mem_vertFinset]
      simp only [F, ContinuousLinearMap.toExposed, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hiI, _, hmax⟩
        by_contra hi_notS
        have hi_sdiff : i ∈ I \ S := Finset.mem_sdiff.mpr ⟨hiI, hi_notS⟩
        have h_lt : l (V i) < c := by
          rw [hl_apply]
          linarith [hpos i hi_sdiff]
        have h_ge : c ≤ l (V i) := by
          rw [← h_i0_eq]
          exact hmax (V i0) hVi0_PI
        linarith
      · intro hiS
        have hiI : i ∈ I := hSI hiS
        have h_eq : l (V i) = c := by
          rw [hl_apply]
          linarith [hS0 i hiS]
        refine ⟨hiI, subset_convexHull ℝ _ ⟨i, hiI, rfl⟩, fun y hy => ?_⟩
        rw [h_eq]
        exact h_le_c hy

/-- Equivalence between vertex-preserving face-poset isomorphisms on a subpolytope `I`
and matching `IsAffineExposed` subsets. -/
lemma orderIso_subpolytope_iff_isAffineExposed {d m : ℕ}
    {P Q : Set (Fin d → ℝ)} (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    {V W : Fin m → (Fin d → ℝ)}
    (hVinj : Function.Injective V) (hWinj : Function.Injective W)
    (hV : Set.range V = {x | IsExposed ℝ P {x}})
    (hW : Set.range W = {x | IsExposed ℝ Q {x}})
    (θ : Equiv.Perm (Fin m)) (I : Finset (Fin m)) :
    (∃ Ψ : PolytopeFace (convexHull ℝ (V '' (I : Set (Fin m)))) ≃o
        PolytopeFace (convexHull ℝ (W '' (θ '' (I : Set (Fin m))))),
      ∀ (i : Fin m), i ∈ (I : Set (Fin m)) →
        ∀ F : PolytopeFace (convexHull ℝ (V '' (I : Set (Fin m)))),
          F.val = {V i} → (Ψ F).val = {W (θ i)}) ↔
    (∀ S : Finset (Fin m),
      IsAffineExposed V I S ↔ IsAffineExposed W (I.map θ.toEmbedding) (S.map θ.toEmbedding)) := by
  classical
  set I_W : Finset (Fin m) := I.map θ.toEmbedding
  have hIW_coe : (I_W : Set (Fin m)) = θ '' (I : Set (Fin m)) := by
    simp [I_W, Finset.coe_map]
  rw [← hIW_coe]
  constructor
  · rintro ⟨Ψ, hΨ⟩ S
    rw [← subpolytope_face_iff_isAffineExposed V I S,
      ← subpolytope_face_iff_isAffineExposed W I_W (S.map θ.toEmbedding)]
    have h_vert_Ψ : ∀ F : PolytopeFace (convexHull ℝ (V '' (I : Set (Fin m)))),
        vertFinset W I_W (Ψ F).val = (vertFinset V I F.val).map θ.toEmbedding := by
      intro F
      ext j
      obtain ⟨i, rfl⟩ := θ.surjective j
      simp only [Finset.mem_map, Equiv.toEmbedding_apply, θ.injective.eq_iff, exists_eq_right,
        mem_vertFinset, I_W]
      by_cases hiI : i ∈ I
      · simp only [hiI, true_and]
        let sP : PolytopeFace (convexHull ℝ (V '' (I : Set (Fin m)))) :=
          ⟨{V i}, exposed_singleton_subpolytope hP hV (Finset.mem_coe.mpr hiI)⟩
        have hθi : θ i ∈ (I.map θ.toEmbedding : Set (Fin m)) := by
          simp [hiI]
        let sQ : PolytopeFace (convexHull ℝ (W '' (I_W : Set (Fin m)))) :=
          ⟨{W (θ i)}, exposed_singleton_subpolytope hQ hW hθi⟩
        have hsP_eq : Ψ sP = sQ := by
          ext x
          rw [hΨ i (Finset.mem_coe.mpr hiI) sP rfl]
        have h1 : V i ∈ F.val ↔ sP ≤ F := by
          change V i ∈ F.val ↔ {V i} ⊆ F.val
          exact Set.singleton_subset_iff.symm
        have h2 : W (θ i) ∈ (Ψ F).val ↔ sQ ≤ Ψ F := by
          change W (θ i) ∈ (Ψ F).val ↔ {W (θ i)} ⊆ (Ψ F).val
          exact Set.singleton_subset_iff.symm
        rw [h1, h2, ← hsP_eq, Ψ.le_iff_le]
      · simp [hiI]
    constructor
    · rintro ⟨F, rfl⟩
      exact ⟨Ψ F, h_vert_Ψ F⟩
    · rintro ⟨F', hF'⟩
      refine ⟨Ψ.symm F', ?_⟩
      have h_eq := h_vert_Ψ (Ψ.symm F')
      rw [Ψ.apply_symm_apply, hF'] at h_eq
      exact Finset.map_injective θ.toEmbedding h_eq.symm
  · intro h
    have h_face : ∀ S : Finset (Fin m),
        (∃ F : PolytopeFace (convexHull ℝ (V '' (I : Set (Fin m)))), vertFinset V I F.val = S) ↔
        (∃ F' : PolytopeFace (convexHull ℝ (W '' (I_W : Set (Fin m)))),
          vertFinset W I_W F'.val = S.map θ.toEmbedding) := by
      intro S
      rw [subpolytope_face_iff_isAffineExposed V I S,
        subpolytope_face_iff_isAffineExposed W I_W (S.map θ.toEmbedding)]
      exact h S
    have h_fwd : ∀ F : PolytopeFace (convexHull ℝ (V '' (I : Set (Fin m)))),
        ∃ F' : PolytopeFace (convexHull ℝ (W '' (I_W : Set (Fin m)))),
          vertFinset W I_W F'.val = (vertFinset V I F.val).map θ.toEmbedding :=
      fun F => (h_face (vertFinset V I F.val)).mp ⟨F, rfl⟩
    have h_bwd : ∀ F' : PolytopeFace (convexHull ℝ (W '' (I_W : Set (Fin m)))),
        ∃ F : PolytopeFace (convexHull ℝ (V '' (I : Set (Fin m)))),
          vertFinset V I F.val = (vertFinset W I_W F'.val).map θ.symm.toEmbedding := by
      intro F'
      have h_map : ((vertFinset W I_W F'.val).map θ.symm.toEmbedding).map θ.toEmbedding =
          vertFinset W I_W F'.val := by
        ext j
        simp
      obtain ⟨F, hF⟩ :=
        (h_face ((vertFinset W I_W F'.val).map θ.symm.toEmbedding)).mpr ⟨F', h_map.symm⟩
      exact ⟨F, hF⟩
    let toFun := fun F => Classical.choose (h_fwd F)
    have h_toFun : ∀ F, vertFinset W I_W (toFun F).val =
        (vertFinset V I F.val).map θ.toEmbedding :=
      fun F => Classical.choose_spec (h_fwd F)
    let invFun := fun F' => Classical.choose (h_bwd F')
    have h_invFun : ∀ F', vertFinset V I (invFun F').val =
        (vertFinset W I_W F'.val).map θ.symm.toEmbedding :=
      fun F' => Classical.choose_spec (h_bwd F')
    refine ⟨{
      toFun := toFun
      invFun := invFun
      left_inv := fun F => by
        rw [subpolytope_face_eq_iff hP hV I, h_invFun, h_toFun]
        ext i; simp
      right_inv := fun F' => by
        rw [subpolytope_face_eq_iff hQ hW I_W, h_toFun, h_invFun]
        ext j; simp
      map_rel_iff' := fun {F1 F2} => by
        rw [subpolytope_face_le_iff hQ hW I_W, subpolytope_face_le_iff hP hV I]
        change vertFinset W I_W (toFun F1).val ⊆ vertFinset W I_W (toFun F2).val ↔
          vertFinset V I F1.val ⊆ vertFinset V I F2.val
        rw [h_toFun, h_toFun, Finset.map_subset_map]
    }, ?_⟩
    intro i hiI F hF_eq
    have hiI' : i ∈ I := Finset.mem_coe.mp hiI
    have hθiI : θ i ∈ I_W := Finset.mem_map.mpr ⟨i, hiI', rfl⟩
    have h_v : vertFinset V I F.val = {i} := by
      rw [hF_eq, vertFinset_singleton hVinj hiI']
    have h_w : vertFinset W I_W (toFun F).val = {θ i} := by
      rw [h_toFun F, h_v, Finset.map_singleton, Equiv.toEmbedding_apply]
    have h_s : vertFinset W I_W ({W (θ i)} : Set (Fin d → ℝ)) = {θ i} :=
      vertFinset_singleton hWinj hθiI
    have h_face_eq : toFun F =
        ⟨{W (θ i)}, exposed_singleton_subpolytope hQ hW (Finset.mem_coe.mpr hθiI)⟩ := by
      rw [subpolytope_face_eq_iff hQ hW I_W, h_w, h_s]
    exact congrArg Subtype.val h_face_eq

/-- Intermediate finset existence lemma: given `s ⊆ u` and `s.card ≤ n ≤ u.card`,
there exists `t` with `s ⊆ t ⊆ u` and `t.card = n`. -/
lemma exists_superset_subset_card_eq {m n : ℕ} {s u : Finset (Fin m)}
    (hsu : s ⊆ u) (hsn : s.card ≤ n) (hnu : n ≤ u.card) :
    ∃ t : Finset (Fin m), s ⊆ t ∧ t ⊆ u ∧ t.card = n := by
  classical
  have h_sdiff : n - s.card ≤ (u \ s).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsu]
    omega
  obtain ⟨d, hdu, hd_card⟩ := Finset.exists_subset_card_eq h_sdiff
  refine ⟨s ∪ d, Finset.subset_union_left, ?_, ?_⟩
  · exact Finset.union_subset hsu (hdu.trans Finset.sdiff_subset)
  · have h_disj : Disjoint s d :=
      Finset.disjoint_of_subset_right hdu disjoint_sdiff_self_right
    rw [Finset.card_union_of_disjoint h_disj, hd_card]
    omega

/-- Linear evaluation map `(u, c) ↦ (i ↦ ∑ k, u k * V i k + c)` on a subset `K : Finset (Fin m)`. -/
def evalKMap {d m : ℕ} (V : Fin m → (Fin d → ℝ)) (K : Finset (Fin m)) :
    ((Fin d → ℝ) × ℝ) →ₗ[ℝ] (K → ℝ) where
  toFun p i := (∑ k : Fin d, p.1 k * V i.val k) + p.2
  map_add' p q := by
    ext i
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' r p := by
    ext i
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      mul_add, ← Finset.mul_sum, mul_assoc]

@[simp]
lemma evalKMap_apply {d m : ℕ} (V : Fin m → (Fin d → ℝ)) (K : Finset (Fin m))
    (p : (Fin d → ℝ) × ℝ) (i : K) :
    evalKMap V K p i = (∑ k : Fin d, p.1 k * V i.val k) + p.2 := rfl

/-- Transpose map `w ↦ (∑ i : K, w i • V i, ∑ i : K, w i)`. -/
def evalKTranspose {d m : ℕ} (V : Fin m → (Fin d → ℝ)) (K : Finset (Fin m)) :
    (K → ℝ) →ₗ[ℝ] ((Fin d → ℝ) × ℝ) where
  toFun w := (∑ i : K, w i • V i.val, ∑ i : K, w i)
  map_add' w1 w2 := by
    ext k
    · simp only [Prod.fst_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    · simp only [Prod.snd_add, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r w := by
    ext k
    · simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul,
        ← Finset.smul_sum]
    · simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]

@[simp]
lemma evalKTranspose_fst {d m : ℕ} (V : Fin m → (Fin d → ℝ)) (K : Finset (Fin m)) (w : K → ℝ) :
    (evalKTranspose V K w).1 = ∑ i : K, w i • V i.val := rfl

@[simp]
lemma evalKTranspose_snd {d m : ℕ} (V : Fin m → (Fin d → ℝ)) (K : Finset (Fin m)) (w : K → ℝ) :
    (evalKTranspose V K w).2 = ∑ i : K, w i := rfl

/-- Duality identity pairing `evalKMap` and `evalKTranspose`. -/
lemma evalK_duality {d m : ℕ} (V : Fin m → (Fin d → ℝ)) (K : Finset (Fin m))
    (p : (Fin d → ℝ) × ℝ) (w : K → ℝ) :
    ∑ i : K, w i * evalKMap V K p i =
      (∑ k : Fin d, p.1 k * (evalKTranspose V K w).1 k) + p.2 * (evalKTranspose V K w).2 := by
  simp only [evalKMap_apply, evalKTranspose_fst, evalKTranspose_snd, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, mul_comm (p.2)]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun i _ => by ring)

/-- A full-dimensional `d`-polytope has at least `d + 1` vertices. -/
lemma card_univ_ge_dim_add_one {d m : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    {V : Fin m → (Fin d → ℝ)} (hV : Set.range V = {x | IsExposed ℝ P {x}}) :
    d + 1 ≤ m := by
  have hinj : Function.Injective (evalKMap V Finset.univ) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨u, c⟩ h_ker
    rw [LinearMap.mem_ker] at h_ker
    have h_zero_V : ∀ i : Fin m, (∑ k : Fin d, u k * V i k) + c = 0 := by
      intro i
      exact congrFun h_ker ⟨i, Finset.mem_univ i⟩
    have h_zero_P : ∀ x ∈ P, (∑ k : Fin d, u k * x k) + c = 0 := by
      rw [P_eq_convexHull_range hP hV]
      intro x hx
      refine convexHull_min (s := Set.range V)
        (t := {z : Fin d → ℝ | (∑ k : Fin d, u k * z k) + c = 0}) ?_ ?_ hx
      · rintro z ⟨i, rfl⟩
        exact h_zero_V i
      · intro x1 hx1 x2 hx2 a b _ _ hab
        change (∑ k : Fin d, u k * x1 k) + c = 0 at hx1
        change (∑ k : Fin d, u k * x2 k) + c = 0 at hx2
        change (∑ k : Fin d, u k * (a • x1 + b • x2) k) + c = 0
        have h_comb : (∑ k : Fin d, u k * (a • x1 + b • x2) k) + c =
            a * ((∑ k : Fin d, u k * x1 k) + c) + b * ((∑ k : Fin d, u k * x2 k) + c) +
            (1 - (a + b)) * c := by
          simp_rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
            ← mul_assoc, mul_comm (u _) a, mul_comm (u _) b, mul_assoc, ← Finset.mul_sum]
          ring
        rw [h_comb, hx1, hx2, hab]
        ring
    have h_zero_aff : ∀ x ∈ affineSpan ℝ P, (∑ k : Fin d, u k * x k) + c = 0 := by
      intro x hx
      refine affineSpan_induction (k := ℝ) (s := P)
        (p := fun z => (∑ k : Fin d, u k * z k) + c = 0) hx h_zero_P ?_
      intro r x1 y1 z1 hx1 hy1 hz1
      have h_comb : (∑ k : Fin d, u k * (r • (x1 -ᵥ y1) +ᵥ z1) k) + c =
          r * (((∑ k : Fin d, u k * x1 k) + c) - ((∑ k : Fin d, u k * y1 k) + c)) +
          ((∑ k : Fin d, u k * z1 k) + c) := by
        simp_rw [vadd_eq_add, vsub_eq_sub, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
          smul_eq_mul, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← mul_assoc, mul_comm (u _) r, mul_assoc, ← Finset.mul_sum]
        ring
      rw [h_comb, hx1, hy1, hz1]
      ring
    have h_all : ∀ x : Fin d → ℝ, (∑ k : Fin d, u k * x k) + c = 0 := by
      intro x
      apply h_zero_aff x
      rw [hP.2]
      exact AffineSubspace.mem_top ℝ (Fin d → ℝ) x
    have hc : c = 0 := by
      have h0 := h_all 0
      simpa using h0
    have hu : u = 0 := by
      ext k
      have hk := h_all (stdBasis k)
      rw [hc, add_zero] at hk
      simpa [stdBasis_apply] using hk
    exact Prod.ext hu hc
  have h_rank := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_prod, Module.finrank_pi, Module.finrank_self, Fintype.card_fin] using h_rank

/-- Local `r`-neighborliness predicate on `I : Finset (Fin m)`. -/
def IsRNeighborlyOn {r m : ℕ} (V : Fin m → (Fin (2 * r) → ℝ)) (r_val : ℕ)
    (I : Finset (Fin m)) : Prop :=
  2 * r_val + 1 ≤ I.card ∧ ∀ A : Finset (Fin m), A ⊆ I → A.card = r_val → IsAffineExposed V I A

lemma isRNeighborlyOn_univ {r m : ℕ} {P : Set (Fin (2 * r) → ℝ)}
    (hP : IsDPolytope P) (hPn : IsKNeighborly r P)
    {V : Fin m → (Fin (2 * r) → ℝ)} (hVinj : Function.Injective V)
    (hV : Set.range V = {x | IsExposed ℝ P {x}}) :
    IsRNeighborlyOn V r Finset.univ := by
  classical
  refine ⟨?_, ?_⟩
  · simpa using card_univ_ge_dim_add_one hP hV
  · intro A _ hA_card
    let VA : Finset (Fin (2 * r) → ℝ) := A.image V
    have hVA_exp : ∀ x ∈ VA, IsExposed ℝ P {x} := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
      exact exposed_singleton_vertex hV i
    have hVA_card : VA.card = r := by
      rw [Finset.card_image_of_injective A hVinj, hA_card]
    obtain ⟨hFA_exp, _, hFA_verts⟩ := hPn.2 VA hVA_exp hVA_card
    have hP_eq : P = convexHull ℝ (V '' ((Finset.univ : Finset (Fin m)) : Set (Fin m))) := by
      rw [Finset.coe_univ, Set.image_univ, ← P_eq_convexHull_range hP hV]
    let F : PolytopeFace (convexHull ℝ (V '' ((Finset.univ : Finset (Fin m)) : Set (Fin m)))) :=
      ⟨convexHull ℝ (VA : Set (Fin (2 * r) → ℝ)), hP_eq ▸ hFA_exp⟩
    rw [← subpolytope_face_iff_isAffineExposed V Finset.univ A]
    refine ⟨F, ?_⟩
    ext i
    rw [mem_vertFinset]
    simp only [Finset.mem_univ, true_and, F]
    constructor
    · intro hiF
      have hFA_sub_P : convexHull ℝ (VA : Set (Fin (2 * r) → ℝ)) ⊆ P := hFA_exp.subset
      have hi_exp_FA : IsExposed ℝ (convexHull ℝ (VA : Set (Fin (2 * r) → ℝ))) {V i} :=
        isExposed_singleton_mono (exposed_singleton_vertex hV i) hFA_sub_P hiF
      have hi_in_VA : V i ∈ (VA : Set (Fin (2 * r) → ℝ)) := by
        rw [← hFA_verts]
        exact hi_exp_FA
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hi_in_VA) with ⟨j, hjA, hj_eq⟩
      exact hVinj hj_eq ▸ hjA
    · intro hiA
      apply subset_convexHull ℝ (VA : Set (Fin (2 * r) → ℝ))
      exact Finset.mem_coe.mpr (Finset.mem_image_of_mem V hiA)

lemma affine_dep_eval_zero {d m : ℕ} {V : Fin m → (Fin d → ℝ)}
    {a : Fin m → ℝ} (ha_sum : ∑ i : Fin m, a i = 0) (ha_vec : ∑ i : Fin m, a i • V i = 0)
    (u : Fin d → ℝ) (c : ℝ) :
    ∑ i : Fin m, a i * ((∑ k : Fin d, u k * V i k) + c) = 0 := by
  have h_vec_k : ∀ k : Fin d, ∑ i : Fin m, a i * V i k = 0 := by
    intro k
    have hk := congrFun ha_vec k
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hk
  calc ∑ i : Fin m, a i * ((∑ k : Fin d, u k * V i k) + c)
      = (∑ i : Fin m, ∑ k : Fin d, u k * (a i * V i k)) + (∑ i : Fin m, a i) * c := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun k _ => by ring)
    _ = (∑ k : Fin d, u k * (∑ i : Fin m, a i * V i k)) + (∑ i : Fin m, a i) * c := by
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum]
    _ = 0 := by
        simp [h_vec_k, ha_sum]

/-- In an `r`-neighborly `2r`-polytope, any non-zero affine dependency has at least `r + 1`
strictly positive coefficients. -/
lemma neighborly_affine_dep_pos_card {r m : ℕ} (hr : 1 ≤ r)
    {V : Fin m → (Fin (2 * r) → ℝ)} (hN : IsRNeighborlyOn V r Finset.univ)
    {a : Fin m → ℝ} (ha_ne : ∃ i, a i ≠ 0)
    (ha_sum : ∑ i : Fin m, a i = 0)
    (ha_vec : ∑ i : Fin m, a i • V i = 0) :
    r + 1 ≤ (Finset.univ.filter (fun i => 0 < a i)).card := by
  classical
  set C_pos := Finset.univ.filter (fun i => 0 < a i)
  set C_neg := Finset.univ.filter (fun i => a i < 0)
  have h_neg_ne : C_neg.Nonempty := by
    by_contra h_empty
    rw [Finset.not_nonempty_iff_eq_empty] at h_empty
    have ha_nonneg : ∀ i ∈ Finset.univ, 0 ≤ a i := by
      intro i _
      by_contra h_lt
      push_neg at h_lt
      have hi : i ∈ C_neg := Finset.mem_filter.mpr ⟨Finset.mem_univ i, h_lt⟩
      rw [h_empty] at hi
      exact Finset.notMem_empty i hi
    have ha_all_zero : ∀ i ∈ Finset.univ, a i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg ha_nonneg).mp ha_sum
    rcases ha_ne with ⟨i0, hi0⟩
    exact hi0 (ha_all_zero i0 (Finset.mem_univ i0))
  rcases h_neg_ne with ⟨j0, hj0⟩
  have hj0_neg : a j0 < 0 := (Finset.mem_filter.mp hj0).2
  by_contra h_le
  push_neg at h_le
  have hC_pos_le : C_pos.card ≤ r := Nat.lt_succ_iff.mp h_le
  have hC_pos_sub : C_pos ⊆ Finset.univ.erase j0 := by
    intro i hi
    have hi_pos : 0 < a i := (Finset.mem_filter.mp hi).2
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ i⟩
    intro h_eq
    subst h_eq
    linarith
  have h_erase_card : r ≤ (Finset.univ.erase j0).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j0)]
    have h_univ := hN.1
    omega
  obtain ⟨A, hC_pos_A, hA_erase, hA_card⟩ :=
    exists_superset_subset_card_eq hC_pos_sub hC_pos_le h_erase_card
  have hA_exp : IsAffineExposed V Finset.univ A :=
    hN.2 A (Finset.subset_univ A) hA_card
  rcases hA_exp with ⟨_, u, c, hA0, hpos⟩
  let g : Fin m → ℝ := fun i => (∑ k : Fin (2 * r), u k * V i k) + c
  have hg_sum : ∑ i : Fin m, a i * g i = 0 :=
    affine_dep_eval_zero ha_sum ha_vec u c
  have hg_nonpos : ∀ i ∈ Finset.univ, a i * g i ≤ 0 := by
    intro i _
    by_cases hiA : i ∈ A
    · have hgi : g i = 0 := hA0 i hiA
      simp [hgi]
    · have hi_sdiff : i ∈ Finset.univ \ A := Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiA⟩
      have hgi_pos : 0 < g i := hpos i hi_sdiff
      have hi_not_pos : ¬ (0 < a i) := by
        intro h_pos
        exact hiA (hC_pos_A (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h_pos⟩))
      have hai_le : a i ≤ 0 := not_lt.mp hi_not_pos
      exact mul_nonpos_of_nonpos_of_nonneg hai_le (le_of_lt hgi_pos)
  have hj0_notA : j0 ∉ A := by
    intro hj0A
    exact (Finset.mem_erase.mp (hA_erase hj0A)).1 rfl
  have hj0_sdiff : j0 ∈ Finset.univ \ A := Finset.mem_sdiff.mpr ⟨Finset.mem_univ j0, hj0_notA⟩
  have hgj0_pos : 0 < g j0 := hpos j0 hj0_sdiff
  have hj0_strict : a j0 * g j0 < 0 := mul_neg_of_neg_of_pos hj0_neg hgj0_pos
  have h_le_sum := Finset.single_le_sum
    (f := fun i => -(a i * g i))
    (fun i hi => neg_nonneg.mpr (hg_nonpos i hi))
    (Finset.mem_univ j0)
  rw [Finset.sum_neg_distrib, hg_sum, neg_zero] at h_le_sum
  linarith

lemma neighborly_affine_dep_pos_neg_card {r m : ℕ} (hr : 1 ≤ r)
    {V : Fin m → (Fin (2 * r) → ℝ)} (hN : IsRNeighborlyOn V r Finset.univ)
    {a : Fin m → ℝ} (ha_ne : ∃ i, a i ≠ 0)
    (ha_sum : ∑ i : Fin m, a i = 0)
    (ha_vec : ∑ i : Fin m, a i • V i = 0) :
    r + 1 ≤ (Finset.univ.filter (fun i => 0 < a i)).card ∧
    r + 1 ≤ (Finset.univ.filter (fun i => a i < 0)).card := by
  refine ⟨neighborly_affine_dep_pos_card hr hN ha_ne ha_sum ha_vec, ?_⟩
  have h_neg_ne : ∃ i, (-a) i ≠ 0 := by
    rcases ha_ne with ⟨i, hi⟩
    exact ⟨i, neg_ne_zero.mpr hi⟩
  have h_neg_sum : ∑ i : Fin m, (-a) i = 0 := by
    simp [Finset.sum_neg_distrib, ha_sum]
  have h_neg_vec : ∑ i : Fin m, (-a) i • V i = 0 := by
    simp [neg_smul, Finset.sum_neg_distrib, ha_vec]
  have h_pos := neighborly_affine_dep_pos_card hr hN h_neg_ne h_neg_sum h_neg_vec
  have h_filter_eq :
      Finset.univ.filter (fun i => 0 < (-a) i) = Finset.univ.filter (fun i => a i < 0) := by
    ext i
    simp [neg_pos]
  rwa [h_filter_eq] at h_pos

/-- General position: any affine dependency supported on at most `2 * r + 1` vertices is zero. -/
lemma affine_dep_eq_zero_of_support_card_le {r m : ℕ} (hr : 1 ≤ r)
    {V : Fin m → (Fin (2 * r) → ℝ)} (hN : IsRNeighborlyOn V r Finset.univ)
    {K : Finset (Fin m)} (hK : K.card ≤ 2 * r + 1)
    {a : Fin m → ℝ} (ha_supp : ∀ i, i ∉ K → a i = 0)
    (ha_sum : ∑ i : Fin m, a i = 0)
    (ha_vec : ∑ i : Fin m, a i • V i = 0) :
    ∀ i : Fin m, a i = 0 := by
  classical
  by_contra h_not_all
  push_neg at h_not_all
  obtain ⟨h_pos, h_neg⟩ := neighborly_affine_dep_pos_neg_card hr hN h_not_all ha_sum ha_vec
  set C_pos := Finset.univ.filter (fun i => 0 < a i)
  set C_neg := Finset.univ.filter (fun i => a i < 0)
  have h_disj : Disjoint C_pos C_neg := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have h1 : 0 < a i := (Finset.mem_filter.mp hi1).2
    have h2 : a i < 0 := (Finset.mem_filter.mp hi2).2
    linarith
  have h_sub : C_pos ∪ C_neg ⊆ K := by
    intro i hi
    by_contra hiK
    have hai0 : a i = 0 := ha_supp i hiK
    rcases Finset.mem_union.mp hi with hi1 | hi2
    · have h1 : 0 < a i := (Finset.mem_filter.mp hi1).2
      linarith
    · have h2 : a i < 0 := (Finset.mem_filter.mp hi2).2
      linarith
  have h_card_union : C_pos.card + C_neg.card ≤ K.card := by
    rw [← Finset.card_union_of_disjoint h_disj]
    exact Finset.card_le_card h_sub
  omega

lemma evalKTranspose_bijective_of_card_eq {r m : ℕ} (hr : 1 ≤ r)
    {V : Fin m → (Fin (2 * r) → ℝ)} (hN : IsRNeighborlyOn V r Finset.univ)
    {K : Finset (Fin m)} (hK : K.card = 2 * r + 1) :
    Function.Bijective (evalKTranspose V K) := by
  have hinj : Function.Injective (evalKTranspose V K) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker] at hw
    have hw_vec : ∑ i : K, w i • V i.val = 0 := congrArg Prod.fst hw
    have hw_sum : ∑ i : K, w i = 0 := congrArg Prod.snd hw
    classical
    let a : Fin m → ℝ := fun i => if h : i ∈ K then w ⟨i, h⟩ else 0
    have ha_supp : ∀ i, i ∉ K → a i = 0 := by
      intro i hi
      simp [a, hi]
    have ha_sum : ∑ i : Fin m, a i = 0 := by
      have h1 : ∑ i : Fin m, a i = ∑ i ∈ K, a i := by
        refine (Finset.sum_subset (Finset.subset_univ K) ?_).symm
        intro i _ hiK
        exact ha_supp i hiK
      have h2 : ∑ i ∈ K, a i = ∑ i : K, w i := by
        rw [← Finset.sum_attach K]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp [a, i.property]
      rw [h1, h2, hw_sum]
    have ha_vec : ∑ i : Fin m, a i • V i = 0 := by
      have h1 : ∑ i : Fin m, a i • V i = ∑ i ∈ K, a i • V i := by
        refine (Finset.sum_subset (Finset.subset_univ K) ?_).symm
        intro i _ hiK
        simp [ha_supp i hiK]
      have h2 : ∑ i ∈ K, a i • V i = ∑ i : K, w i • V i.val := by
        rw [← Finset.sum_attach K]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp [a, i.property]
      rw [h1, h2, hw_vec]
    have ha0 := affine_dep_eq_zero_of_support_card_le hr hN (le_of_eq hK) ha_supp ha_sum ha_vec
    ext ⟨i, hi⟩
    have := ha0 i
    simpa [a, hi] using this
  have h_finrank :
      Module.finrank ℝ (K → ℝ) = Module.finrank ℝ ((Fin (2 * r) → ℝ) × ℝ) := by
    simp [Module.finrank_prod, Module.finrank_pi, Module.finrank_self, Fintype.card_fin, hK]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_finrank).mp hinj⟩

lemma evalKMap_bijective_of_card_eq {r m : ℕ} (hr : 1 ≤ r)
    {V : Fin m → (Fin (2 * r) → ℝ)} (hN : IsRNeighborlyOn V r Finset.univ)
    {K : Finset (Fin m)} (hK : K.card = 2 * r + 1) :
    Function.Bijective (evalKMap V K) := by
  have hT_bij := evalKTranspose_bijective_of_card_eq hr hN hK
  have hinj : Function.Injective (evalKMap V K) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨u, c⟩ hp
    rw [LinearMap.mem_ker] at hp
    obtain ⟨w, hw⟩ := hT_bij.2 (u, c)
    have h_dual := evalK_duality V K (u, c) w
    rw [hp, hw] at h_dual
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h_dual
    have h_u_nonneg : 0 ≤ ∑ k : Fin (2 * r), u k * u k :=
      Finset.sum_nonneg (fun k _ => mul_self_nonneg (u k))
    have h_c_nonneg : 0 ≤ c * c := mul_self_nonneg c
    have hc2 : c * c = 0 := by linarith
    have hc : c = 0 := mul_self_eq_zero.mp hc2
    have hu2 : ∑ k : Fin (2 * r), u k * u k = 0 := by linarith
    have hu_all : ∀ k ∈ (Finset.univ : Finset (Fin (2 * r))), u k * u k = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_self_nonneg (u k))).mp hu2
    have hu : u = 0 := by
      ext k
      exact mul_self_eq_zero.mp (hu_all k (Finset.mem_univ k))
    exact Prod.ext hu hc
  have h_finrank :
      Module.finrank ℝ ((Fin (2 * r) → ℝ) × ℝ) = Module.finrank ℝ (K → ℝ) := by
    simp [Module.finrank_prod, Module.finrank_pi, Module.finrank_self, Fintype.card_fin, hK]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_finrank).mp hinj⟩

/-- Any function on a subset `K` of cardinality at most `2 * r + 1` is the restriction of
an affine functional on `Fin (2 * r) → ℝ`. -/
lemma exists_affineEval_of_card_le {r m : ℕ} (hr : 1 ≤ r)
    {V : Fin m → (Fin (2 * r) → ℝ)} (hN : IsRNeighborlyOn V r Finset.univ)
    {K : Finset (Fin m)} (hK : K.card ≤ 2 * r + 1) (b : Fin m → ℝ) :
    ∃ (u : Fin (2 * r) → ℝ) (c : ℝ),
      ∀ i ∈ K, (∑ k : Fin (2 * r), u k * V i k) + c = b i := by
  obtain ⟨K', hKK', _, hK'_card⟩ :=
    exists_superset_subset_card_eq (Finset.subset_univ K) hK hN.1
  obtain ⟨⟨u, c⟩, h_eq⟩ :=
    (evalKMap_bijective_of_card_eq hr hN hK'_card).2 (fun i : K' => b i.val)
  refine ⟨u, c, ?_⟩
  intro i hiK
  have hi := congrFun h_eq ⟨i, hKK' hiK⟩
  simpa [evalKMap_apply] using hi

/-- Any affine functional vanishing on `2 * r + 1` vertices is identically zero. -/
lemma affineEval_eq_zero_of_card_eq {r m : ℕ} (hr : 1 ≤ r)
    {V : Fin m → (Fin (2 * r) → ℝ)} (hN : IsRNeighborlyOn V r Finset.univ)
    {K : Finset (Fin m)} (hK : K.card = 2 * r + 1)
    {u : Fin (2 * r) → ℝ} {c : ℝ}
    (h0 : ∀ i ∈ K, (∑ k : Fin (2 * r), u k * V i k) + c = 0) :
    u = 0 ∧ c = 0 := by
  have hp : evalKMap V K (u, c) = 0 := by
    ext ⟨i, hi⟩
    simpa [evalKMap_apply] using h0 i hi
  have h_eq := (evalKMap_bijective_of_card_eq hr hN hK).1 (hp.trans (LinearMap.map_zero _).symm)
  exact Prod.ext_iff.mp h_eq

/-- Simplex subpolytopes: when `I.card ≤ 2 * r + 1`, every subset `S ⊆ I` is affine-exposed. -/
lemma isAffineExposed_iff_subset_of_card_le {r m : ℕ} (hr : 1 ≤ r)
    {V : Fin m → (Fin (2 * r) → ℝ)} (hN : IsRNeighborlyOn V r Finset.univ)
    {I : Finset (Fin m)} (hI : I.card ≤ 2 * r + 1) (S : Finset (Fin m)) :
    IsAffineExposed V I S ↔ S ⊆ I := by
  classical
  constructor
  · exact fun h => h.1
  · intro hSI
    obtain ⟨u, c, h_eq⟩ :=
      exists_affineEval_of_card_le hr hN hI (fun i => if i ∈ S then (0 : ℝ) else 1)
    refine ⟨hSI, u, c, ?_, ?_⟩
    · intro i hiS
      have hi := h_eq i (hSI hiS)
      simpa [hiS] using hi
    · intro j hj
      rw [Finset.mem_sdiff] at hj
      have hj_eq := h_eq j hj.1
      simp only [hj.2, ↓reduceIte] at hj_eq
      linarith

/-- Any proper affine-exposed subset of `I` has cardinality at most `2 * r`. -/
lemma proper_isAffineExposed_card_le {r m : ℕ} (hr : 1 ≤ r)
    {V : Fin m → (Fin (2 * r) → ℝ)} (hN : IsRNeighborlyOn V r Finset.univ)
    {I S : Finset (Fin m)} (hS : IsAffineExposed V I S) (hSne : S ≠ I) :
    S.card ≤ 2 * r := by
  rcases hS with ⟨hSI, u, c, hS0, hpos⟩
  have h_sdiff_ne : (I \ S).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne.eq_def, Finset.sdiff_eq_empty_iff_subset]
    intro hIS
    exact hSne (Finset.Subset.antisymm hSI hIS)
  rcases h_sdiff_ne with ⟨j0, hj0⟩
  by_contra h_gt
  push_neg at h_gt
  obtain ⟨K, hKS, hK_card⟩ := Finset.exists_subset_card_eq h_gt
  have hK0 : ∀ i ∈ K, (∑ k : Fin (2 * r), u k * V i k) + c = 0 :=
    fun i hiK => hS0 i (hKS hiK)
  obtain ⟨hu, hc⟩ := affineEval_eq_zero_of_card_eq hr hN hK_card hK0
  have hj0_pos := hpos j0 hj0
  simp [hu, hc] at hj0_pos

/-- Every subset `S` of an affine-exposed set `F` of size at most `2 * r + 1` is affine-exposed. -/
lemma isAffineExposed_of_subset_facet {r m : ℕ} (hr : 1 ≤ r)
    {V : Fin m → (Fin (2 * r) → ℝ)} (hN : IsRNeighborlyOn V r Finset.univ)
    {I F S : Finset (Fin m)} (hF : IsAffineExposed V I F) (hF_card : F.card ≤ 2 * r + 1)
    (hSF : S ⊆ F) :
    IsAffineExposed V I S := by
  classical
  rcases hF with ⟨hFI, u, c, hF0, hpos⟩
  obtain ⟨u', c', hg_eq⟩ :=
    exists_affineEval_of_card_le hr hN hF_card (fun i => if i ∈ S then (0 : ℝ) else 1)
  let f : Fin m → ℝ := fun i => (∑ k : Fin (2 * r), u k * V i k) + c
  let g : Fin m → ℝ := fun i => (∑ k : Fin (2 * r), u' k * V i k) + c'
  rcases (I \ F).eq_empty_or_nonempty with h_empty | h_ne
  · have hIF : I = F :=
      Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp h_empty) hFI
    subst hIF
    refine ⟨hSF, u', c', ?_, ?_⟩
    · intro i hiS
      have := hg_eq i (hSF hiS)
      simpa [hiS] using this
    · intro j hj
      rw [Finset.mem_sdiff] at hj
      have := hg_eq j hj.1
      simp only [hj.2, ↓reduceIte] at this
      linarith
  · obtain ⟨j_min, hj_min_mem, hj_min_le⟩ := Finset.exists_min_image (I \ F) f h_ne
    have hfj_min_pos : 0 < f j_min := hpos j_min hj_min_mem
    let B : ℝ := (∑ j ∈ I \ F, |g j|) + 1
    have hB_pos : 0 < B := by
      have : 0 ≤ ∑ j ∈ I \ F, |g j| := Finset.sum_nonneg (fun j _ => abs_nonneg (g j))
      linarith
    let M : ℝ := B / f j_min
    have hM_pos : 0 < M := div_pos hB_pos hfj_min_pos
    refine ⟨hSF.trans hFI, fun k => M * u k + u' k, M * c + c', ?_, ?_⟩
    · intro i hiS
      have h_lin : (∑ k : Fin (2 * r), (M * u k + u' k) * V i k) + (M * c + c') =
          M * f i + g i := by
        simp only [f, g, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
      rw [h_lin]
      have hfi : f i = 0 := hF0 i (hSF hiS)
      have hgi : g i = 0 := by
        have := hg_eq i (hSF hiS)
        simpa [hiS] using this
      rw [hfi, hgi]
      ring
    · intro j hj
      have h_lin : (∑ k : Fin (2 * r), (M * u k + u' k) * V j k) + (M * c + c') =
          M * f j + g j := by
        simp only [f, g, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
      rw [h_lin]
      rw [Finset.mem_sdiff] at hj
      by_cases hjF : j ∈ F
      · have hfj : f j = 0 := hF0 j hjF
        have hgj : g j = 1 := by
          have := hg_eq j hjF
          simpa [hj.2] using this
        rw [hfj, hgj]
        linarith
      · have hj_sdiff : j ∈ I \ F := Finset.mem_sdiff.mpr ⟨hj.1, hjF⟩
        have hfj_ge : f j_min ≤ f j := hj_min_le j hj_sdiff
        have hM_fj : B ≤ M * f j := by
          have h1 : B = M * f j_min := (div_mul_cancel₀ B (ne_of_gt hfj_min_pos)).symm
          nlinarith
        have h_abs_le : |g j| ≤ ∑ x ∈ I \ F, |g x| :=
          Finset.single_le_sum (fun x _ => abs_nonneg (g x)) hj_sdiff
        have h_neg_le : - |g j| ≤ g j := neg_abs_le (g j)
        linarith

/-- If `S ⊂ I` is affine-exposed and `S.card < 2 * r`, it can be strictly enlarged to a proper
affine-exposed subset `S' ⊂ I`. -/
lemma exists_strict_superset_isAffineExposed {r m : ℕ} (hr : 1 ≤ r)
    {V : Fin m → (Fin (2 * r) → ℝ)} (hN : IsRNeighborlyOn V r Finset.univ)
    {I S : Finset (Fin m)} (hI : 2 * r + 1 ≤ I.card)
    (hS : IsAffineExposed V I S) (hS_card : S.card < 2 * r) :
    ∃ S' : Finset (Fin m), S ⊆ S' ∧ S.card < S'.card ∧ S' ≠ I ∧ IsAffineExposed V I S' := by
  classical
  rcases hS with ⟨hSI, u, c, hS0, hpos⟩
  let f : Fin m → ℝ := fun i => (∑ k : Fin (2 * r), u k * V i k) + c
  have h_sdiff_card : 2 ≤ (I \ S).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hSI]
    omega
  have h_sdiff_ne : (I \ S).Nonempty := Finset.card_pos.mp (by omega)
  rcases h_sdiff_ne with ⟨y0, hy0⟩
  have h_erase_ne : ((I \ S).erase y0).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hy0]
    omega
  rcases h_erase_ne with ⟨z0, hz0⟩
  have hz0_sdiff : z0 ∈ I \ S := Finset.mem_of_mem_erase hz0
  have hz0_ne_y0 : z0 ≠ y0 := (Finset.mem_erase.mp hz0).1
  have hy0I : y0 ∈ I := (Finset.mem_sdiff.mp hy0).1
  have hy0_notS : y0 ∉ S := (Finset.mem_sdiff.mp hy0).2
  have hz0I : z0 ∈ I := (Finset.mem_sdiff.mp hz0_sdiff).1
  have hz0_notS : z0 ∉ S := (Finset.mem_sdiff.mp hz0_sdiff).2
  have hS_sub_erase : S ⊆ (I.erase y0).erase z0 := by
    intro i hiS
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hSI hiS⟩⟩
    · intro h_eq; exact hz0_notS (h_eq ▸ hiS)
    · intro h_eq; exact hy0_notS (h_eq ▸ hiS)
  have hS_le : S.card ≤ 2 * r - 1 := by omega
  have h_erase2_card : 2 * r - 1 ≤ ((I.erase y0).erase z0).card := by
    have hz0_mem_erase : z0 ∈ I.erase y0 := Finset.mem_erase.mpr ⟨hz0_ne_y0, hz0I⟩
    rw [Finset.card_erase_of_mem hz0_mem_erase, Finset.card_erase_of_mem hy0I]
    omega
  obtain ⟨B, hSB, hB_sub, hB_card⟩ :=
    exists_superset_subset_card_eq hS_sub_erase hS_le h_erase2_card
  have hy0_notB : y0 ∉ B := by
    intro h_mem
    exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase (hB_sub h_mem))).1 rfl
  have hz0_notB : z0 ∉ B := by
    intro h_mem
    exact (Finset.mem_erase.mp (hB_sub h_mem)).1 rfl
  have hz0_not_ins : z0 ∉ insert y0 B := by
    rw [Finset.mem_insert, not_or]
    exact ⟨hz0_ne_y0, hz0_notB⟩
  let K : Finset (Fin m) := insert z0 (insert y0 B)
  have hK_card : K.card ≤ 2 * r + 1 := by
    rw [Finset.card_insert_of_notMem hz0_not_ins, Finset.card_insert_of_notMem hy0_notB, hB_card]
    omega
  obtain ⟨u', c', hg_eq⟩ := exists_affineEval_of_card_le hr hN hK_card
    (fun i => if i = y0 then (1 : ℝ) else if i = z0 then (-1 : ℝ) else 0)
  let g : Fin m → ℝ := fun i => (∑ k : Fin (2 * r), u' k * V i k) + c'
  have hg_B : ∀ i ∈ B, g i = 0 := by
    intro i hiB
    have hiK : i ∈ K := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hiB)
    have hiy0 : i ≠ y0 := fun h => hy0_notB (h ▸ hiB)
    have hiz0 : i ≠ z0 := fun h => hz0_notB (h ▸ hiB)
    have := hg_eq i hiK
    simpa [g, hiy0, hiz0] using this
  have hg_y0 : g y0 = 1 := by
    have hy0K : y0 ∈ K := Finset.mem_insert_of_mem (Finset.mem_insert_self y0 B)
    have := hg_eq y0 hy0K
    simpa [g] using this
  have hg_z0 : g z0 = -1 := by
    have hz0K : z0 ∈ K := Finset.mem_insert_self z0 (insert y0 B)
    have := hg_eq z0 hz0K
    simpa [g, hz0_ne_y0] using this
  let J_pos : Finset (Fin m) := (I \ S).filter (fun j => 0 < g j)
  have hJ_pos_ne : J_pos.Nonempty := by
    refine ⟨y0, Finset.mem_filter.mpr ⟨hy0, ?_⟩⟩
    linarith
  obtain ⟨x, hx_mem, hx_min⟩ := Finset.exists_min_image J_pos (fun j => f j / g j) hJ_pos_ne
  have hx_sdiff : x ∈ I \ S := (Finset.mem_filter.mp hx_mem).1
  have hgx_pos : 0 < g x := (Finset.mem_filter.mp hx_mem).2
  have hfx_pos : 0 < f x := hpos x hx_sdiff
  let u'' : Fin (2 * r) → ℝ := fun k => g x * u k - f x * u' k
  let c'' : ℝ := g x * c - f x * c'
  let h : Fin m → ℝ := fun i => (∑ k : Fin (2 * r), u'' k * V i k) + c''
  have hh_eq : ∀ i : Fin m, h i = g x * f i - f x * g i := by
    intro i
    simp only [h, u'', c'', f, g, sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  let S' : Finset (Fin m) := I.filter (fun i => h i = 0)
  have hSS' : S ⊆ S' := by
    intro i hiS
    refine Finset.mem_filter.mpr ⟨hSI hiS, ?_⟩
    have hfi : f i = 0 := hS0 i hiS
    rw [hh_eq, hfi, hg_B i (hSB hiS)]
    ring
  have hxS' : x ∈ S' := by
    refine Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hx_sdiff).1, ?_⟩
    rw [hh_eq]
    ring
  have hx_notS : x ∉ S := (Finset.mem_sdiff.mp hx_sdiff).2
  have hS_lt_S' : S.card < S'.card := by
    have h_ins_sub : insert x S ⊆ S' := Finset.insert_subset_iff.mpr ⟨hxS', hSS'⟩
    calc S.card < (insert x S).card := by rw [Finset.card_insert_of_notMem hx_notS]; omega
      _ ≤ S'.card := Finset.card_le_card h_ins_sub
  have hz0_notS' : z0 ∉ S' := by
    intro hz0S'
    have hhz0 : h z0 = 0 := (Finset.mem_filter.mp hz0S').2
    have hfz0_pos : 0 < f z0 := hpos z0 hz0_sdiff
    rw [hh_eq, hg_z0] at hhz0
    nlinarith
  have hS'_ne_I : S' ≠ I := by
    intro h_eq
    exact hz0_notS' (h_eq ▸ hz0I)
  refine ⟨S', hSS', hS_lt_S', hS'_ne_I, ?_⟩
  refine ⟨Finset.filter_subset _ I, u'', c'', ?_, ?_⟩
  · intro i hiS'
    exact (Finset.mem_filter.mp hiS').2
  · intro j hj
    rw [Finset.mem_sdiff] at hj
    have hjI : j ∈ I := hj.1
    have hj_ne0 : h j ≠ 0 := by
      intro h0
      exact hj.2 (Finset.mem_filter.mpr ⟨hjI, h0⟩)
    have hj_notS : j ∉ S := fun hjS => hj.2 (hSS' hjS)
    have hj_sdiff : j ∈ I \ S := Finset.mem_sdiff.mpr ⟨hjI, hj_notS⟩
    have hfj_pos : 0 < f j := hpos j hj_sdiff
    change 0 < h j
    by_cases hgj_pos : 0 < g j
    · have hj_Jpos : j ∈ J_pos := Finset.mem_filter.mpr ⟨hj_sdiff, hgj_pos⟩
      have h_div_le : f x / g x ≤ f j / g j := hx_min j hj_Jpos
      have h_mul_le : f x * g j ≤ f j * g x := (div_le_div_iff₀ hgx_pos hgj_pos).mp h_div_le
      have h_nonneg : 0 ≤ h j := by
        rw [hh_eq]
        linarith
      exact lt_of_le_of_ne h_nonneg (Ne.symm hj_ne0)
    · have hgj_le : g j ≤ 0 := not_lt.mp hgj_pos
      rw [hh_eq]
      nlinarith

/-- Every proper affine-exposed subset `S ⊂ I` (when `2 * r + 1 ≤ I.card`) is contained in an
affine-exposed subset `F ⊆ I` of cardinality `2 * r`. -/
lemma exists_facet_superset_of_proper_isAffineExposed {r m : ℕ} (hr : 1 ≤ r)
    {V : Fin m → (Fin (2 * r) → ℝ)} (hN : IsRNeighborlyOn V r Finset.univ)
    {I : Finset (Fin m)} (hI : 2 * r + 1 ≤ I.card) :
    ∀ (k : ℕ) (S : Finset (Fin m)), 2 * r - S.card ≤ k →
      IsAffineExposed V I S → S ≠ I →
      ∃ F : Finset (Fin m), F ⊆ I ∧ F.card = 2 * r ∧ S ⊆ F ∧ IsAffineExposed V I F
  | 0, S, hk, hS, hSne => by
    have h_le := proper_isAffineExposed_card_le hr hN hS hSne
    have h_eq : S.card = 2 * r := by omega
    exact ⟨S, hS.1, h_eq, Finset.Subset.refl S, hS⟩
  | k + 1, S, hk, hS, hSne => by
    have h_le := proper_isAffineExposed_card_le hr hN hS hSne
    by_cases h_eq : S.card = 2 * r
    · exact ⟨S, hS.1, h_eq, Finset.Subset.refl S, hS⟩
    · have h_lt : S.card < 2 * r := lt_of_le_of_ne h_le h_eq
      obtain ⟨S', hSS', hS_lt_S', hS'_ne, hS'_exp⟩ :=
        exists_strict_superset_isAffineExposed hr hN hI hS h_lt
      have hk' : 2 * r - S'.card ≤ k := by omega
      obtain ⟨F, hFI, hF_card, hS'F, hF_exp⟩ :=
        exists_facet_superset_of_proper_isAffineExposed hr hN hI k S' hk' hS'_exp hS'_ne
      exact ⟨F, hFI, hF_card, hSS'.trans hS'F, hF_exp⟩

/-- Facet reduction: when `2 * r + 1 ≤ I.card`, a proper subset `S ⊂ I` is affine-exposed in `I`
if and only if it is contained in an affine-exposed subset `F ⊆ I` of cardinality `2 * r`. -/
lemma proper_isAffineExposed_iff_exists_facet {r m : ℕ} (hr : 1 ≤ r)
    {V : Fin m → (Fin (2 * r) → ℝ)} (hN : IsRNeighborlyOn V r Finset.univ)
    {I S : Finset (Fin m)} (hI : 2 * r + 1 ≤ I.card) (hSne : S ≠ I) :
    IsAffineExposed V I S ↔
      ∃ F : Finset (Fin m), F ⊆ I ∧ F.card = 2 * r ∧ S ⊆ F ∧ IsAffineExposed V I F := by
  constructor
  · intro hS
    exact exists_facet_superset_of_proper_isAffineExposed hr hN hI (2 * r - S.card) S
      (le_refl _) hS hSne
  · rintro ⟨F, _, hF_card, hSF, hF_exp⟩
    exact isAffineExposed_of_subset_facet hr hN hF_exp (by omega) hSF

/-- Single-vertex deletion formula for facets of size `2 * r`. -/
lemma facet_erase_iff {r m : ℕ} (hr : 1 ≤ r)
    {V : Fin m → (Fin (2 * r) → ℝ)} (hN : IsRNeighborlyOn V r Finset.univ)
    {I F : Finset (Fin m)} {v : Fin m} (hv : v ∈ I)
    (hI' : 2 * r + 1 ≤ (I.erase v).card)
    (hFI' : F ⊆ I.erase v) (hF_card : F.card = 2 * r) :
    IsAffineExposed V (I.erase v) F ↔
      IsAffineExposed V I F ∨
        (∀ A : Finset (Fin m), A ⊆ F → A.card = r → IsAffineExposed V I (insert v A)) := by
  classical
  have hv_notF : v ∉ F := fun hvF => (Finset.mem_erase.mp (hFI' hvF)).1 rfl
  have hFI : F ⊆ I := hFI'.trans (Finset.erase_subset v I)
  have h_ins_card : (insert v F).card = 2 * r + 1 := by
    rw [Finset.card_insert_of_notMem hv_notF, hF_card]
  constructor
  · rintro ⟨_, u, c, hF0, hpos⟩
    let f : Fin m → ℝ := fun i => (∑ k : Fin (2 * r), u k * V i k) + c
    have hfv_ne0 : f v ≠ 0 := by
      intro hfv0
      have h_all0 : ∀ i ∈ insert v F, f i = 0 := by
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hiF
        · exact hfv0
        · exact hF0 i hiF
      obtain ⟨hu, hc⟩ := affineEval_eq_zero_of_card_eq hr hN h_ins_card h_all0
      have h_sdiff_ne : (I.erase v \ F).Nonempty := by
        rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_eq_left.mpr hFI']
        omega
      rcases h_sdiff_ne with ⟨j0, hj0⟩
      have hj0_pos := hpos j0 hj0
      simp [hu, hc] at hj0_pos
    rcases lt_or_gt_of_ne hfv_ne0 with hfv_neg | hfv_pos
    · right
      intro A hAF hA_card
      have hA_exp : IsAffineExposed V I A :=
        (hN.2 A (Finset.subset_univ A) hA_card).mono (hAF.trans hFI) (Finset.subset_univ I)
      rcases hA_exp with ⟨hAI, u', c', hA0, hg_pos⟩
      let g : Fin m → ℝ := fun i => (∑ k : Fin (2 * r), u' k * V i k) + c'
      have hv_notA : v ∉ A := fun hvA => hv_notF (hAF hvA)
      have hgv_pos : 0 < g v := hg_pos v (Finset.mem_sdiff.mpr ⟨hv, hv_notA⟩)
      let u'' : Fin (2 * r) → ℝ := fun k => (- f v) * u' k + g v * u k
      let c'' : ℝ := (- f v) * c' + g v * c
      have h_comb : ∀ i : Fin m,
          (∑ k : Fin (2 * r), u'' k * V i k) + c'' = (- f v) * g i + g v * f i := by
        intro i
        simp only [u'', c'', f, g, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
      refine ⟨Finset.insert_subset_iff.mpr ⟨hv, hAI⟩, u'', c'', ?_, ?_⟩
      · intro i hi
        rw [h_comb]
        rcases Finset.mem_insert.mp hi with rfl | hiA
        · ring
        · have hgi : g i = 0 := hA0 i hiA
          have hfi : f i = 0 := hF0 i (hAF hiA)
          rw [hgi, hfi]
          ring
      · intro j hj
        rw [h_comb]
        rw [Finset.mem_sdiff, Finset.mem_insert, not_or] at hj
        have hjI : j ∈ I := hj.1
        have hj_ne_v : j ≠ v := hj.2.1
        have hj_notA : j ∉ A := hj.2.2
        have hgj_pos : 0 < g j := hg_pos j (Finset.mem_sdiff.mpr ⟨hjI, hj_notA⟩)
        have hfj_nonneg : 0 ≤ f j := by
          by_cases hjF : j ∈ F
          · exact le_of_eq (hF0 j hjF).symm
          · have hj_erase : j ∈ I.erase v \ F :=
              Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hj_ne_v, hjI⟩, hjF⟩
            exact le_of_lt (hpos j hj_erase)
        nlinarith
    · left
      refine ⟨hFI, u, c, hF0, ?_⟩
      intro j hj
      rw [Finset.mem_sdiff] at hj
      by_cases hjv : j = v
      · subst hjv
        exact hfv_pos
      · exact hpos j (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hjv, hj.1⟩, hj.2⟩)
  · rintro (hF_I | hA_all)
    · exact hF_I.mono hFI' (Finset.erase_subset v I)
    · let K : Finset (Fin m) := insert v F
      obtain ⟨u, c, hf_eq⟩ := exists_affineEval_of_card_le hr hN (le_of_eq h_ins_card)
        (fun i => if i = v then (-1 : ℝ) else 0)
      let f : Fin m → ℝ := fun i => (∑ k : Fin (2 * r), u k * V i k) + c
      have hf_F : ∀ i ∈ F, f i = 0 := by
        intro i hiF
        have hiK : i ∈ K := Finset.mem_insert_of_mem hiF
        have hiv : i ≠ v := fun h => hv_notF (h ▸ hiF)
        have := hf_eq i hiK
        simpa [f, hiv] using this
      have hf_v : f v = -1 := by
        have hvK : v ∈ K := Finset.mem_insert_self v F
        have := hf_eq v hvK
        simpa [f] using this
      refine ⟨hFI', u, c, hf_F, ?_⟩
      intro x hx
      rw [Finset.mem_sdiff] at hx
      have hx_erase : x ∈ I.erase v := hx.1
      have hx_notF : x ∉ F := hx.2
      have hxv : x ≠ v := (Finset.mem_erase.mp hx_erase).1
      have hxI : x ∈ I := (Finset.mem_erase.mp hx_erase).2
      have hx_notK : x ∉ K := by
        rw [Finset.mem_insert, not_or]
        exact ⟨hxv, hx_notF⟩
      change 0 < f x
      by_contra h_not_pos
      push_neg at h_not_pos
      have hfx_ne0 : f x ≠ 0 := by
        intro hfx0
        have h_ins_x_card : (insert x F).card = 2 * r + 1 := by
          rw [Finset.card_insert_of_notMem hx_notF, hF_card]
        have h_all0 : ∀ i ∈ insert x F, f i = 0 := by
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hiF
          · exact hfx0
          · exact hf_F i hiF
        obtain ⟨hu, hc⟩ := affineEval_eq_zero_of_card_eq hr hN h_ins_x_card h_all0
        have hfv0 : f v = 0 := by simp [f, hu, hc]
        linarith
      have hfx_neg : f x < 0 := lt_of_le_of_ne h_not_pos hfx_ne0
      obtain ⟨w, hw⟩ :=
        (evalKTranspose_bijective_of_card_eq hr hN h_ins_card).2 (V x, 1)
      have hw_vec : ∑ i : K, w i • V i.val = V x := congrArg Prod.fst hw
      have hw_sum : ∑ i : K, w i = 1 := congrArg Prod.snd hw
      let a : Fin m → ℝ := fun i =>
        if i = x then -1 else if h : i ∈ K then w ⟨i, h⟩ else 0
      have ha_x : a x = -1 := by simp [a]
      have ha_K : ∀ i (hi : i ∈ K), a i = w ⟨i, hi⟩ := by
        intro i hi
        have hix : i ≠ x := fun h => hx_notK (h ▸ hi)
        simp [a, hix, hi]
      have ha_supp : ∀ i, i ∉ insert x K → a i = 0 := by
        intro i hi
        rw [Finset.mem_insert, not_or] at hi
        simp [a, hi.1, hi.2]
      have ha_sum_K : ∑ i ∈ K, a i = 1 := by
        rw [← Finset.sum_attach K, ← Finset.univ_eq_attach]
        have h_congr : ∑ i : K, a i.val = ∑ i : K, w i :=
          Finset.sum_congr rfl (fun i _ => ha_K i.val i.property)
        rw [h_congr, hw_sum]
      have ha_vec_K : ∑ i ∈ K, a i • V i = V x := by
        rw [← Finset.sum_attach K, ← Finset.univ_eq_attach]
        have h_congr : ∑ i : K, a i.val • V i.val = ∑ i : K, w i • V i.val :=
          Finset.sum_congr rfl (fun i _ => by rw [ha_K i.val i.property])
        rw [h_congr, hw_vec]
      have ha_sum : ∑ i : Fin m, a i = 0 := by
        have h1 : ∑ i : Fin m, a i = ∑ i ∈ insert x K, a i := by
          refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
          intro i _ hi
          exact ha_supp i hi
        rw [h1, Finset.sum_insert hx_notK, ha_x, ha_sum_K]
        ring
      have ha_vec : ∑ i : Fin m, a i • V i = 0 := by
        have h1 : ∑ i : Fin m, a i • V i = ∑ i ∈ insert x K, a i • V i := by
          refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
          intro i _ hi
          simp [ha_supp i hi]
        rw [h1, Finset.sum_insert hx_notK, ha_x, ha_vec_K, neg_one_smul, neg_add_cancel]
      have ha_ne : ∃ i, a i ≠ 0 := ⟨x, by linarith⟩
      have h_eval_f := affine_dep_eval_zero ha_sum ha_vec u c
      have h_eval_f_split :
          ∑ i : Fin m, a i * f i = a x * f x + a v * f v := by
        have h1 : ∑ i : Fin m, a i * f i = ∑ i ∈ insert x K, a i * f i := by
          refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
          intro i _ hi
          simp [ha_supp i hi]
        have h2 : ∑ i ∈ F, a i * f i = 0 :=
          Finset.sum_eq_zero (fun i hiF => by simp [hf_F i hiF])
        rw [h1, Finset.sum_insert hx_notK, Finset.sum_insert hv_notF, h2, add_zero]
      have hav_pos : 0 < a v := by
        rw [h_eval_f_split, ha_x, hf_v] at h_eval_f
        linarith
      obtain ⟨h_pos_card, h_neg_card⟩ :=
        neighborly_affine_dep_pos_neg_card hr hN ha_ne ha_sum ha_vec
      set C_pos := Finset.univ.filter (fun i => 0 < a i)
      set C_neg := Finset.univ.filter (fun i => a i < 0)
      have h_disj : Disjoint C_pos C_neg := by
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        have h1 : 0 < a i := (Finset.mem_filter.mp hi1).2
        have h2 : a i < 0 := (Finset.mem_filter.mp hi2).2
        linarith
      have h_sub : C_pos ∪ C_neg ⊆ insert x K := by
        intro i hi
        by_contra hi_not
        have hai0 := ha_supp i hi_not
        rcases Finset.mem_union.mp hi with hi1 | hi2
        · have h1 : 0 < a i := (Finset.mem_filter.mp hi1).2; linarith
        · have h2 : a i < 0 := (Finset.mem_filter.mp hi2).2; linarith
      have h_ins_xK_card : (insert x K).card = 2 * r + 2 := by
        rw [Finset.card_insert_of_notMem hx_notK, h_ins_card]
      have h_union_le : C_pos.card + C_neg.card ≤ 2 * r + 2 := by
        rw [← Finset.card_union_of_disjoint h_disj, ← h_ins_xK_card]
        exact Finset.card_le_card h_sub
      have hC_pos_card : C_pos.card = r + 1 := by omega
      have hv_Cpos : v ∈ C_pos := Finset.mem_filter.mpr ⟨Finset.mem_univ v, hav_pos⟩
      have hx_not_Cpos : x ∉ C_pos := by
        intro hx_in
        have : 0 < a x := (Finset.mem_filter.mp hx_in).2
        linarith
      let A : Finset (Fin m) := C_pos.erase v
      have hAF : A ⊆ F := by
        intro i hiA
        have hiv : i ≠ v := (Finset.mem_erase.mp hiA).1
        have hi_Cpos : i ∈ C_pos := (Finset.mem_erase.mp hiA).2
        have hi_ins : i ∈ insert x (insert v F) :=
          h_sub (Finset.mem_union_left C_neg hi_Cpos)
        rcases Finset.mem_insert.mp hi_ins with rfl | hi_K
        · exact False.elim (hx_not_Cpos hi_Cpos)
        · rcases Finset.mem_insert.mp hi_K with rfl | hiF
          · exact False.elim (hiv rfl)
          · exact hiF
      have hA_card : A.card = r := by
        rw [Finset.card_erase_of_mem hv_Cpos, hC_pos_card]
        omega
      have h_ins_vA : insert v A = C_pos := Finset.insert_erase hv_Cpos
      have hC_pos_exp : IsAffineExposed V I C_pos := by
        rw [← h_ins_vA]
        exact hA_all A hAF hA_card
      rcases hC_pos_exp with ⟨_, u', c', hC0, hg_pos⟩
      let g : Fin m → ℝ := fun i => (∑ k : Fin (2 * r), u' k * V i k) + c'
      have hg_sum : ∑ i : Fin m, a i * g i = 0 :=
        affine_dep_eval_zero ha_sum ha_vec u' c'
      have hg_nonpos : ∀ i ∈ Finset.univ, a i * g i ≤ 0 := by
        intro i _
        by_cases hi_ins : i ∈ insert x K
        · by_cases hi_Cpos : i ∈ C_pos
          · have hgi : g i = 0 := hC0 i hi_Cpos
            rw [hgi, mul_zero]
          · have hiI : i ∈ I := by
              rcases Finset.mem_insert.mp hi_ins with rfl | hiK
              · exact hxI
              · rcases Finset.mem_insert.mp hiK with rfl | hiF
                · exact hv
                · exact hFI hiF
            have hgi_pos : 0 < g i := hg_pos i (Finset.mem_sdiff.mpr ⟨hiI, hi_Cpos⟩)
            have hai_le : a i ≤ 0 := by
              by_contra h_pos
              push_neg at h_pos
              exact hi_Cpos (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h_pos⟩)
            exact mul_nonpos_of_nonpos_of_nonneg hai_le (le_of_lt hgi_pos)
        · rw [ha_supp i hi_ins, zero_mul]
      have hgx_pos : 0 < g x := hg_pos x (Finset.mem_sdiff.mpr ⟨hxI, hx_not_Cpos⟩)
      have hx_strict : a x * g x < 0 := by
        rw [ha_x]
        linarith
      have h_le_sum := Finset.single_le_sum
        (f := fun i => -(a i * g i))
        (fun i hi => neg_nonneg.mpr (hg_nonpos i hi))
        (Finset.mem_univ x)
      rw [Finset.sum_neg_distrib, hg_sum, neg_zero] at h_le_sum
      linarith

/-- Single-vertex deletion preserves matching `IsAffineExposed` subsets as long as at least
`2 * r + 1` vertices remain. -/
lemma same_isAffineExposed_erase {r m : ℕ} (hr : 1 ≤ r)
    {V W : Fin m → (Fin (2 * r) → ℝ)}
    (hNV : IsRNeighborlyOn V r Finset.univ)
    (hNW : IsRNeighborlyOn W r Finset.univ)
    (θ : Equiv.Perm (Fin m))
    {I : Finset (Fin m)} {v : Fin m} (hv : v ∈ I)
    (hI' : 2 * r + 1 ≤ (I.erase v).card)
    (h_same : ∀ S : Finset (Fin m),
      IsAffineExposed V I S ↔ IsAffineExposed W (I.map θ.toEmbedding) (S.map θ.toEmbedding)) :
    ∀ S : Finset (Fin m),
      IsAffineExposed V (I.erase v) S ↔
        IsAffineExposed W ((I.erase v).map θ.toEmbedding) (S.map θ.toEmbedding) := by
  classical
  have h_map_erase :
      (I.erase v).map θ.toEmbedding = (I.map θ.toEmbedding).erase (θ v) := by
    ext j
    simp only [Finset.mem_map, Finset.mem_erase, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨i, ⟨hiv, hiI⟩, rfl⟩
      exact ⟨θ.injective.ne hiv, i, hiI, rfl⟩
    · rintro ⟨hjv, i, hiI, rfl⟩
      exact ⟨i, ⟨fun h => hjv (congrArg θ h), hiI⟩, rfl⟩
  have hθv : θ v ∈ I.map θ.toEmbedding := Finset.mem_map.mpr ⟨v, hv, rfl⟩
  have hI'_W : 2 * r + 1 ≤ ((I.map θ.toEmbedding).erase (θ v)).card := by
    rw [← h_map_erase, Finset.card_map]
    exact hI'
  have h_facets : ∀ F : Finset (Fin m), F ⊆ I.erase v → F.card = 2 * r →
      (IsAffineExposed V (I.erase v) F ↔
        IsAffineExposed W ((I.erase v).map θ.toEmbedding) (F.map θ.toEmbedding)) := by
    intro F hFI' hF_card
    have hF_W_sub : F.map θ.toEmbedding ⊆ (I.map θ.toEmbedding).erase (θ v) := by
      rw [← h_map_erase]
      exact Finset.map_subset_map.mpr hFI'
    have hF_W_card : (F.map θ.toEmbedding).card = 2 * r := by
      rw [Finset.card_map, hF_card]
    rw [h_map_erase,
      facet_erase_iff hr hNV hv hI' hFI' hF_card,
      facet_erase_iff hr hNW hθv hI'_W hF_W_sub hF_W_card]
    refine or_congr (h_same F) ?_
    constructor
    · intro hA A' hA'F hA'_card
      let A : Finset (Fin m) := A'.map θ.symm.toEmbedding
      have hA_map : A.map θ.toEmbedding = A' := by
        ext j; simp [A]
      have hAF : A ⊆ F := by
        rw [← Finset.map_subset_map (f := θ.toEmbedding), hA_map]
        exact hA'F
      have hA_card : A.card = r := by
        rw [← Finset.card_map θ.toEmbedding, hA_map, hA'_card]
      have h_ins_map : (insert v A).map θ.toEmbedding = insert (θ v) A' := by
        rw [Finset.map_insert, Equiv.toEmbedding_apply, hA_map]
      rw [← h_ins_map]
      exact (h_same (insert v A)).mp (hA A hAF hA_card)
    · intro hA' A hAF hA_card
      have hA_map_sub : A.map θ.toEmbedding ⊆ F.map θ.toEmbedding :=
        Finset.map_subset_map.mpr hAF
      have hA_map_card : (A.map θ.toEmbedding).card = r := by
        rw [Finset.card_map, hA_card]
      have h_ins_map : (insert v A).map θ.toEmbedding = insert (θ v) (A.map θ.toEmbedding) := by
        rw [Finset.map_insert, Equiv.toEmbedding_apply]
      apply (h_same (insert v A)).mpr
      rw [h_ins_map]
      exact hA' (A.map θ.toEmbedding) hA_map_sub hA_map_card
  intro S
  by_cases hSI' : S ⊆ I.erase v
  · by_cases hS_eq : S = I.erase v
    · subst hS_eq
      exact ⟨fun _ => isAffineExposed_self W _, fun _ => isAffineExposed_self V _⟩
    · have hSW_ne : S.map θ.toEmbedding ≠ (I.erase v).map θ.toEmbedding :=
        fun h_eq => hS_eq (Finset.map_injective θ.toEmbedding h_eq)
      have hI'_W_card : 2 * r + 1 ≤ ((I.erase v).map θ.toEmbedding).card := by
        rw [Finset.card_map]
        exact hI'
      rw [proper_isAffineExposed_iff_exists_facet hr hNV hI' hS_eq,
        proper_isAffineExposed_iff_exists_facet hr hNW hI'_W_card hSW_ne]
      constructor
      · rintro ⟨F, hFI', hF_card, hSF, hF_exp⟩
        refine ⟨F.map θ.toEmbedding, Finset.map_subset_map.mpr hFI', ?_,
          Finset.map_subset_map.mpr hSF, (h_facets F hFI' hF_card).mp hF_exp⟩
        rw [Finset.card_map, hF_card]
      · rintro ⟨F', hF'I', hF'_card, hSF', hF'_exp⟩
        let F : Finset (Fin m) := F'.map θ.symm.toEmbedding
        have hF_map : F.map θ.toEmbedding = F' := by
          ext j; simp [F]
        have hFI' : F ⊆ I.erase v := by
          rw [← Finset.map_subset_map (f := θ.toEmbedding), hF_map]
          exact hF'I'
        have hF_card : F.card = 2 * r := by
          rw [← Finset.card_map θ.toEmbedding, hF_map, hF'_card]
        have hSF : S ⊆ F := by
          rw [← Finset.map_subset_map (f := θ.toEmbedding), hF_map]
          exact hSF'
        refine ⟨F, hFI', hF_card, hSF, (h_facets F hFI' hF_card).mpr ?_⟩
        rwa [hF_map]
  · constructor
    · intro h
      exact False.elim (hSI' h.1)
    · intro h
      have hSW_sub : S.map θ.toEmbedding ⊆ (I.erase v).map θ.toEmbedding := h.1
      exact False.elim (hSI' (Finset.map_subset_map.mp hSW_sub))

/-- Downward induction on `m - I.card` from `Finset.univ` to any `I` with `2 * r + 1 ≤ I.card`. -/
lemma same_isAffineExposed_of_card_ge {r m : ℕ} (hr : 1 ≤ r)
    {V W : Fin m → (Fin (2 * r) → ℝ)}
    (hNV : IsRNeighborlyOn V r Finset.univ)
    (hNW : IsRNeighborlyOn W r Finset.univ)
    (θ : Equiv.Perm (Fin m))
    (h_univ : ∀ S : Finset (Fin m),
      IsAffineExposed V Finset.univ S ↔
        IsAffineExposed W (Finset.univ.map θ.toEmbedding) (S.map θ.toEmbedding)) :
    ∀ (k : ℕ) (I : Finset (Fin m)),
      (Finset.univ : Finset (Fin m)).card - I.card ≤ k →
      2 * r + 1 ≤ I.card →
      ∀ S : Finset (Fin m),
        IsAffineExposed V I S ↔
          IsAffineExposed W (I.map θ.toEmbedding) (S.map θ.toEmbedding)
  | 0, I, hk, _, S => by
    have h_card_le : I.card ≤ (Finset.univ : Finset (Fin m)).card :=
      Finset.card_le_card (Finset.subset_univ I)
    have h_card_eq : I.card = (Finset.univ : Finset (Fin m)).card := by omega
    have hI_eq : I = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.subset_univ I) (le_of_eq h_card_eq.symm)
    subst hI_eq
    exact h_univ S
  | k + 1, I, hk, hI, S => by
    classical
    by_cases hI_eq : I = Finset.univ
    · subst hI_eq
      exact h_univ S
    · have h_compl_ne : (Finset.univ \ I).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty, Ne.eq_def, Finset.sdiff_eq_empty_iff_subset]
        intro h_sub
        exact hI_eq (Finset.Subset.antisymm (Finset.subset_univ I) h_sub)
      rcases h_compl_ne with ⟨v, hv⟩
      have hv_notI : v ∉ I := (Finset.mem_sdiff.mp hv).2
      let J : Finset (Fin m) := insert v I
      have hvJ : v ∈ J := Finset.mem_insert_self v I
      have hJ_erase : J.erase v = I := Finset.erase_insert hv_notI
      have hJ_card : J.card = I.card + 1 := Finset.card_insert_of_notMem hv_notI
      have hI_lt : I.card < (Finset.univ : Finset (Fin m)).card :=
        Finset.card_lt_card (ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ I, hI_eq⟩)
      have hk' : (Finset.univ : Finset (Fin m)).card - J.card ≤ k := by omega
      have hJ_ge : 2 * r + 1 ≤ J.card := by omega
      have h_same_J := same_isAffineExposed_of_card_ge hr hNV hNW θ h_univ k J hk' hJ_ge
      have hI'_ge : 2 * r + 1 ≤ (J.erase v).card := by
        rw [hJ_erase]
        exact hI
      have h_same_erase := same_isAffineExposed_erase hr hNV hNW θ hvJ hI'_ge h_same_J S
      rwa [hJ_erase] at h_same_erase

end ShemerRigidity

open ShemerRigidity

/-- Shemer's rigidity theorem as stated in Grünbaum (2003), §7.5,
"Cyclic polytopes", printed p.129b / PDF161. -/
theorem neighborly_subpolytope_rigidity (r m : ℕ) (hr : 1 ≤ r)
    (P Q : Set (Fin (2 * r) → ℝ))
    (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (hPn : IsKNeighborly r P) (hQn : IsKNeighborly r Q)
    (V W : Fin m → (Fin (2 * r) → ℝ))
    (hVinj : Function.Injective V) (hWinj : Function.Injective W)
    (hV : Set.range V = {x | IsExposed ℝ P {x}})
    (hW : Set.range W = {x | IsExposed ℝ Q {x}})
    (θ : Equiv.Perm (Fin m)) (Φ : PolytopeFace P ≃o PolytopeFace Q)
    (hΦ : ∀ (i : Fin m) (F : PolytopeFace P),
      F.val = {V i} → (Φ F).val = {W (θ i)}) :
    ∀ I : Set (Fin m),
      ∃ Ψ : PolytopeFace (convexHull ℝ (V '' I)) ≃o
          PolytopeFace (convexHull ℝ (W '' (θ '' I))),
        ∀ (i : Fin m), i ∈ I →
          ∀ F : PolytopeFace (convexHull ℝ (V '' I)),
            F.val = {V i} → (Ψ F).val = {W (θ i)} := by
  classical
  have hNV : IsRNeighborlyOn V r Finset.univ := isRNeighborlyOn_univ hP hPn hVinj hV
  have hNW : IsRNeighborlyOn W r Finset.univ := isRNeighborlyOn_univ hQ hQn hWinj hW
  have hP_univ : convexHull ℝ (V '' ((Finset.univ : Finset (Fin m)) : Set (Fin m))) = P := by
    rw [Finset.coe_univ, Set.image_univ, ← P_eq_convexHull_range hP hV]
  have hQ_univ :
      convexHull ℝ (W '' (θ '' ((Finset.univ : Finset (Fin m)) : Set (Fin m)))) = Q := by
    have hθ_univ : θ '' ((Finset.univ : Finset (Fin m)) : Set (Fin m)) = Set.univ := by
      rw [Finset.coe_univ, Set.image_univ, θ.surjective.range_eq]
    rw [hθ_univ, Set.image_univ, ← P_eq_convexHull_range hQ hW]
  have h_univ : ∀ S : Finset (Fin m),
      IsAffineExposed V Finset.univ S ↔
        IsAffineExposed W (Finset.univ.map θ.toEmbedding) (S.map θ.toEmbedding) := by
    rw [← orderIso_subpolytope_iff_isAffineExposed hP hQ hVinj hWinj hV hW θ Finset.univ]
    rw [hP_univ, hQ_univ]
    exact ⟨Φ, fun i _ F hF => hΦ i F hF⟩
  intro I
  let Ifin : Finset (Fin m) := I.toFinset
  have hIfin_coe : (Ifin : Set (Fin m)) = I := Set.coe_toFinset I
  rw [← hIfin_coe, orderIso_subpolytope_iff_isAffineExposed hP hQ hVinj hWinj hV hW θ Ifin]
  by_cases hI_le : Ifin.card ≤ 2 * r + 1
  · intro S
    have hIW_le : (Ifin.map θ.toEmbedding).card ≤ 2 * r + 1 := by
      rw [Finset.card_map]
      exact hI_le
    rw [isAffineExposed_iff_subset_of_card_le hr hNV hI_le S,
      isAffineExposed_iff_subset_of_card_le hr hNW hIW_le (S.map θ.toEmbedding),
      Finset.map_subset_map]
  · push_neg at hI_le
    have hI_ge : 2 * r + 1 ≤ Ifin.card := by omega
    exact same_isAffineExposed_of_card_ge hr hNV hNW θ h_univ
      ((Finset.univ : Finset (Fin m)).card - Ifin.card) Ifin (le_refl _) hI_ge

end Grunbaum2003

open Grunbaum2003

/-- Submission entrypoint matching `neighborly_subpolytope_rigidity`. -/
theorem solution (r m : ℕ) (hr : 1 ≤ r)
    (P Q : Set (Fin (2 * r) → ℝ))
    (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (hPn : IsKNeighborly r P) (hQn : IsKNeighborly r Q)
    (V W : Fin m → (Fin (2 * r) → ℝ))
    (hVinj : Function.Injective V) (hWinj : Function.Injective W)
    (hV : Set.range V = {x | IsExposed ℝ P {x}})
    (hW : Set.range W = {x | IsExposed ℝ Q {x}})
    (θ : Equiv.Perm (Fin m)) (Φ : PolytopeFace P ≃o PolytopeFace Q)
    (hΦ : ∀ (i : Fin m) (F : PolytopeFace P),
      F.val = {V i} → (Φ F).val = {W (θ i)}) :
    ∀ I : Set (Fin m),
      ∃ Ψ : PolytopeFace (convexHull ℝ (V '' I)) ≃o
          PolytopeFace (convexHull ℝ (W '' (θ '' I))),
        ∀ (i : Fin m), i ∈ I →
          ∀ F : PolytopeFace (convexHull ℝ (V '' I)),
            F.val = {V i} → (Ψ F).val = {W (θ i)} :=
  neighborly_subpolytope_rigidity r m hr P Q hP hQ hPn hQn V W hVinj hWinj hV hW θ Φ hΦ
