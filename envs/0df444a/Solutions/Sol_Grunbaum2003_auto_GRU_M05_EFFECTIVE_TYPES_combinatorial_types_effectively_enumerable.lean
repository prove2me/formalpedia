-- Prove2me | solution 1 for Grunbaum2003.auto_GRU_M05_EFFECTIVE_TYPES_combinatorial_types_effectively_enumerable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T22:28:41.566528+00:00
-- url     : https://prove2.me/submissions/324e995e-0878-49b7-83f9-bfc01ade4d38
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_auto_GRU_M05_EFFECTIVE_TYPES_IsDPolytope
import Definitions.Def_auto_GRU_M05_EFFECTIVE_TYPES_faceCount
import Definitions.Def_auto_GRU_M05_EFFECTIVE_TYPES_PolytopeFace
import Definitions.Def_auto_GRU_M05_EFFECTIVE_TYPES_SchemeRealizes
import Theorems.Thm_Grunbaum2003_auto_GRU_M05_EFFECTIVE_TYPES_exists_computable_realizable_scheme_representatives
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Set.Card
import Mathlib.Computability.Partrec
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

lemma extremePoints_eq_exposedSingletons_m05 {d : ℕ} (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
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

theorem exists_scheme_realizing_dpolytope_m05 (d k : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) (hk : faceCount P 0 = k) :
    ∃ S : List (List ℕ), SchemeRealizes k S P := by
  classical
  rcases hP.1 with ⟨V0, hV0_fin, _, hP_eq⟩
  have hExtEq : P.extremePoints ℝ = {x : Fin d → ℝ | IsExposed ℝ P {x}} :=
    extremePoints_eq_exposedSingletons_m05 P hP
  have hVertFin : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite := by
    rw [← hExtEq, hP_eq]
    exact hV0_fin.subset extremePoints_convexHull_subset
  let V' := hVertFin.toFinset
  have hVertEq : {x : Fin d → ℝ | IsExposed ℝ P {x}} = (V' : Set (Fin d → ℝ)) :=
    (hVertFin.coe_toFinset).symm
  have hZeroFaces :
      {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = 0} =
      (fun x : Fin d → ℝ => ({x} : Set (Fin d → ℝ))) '' {x : Fin d → ℝ | IsExposed ℝ P {x}} := by
    ext F
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨⟨x, hxF⟩, hFe, hdim⟩
      have hsub : Subsingleton (affineSpan ℝ F).direction :=
        Module.finrank_zero_iff.mp hdim
      have hF_eq : F = {x} := by
        ext y
        simp only [Set.mem_singleton_iff]
        constructor
        · intro hyF
          have hyx : y - x ∈ (affineSpan ℝ F).direction := by
            rw [direction_affineSpan]
            exact vsub_mem_vectorSpan ℝ hyF hxF
          exact sub_eq_zero.mp (congr_arg Subtype.val (@Subsingleton.elim _ hsub ⟨y - x, hyx⟩ 0))
        · rintro rfl
          exact hxF
      subst hF_eq
      exact ⟨x, hFe, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨Set.singleton_nonempty x, hx, ?_⟩
      rw [direction_affineSpan, vectorSpan_singleton, finrank_bot]
  have hcard : V'.card = k := by
    have h1 : faceCount P 0 = V'.card := by
      unfold faceCount
      rw [hZeroFaces, Set.ncard_image_of_injective _ Set.singleton_injective,
        hVertEq, Set.ncard_coe_finset]
    omega
  let e : Fin k ≃ V' := (Finset.equivFinOfCardEq hcard).symm
  let V : Fin k → (Fin d → ℝ) := fun i => (e i).val
  have hV_inj : Function.Injective V := Subtype.val_injective.comp e.injective
  have hV_range : Set.range V = {x : Fin d → ℝ | IsExposed ℝ P {x}} := by
    rw [hVertEq]
    ext x
    simp only [Set.mem_range, Finset.mem_coe, V]
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp⟩
  let Fset : Finset (Finset ℕ) :=
    (Finset.range k).powerset.filter (fun J =>
      ∃ F : Set (Fin d → ℝ), IsExposed ℝ P F ∧ F.Nonempty ∧ F ≠ P ∧
        (J : Set ℕ) = {n | ∃ i : Fin k, i.val = n ∧ V i ∈ F})
  refine ⟨Fset.toList.map Finset.toList, hP, V, hV_inj, hV_range, ?_⟩
  intro J
  constructor
  · rintro ⟨L, hL, rfl⟩
    rw [List.mem_map] at hL
    rcases hL with ⟨J', hJ'mem, rfl⟩
    rw [Finset.mem_toList, Finset.mem_filter] at hJ'mem
    simpa [Finset.toList_toFinset] using hJ'mem.2
  · intro hJ
    have hJsub : J ⊆ Finset.range k := by
      rcases hJ with ⟨F, _, _, _, hJeq⟩
      intro n hn
      have hn' : n ∈ (J : Set ℕ) := hn
      rw [hJeq] at hn'
      rcases hn' with ⟨i, rfl, _⟩
      exact Finset.mem_range.mpr i.isLt
    have hJmem : J ∈ Fset := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hJsub, hJ⟩
    refine ⟨J.toList, ?_, Finset.toList_toFinset J⟩
    rw [List.mem_map]
    exact ⟨J, Finset.mem_toList.mpr hJmem, rfl⟩

theorem auto_GRU_M05_EFFECTIVE_TYPES_combinatorial_types_effectively_enumerable_sol :
    ∃ E : ℕ → ℕ → List (List (List ℕ)), Computable₂ E ∧
      ∀ d k : ℕ,
        (∀ S ∈ E d k, ∃ P : Set (Fin d → ℝ), SchemeRealizes k S P) ∧
        (∀ P : Set (Fin d → ℝ), IsDPolytope P → faceCount P 0 = k →
          ∃ S ∈ E d k, SchemeRealizes k S P) ∧
        (∀ i j : Fin (E d k).length,
          ∀ P Q : Set (Fin d → ℝ),
            SchemeRealizes k ((E d k).get i) P →
            SchemeRealizes k ((E d k).get j) Q →
            Nonempty (PolytopeFace P ≃o PolytopeFace Q) → i = j) := by
  obtain ⟨E, hComp, hProps⟩ :=
    auto_GRU_M05_EFFECTIVE_TYPES_exists_computable_realizable_scheme_representatives
  refine ⟨E, hComp, ?_⟩
  intro d k
  obtain ⟨hSound, hComplete, hUnique⟩ := hProps d k
  refine ⟨hSound, ?_, hUnique⟩
  intro P hP hk
  obtain ⟨S₀, hS₀⟩ := exists_scheme_realizing_dpolytope_m05 d k P hP hk
  obtain ⟨S, hSMem, hSImp⟩ := hComplete S₀ ⟨P, hS₀⟩
  exact ⟨S, hSMem, hSImp P hS₀⟩

end Grunbaum2003

theorem solution :
    ∃ E : ℕ → ℕ → List (List (List ℕ)), Computable₂ E ∧
      ∀ d k : ℕ,
        (∀ S ∈ E d k, ∃ P : Set (Fin d → ℝ), Grunbaum2003.SchemeRealizes k S P) ∧
        (∀ P : Set (Fin d → ℝ), Grunbaum2003.IsDPolytope P → Grunbaum2003.faceCount P 0 = k →
          ∃ S ∈ E d k, Grunbaum2003.SchemeRealizes k S P) ∧
        (∀ i j : Fin (E d k).length,
          ∀ P Q : Set (Fin d → ℝ),
            Grunbaum2003.SchemeRealizes k ((E d k).get i) P →
            Grunbaum2003.SchemeRealizes k ((E d k).get j) Q →
            Nonempty (Grunbaum2003.PolytopeFace P ≃o Grunbaum2003.PolytopeFace Q) → i = j) :=
  Grunbaum2003.auto_GRU_M05_EFFECTIVE_TYPES_combinatorial_types_effectively_enumerable_sol
