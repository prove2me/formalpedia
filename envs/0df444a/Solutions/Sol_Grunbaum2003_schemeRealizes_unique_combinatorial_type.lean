-- Prove2me | solution 1 for Grunbaum2003.schemeRealizes_unique_combinatorial_type
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T22:17:21.585665+00:00
-- url     : https://prove2.me/submissions/5fbfe9bb-18e8-4c17-83cd-9b70d2a4716b

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SchemeRealizes
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

lemma extremePoints_eq_exposedSingletons_sr {d : ℕ} (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
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

theorem polytope_face_eq_convexHull_exposed_vertices_sr (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ F : PolytopeFace P,
        F.val = convexHull ℝ (F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}) := by
  rcases hP.1 with ⟨V0, hV0_fin, _, hP_eq⟩
  have hExtEq : P.extremePoints ℝ = {x : Fin d → ℝ | IsExposed ℝ P {x}} :=
    extremePoints_eq_exposedSingletons_sr P hP
  have hVertFin : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite := by
    rw [← hExtEq, hP_eq]
    exact hV0_fin.subset extremePoints_convexHull_subset
  refine ⟨hVertFin, ?_⟩
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

noncomputable def schemeVertSet {d k : ℕ} {P : Set (Fin d → ℝ)}
    (V : Fin k → (Fin d → ℝ)) (F : PolytopeFace P) : Finset ℕ :=
  by
    classical
    exact (Finset.univ.filter (fun i : Fin k => V i ∈ F.val)).map ⟨Fin.val, Fin.val_injective⟩

theorem coe_schemeVertSet {d k : ℕ} {P : Set (Fin d → ℝ)}
    (V : Fin k → (Fin d → ℝ)) (F : PolytopeFace P) :
    (schemeVertSet V F : Set ℕ) = {n : ℕ | ∃ i : Fin k, i.val = n ∧ V i ∈ F.val} := by
  classical
  ext n
  simp [schemeVertSet, and_comm]

theorem schemeVertSet_le_iff {d k : ℕ} {P : Set (Fin d → ℝ)}
    (hPd : IsDPolytope P)
    (V : Fin k → (Fin d → ℝ)) (hV_range : Set.range V = {x | IsExposed ℝ P {x}})
    (F₁ F₂ : PolytopeFace P) :
    F₁ ≤ F₂ ↔ schemeVertSet V F₁ ⊆ schemeVertSet V F₂ := by
  constructor
  · intro hle n hn
    rw [ ← Finset.mem_coe, coe_schemeVertSet ] at hn ⊢
    rcases hn with ⟨i, rfl, hi⟩
    exact ⟨i, rfl, hle hi⟩
  · intro hsub
    have hHull := (polytope_face_eq_convexHull_exposed_vertices_sr d P hPd).2 F₁
    rw [← hV_range] at hHull
    obtain ⟨⟨Vset, _, _, hPhull⟩, _⟩ := hPd
    have hF2_conv : Convex ℝ F₂.val := by
      refine F₂.2.convex ?_
      rw [hPhull]
      exact convex_convexHull ℝ _
    change F₁.val ⊆ F₂.val
    rw [hHull]
    refine convexHull_min ?_ hF2_conv
    rintro x ⟨hxF1, i, rfl⟩
    have hi1 : i.val ∈ (schemeVertSet V F₁ : Set ℕ) := by
      rw [coe_schemeVertSet]
      exact ⟨i, rfl, hxF1⟩
    have hi2 : i.val ∈ (schemeVertSet V F₂ : Set ℕ) := hsub hi1
    rw [coe_schemeVertSet] at hi2
    rcases hi2 with ⟨j, hj, hjF2⟩
    have hij : j = i := Fin.ext hj
    subst hij
    exact hjF2

theorem mem_range_schemeVertSet_iff {d k : ℕ} {P : Set (Fin d → ℝ)} {S : List (List ℕ)}
    (V : Fin k → (Fin d → ℝ)) (hV_range : Set.range V = {x | IsExposed ℝ P {x}})
    (hS : ∀ J : Finset ℕ,
      (∃ L ∈ S, L.toFinset = J) ↔
        ∃ F : Set (Fin d → ℝ), IsExposed ℝ P F ∧ F.Nonempty ∧ F ≠ P ∧
          (J : Set ℕ) = {n | ∃ i : Fin k, i.val = n ∧ V i ∈ F})
    (J : Finset ℕ) :
    (∃ F : PolytopeFace P, schemeVertSet V F = J) ↔
      J = ∅ ∨ J = Finset.range k ∨ (∃ L ∈ S, L.toFinset = J) := by
  have hVP : ∀ i : Fin k, V i ∈ P := by
    intro i
    have hVi : V i ∈ Set.range V := Set.mem_range_self i
    rw [hV_range] at hVi
    exact hVi.subset (Set.mem_singleton (V i))
  have hTopSet : ({n : ℕ | ∃ i : Fin k, i.val = n ∧ V i ∈ P} : Set ℕ) =
      (Finset.range k : Set ℕ) := by
    ext n
    simp only [Set.mem_setOf_eq, Finset.coe_range, Set.mem_Iio]
    constructor
    · rintro ⟨i, rfl, _⟩
      exact i.isLt
    · intro hn
      exact ⟨⟨n, hn⟩, rfl, hVP ⟨n, hn⟩⟩
  constructor
  · rintro ⟨F, rfl⟩
    rcases F.val.eq_empty_or_nonempty with hEmp | hNe
    · left
      rw [← Finset.coe_inj, coe_schemeVertSet, hEmp]
      simp
    · by_cases hFP : F.val = P
      · right; left
        rw [← Finset.coe_inj, coe_schemeVertSet, hFP, hTopSet]
      · right; right
        rw [hS]
        exact ⟨F.val, F.2, hNe, hFP, coe_schemeVertSet V F⟩
  · rintro (rfl | rfl | hLS)
    · refine ⟨⟨∅, fun h => (Set.not_nonempty_empty h).elim⟩, ?_⟩
      rw [← Finset.coe_inj, coe_schemeVertSet]
      simp
    · refine ⟨⟨P, fun _ => ⟨0, by simp⟩⟩, ?_⟩
      rw [← Finset.coe_inj, coe_schemeVertSet, hTopSet]
    · obtain ⟨Fset, hFe, _, _, hJeq⟩ := (hS J).mp hLS
      refine ⟨⟨Fset, hFe⟩, ?_⟩
      rw [← Finset.coe_inj, coe_schemeVertSet, hJeq]

/-- Grünbaum (2003), §3.2 & §5.5 (Theorem 5.5.2, p. 91): any two polytopes that realize
the same vertex-face incidence scheme `S` on `k` vertices have order-isomorphic face posets. -/
theorem schemeRealizes_unique_combinatorial_type (d₁ d₂ k : ℕ) (S : List (List ℕ))
    (P : Set (Fin d₁ → ℝ)) (Q : Set (Fin d₂ → ℝ))
    (hP : SchemeRealizes k S P) (hQ : SchemeRealizes k S Q) :
    Nonempty (PolytopeFace P ≃o PolytopeFace Q) := by
  classical
  rcases hP with ⟨hPd, VP, _, hVP_range, hSP⟩
  rcases hQ with ⟨hQd, VQ, _, hVQ_range, hSQ⟩
  have hFwd : ∀ F : PolytopeFace P, ∃ G : PolytopeFace Q,
      schemeVertSet VQ G = schemeVertSet VP F := by
    intro F
    rw [mem_range_schemeVertSet_iff VQ hVQ_range hSQ,
      ← mem_range_schemeVertSet_iff VP hVP_range hSP]
    exact ⟨F, rfl⟩
  have hBwd : ∀ G : PolytopeFace Q, ∃ F : PolytopeFace P,
      schemeVertSet VP F = schemeVertSet VQ G := by
    intro G
    rw [mem_range_schemeVertSet_iff VP hVP_range hSP,
      ← mem_range_schemeVertSet_iff VQ hVQ_range hSQ]
    exact ⟨G, rfl⟩
  let toFun : PolytopeFace P → PolytopeFace Q := fun F => Classical.choose (hFwd F)
  have htoFun : ∀ F : PolytopeFace P, schemeVertSet VQ (toFun F) = schemeVertSet VP F :=
    fun F => Classical.choose_spec (hFwd F)
  let invFun : PolytopeFace Q → PolytopeFace P := fun G => Classical.choose (hBwd G)
  have hinvFun : ∀ G : PolytopeFace Q, schemeVertSet VP (invFun G) = schemeVertSet VQ G :=
    fun G => Classical.choose_spec (hBwd G)
  have hLeft : Function.LeftInverse invFun toFun := by
    intro F
    apply le_antisymm
    · rw [schemeVertSet_le_iff hPd VP hVP_range, hinvFun, htoFun]
    · rw [schemeVertSet_le_iff hPd VP hVP_range, hinvFun, htoFun]
  have hRight : Function.RightInverse invFun toFun := by
    intro G
    apply le_antisymm
    · rw [schemeVertSet_le_iff hQd VQ hVQ_range, htoFun, hinvFun]
    · rw [schemeVertSet_le_iff hQd VQ hVQ_range, htoFun, hinvFun]
  exact ⟨{
    toFun := toFun
    invFun := invFun
    left_inv := hLeft
    right_inv := hRight
    map_rel_iff' := by
      intro F₁ F₂
      change toFun F₁ ≤ toFun F₂ ↔ F₁ ≤ F₂
      rw [schemeVertSet_le_iff hQd VQ hVQ_range, htoFun, htoFun,
        ← schemeVertSet_le_iff hPd VP hVP_range]
  }⟩

end Grunbaum2003

theorem solution (d₁ d₂ k : ℕ) (S : List (List ℕ))
    (P : Set (Fin d₁ → ℝ)) (Q : Set (Fin d₂ → ℝ))
    (hP : Grunbaum2003.SchemeRealizes k S P) (hQ : Grunbaum2003.SchemeRealizes k S Q) :
    Nonempty (Grunbaum2003.PolytopeFace P ≃o Grunbaum2003.PolytopeFace Q) :=
  Grunbaum2003.schemeRealizes_unique_combinatorial_type d₁ d₂ k S P Q hP hQ
