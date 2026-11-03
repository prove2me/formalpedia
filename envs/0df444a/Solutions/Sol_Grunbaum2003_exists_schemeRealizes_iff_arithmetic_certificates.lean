-- Prove2me | solution 1 for Grunbaum2003.exists_schemeRealizes_iff_arithmetic_certificates
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T07:15:58.773125+00:00
-- url     : https://prove2.me/submissions/3fa69597-8b16-41bc-928d-e6dc99b6a401

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SchemeRealizes
import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.Pi

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace Grunbaum2003


/-- Any exposed face of a finite hull is the hull of its incident input points.
The input need not be an irredundant vertex list. -/
theorem exposedFace_eq_convexHull_incident_range {d n : ℕ}
    (v : Fin n → Fin d → ℝ) {F : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ (convexHull ℝ (Set.range v)) F) :
    F = convexHull ℝ (F ∩ Set.range v) := by
  have hPcomp : IsCompact (convexHull ℝ (Set.range v)) :=
    (Set.finite_range v).isCompact_convexHull ℝ
  have hFcomp : IsCompact F := hF.isCompact hPcomp
  have hFconv : Convex ℝ F := hF.convex (convex_convexHull ℝ (Set.range v))
  have hExtRange : F.extremePoints ℝ ⊆ Set.range v := by
    intro x hx
    rw [hF.isExtreme.extremePoints_eq] at hx
    exact extremePoints_convexHull_subset hx.2
  have hExtFin : (F.extremePoints ℝ).Finite := (Set.finite_range v).subset hExtRange
  have hKM := closure_convexHull_extremePoints hFcomp hFconv
  rw [(hExtFin.isCompact_convexHull ℝ).isClosed.closure_eq] at hKM
  apply Set.Subset.antisymm
  · apply hKM.symm.subset.trans
    apply convexHull_mono
    intro x hx
    exact ⟨extremePoints_subset hx, hExtRange hx⟩
  · exact convexHull_min Set.inter_subset_left hFconv

/-- Containment of finite-hull faces is exactly containment of their incident
input-label sets. This provides the order embedding used by finite certificates. -/
theorem exposedFace_subset_iff_incident_labels {d n : ℕ}
    (v : Fin n → Fin d → ℝ) {F G : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ (convexHull ℝ (Set.range v)) F)
    (hG : IsExposed ℝ (convexHull ℝ (Set.range v)) G) :
    F ⊆ G ↔ ∀ i : Fin n, v i ∈ F → v i ∈ G := by
  constructor
  · intro h i hi
    exact h hi
  · intro h
    rw [exposedFace_eq_convexHull_incident_range v hF,
      exposedFace_eq_convexHull_incident_range v hG]
    apply convexHull_mono
    rintro x ⟨hx, i, rfl⟩
    exact ⟨h i hx, ⟨i, rfl⟩⟩

/-- A finite rational/linear support certificate realizes a face and certifies
its exact input-label incidence set. -/
theorem exposedFace_of_label_maximizers {d n : ℕ}
    (v : Fin n → Fin d → ℝ) (s : Set (Fin n)) (hs : s.Nonempty)
    (l : (Fin d → ℝ) →L[ℝ] ℝ) (b : ℝ)
    (hbound : ∀ i : Fin n, l (v i) ≤ b)
    (heq : ∀ i : Fin n, l (v i) = b ↔ i ∈ s) :
    IsExposed ℝ (convexHull ℝ (Set.range v)) (convexHull ℝ (v '' s)) ∧
      ∀ i : Fin n, v i ∈ convexHull ℝ (v '' s) ↔ i ∈ s := by
  let P := convexHull ℝ (Set.range v)
  let F := l.toExposed P
  have hPbound : ∀ x ∈ P, l x ≤ b := by
    have hconv : Convex ℝ {x : Fin d → ℝ | l x ≤ b} := by
      intro x hx y hy a c ha hc hac
      change l (a • x + c • y) ≤ b
      rw [map_add, map_smul, map_smul]
      change a * l x + c * l y ≤ b
      calc a * l x + c * l y ≤ a * b + c * b :=
          add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hc)
        _ = b := by rw [← add_mul, hac, one_mul]
    exact convexHull_min (by rintro _ ⟨i, rfl⟩; exact hbound i) hconv
  have hFlabels : ∀ i : Fin n, v i ∈ F ↔ i ∈ s := by
    intro i
    constructor
    · intro hi
      obtain ⟨j, hj⟩ := hs
      have hbj : l (v j) = b := (heq j).mpr hj
      have hbi : b ≤ l (v i) := by
        rw [← hbj]
        exact hi.2 (v j) (subset_convexHull ℝ _ (Set.mem_range_self j))
      exact (heq i).mp (le_antisymm (hbound i) hbi)
    · intro hi
      refine ⟨subset_convexHull ℝ _ (Set.mem_range_self i), ?_⟩
      intro x hx
      rw [(heq i).mpr hi]
      exact hPbound x hx
  have hInc : F ∩ Set.range v = v '' s := by
    ext x
    constructor
    · rintro ⟨hx, i, rfl⟩
      exact ⟨i, (hFlabels i).mp hx, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(hFlabels i).mpr hi, Set.mem_range_self i⟩
  have hFhull : F = convexHull ℝ (v '' s) := by
    calc F = convexHull ℝ (F ∩ Set.range v) :=
          exposedFace_eq_convexHull_incident_range v
            (ContinuousLinearMap.toExposed.isExposed (l := l) (A := P))
      _ = convexHull ℝ (v '' s) := congrArg (convexHull ℝ) hInc
  constructor
  · rw [← hFhull]
    exact (ContinuousLinearMap.toExposed.isExposed (l := l) (A := P))
  · intro i
    rw [← hFhull]
    exact hFlabels i

/-- A complete finite incidence certificate identifies the actual exposed-face
poset. The two certificate obligations concern only its finite label family. -/
theorem exposedFaces_orderIso_of_incidence_certificate {d n : ℕ}
    (v : Fin n → Fin d → ℝ) (family : Finset (Finset (Fin n)))
    (hSound : ∀ F : Set (Fin d → ℝ),
      IsExposed ℝ (convexHull ℝ (Set.range v)) F →
      ∀ s : Finset (Fin n), (∀ i : Fin n, i ∈ s ↔ v i ∈ F) → s ∈ family)
    (hComplete : ∀ s ∈ family,
      IsExposed ℝ (convexHull ℝ (Set.range v)) (convexHull ℝ (v '' (s : Set (Fin n)))) ∧
        ∀ i : Fin n, v i ∈ convexHull ℝ (v '' (s : Set (Fin n))) ↔ i ∈ s) :
    Nonempty ({F : Set (Fin d → ℝ) // IsExposed ℝ (convexHull ℝ (Set.range v)) F} ≃o
      ↥family) := by
  classical
  let f : {F : Set (Fin d → ℝ) // IsExposed ℝ (convexHull ℝ (Set.range v)) F} ↪o ↥family := {
    toFun := fun F => ⟨Finset.univ.filter (fun i => v i ∈ F.val),
      hSound F.val F.property _ (by intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and])⟩
    inj' := by
      intro F G h
      have hfg : (Finset.univ.filter fun i => v i ∈ F.val) =
          (Finset.univ.filter fun i => v i ∈ G.val) := congrArg Subtype.val h
      have hi : ∀ i : Fin n, v i ∈ F.val ↔ v i ∈ G.val := by
        intro i
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
          (Finset.ext_iff.mp hfg i)
      apply Subtype.ext
      apply Set.Subset.antisymm
      · exact (exposedFace_subset_iff_incident_labels v F.property G.property).mpr
          (fun i hv => (hi i).mp hv)
      · exact (exposedFace_subset_iff_incident_labels v G.property F.property).mpr
          (fun i hv => (hi i).mpr hv)
    map_rel_iff' := by
      intro F G
      change (Finset.univ.filter (fun i => v i ∈ F.val)) ⊆
        (Finset.univ.filter (fun i => v i ∈ G.val)) ↔ F.val ⊆ G.val
      simpa only [Finset.subset_iff, Finset.mem_filter,
        Finset.mem_univ, true_and] using
        (exposedFace_subset_iff_incident_labels v F.property G.property).symm }
  have hf : Function.Surjective f := by
    intro s
    refine ⟨⟨convexHull ℝ (v '' (s.val : Set (Fin n))), (hComplete s.val s.property).1⟩, ?_⟩
    apply Subtype.ext
    ext i
    change i ∈ Finset.univ.filter (fun i => v i ∈ convexHull ℝ (v '' (s.val : Set (Fin n)))) ↔
      i ∈ s.val
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (hComplete s.val s.property).2 i
  exact ⟨OrderIso.ofSurjective f hf⟩

/-- The complete certificate isomorphism retains the actual vertex incidences. -/
theorem exposedFaces_orderIso_of_incidence_certificate_with_incidence {d n : ℕ}
    (v : Fin n → Fin d → ℝ) (family : Finset (Finset (Fin n)))
    (hSound : ∀ F : Set (Fin d → ℝ),
      IsExposed ℝ (convexHull ℝ (Set.range v)) F →
      ∀ s : Finset (Fin n), (∀ i : Fin n, i ∈ s ↔ v i ∈ F) → s ∈ family)
    (hComplete : ∀ s ∈ family,
      IsExposed ℝ (convexHull ℝ (Set.range v)) (convexHull ℝ (v '' (s : Set (Fin n)))) ∧
        ∀ i : Fin n, v i ∈ convexHull ℝ (v '' (s : Set (Fin n))) ↔ i ∈ s) :
    ∃ Φ : {F : Set (Fin d → ℝ) // IsExposed ℝ (convexHull ℝ (Set.range v)) F} ≃o ↥family,
      ∀ F i, i ∈ (Φ F).val ↔ v i ∈ F.val := by
  classical
  let f : {F : Set (Fin d → ℝ) // IsExposed ℝ (convexHull ℝ (Set.range v)) F} ↪o ↥family := {
    toFun := fun F => ⟨Finset.univ.filter (fun i => v i ∈ F.val),
      hSound F.val F.property _ (by intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and])⟩
    inj' := by
      intro F G h
      have hfg : (Finset.univ.filter fun i => v i ∈ F.val) =
          (Finset.univ.filter fun i => v i ∈ G.val) := congrArg Subtype.val h
      have hi : ∀ i : Fin n, v i ∈ F.val ↔ v i ∈ G.val := by
        intro i
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
          (Finset.ext_iff.mp hfg i)
      apply Subtype.ext
      apply Set.Subset.antisymm
      · exact (exposedFace_subset_iff_incident_labels v F.property G.property).mpr
          (fun i hv => (hi i).mp hv)
      · exact (exposedFace_subset_iff_incident_labels v G.property F.property).mpr
          (fun i hv => (hi i).mpr hv)
    map_rel_iff' := by
      intro F G
      change (Finset.univ.filter (fun i => v i ∈ F.val)) ⊆
        (Finset.univ.filter (fun i => v i ∈ G.val)) ↔ F.val ⊆ G.val
      simpa only [Finset.subset_iff, Finset.mem_filter,
        Finset.mem_univ, true_and] using
        (exposedFace_subset_iff_incident_labels v F.property G.property).symm }
  have hf : Function.Surjective f := by
    intro s
    refine ⟨⟨convexHull ℝ (v '' (s.val : Set (Fin n))), (hComplete s.val s.property).1⟩, ?_⟩
    apply Subtype.ext
    ext i
    change i ∈ Finset.univ.filter (fun i => v i ∈ convexHull ℝ (v '' (s.val : Set (Fin n)))) ↔
      i ∈ s.val
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (hComplete s.val s.property).2 i
  refine ⟨OrderIso.ofSurjective f hf, ?_⟩
  intro F i
  change i ∈ Finset.univ.filter (fun i => v i ∈ F.val) ↔ v i ∈ F.val
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]




noncomputable section

private def supportFunctional {d : ℕ} (a : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] ℝ :=
  ({ toFun := fun x => ∑ t, a t * x t
     map_add' := by
       intro x y
       simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
     map_smul' := by
       intro c x
       simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
       exact Finset.sum_congr rfl (fun t _ => mul_left_comm (a t) c (x t))
    } : (Fin d → ℝ) →ₗ[ℝ] ℝ).toContinuousLinearMap

private theorem supportFunctional_apply {d : ℕ} (a x : Fin d → ℝ) :
    supportFunctional a x = ∑ t, a t * x t := rfl

private theorem exists_support_coefficients {d : ℕ} (l : (Fin d → ℝ) →L[ℝ] ℝ) :
    ∃ a : Fin d → ℝ, ∀ x : Fin d → ℝ, l x = ∑ t, a t * x t := by
  refine ⟨fun t => l (fun j => if t = j then 1 else 0), ?_⟩
  intro x
  simpa only [ContinuousLinearMap.coe_coe, smul_eq_mul, mul_comm] using l.toLinearMap.pi_apply_eq_sum_univ x

/-- Converting the natural-number incidence set to its finitely indexed form.
The explicit bound is essential for the reverse implication. -/
theorem incidence_set_eq_iff {d k : ℕ} (V : Fin k → Fin d → ℝ)
    (J : Finset ℕ) (hJ : J ⊆ Finset.range k) (F : Set (Fin d → ℝ)) :
    (J : Set ℕ) = {n | ∃ i : Fin k, i.val = n ∧ V i ∈ F} ↔
      ∀ i : Fin k, V i ∈ F ↔ i.val ∈ J := by
  constructor
  · intro h i
    constructor
    · intro hi
      have hn : i.val ∈ (J : Set ℕ) := by rw [h]; exact ⟨i, rfl, hi⟩
      exact hn
    · intro hi
      have hn : i.val ∈ (J : Set ℕ) := hi
      rw [h] at hn
      obtain ⟨j, hji, hjF⟩ := hn
      have hji' : j = i := Fin.ext hji
      exact hji' ▸ hjF
  · intro h
    ext n
    constructor
    · intro hn
      have hnk : n < k := Finset.mem_range.mp (hJ hn)
      exact ⟨⟨n, hnk⟩, rfl, (h ⟨n, hnk⟩).mpr hn⟩
    · rintro ⟨i, rfl, hi⟩
      exact (h i).mp hi

/-- A nonempty proper bounded label set is the incidence of an actual exposed
face exactly when finitely many bilinear support equalities/inequalities hold. -/
theorem proper_face_incidence_iff_support_coefficients {d k : ℕ}
    (V : Fin k → Fin d → ℝ) (P : Set (Fin d → ℝ))
    (hPgen : P = convexHull ℝ (Set.range V))
    (J : Finset ℕ) (hJ : J ⊆ Finset.range k) (hJne : J.Nonempty)
    (hJproper : J ≠ Finset.range k) :
    (∃ F : Set (Fin d → ℝ), IsExposed ℝ P F ∧ F.Nonempty ∧ F ≠ P ∧
      (J : Set ℕ) = {n | ∃ i : Fin k, i.val = n ∧ V i ∈ F}) ↔
    ∃ (a : Fin d → ℝ) (b : ℝ),
      (∀ i : Fin k, (∑ t, a t * V i t) ≤ b) ∧
      (∀ i : Fin k, (∑ t, a t * V i t) = b ↔ i.val ∈ J) := by
  have hVP (i : Fin k) : V i ∈ P := by rw [hPgen]; exact subset_convexHull ℝ _ (Set.mem_range_self i)
  constructor
  · rintro ⟨F, hF, hFne, hFproper, hInc⟩
    have hAt := (incidence_set_eq_iff V J hJ F).mp hInc
    obtain ⟨n, hn⟩ := hJne
    let i : Fin k := ⟨n, Finset.mem_range.mp (hJ hn)⟩
    have hiF : V i ∈ F := (hAt i).mpr hn
    obtain ⟨l, hl⟩ := hF hFne
    have hiMax : V i ∈ P ∧ ∀ x ∈ P, l x ≤ l (V i) := by
      simpa only [hl, Set.mem_ofPred_eq] using hiF
    obtain ⟨a, ha⟩ := exists_support_coefficients l
    refine ⟨a, l (V i), ?_, ?_⟩
    · intro j
      rw [← ha]
      exact hiMax.2 (V j) (hVP j)
    · intro j
      rw [← ha]
      constructor
      · intro hj
        apply (hAt j).mp
        rw [hl]
        exact ⟨hVP j, by rw [hj]; exact hiMax.2⟩
      · intro hj
        have hjF := (hAt j).mpr hj
        rw [hl] at hjF
        exact le_antisymm (hiMax.2 _ (hVP j)) (hjF.2 _ (hVP i))
  · rintro ⟨a, b, hbound, heq⟩
    let s : Set (Fin k) := {i | i.val ∈ J}
    have hs : s.Nonempty := by
      obtain ⟨n, hn⟩ := hJne
      exact ⟨⟨n, Finset.mem_range.mp (hJ hn)⟩, hn⟩
    obtain ⟨hF, hAt⟩ := exposedFace_of_label_maximizers V s hs
      (supportFunctional a) b (by simpa only [supportFunctional_apply] using hbound)
        (by simpa only [supportFunctional_apply, s, Set.mem_ofPred_eq] using heq)
    let F := convexHull ℝ (V '' s)
    have hFne : F.Nonempty := hs.image V |>.convexHull
    have hInc : (J : Set ℕ) = {n | ∃ i : Fin k, i.val = n ∧ V i ∈ F} :=
      (incidence_set_eq_iff V J hJ F).mpr hAt
    refine ⟨F, hPgen ▸ hF, hFne, ?_, hInc⟩
    intro hFP
    apply hJproper
    apply Finset.Subset.antisymm hJ
    intro n hn
    let i : Fin k := ⟨n, Finset.mem_range.mp hn⟩
    apply (hAt i).mp
    change V i ∈ F
    rw [hFP]
    exact hVP i

/-- Proper nonempty face incidences of a finite hull are nonempty proper bounded
sets of labels. This is valid even if the finite input list is redundant. -/
theorem proper_face_incidence_bounds {d k : ℕ}
    (V : Fin k → Fin d → ℝ) (P : Set (Fin d → ℝ))
    (hPgen : P = convexHull ℝ (Set.range V))
    (J : Finset ℕ) (F : Set (Fin d → ℝ))
    (hF : IsExposed ℝ P F) (hFne : F.Nonempty) (hFP : F ≠ P)
    (hInc : (J : Set ℕ) = {n | ∃ i : Fin k, i.val = n ∧ V i ∈ F}) :
    J ⊆ Finset.range k ∧ J.Nonempty ∧ J ≠ Finset.range k := by
  have hJ : J ⊆ Finset.range k := by
    intro n hn
    have hn' : n ∈ (J : Set ℕ) := hn
    rw [hInc] at hn'
    obtain ⟨i, rfl, _⟩ := hn'
    exact Finset.mem_range.mpr i.isLt
  have hAt := (incidence_set_eq_iff V J hJ F).mp hInc
  have hF' : IsExposed ℝ (convexHull ℝ (Set.range V)) F := hPgen ▸ hF
  have hFhull := exposedFace_eq_convexHull_incident_range V (F := F) hF' 
  have hIncNe : (F ∩ Set.range V).Nonempty :=
    convexHull_nonempty_iff.mp (hFhull ▸ hFne)
  obtain ⟨_, hxF, i, rfl⟩ := hIncNe
  refine ⟨hJ, ⟨i.val, (hAt i).mp hxF⟩, ?_⟩
  intro hJall
  apply hFP
  apply Set.Subset.antisymm hF.subset
  rw [hPgen]
  apply convexHull_min ?_ (hF.convex (by rw [hPgen]; exact convex_convexHull ℝ _))
  rintro _ ⟨j, rfl⟩
  apply (hAt j).mpr
  rw [hJall]
  exact Finset.mem_range.mpr j.isLt

/-- Irredundancy of a finite generator is exactly a strict linear support
certificate at that generator; the singleton-body case is included. -/
theorem singleton_exposed_iff_strict_support_coefficients {d k : ℕ}
    (V : Fin k → Fin d → ℝ) (P : Set (Fin d → ℝ))
    (hPgen : P = convexHull ℝ (Set.range V)) (hV : Function.Injective V) (i : Fin k) :
    IsExposed ℝ P {V i} ↔
      ∃ a : Fin d → ℝ, ∀ j : Fin k, j ≠ i →
        (∑ t, a t * V j t) < ∑ t, a t * V i t := by
  have hVP (j : Fin k) : V j ∈ P := by
    rw [hPgen]
    exact subset_convexHull ℝ _ (Set.mem_range_self j)
  constructor
  · intro hi
    obtain ⟨l, hl⟩ := hi (Set.singleton_nonempty (V i))
    have hiMax : ∀ x ∈ P, l x ≤ l (V i) := by
      have hVi : V i ∈ ({V i} : Set (Fin d → ℝ)) := Set.mem_singleton _
      rw [hl] at hVi
      exact hVi.2
    obtain ⟨a, ha⟩ := exists_support_coefficients l
    refine ⟨a, ?_⟩
    intro j hji
    rw [← ha, ← ha]
    apply lt_of_le_of_ne (hiMax _ (hVP j))
    intro heq
    have hjF : V j ∈ ({V i} : Set (Fin d → ℝ)) := by
      rw [hl]
      refine ⟨hVP j, ?_⟩
      rw [heq]
      exact hiMax
    exact hji (hV (Set.mem_singleton_iff.mp hjF))
  · rintro ⟨a, ha⟩
    have hbound : ∀ j : Fin k, supportFunctional a (V j) ≤ supportFunctional a (V i) := by
      intro j
      rw [supportFunctional_apply, supportFunctional_apply]
      by_cases hji : j = i
      · rw [hji]
      · exact (ha j hji).le
    have heq : ∀ j : Fin k,
        supportFunctional a (V j) = supportFunctional a (V i) ↔ j ∈ ({i} : Set (Fin k)) := by
      intro j
      rw [supportFunctional_apply, supportFunctional_apply]
      change _ ↔ j = i
      constructor
      · intro h
        by_contra hji
        exact (ne_of_lt (ha j hji)) h
      · intro hji
        rw [hji]
    have h := (exposedFace_of_label_maximizers V ({i} : Set (Fin k))
      (Set.singleton_nonempty i) (supportFunctional a) (supportFunctional a (V i)) hbound heq).1
    rw [hPgen]
    simpa only [Set.image_singleton, convexHull_singleton] using h

/-- Exact realizability characterization by a finite vertex configuration and
finite support-vector tests. All face-incidence quantifiers range over the
explicit powerset of k labels. This is a semantic producer for the existing
computable-representatives frontier, not a decision procedure. -/
theorem exists_schemeRealizes_iff_finite_support_certificates (d k : ℕ)
    (S : List (List ℕ)) :
    (∃ P : Set (Fin d → ℝ), SchemeRealizes k S P) ↔
    ∃ V : Fin k → Fin d → ℝ,
      0 < k ∧ Function.Injective V ∧ affineSpan ℝ (Set.range V) = ⊤ ∧
      (∀ i : Fin k, ∃ a : Fin d → ℝ, ∀ j : Fin k, j ≠ i →
        (∑ t, a t * V j t) < ∑ t, a t * V i t) ∧
      (∀ L ∈ S, ∀ n ∈ L, n < k) ∧
      ∀ J ∈ (Finset.range k).powerset,
        (∃ L ∈ S, L.toFinset = J) ↔
          J.Nonempty ∧ J ≠ Finset.range k ∧
            ∃ (a : Fin d → ℝ) (b : ℝ),
              (∀ i : Fin k, (∑ t, a t * V i t) ≤ b) ∧
              (∀ i : Fin k, (∑ t, a t * V i t) = b ↔ i.val ∈ J) := by
  classical
  constructor
  · rintro ⟨P, hP, V, hV, hRange, hFaces⟩
    have hVP : Set.range V ⊆ P := by
      intro x hx
      rw [hRange] at hx
      exact hx.subset (Set.mem_singleton x)
    have hPgen : P = convexHull ℝ (Set.range V) := by
      have h := (polytope_face_eq_convexHull_exposed_vertices d P hP).2 ⟨P, IsExposed.refl P⟩
      rw [← hRange, Set.inter_eq_right.mpr hVP] at h
      exact h
    have hPne : P.Nonempty := by
      obtain ⟨W, _, hWne, hPW⟩ := hP.1
      rw [hPW]
      exact hWne.convexHull
    have hVne : (Set.range V).Nonempty := convexHull_nonempty_iff.mp (hPgen ▸ hPne)
    obtain ⟨_, i, rfl⟩ := hVne
    refine ⟨V, lt_of_le_of_lt (Nat.zero_le i.val) i.isLt, hV, ?_, ?_, ?_, ?_⟩
    · rw [← affineSpan_convexHull, ← hPgen]
      exact hP.2
    · intro j
      apply (singleton_exposed_iff_strict_support_coefficients V P hPgen hV j).mp
      have hj : V j ∈ Set.range V := Set.mem_range_self j
      rw [hRange] at hj
      exact hj
    · intro L hL n hn
      obtain ⟨F, hF, hFne, hFP, hInc⟩ := (hFaces L.toFinset).mp ⟨L, hL, rfl⟩
      have hBounds := proper_face_incidence_bounds V P hPgen L.toFinset F hF hFne hFP hInc
      exact Finset.mem_range.mp (hBounds.1 (List.mem_toFinset.mpr hn))
    · intro J hJpow
      have hJ : J ⊆ Finset.range k := Finset.mem_powerset.mp hJpow
      constructor
      · intro hJS
        obtain ⟨F, hF, hFne, hFP, hInc⟩ := (hFaces J).mp hJS
        have hBounds := proper_face_incidence_bounds V P hPgen J F hF hFne hFP hInc
        refine ⟨hBounds.2.1, hBounds.2.2, ?_⟩
        exact (proper_face_incidence_iff_support_coefficients V P hPgen J hJ
          hBounds.2.1 hBounds.2.2).mp ⟨F, hF, hFne, hFP, hInc⟩
      · rintro ⟨hJne, hJproper, hCert⟩
        exact (hFaces J).mpr ((proper_face_incidence_iff_support_coefficients V P hPgen J
          hJ hJne hJproper).mpr hCert)
  · rintro ⟨V, hk, hV, hSpan, hVertices, hBound, hRows⟩
    let P := convexHull ℝ (Set.range V)
    have hP : IsDPolytope P := by
      refine ⟨⟨Set.range V, Set.finite_range V,
        ⟨V ⟨0, hk⟩, ⟨⟨0, hk⟩, rfl⟩⟩, rfl⟩, ?_⟩
      rw [affineSpan_convexHull]
      exact hSpan
    have hVertex (i : Fin k) : IsExposed ℝ P {V i} :=
      (singleton_exposed_iff_strict_support_coefficients V P rfl hV i).mpr (hVertices i)
    have hRange : Set.range V = {x | IsExposed ℝ P {x}} := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact hVertex i
      · intro hx
        have hExt := exposedPoints_subset_extremePoints
          (mem_exposedPoints_iff_exposed_singleton.mpr hx)
        exact extremePoints_convexHull_subset hExt
    refine ⟨P, hP, V, hV, hRange, ?_⟩
    intro J
    by_cases hJ : J ⊆ Finset.range k
    · constructor
      · intro hJS
        obtain ⟨hJne, hJproper, hCert⟩ := (hRows J (Finset.mem_powerset.mpr hJ)).mp hJS
        exact (proper_face_incidence_iff_support_coefficients V P rfl J hJ hJne hJproper).mpr hCert
      · rintro ⟨F, hF, hFne, hFP, hInc⟩
        have hBounds := proper_face_incidence_bounds V P rfl J F hF hFne hFP hInc
        apply (hRows J (Finset.mem_powerset.mpr hJ)).mpr
        exact ⟨hBounds.2.1, hBounds.2.2,
          (proper_face_incidence_iff_support_coefficients V P rfl J hJ
            hBounds.2.1 hBounds.2.2).mp ⟨F, hF, hFne, hFP, hInc⟩⟩
    · constructor
      · rintro ⟨L, hLS, rfl⟩
        apply False.elim
        apply hJ
        intro n hn
        exact Finset.mem_range.mpr (hBound L hLS n (List.mem_toFinset.mp hn))
      · rintro ⟨F, hF, hFne, hFP, hInc⟩
        exact (hJ (proper_face_incidence_bounds V P rfl J F hF hFne hFP hInc).1).elim

end



/-- Full affine span of a finite configuration is a first-order real-field
condition on affine weights, including empty and zero-dimensional cases. -/
theorem affineSpan_eq_top_iff_affine_weights {d k : ℕ} (V : Fin k → Fin d → ℝ) :
    affineSpan ℝ (Set.range V) = ⊤ ↔
      ∀ x : Fin d → ℝ, ∃ w : Fin k → ℝ,
        (∑ i, w i) = 1 ∧ ∀ t : Fin d, (∑ i, w i * V i t) = x t := by
  constructor
  · intro hSpan x
    have hx : x ∈ affineSpan ℝ (Set.range V) := by rw [hSpan]; trivial
    obtain ⟨w, hw, hxw⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hx
    rw [Finset.affineCombination_eq_linear_combination Finset.univ V w hw] at hxw
    refine ⟨w, hw, ?_⟩
    intro t
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using (congrFun hxw t).symm
  · intro hWeights
    apply top_unique
    intro x hx
    obtain ⟨w, hw, hcoords⟩ := hWeights x
    have hxw : x = ∑ i, w i • V i := by
      ext t
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using (hcoords t).symm
    rw [hxw]
    have hmem := affineCombination_mem_affineSpan (s := Finset.univ) hw V
    rwa [Finset.affineCombination_eq_linear_combination Finset.univ V w hw] at hmem

/-- Exact scheme realizability expressed using only finite incidence data and
ordered-real-field equations and inequalities. This supplies semantic
correctness for a future uniform formula compiler/decision procedure; it does
not assert that such a decision procedure has already been implemented. -/
theorem exists_schemeRealizes_iff_arithmetic_certificates (d k : ℕ)
    (S : List (List ℕ)) :
    (∃ P : Set (Fin d → ℝ), SchemeRealizes k S P) ↔
    ∃ V : Fin k → Fin d → ℝ,
      0 < k ∧ Function.Injective V ∧
      (∀ x : Fin d → ℝ, ∃ w : Fin k → ℝ,
        (∑ i, w i) = 1 ∧ ∀ t : Fin d, (∑ i, w i * V i t) = x t) ∧
      (∀ i : Fin k, ∃ a : Fin d → ℝ, ∀ j : Fin k, j ≠ i →
        (∑ t, a t * V j t) < ∑ t, a t * V i t) ∧
      (∀ L ∈ S, ∀ n ∈ L, n < k) ∧
      ∀ J ∈ (Finset.range k).powerset,
        (∃ L ∈ S, L.toFinset = J) ↔
          J.Nonempty ∧ J ≠ Finset.range k ∧
            ∃ (a : Fin d → ℝ) (b : ℝ),
              (∀ i : Fin k, (∑ t, a t * V i t) ≤ b) ∧
              (∀ i : Fin k, (∑ t, a t * V i t) = b ↔ i.val ∈ J) := by
  simpa only [affineSpan_eq_top_iff_affine_weights] using
    exists_schemeRealizes_iff_finite_support_certificates d k S


end Grunbaum2003
end

theorem solution (d k : ℕ) (S : List (List ℕ)) :
    (∃ P : Set (Fin d → ℝ), Grunbaum2003.SchemeRealizes k S P) ↔
    ∃ V : Fin k → Fin d → ℝ,
      0 < k ∧ Function.Injective V ∧
      (∀ x : Fin d → ℝ, ∃ w : Fin k → ℝ,
        (∑ i, w i) = 1 ∧ ∀ t : Fin d, (∑ i, w i * V i t) = x t) ∧
      (∀ i : Fin k, ∃ a : Fin d → ℝ, ∀ j : Fin k, j ≠ i →
        (∑ t, a t * V j t) < ∑ t, a t * V i t) ∧
      (∀ L ∈ S, ∀ n ∈ L, n < k) ∧
      ∀ J ∈ (Finset.range k).powerset,
        (∃ L ∈ S, L.toFinset = J) ↔
          J.Nonempty ∧ J ≠ Finset.range k ∧
            ∃ (a : Fin d → ℝ) (b : ℝ),
              (∀ i : Fin k, (∑ t, a t * V i t) ≤ b) ∧
              (∀ i : Fin k, (∑ t, a t * V i t) = b ↔ i.val ∈ J) :=
  Grunbaum2003.exists_schemeRealizes_iff_arithmetic_certificates d k S
