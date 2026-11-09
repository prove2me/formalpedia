-- Prove2me | solution 1 for Grunbaum2003.exists_apex_beyond_simplicial_facet_preserving_proper_faces
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T04:48:19.714207+00:00
-- url     : https://prove2.me/submissions/d094a2a1-44c4-4d26-9d00-baebe48fd99e

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Join
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
open scoped Classical BigOperators

private lemma finite_strict_perturbation {d m : ℕ}
    (ψ : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin m → ℝ)
    (w u : Fin d → ℝ) (hw : ∀ i, ψ i w < c i) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ ∀ i, ψ i (w + t • u) < c i := by
  let r : Fin m → ℝ := fun i => |ψ i u| / (c i - ψ i w)
  let B : ℝ := ∑ i, r i
  have hr : ∀ i, 0 ≤ r i := fun i => div_nonneg (abs_nonneg _) (sub_pos.mpr (hw i)).le
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => hr i)
  have hden : 0 < 1 + B := by linarith
  let t : ℝ := 1 / (1 + B)
  have ht : 0 < t := div_pos zero_lt_one hden
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact (div_le_one hden).2 (by linarith)
  have htden : t * (1 + B) = 1 := by
    dsimp [t]
    exact div_mul_cancel₀ _ (ne_of_gt hden)
  refine ⟨t, ht, ht1, fun i => ?_⟩
  have hri : r i ≤ B := Finset.single_le_sum (fun j _ => hr j) (Finset.mem_univ i)
  have hsmall : t * r i < 1 := by
    calc
      t * r i < t * (1 + B) := mul_lt_mul_of_pos_left (by linarith) ht
      _ = 1 := htden
  have hδ : 0 < c i - ψ i w := sub_pos.mpr (hw i)
  have hratio : t * |ψ i u| / (c i - ψ i w) < 1 := by
    simpa only [r, mul_div_assoc] using hsmall
  have hgap : t * |ψ i u| < c i - ψ i w := (div_lt_one hδ).1 hratio
  have hslope := mul_le_mul_of_nonneg_left (le_abs_self (ψ i u)) ht.le
  rw [map_add, map_smul, smul_eq_mul]
  linarith

/-- A point can move strictly beyond one support plane while remaining strictly
beneath any given finite family of other support planes. -/
private theorem small_apex {d m : ℕ} {P : Set (Fin d → ℝ)}
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (w z : Fin d → ℝ)
    (hbound : ∀ x ∈ P, φ x ≤ φ w) (hz : φ z < φ w)
    (ψ : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hw : ∀ i, ψ i w < c i) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      φ w < φ (w + t • (w - z)) ∧
      w + t • (w - z) ∉ P ∧
      ∀ i, ψ i (w + t • (w - z)) < c i := by
  obtain ⟨t, ht, ht1, hplanes⟩ := finite_strict_perturbation ψ c w (w - z) hw
  have habove : φ w < φ (w + t • (w - z)) := by
    rw [map_add, map_smul, map_sub, smul_eq_mul]
    nlinarith [mul_pos ht (sub_pos.mpr hz)]
  exact ⟨t, ht, ht1, habove, fun h => (not_le_of_gt habove) (hbound _ h), hplanes⟩

/-- The barycenter of the selected support vertices admits an exterior
perturbation beneath every other finite support plane that does not contain
all of those vertices. -/
private theorem stellarSupportLower_barycenter_apex {d m : ℕ} (hd : 0 < d) {P : Set (Fin d → ℝ)}
    (hP : Convex ℝ P) (v : Fin d → Fin d → ℝ) (hvP : ∀ i, v i ∈ P)
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (hbound : ∀ x ∈ P, φ x ≤ a) (hlevel : ∀ i, φ (v i) = a)
    (z : Fin d → ℝ) (hz : φ z < a)
    (ψ : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hother : ∀ j, (∀ i, ψ j (v i) ≤ c j) ∧ ∃ i, ψ j (v i) < c j) :
    let w : Fin d → ℝ := (d : ℝ)⁻¹ • ∑ i, v i
    w ∈ P ∧ φ w = a ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
        a < φ (w + t • (w - z)) ∧
        w + t • (w - z) ∉ P ∧
        ∀ j, ψ j (w + t • (w - z)) < c j := by
  intro w
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  have hwP : w ∈ P := by
    have hmass := hP.centerMass_mem (t := Finset.univ) (w := fun _ : Fin d => (1 : ℝ))
      (z := v) (fun _ _ => zero_le_one) (by simpa using hdpos) (fun i _ => hvP i)
    simpa [Finset.centerMass] using hmass
  have hφw : φ w = a := by
    dsimp [w]
    rw [map_smul, map_sum]
    simp [hlevel, smul_eq_mul, hdne]
  have hplanes : ∀ j, ψ j w < c j := by
    intro j
    have hsum : (∑ i, ψ j (v i)) < (d : ℝ) * c j := by
      calc
        (∑ i, ψ j (v i)) < ∑ _i : Fin d, c j := by
          obtain ⟨i, hi⟩ := (hother j).2
          exact Finset.sum_lt_sum (fun i _ => (hother j).1 i) ⟨i, Finset.mem_univ i, hi⟩
        _ = (d : ℝ) * c j := by simp
    calc
      ψ j w = (d : ℝ)⁻¹ * ∑ i, ψ j (v i) := by
        dsimp [w]
        rw [map_smul, map_sum, smul_eq_mul]
      _ < (d : ℝ)⁻¹ * ((d : ℝ) * c j) :=
        mul_lt_mul_of_pos_left hsum (inv_pos.mpr hdpos)
      _ = c j := by rw [← mul_assoc, inv_mul_cancel₀ hdne, one_mul]
  refine ⟨hwP, hφw, ?_⟩
  have hbound' : ∀ x ∈ P, φ x ≤ φ w := by simpa [hφw] using hbound
  have hz' : φ z < φ w := by simpa [hφw] using hz
  obtain ⟨t, ht, ht1, hφ, hout, hrest⟩ := small_apex φ w z hbound' hz' ψ c hplanes
  exact ⟨t, ht, ht1, hφw ▸ hφ, hout, hrest⟩

set_option autoImplicit false
open scoped Classical BigOperators

namespace Grunbaum2003

/-- An exposed face is recovered by intersecting its affine span with the ambient set. -/
theorem stellarSupportLower_exposed_eq_inter_affineSpan {d : ℕ}
    {P F : Set (Fin d → ℝ)} (hF : IsExposed ℝ P F) (hne : F.Nonempty) :
    F = P ∩ (affineSpan ℝ F : Set (Fin d → ℝ)) := by
  obtain ⟨φ, hφ⟩ := hF hne
  obtain ⟨w, hwF⟩ := hne
  have hw : w ∈ P ∧ ∀ x ∈ P, φ x ≤ φ w := by simpa [hφ] using hwF
  let H := (affineSpan ℝ ({φ w} : Set ℝ)).comap φ.toLinearMap.toAffineMap
  have hFH : F ⊆ (H : Set (Fin d → ℝ)) := by
    intro x hx
    have hx' : x ∈ P ∧ ∀ y ∈ P, φ y ≤ φ x := by simpa [hφ] using hx
    have heq : φ x = φ w := le_antisymm (hw.2 x hx'.1) (hx'.2 w hw.1)
    simpa [H, AffineSubspace.mem_comap] using heq
  have hspanH := affineSpan_le_of_subset_coe hFH
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨hF.subset hx, subset_affineSpan ℝ F hx⟩
  · rintro x ⟨hxP, hxspan⟩
    have hxH := hspanH hxspan
    have heq : φ x = φ w := by simpa [H, AffineSubspace.mem_comap] using hxH
    rw [hφ]
    exact ⟨hxP, fun y hy => heq ▸ hw.2 y hy⟩

/-- Two comparable nonempty exposed faces with equal affine dimension coincide. -/
theorem stellarSupportLower_exposed_eq_of_subset_of_finrank_eq {d : ℕ}
    {P F G : Set (Fin d → ℝ)} (hF : IsExposed ℝ P F) (hne : F.Nonempty)
    (hG : IsExposed ℝ P G) (hFG : F ⊆ G)
    (hdim : Module.finrank ℝ (affineSpan ℝ F).direction =
      Module.finrank ℝ (affineSpan ℝ G).direction) : F = G := by
  have hle : affineSpan ℝ F ≤ affineSpan ℝ G := affineSpan_mono ℝ hFG
  have hdirection : (affineSpan ℝ F).direction = (affineSpan ℝ G).direction :=
    Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle) hdim
  have hspan : affineSpan ℝ F = affineSpan ℝ G :=
    AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdirection (hne.affineSpan ℝ) hle
  rw [stellarSupportLower_exposed_eq_inter_affineSpan hF hne,
    stellarSupportLower_exposed_eq_inter_affineSpan hG (hne.mono hFG), hspan]

/-- Every nonempty proper exposed face of a full-dimensional polytope has
affine dimension strictly smaller than the ambient dimension. -/
theorem stellarSupportLower_proper_face_finrank {d : ℕ} {P G : Set (Fin d → ℝ)}
    (hP : IsDPolytope P) (hG : IsExposed ℝ P G) (hGne : G.Nonempty) (hproper : G ≠ P) :
    Module.finrank ℝ (affineSpan ℝ G).direction + 1 ≤ d := by
  have hPdim : Module.finrank ℝ (affineSpan ℝ P).direction = d := by
    rw [hP.2, AffineSubspace.direction_top, finrank_top, Module.finrank_fin_fun]
  have hle : Module.finrank ℝ (affineSpan ℝ G).direction ≤ d := by
    simpa only [Module.finrank_fin_fun] using
      Submodule.finrank_le (affineSpan ℝ G).direction
  have hne : Module.finrank ℝ (affineSpan ℝ G).direction ≠ d := by
    intro heq
    exact hproper (stellarSupportLower_exposed_eq_of_subset_of_finrank_eq hG hGne
      (IsExposed.refl P) hG.subset (heq.trans hPdim.symm))
  omega

/-- Choose a supporting functional with an exact level-set description of a nonempty face. -/
theorem stellarSupportLower_exists_support {d : ℕ} {P F : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ P F) (hne : F.Nonempty) :
    ∃ (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ),
      (∀ x ∈ P, φ x ≤ a) ∧ F = {x ∈ P | φ x = a} := by
  obtain ⟨φ, hφ⟩ := hF hne
  obtain ⟨w, hwF⟩ := hne
  have hw : w ∈ P ∧ ∀ x ∈ P, φ x ≤ φ w := by simpa [hφ] using hwF
  refine ⟨φ, φ w, hw.2, ?_⟩
  rw [hφ]
  ext x
  constructor
  · rintro ⟨hxP, hx⟩
    exact ⟨hxP, le_antisymm (hw.2 x hxP) (hx w hw.1)⟩
  · rintro ⟨hxP, hx⟩
    exact ⟨hxP, fun y hy => hx ▸ hw.2 y hy⟩

/-- A supporting plane of a distinct face of no greater dimension is strict
at some vertex of a generating simplex for the selected face. -/
theorem stellarSupportLower_exists_vertex_strict {d n : ℕ}
    {P F G : Set (Fin d → ℝ)} (hF : IsExposed ℝ P F) (hFne : F.Nonempty)
    (hG : IsExposed ℝ P G) (hFG : F ≠ G)
    (hdim_le : Module.finrank ℝ (affineSpan ℝ G).direction ≤
      Module.finrank ℝ (affineSpan ℝ F).direction)
    (v : Fin n → Fin d → ℝ) (hFv : F = convexHull ℝ (Set.range v))
    (ψ : (Fin d → ℝ) →L[ℝ] ℝ) (c : ℝ)
    (hbound : ∀ x ∈ P, ψ x ≤ c) (hGeq : G = {x ∈ P | ψ x = c}) :
    ∃ i, ψ (v i) < c := by
  have hvF : ∀ i, v i ∈ F := by
    intro i
    rw [hFv]
    exact subset_convexHull ℝ _ (Set.mem_range_self i)
  by_contra! hnotstrict
  have hveq : ∀ i, ψ (v i) = c :=
    fun i => le_antisymm (hbound (v i) (hF.subset (hvF i))) (hnotstrict i)
  have hconst : ∀ x ∈ F, ψ x = c := by
    rw [hFv]
    exact convexHull_min (by rintro _ ⟨i, rfl⟩; exact hveq i)
      ((convex_singleton c).linear_preimage ψ.toLinearMap)
  have hsub : F ⊆ G := by
    intro x hx
    rw [hGeq]
    exact ⟨hF.subset hx, hconst x hx⟩
  have hdim : Module.finrank ℝ (affineSpan ℝ F).direction =
      Module.finrank ℝ (affineSpan ℝ G).direction :=
    le_antisymm (Submodule.finrank_mono (AffineSubspace.direction_le
      (affineSpan_mono ℝ hsub))) hdim_le
  exact hFG (stellarSupportLower_exposed_eq_of_subset_of_finrank_eq hF hFne hG hsub hdim)

end Grunbaum2003

namespace Grunbaum2003

/-- A strict support inequality at a newly adjoined point preserves its old contact face. -/
theorem stellarSupportLower_face_survives_strict_apex {d : ℕ}
    {P G : Set (Fin d → ℝ)} (hconv : Convex ℝ P)
    (ψ : (Fin d → ℝ) →L[ℝ] ℝ) (c : ℝ)
    (hbound : ∀ x ∈ P, ψ x ≤ c) (hGeq : G = {x ∈ P | ψ x = c})
    (y : Fin d → ℝ) (hy : ψ y < c) :
    IsExposed ℝ (convexHull ℝ (insert y P)) G := by
  intro hGne
  obtain ⟨w, hwG⟩ := hGne
  have hw : w ∈ P ∧ ψ w = c := by simpa [hGeq] using hwG
  have hwQ : w ∈ convexHull ℝ (insert y P) :=
    subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hw.1)
  have hQbound : ∀ x ∈ convexHull ℝ (insert y P), ψ x ≤ c := by
    apply convexHull_min
    · intro x hx
      rcases hx with rfl | hx
      · exact hy.le
      · exact hbound x hx
    · exact (convex_Iic c).linear_preimage ψ.toLinearMap
  refine ⟨ψ, Set.Subset.antisymm ?_ ?_⟩
  · intro x hxG
    have hx : x ∈ P ∧ ψ x = c := by simpa [hGeq] using hxG
    exact ⟨subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hx.1),
      fun z hz => hx.2 ▸ hQbound z hz⟩
  · rintro x ⟨hxQ, hxmax⟩
    have hxlevel : ψ x = c :=
      le_antisymm (hQbound x hxQ) (hw.2 ▸ hxmax w hwQ)
    rw [convexHull_insert ⟨w, hw.1⟩, hconv.convexHull_eq, mem_convexJoin] at hxQ
    rcases hxQ with ⟨y', hy', z, hz, a, b, ha, hb, hab, hrepr⟩
    obtain rfl : y' = y := hy'
    have heq := congrArg ψ hrepr
    simp only [map_add, map_smul, smul_eq_mul, hxlevel] at heq
    have hsum : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
    have ha0 : a = 0 := by
      apply le_antisymm _ ha
      by_contra! hapos
      have hgap := mul_pos hapos (sub_pos.mpr hy)
      have hgap' := mul_nonneg hb (sub_nonneg.mpr (hbound z hz))
      nlinarith
    have hb1 : b = 1 := by linarith
    have hxz : x = z := by simpa [ha0, hb1] using hrepr.symm
    rw [hGeq]
    exact ⟨hxz ▸ hz, hxlevel⟩

/-- A simplicial facet has an apex beyond its prescribed support plane and
strictly beneath prescribed support planes of any finite family of other
proper faces. The selected facet ceases to be exposed after the apex is added. -/
theorem stellarSupportLower_exists_apex_prescribed_supports {d m : ℕ}
    {P F : Set (Fin d → ℝ)} (hP : IsSimplicialDPolytope P)
    (hFne : F.Nonempty) (hF : IsExposed ℝ P F)
    (hFdim : Module.finrank ℝ (affineSpan ℝ F).direction + 1 = d)
    (G : Fin m → Set (Fin d → ℝ))
    (hG : ∀ j, IsExposed ℝ P (G j))
    (hGproper : ∀ j, G j ≠ P)
    (hGF : ∀ j, G j ≠ F)
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (hbound : ∀ x ∈ P, φ x ≤ a) (hFeq : F = {x ∈ P | φ x = a})
    (ψ : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hother_bound : ∀ j x, x ∈ P → ψ j x ≤ c j)
    (hGeq : ∀ j, G j = {x ∈ P | ψ j x = c j}) :
    ∃ y : Fin d → ℝ, y ∉ P ∧ a < φ y ∧ (∀ j, ψ j y < c j) ∧
      (∀ j, IsExposed ℝ (convexHull ℝ (insert y P)) (G j)) ∧
      ¬ IsExposed ℝ (convexHull ℝ (insert y P)) F := by
  have hd : 0 < d := by omega
  obtain ⟨v, hv, hFv⟩ := hP.2 F hFne hF hFdim
  have hvF : ∀ i, v i ∈ F := by
    intro i
    rw [hFv]
    exact subset_convexHull ℝ _ (Set.mem_range_self i)
  have hvP : ∀ i, v i ∈ P := fun i => hF.subset (hvF i)
  have hlevel : ∀ i, φ (v i) = a := by
    intro i
    have hi := hvF i
    rw [hFeq] at hi
    exact hi.2
  have hproper : F ≠ P := by
    intro heq
    have hf := hFdim
    rw [heq, hP.1.2, AffineSubspace.direction_top, finrank_top,
      Module.finrank_fin_fun] at hf
    omega
  have hnot : ¬ P ⊆ F := fun h => hproper (Set.Subset.antisymm hF.subset h)
  obtain ⟨z, hzP, hzF⟩ := Set.not_subset.mp hnot
  have hz : φ z < a := by
    apply lt_of_le_of_ne (hbound z hzP)
    intro heq
    apply hzF
    rw [hFeq]
    exact ⟨hzP, heq⟩
  have hstrict : ∀ j, ∃ i, ψ j (v i) < c j := by
    intro j
    have hj : Module.finrank ℝ (affineSpan ℝ (G j)).direction + 1 ≤ d := by
      rcases (G j).eq_empty_or_nonempty with hE | hN
      · have hzero : Module.finrank ℝ (affineSpan ℝ (G j)).direction = 0 := by simp [hE]
        omega
      · exact stellarSupportLower_proper_face_finrank hP.1 (hG j) hN (hGproper j)
    have hdim : Module.finrank ℝ (affineSpan ℝ (G j)).direction ≤
        Module.finrank ℝ (affineSpan ℝ F).direction := by
      omega
    exact stellarSupportLower_exists_vertex_strict hF hFne (hG j) (Ne.symm (hGF j))
      hdim v hFv (ψ j) (c j) (hother_bound j) (hGeq j)
  have hconv : Convex ℝ P := by
    obtain ⟨V, _, _, rfl⟩ := hP.1.1
    exact convex_convexHull ℝ V
  let w : Fin d → ℝ := (d : ℝ)⁻¹ • ∑ i, v i
  have hsmall := stellarSupportLower_barycenter_apex hd hconv v hvP φ a hbound hlevel z hz ψ c
    (fun j => ⟨fun i => hother_bound j (v i) (hvP i), hstrict j⟩)
  change w ∈ P ∧ φ w = a ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
    a < φ (w + t • (w - z)) ∧ w + t • (w - z) ∉ P ∧
    ∀ j, ψ j (w + t • (w - z)) < c j at hsmall
  obtain ⟨hwP, hwφ, t, ht, _, habove, hout, hrest⟩ := hsmall
  let y := w + t • (w - z)
  refine ⟨y, hout, habove, hrest, ?_, ?_⟩
  · intro j
    exact stellarSupportLower_face_survives_strict_apex hconv (ψ j) (c j)
      (hother_bound j) (hGeq j) y (hrest j)
  intro hFQ
  have hwF : w ∈ F := by
    rw [hFeq]
    exact ⟨hwP, hwφ⟩
  have hzQ : z ∈ convexHull ℝ (insert y P) :=
    subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hzP)
  have hyQ : y ∈ convexHull ℝ (insert y P) :=
    subset_convexHull ℝ _ (Set.mem_insert _ _)
  let r : ℝ := 1 / (1 + t)
  have hden : 0 < 1 + t := by linarith
  have hr0 : 0 < r := div_pos zero_lt_one hden
  have hr1 : r < 1 := (div_lt_one hden).2 (by linarith)
  have hline : AffineMap.lineMap z y r = w := by
    rw [AffineMap.lineMap_apply_module']
    ext i
    change r * (y i - z i) + z i = w i
    dsimp [y, r]
    field_simp [ne_of_gt hden]
    <;> ring
  have hwseg : w ∈ openSegment ℝ z y := by
    rw [← hline]
    exact lineMap_mem_openSegment ℝ z y ⟨hr0, hr1⟩
  exact hout (hF.subset (hFQ.isExtreme.right_mem_of_mem_openSegment hzQ hyQ hwF hwseg))

end Grunbaum2003

open Grunbaum2003 in
theorem solution :
∀ {d m : ℕ}
    {P F : Set (Fin d → ℝ)} (hP : IsSimplicialDPolytope P)
    (hFne : F.Nonempty) (hF : IsExposed ℝ P F)
    (hFdim : Module.finrank ℝ (affineSpan ℝ F).direction + 1 = d)
    (G : Fin m → Set (Fin d → ℝ))
    (hG : ∀ j, IsExposed ℝ P (G j))
    (hGproper : ∀ j, G j ≠ P)
    (hGF : ∀ j, G j ≠ F)
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (hbound : ∀ x ∈ P, φ x ≤ a) (hFeq : F = {x ∈ P | φ x = a})
    (ψ : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hother_bound : ∀ j x, x ∈ P → ψ j x ≤ c j)
    (hGeq : ∀ j, G j = {x ∈ P | ψ j x = c j}),
∃ y : Fin d → ℝ, y ∉ P ∧ a < φ y ∧ (∀ j, ψ j y < c j) ∧
      (∀ j, IsExposed ℝ (convexHull ℝ (insert y P)) (G j)) ∧
      ¬ IsExposed ℝ (convexHull ℝ (insert y P)) F :=
  @Grunbaum2003.stellarSupportLower_exists_apex_prescribed_supports
