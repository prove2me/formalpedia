-- Prove2me | solution 1 for Grunbaum2003.pyramid_extension_set_and_face_classification
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T04:48:18.891418+00:00
-- url     : https://prove2.me/submissions/154ce636-8375-4e97-aa36-063e60cb42ca

import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Compact


set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003

/-- An apex beyond one supporting plane and beneath every other plane adds
exactly the pyramid over the chosen face. The family of other planes may be infinite. -/
theorem convexHull_insert_eq_union_pyramid
    {d : ℕ} {ι : Type*} (P : Set (Fin d → ℝ))
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (ψ : ι → (Fin d → ℝ) →L[ℝ] ℝ) (c : ι → ℝ)
    (hP : P = {x | φ x ≤ a ∧ ∀ j, ψ j x ≤ c j})
    (hPne : P.Nonempty) (y : Fin d → ℝ)
    (hyφ : a < φ y) (hyψ : ∀ j, ψ j y ≤ c j) :
    convexHull ℝ (insert y P) =
      P ∪ convexHull ℝ (insert y {x ∈ P | φ x = a}) := by
  have hmem (x : Fin d → ℝ) : x ∈ P ↔ φ x ≤ a ∧ ∀ j, ψ j x ≤ c j := by
    rw [hP]
    rfl
  have hconv : Convex ℝ P := by
    intro x hx z hz u v hu hv huv
    rw [hmem] at hx hz ⊢
    constructor
    · simp only [map_add, map_smul, smul_eq_mul]
      calc
        u * φ x + v * φ z ≤ u * a + v * a :=
          add_le_add (mul_le_mul_of_nonneg_left hx.1 hu)
            (mul_le_mul_of_nonneg_left hz.1 hv)
        _ = a := by rw [← add_mul, huv, one_mul]
    · intro j
      simp only [map_add, map_smul, smul_eq_mul]
      calc
        u * ψ j x + v * ψ j z ≤ u * c j + v * c j :=
          add_le_add (mul_le_mul_of_nonneg_left (hx.2 j) hu)
            (mul_le_mul_of_nonneg_left (hz.2 j) hv)
        _ = c j := by rw [← add_mul, huv, one_mul]
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hxP : x ∈ P
    · exact Or.inl hxP
    right
    rw [convexHull_insert hPne, hconv.convexHull_eq, mem_convexJoin] at hx
    obtain ⟨y', hy', z, hz, u, v, hu, hv, huv, hrep⟩ := hx
    have heqy : y' = y := hy'
    subst y'
    have hzφ := ((hmem z).mp hz).1
    have hzψ := ((hmem z).mp hz).2
    have hxψ (j : ι) : ψ j x ≤ c j := by
      rw [← hrep]
      simp only [map_add, map_smul, smul_eq_mul]
      calc
        u * ψ j y + v * ψ j z ≤ u * c j + v * c j :=
          add_le_add (mul_le_mul_of_nonneg_left (hyψ j) hu)
            (mul_le_mul_of_nonneg_left (hzψ j) hv)
        _ = c j := by rw [← add_mul, huv, one_mul]
    have hxφ : a < φ x := by
      by_contra! h
      exact hxP ((hmem x).mpr ⟨h, hxψ⟩)
    have hD : 0 < φ y - φ z := by linarith
    have hD0 : φ y - φ z ≠ 0 := ne_of_gt hD
    let r : ℝ := (a - φ z) / (φ y - φ z)
    let s : ℝ := (φ y - a) / (φ y - φ z)
    have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr hzφ) hD.le
    have hs : 0 < s := div_pos (sub_pos.mpr hyφ) hD
    have hrs : r + s = 1 := by
      dsimp [r, s]
      field_simp
      ring
    let w : Fin d → ℝ := r • y + s • z
    have hwφ : φ w = a := by
      dsimp [w]
      simp only [map_add, map_smul, smul_eq_mul]
      dsimp [r, s]
      field_simp
      ring
    have hwψ (j : ι) : ψ j w ≤ c j := by
      dsimp [w]
      simp only [map_add, map_smul, smul_eq_mul]
      calc
        r * ψ j y + s * ψ j z ≤ r * c j + s * c j :=
          add_le_add (mul_le_mul_of_nonneg_left (hyψ j) hr)
            (mul_le_mul_of_nonneg_left (hzψ j) hs.le)
        _ = c j := by rw [← add_mul, hrs, one_mul]
    have hw : w ∈ {x ∈ P | φ x = a} :=
      ⟨(hmem w).mpr ⟨hwφ.le, hwψ⟩, hwφ⟩
    have hvle : v ≤ s := by
      apply (le_div_iff₀ hD).mpr
      have hval := congrArg φ hrep
      simp only [map_add, map_smul, smul_eq_mul] at hval
      nlinarith [congrArg (fun q : ℝ => q * φ y) huv]
    have hvs : 0 ≤ v / s := div_nonneg hv hs.le
    have hvs1 : v / s ≤ 1 := (div_le_one hs).mpr hvle
    have hwHull : w ∈ convexHull ℝ (insert y {x ∈ P | φ x = a}) :=
      subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hw)
    have hyHull : y ∈ convexHull ℝ (insert y {x ∈ P | φ x = a}) :=
      subset_convexHull ℝ _ (Set.mem_insert _ _)
    have heq : (1 - v / s) • y + (v / s) • w = x := by
      rw [← hrep]
      dsimp [w]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hs0 : s ≠ 0 := ne_of_gt hs
      field_simp
      nlinarith [congrArg (fun q : ℝ => q * (v * y i)) hrs,
        congrArg (fun q : ℝ => q * (s * y i)) huv]
    rw [← heq]
    exact (convex_convexHull ℝ _) hyHull hwHull
      (sub_nonneg.mpr hvs1) hvs (by ring)
  · rintro x (hx | hx)
    · exact subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hx)
    · exact convexHull_mono (by
        intro z hz
        rcases hz with rfl | hz
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ hz.1) hx

end Grunbaum2003



set_option autoImplicit false
open scoped Classical Topology

namespace Grunbaum2003

/-- A proper supporting plane through an apex that violates only one of finitely
many defining inequalities meets the old polytope only in that chosen facet. -/
theorem support_through_apex_meets_chosen_face
    {d : ℕ} {ι : Type*} [Finite ι] (P : Set (Fin d → ℝ))
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (ψ : ι → (Fin d → ℝ) →L[ℝ] ℝ) (c : ι → ℝ)
    (hP : P = {x | φ x ≤ a ∧ ∀ j, ψ j x ≤ c j})
    (y : Fin d → ℝ) (hyφ : a < φ y) (hyψ : ∀ j, ψ j y < c j)
    (θ : (Fin d → ℝ) →L[ℝ] ℝ) (hθ : θ ≠ 0)
    (hmax : ∀ x ∈ P, θ x ≤ θ y) :
    ∀ x ∈ P, θ x = θ y → φ x = a := by
  intro x hx hθx
  have hxmem : φ x ≤ a ∧ ∀ j, ψ j x ≤ c j := by simpa [hP] using hx
  by_contra hxa
  have hxφ : φ x < a := lt_of_le_of_ne hxmem.1 hxa
  have hD : 0 < φ y - φ x := by linarith
  have hD0 : φ y - φ x ≠ 0 := ne_of_gt hD
  let s : ℝ := (a - φ x) / (2 * (φ y - φ x))
  have hs : 0 < s := div_pos (sub_pos.mpr hxφ) (by positivity)
  have hs1 : s < 1 := by
    apply (div_lt_one (by positivity : 0 < 2 * (φ y - φ x))).mpr
    linarith
  have hsD : s * (φ y - φ x) = (a - φ x) / 2 := by
    dsimp [s]
    field_simp
  let q : Fin d → ℝ := s • y + (1 - s) • x
  have hqφ : φ q < a := by
    dsimp [q]
    simp only [map_add, map_smul, smul_eq_mul]
    nlinarith [hsD]
  have hqψ (j : ι) : ψ j q < c j := by
    dsimp [q]
    simp only [map_add, map_smul, smul_eq_mul]
    calc
      s * ψ j y + (1 - s) * ψ j x < s * c j + (1 - s) * c j :=
        add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (hyψ j) hs)
          (mul_le_mul_of_nonneg_left (hxmem.2 j) (by linarith))
      _ = c j := by ring
  have hqθ : θ q = θ y := by
    dsimp [q]
    simp only [map_add, map_smul, smul_eq_mul, hθx]
    ring
  let U : Set (Fin d → ℝ) := {z | φ z < a ∧ ∀ j, ψ j z < c j}
  have hU : IsOpen U := by
    have hUeq : U = {z | φ z < a} ∩ ⋂ j, {z | ψ j z < c j} := by
      ext z
      simp [U]
    rw [hUeq]
    exact (isOpen_lt φ.continuous continuous_const).inter
      (isOpen_iInter_of_finite (fun j => isOpen_lt (ψ j).continuous continuous_const))
  have hqU : q ∈ U := ⟨hqφ, hqψ⟩
  have hmaxq : IsLocalMax (fun z => θ z) q := by
    filter_upwards [hU.mem_nhds hqU] with z hz
    have hzP : z ∈ P := by
      rw [hP]
      exact ⟨hz.1.le, fun j => (hz.2 j).le⟩
    simpa only [hqθ] using hmax z hzP
  exact hθ (hmaxq.hasFDerivAt_eq_zero θ.hasFDerivAt)

end Grunbaum2003


namespace Grunbaum2003

private lemma exposed_eq_level {d : ℕ} {P : Set (Fin d → ℝ)}
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) {w : Fin d → ℝ} (hw : w ∈ P)
    (hmax : ∀ x ∈ P, φ x ≤ φ w) :
    φ.toExposed P = {x ∈ P | φ x = φ w} := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, le_antisymm (hmax x hx.1) (hx.2 w hw)⟩
  · rintro ⟨hx, heq⟩
    exact ⟨hx, fun z hz => by rw [heq]; exact hmax z hz⟩

private lemma hull_bound {d : ℕ} {P : Set (Fin d → ℝ)}
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (c : ℝ)
    (hmax : ∀ x ∈ P, φ x ≤ c) {y : Fin d → ℝ} (hy : φ y ≤ c) :
    ∀ x ∈ convexHull ℝ (insert y P), φ x ≤ c := by
  apply convexHull_min
  · intro x hx
    rcases hx with rfl | hx
    · exact hy
    · exact hmax x hx
  · exact (convex_Iic c).linear_preimage φ.toLinearMap

/-- Adding an apex changes each support maximizer set according to its height
relative to the old support value. -/
theorem exposed_insert_trichotomy {d : ℕ} {P : Set (Fin d → ℝ)} (hP : Convex ℝ P)
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (w : Fin d → ℝ) (hw : w ∈ P)
    (hmax : ∀ x ∈ P, φ x ≤ φ w) (y : Fin d → ℝ) :
    (φ y < φ w → φ.toExposed (convexHull ℝ (insert y P)) = φ.toExposed P) ∧
    (φ y = φ w → φ.toExposed (convexHull ℝ (insert y P)) =
      convexHull ℝ (insert y (φ.toExposed P))) ∧
    (φ w < φ y → φ.toExposed (convexHull ℝ (insert y P)) = {y}) := by
  have hrepr (x : Fin d → ℝ) (hx : x ∈ convexHull ℝ (insert y P)) :
      ∃ z ∈ P, ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧
        a • y + b • z = x := by
    rw [convexHull_insert ⟨w, hw⟩, hP.convexHull_eq, mem_convexJoin] at hx
    rcases hx with ⟨y', hy', z, hz, a, b, ha, hb, hab, hx⟩
    obtain rfl : y' = y := hy'
    exact ⟨z, hz, a, b, ha, hb, hab, hx⟩
  have hwHull : w ∈ convexHull ℝ (insert y P) :=
    subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hw)
  have hyHull : y ∈ convexHull ℝ (insert y P) :=
    subset_convexHull ℝ _ (Set.mem_insert _ _)
  refine ⟨?_, ?_, ?_⟩
  · intro hy
    rw [exposed_eq_level φ hwHull (hull_bound φ (φ w) hmax hy.le),
      exposed_eq_level φ hw hmax]
    ext x
    constructor
    · rintro ⟨hx, heq⟩
      obtain ⟨z, hz, a, b, ha, hb, hab, hrep⟩ := hrepr x hx
      have heq' := congrArg φ hrep
      simp only [map_add, map_smul, smul_eq_mul] at heq'
      have hs : a * φ w + b * φ w = φ w := by rw [← add_mul, hab, one_mul]
      have ha0 : a = 0 := by
        apply le_antisymm _ ha
        by_contra! hapos
        have hgap := mul_pos hapos (sub_pos.mpr hy)
        have hgap' := mul_nonneg hb (sub_nonneg.mpr (hmax z hz))
        nlinarith
      have hb1 : b = 1 := by linarith
      have hxz : x = z := by simpa [ha0, hb1] using hrep.symm
      exact ⟨hxz ▸ hz, heq⟩
    · rintro ⟨hx, heq⟩
      exact ⟨subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hx), heq⟩
  · intro hy
    rw [exposed_eq_level φ hwHull (hull_bound φ (φ w) hmax hy.le)]
    apply Set.Subset.antisymm
    · rintro x ⟨hx, heq⟩
      obtain ⟨z, hz, a, b, ha, hb, hab, hrep⟩ := hrepr x hx
      have heq' := congrArg φ hrep
      simp only [map_add, map_smul, smul_eq_mul, hy] at heq'
      have hs : a * φ w + b * φ w = φ w := by rw [← add_mul, hab, one_mul]
      by_cases hb0 : b = 0
      · have ha1 : a = 1 := by linarith
        have hxy : x = y := by simpa [hb0, ha1] using hrep.symm
        rw [hxy]
        exact subset_convexHull ℝ _ (Set.mem_insert _ _)
      · have hzmax : φ z = φ w := by
          apply le_antisymm (hmax z hz)
          by_contra! hzlt
          have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
          have hgap := mul_pos hbpos (sub_pos.mpr hzlt)
          nlinarith
        have hzF : z ∈ φ.toExposed P := by
          rw [exposed_eq_level φ hw hmax]
          exact ⟨hz, hzmax⟩
        rw [← hrep]
        exact (convex_convexHull ℝ _)
          (subset_convexHull ℝ _ (Set.mem_insert _ _))
          (subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hzF)) ha hb hab
    · have hsub : insert y (φ.toExposed P) ⊆
          {x ∈ convexHull ℝ (insert y P) | φ x = φ w} := by
        intro x hx
        rcases hx with rfl | hx
        · exact ⟨hyHull, hy⟩
        · exact ⟨subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hx.1),
            le_antisymm (hmax x hx.1) (hx.2 w hw)⟩
      apply convexHull_min hsub
      exact (convex_convexHull ℝ _).inter
        ((convex_singleton (φ w)).linear_preimage φ.toLinearMap)
  · intro hy
    have hmaxY : ∀ x ∈ P, φ x ≤ φ y := fun x hx => (hmax x hx).trans hy.le
    rw [exposed_eq_level φ hyHull (hull_bound φ (φ y) hmaxY le_rfl)]
    ext x
    constructor
    · rintro ⟨hx, heq⟩
      obtain ⟨z, hz, a, b, ha, hb, hab, hrep⟩ := hrepr x hx
      have heq' := congrArg φ hrep
      simp only [map_add, map_smul, smul_eq_mul] at heq'
      have hs : a * φ y + b * φ y = φ y := by rw [← add_mul, hab, one_mul]
      have hb0 : b = 0 := by
        apply le_antisymm _ hb
        by_contra! hbpos
        have hgap := mul_pos hbpos (sub_pos.mpr (lt_of_le_of_lt (hmax z hz) hy))
        nlinarith
      have ha1 : a = 1 := by linarith
      simpa [hb0, ha1] using hrep.symm
    · intro hx
      obtain rfl : x = y := hx
      exact ⟨hyHull, rfl⟩

end Grunbaum2003

namespace Grunbaum2003

/-- Every new nonempty proper exposed face is an old face, the apex, or a cone
whose base is an old exposed face contained in the chosen supporting plane. -/
theorem exposed_faces_of_pyramid_extension
    {d : ℕ} {ι : Type*} [Finite ι] (P : Set (Fin d → ℝ))
    (hconv : Convex ℝ P) (hcompact : IsCompact P) (hPne : P.Nonempty)
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (ψ : ι → (Fin d → ℝ) →L[ℝ] ℝ) (c : ι → ℝ)
    (hP : P = {x | φ x ≤ a ∧ ∀ j, ψ j x ≤ c j})
    (y : Fin d → ℝ) (hyφ : a < φ y) (hyψ : ∀ j, ψ j y < c j)
    (H : Set (Fin d → ℝ)) (hHne : H.Nonempty)
    (hH : IsExposed ℝ (convexHull ℝ (insert y P)) H)
    (hproper : H ≠ convexHull ℝ (insert y P)) :
    H = {y} ∨ IsExposed ℝ P H ∨
      ∃ G : Set (Fin d → ℝ), G.Nonempty ∧ IsExposed ℝ P G ∧
        G ⊆ {x ∈ P | φ x = a} ∧ H = convexHull ℝ (insert y G) := by
  obtain ⟨θ, hθH⟩ := hH hHne
  change H = θ.toExposed (convexHull ℝ (insert y P)) at hθH
  have hθ : θ ≠ 0 := by
    intro hz
    apply hproper
    simpa [hz, ContinuousLinearMap.toExposed] using hθH
  obtain ⟨w, hw, hmaxOn⟩ := hcompact.exists_isMaxOn hPne θ.continuous.continuousOn
  have hmax : ∀ x ∈ P, θ x ≤ θ w := fun _ hx => hmaxOn hx
  have hsplit := exposed_insert_trichotomy hconv θ w hw hmax y
  rcases lt_trichotomy (θ y) (θ w) with hlt | heq | hgt
  · right; left
    rw [hθH, hsplit.1 hlt]
    exact ContinuousLinearMap.toExposed.isExposed (l := θ)
  · right; right
    refine ⟨θ.toExposed P, ⟨w, hw, hmax⟩,
      ContinuousLinearMap.toExposed.isExposed (l := θ), ?_, hθH.trans (hsplit.2.1 heq)⟩
    intro x hx
    have hmax' : ∀ z ∈ P, θ z ≤ θ y := by simpa only [heq] using hmax
    have hxθ : θ x = θ y := (le_antisymm (hmax x hx.1) (hx.2 w hw)).trans heq.symm
    exact ⟨hx.1, support_through_apex_meets_chosen_face P φ a ψ c hP y hyφ hyψ θ hθ
      hmax' x hx.1 hxθ⟩
  · exact Or.inl (hθH.trans (hsplit.2.2 hgt))

/-- Tilting an old support functional by the chosen facet normal exposes the
cone over every base face whose old support plane strictly separates the apex. -/
theorem cone_exposed_of_support_below_apex
    {d : ℕ} {P : Set (Fin d → ℝ)} (hconv : Convex ℝ P)
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ) (hφ : ∀ x ∈ P, φ x ≤ a)
    (ℓ : (Fin d → ℝ) →L[ℝ] ℝ) (w : Fin d → ℝ) (hw : w ∈ P)
    (hmax : ∀ x ∈ P, ℓ x ≤ ℓ w)
    (hface : ℓ.toExposed P ⊆ {x | φ x = a})
    (y : Fin d → ℝ) (hyφ : a < φ y) (hyℓ : ℓ y < ℓ w) :
    IsExposed ℝ (convexHull ℝ (insert y P))
      (convexHull ℝ (insert y (ℓ.toExposed P))) := by
  let t : ℝ := (ℓ w - ℓ y) / (φ y - a)
  have ht : 0 < t := div_pos (sub_pos.mpr hyℓ) (sub_pos.mpr hyφ)
  have htD : t * (φ y - a) = ℓ w - ℓ y :=
    div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hyφ))
  let θ : (Fin d → ℝ) →L[ℝ] ℝ := ℓ + t • φ
  have hwφ : φ w = a := hface ⟨hw, hmax⟩
  have hθw : θ w = ℓ w + t * a := by simp [θ, hwφ]
  have hθmax : ∀ x ∈ P, θ x ≤ θ w := by
    intro x hx
    simp only [θ, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hwφ]
    exact add_le_add (hmax x hx) (mul_le_mul_of_nonneg_left (hφ x hx) ht.le)
  have hθy : θ y = θ w := by
    simp only [θ, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hwφ]
    nlinarith [htD]
  have hfaces : θ.toExposed P = ℓ.toExposed P := by
    rw [exposed_eq_level θ hw hθmax, exposed_eq_level ℓ hw hmax]
    ext x
    constructor
    · rintro ⟨hx, hxθ⟩
      refine ⟨hx, ?_⟩
      have hnonneg := mul_nonneg ht.le (sub_nonneg.mpr (hφ x hx))
      simp only [θ, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at hxθ
      rw [hwφ] at hxθ
      linarith [hmax x hx]
    · rintro ⟨hx, hxℓ⟩
      have hxφ : φ x = a := hface ⟨hx, fun z hz => by rw [hxℓ]; exact hmax z hz⟩
      exact ⟨hx, by simp [θ, hxℓ, hwφ, hxφ]⟩
  have heq := (exposed_insert_trichotomy hconv θ w hw hθmax y).2.1 hθy
  rw [hfaces] at heq
  rw [← heq]
  exact ContinuousLinearMap.toExposed.isExposed (l := θ)

end Grunbaum2003


namespace Grunbaum2003

/-- Set and exposed-face geometry for adjoining a point beyond one facet. -/
theorem pyramid_extension_set_and_face_classification
    {d m : ℕ} (P : Set (Fin d → ℝ))
    (hconv : Convex ℝ P) (hcompact : IsCompact P) (hPne : P.Nonempty)
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (ψ : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hP : P = {x | φ x ≤ a ∧ ∀ j, ψ j x ≤ c j})
    (y : Fin d → ℝ) (hyφ : a < φ y) (hyψ : ∀ j, ψ j y < c j) :
    (convexHull ℝ (insert y P) =
      P ∪ convexHull ℝ (insert y {x ∈ P | φ x = a})) ∧
    (∀ H : Set (Fin d → ℝ), H.Nonempty →
      IsExposed ℝ (convexHull ℝ (insert y P)) H →
      H ≠ convexHull ℝ (insert y P) →
      H = {y} ∨ IsExposed ℝ P H ∨
        ∃ G : Set (Fin d → ℝ), G.Nonempty ∧ IsExposed ℝ P G ∧
          G ⊆ {x ∈ P | φ x = a} ∧ H = convexHull ℝ (insert y G)) ∧
    (∀ (ℓ : (Fin d → ℝ) →L[ℝ] ℝ) (w : Fin d → ℝ), w ∈ P →
      (∀ x ∈ P, ℓ x ≤ ℓ w) → ℓ y < ℓ w →
      IsExposed ℝ (convexHull ℝ (insert y P)) (ℓ.toExposed P) ∧
      (ℓ.toExposed P ⊆ {x | φ x = a} →
        IsExposed ℝ (convexHull ℝ (insert y P))
          (convexHull ℝ (insert y (ℓ.toExposed P))))) := by
  refine ⟨convexHull_insert_eq_union_pyramid P φ a ψ c hP hPne y hyφ
    (fun j => (hyψ j).le), ?_, ?_⟩
  · exact fun H hne hH hp => exposed_faces_of_pyramid_extension P hconv hcompact hPne
      φ a ψ c hP y hyφ hyψ H hne hH hp
  · intro ℓ w hw hmax hyℓ
    constructor
    · rw [← (exposed_insert_trichotomy hconv ℓ w hw hmax y).1 hyℓ]
      exact ContinuousLinearMap.toExposed.isExposed (l := ℓ)
    · intro hface
      apply cone_exposed_of_support_below_apex hconv φ a _ ℓ w hw hmax hface y hyφ hyℓ
      intro x hx
      rw [hP] at hx
      exact hx.1

end Grunbaum2003

open Grunbaum2003 in
theorem solution :
∀ {d m : ℕ} (P : Set (Fin d → ℝ))
    (hconv : Convex ℝ P) (hcompact : IsCompact P) (hPne : P.Nonempty)
    (φ : (Fin d → ℝ) →L[ℝ] ℝ) (a : ℝ)
    (ψ : Fin m → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin m → ℝ)
    (hP : P = {x | φ x ≤ a ∧ ∀ j, ψ j x ≤ c j})
    (y : Fin d → ℝ) (hyφ : a < φ y) (hyψ : ∀ j, ψ j y < c j),
(convexHull ℝ (insert y P) =
      P ∪ convexHull ℝ (insert y {x ∈ P | φ x = a})) ∧
    (∀ H : Set (Fin d → ℝ), H.Nonempty →
      IsExposed ℝ (convexHull ℝ (insert y P)) H →
      H ≠ convexHull ℝ (insert y P) →
      H = {y} ∨ IsExposed ℝ P H ∨
        ∃ G : Set (Fin d → ℝ), G.Nonempty ∧ IsExposed ℝ P G ∧
          G ⊆ {x ∈ P | φ x = a} ∧ H = convexHull ℝ (insert y G)) ∧
    (∀ (ℓ : (Fin d → ℝ) →L[ℝ] ℝ) (w : Fin d → ℝ), w ∈ P →
      (∀ x ∈ P, ℓ x ≤ ℓ w) → ℓ y < ℓ w →
      IsExposed ℝ (convexHull ℝ (insert y P)) (ℓ.toExposed P) ∧
      (ℓ.toExposed P ⊆ {x | φ x = a} →
        IsExposed ℝ (convexHull ℝ (insert y P))
          (convexHull ℝ (insert y (ℓ.toExposed P))))) :=
  @Grunbaum2003.pyramid_extension_set_and_face_classification
