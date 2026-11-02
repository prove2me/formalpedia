-- Prove2me | solution 2 for Grunbaum2003.boundary_refines_simplex
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T20:30:23.913884+00:00
-- url     : https://prove2.me/submissions/f228a1f9-a39f-47ca-9c3c-7a3107be3d29

import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Analysis.Convex.Exposed
import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Data.Set.Card
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Lean.Elab.Tactic.Omega
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Fin.SuccPred
import Definitions.Def_Grunbaum2003_boundaryFaces
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Definitions.Def_Grunbaum2003_BoundaryRefines
import Mathlib.Topology.Algebra.ContinuousAffineEquiv
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.AffineSpace.Independent

-- Checked local ingredient: Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

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

/-- Grünbaum (2003), Theorem 3.2.2 (p. 36): for every `d`-polytope `P`, the set of exposed
vertices `{x | IsExposed ℝ P {x}}` is finite, and every exposed face `F` of `P` equals the
convex hull of the exposed vertices of `P` contained in `F`. -/
theorem polytope_face_eq_convexHull_exposed_vertices (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ F : PolytopeFace P,
        F.val = convexHull ℝ (F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}) := by
  rcases hP.1 with ⟨V0, hV0_fin, _, hP_eq⟩
  have hExtEq : P.extremePoints ℝ = {x : Fin d → ℝ | IsExposed ℝ P {x}} :=
    extremePoints_eq_exposedSingletons P hP
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

end Grunbaum2003


-- Checked local ingredient: GeometryClosure

-- Exact checked component: CutHull

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

/-- Explicit vertex-figure hull identity for a hyperplane separating one generator from all others.
Private development for the boundary-refinement induction. No finiteness assumption on `W`. -/
theorem convexHull_insert_inter_level_eq (d : ℕ) (v : Fin d → ℝ)
    (W : Set (Fin d → ℝ)) (hW : W.Nonempty)
    (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α) :
    convexHull ℝ (insert v W) ∩ l ⁻¹' {α} =
      convexHull ℝ ((fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))) '' W) := by
  classical
  let q : (Fin d → ℝ) → (Fin d → ℝ) :=
    fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))
  have hD : 0 < l v - α := sub_pos.mpr hα
  have hq (w : Fin d → ℝ) (hw : w ∈ W) :
      q w ∈ convexHull ℝ (insert v W) ∧ l (q w) = α := by
    have hDen : 0 < l v - l w := sub_pos.mpr ((hBelow w hw).trans hα)
    have ht0 : 0 ≤ (l v - α) / (l v - l w) := (div_pos hD hDen).le
    have ht1 : (l v - α) / (l v - l w) ≤ 1 :=
      (div_le_one hDen).mpr (by linarith [hBelow w hw])
    constructor
    · exact (convex_convexHull ℝ _).lineMap_mem
        (subset_convexHull ℝ _ (Set.mem_insert v W))
        (subset_convexHull ℝ _ (Set.mem_insert_of_mem v hw)) ⟨ht0, ht1⟩
    · have hMul : ((l v - α) / (l v - l w)) * (l v - l w) = l v - α :=
        div_mul_cancel₀ _ hDen.ne'
      dsimp [q]
      rw [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul]
      nlinarith [hMul]
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxLevel⟩
    change l x = α at hxLevel
    obtain ⟨ι, hι, a, z, ha, haSum, hz, haz⟩ := mem_convexHull_iff_exists_fintype.mp hx
    letI := hι
    obtain ⟨w₀, hw₀⟩ := hW
    let b : ι → ℝ := fun i => a i * (l v - l (z i)) / (l v - α)
    let u : ι → (Fin d → ℝ) := fun i => if z i = v then q w₀ else q (z i)
    have hzLe (i : ι) : l (z i) ≤ l v := by
      rcases hz i with h | h
      · simpa only [h] using le_refl (l v)
      · exact ((hBelow (z i) h).trans hα).le
    have hb (i : ι) : 0 ≤ b i := div_nonneg (mul_nonneg (ha i) (sub_nonneg.mpr (hzLe i))) hD.le
    have hlSum : ∑ i, a i * l (z i) = α := by
      have h := congrArg l haz
      simpa only [map_sum, map_smul, smul_eq_mul, hxLevel] using h
    have hbSum : ∑ i, b i = 1 := by
      calc
        ∑ i, b i = (∑ i, a i * (l v - l (z i))) / (l v - α) := by
          simp only [b, div_eq_mul_inv, Finset.sum_mul]
        _ = ((∑ i, a i) * l v - ∑ i, a i * l (z i)) / (l v - α) := by
          simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
        _ = 1 := by rw [haSum, hlSum, one_mul, div_self hD.ne']
    have hu (i : ι) : u i ∈ q '' W := by
      dsimp [u]
      split_ifs with hi
      · exact ⟨w₀, hw₀, rfl⟩
      · exact ⟨z i, (Set.mem_insert_iff.mp (hz i)).resolve_left hi, rfl⟩
    have hTerm (i : ι) : b i • u i = b i • v + a i • (z i - v) := by
      by_cases hi : z i = v
      · simp [u, b, hi]
      · have hzi : z i ∈ W := (Set.mem_insert_iff.mp (hz i)).resolve_left hi
        have hDen : l v - l (z i) ≠ 0 := (sub_pos.mpr ((hBelow (z i) hzi).trans hα)).ne'
        have hCoef : b i * ((l v - α) / (l v - l (z i))) = a i := by
          dsimp [b]
          field_simp [hD.ne', hDen] <;> ring
        dsimp [u]
        rw [if_neg hi]
        dsimp [q]
        rw [AffineMap.lineMap_apply_module', smul_add, smul_smul, hCoef, add_comm]
    apply mem_convexHull_of_exists_fintype b u hb hbSum hu
    calc
      ∑ i, b i • u i = ∑ i, (b i • v + a i • (z i - v)) := Finset.sum_congr rfl (fun i _ => hTerm i)
      _ = (∑ i, b i) • v + (∑ i, a i • z i - (∑ i, a i) • v) := by
        simp only [Finset.sum_add_distrib, smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]
      _ = x := by rw [hbSum, haSum, haz, one_smul]; abel
  · apply convexHull_min
    · rintro _ ⟨w, hw, rfl⟩
      exact hq w hw
    · apply (convex_convexHull ℝ _).inter
      intro x hx y hy a b ha hb hab
      change l x = α at hx
      change l y = α at hy
      change l (a • x + b • y) = α
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hx, hy]
      rw [← add_mul, hab, one_mul]

end Grunbaum2003


-- Exact checked component: FaceLift

set_option autoImplicit false

namespace Grunbaum2003

/-- Lift an exposed vertex-figure face to a face of the original hull containing the apex.
Private development for the face-respecting boundary-refinement induction. -/
theorem exposed_vertex_figure_face_lift (d : ℕ) (v : Fin d → ℝ)
    (W : Set (Fin d → ℝ)) (hW : W.Nonempty)
    (l m : StrongDual ℝ (Fin d → ℝ)) (α β : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α)
    (hMax : ∀ x ∈ convexHull ℝ (insert v W) ∩ l ⁻¹' {α}, m x ≤ β) :
    let P := convexHull ℝ (insert v W)
    let n := m + ((β - m v) / (l v - α)) • l
    let G := {x ∈ P | n x = n v}
    (∀ x ∈ P, n x ≤ n v) ∧ IsExposed ℝ P G ∧ v ∈ G ∧
      {x ∈ P ∩ l ⁻¹' {α} | m x = β} = G ∩ l ⁻¹' {α} := by
  classical
  let P := convexHull ℝ (insert v W)
  let c : ℝ := (β - m v) / (l v - α)
  let n : StrongDual ℝ (Fin d → ℝ) := m + c • l
  let G := {x ∈ P | n x = n v}
  change (∀ x ∈ P, n x ≤ n v) ∧ IsExposed ℝ P G ∧ v ∈ G ∧
    {x ∈ P ∩ l ⁻¹' {α} | m x = β} = G ∩ l ⁻¹' {α}
  have hD : 0 < l v - α := sub_pos.mpr hα
  have hcMul : c * (l v - α) = β - m v := div_mul_cancel₀ _ hD.ne'
  have hvP : v ∈ P := subset_convexHull ℝ _ (Set.mem_insert _ _)
  have hGen (w : Fin d → ℝ) (hw : w ∈ insert v W) : n w ≤ n v := by
    rcases hw with rfl | hw
    · exact le_rfl
    · have hDen : 0 < l v - l w := sub_pos.mpr ((hBelow w hw).trans hα)
      let q := AffineMap.lineMap v w ((l v - α) / (l v - l w))
      have hq : q ∈ P ∩ l ⁻¹' {α} := by
        have hmem : q ∈ convexHull ℝ
            ((fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))) '' W) :=
          subset_convexHull ℝ _ ⟨w, hw, rfl⟩
        rwa [← convexHull_insert_inter_level_eq d v W hW l α hα hBelow] at hmem
      have hM := hMax q hq
      have hmq : m q = ((l v - α) * (m w - m v)) / (l v - l w) + m v := by
        dsimp [q]
        rw [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul]
        ring
      rw [hmq] at hM
      have hFrac : ((l v - α) * (m w - m v)) / (l v - l w) ≤ β - m v := by linarith
      have hWeighted : (l v - α) * (m w - m v) ≤ (l v - α) * (c * (l v - l w)) := by
        calc
          (l v - α) * (m w - m v) ≤ (β - m v) * (l v - l w) := (div_le_iff₀ hDen).mp hFrac
          _ = (c * (l v - α)) * (l v - l w) := by rw [hcMul]
          _ = (l v - α) * (c * (l v - l w)) := by ring
      have hBound : m w - m v ≤ c * (l v - l w) := (mul_le_mul_iff_right₀ hD).mp hWeighted
      change m w + c * l w ≤ m v + c * l v
      nlinarith [hBound]
  have hN : ∀ x ∈ P, n x ≤ n v := by
    apply convexHull_min hGen
    intro x hx y hy a b ha hb hab
    change n (a • x + b • y) ≤ n v
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    calc
      a * n x + b * n y ≤ a * n v + b * n v :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
      _ = n v := by rw [← add_mul, hab, one_mul]
  have hG : IsExposed ℝ P G := by
    intro _
    refine ⟨n, ?_⟩
    ext x
    constructor
    · rintro ⟨hxP, hxEq⟩
      refine ⟨hxP, fun y hy => ?_⟩
      calc n y ≤ n v := hN y hy
           _ = n x := hxEq.symm
    · rintro ⟨hxP, hxMax⟩
      exact ⟨hxP, le_antisymm (hN x hxP) (hxMax v hvP)⟩
  have hEq (x : Fin d → ℝ) (hx : l x = α) : n x = n v ↔ m x = β := by
    change m x + c * l x = m v + c * l v ↔ m x = β
    rw [hx]
    constructor <;> intro h <;> nlinarith [hcMul]
  refine ⟨hN, hG, ⟨hvP, rfl⟩, ?_⟩
  ext x
  constructor
  · rintro ⟨⟨hxP, hxLevel⟩, hxM⟩
    exact ⟨⟨hxP, (hEq x hxLevel).mpr hxM⟩, hxLevel⟩
  · rintro ⟨⟨hxP, hxN⟩, hxLevel⟩
    exact ⟨⟨hxP, hxLevel⟩, (hEq x hxLevel).mp hxN⟩

end Grunbaum2003


-- Exact checked component: FaceRestriction

set_option autoImplicit false

namespace Grunbaum2003

/-- Restriction of a supporting face to a subset, including the empty intersection. -/
theorem isExposed_inter_restrict {d : ℕ} {P G B : Set (Fin d → ℝ)}
    (hG : IsExposed ℝ P G) (hBP : B ⊆ P) : IsExposed ℝ B (G ∩ B) := by
  intro hNonempty
  obtain ⟨z, hzG, hzB⟩ := hNonempty
  obtain ⟨m, hm⟩ := hG ⟨z, hzG⟩
  have hzMax : ∀ y ∈ P, m y ≤ m z := by
    have hz := hzG
    rw [hm] at hz
    exact hz.2
  refine ⟨m, ?_⟩
  ext x
  constructor
  · rintro ⟨hxG, hxB⟩
    rw [hm] at hxG
    exact ⟨hxB, fun y hy => hxG.2 y (hBP hy)⟩
  · rintro ⟨hxB, hxMax⟩
    refine ⟨?_, hxB⟩
    rw [hm]
    refine ⟨hBP hxB, fun y hy => ?_⟩
    exact (hzMax y hy).trans (hxMax z hzB)

/-- For a face containing the apex, membership of an internal crossing point is equivalent to
membership of the other endpoint. This supplies order reflection for vertex-figure sections. -/
theorem lineMap_mem_face_iff {d : ℕ} {P G : Set (Fin d → ℝ)}
    (hP : Convex ℝ P) (hG : IsExposed ℝ P G)
    {v w : Fin d → ℝ} (hvG : v ∈ G) (hwP : w ∈ P)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    AffineMap.lineMap v w t ∈ G ↔ w ∈ G := by
  constructor
  · intro hx
    exact hG.isExtreme.right_mem_of_mem_openSegment (hG.subset hvG) hwP hx
      (lineMap_mem_openSegment ℝ v w ht)
  · intro hwG
    exact (hG.convex hP).lineMap_mem hvG hwG ⟨ht.1.le, ht.2.le⟩

end Grunbaum2003


-- Exact checked component: AntistarProperties

set_option autoImplicit false

namespace Grunbaum2003

/-- The antistar is compact; every point is below the vertex-figure plane and terminal on its
ray from the apex. Private development for the actual radial homeomorphism. -/
theorem antistar_compact_below_and_terminal (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (v : Fin d → ℝ) (hvP : v ∈ P)
    (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
    (hBelow : ∀ w : Fin d → ℝ, IsExposed ℝ P {w} → w ≠ v → l w < α) :
    let A := ⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}
    IsCompact A ∧ A ⊆ P ∧ ∀ x ∈ A,
      l x < α ∧ ∀ t : ℝ, 0 < t → x + t • (x - v) ∉ P := by
  classical
  let V := {x : Fin d → ℝ | IsExposed ℝ P {x}}
  obtain ⟨hVfin, hFaces⟩ := polytope_face_eq_convexHull_exposed_vertices d P hP
  have hFaceFin : {F : Set (Fin d → ℝ) | IsExposed ℝ P F}.Finite := by
    apply ((hVfin.powerset).image (convexHull ℝ)).subset
    intro F hF
    refine ⟨F ∩ V, Set.inter_subset_right, ?_⟩
    exact (hFaces ⟨F, hF⟩).symm
  have hAFin : {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}.Finite :=
    hFaceFin.subset (fun F hF => hF.1)
  have hPcomp : IsCompact P := by
    obtain ⟨W, hWfin, _, hPW⟩ := hP.1
    rw [hPW]
    exact hWfin.isCompact_convexHull ℝ
  refine ⟨hAFin.isCompact_sUnion (fun F hF => hF.1.isCompact hPcomp), ?_, ?_⟩
  · rintro x ⟨F, ⟨hF, _⟩, hx⟩
    exact hF.subset hx
  · rintro x ⟨F, ⟨hF, hvF⟩, hxF⟩
    constructor
    · have hHullF : F = convexHull ℝ (F ∩ V) := hFaces ⟨F, hF⟩
      have hLow : F ⊆ {y | l y < α} := by
        rw [hHullF]
        apply convexHull_min ?_ (convex_halfSpace_lt l.toLinearMap.isLinear α)
        rintro w ⟨hwF, hwV⟩
        exact hBelow w hwV (fun hwv => hvF (hwv ▸ hwF))
      exact hLow hxF
    · intro t ht hPoint
      let y := x + t • (x - v)
      let s : ℝ := 1 / (1 + t)
      have hDen : 0 < 1 + t := by linarith
      have hs₀ : 0 < s := div_pos zero_lt_one hDen
      have hs₁ : s < 1 := (div_lt_one hDen).mpr (by linarith)
      have hLine : AffineMap.lineMap v y s = x := by
        rw [AffineMap.lineMap_apply_module']
        ext i
        change s * (y i - v i) + v i = x i
        dsimp [y, s]
        field_simp [hDen.ne']
        <;> ring
      have hxInt : x ∈ openSegment ℝ v y := by
        rw [← hLine]
        exact lineMap_mem_openSegment ℝ v y ⟨hs₀, hs₁⟩
      exact hvF (hF.isExtreme.left_mem_of_mem_openSegment hvP hPoint hxF hxInt)

end Grunbaum2003


-- Exact checked component: ExposedTrans

set_option autoImplicit false

namespace Grunbaum2003

/-- Exposed-face transitivity for finite polytopes. This is false for arbitrary convex sets.
Private development for the finite facial descent in the antistar construction. -/
theorem isExposed_trans_polytope (d : ℕ) (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (F G : Set (Fin d → ℝ)) (hF : IsExposed ℝ P F) (hG : IsExposed ℝ F G) :
    IsExposed ℝ P G := by
  classical
  by_cases hEmpty : G = ∅
  · rw [hEmpty]
    exact isExposed_empty
  obtain ⟨z, hzG⟩ := Set.nonempty_iff_ne_empty.mpr hEmpty
  have hzF : z ∈ F := hG.subset hzG
  have hzP : z ∈ P := hF.subset hzF
  obtain ⟨l, hFl⟩ := hF ⟨z, hzF⟩
  obtain ⟨m, hGm⟩ := hG ⟨z, hzG⟩
  have hlMax : ∀ x ∈ P, l x ≤ l z := by
    have hz := hzF
    rw [hFl] at hz
    exact hz.2
  have hmMax : ∀ x ∈ F, m x ≤ m z := by
    have hz := hzG
    rw [hGm] at hz
    exact hz.2
  have hFlevel (x : Fin d → ℝ) (hxP : x ∈ P) : x ∈ F ↔ l x = l z := by
    constructor
    · intro hxF
      rw [hFl] at hxF
      exact le_antisymm (hlMax x hxP) (hxF.2 z hzP)
    · intro hxEq
      rw [hFl]
      exact ⟨hxP, fun y hy => by rw [hxEq]; exact hlMax y hy⟩
  have hGlevel (x : Fin d → ℝ) (hxF : x ∈ F) : x ∈ G ↔ m x = m z := by
    constructor
    · intro hxG
      rw [hGm] at hxG
      exact le_antisymm (hmMax x hxF) (hxG.2 z hzF)
    · intro hxEq
      rw [hGm]
      exact ⟨hxF, fun y hy => by rw [hxEq]; exact hmMax y hy⟩
  let V := {x : Fin d → ℝ | IsExposed ℝ P {x}}
  obtain ⟨hVfin, hFaces⟩ := polytope_face_eq_convexHull_exposed_vertices d P hP
  have hVP : V ⊆ P := fun x hx => (mem_exposedPoints_iff_exposed_singleton.mpr hx).1
  have hPgen : P = convexHull ℝ V := by
    have h := hFaces ⟨P, IsExposed.refl P⟩
    change P = convexHull ℝ (P ∩ V) at h
    rwa [Set.inter_eq_right.mpr hVP] at h
  have hPconv : Convex ℝ P := hPgen ▸ convex_convexHull ℝ V
  let r : (Fin d → ℝ) → ℝ := fun w => (m w - m z) / (l z - l w)
  obtain ⟨M, hM⟩ := ((hVfin.image r).insert 0).bddAbove
  let C : ℝ := M + 1
  let n : StrongDual ℝ (Fin d → ℝ) := C • l + m
  have hStrict (w : Fin d → ℝ) (hwV : w ∈ V) (hwF : w ∉ F) : n w < n z := by
    have hwP : w ∈ P := hVP hwV
    have hlw : l w < l z := lt_of_le_of_ne (hlMax w hwP) (fun h => hwF ((hFlevel w hwP).mpr h))
    have hDen : 0 < l z - l w := sub_pos.mpr hlw
    have hRatio : r w < C := lt_of_le_of_lt (hM (Set.mem_insert_of_mem 0 ⟨w, hwV, rfl⟩)) (by dsimp [C]; linarith)
    have hNum : m w - m z < C * (l z - l w) := (div_lt_iff₀ hDen).mp hRatio
    change C * l w + m w < C * l z + m z
    nlinarith [hNum]
  have hGen (w : Fin d → ℝ) (hwV : w ∈ V) : n w ≤ n z := by
    by_cases hwF : w ∈ F
    · change C * l w + m w ≤ C * l z + m z
      rw [(hFlevel w (hVP hwV)).mp hwF]
      exact add_le_add le_rfl (hmMax w hwF)
    · exact (hStrict w hwV hwF).le
  have hnMax : ∀ x ∈ P, n x ≤ n z := by
    rw [hPgen]
    apply convexHull_min hGen
    intro x hx y hy a b ha hb hab
    change n (a • x + b • y) ≤ n z
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    calc
      a * n x + b * n y ≤ a * n z + b * n z :=
        add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
      _ = n z := by rw [← add_mul, hab, one_mul]
  let K := {x ∈ P | n x = n z}
  have hK : IsExposed ℝ P K := by
    intro _
    refine ⟨n, ?_⟩
    ext x
    constructor
    · rintro ⟨hxP, hxEq⟩
      exact ⟨hxP, fun y hy => (hnMax y hy).trans_eq hxEq.symm⟩
    · rintro ⟨hxP, hxMax⟩
      exact ⟨hxP, le_antisymm (hnMax x hxP) (hxMax z hzP)⟩
  have hKsubG : K ⊆ G := by
    have hHullK := hFaces ⟨K, hK⟩
    change K = convexHull ℝ (K ∩ V) at hHullK
    rw [hHullK]
    apply convexHull_min ?_ (hG.convex (hF.convex hPconv))
    rintro w ⟨hwK, hwV⟩
    have hwF : w ∈ F := by
      by_contra hnF
      exact (hStrict w hwV hnF).ne hwK.2
    apply (hGlevel w hwF).mpr
    have hEq : C * l w + m w = C * l z + m z := hwK.2
    rw [(hFlevel w hwK.1).mp hwF] at hEq
    linarith
  have hGsubK : G ⊆ K := by
    intro x hxG
    have hxF : x ∈ F := hG.subset hxG
    have hxP : x ∈ P := hF.subset hxF
    refine ⟨hxP, ?_⟩
    change C * l x + m x = C * l z + m z
    rw [(hFlevel x hxP).mp hxF, (hGlevel x hxF).mp hxG]
  have hKG : K = G := Set.Subset.antisymm hKsubG hGsubK
  rwa [hKG] at hK

end Grunbaum2003


-- Exact checked component: RelativeSupportingFace

set_option autoImplicit false

namespace Grunbaum2003

/-- A relative-boundary point of a convex set has a proper exposed supporting face, in the
original ambient space. Private ingredient for finite facial descent at a ray endpoint. -/
theorem exists_proper_exposed_of_not_intrinsicInterior (d : ℕ)
    (K : Set (Fin d → ℝ)) (hK : Convex ℝ K) (z : Fin d → ℝ)
    (hz : z ∈ K) (hzint : z ∉ intrinsicInterior ℝ K) :
    ∃ F : Set (Fin d → ℝ), IsExposed ℝ K F ∧ z ∈ F ∧ F ≠ K := by
  classical
  let A := affineSpan ℝ K
  have hzA : z ∈ A := subset_affineSpan ℝ _ hz
  haveI : Nonempty A := ⟨⟨z, hzA⟩⟩
  haveI : Nonempty K := ⟨⟨z, hz⟩⟩
  let zA : A := ⟨z, hzA⟩
  let e : A.direction ≃ᵃⁱ[ℝ] A := AffineIsometryEquiv.vaddConst ℝ zA
  let KA : Set A := ((↑) : A → (Fin d → ℝ)) ⁻¹' K
  let B : Set A.direction := e ⁻¹' KA
  have hB : Convex ℝ B := hK.affine_preimage
    (A.subtype.comp e.toAffineEquiv.toAffineMap)
  have hBSpan : affineSpan ℝ B = ⊤ := by
    change affineSpan ℝ (e.toAffineEquiv ⁻¹' KA) = ⊤
    rw [← AffineSubspace.comap_span e.toAffineEquiv KA]
    have hKA : affineSpan ℝ KA = ⊤ := affineSpan_coe_preimage_eq_top K
    rw [hKA, AffineSubspace.comap_top]
  have hBint : (interior B).Nonempty := hB.interior_nonempty_iff_affineSpan_eq_top.mpr hBSpan
  have h0not : (0 : A.direction) ∉ interior B := by
    intro h0
    change (0 : A.direction) ∈ interior (e.toHomeomorph ⁻¹' KA) at h0
    rw [← e.toHomeomorph.preimage_interior] at h0
    have hzIntA : zA ∈ interior KA := by simpa [e] using h0
    exact hzint ⟨zA, hzIntA, rfl⟩
  obtain ⟨f, hfne, hfmax⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point hB h0not hBint
  have hfMax : ∀ x ∈ B, f x ≤ 0 := by simpa only [map_zero] using hfmax
  obtain ⟨g, hg, _⟩ := exists_extension_norm_eq A.direction f
  have hgMax (x : Fin d → ℝ) (hx : x ∈ K) : g x ≤ g z := by
    have hxA : x ∈ A := subset_affineSpan ℝ _ hx
    let u : A.direction := ⟨x - z, A.vsub_mem_direction hxA hzA⟩
    have hu : u ∈ B := by
      change (x - z) + z ∈ K
      simpa only [sub_add_cancel] using hx
    have h := hfMax u hu
    rw [← hg u] at h
    change g (x - z) ≤ 0 at h
    rw [map_sub] at h
    linarith
  let F := {x ∈ K | g x = g z}
  have hF : IsExposed ℝ K F := by
    intro _
    refine ⟨g, ?_⟩
    ext x
    constructor
    · rintro ⟨hx, hxEq⟩
      exact ⟨hx, fun y hy => (hgMax y hy).trans_eq hxEq.symm⟩
    · rintro ⟨hx, hxMax⟩
      exact ⟨hx, le_antisymm (hgMax x hx) (hxMax z hz)⟩
  refine ⟨F, hF, ⟨hz, rfl⟩, ?_⟩
  intro hFK
  obtain ⟨y, hy⟩ := hBint
  have hyK : ((e y : A) : Fin d → ℝ) ∈ K := by
    have hyB : y ∈ B := interior_subset hy
    exact hyB
  have hyF : ((e y : A) : Fin d → ℝ) ∈ F := by rw [hFK]; exact hyK
  have hyEq : g (((e y : A) : Fin d → ℝ)) = g z := hyF.2
  have hgy : g (((e y : A) : Fin d → ℝ)) = f y + g z := by
    change g ((y : Fin d → ℝ) + z) = f y + g z
    rw [map_add, hg y]
  have hfy : f y = 0 := by linarith
  have hSub : f '' interior B ⊆ Set.Iic (f y) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [hfy]
    exact hfMax w (interior_subset hw)
  have hopen : IsOpen (f '' interior B) :=
    f.isOpenMap_of_ne_zero hfne (interior B) isOpen_interior
  have hyImpossible : f y ∈ interior (Set.Iic (f y)) :=
    interior_maximal hSub hopen (Set.mem_image_of_mem f hy)
  simpa only [interior_Iic, Set.mem_Iio, lt_self_iff_false] using hyImpossible

end Grunbaum2003


-- Exact checked component: IntrinsicRay

set_option autoImplicit false
open scoped Topology

namespace Grunbaum2003

/-- Intrinsic interior allows positive continuation away from any other point of the set. -/
theorem exists_forward_ray_of_intrinsicInterior (d : ℕ) (K : Set (Fin d → ℝ))
    (z v : Fin d → ℝ) (hz : z ∈ intrinsicInterior ℝ K) (hv : v ∈ K) :
    ∃ t : ℝ, 0 < t ∧ z + t • (z - v) ∈ K := by
  classical
  let A := affineSpan ℝ K
  have hzA : z ∈ A := subset_affineSpan ℝ _ (intrinsicInterior_subset hz)
  have hvA : v ∈ A := subset_affineSpan ℝ _ hv
  haveI : Nonempty A := ⟨⟨z, hzA⟩⟩
  let zA : A := ⟨z, hzA⟩
  let vA : A := ⟨v, hvA⟩
  let D : A.direction := zA -ᵥ vA
  let KA : Set A := ((↑) : A → (Fin d → ℝ)) ⁻¹' K
  have hzInt : zA ∈ interior KA := by
    obtain ⟨x, hx, hxeq⟩ := hz
    have hxz : x = zA := Subtype.ext hxeq
    exact hxz ▸ hx
  have hsmul : Continuous (fun t : ℝ => t • D) := continuous_id.smul continuous_const
  have hzconst : Continuous (fun _ : ℝ => zA) := continuous_const
  have hc : Continuous (fun t : ℝ => t • D +ᵥ zA) := hsmul.vadd hzconst
  have hNear : {t : ℝ | t • D +ᵥ zA ∈ KA} ∈ 𝓝 0 := by
    have hKA : KA ∈ 𝓝 zA := mem_interior_iff_mem_nhds.mp hzInt
    have hKA' : KA ∈ 𝓝 ((0 : ℝ) • D +ᵥ zA) := by
      simpa only [zero_smul, zero_vadd] using hKA
    exact hc.continuousAt.preimage_mem_nhds hKA'
  obtain ⟨ε, hε, hBall⟩ := Metric.mem_nhds_iff.mp hNear
  have htBall : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith : 0 < ε / 2)]
    linarith
  have hPoint := hBall htBall
  change (ε / 2) • (z - v) + z ∈ K at hPoint
  exact ⟨ε / 2, by linarith, by simpa only [add_comm] using hPoint⟩

end Grunbaum2003


-- Exact checked component: BlockingFace

set_option autoImplicit false

namespace Grunbaum2003

/-- A terminal point of a ray in a finite polytope lies in an exposed face excluding its
starting point. Private antistar construction; finite facial descent, not a frontier shortcut. -/
theorem exists_blocking_exposed_face (d : ℕ) (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (v z : Fin d → ℝ) (hv : v ∈ P) (hz : z ∈ P)
    (hStop : ∀ t : ℝ, 0 < t → z + t • (z - v) ∉ P) :
    ∃ F : Set (Fin d → ℝ), IsExposed ℝ P F ∧ z ∈ F ∧ v ∉ F := by
  classical
  let V := {x : Fin d → ℝ | IsExposed ℝ P {x}}
  obtain ⟨hVfin, hFaces⟩ := polytope_face_eq_convexHull_exposed_vertices d P hP
  let p : ℕ → Prop := fun n => ∃ F : Set (Fin d → ℝ),
    IsExposed ℝ P F ∧ z ∈ F ∧ (F ∩ V).ncard = n
  have hExists : ∃ n, p n := ⟨(P ∩ V).ncard, P, IsExposed.refl P, hz, rfl⟩
  obtain ⟨K, hK, hzK, hCount⟩ := Nat.find_spec hExists
  refine ⟨K, hK, hzK, ?_⟩
  intro hvK
  have hPconv : Convex ℝ P := by
    obtain ⟨W, _, _, hPW⟩ := hP.1
    rw [hPW]
    exact convex_convexHull ℝ W
  have hKconv : Convex ℝ K := hK.convex hPconv
  have hzNotInt : z ∉ intrinsicInterior ℝ K := by
    intro hzInt
    obtain ⟨t, ht, hPoint⟩ := exists_forward_ray_of_intrinsicInterior d K z v hzInt hvK
    exact hStop t ht (hK.subset hPoint)
  obtain ⟨H, hH, hzH, hHK⟩ :=
    exists_proper_exposed_of_not_intrinsicInterior d K hKconv z hzK hzNotInt
  have hHP : IsExposed ℝ P H := isExposed_trans_polytope d P hP K H hK hH
  have hHullK : K = convexHull ℝ (K ∩ V) := hFaces ⟨K, hK⟩
  have hHullH : H = convexHull ℝ (H ∩ V) := hFaces ⟨H, hHP⟩
  have hSub : H ∩ V ⊆ K ∩ V := fun x hx => ⟨hH.subset hx.1, hx.2⟩
  have hNe : H ∩ V ≠ K ∩ V := by
    intro hEq
    apply hHK
    calc
      H = convexHull ℝ (H ∩ V) := hHullH
      _ = convexHull ℝ (K ∩ V) := by rw [hEq]
      _ = K := hHullK.symm
  have hKfin : (K ∩ V).Finite := hVfin.subset Set.inter_subset_right
  have hLess : (H ∩ V).ncard < (K ∩ V).ncard :=
    Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨hSub, hNe⟩) hKfin
  have hMin : Nat.find hExists ≤ (H ∩ V).ncard :=
    Nat.find_min' hExists ⟨H, hHP, hzH, rfl⟩
  rw [← hCount] at hMin
  exact (not_le_of_gt hLess) hMin

end Grunbaum2003


-- Exact checked component: RayEndpoint

set_option autoImplicit false

namespace Grunbaum2003

/-- A ray through a vertex-figure point has a last point in the polytope, and that point lies
in the actual antistar by the finite blocking-face theorem. -/
theorem exists_ray_endpoint_in_antistar (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (v : Fin d → ℝ) (hvP : v ∈ P)
    (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ) (hα : α < l v)
    (q : Fin d → ℝ) (hqP : q ∈ P) (hqLevel : l q = α) :
    ∃ r : ℝ, 1 ≤ r ∧
      let z := AffineMap.lineMap v q r
      z ∈ P ∧ z ∈ ⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F} ∧
        ∀ s : ℝ, 0 < s → z + s • (z - v) ∉ P := by
  classical
  have hPcomp : IsCompact P := by
    obtain ⟨W, hWfin, _, hPW⟩ := hP.1
    rw [hPW]
    exact hWfin.isCompact_convexHull ℝ
  obtain ⟨m, hm⟩ := (hPcomp.image l.continuous).exists_isLeast
    ⟨l v, ⟨v, hvP, rfl⟩⟩
  have hLow (x : Fin d → ℝ) (hx : x ∈ P) : m ≤ l x := hm.2 ⟨x, hx, rfl⟩
  let line : ℝ → (Fin d → ℝ) := AffineMap.lineMap v q
  let T : Set ℝ := {t | line t ∈ P ∧ 1 ≤ t}
  have hCont : Continuous line := by
    have hs : Continuous (fun t : ℝ => t • (q - v)) := continuous_id.smul continuous_const
    have hv : Continuous (fun _ : ℝ => v) := continuous_const
    exact hs.add hv
  have hClosed : IsClosed T := (hPcomp.isClosed.preimage hCont).inter isClosed_Ici
  have hD : 0 < l v - α := sub_pos.mpr hα
  have hBound : T ⊆ Set.Icc 1 ((l v - m) / (l v - α)) := by
    intro t ht
    refine ⟨ht.2, (le_div_iff₀ hD).mpr ?_⟩
    have h := hLow (line t) ht.1
    change m ≤ l (AffineMap.lineMap v q t) at h
    rw [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul, hqLevel] at h
    nlinarith [h]
  have hTcomp : IsCompact T := isCompact_Icc.of_isClosed_subset hClosed hBound
  have hTne : T.Nonempty := by
    refine ⟨1, ?_, le_rfl⟩
    simpa only [line, AffineMap.lineMap_apply_one] using hqP
  obtain ⟨r, hr⟩ := hTcomp.exists_isGreatest hTne
  let z := line r
  have hrPos : 0 < r := lt_of_lt_of_le zero_lt_one hr.1.2
  have hzP : z ∈ P := hr.1.1
  have hStop : ∀ s : ℝ, 0 < s → z + s • (z - v) ∉ P := by
    intro s hs hPoint
    have hSr : 0 < s * r := mul_pos hs hrPos
    have hEq : line ((1 + s) * r) = z + s • (z - v) := by
      change AffineMap.lineMap v q ((1 + s) * r) = _
      rw [← AffineMap.lineMap_lineMap_right v q r (1 + s)]
      change AffineMap.lineMap v z (1 + s) = _
      rw [AffineMap.lineMap_apply_module']
      ext i
      change (1 + s) * (z i - v i) + v i = z i + s * (z i - v i)
      ring
    have hInT : (1 + s) * r ∈ T := by
      refine ⟨?_, ?_⟩
      · rw [hEq]
        exact hPoint
      · nlinarith [hr.1.2, hSr]
    have hLe := hr.2 hInT
    nlinarith [hSr]
  obtain ⟨F, hF, hzF, hvF⟩ := exists_blocking_exposed_face d P hP v z hvP hzP hStop
  refine ⟨r, hr.1.2, hzP, ?_, hStop⟩
  exact ⟨F, ⟨hF, hvF⟩, hzF⟩

end Grunbaum2003


-- Exact checked component: AntistarHomeomorph

set_option autoImplicit false

namespace Grunbaum2003

/-- The actual antistar is homeomorphic to the vertex figure by the explicit radial map.
Finite facial descent supplies surjectivity at ray endpoints. Private induction development. -/
theorem antistar_radial_homeomorph (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (v : Fin d → ℝ) (hvP : v ∈ P)
    (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ) (hα : α < l v)
    (hBelow : ∀ w : Fin d → ℝ, IsExposed ℝ P {w} → w ≠ v → l w < α) :
    ∃ ψ : (⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}) ≃ₜ ↥(P ∩ l ⁻¹' {α}),
      ∀ x, (ψ x).val = AffineMap.lineMap v x.val ((l v - α) / (l v - l x.val)) := by
  classical
  let A := ⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}
  let Q := P ∩ l ⁻¹' {α}
  let D := l v - α
  let p : (Fin d → ℝ) → (Fin d → ℝ) :=
    fun x => AffineMap.lineMap v x (D / (l v - l x))
  obtain ⟨hAc, hAP, hAT⟩ := antistar_compact_below_and_terminal d P hP v hvP l α hBelow
  have hPconv : Convex ℝ P := by
    obtain ⟨W, _, _, hPW⟩ := hP.1
    rw [hPW]
    exact convex_convexHull ℝ W
  have hD : 0 < D := sub_pos.mpr hα
  have hDen (x : A) : 0 < l v - l x.val := sub_pos.mpr (((hAT x.val x.property).1).trans hα)
  have hpxQ (x : A) : p x.val ∈ Q := by
    have ht₀ : 0 < D / (l v - l x.val) := div_pos hD (hDen x)
    have ht₁ : D / (l v - l x.val) < 1 :=
      (div_lt_one (hDen x)).mpr (by dsimp [D]; linarith [(hAT x.val x.property).1])
    refine ⟨hPconv.lineMap_mem hvP (hAP x.property) ⟨ht₀.le, ht₁.le⟩, ?_⟩
    have hMul : (D / (l v - l x.val)) * (l v - l x.val) = D :=
      div_mul_cancel₀ _ (hDen x).ne'
    change l (AffineMap.lineMap v x.val (D / (l v - l x.val))) = α
    rw [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul]
    dsimp [D] at hMul
    nlinarith [hMul]
  let f : A → Q := fun x => ⟨p x.val, hpxQ x⟩
  have hCross (x y : A) (hxy : p x.val = p y.val) :
      AffineMap.lineMap v y.val ((l v - l x.val) / (l v - l y.val)) = x.val := by
    let tx := D / (l v - l x.val)
    let ty := D / (l v - l y.val)
    have htx : tx ≠ 0 := (div_pos hD (hDen x)).ne'
    have hEq : tx • (x.val - v) = ty • (y.val - v) := by
      have hEq' : tx • (x.val - v) + v = ty • (y.val - v) + v := hxy
      exact add_right_cancel hEq'
    have hCancel : x.val - v = (tx⁻¹ * ty) • (y.val - v) := by
      have h := congrArg (fun u : Fin d → ℝ => tx⁻¹ • u) hEq
      simpa only [smul_smul, inv_mul_cancel₀ htx, one_smul] using h
    have hRatio : tx⁻¹ * ty = (l v - l x.val) / (l v - l y.val) := by
      dsimp [tx, ty]
      field_simp [hD.ne', (hDen x).ne', (hDen y).ne']
    rw [AffineMap.lineMap_apply_module', ← hRatio, ← hCancel, sub_add_cancel]
  have hNoLess (x y : A) (hxy : p x.val = p y.val)
      (hlt : l v - l x.val < l v - l y.val) : False := by
    obtain ⟨F, ⟨hF, hvF⟩, hxF⟩ := x.property
    have ht₀ : 0 < (l v - l x.val) / (l v - l y.val) := div_pos (hDen x) (hDen y)
    have ht₁ : (l v - l x.val) / (l v - l y.val) < 1 := (div_lt_one (hDen y)).mpr hlt
    have hxInt : x.val ∈ openSegment ℝ v y.val := by
      rw [← hCross x y hxy]
      exact lineMap_mem_openSegment ℝ v y.val ⟨ht₀, ht₁⟩
    exact hvF (hF.isExtreme.left_mem_of_mem_openSegment hvP (hAP y.property) hxF hxInt)
  have hInj : Function.Injective f := by
    intro x y hxy
    have hxy' : p x.val = p y.val := congrArg Subtype.val hxy
    have hEq : l v - l x.val = l v - l y.val :=
      le_antisymm (le_of_not_gt (fun h => hNoLess y x hxy'.symm h))
        (le_of_not_gt (fun h => hNoLess x y hxy' h))
    have h := hCross x y hxy'
    rw [hEq, div_self (hDen y).ne', AffineMap.lineMap_apply_one] at h
    exact Subtype.ext h.symm
  have hSurj : Function.Surjective f := by
    intro q
    obtain ⟨r, hr, hzP, hzA, _⟩ :=
      exists_ray_endpoint_in_antistar d P hP v hvP l α hα q.val q.property.1 q.property.2
    let z := AffineMap.lineMap v q.val r
    have hrPos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hLz : l z = r * (α - l v) + l v := by
      dsimp [z]
      rw [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul, q.property.2]
    have hDenZ : l v - l z = r * D := by rw [hLz]; dsimp [D]; ring
    have hCoef : (D / (l v - l z)) * r = 1 := by
      rw [hDenZ]
      field_simp [hrPos.ne', hD.ne']
    refine ⟨⟨z, hzA⟩, ?_⟩
    apply Subtype.ext
    change p z = q.val
    change AffineMap.lineMap v (AffineMap.lineMap v q.val r) (D / (l v - l z)) = q.val
    rw [AffineMap.lineMap_lineMap_right, hCoef, AffineMap.lineMap_apply_one]
  have hdc : Continuous (fun x : A => l v - l x.val) :=
    continuous_const.sub (l.continuous.comp continuous_subtype_val)
  have hfc : Continuous (fun x : A => D / (l v - l x.val)) :=
    continuous_const.div hdc (fun x => (hDen x).ne')
  have hvc : Continuous (fun x : A => x.val - v) := continuous_subtype_val.sub continuous_const
  have hsc : Continuous (fun x : A => (D / (l v - l x.val)) • (x.val - v)) := hfc.smul hvc
  have hpc : Continuous (fun x : A => p x.val) := by
    apply (hsc.add (continuous_const : Continuous (fun _ : A => v))).congr
    intro x
    simp only [Pi.add_apply, p, AffineMap.lineMap_apply_module']
  have hFcont : Continuous f := hpc.subtype_mk hpxQ
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hAc
  let e : A ≃ Q := Equiv.ofBijective f ⟨hInj, hSurj⟩
  have heCont : Continuous e := hFcont
  let ψ : A ≃ₜ Q := heCont.homeoOfEquivCompactToT2
  refine ⟨ψ, ?_⟩
  intro x
  rfl

end Grunbaum2003


-- Exact checked component: ConeQuotient

set_option autoImplicit false

namespace Grunbaum2003

/-- The finite vertex cutoff forces the cutting functional to have its unique maximum at v. -/
theorem cut_functional_strict_max (d : ℕ) (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (v : Fin d → ℝ) (hvP : v ∈ P)
    (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ) (hα : α < l v)
    (hBelow : ∀ w : Fin d → ℝ, IsExposed ℝ P {w} → w ≠ v → l w < α) :
    ∀ x ∈ P, x ≠ v → l x < l v := by
  classical
  let V := {x : Fin d → ℝ | IsExposed ℝ P {x}}
  obtain ⟨_, hFaces⟩ := polytope_face_eq_convexHull_exposed_vertices d P hP
  have hVP : V ⊆ P := fun x hx => (mem_exposedPoints_iff_exposed_singleton.mpr hx).1
  have hPgen : P = convexHull ℝ V := by
    have h := hFaces ⟨P, IsExposed.refl P⟩
    change P = convexHull ℝ (P ∩ V) at h
    rwa [Set.inter_eq_right.mpr hVP] at h
  have hMax : ∀ x ∈ P, l x ≤ l v := by
    rw [hPgen]
    apply convexHull_min ?_ (convex_halfSpace_le l.toLinearMap.isLinear (l v))
    intro w hw
    change l w ≤ l v
    by_cases hwv : w = v
    · simpa only [hwv] using le_refl (l v)
    · exact ((hBelow w hw hwv).trans hα).le
  let K := {x ∈ P | l x = l v}
  have hK : IsExposed ℝ P K := by
    intro _
    refine ⟨l, ?_⟩
    ext x
    constructor
    · rintro ⟨hxP, hxEq⟩
      exact ⟨hxP, fun y hy => (hMax y hy).trans_eq hxEq.symm⟩
    · rintro ⟨hxP, hxMax⟩
      exact ⟨hxP, le_antisymm (hMax x hxP) (hxMax v hvP)⟩
  have hKsub : K ⊆ {v} := by
    have hHull : K = convexHull ℝ (K ∩ V) := hFaces ⟨K, hK⟩
    rw [hHull]
    apply convexHull_min ?_ (convex_singleton v)
    rintro w ⟨hwK, hwV⟩
    by_cases hwv : w = v
    · exact hwv
    · exact (((hBelow w hwV hwv).trans hα).ne hwK.2).elim
  intro x hxP hxv
  apply lt_of_le_of_ne (hMax x hxP)
  intro hEq
  exact hxv (hKsub ⟨hxP, hEq⟩)

/-- The actual antistar times the unit interval continuously surjects onto a positive-dimensional
polytope. It is a quotient map, with precisely the apex fiber collapsed. No abstract cone type is
introduced. Private construction for the global boundary-refinement map. -/
theorem antistar_cone_quotient (d : ℕ) (hd : 0 < d)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (v : Fin d → ℝ) (hvP : v ∈ P)
    (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ) (hα : α < l v)
    (hBelow : ∀ w : Fin d → ℝ, IsExposed ℝ P {w} → w ≠ v → l w < α) :
    let A := ⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}
    let I := Set.Icc (0 : ℝ) 1
    ∃ f : (A × I) → P,
      (∀ a, (f a).val = AffineMap.lineMap v a.1.val a.2.val) ∧
      Continuous f ∧ Function.Surjective f ∧ Topology.IsQuotientMap f ∧
      ∀ a b, f a = f b ↔
        (a.2.val = 0 ∧ b.2.val = 0) ∨ (a.1 = b.1 ∧ a.2 = b.2) := by
  classical
  let A := ⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}
  let I := Set.Icc (0 : ℝ) 1
  let D := l v - α
  let p : (Fin d → ℝ) → (Fin d → ℝ) :=
    fun x => AffineMap.lineMap v x (D / (l v - l x))
  obtain ⟨hAc, hAP, hAT⟩ := antistar_compact_below_and_terminal d P hP v hvP l α hBelow
  obtain ⟨ψ, hψ⟩ := antistar_radial_homeomorph d P hP v hvP l α hα hBelow
  have hPconv : Convex ℝ P := by
    obtain ⟨W, _, _, hPW⟩ := hP.1
    rw [hPW]
    exact convex_convexHull ℝ W
  have hD : 0 < D := sub_pos.mpr hα
  have hDen (y : A) : 0 < l v - l y.val := sub_pos.mpr (((hAT y.val y.property).1).trans hα)
  have hStrict := cut_functional_strict_max d P hP v hvP l α hα hBelow
  have hOther : ∃ x ∈ P, x ≠ v := by
    by_contra h
    have hAll (x : Fin d → ℝ) (hx : x ∈ P) : x = v := by
      by_contra hxv
      exact h ⟨x, hx, hxv⟩
    have hSub : P.Subsingleton := fun x hx y hy => (hAll x hx).trans (hAll y hy).symm
    haveI : Subsingleton (Fin d → ℝ) :=
      AffineSubspace.subsingleton_of_subsingleton_span_eq_top hSub hP.2
    have hz : (0 : Fin d → ℝ) = 1 := Subsingleton.elim _ _
    exact zero_ne_one (congrFun hz ⟨0, hd⟩)
  obtain ⟨x₀, hx₀, hx₀v⟩ := hOther
  obtain ⟨r₀, _, _, hy₀, _⟩ := exists_ray_endpoint_in_antistar d P hP v hvP l (l x₀)
    (hStrict x₀ hx₀ hx₀v) x₀ hx₀ rfl
  let y₀ : A := ⟨AffineMap.lineMap v x₀ r₀, hy₀⟩
  let f : (A × I) → P := fun a =>
    ⟨AffineMap.lineMap v a.1.val a.2.val,
      hPconv.lineMap_mem hvP (hAP a.1.property) a.2.property⟩
  have hSurj : Function.Surjective f := by
    intro x
    by_cases hxv : x.val = v
    · refine ⟨(y₀, ⟨0, le_refl 0, zero_le_one⟩), ?_⟩
      apply Subtype.ext
      change AffineMap.lineMap v y₀.val 0 = x.val
      rw [AffineMap.lineMap_apply_zero]
      exact hxv.symm
    · obtain ⟨r, hr, _, hyA, _⟩ := exists_ray_endpoint_in_antistar d P hP v hvP l (l x.val)
        (hStrict x.val x.property hxv) x.val x.property rfl
      have hrPos : 0 < r := lt_of_lt_of_le zero_lt_one hr
      let y : A := ⟨AffineMap.lineMap v x.val r, hyA⟩
      let t : I := ⟨1 / r, (div_pos zero_lt_one hrPos).le, (div_le_one hrPos).mpr hr⟩
      refine ⟨(y, t), ?_⟩
      apply Subtype.ext
      change AffineMap.lineMap v (AffineMap.lineMap v x.val r) (1 / r) = x.val
      rw [AffineMap.lineMap_lineMap_right, div_mul_cancel₀ 1 hrPos.ne', AffineMap.lineMap_apply_one]
  have hEval (a : A × I) : l v - l (f a).val = a.2.val * (l v - l a.1.val) := by
    change l v - l (AffineMap.lineMap v a.1.val a.2.val) = _
    rw [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul]
    ring
  have hProj (a : A × I) (ht : 0 < a.2.val) : p (f a).val = p a.1.val := by
    have hCoef : (D / (l v - l (f a).val)) * a.2.val = D / (l v - l a.1.val) := by
      rw [hEval a]
      field_simp [ht.ne', (hDen a.1).ne']
    change AffineMap.lineMap v (AffineMap.lineMap v a.1.val a.2.val)
      (D / (l v - l (f a).val)) = AffineMap.lineMap v a.1.val (D / (l v - l a.1.val))
    rw [AffineMap.lineMap_lineMap_right, hCoef]
  have hFiber (a b : A × I) : f a = f b ↔
      (a.2.val = 0 ∧ b.2.val = 0) ∨ (a.1 = b.1 ∧ a.2 = b.2) := by
    constructor
    · intro hEq
      have hEqDen : a.2.val * (l v - l a.1.val) = b.2.val * (l v - l b.1.val) := by
        rw [← hEval a, ← hEval b]
        exact congrArg (fun x : Fin d → ℝ => l v - l x) (congrArg Subtype.val hEq)
      by_cases hta : a.2.val = 0
      · have htb : b.2.val = 0 := by
          have hProd : b.2.val * (l v - l b.1.val) = 0 := by simpa only [hta, zero_mul] using hEqDen.symm
          exact (mul_eq_zero.mp hProd).resolve_right (hDen b.1).ne'
        exact Or.inl ⟨hta, htb⟩
      · have htb : b.2.val ≠ 0 := by
          intro htb
          have hProd : a.2.val * (l v - l a.1.val) = 0 := by simpa only [htb, zero_mul] using hEqDen
          exact hta ((mul_eq_zero.mp hProd).resolve_right (hDen a.1).ne')
        have htaPos : 0 < a.2.val := lt_of_le_of_ne a.2.property.1 (Ne.symm hta)
        have htbPos : 0 < b.2.val := lt_of_le_of_ne b.2.property.1 (Ne.symm htb)
        have hpEq : p a.1.val = p b.1.val := by
          calc
            p a.1.val = p (f a).val := (hProj a htaPos).symm
            _ = p (f b).val := congrArg p (congrArg Subtype.val hEq)
            _ = p b.1.val := hProj b htbPos
        have hψEq : ψ a.1 = ψ b.1 := by
          apply Subtype.ext
          rw [hψ a.1, hψ b.1]
          exact hpEq
        have hyEq : a.1 = b.1 := ψ.injective hψEq
        have hEqDen' : a.2.val * (l v - l b.1.val) = b.2.val * (l v - l b.1.val) := by
          simpa only [hyEq] using hEqDen
        have htEq : a.2.val = b.2.val := mul_right_cancel₀ (hDen b.1).ne' hEqDen'
        exact Or.inr ⟨hyEq, Subtype.ext htEq⟩
    · rintro (⟨hta, htb⟩ | ⟨hy, ht⟩)
      · apply Subtype.ext
        change AffineMap.lineMap v a.1.val a.2.val = AffineMap.lineMap v b.1.val b.2.val
        simp only [hta, htb, AffineMap.lineMap_apply_zero]
      · exact congrArg f (Prod.ext hy ht)
  have htc : Continuous (fun a : A × I => a.2.val) := continuous_subtype_val.comp continuous_snd
  have hyc : Continuous (fun a : A × I => a.1.val) := continuous_subtype_val.comp continuous_fst
  have hdc : Continuous (fun a : A × I => a.1.val - v) := hyc.sub continuous_const
  have hsc : Continuous (fun a : A × I => a.2.val • (a.1.val - v)) := htc.smul hdc
  have hfc : Continuous (fun a : A × I => (f a).val) := by
    apply (hsc.add (continuous_const : Continuous (fun _ : A × I => v))).congr
    intro a
    simp only [Pi.add_apply, f, AffineMap.lineMap_apply_module']
  have hCont : Continuous f := hfc.subtype_mk _
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hAc
  haveI : CompactSpace I := isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))
  exact ⟨f, (fun _ => rfl), hCont, hSurj,
    Topology.IsQuotientMap.of_surjective_continuous hSurj hCont, hFiber⟩

end Grunbaum2003


-- Exact checked component: SectionOrder

set_option autoImplicit false

namespace Grunbaum2003

/-- Cutting-plane sections reflect inclusion among polytope faces containing the chosen vertex.
This is the injectivity/order-reflection half of the vertex-figure face correspondence. -/
theorem vertex_figure_section_order_reflects (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (v : Fin d → ℝ) (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
    (hα : α < l v)
    (hBelow : ∀ w : Fin d → ℝ, IsExposed ℝ P {w} → w ≠ v → l w < α)
    (G₁ G₂ : Set (Fin d → ℝ)) (hG₁ : IsExposed ℝ P G₁) (hG₂ : IsExposed ℝ P G₂)
    (hv₁ : v ∈ G₁) (hv₂ : v ∈ G₂)
    (hSections : G₁ ∩ l ⁻¹' {α} ⊆ G₂ ∩ l ⁻¹' {α}) : G₁ ⊆ G₂ := by
  classical
  have hPconv : Convex ℝ P := by
    obtain ⟨V, _, _, hPV⟩ := hP.1
    rw [hPV]
    exact convex_convexHull ℝ V
  have hHull := (polytope_face_eq_convexHull_exposed_vertices d P hP).2 ⟨G₁, hG₁⟩
  calc
    G₁ = convexHull ℝ (G₁ ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}) := hHull
    _ ⊆ G₂ := by
      apply convexHull_min ?_ (hG₂.convex hPconv)
      rintro w ⟨hw₁, hwVertex⟩
      by_cases hwv : w = v
      · simpa only [hwv] using hv₂
      · have hLow : l w < α := hBelow w hwVertex hwv
        have hDen : 0 < l v - l w := sub_pos.mpr (hLow.trans hα)
        let t : ℝ := (l v - α) / (l v - l w)
        have ht₀ : 0 < t := div_pos (sub_pos.mpr hα) hDen
        have ht₁ : t < 1 := (div_lt_one hDen).mpr (by linarith)
        have hwP : w ∈ P := hG₁.subset hw₁
        have hq₁ : AffineMap.lineMap v w t ∈ G₁ :=
          (lineMap_mem_face_iff hPconv hG₁ hv₁ hwP ⟨ht₀, ht₁⟩).mpr hw₁
        have htMul : t * (l v - l w) = l v - α := div_mul_cancel₀ _ hDen.ne'
        have hqLevel : l (AffineMap.lineMap v w t) = α := by
          rw [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul]
          nlinarith [htMul]
        have hq₂ : AffineMap.lineMap v w t ∈ G₂ := (hSections ⟨hq₁, hqLevel⟩).1
        exact (lineMap_mem_face_iff hPconv hG₂ hv₂ hwP ⟨ht₀, ht₁⟩).mp hq₂

end Grunbaum2003


-- Exact checked component: VertexFigureFaceIso

set_option autoImplicit false

namespace Grunbaum2003

/-- The actual vertex-figure face lattice is the interval of faces containing the apex.
The order isomorphism is explicitly cutting-plane intersection. Private induction development. -/
theorem vertex_figure_face_orderIso (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (v : Fin d → ℝ) (hv : IsExposed ℝ P {v})
    (W : Set (Fin d → ℝ)) (hW : W.Nonempty)
    (hPgen : P = convexHull ℝ (insert v W))
    (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α) :
    ∃ Φ : {G : PolytopeFace P // v ∈ G.val} ≃o PolytopeFace (P ∩ l ⁻¹' {α}),
      ∀ G, (Φ G).val = G.val.val ∩ (P ∩ l ⁻¹' {α}) := by
  classical
  let Q := P ∩ l ⁻¹' {α}
  let A := {G : PolytopeFace P // v ∈ G.val}
  let f : A → PolytopeFace Q := fun G =>
    ⟨G.val.val ∩ Q, isExposed_inter_restrict G.val.property Set.inter_subset_left⟩
  have hBelowVertices (w : Fin d → ℝ) (hw : IsExposed ℝ P {w}) (hwv : w ≠ v) : l w < α := by
    have hwExt : w ∈ P.extremePoints ℝ :=
      exposedPoints_subset_extremePoints (mem_exposedPoints_iff_exposed_singleton.mpr hw)
    rw [hPgen] at hwExt
    have hwGen := extremePoints_convexHull_subset hwExt
    exact hBelow w ((Set.mem_insert_iff.mp hwGen).resolve_left hwv)
  have hMap (G₁ G₂ : A) : f G₁ ≤ f G₂ ↔ G₁ ≤ G₂ := by
    change G₁.val.val ∩ Q ⊆ G₂.val.val ∩ Q ↔ G₁.val.val ⊆ G₂.val.val
    constructor
    · intro h
      apply vertex_figure_section_order_reflects d P hP v l α hα hBelowVertices
        G₁.val.val G₂.val.val G₁.val.property G₂.val.property G₁.property G₂.property
      rintro x ⟨hxG, hxLevel⟩
      have hxQ : x ∈ Q := ⟨G₁.val.property.subset hxG, hxLevel⟩
      have hx := h ⟨hxG, hxQ⟩
      exact ⟨hx.1, hx.2.2⟩
    · intro h x hx
      exact ⟨h hx.1, hx.2⟩
  let emb : A ↪o PolytopeFace Q := OrderEmbedding.ofMapLEIff f hMap
  have hSurj : Function.Surjective f := by
    intro R
    by_cases hEmpty : R.val = ∅
    · let G : A := ⟨⟨{v}, hv⟩, Set.mem_singleton v⟩
      refine ⟨G, ?_⟩
      apply Subtype.ext
      change {v} ∩ Q = R.val
      rw [hEmpty]
      apply Set.Subset.antisymm ?_ (Set.empty_subset _)
      rintro x ⟨hxv, hxQ⟩
      have hx : x = v := hxv
      subst x
      exact (hα.ne hxQ.2.symm).elim
    · have hRne : R.val.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
      obtain ⟨z, hz⟩ := hRne
      obtain ⟨m, hm⟩ := R.property ⟨z, hz⟩
      have hzQ : z ∈ Q := R.property.subset hz
      have hzMax : ∀ y ∈ Q, m y ≤ m z := by
        have hz' := hz
        rw [hm] at hz'
        exact hz'.2
      let β := m z
      have hRmax : R.val = {x ∈ Q | m x = β} := by
        ext x
        constructor
        · intro hx
          have hx' := hx
          rw [hm] at hx'
          exact ⟨hx'.1, le_antisymm (hzMax x hx'.1) (hx'.2 z hzQ)⟩
        · rintro ⟨hxQ, hxEq⟩
          rw [hm]
          refine ⟨hxQ, fun y hy => ?_⟩
          calc m y ≤ m z := hzMax y hy
               _ = m x := hxEq.symm
      have hMax : ∀ x ∈ convexHull ℝ (insert v W) ∩ l ⁻¹' {α}, m x ≤ β := by
        rw [← hPgen]
        exact hzMax
      obtain ⟨hN, hExpose, hVertex, hSlice⟩ :=
        exposed_vertex_figure_face_lift d v W hW l m α β hα hBelow hMax
      let n := m + ((β - m v) / (l v - α)) • l
      let G : Set (Fin d → ℝ) := {x ∈ P | n x = n v}
      have hG : IsExposed ℝ P G := by simpa only [← hPgen] using hExpose
      have hvG : v ∈ G := by simpa only [← hPgen] using hVertex
      have hSlice' : {x ∈ Q | m x = β} = G ∩ l ⁻¹' {α} := by
        simpa only [← hPgen] using hSlice
      refine ⟨⟨⟨G, hG⟩, hvG⟩, ?_⟩
      apply Subtype.ext
      change G ∩ Q = R.val
      rw [hRmax, hSlice']
      ext x
      constructor
      · rintro ⟨hxG, hxQ⟩
        exact ⟨hxG, hxQ.2⟩
      · rintro ⟨hxG, hxLevel⟩
        exact ⟨hxG, ⟨hG.subset hxG, hxLevel⟩⟩
  let Φ : A ≃o PolytopeFace Q := OrderIso.ofSurjective emb hSurj
  refine ⟨Φ, ?_⟩
  intro G
  rfl

end Grunbaum2003


-- Exact checked component: ConeBoundary

set_option autoImplicit false

namespace Grunbaum2003

/-- Actual boundary carriers in cone coordinates. The same radial antistar map identifies the
non-apex/non-antistar boundary with the proper exposed-face carrier of the vertex figure. -/
theorem antistar_cone_boundary_criterion (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (v : Fin d → ℝ) (hv : IsExposed ℝ P {v})
    (W : Set (Fin d → ℝ)) (hW : W.Nonempty)
    (hPgen : P = convexHull ℝ (insert v W))
    (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α)
    (ψ : (⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}) ≃ₜ ↥(P ∩ l ⁻¹' {α}))
    (hψ : ∀ y, (ψ y).val = AffineMap.lineMap v y.val ((l v - α) / (l v - l y.val))) :
    v ∈ ⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ F ≠ P} ∧
      (⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}) ⊆
        ⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ F ≠ P} ∧
      ∀ (y : ⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}) (t : ℝ), 0 < t → t < 1 →
        (AffineMap.lineMap v y.val t ∈ ⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ F ≠ P} ↔
          (ψ y).val ∈ ⋃₀ {R : Set (Fin d → ℝ) | IsExposed ℝ (P ∩ l ⁻¹' {α}) R ∧ R ≠ P ∩ l ⁻¹' {α}}) := by
  classical
  let A := ⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}
  let Q := P ∩ l ⁻¹' {α}
  have hvP : v ∈ P := hv.subset (Set.mem_singleton v)
  have hPconv : Convex ℝ P := by rw [hPgen]; exact convex_convexHull ℝ _
  have hBelowVertices (w : Fin d → ℝ) (hw : IsExposed ℝ P {w}) (hwv : w ≠ v) : l w < α := by
    have hwExt : w ∈ P.extremePoints ℝ :=
      exposedPoints_subset_extremePoints (mem_exposedPoints_iff_exposed_singleton.mpr hw)
    rw [hPgen] at hwExt
    exact hBelow w ((Set.mem_insert_iff.mp (extremePoints_convexHull_subset hwExt)).resolve_left hwv)
  obtain ⟨Φ, hΦ⟩ := vertex_figure_face_orderIso d P hP v hv W hW hPgen l α hα hBelow
  obtain ⟨_, hAP, hAT⟩ := antistar_compact_below_and_terminal d P hP v hvP l α hBelowVertices
  let J := {G : PolytopeFace P // v ∈ G.val}
  let topFace : J := ⟨⟨P, IsExposed.refl P⟩, hvP⟩
  have hTop : (Φ topFace).val = Q := by
    rw [hΦ topFace]
    change P ∩ Q = Q
    exact Set.inter_eq_right.mpr Set.inter_subset_left
  have hProper (G : J) : G.val.val ≠ P ↔ (Φ G).val ≠ Q := by
    constructor
    · intro hGP hRQ
      apply hGP
      have hEq : Φ G = Φ topFace := Subtype.ext (hRQ.trans hTop.symm)
      exact congrArg (fun H : J => H.val.val) (Φ.injective hEq)
    · intro hRQ hGP
      apply hRQ
      have h := hΦ G
      rw [hGP] at h
      exact h.trans (Set.inter_eq_right.mpr Set.inter_subset_left)
  have hSliceMember (y : A) (G : J) : (ψ y).val ∈ (Φ G).val ↔ y.val ∈ G.val.val := by
    have hDen : 0 < l v - l y.val := sub_pos.mpr (((hAT y.val y.property).1).trans hα)
    have ht₀ : 0 < (l v - α) / (l v - l y.val) := div_pos (sub_pos.mpr hα) hDen
    have ht₁ : (l v - α) / (l v - l y.val) < 1 :=
      (div_lt_one hDen).mpr (by linarith [(hAT y.val y.property).1])
    have hGmem : (ψ y).val ∈ G.val.val ↔ y.val ∈ G.val.val := by
      rw [hψ y]
      exact lineMap_mem_face_iff hPconv G.val.property G.property (hAP y.property) ⟨ht₀, ht₁⟩
    rw [hΦ G]
    exact ⟨fun h => hGmem.mp h.1, fun h => ⟨hGmem.mpr h, (ψ y).property⟩⟩
  obtain ⟨w₀, hw₀⟩ := hW
  have hw₀P : w₀ ∈ P := by rw [hPgen]; exact subset_convexHull ℝ _ (Set.mem_insert_of_mem v hw₀)
  have hw₀v : w₀ ≠ v := by
    intro h
    have hLow := hBelow w₀ hw₀
    rw [h] at hLow
    exact lt_asymm hα hLow
  have hvNeP : ({v} : Set (Fin d → ℝ)) ≠ P := by
    intro h
    have hwv : w₀ ∈ ({v} : Set (Fin d → ℝ)) := by rw [h]; exact hw₀P
    exact hw₀v hwv
  refine ⟨⟨{v}, ⟨hv, hvNeP⟩, Set.mem_singleton v⟩, ?_, ?_⟩
  · rintro x ⟨F, ⟨hF, hvF⟩, hxF⟩
    refine ⟨F, ⟨hF, ?_⟩, hxF⟩
    intro hFP
    apply hvF
    rw [hFP]
    exact hvP
  · intro y t ht₀ ht₁
    constructor
    · rintro ⟨F, ⟨hF, hFP⟩, hxF⟩
      have hxOpen := lineMap_mem_openSegment ℝ v y.val ⟨ht₀, ht₁⟩
      have hvF : v ∈ F := hF.isExtreme.left_mem_of_mem_openSegment hvP (hAP y.property) hxF hxOpen
      have hyF : y.val ∈ F := hF.isExtreme.right_mem_of_mem_openSegment hvP (hAP y.property) hxF hxOpen
      let G : J := ⟨⟨F, hF⟩, hvF⟩
      exact ⟨(Φ G).val, ⟨(Φ G).property, (hProper G).mp hFP⟩, (hSliceMember y G).mpr hyF⟩
    · rintro ⟨R, ⟨hR, hRQ⟩, hyR⟩
      let G : J := Φ.symm ⟨R, hR⟩
      have hRval : (Φ G).val = R := congrArg Subtype.val (Φ.apply_symm_apply ⟨R, hR⟩)
      have hGP : G.val.val ≠ P := (hProper G).mpr (by rw [hRval]; exact hRQ)
      have hyG : y.val ∈ G.val.val := (hSliceMember y G).mp (by rw [hRval]; exact hyR)
      have hxG : AffineMap.lineMap v y.val t ∈ G.val.val :=
        (G.val.property.convex hPconv).lineMap_mem G.property hyG ⟨ht₀.le, ht₁.le⟩
      exact ⟨G.val.val, ⟨G.val.property, hGP⟩, hxG⟩

end Grunbaum2003


-- Exact checked component: QuotientHomeomorph

set_option autoImplicit false

noncomputable section

namespace Grunbaum2003
open Topology

/-- Matching the fibers of two quotient presentations gives a homeomorphism
of their codomains, with the prescribed value on every representative. -/
theorem quotient_homeomorph_of_fiber_equiv
    {X Y P Q : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace P] [TopologicalSpace Q]
    (f : X → P) (g : Y → Q)
    (hf : IsQuotientMap f) (hg : IsQuotientMap g)
    (e : X ≃ₜ Y)
    (he : ∀ x y, f x = f y ↔ g (e x) = g (e y)) :
    ∃ H : P ≃ₜ Q, ∀ x, H (f x) = g (e x) := by
  let k : Quotient (Setoid.ker f) ≃ₜ Quotient (Setoid.ker g) :=
    Homeomorph.Quotient.congr e he
  let F : C(X, P) := ⟨f, hf.continuous⟩
  let G : C(Y, Q) := ⟨g, hg.continuous⟩
  let p : Quotient (Setoid.ker f) ≃ₜ P := IsQuotientMap.homeomorph (f := F) hf
  let q : Quotient (Setoid.ker g) ≃ₜ Q := IsQuotientMap.homeomorph (f := G) hg
  let H : P ≃ₜ Q := p.symm.trans (k.trans q)
  refine ⟨H, ?_⟩
  intro x
  change q (k (p.symm (f x))) = g (e x)
  rw [show f x = p (Quotient.mk (Setoid.ker f) x) from rfl,
    p.symm_apply_apply]
  rfl

end Grunbaum2003

end

-- Exact checked component: ConeHomeomorph

set_option autoImplicit false

namespace Grunbaum2003
open Topology

/-- Homeomorphisms of the bases extend over quotient presentations which
collapse exactly one end of a product. -/
theorem cone_homeomorph_of_base_homeomorph
    {A B I P Q : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace I] [TopologicalSpace P] [TopologicalSpace Q]
    (i₀ : I) (f : A × I → P) (g : B × I → Q)
    (hf : IsQuotientMap f) (hg : IsQuotientMap g)
    (hF : ∀ a b, f a = f b ↔
      (a.2 = i₀ ∧ b.2 = i₀) ∨ (a.1 = b.1 ∧ a.2 = b.2))
    (hG : ∀ a b, g a = g b ↔
      (a.2 = i₀ ∧ b.2 = i₀) ∨ (a.1 = b.1 ∧ a.2 = b.2))
    (e : A ≃ₜ B) :
    ∃ H : P ≃ₜ Q, ∀ a t, H (f (a, t)) = g (e a, t) := by
  let E : (A × I) ≃ₜ (B × I) := e.prodCongr (.refl I)
  have hFibers : ∀ a b, f a = f b ↔ g (E a) = g (E b) := by
    intro a b
    rw [hF, hG]
    change ((a.2 = i₀ ∧ b.2 = i₀) ∨ (a.1 = b.1 ∧ a.2 = b.2)) ↔
      ((a.2 = i₀ ∧ b.2 = i₀) ∨ (e a.1 = e b.1 ∧ a.2 = b.2))
    rw [e.injective.eq_iff]
  obtain ⟨H, hH⟩ := quotient_homeomorph_of_fiber_equiv f g hf hg E hFibers
  exact ⟨H, fun a t => hH (a, t)⟩

end Grunbaum2003


-- Exact checked component: GlobalConeBoundary

set_option autoImplicit false

namespace Grunbaum2003

private def ambientBoundaryHomeomorph {E : Type*} [TopologicalSpace E]
    (P B : Set E) (hBP : B ⊆ P) : B ≃ₜ {x : P | x.val ∈ B} where
  toFun := fun b => ⟨⟨b.val, hBP b.property⟩, b.property⟩
  invFun := fun b => ⟨b.val.val, b.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := by
    have h : Continuous (fun b : B => (⟨b.val, hBP b.property⟩ : P)) := continuous_subtype_val.subtype_mk _
    exact h.subtype_mk _
  continuous_invFun := by
    have h : Continuous (fun b : {x : P | x.val ∈ B} => b.val.val) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact h.subtype_mk _

/-- A boundary-preserving homeomorphism of actual vertex figures induces a full-body homeomorphism
and a homeomorphism of the actual exposed-face boundary carriers, by the checked cone quotient
presentations. Both radial antistar maps are the same recorded maps used in the cell data. -/
theorem global_cone_boundary_homeomorph
    (d d' : ℕ) (hd : 0 < d) (hd' : 0 < d')
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (P' : Set (Fin d' → ℝ)) (hP' : IsDPolytope P')
    (v : Fin d → ℝ) (hv : IsExposed ℝ P {v})
    (v' : Fin d' → ℝ) (hv' : IsExposed ℝ P' {v'})
    (W : Set (Fin d → ℝ)) (hW : W.Nonempty) (hPgen : P = convexHull ℝ (insert v W))
    (W' : Set (Fin d' → ℝ)) (hW' : W'.Nonempty) (hPgen' : P' = convexHull ℝ (insert v' W'))
    (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ) (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α)
    (l' : StrongDual ℝ (Fin d' → ℝ)) (α' : ℝ) (hα' : α' < l' v') (hBelow' : ∀ w ∈ W', l' w < α')
    (ψ : (⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}) ≃ₜ ↥(P ∩ l ⁻¹' {α}))
    (hψ : ∀ y, (ψ y).val = AffineMap.lineMap v y.val ((l v - α) / (l v - l y.val)))
    (ψ' : (⋃₀ {F : Set (Fin d' → ℝ) | IsExposed ℝ P' F ∧ v' ∉ F}) ≃ₜ ↥(P' ∩ l' ⁻¹' {α'}))
    (hψ' : ∀ y, (ψ' y).val = AffineMap.lineMap v' y.val ((l' v' - α') / (l' v' - l' y.val)))
    (h : ↥(P ∩ l ⁻¹' {α}) ≃ₜ ↥(P' ∩ l' ⁻¹' {α'}))
    (hCarrier : ∀ q, (h q).val ∈ ⋃₀ {R : Set (Fin d' → ℝ) |
        IsExposed ℝ (P' ∩ l' ⁻¹' {α'}) R ∧ R ≠ P' ∩ l' ⁻¹' {α'}} ↔
      q.val ∈ ⋃₀ {R : Set (Fin d → ℝ) | IsExposed ℝ (P ∩ l ⁻¹' {α}) R ∧ R ≠ P ∩ l ⁻¹' {α}}) :
    ∃ H : P ≃ₜ P',
      (∀ y (t : Set.Icc (0 : ℝ) 1) (x : P), x.val = AffineMap.lineMap v y.val t.val →
        (H x).val = AffineMap.lineMap v' (ψ'.symm (h (ψ y))).val t.val) ∧
      (∀ x : P, (H x).val ∈ ⋃₀ {F : Set (Fin d' → ℝ) | IsExposed ℝ P' F ∧ F ≠ P'} ↔
        x.val ∈ ⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ F ≠ P}) ∧
      ∃ Ψ : (⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ F ≠ P}) ≃ₜ
          (⋃₀ {F : Set (Fin d' → ℝ) | IsExposed ℝ P' F ∧ F ≠ P'}),
        ∀ b (x : P), x.val = b.val → (Ψ b).val = (H x).val := by
  classical
  let A := ⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}
  let A' := ⋃₀ {F : Set (Fin d' → ℝ) | IsExposed ℝ P' F ∧ v' ∉ F}
  let B := ⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ F ≠ P}
  let B' := ⋃₀ {F : Set (Fin d' → ℝ) | IsExposed ℝ P' F ∧ F ≠ P'}
  let I := Set.Icc (0 : ℝ) 1
  have hvP : v ∈ P := hv.subset (Set.mem_singleton v)
  have hvP' : v' ∈ P' := hv'.subset (Set.mem_singleton v')
  have hBelowV (w : Fin d → ℝ) (hw : IsExposed ℝ P {w}) (hwv : w ≠ v) : l w < α := by
    have hwExt := exposedPoints_subset_extremePoints (mem_exposedPoints_iff_exposed_singleton.mpr hw)
    rw [hPgen] at hwExt
    exact hBelow w ((Set.mem_insert_iff.mp (extremePoints_convexHull_subset hwExt)).resolve_left hwv)
  have hBelowV' (w : Fin d' → ℝ) (hw : IsExposed ℝ P' {w}) (hwv : w ≠ v') : l' w < α' := by
    have hwExt := exposedPoints_subset_extremePoints (mem_exposedPoints_iff_exposed_singleton.mpr hw)
    rw [hPgen'] at hwExt
    exact hBelow' w ((Set.mem_insert_iff.mp (extremePoints_convexHull_subset hwExt)).resolve_left hwv)
  obtain ⟨f, hFform, _, hFsurj, hFquot, hFfib⟩ := antistar_cone_quotient d hd P hP v hvP l α hα hBelowV
  obtain ⟨g, hGform, _, _, hGquot, hGfib⟩ := antistar_cone_quotient d' hd' P' hP' v' hvP' l' α' hα' hBelowV'
  let i₀ : I := ⟨0, le_refl 0, zero_le_one⟩
  have hFfib' (a b : A × I) : f a = f b ↔
      (a.2 = i₀ ∧ b.2 = i₀) ∨ (a.1 = b.1 ∧ a.2 = b.2) := by
    simpa only [Subtype.ext_iff, i₀] using hFfib a b
  have hGfib' (a b : A' × I) : g a = g b ↔
      (a.2 = i₀ ∧ b.2 = i₀) ∨ (a.1 = b.1 ∧ a.2 = b.2) := by
    simpa only [Subtype.ext_iff, i₀] using hGfib a b
  let eA : A ≃ₜ A' := ψ.trans (h.trans ψ'.symm)
  obtain ⟨H, hH⟩ := cone_homeomorph_of_base_homeomorph i₀ f g hFquot hGquot hFfib' hGfib' eA
  have hRep (a : A × I) : H (f a) = g (eA a.1, a.2) := hH a.1 a.2
  obtain ⟨hApex, hAIncl, hCrit⟩ := antistar_cone_boundary_criterion d P hP v hv W hW hPgen l α hα hBelow ψ hψ
  obtain ⟨hApex', hAIncl', hCrit'⟩ := antistar_cone_boundary_criterion d' P' hP' v' hv' W' hW' hPgen' l' α' hα' hBelow' ψ' hψ'
  have hBoundary (x : P) : (H x).val ∈ B' ↔ x.val ∈ B := by
    obtain ⟨a, rfl⟩ := hFsurj x
    by_cases ht₀ : a.2.val = 0
    · have hSrc : (f a).val ∈ B := by rw [hFform a, ht₀, AffineMap.lineMap_apply_zero]; exact hApex
      have hTgt : (H (f a)).val ∈ B' := by
        rw [hRep a, hGform (eA a.1, a.2), ht₀, AffineMap.lineMap_apply_zero]
        exact hApex'
      exact ⟨fun _ => hSrc, fun _ => hTgt⟩
    · by_cases ht₁ : a.2.val = 1
      · have hSrc : (f a).val ∈ B := by rw [hFform a, ht₁, AffineMap.lineMap_apply_one]; exact hAIncl a.1.property
        have hTgt : (H (f a)).val ∈ B' := by
          rw [hRep a, hGform (eA a.1, a.2), ht₁, AffineMap.lineMap_apply_one]
          exact hAIncl' (eA a.1).property
        exact ⟨fun _ => hSrc, fun _ => hTgt⟩
      · have htPos : 0 < a.2.val := lt_of_le_of_ne a.2.property.1 (Ne.symm ht₀)
        have htLt : a.2.val < 1 := lt_of_le_of_ne a.2.property.2 ht₁
        rw [hRep a, hGform (eA a.1, a.2), hFform a]
        rw [hCrit' (eA a.1) a.2.val htPos htLt, hCrit a.1 a.2.val htPos htLt]
        have hCompatible : ψ' (eA a.1) = h (ψ a.1) := by simp only [eA, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
        rw [hCompatible]
        exact hCarrier (ψ a.1)
  have hBP : B ⊆ P := by rintro x ⟨F, ⟨hF, _⟩, hx⟩; exact hF.subset hx
  have hBP' : B' ⊆ P' := by rintro x ⟨F, ⟨hF, _⟩, hx⟩; exact hF.subset hx
  let HB : {x : P | x.val ∈ B} ≃ₜ {x : P' | x.val ∈ B'} := H.subtype (fun x => (hBoundary x).symm)
  let Ψ : B ≃ₜ B' := (ambientBoundaryHomeomorph P B hBP).trans
    (HB.trans (ambientBoundaryHomeomorph P' B' hBP').symm)
  refine ⟨H, ?_, hBoundary, Ψ, ?_⟩
  · intro y t x hx
    have hxF : x = f (y, t) := Subtype.ext (hx.trans (hFform (y, t)).symm)
    rw [hxF, hH y t, hGform (eA y, t)]
    rfl
  · intro b x hx
    have hx' : x = (⟨b.val, hBP b.property⟩ : P) := Subtype.ext hx
    rw [hx']
    rfl

end Grunbaum2003


-- Exact checked component: LiftedSubcomplex

set_option autoImplicit false

namespace Grunbaum2003

/-- A union of proper vertex-figure faces lifts, together with the apex, to an
actual finite source boundary subcomplex. Its membership formula uses the same
radial antistar map as the global cone construction. -/
theorem lifted_vertexFigure_subcomplex (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (v : Fin d → ℝ) (hv : IsExposed ℝ P {v})
    (W : Set (Fin d → ℝ)) (hW : W.Nonempty)
    (hPgen : P = convexHull ℝ (insert v W))
    (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α)
    (ψ : (⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}) ≃ₜ ↥(P ∩ l ⁻¹' {α}))
    (hψ : ∀ y, (ψ y).val = AffineMap.lineMap v y.val ((l v - α) / (l v - l y.val)))
    (C : Set (Set (Fin d → ℝ)))
    (hC : C ⊆ {R | IsExposed ℝ (P ∩ l ⁻¹' {α}) R ∧ R ≠ P ∩ l ⁻¹' {α}}) :
    ∃ D : Set (Set (Fin d → ℝ)), D.Finite ∧
      D ⊆ {F | IsExposed ℝ P F ∧ F ≠ P} ∧
      (∀ F ∈ D, ∀ H, IsExposed ℝ F H → H ∈ D) ∧
      ∀ (y : ⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}) (t : ℝ),
        0 ≤ t → t ≤ 1 →
        (AffineMap.lineMap v y.val t ∈ ⋃₀ D ↔ t = 0 ∨ (ψ y).val ∈ ⋃₀ C) := by
  classical
  let A := ⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}
  let Q := P ∩ l ⁻¹' {α}
  have hvP : v ∈ P := hv.subset (Set.mem_singleton v)
  have hPconv : Convex ℝ P := by rw [hPgen]; exact convex_convexHull ℝ _
  have hBelowVertices (w : Fin d → ℝ) (hw : IsExposed ℝ P {w}) (hwv : w ≠ v) : l w < α := by
    have hwExt : w ∈ P.extremePoints ℝ :=
      exposedPoints_subset_extremePoints (mem_exposedPoints_iff_exposed_singleton.mpr hw)
    rw [hPgen] at hwExt
    exact hBelow w ((Set.mem_insert_iff.mp (extremePoints_convexHull_subset hwExt)).resolve_left hwv)
  obtain ⟨Φ, hΦ⟩ := vertex_figure_face_orderIso d P hP v hv W hW hPgen l α hα hBelow
  obtain ⟨_, hAP, hAT⟩ := antistar_compact_below_and_terminal d P hP v hvP l α hBelowVertices
  let J := {G : PolytopeFace P // v ∈ G.val}
  let topFace : J := ⟨⟨P, IsExposed.refl P⟩, hvP⟩
  have hTop : (Φ topFace).val = Q := by
    rw [hΦ topFace]
    exact Set.inter_eq_right.mpr Set.inter_subset_left
  have hProper (G : J) (hGC : (Φ G).val ∈ C) : G.val.val ≠ P := by
    intro hGP
    apply (hC hGC).2
    have h := hΦ G
    rw [hGP] at h
    exact h.trans (Set.inter_eq_right.mpr Set.inter_subset_left)
  have hSliceMember (y : A) (G : J) : (ψ y).val ∈ (Φ G).val ↔ y.val ∈ G.val.val := by
    have hDen : 0 < l v - l y.val := sub_pos.mpr (((hAT y.val y.property).1).trans hα)
    have ht₀ : 0 < (l v - α) / (l v - l y.val) := div_pos (sub_pos.mpr hα) hDen
    have ht₁ : (l v - α) / (l v - l y.val) < 1 :=
      (div_lt_one hDen).mpr (by linarith [(hAT y.val y.property).1])
    have hGmem : (ψ y).val ∈ G.val.val ↔ y.val ∈ G.val.val := by
      rw [hψ y]
      exact lineMap_mem_face_iff hPconv G.val.property G.property (hAP y.property) ⟨ht₀, ht₁⟩
    rw [hΦ G]
    exact ⟨fun h => hGmem.mp h.1, fun h => ⟨hGmem.mpr h, (ψ y).property⟩⟩
  obtain ⟨w₀, hw₀⟩ := hW
  have hw₀P : w₀ ∈ P := by rw [hPgen]; exact subset_convexHull ℝ _ (Set.mem_insert_of_mem v hw₀)
  have hw₀v : w₀ ≠ v := by
    intro h
    have hLow := hBelow w₀ hw₀
    rw [h] at hLow
    exact lt_asymm hα hLow
  let V := {x : Fin d → ℝ | IsExposed ℝ P {x}}
  obtain ⟨hVfin, hFaces⟩ := polytope_face_eq_convexHull_exposed_vertices d P hP
  have hFaceFin : {F : Set (Fin d → ℝ) | IsExposed ℝ P F}.Finite := by
    apply ((hVfin.powerset).image (convexHull ℝ)).subset
    intro F hF
    exact ⟨F ∩ V, Set.inter_subset_right, (hFaces ⟨F, hF⟩).symm⟩
  let D : Set (Set (Fin d → ℝ)) :=
    {F | IsExposed ℝ P F ∧ (F ⊆ {v} ∨ ∃ G : J, (Φ G).val ∈ C ∧ F ⊆ G.val.val)}
  refine ⟨D, hFaceFin.subset (fun F hF => hF.1), ?_, ?_, ?_⟩
  · intro F hF
    refine ⟨hF.1, ?_⟩
    intro hFP
    rcases hF.2 with hFv | ⟨G, hGC, hFG⟩
    · apply hw₀v
      apply hFv
      rw [hFP]
      exact hw₀P
    · apply hProper G hGC
      apply Set.Subset.antisymm G.val.property.subset
      intro x hxP
      exact hFG (hFP.symm ▸ hxP)
  · intro F hF H hH
    refine ⟨isExposed_trans_polytope d P hP F H hF.1 hH, ?_⟩
    rcases hF.2 with hFv | ⟨G, hGC, hFG⟩
    · exact Or.inl (hH.subset.trans hFv)
    · exact Or.inr ⟨G, hGC, hH.subset.trans hFG⟩
  · intro y t ht₀ ht₁
    have hvy : v ≠ y.val := by
      intro h
      have hLow := (hAT y.val y.property).1
      rw [← h] at hLow
      exact lt_asymm hα hLow
    constructor
    · rintro ⟨F, hF, hxF⟩
      rcases hF.2 with hFv | ⟨G, hGC, hFG⟩
      · have hxv : AffineMap.lineMap v y.val t = v := hFv hxF
        exact Or.inl ((AffineMap.lineMap_eq_left_iff.mp hxv).resolve_left hvy)
      · by_cases ht : t = 0
        · exact Or.inl ht
        · have hyG : y.val ∈ G.val.val := by
            by_cases htOne : t = 1
            · have hxG := hFG hxF
              simpa only [htOne, AffineMap.lineMap_apply_one] using hxG
            · exact (lineMap_mem_face_iff hPconv G.val.property G.property (hAP y.property)
                ⟨lt_of_le_of_ne ht₀ (Ne.symm ht), lt_of_le_of_ne ht₁ htOne⟩).mp (hFG hxF)
          exact Or.inr ⟨(Φ G).val, hGC, (hSliceMember y G).mpr hyG⟩
    · rintro (ht | ⟨R, hRC, hyR⟩)
      · refine ⟨{v}, ⟨hv, Or.inl Set.Subset.rfl⟩, ?_⟩
        rw [ht, AffineMap.lineMap_apply_zero]
        exact Set.mem_singleton v
      · let G : J := Φ.symm ⟨R, (hC hRC).1⟩
        have hRval : (Φ G).val = R := congrArg Subtype.val (Φ.apply_symm_apply ⟨R, (hC hRC).1⟩)
        have hGC : (Φ G).val ∈ C := by rw [hRval]; exact hRC
        have hyG : y.val ∈ G.val.val := (hSliceMember y G).mp (by rw [hRval]; exact hyR)
        refine ⟨G.val.val, ⟨G.val.property, Or.inr ⟨G, hGC, Set.Subset.rfl⟩⟩, ?_⟩
        exact (G.val.property.convex hPconv).lineMap_mem G.property hyG ⟨ht₀, ht₁⟩

end Grunbaum2003


-- Exact checked component: AntistarFacePreimages

set_option autoImplicit false

namespace Grunbaum2003

/-- The antistar radial homeomorphism has actual finite source-subcomplex preimages for every
vertex-figure face. This is the face-respecting opposite-facet branch of the induction. -/
theorem antistar_radial_refinement_data (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (v : Fin d → ℝ) (hv : IsExposed ℝ P {v})
    (W : Set (Fin d → ℝ)) (hW : W.Nonempty)
    (hPgen : P = convexHull ℝ (insert v W))
    (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α) :
    ∃ ψ : (⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}) ≃ₜ ↥(P ∩ l ⁻¹' {α}),
      (∀ x, (ψ x).val = AffineMap.lineMap v x.val ((l v - α) / (l v - l x.val))) ∧
      ∀ R : PolytopeFace (P ∩ l ⁻¹' {α}),
        ∃ C : Set (Set (Fin d → ℝ)), C.Finite ∧
          C ⊆ {F | IsExposed ℝ P F ∧ F ≠ P} ∧
          (∀ F ∈ C, ∀ H : Set (Fin d → ℝ), IsExposed ℝ F H → H ∈ C) ∧
          ∀ x, (ψ x).val ∈ R.val ↔ x.val ∈ ⋃₀ C := by
  classical
  let A := ⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}
  let Q := P ∩ l ⁻¹' {α}
  have hvP : v ∈ P := hv.subset (Set.mem_singleton v)
  have hPconv : Convex ℝ P := by rw [hPgen]; exact convex_convexHull ℝ _
  have hBelowVertices (w : Fin d → ℝ) (hw : IsExposed ℝ P {w}) (hwv : w ≠ v) : l w < α := by
    have hwExt : w ∈ P.extremePoints ℝ :=
      exposedPoints_subset_extremePoints (mem_exposedPoints_iff_exposed_singleton.mpr hw)
    rw [hPgen] at hwExt
    exact hBelow w ((Set.mem_insert_iff.mp (extremePoints_convexHull_subset hwExt)).resolve_left hwv)
  obtain ⟨ψ, hψ⟩ := antistar_radial_homeomorph d P hP v hvP l α hα hBelowVertices
  obtain ⟨Φ, hΦ⟩ := vertex_figure_face_orderIso d P hP v hv W hW hPgen l α hα hBelow
  obtain ⟨_, hAP, hAT⟩ := antistar_compact_below_and_terminal d P hP v hvP l α hBelowVertices
  let V := {x : Fin d → ℝ | IsExposed ℝ P {x}}
  obtain ⟨hVfin, hFaces⟩ := polytope_face_eq_convexHull_exposed_vertices d P hP
  have hFaceFin : {F : Set (Fin d → ℝ) | IsExposed ℝ P F}.Finite := by
    apply ((hVfin.powerset).image (convexHull ℝ)).subset
    intro F hF
    exact ⟨F ∩ V, Set.inter_subset_right, (hFaces ⟨F, hF⟩).symm⟩
  refine ⟨ψ, hψ, ?_⟩
  intro R
  let G : {F : PolytopeFace P // v ∈ F.val} := Φ.symm R
  have hRG : R.val = G.val.val ∩ Q := by
    simpa only [G, OrderIso.apply_symm_apply] using hΦ (Φ.symm R)
  let C : Set (Set (Fin d → ℝ)) := {F | IsExposed ℝ P F ∧ v ∉ F ∧ F ⊆ G.val.val}
  have hCFin : C.Finite := hFaceFin.subset (fun F hF => hF.1)
  refine ⟨C, hCFin, ?_, ?_, ?_⟩
  · intro F hF
    refine ⟨hF.1, ?_⟩
    intro hFP
    apply hF.2.1
    rw [hFP]
    exact hvP
  · intro F hF H hH
    refine ⟨isExposed_trans_polytope d P hP F H hF.1 hH, ?_, ?_⟩
    · intro hvH
      exact hF.2.1 (hH.subset hvH)
    · exact hH.subset.trans hF.2.2
  · intro x
    have hDen : 0 < l v - l x.val := sub_pos.mpr (((hAT x.val x.property).1).trans hα)
    have ht₀ : 0 < (l v - α) / (l v - l x.val) := div_pos (sub_pos.mpr hα) hDen
    have ht₁ : (l v - α) / (l v - l x.val) < 1 :=
      (div_lt_one hDen).mpr (by linarith [(hAT x.val x.property).1])
    have hGmem : (ψ x).val ∈ G.val.val ↔ x.val ∈ G.val.val := by
      rw [hψ x]
      exact lineMap_mem_face_iff hPconv G.val.property G.property (hAP x.property) ⟨ht₀, ht₁⟩
    have hRmem : (ψ x).val ∈ R.val ↔ x.val ∈ G.val.val := by
      rw [hRG]
      exact ⟨fun h => hGmem.mp h.1, fun h => ⟨hGmem.mpr h, (ψ x).property⟩⟩
    rw [hRmem]
    constructor
    · intro hxG
      obtain ⟨F, ⟨hF, hvF⟩, hxF⟩ := x.property
      refine ⟨F ∩ G.val.val, ⟨hF.inter G.val.property, ?_, Set.inter_subset_right⟩, ⟨hxF, hxG⟩⟩
      intro hvFG
      exact hvF hvFG.1
    · rintro ⟨F, hF, hxF⟩
      exact hF.2.2 hxF

end Grunbaum2003


-- Exact checked component: CutSpan

set_option autoImplicit false

namespace Grunbaum2003

/-- The explicit vertex-figure generators span the complete cutting hyperplane.
Private development for the boundary-refinement induction. -/
theorem affineSpan_crossing_image_eq_level (d : ℕ) (v : Fin d → ℝ)
    (W : Set (Fin d → ℝ)) (hW : W.Nonempty)
    (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α)
    (hSpan : affineSpan ℝ (insert v W) = ⊤) :
    (affineSpan ℝ ((fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))) '' W) :
      Set (Fin d → ℝ)) = l ⁻¹' {α} := by
  classical
  let q : (Fin d → ℝ) → (Fin d → ℝ) :=
    fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))
  let A : AffineSubspace ℝ (Fin d → ℝ) := affineSpan ℝ (q '' W)
  let H : AffineSubspace ℝ (Fin d → ℝ) :=
    (affineSpan ℝ ({α} : Set ℝ)).comap l.toLinearMap.toAffineMap
  have hH (x : Fin d → ℝ) : x ∈ H ↔ l x = α := by
    change l x ∈ affineSpan ℝ ({α} : Set ℝ) ↔ _
    exact AffineSubspace.mem_affineSpan_singleton ℝ ℝ
  have hqLevel (w : Fin d → ℝ) (hw : w ∈ W) : l (q w) = α := by
    have hq : q w ∈ convexHull ℝ (q '' W) := subset_convexHull ℝ _ ⟨w, hw, rfl⟩
    rw [← convexHull_insert_inter_level_eq d v W hW l α hα hBelow] at hq
    exact hq.2
  have hAH : A ≤ H := by
    apply affineSpan_le_of_subset_coe
    rintro x ⟨w, hw, rfl⟩
    exact (hH _).mpr (hqLevel w hw)
  have hALevel (x : Fin d → ℝ) (hx : x ∈ A) : l x = α := (hH x).mp (hAH hx)
  obtain ⟨w₀, hw₀⟩ := hW
  have hq₀ : q w₀ ∈ A := subset_affineSpan ℝ _ ⟨w₀, hw₀, rfl⟩
  let S : AffineSubspace ℝ (Fin d → ℝ) := affineSpan ℝ (insert v (A : Set (Fin d → ℝ)))
  have hvS : v ∈ S := subset_affineSpan ℝ _ (Set.mem_insert _ _)
  have hCover : insert v W ⊆ S := by
    rintro w (rfl | hw)
    · exact hvS
    · have hqwS : q w ∈ S := subset_affineSpan ℝ _
        (Set.mem_insert_of_mem v (subset_affineSpan ℝ _ ⟨w, hw, rfl⟩))
      let t : ℝ := (l v - α) / (l v - l w)
      have ht : t ≠ 0 := div_ne_zero (sub_pos.mpr hα).ne'
        (sub_pos.mpr ((hBelow w hw).trans hα)).ne'
      have hLine : AffineMap.lineMap v (q w) t⁻¹ = w := by
        change AffineMap.lineMap v (AffineMap.lineMap v w t) t⁻¹ = w
        rw [AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ ht, AffineMap.lineMap_apply_one]
      have hm := AffineMap.lineMap_mem t⁻¹ hvS hqwS
      rwa [hLine] at hm
  have hSTop : S = ⊤ := by
    apply eq_top_iff.mpr
    have h := affineSpan_le_of_subset_coe hCover
    rwa [hSpan] at h
  ext x
  change x ∈ A ↔ l x = α
  constructor
  · exact hALevel x
  · intro hx
    have hxS : x ∈ S := by rw [hSTop]; trivial
    obtain ⟨r, p₀, hp₀, hxp₀⟩ := (AffineSubspace.mem_affineSpan_insert_iff hq₀ v x).mp hxS
    have hEq := congrArg l hxp₀
    simp only [vsub_eq_sub, vadd_eq_add, map_add, map_smul, map_sub, smul_eq_mul] at hEq
    rw [hx, hALevel p₀ hp₀, hALevel (q w₀) hq₀] at hEq
    have hMul : r * (l v - α) = 0 := by linarith
    have hr : r = 0 := (mul_eq_zero.mp hMul).resolve_right (sub_pos.mpr hα).ne'
    simp only [hr, zero_smul, zero_vadd] at hxp₀
    rwa [hxp₀]

end Grunbaum2003


-- Exact checked component: VertexFigureCoordinates

set_option autoImplicit false

namespace Grunbaum2003

/-- An actual finite vertex figure admits full-dimensional coordinates in dimension `d-1`.
Private development for the boundary-refinement induction. -/
theorem exists_vertex_figure_coordinates (d : ℕ) (v : Fin d → ℝ)
    (W : Set (Fin d → ℝ)) (hWfin : W.Finite) (hW : W.Nonempty)
    (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α)
    (hSpan : affineSpan ℝ (insert v W) = ⊤) :
    let Q := (fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))) '' W
    letI : Nonempty (affineSpan ℝ Q) := by
      obtain ⟨w, hw⟩ := hW
      exact ⟨⟨_, subset_affineSpan ℝ Q ⟨w, hw, rfl⟩⟩⟩
    ∃ e : (affineSpan ℝ Q) ≃ᵃ[ℝ] (Fin (d - 1) → ℝ),
      IsDPolytope (convexHull ℝ (e '' (((↑) : affineSpan ℝ Q → (Fin d → ℝ)) ⁻¹' Q))) := by
  classical
  let q : (Fin d → ℝ) → (Fin d → ℝ) :=
    fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))
  let A : AffineSubspace ℝ (Fin d → ℝ) := affineSpan ℝ (q '' W)
  obtain ⟨w₀, hw₀⟩ := hW
  have hq₀ : q w₀ ∈ A := subset_affineSpan ℝ _ ⟨w₀, hw₀, rfl⟩
  haveI : Nonempty A := ⟨⟨q w₀, hq₀⟩⟩
  change ∃ e : A ≃ᵃ[ℝ] (Fin (d - 1) → ℝ),
    IsDPolytope (convexHull ℝ (e '' (((↑) : A → (Fin d → ℝ)) ⁻¹' (q '' W))))
  have hASet : (A : Set (Fin d → ℝ)) = l ⁻¹' {α} :=
    affineSpan_crossing_image_eq_level d v W ⟨w₀, hw₀⟩ l α hα hBelow hSpan
  have hALevel (x : Fin d → ℝ) (hx : x ∈ A) : l x = α := by
    have hx' : x ∈ (A : Set (Fin d → ℝ)) := hx
    rw [hASet] at hx'
    exact hx'
  have hDir : A.direction = LinearMap.ker l.toLinearMap := by
    ext z
    change z ∈ A.direction ↔ l z = 0
    rw [← AffineSubspace.vadd_mem_iff_mem_direction z hq₀]
    change z + q w₀ ∈ (A : Set (Fin d → ℝ)) ↔ l z = 0
    rw [hASet]
    change l (z + q w₀) = α ↔ l z = 0
    rw [map_add, hALevel (q w₀) hq₀]
    constructor <;> intro h <;> linarith
  have hlne : l.toLinearMap ≠ 0 := by
    intro hz
    have hzv := LinearMap.congr_fun hz v
    have hzw := LinearMap.congr_fun hz w₀
    change l v = 0 at hzv
    change l w₀ = 0 at hzw
    linarith [hBelow w₀ hw₀]
  have hRank : Module.finrank ℝ (LinearMap.ker l.toLinearMap) + 1 = d := by
    simpa using Module.Dual.finrank_ker_add_one_of_ne_zero hlne
  have hDim : Module.finrank ℝ A.direction = d - 1 := by
    rw [hDir]
    omega
  let eL : A.direction ≃ₗ[ℝ] (Fin (d - 1) → ℝ) :=
    LinearEquiv.ofFinrankEq A.direction (Fin (d - 1) → ℝ) (by simpa using hDim)
  let e : A ≃ᵃ[ℝ] (Fin (d - 1) → ℝ) :=
    (AffineEquiv.vaddConst ℝ (⟨q w₀, hq₀⟩ : A)).symm.trans eL.toAffineEquiv
  let V : Set A := ((↑) : A → (Fin d → ℝ)) ⁻¹' (q '' W)
  have hVfin : V.Finite := Set.Finite.preimage Subtype.val_injective.injOn (hWfin.image q)
  have hVne : V.Nonempty := ⟨⟨q w₀, hq₀⟩, ⟨w₀, hw₀, rfl⟩⟩
  haveI : Nonempty (q '' W) := ⟨⟨q w₀, ⟨w₀, hw₀, rfl⟩⟩⟩
  have hVSpan : affineSpan ℝ V = ⊤ := affineSpan_coe_preimage_eq_top (q '' W)
  refine ⟨e, ⟨⟨e '' V, hVfin.image e, hVne.image e, rfl⟩, ?_⟩⟩
  rw [affineSpan_convexHull]
  exact e.span_eq_top_iff.mp hVSpan

end Grunbaum2003



-- Checked local ingredient: NativeVertexFigureData


set_option autoImplicit false

namespace Grunbaum2003

/-- The cutting hyperplane in Grünbaum's vertex-figure induction can be chosen strictly
between an exposed vertex and every other vertex, crossing every vertex segment internally.
This is private development for `boundary_refines_simplex_ge_two`, not a published child. -/
theorem exists_vertex_cut_level (d : ℕ) (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    ∃ v : Fin d → ℝ, IsExposed ℝ P {v} ∧
      ∃ (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ),
        α < l v ∧ (∀ x ∈ P, l x ≤ l v) ∧
        ∀ w : Fin d → ℝ, IsExposed ℝ P {w} → w ≠ v →
          l w < α ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ l (AffineMap.lineMap v w t) = α := by
  classical
  obtain ⟨hVfin, hFaces⟩ := polytope_face_eq_convexHull_exposed_vertices d P hP
  have hPne : P.Nonempty := by
    obtain ⟨V, _, hVne, hHull⟩ := hP.1
    rw [hHull]
    exact hVne.convexHull
  have hHull := hFaces ⟨P, IsExposed.refl P⟩
  have hHullne : (convexHull ℝ (P ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})).Nonempty := by
    rw [← hHull]
    exact hPne
  obtain ⟨v, _, hv⟩ := convexHull_nonempty_iff.mp hHullne
  obtain ⟨hvP, l, hl⟩ := mem_exposedPoints_iff_exposed_singleton.mpr hv
  let V' := {x : Fin d → ℝ | IsExposed ℝ P {x}} \ {v}
  have hV'fin : V'.Finite := hVfin.diff
  have hStrict (w : Fin d → ℝ) (hw : w ∈ V') : l w < l v := by
    have hwP : w ∈ P := (mem_exposedPoints_iff_exposed_singleton.mpr hw.1).1
    apply lt_of_le_of_ne (hl w hwP).1
    intro heq
    exact hw.2 ((hl w hwP).2 heq.ge)
  obtain ⟨α, hα, hBelow⟩ : ∃ α : ℝ, α < l v ∧ ∀ w ∈ V', l w < α := by
    by_cases hV'ne : V'.Nonempty
    · obtain ⟨w, hw, hMax⟩ := Set.exists_max_image V' l hV'fin hV'ne
      refine ⟨(l w + l v) / 2, ?_, ?_⟩
      · linarith [hStrict w hw]
      · intro u hu
        linarith [hMax u hu, hStrict w hw]
    · refine ⟨l v - 1, by linarith, ?_⟩
      intro w hw
      exact (hV'ne ⟨w, hw⟩).elim
  refine ⟨v, hv, l, α, hα, fun x hx => (hl x hx).1, ?_⟩
  intro w hw hwv
  have hwα : l w < α := hBelow w ⟨hw, hwv⟩
  refine ⟨hwα, ?_⟩
  let t : ℝ := (l v - α) / (l v - l w)
  have hDen : 0 < l v - l w := sub_pos.mpr (hwα.trans hα)
  have htPos : 0 < t := div_pos (sub_pos.mpr hα) hDen
  have htOne : t < 1 := (div_lt_one hDen).mpr (by linarith)
  refine ⟨t, htPos, htOne, ?_⟩
  have htMul : t * (l v - l w) = l v - α := div_mul_cancel₀ _ hDen.ne'
  rw [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul]
  nlinarith [htMul]

end Grunbaum2003



set_option autoImplicit false

namespace Grunbaum2003

/-- Actual vertex-cut data and a full-dimensional coordinate body for the vertex figure of any
positive-dimensional polytope. The coordinate body is the image of the actual cutting section. -/
theorem exists_vertex_figure_data (d : ℕ) (hd : 0 < d)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    ∃ (v : Fin d → ℝ) (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
      (W : Set (Fin d → ℝ)) (hW : W.Nonempty),
      IsExposed ℝ P {v} ∧
      W = {w : Fin d → ℝ | IsExposed ℝ P {w}} \ {v} ∧
      W.Finite ∧ P = convexHull ℝ (insert v W) ∧
      affineSpan ℝ (insert v W) = ⊤ ∧
      α < l v ∧ (∀ x ∈ P, l x ≤ l v) ∧ (∀ w ∈ W, l w < α) ∧
      let R := (fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))) '' W
      letI : Nonempty (affineSpan ℝ R) := by
        obtain ⟨w, hw⟩ := hW
        exact ⟨⟨_, subset_affineSpan ℝ R ⟨w, hw, rfl⟩⟩⟩
      ∃ e : affineSpan ℝ R ≃ᵃ[ℝ] (Fin (d - 1) → ℝ),
        P ∩ l ⁻¹' {α} = convexHull ℝ R ∧
        affineSpan ℝ (P ∩ l ⁻¹' {α}) = affineSpan ℝ R ∧
        (affineSpan ℝ R : Set (Fin d → ℝ)) = l ⁻¹' {α} ∧
        IsDPolytope (e '' (((↑) : affineSpan ℝ R → (Fin d → ℝ)) ⁻¹' (P ∩ l ⁻¹' {α}))) := by
  classical
  obtain ⟨v, hv, l, α, hα, hMax, hCut⟩ := exists_vertex_cut_level d P hP
  obtain ⟨hVfin, hFaces⟩ := polytope_face_eq_convexHull_exposed_vertices d P hP
  let V := {w : Fin d → ℝ | IsExposed ℝ P {w}}
  let W := V \ {v}
  have hVP : V ⊆ P := fun w hw => (mem_exposedPoints_iff_exposed_singleton.mpr hw).1
  have hHullP : P = convexHull ℝ V := by
    have hHull := hFaces ⟨P, IsExposed.refl P⟩
    change P = convexHull ℝ (P ∩ V) at hHull
    rw [Set.inter_eq_right.mpr hVP] at hHull
    exact hHull
  have hInsert : insert v W = V := by
    ext w
    constructor
    · rintro (rfl | hw)
      · exact hv
      · exact hw.1
    · intro hw
      by_cases hwv : w = v
      · exact Set.mem_insert_iff.mpr (Or.inl hwv)
      · exact Set.mem_insert_iff.mpr (Or.inr ⟨hw, hwv⟩)
  have hPgen : P = convexHull ℝ (insert v W) := by rw [hInsert]; exact hHullP
  have hW : W.Nonempty := by
    by_contra h
    have hEmpty : W = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hPSingle : P ⊆ {v} := by
      rw [hPgen, hEmpty]
      rw [insert_empty_eq, convexHull_singleton]
    have hSub : P.Subsingleton := Set.subsingleton_of_subset_singleton hPSingle
    have : Subsingleton (Fin d → ℝ) :=
      AffineSubspace.subsingleton_of_subsingleton_span_eq_top hSub hP.2
    have hz : (0 : Fin d → ℝ) = 1 := Subsingleton.elim _ _
    exact zero_ne_one (congrFun hz ⟨0, hd⟩)
  have hWfin : W.Finite := hVfin.sdiff
  have hSpan : affineSpan ℝ (insert v W) = ⊤ := by
    rw [← affineSpan_convexHull, ← hPgen]
    exact hP.2
  have hBelow (w : Fin d → ℝ) (hw : w ∈ W) : l w < α := (hCut w hw.1 hw.2).1
  let R := (fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))) '' W
  let A := affineSpan ℝ R
  have : Nonempty A := by
    obtain ⟨w, hw⟩ := hW
    exact ⟨⟨_, subset_affineSpan ℝ R ⟨w, hw, rfl⟩⟩⟩
  obtain ⟨e, hPoly⟩ := exists_vertex_figure_coordinates d v W hWfin hW l α hα hBelow hSpan
  have hQHull : P ∩ l ⁻¹' {α} = convexHull ℝ R := by
    rw [hPgen]
    exact convexHull_insert_inter_level_eq d v W hW l α hα hBelow
  have hASpan : (A : Set (Fin d → ℝ)) = l ⁻¹' {α} :=
    affineSpan_crossing_image_eq_level d v W hW l α hα hBelow hSpan
  let T : Set A := ((↑) : A → (Fin d → ℝ)) ⁻¹' R
  let f : (Fin (d - 1) → ℝ) →ᵃ[ℝ] (Fin d → ℝ) := A.subtype.comp e.symm.toAffineMap
  have hImageT : f '' (e '' T) = R := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      change (e.symm (e z)).val ∈ R
      rw [e.symm_apply_apply]
      exact hz
    · intro x hx
      let z : A := ⟨x, subset_affineSpan ℝ R hx⟩
      refine ⟨e z, ⟨z, hx, rfl⟩, ?_⟩
      change (e.symm (e z)).val = x
      rw [e.symm_apply_apply]
  have hImageHull : f '' convexHull ℝ (e '' T) = P ∩ l ⁻¹' {α} := by
    rw [f.image_convexHull, hImageT, hQHull]
  have hBody : e '' (((↑) : A → (Fin d → ℝ)) ⁻¹' (P ∩ l ⁻¹' {α})) =
      convexHull ℝ (e '' T) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, hz, hzx⟩ := hImageHull.symm.subset hx
      have hzx' : e.symm z = x := Subtype.ext hzx
      have hzex : z = e x := by
        rw [← hzx', e.apply_symm_apply]
      exact hzex ▸ hz
    · intro hy
      have hfy : f y ∈ P ∩ l ⁻¹' {α} := hImageHull.subset ⟨y, hy, rfl⟩
      exact ⟨e.symm y, hfy, e.apply_symm_apply y⟩
  refine ⟨v, l, α, W, hW, hv, rfl, hWfin, hPgen, hSpan, hα, hMax, hBelow, e,
    hQHull, ?_, hASpan, ?_⟩
  · rw [hQHull, affineSpan_convexHull]
  · rw [hBody]
    exact hPoly

end Grunbaum2003


-- Checked local ingredient: SourceRefinementData

set_option autoImplicit false
noncomputable section

namespace Grunbaum2003

/-- A native coordinate polytope and its affine embedding onto the actual
vertex-cut section, with no affine-subspace binders in the conclusion. -/
theorem exists_source_refinement_data (d : ℕ) (hd : 0 < d)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    ∃ (v : Fin d → ℝ) (W : Set (Fin d → ℝ))
      (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
      (Q₀ : Set (Fin (d - 1) → ℝ))
      (f : (Fin (d - 1) → ℝ) →ᵃ[ℝ] (Fin d → ℝ)),
      W.Nonempty ∧ IsExposed ℝ P {v} ∧ W.Finite ∧
      P = convexHull ℝ (insert v W) ∧
      affineSpan ℝ (insert v W) = ⊤ ∧
      α < l v ∧ (∀ x ∈ P, l x ≤ l v) ∧ (∀ w ∈ W, l w < α) ∧
      IsDPolytope Q₀ ∧ Function.Injective f ∧
      f '' Q₀ = P ∩ l ⁻¹' {α} := by
  obtain ⟨v, l, α, W, hW, hv, _, hWfin, hPgen, hSpan, hα, hMax, hBelow, hData⟩ :=
    exists_vertex_figure_data d hd P hP
  let R := (fun w => AffineMap.lineMap v w ((l v - α) / (l v - l w))) '' W
  let A := affineSpan ℝ R
  haveI : Nonempty A := by
    obtain ⟨w, hw⟩ := hW
    exact ⟨⟨_, subset_affineSpan ℝ R ⟨w, hw, rfl⟩⟩⟩
  change ∃ e : A ≃ᵃ[ℝ] (Fin (d - 1) → ℝ), _ at hData
  obtain ⟨e, _, _, hALevel, hQ₀⟩ := hData
  let Q₀ := e '' (((↑) : A → (Fin d → ℝ)) ⁻¹' (P ∩ l ⁻¹' {α}))
  let f : (Fin (d - 1) → ℝ) →ᵃ[ℝ] (Fin d → ℝ) := A.subtype.comp e.symm.toAffineMap
  refine ⟨v, W, l, α, Q₀, f, hW, hv, hWfin, hPgen, hSpan, hα, hMax, hBelow,
    hQ₀, A.subtype_injective.comp e.symm.injective, ?_⟩
  apply Set.Subset.antisymm
  · rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    change (e.symm (e z)).val ∈ P ∩ l ⁻¹' {α}
    rw [e.symm_apply_apply]
    exact hz
  · intro x hx
    have hxA : x ∈ A := (Set.ext_iff.mp hALevel x).mpr hx.2
    let z : A := ⟨x, hxA⟩
    refine ⟨e z, ⟨z, hx, rfl⟩, ?_⟩
    change (e.symm (e z)).val = x
    rw [e.symm_apply_apply]

end Grunbaum2003

end

-- Checked local ingredient: FiniteHullFaces

set_option autoImplicit false

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


end Grunbaum2003

-- Checked local ingredient: SimplexFaces

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Grunbaum2003

/-- A simplex with d+1 independent vertices in real d-space has full affine span. -/
theorem simplex_affineSpan_eq_top (d : ℕ) (v : Fin (d + 1) → Fin d → ℝ)
    (hv : AffineIndependent ℝ v) : affineSpan ℝ (Set.range v) = ⊤ := by
  apply hv.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
  simp only [Fintype.card_fin, Module.finrank_fin_fun]

/-- The actual finite convex hull of a full simplex is a d-polytope. -/
theorem simplex_isDPolytope (d : ℕ) (v : Fin (d + 1) → Fin d → ℝ)
    (hv : AffineIndependent ℝ v) : IsDPolytope (convexHull ℝ (Set.range v)) := by
  refine ⟨⟨Set.range v, Set.finite_range v, Set.range_nonempty v, rfl⟩, ?_⟩
  rw [affineSpan_convexHull]
  exact simplex_affineSpan_eq_top d v hv

/-- Every vertex-subset hull of a simplex is an actual exposed face, and it has
exactly the selected incident vertices. Empty and full subsets are retained. -/
theorem simplex_subset_hull_isExposed_and_labels (d : ℕ)
    (v : Fin (d + 1) → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (I : Finset (Fin (d + 1))) :
    IsExposed ℝ (convexHull ℝ (Set.range v)) (convexHull ℝ (v '' (I : Set (Fin (d + 1))))) ∧
      ∀ j : Fin (d + 1), v j ∈ convexHull ℝ (v '' (I : Set (Fin (d + 1)))) ↔ j ∈ I := by
  classical
  rcases I.eq_empty_or_nonempty with rfl | hI
  · simp only [Finset.coe_empty, Set.image_empty, convexHull_empty, Set.mem_empty_iff_false,
      Finset.notMem_empty, implies_true, and_true]
    exact isExposed_empty
  let b : AffineBasis (Fin (d + 1)) ℝ (Fin d → ℝ) :=
    ⟨v, hv, simplex_affineSpan_eq_top d v hv⟩
  let L : (Fin d → ℝ) →ₗ[ℝ] ℝ := ∑ i ∈ I, (b.coord i).linear
  let c : ℝ := ∑ i ∈ I, b.coord i 0
  let l : StrongDual ℝ (Fin d → ℝ) := L.toContinuousLinearMap
  have hl : ∀ j : Fin (d + 1), l (v j) = (if j ∈ I then 1 else 0) - c := by
    intro j
    change L (v j) = _
    simp only [L, LinearMap.sum_apply]
    have hlin : ∀ i : Fin (d + 1), (b.coord i).linear (v j) =
        b.coord i (v j) - b.coord i 0 := by
      intro i
      exact congrFun (b.coord i).decomp' (v j)
    simp_rw [hlin]
    rw [Finset.sum_sub_distrib]
    change (∑ i ∈ I, b.coord i (b j)) - c = _
    simp only [AffineBasis.coord_apply, Finset.sum_ite_eq']
  apply exposedFace_of_label_maximizers v (I : Set (Fin (d + 1)))
    (Finset.coe_nonempty.mpr hI) l (1 - c)
  · intro j
    rw [hl j]
    by_cases hj : j ∈ I
    · simp only [hj, if_true, le_refl]
    · simp only [hj, if_false]
      exact sub_le_sub_right zero_le_one c
  · intro j
    rw [hl j]
    by_cases hj : j ∈ I
    · simp only [hj, if_true, SetLike.mem_coe]
    · simp only [hj, if_false, Finset.mem_coe, iff_false]
      exact fun h ↦ zero_ne_one (sub_left_injective h)

end Grunbaum2003

end

-- Checked local ingredient: SimplexBoundary

set_option autoImplicit false
noncomputable section

namespace Grunbaum2003

/-- The opposite facet is an actual exposed face and contains exactly the
vertices other than the chosen apex. -/
theorem simplex_opposite_facet (d : ℕ)
    (v : Fin (d + 1) → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (a : Fin (d + 1)) :
    IsExposed ℝ (convexHull ℝ (Set.range v))
      (convexHull ℝ (v '' {i | i ≠ a})) ∧
      ∀ j, v j ∈ convexHull ℝ (v '' {i | i ≠ a}) ↔ j ≠ a := by
  classical
  have h := simplex_subset_hull_isExposed_and_labels d v hv (Finset.univ.erase a)
  have hset : ((Finset.univ.erase a : Finset (Fin (d + 1))) : Set (Fin (d + 1))) =
      {i | i ≠ a} := by
    ext i
    simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true,
      Set.mem_ofPred_eq]
  rw [hset] at h
  simpa only [Finset.mem_erase, Finset.mem_univ, and_true] using h

/-- The apex itself is an exposed singleton of the actual simplex. -/
theorem simplex_apex_isExposed (d : ℕ)
    (v : Fin (d + 1) → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (a : Fin (d + 1)) :
    IsExposed ℝ (convexHull ℝ (Set.range v)) {v a} := by
  have h := (simplex_subset_hull_isExposed_and_labels d v hv {a}).1
  simpa only [Finset.coe_singleton, Set.image_singleton, convexHull_singleton] using h

/-- An exposed face of a simplex avoids the apex exactly when it is contained
in the opposite facet. -/
theorem simplex_face_avoids_apex_iff (d : ℕ)
    (v : Fin (d + 1) → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (a : Fin (d + 1)) {F : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ (convexHull ℝ (Set.range v)) F) :
    v a ∉ F ↔ F ⊆ convexHull ℝ (v '' {i | i ≠ a}) := by
  have hB := simplex_opposite_facet d v hv a
  constructor
  · intro ha
    apply (exposedFace_subset_iff_incident_labels v hF hB.1).mpr
    intro i hi
    apply (hB.2 i).mpr
    intro hia
    exact ha (hia ▸ hi)
  · intro h ha
    exact ((hB.2 a).mp (h ha)) rfl

/-- The complete antistar carrier in a simplex is its opposite facet. -/
theorem simplex_antistar_eq_opposite_facet (d : ℕ)
    (v : Fin (d + 1) → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (a : Fin (d + 1)) :
    ⋃₀ {F : Set (Fin d → ℝ) |
      IsExposed ℝ (convexHull ℝ (Set.range v)) F ∧ v a ∉ F} =
        convexHull ℝ (v '' {i | i ≠ a}) := by
  have hB := simplex_opposite_facet d v hv a
  apply Set.Subset.antisymm
  · rintro x ⟨F, ⟨hF, ha⟩, hx⟩
    exact (simplex_face_avoids_apex_iff d v hv a hF).mp ha hx
  · intro x hx
    exact Set.mem_sUnion.mpr ⟨_, ⟨hB.1, fun ha => (hB.2 a).mp ha rfl⟩, hx⟩

/-- Every face through the apex is the cone over its intersection with the
opposite facet, with the equality on actual point sets. -/
theorem simplex_face_through_apex_eq_cone (d : ℕ)
    (v : Fin (d + 1) → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (a : Fin (d + 1)) {F : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ (convexHull ℝ (Set.range v)) F) (ha : v a ∈ F) :
    F = convexHull ℝ (insert (v a) (F ∩ convexHull ℝ (v '' {i | i ≠ a}))) := by
  have hB := simplex_opposite_facet d v hv a
  have hFconv := hF.convex (convex_convexHull ℝ (Set.range v))
  apply Set.Subset.antisymm
  · apply (exposedFace_eq_convexHull_incident_range v hF).subset.trans
    apply convexHull_min
    · rintro x ⟨hx, i, rfl⟩
      apply subset_convexHull ℝ _
      by_cases hi : i = a
      · exact Set.mem_insert_iff.mpr (Or.inl (congrArg v hi))
      · exact Set.mem_insert_of_mem _ ⟨hx, (hB.2 i).mpr hi⟩
    · exact convex_convexHull ℝ _
  · apply convexHull_min
    · intro x hx
      rcases Set.mem_insert_iff.mp hx with h | h
      · exact h ▸ ha
      · exact h.1
    · exact hFconv

end Grunbaum2003

end

-- Checked local ingredient: SimplexCoordinates

set_option autoImplicit false
noncomputable section

namespace Grunbaum2003

/-- An affinely independent finite hull stays an affinely independent finite
hull in any affine coordinates of a containing affine subspace. -/
theorem affineIndependent_hull_in_coordinates {d n k : ℕ}
    (u : Fin n → Fin d → ℝ) (hu : AffineIndependent ℝ u)
    (A : AffineSubspace ℝ (Fin d → ℝ)) [Nonempty A]
    (hA : ∀ i, u i ∈ A) (e : A ≃ᵃ[ℝ] (Fin k → ℝ)) :
    ∃ w : Fin n → Fin k → ℝ, AffineIndependent ℝ w ∧
      e '' (((↑) : A → (Fin d → ℝ)) ⁻¹' convexHull ℝ (Set.range u)) =
        convexHull ℝ (Set.range w) := by
  let uA : Fin n → A := fun i => ⟨u i, hA i⟩
  have huA : AffineIndependent ℝ uA :=
    AffineIndependent.of_comp A.subtype hu
  let w := e ∘ uA
  let g : (Fin k → ℝ) →ᵃ[ℝ] (Fin d → ℝ) := A.subtype.comp e.symm.toAffineMap
  refine ⟨w, huA.map' e.toAffineMap e.injective, ?_⟩
  have hcomp : g ∘ w = u := by
    funext i
    exact congrArg Subtype.val (e.symm_apply_apply (uA i))
  have hHull : g '' convexHull ℝ (Set.range w) = convexHull ℝ (Set.range u) := by
    rw [AffineMap.image_convexHull, ← Set.range_comp, hcomp]
  rw [← hHull]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, heq⟩ := hx
    have hxy : e.symm y = x := Subtype.ext heq
    have hEq : e x = y := by rw [← hxy, e.apply_symm_apply]
    exact hEq.symm ▸ hy
  · intro hz
    refine ⟨e.symm z, ⟨z, hz, rfl⟩, e.apply_symm_apply z⟩

/-- The nonapex vertices, indexed without repetitions, form an independent
family whose actual range is the opposite-facet generating set. -/
theorem simplex_opposite_vertex_family (d : ℕ)
    (v : Fin (d + 1) → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (a : Fin (d + 1)) :
    ∃ w : Fin d → Fin d → ℝ, AffineIndependent ℝ w ∧
      Set.range w = v '' {i | i ≠ a} := by
  refine ⟨v ∘ a.succAbove,
    hv.comp_embedding ⟨a.succAbove, Fin.succAbove_right_injective⟩, ?_⟩
  rw [Set.range_comp, Fin.range_succAbove]
  rfl

/-- Every coordinate realization of the halfway vertex figure has exactly
an independent family of d generating points; hence it is a simplex. -/
theorem simplex_halfway_hull_in_coordinates (d : ℕ)
    (v : Fin (d + 1) → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (a : Fin (d + 1)) (A : AffineSubspace ℝ (Fin d → ℝ)) [Nonempty A]
    (hA : ∀ i, i ≠ a → AffineMap.homothety (v a) (1 / 2 : ℝ) (v i) ∈ A)
    (e : A ≃ᵃ[ℝ] (Fin (d - 1) → ℝ)) :
    ∃ w : Fin d → Fin (d - 1) → ℝ, AffineIndependent ℝ w ∧
      e '' (((↑) : A → (Fin d → ℝ)) ⁻¹'
        ((AffineMap.homothety (v a) (1 / 2 : ℝ)) '' convexHull ℝ (v '' {i | i ≠ a}))) =
        convexHull ℝ (Set.range w) := by
  obtain ⟨u, hu, hurange⟩ := simplex_opposite_vertex_family d v hv a
  let f := AffineMap.homothety (v a) (1 / 2 : ℝ)
  have hf : Function.Injective f := AffineMap.homothety_injective _ (by norm_num)
  have hfu : AffineIndependent ℝ (f ∘ u) := hu.map' f hf
  have hfuA : ∀ i, (f ∘ u) i ∈ A := by
    intro i
    have hi : u i ∈ v '' {j | j ≠ a} := by rw [← hurange]; exact Set.mem_range_self i
    obtain ⟨j, hj, heq⟩ := hi
    rw [Function.comp_apply, ← heq]
    exact hA j hj
  have hHull : convexHull ℝ (Set.range (f ∘ u)) =
      f '' convexHull ℝ (v '' {i | i ≠ a}) := by
    rw [Set.range_comp, hurange, ← AffineMap.image_convexHull]
  rw [← hHull]
  exact affineIndependent_hull_in_coordinates (f ∘ u) hfu A hfuA e

end Grunbaum2003

end

-- Checked local ingredient: SimplexProperFaces

set_option autoImplicit false
noncomputable section

namespace Grunbaum2003

/-- The opposite facet is proper in the full simplex, including dimension zero. -/
theorem simplex_opposite_facet_ne_full (d : ℕ)
    (v : Fin (d + 1) → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (a : Fin (d + 1)) :
    convexHull ℝ (v '' {i | i ≠ a}) ≠ convexHull ℝ (Set.range v) := by
  intro h
  have ha : v a ∈ convexHull ℝ (v '' {i | i ≠ a}) := by
    rw [h]
    exact subset_convexHull ℝ _ (Set.mem_range_self a)
  exact ((simplex_opposite_facet d v hv a).2 a).mp ha rfl

/-- The base of a proper simplex face through the apex is a proper exposed
face of the opposite facet. -/
theorem simplex_proper_face_base (d : ℕ)
    (v : Fin (d + 1) → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (a : Fin (d + 1)) {F : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ (convexHull ℝ (Set.range v)) F)
    (hproper : F ≠ convexHull ℝ (Set.range v)) (ha : v a ∈ F) :
    IsExposed ℝ (convexHull ℝ (v '' {i | i ≠ a}))
      (F ∩ convexHull ℝ (v '' {i | i ≠ a})) ∧
      F ∩ convexHull ℝ (v '' {i | i ≠ a}) ≠ convexHull ℝ (v '' {i | i ≠ a}) := by
  have hB := simplex_opposite_facet d v hv a
  constructor
  · exact (hF.inter hB.1).mono hB.1.subset Set.inter_subset_right
  · intro heq
    have hBF : convexHull ℝ (v '' {i | i ≠ a}) ⊆ F := by
      rw [← heq]
      exact Set.inter_subset_left
    have hPF : convexHull ℝ (Set.range v) ⊆ F := by
      apply convexHull_min
      · rintro x ⟨i, rfl⟩
        by_cases hi : i = a
        · exact hi ▸ ha
        · exact hBF ((hB.2 i).mpr hi)
      · exact hF.convex (convex_convexHull ℝ (Set.range v))
    exact hproper (hF.subset.antisymm hPF)

/-- A face missing the apex is also an exposed face of the opposite facet. -/
theorem simplex_face_avoiding_apex_isExposed_in_base (d : ℕ)
    (v : Fin (d + 1) → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (a : Fin (d + 1)) {F : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ (convexHull ℝ (Set.range v)) F) (ha : v a ∉ F) :
    IsExposed ℝ (convexHull ℝ (v '' {i | i ≠ a})) F := by
  exact hF.mono (simplex_opposite_facet d v hv a).1.subset
    ((simplex_face_avoids_apex_iff d v hv a hF).mp ha)

end Grunbaum2003

end

-- Checked local ingredient: SimplexCut

set_option autoImplicit false
noncomputable section

namespace Grunbaum2003

/-- The apex barycentric functional cuts every other vertex segment halfway.
Consequently the actual vertex figure is the half-scale homothetic image of
the actual opposite facet. -/
theorem simplex_halfway_cut (d : ℕ) (hd : 0 < d)
    (v : Fin (d + 1) → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (a : Fin (d + 1)) :
    ∃ (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ),
      α < l (v a) ∧
      (∀ x ∈ convexHull ℝ (Set.range v), l x ≤ l (v a)) ∧
      (∀ w ∈ v '' {i | i ≠ a}, l w < α) ∧
      (∀ w ∈ v '' {i | i ≠ a}, (l (v a) - α) / (l (v a) - l w) = (1 / 2 : ℝ)) ∧
      convexHull ℝ (Set.range v) ∩ l ⁻¹' {α} =
        (AffineMap.homothety (v a) (1 / 2 : ℝ)) ''
          convexHull ℝ (v '' {i | i ≠ a}) := by
  classical
  let b : AffineBasis (Fin (d + 1)) ℝ (Fin d → ℝ) :=
    ⟨v, hv, simplex_affineSpan_eq_top d v hv⟩
  let c : ℝ := b.coord a 0
  let l : StrongDual ℝ (Fin d → ℝ) := (b.coord a).linear.toContinuousLinearMap
  let α : ℝ := 1 / 2 - c
  have hl (j : Fin (d + 1)) : l (v j) = (if a = j then 1 else 0) - c := by
    change (b.coord a).linear (v j) = _
    rw [congrFun (b.coord a).decomp' (v j)]
    change b.coord a (b j) - c = _
    rw [AffineBasis.coord_apply]
  have hla : l (v a) = 1 - c := by
    rw [hl a, if_pos rfl]
  have hOff : ∀ w ∈ v '' {i | i ≠ a}, l w = -c := by
    rintro w ⟨j, hj, rfl⟩
    rw [hl j, if_neg (Ne.symm hj), zero_sub]
  have hα : α < l (v a) := by rw [hla]; dsimp [α]; linarith
  have hBelow : ∀ w ∈ v '' {i | i ≠ a}, l w < α := by
    intro w hw
    rw [hOff w hw]
    dsimp [α]
    linarith
  have hratio : ∀ w ∈ v '' {i | i ≠ a},
      (l (v a) - α) / (l (v a) - l w) = (1 / 2 : ℝ) := by
    intro w hw
    rw [hla, hOff w hw]
    dsimp [α]
    ring_nf
  have hmax : ∀ x ∈ convexHull ℝ (Set.range v), l x ≤ l (v a) := by
    apply convexHull_min
    · rintro x ⟨j, rfl⟩
      change l (v j) ≤ l (v a)
      rw [hl j, hla]
      split_ifs <;> linarith
    · exact (convex_Iic (l (v a))).linear_preimage l.toLinearMap
  have hW : (v '' {i | i ≠ a}).Nonempty := by
    haveI : Nontrivial (Fin (d + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨j, hj⟩ := exists_ne a
    exact ⟨v j, j, hj, rfl⟩
  have hvertices : Set.range v = insert (v a) (v '' {i | i ≠ a}) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      by_cases hj : j = a
      · exact Set.mem_insert_iff.mpr (Or.inl (congrArg v hj))
      · exact Set.mem_insert_of_mem _ ⟨j, hj, rfl⟩
    · intro hx
      rcases Set.mem_insert_iff.mp hx with hx | ⟨j, _, rfl⟩
      · exact hx ▸ Set.mem_range_self a
      · exact Set.mem_range_self j
  refine ⟨l, α, hα, hmax, hBelow, hratio, ?_⟩
  rw [hvertices, convexHull_insert_inter_level_eq d (v a) _ hW l α hα hBelow,
    AffineMap.image_convexHull]
  congr 1
  apply Set.image_congr
  intro w hw
  rw [hratio w hw, AffineMap.homothety_eq_lineMap]

end Grunbaum2003

end

-- Checked local ingredient: SimplexCutBase

set_option autoImplicit false
noncomputable section

namespace Grunbaum2003

/-- The halfway cut is constant on the entire opposite facet. Its radial map
agrees pointwise with the same homothety on the full antistar carrier. -/
theorem simplex_halfway_cut_on_opposite_facet (d : ℕ) (hd : 0 < d)
    (v : Fin (d + 1) → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (a : Fin (d + 1)) :
    ∃ (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ),
      α < l (v a) ∧
      (∀ x ∈ convexHull ℝ (Set.range v), l x ≤ l (v a)) ∧
      (∀ b ∈ convexHull ℝ (v '' {i | i ≠ a}), l b = 2 * α - l (v a)) ∧
      (∀ b ∈ convexHull ℝ (v '' {i | i ≠ a}), l b < α) ∧
      (∀ b ∈ convexHull ℝ (v '' {i | i ≠ a}),
        AffineMap.lineMap (v a) b ((l (v a) - α) / (l (v a) - l b)) =
          AffineMap.homothety (v a) (1 / 2 : ℝ) b) ∧
      convexHull ℝ (Set.range v) ∩ l ⁻¹' {α} =
        (AffineMap.homothety (v a) (1 / 2 : ℝ)) ''
          convexHull ℝ (v '' {i | i ≠ a}) := by
  obtain ⟨l, α, hα, hmax, hBelow, hratio, hsection⟩ := simplex_halfway_cut d hd v hv a
  have hconst : ∀ w ∈ v '' {i | i ≠ a}, l w = 2 * α - l (v a) := by
    intro w hw
    have hDen : l (v a) - l w ≠ 0 := (sub_pos.mpr ((hBelow w hw).trans hα)).ne'
    have hmul := (div_eq_iff hDen).mp (hratio w hw)
    linarith only [hmul]
  have hbase : ∀ b ∈ convexHull ℝ (v '' {i | i ≠ a}), l b = 2 * α - l (v a) := by
    apply convexHull_min
    · intro w hw
      exact hconst w hw
    · exact (convex_singleton (2 * α - l (v a))).linear_preimage l.toLinearMap
  refine ⟨l, α, hα, hmax, hbase, ?_, ?_, hsection⟩
  · intro b hb
    rw [hbase b hb]
    linarith only [hα]
  · intro b hb
    have hDen : l (v a) - l b ≠ 0 := by
      rw [hbase b hb]
      linarith only [hα]
    have hratioB : (l (v a) - α) / (l (v a) - l b) = (1 / 2 : ℝ) := by
      apply (div_eq_iff hDen).mpr
      rw [hbase b hb]
      ring
    rw [hratioB, AffineMap.homothety_eq_lineMap]

end Grunbaum2003

end

-- Checked local ingredient: SimplexTargetData

set_option autoImplicit false
noncomputable section

namespace Grunbaum2003

/-- Actual target geometry for the boundary induction: its antistar is the
opposite facet, its radial cut is a fixed affine homothety on that facet, and
the facet is an injective affine image of a native lower-dimensional simplex. -/
theorem exists_simplex_target_data (d : ℕ) (hd : 0 < d)
    (v : Fin (d + 1) → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (a : Fin (d + 1)) :
    let T := convexHull ℝ (Set.range v)
    let W := v '' {i | i ≠ a}
    let B := convexHull ℝ W
    let r := AffineMap.homothety (v a) (1 / 2 : ℝ)
    ∃ (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
      (u : Fin ((d - 1) + 1) → Fin (d - 1) → ℝ)
      (g : (Fin (d - 1) → ℝ) →ᵃ[ℝ] (Fin d → ℝ)),
      W.Nonempty ∧ W.Finite ∧
      T = convexHull ℝ (insert (v a) W) ∧
      affineSpan ℝ (insert (v a) W) = ⊤ ∧
      IsExposed ℝ T {v a} ∧ IsExposed ℝ T B ∧ B ≠ T ∧
      v a ∉ B ∧
      (⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ T F ∧ v a ∉ F}) = B ∧
      α < l (v a) ∧ (∀ x ∈ T, l x ≤ l (v a)) ∧
      (∀ w ∈ W, l w < α) ∧
      (∀ b ∈ B, AffineMap.lineMap (v a) b ((l (v a) - α) / (l (v a) - l b)) = r b) ∧
      r '' B = T ∩ l ⁻¹' {α} ∧
      AffineIndependent ℝ u ∧ Function.Injective g ∧
      g '' convexHull ℝ (Set.range u) = B := by
  classical
  dsimp only
  let T := convexHull ℝ (Set.range v)
  let W := v '' {i | i ≠ a}
  let B := convexHull ℝ W
  let r := AffineMap.homothety (v a) (1 / 2 : ℝ)
  have hW : W.Nonempty := by
    haveI : Nontrivial (Fin (d + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨j, hj⟩ := exists_ne a
    exact ⟨v j, j, hj, rfl⟩
  have hWfin : W.Finite := (Set.toFinite {i : Fin (d + 1) | i ≠ a}).image v
  have hvertices : Set.range v = insert (v a) W := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      by_cases hj : j = a
      · exact Set.mem_insert_iff.mpr (Or.inl (congrArg v hj))
      · exact Set.mem_insert_of_mem _ ⟨j, hj, rfl⟩
    · intro hx
      rcases Set.mem_insert_iff.mp hx with hx | ⟨j, _, rfl⟩
      · exact hx ▸ Set.mem_range_self a
      · exact Set.mem_range_self j
  have hSpan : affineSpan ℝ (insert (v a) W) = ⊤ := by
    rw [← hvertices]
    exact simplex_affineSpan_eq_top d v hv
  obtain ⟨l, α, hα, hmax, _, hBelowB, hRad, hsection⟩ :=
    simplex_halfway_cut_on_opposite_facet d hd v hv a
  have hBelow : ∀ w ∈ W, l w < α := by
    intro w hw
    exact hBelowB w (subset_convexHull ℝ W hw)
  let q := fun w : Fin d → ℝ =>
    AffineMap.lineMap (v a) w ((l (v a) - α) / (l (v a) - l w))
  let R := q '' W
  have hR : R = r '' W := by
    apply Set.image_congr
    intro w hw
    exact hRad w (subset_convexHull ℝ W hw)
  let A := affineSpan ℝ R
  have hQhull : r '' B = convexHull ℝ R := by
    rw [hR, ← AffineMap.image_convexHull]
  have hQA : r '' B ⊆ A := by
    rw [hQhull]
    exact convexHull_subset_affineSpan R
  haveI : Nonempty A := by
    obtain ⟨w, hw⟩ := hW
    exact ⟨⟨q w, subset_affineSpan ℝ R ⟨w, hw, rfl⟩⟩⟩
  have hCoordinates := exists_vertex_figure_coordinates d (v a) W hWfin hW l α hα hBelow hSpan
  change ∃ e : A ≃ᵃ[ℝ] (Fin (d - 1) → ℝ), _ at hCoordinates
  obtain ⟨e, _⟩ := hCoordinates
  have hA : ∀ i, i ≠ a → r (v i) ∈ A := by
    intro i hi
    apply subset_affineSpan ℝ R
    rw [hR]
    exact ⟨v i, ⟨i, hi, rfl⟩, rfl⟩
  obtain ⟨w, hw, hchart⟩ := simplex_halfway_hull_in_coordinates d v hv a A hA e
  let η : Fin ((d - 1) + 1) ≃ Fin d := finCongr (by omega)
  let u := w ∘ η
  have hu : AffineIndependent ℝ u := hw.comp_embedding η.toEmbedding
  have hurange : Set.range u = Set.range w := by
    rw [Set.range_comp, η.surjective.range_eq, Set.image_univ]
  let s := AffineMap.homothety (v a) (2 : ℝ)
  let g : (Fin (d - 1) → ℝ) →ᵃ[ℝ] (Fin d → ℝ) :=
    s.comp (A.subtype.comp e.symm.toAffineMap)
  have hg : Function.Injective g :=
    (AffineMap.homothety_injective (v a) (by norm_num : (2 : ℝ) ≠ 0)).comp
      (A.subtype_injective.comp e.symm.injective)
  have hinv (b : Fin d → ℝ) : s (r b) = b := by
    change AffineMap.homothety (v a) (2 : ℝ)
      (AffineMap.homothety (v a) (1 / 2 : ℝ) b) = b
    rw [← AffineMap.homothety_mul_apply]
    norm_num
  have hgcoord (z : A) : g (e z) = s (z : Fin d → ℝ) := by
    change s ((e.symm (e z) : A) : Fin d → ℝ) = _
    rw [e.symm_apply_apply]
  have hgimage : g '' convexHull ℝ (Set.range u) = B := by
    rw [hurange, ← hchart]
    apply Set.Subset.antisymm
    · rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      obtain ⟨b, hb, hzb⟩ := hz
      rw [hgcoord, ← hzb, hinv]
      exact hb
    · intro b hb
      let z : A := ⟨r b, hQA ⟨b, hb, rfl⟩⟩
      refine ⟨e z, ⟨z, ⟨b, hb, rfl⟩, rfl⟩, ?_⟩
      rw [hgcoord]
      exact hinv b
  have hB := simplex_opposite_facet d v hv a
  refine ⟨l, α, u, g, hW, hWfin, congrArg (convexHull ℝ) hvertices, hSpan,
    simplex_apex_isExposed d v hv a, hB.1,
    simplex_opposite_facet_ne_full d v hv a, ?_,
    simplex_antistar_eq_opposite_facet d v hv a, hα, hmax, hBelow, hRad,
    hsection.symm, hu, hg, hgimage⟩
  exact fun ha => (hB.2 a).mp ha rfl

end Grunbaum2003

end

-- Checked local ingredient: AntistarSubcomplex

set_option autoImplicit false

namespace Grunbaum2003
open Set

/-- On the antistar, a finite boundary subcomplex may be restricted to its faces
avoiding the chosen vertex. Face closure retains every point of its old carrier
that lies in the antistar, and the new carrier is supported in the antistar. -/
theorem boundary_subcomplex_restrict_antistar {d : ℕ}
    {P : Set (Fin d → ℝ)} (v : Fin d → ℝ)
    (C : Set (Set (Fin d → ℝ))) (hfin : C.Finite) (hsub : C ⊆ boundaryFaces P)
    (hclosed : ∀ F ∈ C, ∀ G : Set (Fin d → ℝ), IsExposed ℝ F G → G ∈ C) :
    ∃ D : Set (Set (Fin d → ℝ)), D.Finite ∧ D ⊆ boundaryFaces P ∧
      (∀ F ∈ D, ∀ G : Set (Fin d → ℝ), IsExposed ℝ F G → G ∈ D) ∧
      (∀ F ∈ D, v ∉ F) ∧
      (⋃₀ D ⊆ ⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}) ∧
      ∀ x : (⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}),
        x.val ∈ ⋃₀ D ↔ x.val ∈ ⋃₀ C := by
  let D : Set (Set (Fin d → ℝ)) := {F | F ∈ C ∧ v ∉ F}
  have hDC : D ⊆ C := fun F hF => hF.1
  refine ⟨D, hfin.subset hDC, hDC.trans hsub, ?_, ?_, ?_, ?_⟩
  · intro F hF G hG
    exact ⟨hclosed F hF.1 G hG, fun hvG => hF.2 (hG.subset hvG)⟩
  · intro F hF
    exact hF.2
  · rintro x ⟨F, hF, hxF⟩
    exact ⟨F, ⟨(hsub hF.1).1, hF.2⟩, hxF⟩
  · intro x
    constructor
    · rintro ⟨F, hF, hxF⟩
      exact ⟨F, hF.1, hxF⟩
    · rintro ⟨F, hFC, hxF⟩
      obtain ⟨G, ⟨hG, hvG⟩, hxG⟩ := x.property
      have hF := (hsub hFC).1
      have hIF : IsExposed ℝ F (F ∩ G) :=
        (hF.inter hG).mono hF.subset Set.inter_subset_left
      exact ⟨F ∩ G, ⟨hclosed F hFC _ hIF, fun hvFG => hvG hvFG.2⟩, ⟨hxF, hxG⟩⟩

end Grunbaum2003


-- Checked local ingredient: FiniteSubcomplexPreimages

set_option autoImplicit false

namespace Grunbaum2003

/-- Finite unions of cells with finite subcomplex preimages again have a finite
subcomplex preimage, using the same point map throughout. -/
theorem finite_subcomplex_preimage_sUnion
    {X E F : Type*} (f : X → F) (p : X → E)
    (S : Set (Set E)) (Subface : Set E → Set E → Prop)
    (C : Set (Set F)) (hC : C.Finite)
    (h : ∀ K ∈ C, ∃ D : Set (Set E),
      D.Finite ∧ D ⊆ S ∧
      (∀ A ∈ D, ∀ B, Subface A B → B ∈ D) ∧
      ∀ x, f x ∈ K ↔ p x ∈ ⋃₀ D) :
    ∃ D : Set (Set E), D.Finite ∧ D ⊆ S ∧
      (∀ A ∈ D, ∀ B, Subface A B → B ∈ D) ∧
      ∀ x, f x ∈ ⋃₀ C ↔ p x ∈ ⋃₀ D := by
  classical
  choose D hDfin hDsub hDclosed hDmem using h
  let U := ⋃ (K : Set F) (hK : K ∈ C), D K hK
  have hUmem (A : Set E) : A ∈ U ↔ ∃ K, ∃ hK : K ∈ C, A ∈ D K hK := by
    simp only [U, Set.mem_iUnion]
  refine ⟨U, hC.biUnion' (fun K hK => hDfin K hK), ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨K, hK, hAD⟩ := (hUmem A).mp hA
    exact hDsub K hK hAD
  · intro A hA B hAB
    obtain ⟨K, hK, hAD⟩ := (hUmem A).mp hA
    exact (hUmem B).mpr ⟨K, hK, hDclosed K hK A hAD B hAB⟩
  · intro x
    constructor
    · rintro ⟨K, hK, hxK⟩
      obtain ⟨A, hAD, hxA⟩ := (hDmem K hK x).mp hxK
      exact ⟨A, (hUmem A).mpr ⟨K, hK, hAD⟩, hxA⟩
    · rintro ⟨A, hAU, hxA⟩
      obtain ⟨K, hK, hAD⟩ := (hUmem A).mp hAU
      exact ⟨K, hK, (hDmem K hK x).mpr ⟨A, hAD, hxA⟩⟩

end Grunbaum2003


-- Checked local ingredient: AntistarComposite

set_option autoImplicit false

namespace Grunbaum2003
open Set

/-- Composing the actual antistar map with one body map combines their finite
subcomplex preimages. The resulting cells avoid the chosen vertex; for the
whole target base their union is exactly the entire antistar. -/
theorem antistar_body_composite_face_preimages {d : ℕ}
    {P Q B : Set (Fin d → ℝ)} (v : Fin d → ℝ)
    (ψ : (⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}) ≃ₜ Q)
    (hψ : ∀ R : PolytopeFace Q,
      ∃ C : Set (Set (Fin d → ℝ)), C.Finite ∧ C ⊆ boundaryFaces P ∧
        (∀ F ∈ C, ∀ G : Set (Fin d → ℝ), IsExposed ℝ F G → G ∈ C) ∧
        ∀ x, (ψ x).val ∈ R.val ↔ x.val ∈ ⋃₀ C)
    (H : Q ≃ₜ B)
    (hH : ∀ K ∈ boundaryFaces B,
      ∃ C : Set (Set (Fin d → ℝ)), C.Finite ∧ C ⊆ boundaryFaces Q ∧
        (∀ F ∈ C, ∀ G : Set (Fin d → ℝ), IsExposed ℝ F G → G ∈ C) ∧
        ∀ x : Q, (H x).val ∈ K ↔ x.val ∈ ⋃₀ C) :
    ∀ K : PolytopeFace B,
      ∃ D : Set (Set (Fin d → ℝ)), D.Finite ∧ D ⊆ boundaryFaces P ∧
        (∀ F ∈ D, ∀ G : Set (Fin d → ℝ), IsExposed ℝ F G → G ∈ D) ∧
        (∀ F ∈ D, v ∉ F) ∧
        (⋃₀ D ⊆ ⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}) ∧
        (K.val = B → ⋃₀ D = ⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}) ∧
        ∀ x, (H (ψ x)).val ∈ K.val ↔ x.val ∈ ⋃₀ D := by
  intro K
  by_cases hKB : K.val = B
  · obtain ⟨C, hfin, hsub, hclosed, hfiber⟩ := hψ ⟨Q, IsExposed.refl Q⟩
    obtain ⟨D, hDfin, hDsub, hDclosed, hDavoid, hDsupport, hDmem⟩ :=
      boundary_subcomplex_restrict_antistar v C hfin hsub hclosed
    have hDEq : ⋃₀ D = ⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F} := by
      apply Set.Subset.antisymm hDsupport
      intro x hx
      exact (hDmem ⟨x, hx⟩).mpr ((hfiber ⟨x, hx⟩).mp (ψ ⟨x, hx⟩).property)
    refine ⟨D, hDfin, hDsub, hDclosed, hDavoid, hDsupport, fun _ => hDEq, ?_⟩
    intro x
    constructor
    · intro _
      rw [hDEq]
      exact x.property
    · intro _
      rw [hKB]
      exact (H (ψ x)).property
  · obtain ⟨C, hfin, hsub, hclosed, hfiber⟩ := hH K.val ⟨K.property, hKB⟩
    obtain ⟨D, hDfin, hDsub, hDclosed, hDmem⟩ :=
      finite_subcomplex_preimage_sUnion
        (fun x : (⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}) => (ψ x).val)
        (fun x : (⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}) => x.val)
        (boundaryFaces P) (fun F G => IsExposed ℝ F G) C hfin
        (fun R hR => hψ ⟨R, (hsub hR).1⟩)
    obtain ⟨D', hD'fin, hD'sub, hD'closed, hD'avoid, hD'support, hD'mem⟩ :=
      boundary_subcomplex_restrict_antistar v D hDfin hDsub hDclosed
    refine ⟨D', hD'fin, hD'sub, hD'closed, hD'avoid, hD'support,
      fun h => (hKB h).elim, ?_⟩
    intro x
    exact (hfiber (ψ x)).trans ((hDmem x).trans (hD'mem x).symm)

end Grunbaum2003


-- Checked local ingredient: BoundaryCarrier

set_option autoImplicit false

namespace Grunbaum2003

private theorem proper_exposed_disjoint_interior {d : ℕ}
    {P F : Set (Fin d → ℝ)} (hF : IsExposed ℝ P F) (hFP : F ≠ P) :
    Disjoint F (interior P) := by
  apply Set.disjoint_left.mpr
  intro x hxF hxint
  obtain ⟨l, hl⟩ := hF ⟨x, hxF⟩
  by_cases hlzero : l = 0
  · apply hFP
    rw [hl, hlzero]
    ext y
    simp only [Set.mem_setOf_eq, ContinuousLinearMap.zero_apply, le_refl, implies_true,
      and_true]
  · have hxmax : ∀ y ∈ P, l y ≤ l x := by
      rw [hl] at hxF
      exact hxF.2
    have hSub : l '' interior P ⊆ Set.Iic (l x) := by
      rintro _ ⟨y, hy, rfl⟩
      exact hxmax y (interior_subset hy)
    have hopen : IsOpen (l '' interior P) := l.isOpenMap_of_ne_zero hlzero (interior P) isOpen_interior
    have hx : l x ∈ interior (Set.Iic (l x)) :=
      interior_maximal hSub hopen (Set.mem_image_of_mem l hxint)
    simpa only [interior_Iic, Set.mem_Iio, lt_self_iff_false] using hx

/-- The exposed-face boundary carrier of a closed convex body with nonempty
interior agrees with its topological frontier. -/
theorem boundary_carrier_eq_frontier_of_convex {d : ℕ}
    (P : Set (Fin d → ℝ)) (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hint : (interior P).Nonempty) :
    ⋃₀ boundaryFaces P = frontier P := by
  ext x
  rw [hclosed.frontier_eq]
  constructor
  · rintro ⟨F, ⟨hF, hFP⟩, hxF⟩
    exact ⟨hF.subset hxF, fun hx =>
      Set.disjoint_left.mp (proper_exposed_disjoint_interior hF hFP) hxF hx⟩
  · rintro ⟨hxP, hxint⟩
    obtain ⟨l, hlne, hlmax⟩ :=
      geometric_hahn_banach_of_nonempty_interior_point hconv hxint hint
    let F := l.toExposed P
    have hxF : x ∈ F := ⟨hxP, hlmax⟩
    have hFP : F ≠ P := by
      intro heq
      obtain ⟨y, hyint⟩ := hint
      have hyF : y ∈ F := by rw [heq]; exact interior_subset hyint
      have hSub : l '' interior P ⊆ Set.Iic (l y) := by
        rintro _ ⟨z, hz, rfl⟩
        exact hyF.2 z (interior_subset hz)
      have hopen : IsOpen (l '' interior P) := l.isOpenMap_of_ne_zero hlne (interior P) isOpen_interior
      have hy : l y ∈ interior (Set.Iic (l y)) :=
        interior_maximal hSub hopen (Set.mem_image_of_mem l hyint)
      simpa only [interior_Iic, Set.mem_Iio, lt_self_iff_false] using hy
    exact ⟨F, ⟨ContinuousLinearMap.toExposed.isExposed, hFP⟩, hxF⟩

theorem boundary_carrier_eq_frontier {d : ℕ}
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    ⋃₀ boundaryFaces P = frontier P := by
  obtain ⟨⟨V, hVfin, hVne, hPV⟩, hspan⟩ := hP
  have hc : Convex ℝ P := by rw [hPV]; exact convex_convexHull ℝ V
  have hcompact : IsCompact P := hPV ▸ hVfin.isCompact_convexHull ℝ
  apply boundary_carrier_eq_frontier_of_convex P hc hcompact.isClosed
  exact hc.interior_nonempty_iff_affineSpan_eq_top.mpr hspan

/-- This is the carrier part of boundary refinement. The additional requirement
that face preimages form subcomplexes is deliberately not asserted here. -/
theorem boundary_carriers_homeomorphic {d : ℕ}
    (P Q : Set (Fin d → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q) :
    Nonempty ((⋃₀ boundaryFaces P) ≃ₜ (⋃₀ boundaryFaces Q)) := by
  have props : ∀ R : Set (Fin d → ℝ), IsDPolytope R →
      Convex ℝ R ∧ (interior R).Nonempty ∧ Bornology.IsVonNBounded ℝ R := by
    rintro R ⟨⟨V, hVfin, hVne, hRV⟩, hspan⟩
    have hc : Convex ℝ R := by rw [hRV]; exact convex_convexHull ℝ V
    have hcomp : IsCompact R := hRV ▸ hVfin.isCompact_convexHull ℝ
    exact ⟨hc, hc.interior_nonempty_iff_affineSpan_eq_top.mpr hspan,
      NormedSpace.isVonNBounded_of_isBounded _ hcomp.isBounded⟩
  obtain ⟨hcP, hiP, hbP⟩ := props P hP
  obtain ⟨hcQ, hiQ, hbQ⟩ := props Q hQ
  obtain ⟨e, _, _, he⟩ := exists_homeomorph_image_eq hcP hiP hbP hcQ hiQ hbQ
  rw [boundary_carrier_eq_frontier P hP, boundary_carrier_eq_frontier Q hQ]
  exact ⟨(e.image (frontier P)).trans (Homeomorph.setCongr he)⟩

end Grunbaum2003


-- Checked local ingredient: RadialExtension

set_option autoImplicit false

noncomputable section

namespace Grunbaum2003
open Metric Set

variable {E : Type*} [NormedAddCommGroup E]

private def extendZero (g : ({0}ᶜ : Set E) ≃ₜ ({0}ᶜ : Set E)) (x : E) : E := by
  classical
  exact if hx : x = 0 then 0 else (g ⟨x, by simpa using hx⟩).val

private theorem extendZero_zero (g : ({0}ᶜ : Set E) ≃ₜ ({0}ᶜ : Set E)) :
    extendZero g 0 = 0 := by simp [extendZero]

private theorem extendZero_coe (g : ({0}ᶜ : Set E) ≃ₜ ({0}ᶜ : Set E))
    (x : ({0}ᶜ : Set E)) : extendZero g x.val = (g x).val := by
  have hx : x.val ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.property
  simp only [extendZero, dif_neg hx]

private theorem extendZero_inverse (g : ({0}ᶜ : Set E) ≃ₜ ({0}ᶜ : Set E)) (x : E) :
    extendZero g.symm (extendZero g x) = x := by
  by_cases hx : x = 0
  · subst x
    rw [extendZero_zero, extendZero_zero]
  · let y : ({0}ᶜ : Set E) := ⟨x, by simpa using hx⟩
    change extendZero g.symm (extendZero g y.val) = y.val
    rw [extendZero_coe, extendZero_coe]
    exact congrArg Subtype.val (g.symm_apply_apply y)

private theorem extendZero_norm (g : ({0}ᶜ : Set E) ≃ₜ ({0}ᶜ : Set E))
    (hnorm : ∀ x : ({0}ᶜ : Set E), ‖(g x).val‖ = ‖x.val‖) (x : E) :
    ‖extendZero g x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    rw [extendZero_zero]
  · exact (extendZero_coe g ⟨x, by simpa using hx⟩ ▸ hnorm ⟨x, by simpa using hx⟩)

private theorem extendZero_continuous (g : ({0}ᶜ : Set E) ≃ₜ ({0}ᶜ : Set E))
    (hnorm : ∀ x : ({0}ᶜ : Set E), ‖(g x).val‖ = ‖x.val‖) :
    Continuous (extendZero g) := by
  have hOn : ContinuousOn (extendZero g) ({0}ᶜ : Set E) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (({0}ᶜ : Set E).domRestrict (extendZero g)) = fun x => (g x).val := by
      funext x
      exact extendZero_coe g x
    rw [heq]
    exact continuous_subtype_val.comp g.continuous
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro y hy
    simpa only [extendZero_zero, dist_zero_right, extendZero_norm g hnorm] using hy
  · exact hOn.continuousAt (isOpen_compl_singleton.mem_nhds (by simpa using hx))

private def extendZeroHomeomorph (g : ({0}ᶜ : Set E) ≃ₜ ({0}ᶜ : Set E))
    (hnorm : ∀ x : ({0}ᶜ : Set E), ‖(g x).val‖ = ‖x.val‖) : E ≃ₜ E where
  toFun := extendZero g
  invFun := extendZero g.symm
  left_inv := extendZero_inverse g
  right_inv := extendZero_inverse g.symm
  continuous_toFun := extendZero_continuous g hnorm
  continuous_invFun := extendZero_continuous g.symm (by
    intro x
    have h := hnorm (g.symm x)
    simpa only [g.apply_symm_apply] using h.symm)

end Grunbaum2003

namespace Grunbaum2003
open Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def puncturedLift
    (h : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) :
    ({0}ᶜ : Set E) ≃ₜ ({0}ᶜ : Set E) :=
  (homeomorphUnitSphereProd E).trans
    ((h.prodCongr (Homeomorph.refl (Ioi (0 : ℝ)))).trans (homeomorphUnitSphereProd E).symm)

private theorem puncturedLift_norm
    (h : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) (x : ({0}ᶜ : Set E)) :
    ‖(puncturedLift h x).val‖ = ‖x.val‖ := by
  change ‖((homeomorphUnitSphereProd E).symm
    (h ((homeomorphUnitSphereProd E x).1), (homeomorphUnitSphereProd E x).2)).val‖ = ‖x.val‖
  have hn : ‖(h ((homeomorphUnitSphereProd E x).1)).val‖ = 1 :=
    mem_sphere_zero_iff_norm.mp (h ((homeomorphUnitSphereProd E x).1)).property
  rw [homeomorphUnitSphereProd_symm_apply_coe, norm_smul, hn, mul_one,
    homeomorphUnitSphereProd_apply_snd_coe, Real.norm_eq_abs, abs_norm]

omit [NormedSpace ℝ E] in
private theorem sphere_nonzero (x : sphere (0 : E) 1) : x.val ≠ 0 := by
  intro hx
  have hn := mem_sphere_zero_iff_norm.mp x.property
  rw [hx, norm_zero] at hn
  exact zero_ne_one hn

private theorem puncturedLift_sphere
    (h : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) (x : sphere (0 : E) 1) :
    (puncturedLift h ⟨x.val, by
      simpa only [mem_compl_iff, mem_singleton_iff] using sphere_nonzero x⟩).val = (h x).val := by
  let y : ({0}ᶜ : Set E) := ⟨x.val, by
    simpa only [mem_compl_iff, mem_singleton_iff] using sphere_nonzero x⟩
  have hn : ‖x.val‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  have hrad : homeomorphUnitSphereProd E y = (x, (⟨(1 : ℝ), (show (0 : ℝ) < (1 : ℝ) from zero_lt_one)⟩ : Ioi (0 : ℝ))) := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [homeomorphUnitSphereProd_apply_fst_coe, y, hn, inv_one, one_smul]
    · apply Subtype.ext
      simp only [homeomorphUnitSphereProd_apply_snd_coe, y, hn]
  change ((homeomorphUnitSphereProd E).symm
    (h ((homeomorphUnitSphereProd E y).1), (homeomorphUnitSphereProd E y).2)).val = (h x).val
  rw [hrad, homeomorphUnitSphereProd_symm_apply_coe, one_smul]

/-- A homeomorphism of the unit sphere extends radially over the closed unit
ball. This holds also for the zero-dimensional normed space. -/
theorem unitSphere_homeomorph_extends_closedBall
    (h : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) :
    ∃ H : closedBall (0 : E) 1 ≃ₜ closedBall (0 : E) 1,
      ∀ x : sphere (0 : E) 1,
        (H ⟨x.val, sphere_subset_closedBall x.property⟩).val = (h x).val := by
  let H0 : E ≃ₜ E := extendZeroHomeomorph (puncturedLift h) (puncturedLift_norm h)
  have hN : ∀ x : E, ‖H0 x‖ = ‖x‖ := extendZero_norm (puncturedLift h) (puncturedLift_norm h)
  let H : closedBall (0 : E) 1 ≃ₜ closedBall (0 : E) 1 :=
    H0.subtype (p := fun x : E => x ∈ closedBall (0 : E) 1)
      (q := fun x : E => x ∈ closedBall (0 : E) 1) (by
        intro x
        simp only [mem_closedBall_zero_iff, hN x])
  refine ⟨H, ?_⟩
  intro x
  change extendZero (puncturedLift h) x.val = (h x).val
  exact (extendZero_coe (puncturedLift h) ⟨x.val, by
    simpa only [mem_compl_iff, mem_singleton_iff] using sphere_nonzero x⟩).trans
      (puncturedLift_sphere h x)

end Grunbaum2003

end

-- Checked local ingredient: ConvexBodyExtension

set_option autoImplicit false

noncomputable section

namespace Grunbaum2003
open Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Any specified boundary homeomorphism between closed bounded convex bodies
with nonempty interior extends to a homeomorphism of the bodies. -/
theorem frontier_homeomorph_extends_convexBody
    {s t : Set E} (hs : IsClosed s) (ht : IsClosed t)
    (hsc : Convex ℝ s) (htc : Convex ℝ t)
    (hsne : (interior s).Nonempty) (htne : (interior t).Nonempty)
    (hsb : Bornology.IsBounded s) (htb : Bornology.IsBounded t)
    (h : frontier s ≃ₜ frontier t) :
    ∃ H : s ≃ₜ t, ∀ x : frontier s,
      (H ⟨x.val, hs.frontier_subset x.property⟩).val = (h x).val := by
  obtain ⟨a, _, haB, haS⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hsc hsne hsb
  obtain ⟨b, _, hbB, hbS⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall htc htne htb
  rw [hs.closure_eq] at haB
  rw [ht.closure_eq] at hbB
  let aB : s ≃ₜ closedBall (0 : E) 1 := (a.image s).trans (.setCongr haB)
  let bB : t ≃ₜ closedBall (0 : E) 1 := (b.image t).trans (.setCongr hbB)
  let aS : frontier s ≃ₜ sphere (0 : E) 1 :=
    (a.image (frontier s)).trans (.setCongr haS)
  let bS : frontier t ≃ₜ sphere (0 : E) 1 :=
    (b.image (frontier t)).trans (.setCongr hbS)
  let k : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1 := aS.symm.trans (h.trans bS)
  obtain ⟨K, hK⟩ := unitSphere_homeomorph_extends_closedBall k
  refine ⟨aB.trans (K.trans bB.symm), ?_⟩
  intro x
  have hAx : aB ⟨x.val, hs.frontier_subset x.property⟩ =
      ⟨(aS x).val, sphere_subset_closedBall (aS x).property⟩ := by
    apply Subtype.ext
    rfl
  have hKx := hK (aS x)
  have hOut : K (aB ⟨x.val, hs.frontier_subset x.property⟩) =
      bB ⟨(h x).val, ht.frontier_subset (h x).property⟩ := by
    rw [hAx]
    apply Subtype.ext
    exact hKx.trans (congrArg Subtype.val (show k (aS x) = bS (h x) from by
      change bS (h (aS.symm (aS x))) = bS (h x)
      rw [aS.symm_apply_apply]))
  change (bB.symm (K (aB ⟨x.val, hs.frontier_subset x.property⟩))).val = (h x).val
  rw [hOut, bB.symm_apply_apply]

end Grunbaum2003

end

-- Checked local ingredient: ExtensionBoundaryMembership

set_option autoImplicit false

namespace Grunbaum2003
open Set

/-- An extension of a bijective frontier map carries exactly the boundary points
to boundary points; this is the membership form needed for the cone construction. -/
theorem frontier_membership_iff_of_extension
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {s : Set E} {t : Set F} (hs : IsClosed s) (ht : IsClosed t)
    (h : frontier s ≃ₜ frontier t) (H : s ≃ₜ t)
    (hH : ∀ x : frontier s,
      (H ⟨x.val, hs.frontier_subset x.property⟩).val = (h x).val) :
    ∀ x : s, (H x).val ∈ frontier t ↔ x.val ∈ frontier s := by
  intro x
  constructor
  · intro hx
    let y : frontier t := ⟨(H x).val, hx⟩
    let z := h.symm y
    have hz : H ⟨z.val, hs.frontier_subset z.property⟩ = H x := by
      apply Subtype.ext
      exact (hH z).trans (congrArg Subtype.val (h.apply_symm_apply y))
    have hzx : z.val = x.val := congrArg Subtype.val (H.injective hz)
    exact hzx ▸ z.property
  · intro hx
    have hEq := hH ⟨x.val, hx⟩
    have hxEq : (⟨x.val, hs.frontier_subset hx⟩ : s) = x := Subtype.ext rfl
    rw [hxEq] at hEq
    rw [hEq]
    exact (h ⟨x.val, hx⟩).property

end Grunbaum2003


-- Checked local ingredient: InductionBody

set_option autoImplicit false

namespace Grunbaum2003
open Set

private theorem isDPolytope_body_properties {d : ℕ}
    {P : Set (Fin d → ℝ)} (hP : IsDPolytope P) :
    Convex ℝ P ∧ IsCompact P ∧ (interior P).Nonempty := by
  obtain ⟨⟨V, hVfin, hVne, hPV⟩, hspan⟩ := hP
  have hc : Convex ℝ P := by rw [hPV]; exact convex_convexHull ℝ V
  exact ⟨hc, hPV ▸ hVfin.isCompact_convexHull ℝ,
    hc.interior_nonempty_iff_affineSpan_eq_top.mpr hspan⟩

/-- A specified boundary refinement extends to the bodies, retaining its finite
subcomplex preimages for every point of the whole source body. -/
theorem boundary_refinement_homeomorph_extends_body {d : ℕ}
    {P Q : Set (Fin d → ℝ)} (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (ψ : (⋃₀ boundaryFaces P) ≃ₜ (⋃₀ boundaryFaces Q))
    (hψ : ∀ K ∈ boundaryFaces Q,
      ∃ C : Set (Set (Fin d → ℝ)), C.Finite ∧ C ⊆ boundaryFaces P ∧
        (∀ F ∈ C, ∀ G : Set (Fin d → ℝ), IsExposed ℝ F G → G ∈ C) ∧
        ∀ x : (⋃₀ boundaryFaces P), (ψ x).val ∈ K ↔ x.val ∈ ⋃₀ C) :
    ∃ H : P ≃ₜ Q,
      (∀ x : (⋃₀ boundaryFaces P),
        (H ⟨x.val, (by
          obtain ⟨F, hF, hxF⟩ := x.property
          exact hF.1.subset hxF)⟩).val =
          (ψ x).val) ∧
      (∀ x : P, (H x).val ∈ ⋃₀ boundaryFaces Q ↔ x.val ∈ ⋃₀ boundaryFaces P) ∧
      ∀ K ∈ boundaryFaces Q,
        ∃ C : Set (Set (Fin d → ℝ)), C.Finite ∧ C ⊆ boundaryFaces P ∧
          (∀ F ∈ C, ∀ G : Set (Fin d → ℝ), IsExposed ℝ F G → G ∈ C) ∧
          ∀ x : P, (H x).val ∈ K ↔ x.val ∈ ⋃₀ C := by
  obtain ⟨hcP, hcompP, hiP⟩ := isDPolytope_body_properties hP
  obtain ⟨hcQ, hcompQ, hiQ⟩ := isDPolytope_body_properties hQ
  have hBP := boundary_carrier_eq_frontier P hP
  have hBQ := boundary_carrier_eq_frontier Q hQ
  have hSubP : (⋃₀ boundaryFaces P) ⊆ P := by
    rw [hBP]
    exact hcompP.isClosed.frontier_subset
  let k : frontier P ≃ₜ frontier Q :=
    (Homeomorph.setCongr hBP.symm).trans (ψ.trans (Homeomorph.setCongr hBQ))
  obtain ⟨H, hH⟩ := frontier_homeomorph_extends_convexBody
    hcompP.isClosed hcompQ.isClosed hcP hcQ hiP hiQ hcompP.isBounded hcompQ.isBounded k
  have hAgree : ∀ x : (⋃₀ boundaryFaces P),
      (H ⟨x.val, hSubP x.property⟩).val = (ψ x).val := by
    intro x
    exact hH ⟨x.val, hBP ▸ x.property⟩
  have hBoundary : ∀ x : P,
      (H x).val ∈ ⋃₀ boundaryFaces Q ↔ x.val ∈ ⋃₀ boundaryFaces P := by
    intro x
    rw [hBQ, hBP]
    exact frontier_membership_iff_of_extension hcompP.isClosed hcompQ.isClosed k H hH x
  refine ⟨H, hAgree, hBoundary, ?_⟩
  intro K hK
  obtain ⟨C, hfin, hsub, hclosed, hfiber⟩ := hψ K hK
  refine ⟨C, hfin, hsub, hclosed, ?_⟩
  intro x
  by_cases hx : x.val ∈ ⋃₀ boundaryFaces P
  · have hEq := hAgree ⟨x.val, hx⟩
    have hxEq : (⟨x.val, hSubP hx⟩ : P) = x := Subtype.ext rfl
    rw [hxEq] at hEq
    rw [hEq]
    exact hfiber ⟨x.val, hx⟩
  · constructor
    · intro hxK
      exact (hx ((hBoundary x).mp ⟨K, hK, hxK⟩)).elim
    · rintro ⟨F, hFC, hxF⟩
      exact (hx ⟨F, hsub hFC, hxF⟩).elim

/-- The original inductive `BoundaryRefines` premise yields one body
homeomorphism whose proper-face preimages are finite source subcomplexes. -/
theorem BoundaryRefines.exists_body_homeomorph {d : ℕ}
    {P Q : Set (Fin d → ℝ)} (h : BoundaryRefines P Q)
    (hP : IsDPolytope P) (hQ : IsDPolytope Q) :
    ∃ H : P ≃ₜ Q,
      (∀ x : P, (H x).val ∈ ⋃₀ boundaryFaces Q ↔ x.val ∈ ⋃₀ boundaryFaces P) ∧
      ∀ K ∈ boundaryFaces Q,
        ∃ C : Set (Set (Fin d → ℝ)), C.Finite ∧ C ⊆ boundaryFaces P ∧
          (∀ F ∈ C, ∀ G : Set (Fin d → ℝ), IsExposed ℝ F G → G ∈ C) ∧
          ∀ x : P, (H x).val ∈ K ↔ x.val ∈ ⋃₀ C := by
  obtain ⟨ψ, hψ⟩ := h
  obtain ⟨H, hAgree, hBoundary, hFaces⟩ :=
    boundary_refinement_homeomorph_extends_body hP hQ ψ hψ
  exact ⟨H, hBoundary, hFaces⟩

end Grunbaum2003


-- Checked local ingredient: AffineTransport

set_option autoImplicit false

namespace Grunbaum2003

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Continuous affine equivalences preserve exposed faces, including the empty face. -/
theorem isExposed_image_continuousAffineEquiv (f : E ≃ᴬ[ℝ] F)
    {P S : Set E} (hS : IsExposed ℝ P S) : IsExposed ℝ (f '' P) (f '' S) := by
  intro hne
  have hSne : S.Nonempty := by
    obtain ⟨y, x, hx, rfl⟩ := hne
    exact ⟨x, hx⟩
  obtain ⟨l, hl⟩ := hS hSne
  let m : F →L[ℝ] ℝ := l.comp f.symm.toContinuousAffineMap.contLinear
  have hm : ∀ x : E, m (f x) = l x - l (f.symm 0) := by
    intro x
    have hf := f.symm.toContinuousAffineMap.contLinear_map_vsub (f x) (0 : F)
    change f.symm.toContinuousAffineMap.contLinear (f x - 0) = f.symm (f x) - f.symm 0 at hf
    have hf' : f.symm.toContinuousAffineMap.contLinear (f x) = x - f.symm 0 := by
      simpa only [sub_zero, f.symm_apply_apply] using hf
    change l (f.symm.toContinuousAffineMap.contLinear (f x)) = _
    rw [hf', map_sub]
  refine ⟨m, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ P ∧ ∀ z ∈ P, l z ≤ l x := by
      simpa only [hl, Set.mem_ofPred_eq] using hx
    refine ⟨⟨x, hx'.1, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [hm, hm]
    exact sub_le_sub_right (hx'.2 z hz) _
  · rintro ⟨⟨x, hx, rfl⟩, hmax⟩
    refine ⟨x, ?_, rfl⟩
    rw [hl]
    refine ⟨hx, ?_⟩
    intro z hz
    have ht := hmax (f z) ⟨z, hz, rfl⟩
    rw [hm, hm] at ht
    exact (sub_le_sub_iff_right _).mp ht

theorem isExposed_image_continuousAffineEquiv_iff (f : E ≃ᴬ[ℝ] F) (P S : Set E) :
    IsExposed ℝ (f '' P) (f '' S) ↔ IsExposed ℝ P S := by
  constructor
  · intro h
    have h' := isExposed_image_continuousAffineEquiv f.symm h
    have hP : f.symm '' (f '' P) = P := f.toEquiv.symm_image_image P
    have hS' : f.symm '' (f '' S) = S := f.toEquiv.symm_image_image S
    rw [hP, hS'] at h'
    exact h'
  · exact isExposed_image_continuousAffineEquiv f

theorem isExposed_image_affineEquiv [FiniteDimensional ℝ E] (f : E ≃ᵃ[ℝ] F)
    {P S : Set E} (hS : IsExposed ℝ P S) : IsExposed ℝ (f '' P) (f '' S) := by
  exact isExposed_image_continuousAffineEquiv (AffineEquiv.toContinuousAffineEquiv f) hS

end Grunbaum2003


-- Checked local ingredient: AffineEmbedding

set_option autoImplicit false

namespace Grunbaum2003

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- In finite-dimensional ambient space, an exposing functional can be extended
along any injective affine map. A linear left inverse supplies the extension. -/
theorem isExposed_image_affineMap_of_injective [FiniteDimensional ℝ F]
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f)
    {P S : Set E} (hS : IsExposed ℝ P S) : IsExposed ℝ (f '' P) (f '' S) := by
  intro hne
  have hSne : S.Nonempty := by
    obtain ⟨y, x, hx, rfl⟩ := hne
    exact ⟨x, hx⟩
  obtain ⟨l, hl⟩ := hS hSne
  have hlin : Function.Injective f.linear := f.linear_injective_iff.mpr hf
  obtain ⟨u, hu⟩ := f.linear.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hlin)
  have hu_apply : ∀ x : E, u (f.linear x) = x := by
    intro x
    exact congrArg (fun L : E →ₗ[ℝ] E => L x) hu
  let m : F →L[ℝ] ℝ := l.comp u.toContinuousLinearMap
  have hm : ∀ x : E, m (f x) = l x + l (u (f 0)) := by
    intro x
    have hfx : f x = f.linear x + f 0 := by
      simpa only [vadd_eq_add, add_zero] using f.map_vadd (0 : E) x
    change l (u (f x)) = _
    rw [hfx, map_add, hu_apply, map_add]
  refine ⟨m, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ P ∧ ∀ z ∈ P, l z ≤ l x := by
      simpa only [hl, Set.mem_ofPred_eq] using hx
    refine ⟨⟨x, hx'.1, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [hm, hm]
    exact add_le_add (hx'.2 z hz) le_rfl
  · rintro ⟨⟨x, hx, rfl⟩, hmax⟩
    refine ⟨x, ?_, rfl⟩
    rw [hl]
    refine ⟨hx, ?_⟩
    intro z hz
    have ht := hmax (f z) ⟨z, hz, rfl⟩
    rw [hm, hm] at ht
    exact (add_le_add_iff_right _).mp ht

/-- Pulling an exposed face back along an injective finite-dimensional affine
map preserves the original exposed-face predicate. -/
theorem isExposed_preimage_affineMap_of_injective [FiniteDimensional ℝ E]
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f)
    {P : Set E} {T : Set F} (hT : IsExposed ℝ (f '' P) T) :
    IsExposed ℝ P (f ⁻¹' T) := by
  intro hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨l, hl⟩ := hT ⟨f x, hx⟩
  let m : E →L[ℝ] ℝ := l.comp f.linear.toContinuousLinearMap
  have hm : ∀ x : E, m x = l (f x) - l (f 0) := by
    intro x
    have hv := f.linearMap_vsub x (0 : E)
    change f.linear (x - 0) = f x - f 0 at hv
    have hv' : f.linear x = f x - f 0 := by simpa only [sub_zero] using hv
    change l (f.linear x) = _
    rw [hv', map_sub]
  refine ⟨m, ?_⟩
  ext y
  constructor
  · intro hy
    change f y ∈ T at hy
    have hy' : f y ∈ f '' P ∧ ∀ z ∈ f '' P, l z ≤ l (f y) := by
      simpa only [hl, Set.mem_ofPred_eq] using hy
    refine ⟨hf.mem_set_image.mp hy'.1, ?_⟩
    intro z hz
    rw [hm, hm]
    exact sub_le_sub_right (hy'.2 (f z) ⟨z, hz, rfl⟩) _
  · rintro ⟨hy, hmax⟩
    change f y ∈ T
    rw [hl]
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have ht := hmax z hz
    rw [hm, hm] at ht
    exact (sub_le_sub_iff_right _).mp ht

theorem isExposed_image_affineMap_iff [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) (P S : Set E) :
    IsExposed ℝ (f '' P) (f '' S) ↔ IsExposed ℝ P S := by
  constructor
  · intro h
    have h' := isExposed_preimage_affineMap_of_injective f hf h
    rw [Set.preimage_image_eq S hf] at h'
    exact h'
  · exact isExposed_image_affineMap_of_injective f hf

end Grunbaum2003


-- Checked local ingredient: BoundaryTransport

set_option autoImplicit false

namespace Grunbaum2003

/-- Proper exposed boundary faces are transported exactly by an affine equivalence. -/
theorem boundaryFaces_image_continuousAffineEquiv {d e : ℕ}
    (f : (Fin d → ℝ) ≃ᴬ[ℝ] (Fin e → ℝ)) (P : Set (Fin d → ℝ)) :
    boundaryFaces (f '' P) = (Set.image f) '' boundaryFaces P := by
  ext G
  constructor
  · rintro ⟨hG, hneq⟩
    refine ⟨f.symm '' G, ⟨?_, ?_⟩, f.toEquiv.image_symm_image G⟩
    · have h := isExposed_image_continuousAffineEquiv f.symm hG
      have hP : f.symm '' (f '' P) = P := f.toEquiv.symm_image_image P
      rw [hP] at h
      exact h
    · intro heq
      apply hneq
      calc G = f '' (f.symm '' G) := (f.toEquiv.image_symm_image G).symm
        _ = f '' P := congrArg (Set.image f) heq
  · rintro ⟨S, ⟨hS, hne⟩, rfl⟩
    exact ⟨isExposed_image_continuousAffineEquiv f hS,
      fun heq => hne (f.injective.image_injective heq)⟩

theorem image_boundaryCarrier_continuousAffineEquiv {d e : ℕ}
    (f : (Fin d → ℝ) ≃ᴬ[ℝ] (Fin e → ℝ)) (P : Set (Fin d → ℝ)) :
    f '' (⋃₀ boundaryFaces P) = ⋃₀ boundaryFaces (f '' P) := by
  rw [Set.image_sUnion, boundaryFaces_image_continuousAffineEquiv f P]

/-- Source and target coordinates may be changed independently in a boundary refinement. -/
theorem BoundaryRefines.image_continuousAffineEquiv {d e : ℕ}
    {P Q : Set (Fin d → ℝ)} (h : BoundaryRefines P Q)
    (f g : (Fin d → ℝ) ≃ᴬ[ℝ] (Fin e → ℝ)) :
    BoundaryRefines (f '' P) (g '' Q) := by
  classical
  obtain ⟨ψ, hψ⟩ := h
  let Hf : (⋃₀ boundaryFaces P) ≃ₜ (⋃₀ boundaryFaces (f '' P)) :=
    f.toHomeomorph.subtype (p := fun x => x ∈ ⋃₀ boundaryFaces P)
      (q := fun x => x ∈ ⋃₀ boundaryFaces (f '' P)) (by
        intro x
        rw [← image_boundaryCarrier_continuousAffineEquiv f P]
        exact f.injective.mem_set_image.symm)
  let Hg : (⋃₀ boundaryFaces Q) ≃ₜ (⋃₀ boundaryFaces (g '' Q)) :=
    g.toHomeomorph.subtype (p := fun x => x ∈ ⋃₀ boundaryFaces Q)
      (q := fun x => x ∈ ⋃₀ boundaryFaces (g '' Q)) (by
        intro x
        rw [← image_boundaryCarrier_continuousAffineEquiv g Q]
        exact g.injective.mem_set_image.symm)
  refine ⟨Hf.symm.trans (ψ.trans Hg), ?_⟩
  intro K hK
  rw [boundaryFaces_image_continuousAffineEquiv g Q] at hK
  obtain ⟨K₀, hK₀, rfl⟩ := hK
  obtain ⟨C, hfin, hsub, hclosed, hfiber⟩ := hψ K₀ hK₀
  refine ⟨(Set.image f) '' C, hfin.image _, ?_, ?_, ?_⟩
  · rintro _ ⟨S, hS, rfl⟩
    rw [boundaryFaces_image_continuousAffineEquiv f P]
    exact ⟨S, hsub hS, rfl⟩
  · rintro _ ⟨S, hS, rfl⟩ T hT
    have hT' : IsExposed ℝ S (f.symm '' T) := by
      have h' := isExposed_image_continuousAffineEquiv f.symm hT
      have hInv : f.symm '' (f '' S) = S := f.toEquiv.symm_image_image S
      rw [hInv] at h'
      exact h'
    exact ⟨f.symm '' T, hclosed S hS _ hT', f.toEquiv.image_symm_image T⟩
  · intro x
    change g (ψ (Hf.symm x)).val ∈ g '' K₀ ↔ x.val ∈ ⋃₀ ((Set.image f) '' C)
    rw [g.injective.mem_set_image, ← Set.image_sUnion]
    have hx : f (Hf.symm x).val = x.val := f.apply_symm_apply x.val
    rw [← hx, f.injective.mem_set_image]
    exact hfiber (Hf.symm x)

theorem boundaryRefines_image_continuousAffineEquiv_iff {d e : ℕ}
    (f g : (Fin d → ℝ) ≃ᴬ[ℝ] (Fin e → ℝ)) (P Q : Set (Fin d → ℝ)) :
    BoundaryRefines (f '' P) (g '' Q) ↔ BoundaryRefines P Q := by
  constructor
  · intro h
    have h' := h.image_continuousAffineEquiv f.symm g.symm
    have hP : f.symm '' (f '' P) = P := f.toEquiv.symm_image_image P
    have hQ : g.symm '' (g '' Q) = Q := g.toEquiv.symm_image_image Q
    rw [hP, hQ] at h'
    exact h'
  · intro h
    exact h.image_continuousAffineEquiv f g

theorem boundaryRefines_image_affineEquiv_iff {d e : ℕ}
    (f g : (Fin d → ℝ) ≃ᵃ[ℝ] (Fin e → ℝ)) (P Q : Set (Fin d → ℝ)) :
    BoundaryRefines (f '' P) (g '' Q) ↔ BoundaryRefines P Q := by
  exact boundaryRefines_image_continuousAffineEquiv_iff
    (AffineEquiv.toContinuousAffineEquiv f) (AffineEquiv.toContinuousAffineEquiv g) P Q

end Grunbaum2003


-- Checked local ingredient: BoundaryEmbedding

set_option autoImplicit false

namespace Grunbaum2003

/-- An injective finite-dimensional affine map is a topological embedding. -/
theorem affineMap_isEmbedding_of_injective
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) : Topology.IsEmbedding f := by
  have hlin : Function.Injective f.linear := f.linear_injective_iff.mpr hf
  have hL : Topology.IsEmbedding f.linear :=
    (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hlin)).isEmbedding
  have hAdd : Topology.IsEmbedding (fun y : F => y + f 0) :=
    (Homeomorph.addRight (f 0)).isEmbedding
  have hEq : (fun x : E => f.linear x + f 0) = f := by
    funext x
    simpa only [vadd_eq_add, add_zero] using (f.map_vadd (0 : E) x).symm
  rw [← hEq]
  exact hAdd.comp hL

theorem boundaryFaces_image_affineMap {d e : ℕ}
    (f : (Fin d → ℝ) →ᵃ[ℝ] (Fin e → ℝ)) (hf : Function.Injective f)
    (P : Set (Fin d → ℝ)) :
    boundaryFaces (f '' P) = (Set.image f) '' boundaryFaces P := by
  ext G
  constructor
  · rintro ⟨hG, hneq⟩
    have hRange : G ⊆ Set.range f := by
      intro x hx
      obtain ⟨y, _, rfl⟩ := hG.subset hx
      exact Set.mem_range_self y
    have hImage : f '' (f ⁻¹' G) = G := Set.image_preimage_eq_of_subset hRange
    refine ⟨f ⁻¹' G, ⟨isExposed_preimage_affineMap_of_injective f hf hG, ?_⟩, hImage⟩
    intro heq
    apply hneq
    calc G = f '' (f ⁻¹' G) := hImage.symm
      _ = f '' P := congrArg (Set.image f) heq
  · rintro ⟨S, ⟨hS, hne⟩, rfl⟩
    exact ⟨isExposed_image_affineMap_of_injective f hf hS,
      fun heq => hne (hf.image_injective heq)⟩

theorem image_boundaryCarrier_affineMap {d e : ℕ}
    (f : (Fin d → ℝ) →ᵃ[ℝ] (Fin e → ℝ)) (hf : Function.Injective f)
    (P : Set (Fin d → ℝ)) :
    f '' (⋃₀ boundaryFaces P) = ⋃₀ boundaryFaces (f '' P) := by
  rw [Set.image_sUnion, boundaryFaces_image_affineMap f hf P]

/-- Refinements transport along injective affine coordinate embeddings, so an
inductive refinement in a hyperplane's coordinates also holds in the ambient space. -/
theorem BoundaryRefines.image_affineMap {d e : ℕ} {P Q : Set (Fin d → ℝ)}
    (h : BoundaryRefines P Q)
    (f g : (Fin d → ℝ) →ᵃ[ℝ] (Fin e → ℝ))
    (hf : Function.Injective f) (hg : Function.Injective g) :
    BoundaryRefines (f '' P) (g '' Q) := by
  classical
  obtain ⟨ψ, hψ⟩ := h
  let Hf : (⋃₀ boundaryFaces P) ≃ₜ (⋃₀ boundaryFaces (f '' P)) :=
    ((affineMap_isEmbedding_of_injective f hf).homeomorphImage (⋃₀ boundaryFaces P)).trans
      (Homeomorph.setCongr (image_boundaryCarrier_affineMap f hf P))
  let Hg : (⋃₀ boundaryFaces Q) ≃ₜ (⋃₀ boundaryFaces (g '' Q)) :=
    ((affineMap_isEmbedding_of_injective g hg).homeomorphImage (⋃₀ boundaryFaces Q)).trans
      (Homeomorph.setCongr (image_boundaryCarrier_affineMap g hg Q))
  refine ⟨Hf.symm.trans (ψ.trans Hg), ?_⟩
  intro K hK
  rw [boundaryFaces_image_affineMap g hg Q] at hK
  obtain ⟨K₀, hK₀, rfl⟩ := hK
  obtain ⟨C, hfin, hsub, hclosed, hfiber⟩ := hψ K₀ hK₀
  refine ⟨(Set.image f) '' C, hfin.image _, ?_, ?_, ?_⟩
  · rintro _ ⟨S, hS, rfl⟩
    rw [boundaryFaces_image_affineMap f hf P]
    exact ⟨S, hsub hS, rfl⟩
  · rintro _ ⟨S, hS, rfl⟩ T hT
    have hT' := isExposed_preimage_affineMap_of_injective f hf hT
    have hRange : T ⊆ Set.range f := by
      intro x hx
      obtain ⟨y, _, rfl⟩ := hT.subset hx
      exact Set.mem_range_self y
    exact ⟨f ⁻¹' T, hclosed S hS _ hT', Set.image_preimage_eq_of_subset hRange⟩
  · intro x
    change g (ψ (Hf.symm x)).val ∈ g '' K₀ ↔ x.val ∈ ⋃₀ ((Set.image f) '' C)
    rw [hg.mem_set_image, ← Set.image_sUnion]
    have hx : f (Hf.symm x).val = x.val := congrArg Subtype.val (Hf.apply_symm_apply x)
    rw [← hx, hf.mem_set_image]
    exact hfiber (Hf.symm x)

/-- The coordinate realization of a refinement in two affine subspaces gives
an ambient refinement. In particular this applies to vertex-figure coordinates. -/
theorem BoundaryRefines.image_affineSubspace_coordinates {n d : ℕ}
    {P Q : Set (Fin n → ℝ)} (h : BoundaryRefines P Q)
    (A B : AffineSubspace ℝ (Fin d → ℝ)) [Nonempty A] [Nonempty B]
    (eA : A ≃ᵃ[ℝ] (Fin n → ℝ)) (eB : B ≃ᵃ[ℝ] (Fin n → ℝ)) :
    BoundaryRefines
      ((fun x => ((eA.symm x : A) : Fin d → ℝ)) '' P)
      ((fun x => ((eB.symm x : B) : Fin d → ℝ)) '' Q) := by
  exact h.image_affineMap (A.subtype.comp eA.symm.toAffineMap)
    (B.subtype.comp eB.symm.toAffineMap)
    (A.subtype_injective.comp eA.symm.injective)
    (B.subtype_injective.comp eB.symm.injective)

end Grunbaum2003



-- Checked local ingredient: InductionBodyEmbedding

set_option autoImplicit false

namespace Grunbaum2003
open Set

/-- The body extension supplied by the inductive boundary refinement transports
through injective affine coordinate realizations, with the same finite-face
preimage property on every point of the realized source body. -/
theorem BoundaryRefines.exists_body_homeomorph_image_affineMap {d e : ℕ}
    {P Q : Set (Fin d → ℝ)} (h : BoundaryRefines P Q)
    (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (f g : (Fin d → ℝ) →ᵃ[ℝ] (Fin e → ℝ))
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ H : (f '' P) ≃ₜ (g '' Q),
      (∀ x : (f '' P), (H x).val ∈ ⋃₀ boundaryFaces (g '' Q) ↔
        x.val ∈ ⋃₀ boundaryFaces (f '' P)) ∧
      ∀ K ∈ boundaryFaces (g '' Q),
        ∃ C : Set (Set (Fin e → ℝ)), C.Finite ∧ C ⊆ boundaryFaces (f '' P) ∧
          (∀ F ∈ C, ∀ G : Set (Fin e → ℝ), IsExposed ℝ F G → G ∈ C) ∧
          ∀ x : (f '' P), (H x).val ∈ K ↔ x.val ∈ ⋃₀ C := by
  classical
  obtain ⟨H, hBoundary, hFaces⟩ := h.exists_body_homeomorph hP hQ
  let Hf : P ≃ₜ (f '' P) := (affineMap_isEmbedding_of_injective f hf).homeomorphImage P
  let Hg : Q ≃ₜ (g '' Q) := (affineMap_isEmbedding_of_injective g hg).homeomorphImage Q
  refine ⟨Hf.symm.trans (H.trans Hg), ?_, ?_⟩
  · intro x
    change g (H (Hf.symm x)).val ∈ ⋃₀ boundaryFaces (g '' Q) ↔
      x.val ∈ ⋃₀ boundaryFaces (f '' P)
    rw [← image_boundaryCarrier_affineMap g hg Q,
      ← image_boundaryCarrier_affineMap f hf P, hg.mem_set_image]
    have hx : f (Hf.symm x).val = x.val := congrArg Subtype.val (Hf.apply_symm_apply x)
    rw [← hx, hf.mem_set_image]
    exact hBoundary (Hf.symm x)
  · intro K hK
    rw [boundaryFaces_image_affineMap g hg Q] at hK
    obtain ⟨K₀, hK₀, rfl⟩ := hK
    obtain ⟨C, hfin, hsub, hclosed, hfiber⟩ := hFaces K₀ hK₀
    refine ⟨(Set.image f) '' C, hfin.image _, ?_, ?_, ?_⟩
    · rintro _ ⟨S, hS, rfl⟩
      rw [boundaryFaces_image_affineMap f hf P]
      exact ⟨S, hsub hS, rfl⟩
    · rintro _ ⟨S, hS, rfl⟩ T hT
      have hT' := isExposed_preimage_affineMap_of_injective f hf hT
      have hRange : T ⊆ Set.range f := by
        intro x hx
        obtain ⟨y, _, rfl⟩ := hT.subset hx
        exact Set.mem_range_self y
      exact ⟨f ⁻¹' T, hclosed S hS _ hT', Set.image_preimage_eq_of_subset hRange⟩
    · intro x
      change g (H (Hf.symm x)).val ∈ g '' K₀ ↔ x.val ∈ ⋃₀ ((Set.image f) '' C)
      rw [hg.mem_set_image, ← Set.image_sUnion]
      have hx : f (Hf.symm x).val = x.val := congrArg Subtype.val (Hf.apply_symm_apply x)
      rw [← hx, hf.mem_set_image]
      exact hfiber (Hf.symm x)

/-- Native inductive refinement yields the full-body refinement map inside the
ambient affine subspaces used for vertex figures. -/
theorem BoundaryRefines.exists_body_homeomorph_affineSubspace_coordinates {n d : ℕ}
    {P Q : Set (Fin n → ℝ)} (h : BoundaryRefines P Q)
    (hP : IsDPolytope P) (hQ : IsDPolytope Q)
    (A B : AffineSubspace ℝ (Fin d → ℝ)) [Nonempty A] [Nonempty B]
    (eA : A ≃ᵃ[ℝ] (Fin n → ℝ)) (eB : B ≃ᵃ[ℝ] (Fin n → ℝ)) :
    ∃ H : ((fun x => ((eA.symm x : A) : Fin d → ℝ)) '' P) ≃ₜ
        ((fun x => ((eB.symm x : B) : Fin d → ℝ)) '' Q),
      (∀ x, (H x).val ∈ ⋃₀ boundaryFaces
          ((fun y => ((eB.symm y : B) : Fin d → ℝ)) '' Q) ↔
        x.val ∈ ⋃₀ boundaryFaces ((fun y => ((eA.symm y : A) : Fin d → ℝ)) '' P)) ∧
      ∀ K ∈ boundaryFaces ((fun y => ((eB.symm y : B) : Fin d → ℝ)) '' Q),
        ∃ C : Set (Set (Fin d → ℝ)), C.Finite ∧
          C ⊆ boundaryFaces ((fun y => ((eA.symm y : A) : Fin d → ℝ)) '' P) ∧
          (∀ F ∈ C, ∀ G : Set (Fin d → ℝ), IsExposed ℝ F G → G ∈ C) ∧
          ∀ x, (H x).val ∈ K ↔ x.val ∈ ⋃₀ C := by
  exact h.exists_body_homeomorph_image_affineMap hP hQ
    (A.subtype.comp eA.symm.toAffineMap) (B.subtype.comp eB.symm.toAffineMap)
    (A.subtype_injective.comp eA.symm.injective)
    (B.subtype_injective.comp eB.symm.injective)

end Grunbaum2003


-- Checked local ingredient: OppositeFacetPreimages

set_option autoImplicit false

namespace Grunbaum2003
open Set

/-- The original native induction hypothesis, its coordinate realization, and
the actual radial antistar map give the opposite-facet preimage branch. One
fixed composite map supplies every target-base face preimage. -/
theorem opposite_facet_preimages_of_induction (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (v : Fin d → ℝ) (hv : IsExposed ℝ P {v})
    (W : Set (Fin d → ℝ)) (hW : W.Nonempty)
    (hPgen : P = convexHull ℝ (insert v W))
    (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α)
    {m : ℕ} {Q₀ B₀ : Set (Fin m → ℝ)}
    (hQ₀ : IsDPolytope Q₀) (hB₀ : IsDPolytope B₀) (hIH : BoundaryRefines Q₀ B₀)
    (f g : (Fin m → ℝ) →ᵃ[ℝ] (Fin d → ℝ))
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hCut : f '' Q₀ = P ∩ l ⁻¹' {α}) :
    ∃ ψ : (⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}) ≃ₜ
        ↥(P ∩ l ⁻¹' {α}),
      ∃ H : ↥(P ∩ l ⁻¹' {α}) ≃ₜ (g '' B₀),
        (∀ x, (ψ x).val = AffineMap.lineMap v x.val ((l v - α) / (l v - l x.val))) ∧
        (∀ x : ↥(P ∩ l ⁻¹' {α}),
          (H x).val ∈ ⋃₀ boundaryFaces (g '' B₀) ↔
            x.val ∈ ⋃₀ boundaryFaces (P ∩ l ⁻¹' {α})) ∧
        (∀ K ∈ boundaryFaces (g '' B₀),
          ∃ C : Set (Set (Fin d → ℝ)), C.Finite ∧
            C ⊆ boundaryFaces (P ∩ l ⁻¹' {α}) ∧
            (∀ F ∈ C, ∀ G : Set (Fin d → ℝ), IsExposed ℝ F G → G ∈ C) ∧
            ∀ x : ↥(P ∩ l ⁻¹' {α}), (H x).val ∈ K ↔ x.val ∈ ⋃₀ C) ∧
        ∀ K : PolytopeFace (g '' B₀),
          ∃ D : Set (Set (Fin d → ℝ)), D.Finite ∧ D ⊆ boundaryFaces P ∧
            (∀ F ∈ D, ∀ G : Set (Fin d → ℝ), IsExposed ℝ F G → G ∈ D) ∧
            (∀ F ∈ D, v ∉ F) ∧
            (⋃₀ D ⊆ ⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}) ∧
            (K.val = g '' B₀ → ⋃₀ D =
              ⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}) ∧
            ∀ x, (H (ψ x)).val ∈ K.val ↔ x.val ∈ ⋃₀ D := by
  obtain ⟨ψ, hψformula, hψ⟩ := antistar_radial_refinement_data
    d P hP v hv W hW hPgen l α hα hBelow
  obtain ⟨H₀, hBoundary, hH₀⟩ :=
    hIH.exists_body_homeomorph_image_affineMap hQ₀ hB₀ f g hf hg
  let J : ↥(P ∩ l ⁻¹' {α}) ≃ₜ (f '' Q₀) := Homeomorph.setCongr hCut.symm
  let H : ↥(P ∩ l ⁻¹' {α}) ≃ₜ (g '' B₀) := J.trans H₀
  have hBoundary' : ∀ x : ↥(P ∩ l ⁻¹' {α}),
      (H x).val ∈ ⋃₀ boundaryFaces (g '' B₀) ↔
        x.val ∈ ⋃₀ boundaryFaces (P ∩ l ⁻¹' {α}) := by
    intro x
    change (H₀ (J x)).val ∈ ⋃₀ boundaryFaces (g '' B₀) ↔
      x.val ∈ ⋃₀ boundaryFaces (P ∩ l ⁻¹' {α})
    apply (hBoundary (J x)).trans
    change x.val ∈ ⋃₀ boundaryFaces (f '' Q₀) ↔
      x.val ∈ ⋃₀ boundaryFaces (P ∩ l ⁻¹' {α})
    rw [hCut]
  have hH : ∀ K ∈ boundaryFaces (g '' B₀),
      ∃ C : Set (Set (Fin d → ℝ)), C.Finite ∧ C ⊆ boundaryFaces (P ∩ l ⁻¹' {α}) ∧
        (∀ F ∈ C, ∀ G : Set (Fin d → ℝ), IsExposed ℝ F G → G ∈ C) ∧
        ∀ x : ↥(P ∩ l ⁻¹' {α}), (H x).val ∈ K ↔ x.val ∈ ⋃₀ C := by
    intro K hK
    obtain ⟨C, hfin, hsub, hclosed, hfiber⟩ := hH₀ K hK
    refine ⟨C, hfin, ?_, hclosed, ?_⟩
    · simpa only [hCut] using hsub
    · intro x
      exact hfiber (J x)
  exact ⟨ψ, H, hψformula, hBoundary', hH, antistar_body_composite_face_preimages v ψ hψ H hH⟩

end Grunbaum2003


-- Checked local ingredient: VertexFigureBodyBridge

set_option autoImplicit false

namespace Grunbaum2003

/-- A fixed body refinement map into a target simplex's opposite facet gives a map to its
vertex figure by the recorded radial antistar map. An injective affine realization of that
radial map transports both the carrier and every proper-face preimage, keeping the same body
map and its exact antistar endpoint. This lemma does not choose a second body extension. -/
theorem antistar_body_to_vertexFigure_map {d d' : ℕ}
    (P' : Set (Fin d' → ℝ)) (v' : Fin d' → ℝ)
    (Q : Set (Fin d → ℝ)) (B Q' : Set (Fin d' → ℝ))
    (ψ' : (⋃₀ {S : Set (Fin d' → ℝ) | IsExposed ℝ P' S ∧ v' ∉ S}) ≃ₜ Q')
    (hBA : B = ⋃₀ {S : Set (Fin d' → ℝ) | IsExposed ℝ P' S ∧ v' ∉ S})
    (F : Q ≃ₜ B)
    (hFBoundary : ∀ q, (F q).val ∈ ⋃₀ boundaryFaces B ↔ q.val ∈ ⋃₀ boundaryFaces Q)
    (hFFaces : ∀ K ∈ boundaryFaces B,
      ∃ C : Set (Set (Fin d → ℝ)), C.Finite ∧ C ⊆ boundaryFaces Q ∧
        (∀ S ∈ C, ∀ T : Set (Fin d → ℝ), IsExposed ℝ S T → T ∈ C) ∧
        ∀ q : Q, (F q).val ∈ K ↔ q.val ∈ ⋃₀ C)
    (r : (Fin d' → ℝ) →ᵃ[ℝ] (Fin d' → ℝ)) (hr : Function.Injective r)
    (hrImage : r '' B = Q')
    (hrRadial : ∀ b : B, r b.val = (ψ' ((Homeomorph.setCongr hBA) b)).val) :
    ∃ k : Q ≃ₜ Q',
      (∀ q, (k q).val ∈ ⋃₀ boundaryFaces Q' ↔ q.val ∈ ⋃₀ boundaryFaces Q) ∧
      (∀ q, (ψ'.symm (k q)).val = (F q).val) ∧
      (∀ q, (k q).val = r (F q).val) ∧
      ∀ K ∈ boundaryFaces Q',
        ∃ C : Set (Set (Fin d → ℝ)), C.Finite ∧ C ⊆ boundaryFaces Q ∧
          (∀ S ∈ C, ∀ T : Set (Fin d → ℝ), IsExposed ℝ S T → T ∈ C) ∧
          ∀ q : Q, (k q).val ∈ K ↔ q.val ∈ ⋃₀ C := by
  let J : B ≃ₜ (⋃₀ {S : Set (Fin d' → ℝ) | IsExposed ℝ P' S ∧ v' ∉ S}) :=
    Homeomorph.setCongr hBA
  let k : Q ≃ₜ Q' := F.trans (J.trans ψ')
  have hkFormula (q : Q) : (k q).val = r (F q).val := (hrRadial (F q)).symm
  refine ⟨k, ?_, ?_, hkFormula, ?_⟩
  · intro q
    rw [hkFormula q, ← hrImage, ← image_boundaryCarrier_affineMap r hr B, hr.mem_set_image]
    exact hFBoundary q
  · intro q
    change (ψ'.symm (ψ' (J (F q)))).val = (F q).val
    rw [ψ'.symm_apply_apply]
    rfl
  · intro K hK
    rw [← hrImage, boundaryFaces_image_affineMap r hr B] at hK
    obtain ⟨K₀, hK₀, rfl⟩ := hK
    obtain ⟨C, hfin, hsub, hclosed, hfiber⟩ := hFFaces K₀ hK₀
    refine ⟨C, hfin, hsub, hclosed, ?_⟩
    intro q
    rw [hkFormula q, hr.mem_set_image]
    exact hfiber q

end Grunbaum2003


-- Checked local ingredient: ConeFaceMembership

set_option autoImplicit false

namespace Grunbaum2003

/-- Membership on a closed cone segment when its apex belongs to the face. -/
theorem lineMap_mem_exposed_iff_of_left_mem {d : ℕ}
    {T K : Set (Fin d → ℝ)} (hT : Convex ℝ T) (hK : IsExposed ℝ T K)
    {a b : Fin d → ℝ} (ha : a ∈ K) (hb : b ∈ T)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    AffineMap.lineMap a b t ∈ K ↔ t = 0 ∨ b ∈ K := by
  constructor
  · intro hx
    by_cases hzero : t = 0
    · exact Or.inl hzero
    · apply Or.inr
      by_cases hone : t = 1
      · simpa only [hone, AffineMap.lineMap_apply_one] using hx
      · exact (lineMap_mem_face_iff hT hK ha hb
          ⟨lt_of_le_of_ne ht₀ (Ne.symm hzero), lt_of_le_of_ne ht₁ hone⟩).mp hx
  · rintro (hzero | hbK)
    · simpa only [hzero, AffineMap.lineMap_apply_zero] using ha
    · exact (hK.convex hT).lineMap_mem ha hbK ⟨ht₀, ht₁⟩

/-- A segment from outside an exposed face reaches it only at the other end. -/
theorem lineMap_mem_exposed_iff_of_left_not_mem {d : ℕ}
    {T K : Set (Fin d → ℝ)} (hK : IsExposed ℝ T K)
    {a b : Fin d → ℝ} (haT : a ∈ T) (ha : a ∉ K) (hb : b ∈ T)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    AffineMap.lineMap a b t ∈ K ↔ t = 1 ∧ b ∈ K := by
  constructor
  · intro hx
    by_cases hone : t = 1
    · exact ⟨hone, by simpa only [hone, AffineMap.lineMap_apply_one] using hx⟩
    · exfalso
      by_cases hzero : t = 0
      · apply ha
        simpa only [hzero, AffineMap.lineMap_apply_zero] using hx
      · apply ha
        exact hK.isExtreme.left_mem_of_mem_openSegment haT hb hx
          (lineMap_mem_openSegment ℝ a b
            ⟨lt_of_le_of_ne ht₀ (Ne.symm hzero), lt_of_le_of_ne ht₁ hone⟩)
  · rintro ⟨hone, hbK⟩
    simpa only [hone, AffineMap.lineMap_apply_one] using hbK

/-- A union of exposed faces avoiding the apex has the endpoint-only formula. -/
theorem lineMap_mem_sUnion_iff_of_left_not_mem {d : ℕ}
    {P : Set (Fin d → ℝ)} (D : Set (Set (Fin d → ℝ))) (v : Fin d → ℝ)
    (hD : ∀ F ∈ D, IsExposed ℝ P F ∧ v ∉ F)
    {y : Fin d → ℝ} (hvP : v ∈ P) (hyP : y ∈ P)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    AffineMap.lineMap v y t ∈ ⋃₀ D ↔ t = 1 ∧ y ∈ ⋃₀ D := by
  constructor
  · rintro ⟨F, hFD, hxF⟩
    obtain ⟨hone, hyF⟩ :=
      (lineMap_mem_exposed_iff_of_left_not_mem (hD F hFD).1 hvP (hD F hFD).2 hyP ht₀ ht₁).mp hxF
    exact ⟨hone, F, hFD, hyF⟩
  · rintro ⟨hone, hy⟩
    simpa only [hone, AffineMap.lineMap_apply_one] using hy

end Grunbaum2003


-- Checked local ingredient: BoundaryRefinesOfCone

set_option autoImplicit false

namespace Grunbaum2003

/-- The two face-preimage branches of the cone induction, using one fixed
body map and one fixed induced boundary map throughout. The target base is
an actual exposed antistar whose cone is the whole target. -/
theorem boundaryRefines_of_cone_face_data (d : ℕ) (hd : 0 < d)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (v : Fin d → ℝ) (hv : IsExposed ℝ P {v})
    (W : Set (Fin d → ℝ)) (hW : W.Nonempty)
    (hPgen : P = convexHull ℝ (insert v W))
    (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α)
    (T B : Set (Fin d → ℝ)) (a : Fin d → ℝ)
    (hT : Convex ℝ T) (haT : a ∈ T)
    (hB : IsExposed ℝ T B)
    (hTB : T = convexHull ℝ (insert a B))
    (hAnti : (⋃₀ {K : Set (Fin d → ℝ) | IsExposed ℝ T K ∧ a ∉ K}) = B)
    (ψ : (⋃₀ {F : Set (Fin d → ℝ) | IsExposed ℝ P F ∧ v ∉ F}) ≃ₜ ↥(P ∩ l ⁻¹' {α}))
    (hψ : ∀ y, (ψ y).val = AffineMap.lineMap v y.val ((l v - α) / (l v - l y.val)))
    (F : ↥(P ∩ l ⁻¹' {α}) ≃ₜ B)
    (hF : ∀ K ∈ boundaryFaces B,
      ∃ C : Set (Set (Fin d → ℝ)), C.Finite ∧ C ⊆ boundaryFaces (P ∩ l ⁻¹' {α}) ∧
        (∀ R ∈ C, ∀ S : Set (Fin d → ℝ), IsExposed ℝ R S → S ∈ C) ∧
        ∀ q : ↥(P ∩ l ⁻¹' {α}), (F q).val ∈ K ↔ q.val ∈ ⋃₀ C)
    (hOpposite : ∀ K : PolytopeFace B,
      ∃ D : Set (Set (Fin d → ℝ)), D.Finite ∧ D ⊆ boundaryFaces P ∧
        (∀ R ∈ D, ∀ S : Set (Fin d → ℝ), IsExposed ℝ R S → S ∈ D) ∧
        (∀ R ∈ D, v ∉ R) ∧
        ∀ y, (F (ψ y)).val ∈ K.val ↔ y.val ∈ ⋃₀ D)
    (H : P ≃ₜ T)
    (hH : ∀ y (t : Set.Icc (0 : ℝ) 1) (x : P),
      x.val = AffineMap.lineMap v y.val t.val →
        (H x).val = AffineMap.lineMap a (F (ψ y)).val t.val)
    (Ψ : (⋃₀ boundaryFaces P) ≃ₜ (⋃₀ boundaryFaces T))
    (hΨ : ∀ b (x : P), x.val = b.val → (Ψ b).val = (H x).val) :
    BoundaryRefines P T := by
  classical
  let A := ⋃₀ {R : Set (Fin d → ℝ) | IsExposed ℝ P R ∧ v ∉ R}
  have hvP : v ∈ P := hv.subset (Set.mem_singleton v)
  have hAP : A ⊆ P := by
    rintro x ⟨R, hR, hxR⟩
    exact hR.1.subset hxR
  have hBelowV (w : Fin d → ℝ) (hw : IsExposed ℝ P {w}) (hwv : w ≠ v) : l w < α := by
    have hwExt := exposedPoints_subset_extremePoints (mem_exposedPoints_iff_exposed_singleton.mpr hw)
    rw [hPgen] at hwExt
    exact hBelow w ((Set.mem_insert_iff.mp (extremePoints_convexHull_subset hwExt)).resolve_left hwv)
  obtain ⟨f, hf, _, hSurj, _, _⟩ := antistar_cone_quotient d hd P hP v hvP l α hα hBelowV
  have hCoordinates (b : ⋃₀ boundaryFaces P) :
      ∃ (y : A) (t : Set.Icc (0 : ℝ) 1),
        b.val = AffineMap.lineMap v y.val t.val ∧
        (Ψ b).val = AffineMap.lineMap a (F (ψ y)).val t.val := by
    have hbP : b.val ∈ P := by
      obtain ⟨R, hR, hbR⟩ := b.property
      exact hR.1.subset hbR
    let x : P := ⟨b.val, hbP⟩
    obtain ⟨z, hz⟩ := hSurj x
    have hx : x.val = AffineMap.lineMap v z.1.val z.2.val :=
      (congrArg Subtype.val hz).symm.trans (hf z)
    refine ⟨z.1, z.2, hx, ?_⟩
    exact (hΨ b x rfl).trans (hH z.1 z.2 x hx)
  refine ⟨Ψ, ?_⟩
  intro K hK
  by_cases haK : a ∈ K
  · have hJ : K ∩ B ∈ boundaryFaces B := by
      refine ⟨(hK.1.inter hB).mono hB.subset Set.inter_subset_right, ?_⟩
      intro hJB
      have hBK : B ⊆ K := Set.inter_eq_right.mp hJB
      have hTK : T ⊆ K := by
        rw [hTB]
        apply convexHull_min ?_ (hK.1.convex hT)
        rintro x (rfl | hx)
        · exact haK
        · exact hBK hx
      exact hK.2 (Set.Subset.antisymm hK.1.subset hTK)
    obtain ⟨C, _, hCsub, _, hCmem⟩ := hF (K ∩ B) hJ
    obtain ⟨D, hDfin, hDsub, hDclosed, hDmem⟩ :=
      lifted_vertexFigure_subcomplex d P hP v hv W hW hPgen l α hα hBelow ψ hψ C hCsub
    refine ⟨D, hDfin, hDsub, hDclosed, ?_⟩
    intro b
    obtain ⟨y, t, hx, hfx⟩ := hCoordinates b
    rw [hfx, hx,
      lineMap_mem_exposed_iff_of_left_mem hT hK.1 haK (hB.subset (F (ψ y)).property)
        t.property.1 t.property.2,
      hDmem y t.val t.property.1 t.property.2]
    apply or_congr Iff.rfl
    have hInBase : (F (ψ y)).val ∈ K ↔ (F (ψ y)).val ∈ K ∩ B :=
      ⟨fun h => ⟨h, (F (ψ y)).property⟩, fun h => h.1⟩
    exact hInBase.trans (hCmem (ψ y))
  · have hKB : K ⊆ B := by
      intro x hxK
      rw [← hAnti]
      exact ⟨K, ⟨hK.1, haK⟩, hxK⟩
    have hKbase : IsExposed ℝ B K := hK.1.mono hB.subset hKB
    obtain ⟨D, hDfin, hDsub, hDclosed, hDavoid, hDmem⟩ := hOpposite ⟨K, hKbase⟩
    refine ⟨D, hDfin, hDsub, hDclosed, ?_⟩
    intro b
    obtain ⟨y, t, hx, hfx⟩ := hCoordinates b
    rw [hfx, hx,
      lineMap_mem_exposed_iff_of_left_not_mem hK.1 haT haK
        (hB.subset (F (ψ y)).property) t.property.1 t.property.2,
      lineMap_mem_sUnion_iff_of_left_not_mem D v
        (fun R hR => ⟨(hDsub hR).1, hDavoid R hR⟩) hvP (hAP y.property)
        t.property.1 t.property.2]
    exact and_congr Iff.rfl (hDmem y)

end Grunbaum2003


-- Checked local ingredient: BoundaryInductionStep

set_option autoImplicit false

namespace Grunbaum2003
open Set

/-- The conditional geometric induction step: native lower-dimensional boundary
refinement, source coordinates, and actual target simplex cut data give the
original ambient boundary refinement. Every branch uses one fixed body map. -/
theorem boundaryRefines_of_native_induction_cut_data
    (d : ℕ) (hd : 0 < d)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (v : Fin d → ℝ) (hv : IsExposed ℝ P {v})
    (W : Set (Fin d → ℝ)) (hW : W.Nonempty)
    (hPgen : P = convexHull ℝ (insert v W))
    (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ)
    (hα : α < l v) (hBelow : ∀ w ∈ W, l w < α)
    {m : ℕ} {Q₀ B₀ : Set (Fin m → ℝ)}
    (hQ₀ : IsDPolytope Q₀) (hB₀ : IsDPolytope B₀) (hIH : BoundaryRefines Q₀ B₀)
    (f g : (Fin m → ℝ) →ᵃ[ℝ] (Fin d → ℝ))
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hCut : f '' Q₀ = P ∩ l ⁻¹' {α})
    (T : Set (Fin d → ℝ)) (hT : IsDPolytope T)
    (a : Fin d → ℝ) (ha : IsExposed ℝ T {a})
    (W' : Set (Fin d → ℝ)) (hW' : W'.Nonempty)
    (hTgen : T = convexHull ℝ (insert a W'))
    (l' : StrongDual ℝ (Fin d → ℝ)) (α' : ℝ)
    (hα' : α' < l' a) (hBelow' : ∀ w ∈ W', l' w < α')
    (B : Set (Fin d → ℝ)) (hB : IsExposed ℝ T B)
    (hTB : T = convexHull ℝ (insert a B))
    (hAnti : (⋃₀ {K : Set (Fin d → ℝ) | IsExposed ℝ T K ∧ a ∉ K}) = B)
    (hBase : g '' B₀ = B)
    (r : (Fin d → ℝ) →ᵃ[ℝ] (Fin d → ℝ)) (hr : Function.Injective r)
    (hrImage : r '' B = T ∩ l' ⁻¹' {α'})
    (hRadial : ∀ b ∈ B,
      AffineMap.lineMap a b ((l' a - α') / (l' a - l' b)) = r b) :
    BoundaryRefines P T := by
  obtain ⟨ψ, F₀, hψ, hF₀Boundary, hF₀Faces, hF₀Opposite⟩ :=
    opposite_facet_preimages_of_induction d P hP v hv W hW hPgen l α hα hBelow
      hQ₀ hB₀ hIH f g hf hg hCut
  let J : (g '' B₀) ≃ₜ B := Homeomorph.setCongr hBase
  let F : ↥(P ∩ l ⁻¹' {α}) ≃ₜ B := F₀.trans J
  have hBaseCarrier : ⋃₀ boundaryFaces (g '' B₀) = ⋃₀ boundaryFaces B :=
    congrArg (fun R : Set (Fin d → ℝ) => ⋃₀ boundaryFaces R) hBase
  have hFBoundary : ∀ q, (F q).val ∈ ⋃₀ boundaryFaces B ↔
      q.val ∈ ⋃₀ boundaryFaces (P ∩ l ⁻¹' {α}) := by
    intro q
    change (F₀ q).val ∈ ⋃₀ boundaryFaces B ↔ _
    rw [← hBaseCarrier]
    exact hF₀Boundary q
  have hFFaces : ∀ K ∈ boundaryFaces B,
      ∃ C : Set (Set (Fin d → ℝ)), C.Finite ∧ C ⊆ boundaryFaces (P ∩ l ⁻¹' {α}) ∧
        (∀ R ∈ C, ∀ S : Set (Fin d → ℝ), IsExposed ℝ R S → S ∈ C) ∧
        ∀ q : ↥(P ∩ l ⁻¹' {α}), (F q).val ∈ K ↔ q.val ∈ ⋃₀ C := by
    intro K hK
    have hK₀ : K ∈ boundaryFaces (g '' B₀) := by rwa [hBase]
    obtain ⟨C, hfin, hsub, hclosed, hfiber⟩ := hF₀Faces K hK₀
    exact ⟨C, hfin, hsub, hclosed, hfiber⟩
  have hOpposite : ∀ K : PolytopeFace B,
      ∃ D : Set (Set (Fin d → ℝ)), D.Finite ∧ D ⊆ boundaryFaces P ∧
        (∀ R ∈ D, ∀ S : Set (Fin d → ℝ), IsExposed ℝ R S → S ∈ D) ∧
        (∀ R ∈ D, v ∉ R) ∧
        ∀ y, (F (ψ y)).val ∈ K.val ↔ y.val ∈ ⋃₀ D := by
    intro K
    have hK₀ : IsExposed ℝ (g '' B₀) K.val := by simpa only [hBase] using K.property
    obtain ⟨D, hfin, hsub, hclosed, havoid, hsupport, hwhole, hfiber⟩ :=
      hF₀Opposite ⟨K.val, hK₀⟩
    exact ⟨D, hfin, hsub, hclosed, havoid, hfiber⟩
  obtain ⟨ψ', hψ', _⟩ :=
    antistar_radial_refinement_data d T hT a ha W' hW' hTgen l' α' hα' hBelow'
  have hrRadial : ∀ b : B,
      r b.val = (ψ' ((Homeomorph.setCongr hAnti.symm) b)).val := by
    intro b
    rw [hψ']
    change r b.val = AffineMap.lineMap a b.val ((l' a - α') / (l' a - l' b.val))
    exact (hRadial b.val b.property).symm
  obtain ⟨k, hkCarrier, hkEndpoint, hkFormula, hkFaces⟩ :=
    antistar_body_to_vertexFigure_map T a (P ∩ l ⁻¹' {α}) B
      (T ∩ l' ⁻¹' {α'}) ψ' hAnti.symm F hFBoundary hFFaces r hr hrImage hrRadial
  obtain ⟨H, hH, hHCarrier, Ψ, hΨ⟩ := global_cone_boundary_homeomorph
    d d hd hd P hP T hT v hv a ha W hW hPgen W' hW' hTgen
      l α hα hBelow l' α' hα' hBelow' ψ hψ ψ' hψ' k hkCarrier
  have hHFormula : ∀ y (t : Set.Icc (0 : ℝ) 1) (x : P),
      x.val = AffineMap.lineMap v y.val t.val →
        (H x).val = AffineMap.lineMap a (F (ψ y)).val t.val := by
    intro y t x hx
    have h := hH y t x hx
    rw [hkEndpoint (ψ y)] at h
    exact h
  have hTconv : Convex ℝ T := by rw [hTgen]; exact convex_convexHull ℝ _
  have haT : a ∈ T := ha.subset (Set.mem_singleton a)
  exact boundaryRefines_of_cone_face_data d hd P hP v hv W hW hPgen l α hα hBelow
    T B a hTconv haT hB hTB hAnti ψ hψ F hFFaces hOpposite H hHFormula Ψ hΨ

end Grunbaum2003


-- Checked local ingredient: ZeroBoundaryBase

set_option autoImplicit false

namespace Grunbaum2003

theorem eq_singleton_zero_of_nonempty_fin_zero {S : Set (Fin 0 → ℝ)} (hS : S.Nonempty) :
    S = {0} := by
  rcases hS with ⟨x, hx⟩
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · intro _
    exact Subsingleton.elim y 0
  · rintro rfl
    have hxz : x = 0 := Subsingleton.elim x 0
    rwa [← hxz]

theorem sUnion_boundaryFaces_eq_empty_of_eq_singleton_zero {S : Set (Fin 0 → ℝ)}
    (hS : S = {0}) : ⋃₀ boundaryFaces S = ∅ := by
  ext x
  simp only [Set.mem_sUnion, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
  intro F hF hxF
  rcases hF with ⟨hFe, hFneS⟩
  have hsub : F ⊆ {0} := hS ▸ hFe.subset
  have hx0 : x = 0 := Subsingleton.elim x 0
  subst hx0
  have hFeq : F = {0} := Set.Subset.antisymm hsub (Set.singleton_subset_iff.mpr hxF)
  exact hFneS (hFeq.trans hS.symm)

/-- Grünbaum (2003), §11.1 (Theorem 11.1.1, p. 200): in dimension `d = 0`, the boundary
complex of every `0`-polytope `P` refines the boundary complex of every `0`-simplex
(both having the empty carrier and sole boundary face `∅`). -/
theorem boundary_refines_simplex_zero_dim
    (P : Set (Fin 0 → ℝ)) (hP : IsDPolytope P)
    (v : Fin 1 → (Fin 0 → ℝ)) (_hv : AffineIndependent ℝ v) :
    BoundaryRefines P (convexHull ℝ (Set.range v)) := by
  obtain ⟨⟨Vset, _, hVne, hPhull⟩, _⟩ := hP
  have hPne : P.Nonempty := by
    rw [hPhull]
    exact hVne.convexHull
  have hQne : (convexHull ℝ (Set.range v)).Nonempty :=
    (Set.range_nonempty v).convexHull
  have hP0 : P = {0} := eq_singleton_zero_of_nonempty_fin_zero hPne
  have hQ0 : convexHull ℝ (Set.range v) = {0} := eq_singleton_zero_of_nonempty_fin_zero hQne
  have hPB : ⋃₀ boundaryFaces P = ∅ := sUnion_boundaryFaces_eq_empty_of_eq_singleton_zero hP0
  have hQB : ⋃₀ boundaryFaces (convexHull ℝ (Set.range v)) = ∅ :=
    sUnion_boundaryFaces_eq_empty_of_eq_singleton_zero hQ0
  haveI : IsEmpty (⋃₀ boundaryFaces P) := by
    rw [hPB]; infer_instance
  haveI : IsEmpty (⋃₀ boundaryFaces (convexHull ℝ (Set.range v))) := by
    rw [hQB]; infer_instance
  let e : (⋃₀ boundaryFaces P) ≃ (⋃₀ boundaryFaces (convexHull ℝ (Set.range v))) :=
    Equiv.equivOfIsEmpty _ _
  refine ⟨{
    toEquiv := e
    continuous_toFun := continuous_of_discreteTopology
    continuous_invFun := continuous_of_discreteTopology
  }, ?_⟩
  intro K _
  refine ⟨{∅}, Set.finite_singleton ∅, ?_, ?_, ?_⟩
  · intro F hF
    rw [Set.mem_singleton_iff] at hF
    subst hF
    refine ⟨fun h => (Set.not_nonempty_empty h).elim, ?_⟩
    rw [hP0]
    exact Set.singleton_nonempty 0 |>.ne_empty.symm
  · intro F hF G hGe
    rw [Set.mem_singleton_iff] at hF ⊢
    subst hF
    exact Set.subset_empty_iff.mp hGe.subset
  · intro x
    exact isEmptyElim x

end Grunbaum2003

-- Checked local ingredient: FinalBoundaryInduction

set_option autoImplicit false

namespace Grunbaum2003

/-- Dimension induction on actual vertex figures, with the prescribed target
simplex and one common map for every target face. -/
theorem boundary_refines_simplex_by_induction :
    ∀ d : ℕ, ∀ P : Set (Fin d → ℝ), IsDPolytope P →
      ∀ v : Fin (d + 1) → Fin d → ℝ, AffineIndependent ℝ v →
        BoundaryRefines P (convexHull ℝ (Set.range v)) := by
  intro d
  induction d with
  | zero =>
      intro P hP v hv
      exact boundary_refines_simplex_zero_dim P hP v hv
  | succ n ih =>
      intro P hP v hv
      have hd : 0 < n + 1 := Nat.zero_lt_succ n
      obtain ⟨p, W, l, α, Q₀, f, hW, hp, _, hPgen, _, hα, _, hBelow, hQ₀, hf, hCut⟩ :=
        exists_source_refinement_data (n + 1) hd P hP
      let a : Fin ((n + 1) + 1) := 0
      let T := convexHull ℝ (Set.range v)
      let W' := v '' {i | i ≠ a}
      let B := convexHull ℝ W'
      let r := AffineMap.homothety (v a) (1 / 2 : ℝ)
      obtain ⟨l', α', u, g, hW', _, hTgen, _, ha, hB, _, _, hAnti,
        hα', _, hBelow', hRadial, hrImage, hu, hg, hBase⟩ :=
          exists_simplex_target_data (n + 1) hd v hv a
      have hT : IsDPolytope T := simplex_isDPolytope (n + 1) v hv
      have hB₀ : IsDPolytope (convexHull ℝ (Set.range u)) := simplex_isDPolytope n u hu
      have hIH : BoundaryRefines Q₀ (convexHull ℝ (Set.range u)) := ih Q₀ hQ₀ u hu
      have haT : v a ∈ T := subset_convexHull ℝ _ (Set.mem_range_self a)
      have hTB : T = convexHull ℝ (insert (v a) B) := by
        have h := simplex_face_through_apex_eq_cone (n + 1) v hv a (IsExposed.refl T) haT
        change T = convexHull ℝ (insert (v a) (T ∩ B)) at h
        rw [Set.inter_eq_right.mpr hB.subset] at h
        exact h
      have hr : Function.Injective r :=
        AffineMap.homothety_injective (v a) (by norm_num : (1 / 2 : ℝ) ≠ 0)
      exact boundaryRefines_of_native_induction_cut_data (n + 1) hd
        P hP p hp W hW hPgen l α hα hBelow hQ₀ hB₀ hIH f g hf hg hCut
        T hT (v a) ha W' hW' hTgen l' α' hα' hBelow' B hB hTB hAnti hBase
        r hr hrImage hRadial

end Grunbaum2003

theorem solution (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : Grunbaum2003.IsDPolytope P)
    (v : Fin (d + 1) → (Fin d → ℝ)) (hv : AffineIndependent ℝ v) :
    Grunbaum2003.BoundaryRefines P (convexHull ℝ (Set.range v)) :=
  Grunbaum2003.boundary_refines_simplex_by_induction d P hP v hv

