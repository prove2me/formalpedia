-- Prove2me | solution 1 for Grunbaum2003.projections_polytope_implies_closed
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T17:57:19.067037+00:00
-- url     : https://prove2.me/submissions/f79505f2-dea6-43d8-910e-c894e67d6928

import Theorems.Thm_Grunbaum2003_compact_convex_nonpolytope_infinite_extreme
import Theorems.Thm_Grunbaum2003_generic_projection_nonpolytope
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false

namespace Grunbaum2003

/-- Extending a nonzero linear functional on `Fin d → ℝ` (`2 ≤ j < d`) to a surjective linear
map onto `Fin j → ℝ` whose `0`-th coordinate equals `l`. -/
theorem aux_closed_extend_surj {d j : ℕ} (hj2 : 2 ≤ j) (hjd : j < d)
    (l : Module.Dual ℝ (Fin d → ℝ)) (v0 : Fin d → ℝ) (hv0 : l v0 = 1) :
    ∃ L : (Fin d → ℝ) →ₗ[ℝ] (Fin j → ℝ),
      Function.Surjective L ∧ ∀ x : Fin d → ℝ, L x ⟨0, by omega⟩ = l x := by
  have hl0 : l ≠ 0 := by
    intro h0; have := hv0; rw [h0, LinearMap.zero_apply] at this; norm_num at this
  have hker_dim : Module.finrank ℝ (LinearMap.ker l) = Module.finrank ℝ (Fin (d - 1) → ℝ) := by
    have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero hl0
    rw [Module.finrank_fin_fun] at h1
    rw [Module.finrank_fin_fun]
    omega
  let E : LinearMap.ker l ≃ₗ[ℝ] (Fin (d - 1) → ℝ) := LinearEquiv.ofFinrankEq _ _ hker_dim
  let π : (Fin d → ℝ) →ₗ[ℝ] LinearMap.ker l :=
    { toFun := fun x => ⟨x - l x • v0, by
        rw [LinearMap.mem_ker, map_sub, map_smul, hv0, smul_eq_mul, mul_one, sub_self]⟩
      map_add' := fun x y => by ext; simp [sub_add_sub_comm, add_smul]
      map_smul' := fun c x => by ext; simp [smul_sub, mul_smul] }
  let coord : Fin j → ((Fin d → ℝ) →ₗ[ℝ] ℝ) := fun i =>
    if hi : i.val = 0 then l
    else (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (d - 1) => ℝ)
      ⟨i.val - 1, by omega⟩).comp (E.toLinearMap.comp π)
  let L : (Fin d → ℝ) →ₗ[ℝ] (Fin j → ℝ) := LinearMap.pi coord
  refine ⟨L, ?_, fun x => by simp [L, coord]⟩
  intro y
  let kvec : Fin (d - 1) → ℝ := fun m =>
    if hm : m.val + 1 < j then y ⟨m.val + 1, hm⟩ else 0
  let w : LinearMap.ker l := E.symm kvec
  have hw_ker : l (w : Fin d → ℝ) = 0 := w.2
  let x : Fin d → ℝ := y ⟨0, by omega⟩ • v0 + (w : Fin d → ℝ)
  have hlx : l x = y ⟨0, by omega⟩ := by
    simp [x, map_add, map_smul, hv0, hw_ker]
  have hπx : π x = w := by
    ext
    simp [π, hlx, x]
  use x
  ext i
  simp only [L, LinearMap.pi_apply, coord]
  split_ifs with hi
  · have hi0 : i = ⟨0, by omega⟩ := Fin.ext hi
    rw [hi0, hlx]
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hπx, w,
      LinearEquiv.apply_symm_apply, LinearMap.proj_apply, kvec]
    have hm : (i.val - 1) + 1 < j := by omega
    rw [dif_pos hm]
    congr 1
    exact Fin.ext (by simp; omega)

end Grunbaum2003

open Grunbaum2003

theorem solution (d : ℕ) (hd : 3 ≤ d)
    (K : Set (Fin d → ℝ)) (hbounded : Bornology.IsBounded K)
    (hconvex : Convex ℝ K)
    (hproj : ∃ j : ℕ, 2 ≤ j ∧ j < d ∧
      ∀ f : (Fin d → ℝ) →ᵃ[ℝ] (Fin j → ℝ), Function.Surjective f →
        ∃ W : Set (Fin j → ℝ), W.Finite ∧ f '' K = convexHull ℝ W) :
    IsClosed K := by
  obtain ⟨j, hj2, hjd, hproj_j⟩ := hproj
  have hcl_img : ∀ f : (Fin d → ℝ) →ᵃ[ℝ] (Fin j → ℝ), Function.Surjective f →
      f '' closure K = f '' K := by
    intro f hsurj
    obtain ⟨W, hWfin, hW⟩ := hproj_j f hsurj
    have hfcont : Continuous f := by
      have h : (f : (Fin d → ℝ) → (Fin j → ℝ)) = fun x => f.linear x + f 0 := by
        funext x
        have := f.map_vadd (0 : Fin d → ℝ) x
        simpa [vsub_eq_sub, vadd_eq_add, add_comm] using this
      rw [h]
      exact f.linear.continuous_of_finiteDimensional.add continuous_const
    have hWclosed : IsClosed (f '' K) := hW ▸ hWfin.isClosed_convexHull ℝ
    exact Set.Subset.antisymm
      ((image_closure_subset_closure_image hfcont).trans hWclosed.closure_subset)
      (Set.image_mono subset_closure)
  have hcompact : IsCompact (closure K) := hbounded.isCompact_closure
  have hconv_cl : Convex ℝ (closure K) := hconvex.closure
  have hcl_poly : ∃ V : Set (Fin d → ℝ), V.Finite ∧ closure K = convexHull ℝ V := by
    by_contra hnotpoly
    have hext := compact_convex_nonpolytope_infinite_extreme d (closure K)
      hcompact hconv_cl hnotpoly
    obtain ⟨f, hsurj, hnotW⟩ := generic_projection_nonpolytope d hd (closure K)
      hcompact hconv_cl hext j hj2 hjd
    obtain ⟨W, hWfin, hW⟩ := hproj_j f hsurj
    exact hnotW ⟨W, hWfin, (hcl_img f hsurj).trans hW⟩
  obtain ⟨V0, hV0fin, hclV0⟩ := hcl_poly
  set S : Set (Fin d → ℝ) := (closure K).extremePoints ℝ with hSdef
  have hSsub : S ⊆ V0 := by rw [hSdef, hclV0]; exact extremePoints_convexHull_subset
  have hSfin : S.Finite := hV0fin.subset hSsub
  have hclS : closure K = convexHull ℝ S := by
    have hkm := closure_convexHull_extremePoints hcompact hconv_cl
    rw [(hSfin.isClosed_convexHull ℝ).closure_eq] at hkm
    exact hkm.symm
  suffices hSK : S ⊆ K by
    exact isClosed_of_closure_subset (hclS ▸ convexHull_min hSK hconvex)
  intro e he
  rcases (S \ {e}).eq_empty_or_nonempty with hdiff_empty | ⟨y0, hy0⟩
  · have hSe : S ⊆ {e} := Set.sdiff_eq_empty.mp hdiff_empty
    have hcl_sub : closure K ⊆ {e} := by
      rw [hclS, ← convexHull_singleton (𝕜 := ℝ) e]
      exact convexHull_mono hSe
    have hKne : K.Nonempty := closure_nonempty_iff.mp ⟨e, he.1⟩
    obtain ⟨x0, hx0⟩ := hKne
    have hx0e : x0 = e := Set.mem_singleton_iff.mp (hcl_sub (subset_closure hx0))
    rwa [← hx0e]
  · have he_not : e ∉ convexHull ℝ (S \ {e}) := by
      intro he_in
      have hS_sub : S ⊆ convexHull ℝ (S \ {e}) := by
        intro z hz
        by_cases hze : z = e
        · rwa [hze]
        · exact subset_convexHull ℝ (S \ {e}) ⟨hz, hze⟩
      have hcl_eq : closure K = convexHull ℝ (S \ {e}) :=
        Set.Subset.antisymm
          (hclS ▸ convexHull_min hS_sub (convex_convexHull ℝ _))
          (hclS ▸ convexHull_mono Set.sdiff_subset)
      have he_ext : e ∈ (convexHull ℝ (S \ {e})).extremePoints ℝ := hcl_eq ▸ he
      exact (extremePoints_convexHull_subset he_ext).2 rfl
    obtain ⟨φ, u, hφS, hφe⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ (S \ {e})) ((hSfin.sdiff).isClosed_convexHull ℝ) he_not
    let l : Module.Dual ℝ (Fin d → ℝ) := (φ : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    have hly0 : l y0 < u := hφS y0 (subset_convexHull ℝ (S \ {e}) hy0)
    have hle : u < l e := hφe
    have hne : l (e - y0) ≠ 0 := by
      rw [map_sub]; linarith
    let v0 : Fin d → ℝ := (l (e - y0))⁻¹ • (e - y0)
    have hv0 : l v0 = 1 := by
      dsimp [v0]
      rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hne]
    obtain ⟨L, hLsurj, hL0⟩ := aux_closed_extend_surj hj2 hjd l v0 hv0
    have hAsurj : Function.Surjective L.toAffineMap := hLsurj
    have himg := hcl_img L.toAffineMap hAsurj
    have he_img : L.toAffineMap e ∈ L.toAffineMap '' K := by
      rw [← himg]
      exact ⟨e, he.1, rfl⟩
    obtain ⟨x, hxK, hLx⟩ := he_img
    have hlxe : l x = l e := by
      have h0 := congrArg (fun w : Fin j → ℝ => w ⟨0, by omega⟩) hLx
      simp only [LinearMap.coe_toAffineMap] at h0
      rwa [hL0 x, hL0 e] at h0
    have hx_cl : x ∈ convexHull ℝ S := hclS ▸ subset_closure hxK
    set F := hSfin.toFinset with hFdef
    have hFS : (F : Set (Fin d → ℝ)) = S := hSfin.coe_toFinset
    rw [← hFS] at hx_cl
    obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.mp hx_cl
    have hlt_z : ∀ z ∈ F, z ≠ e → l z < l e := by
      intro z hz hze
      have hzS : z ∈ S \ {e} := ⟨(Set.Finite.mem_toFinset hSfin).mp hz, hze⟩
      exact (hφS z (subset_convexHull ℝ (S \ {e}) hzS)).trans hle
    have hle_z : ∀ z ∈ F, l z ≤ l e := by
      intro z hz
      by_cases hze : z = e
      · rw [hze]
      · exact (hlt_z z hz hze).le
    have hsum0 : ∑ z ∈ F, w z * (l e - l z) = 0 := by
      have h1 : l x = ∑ z ∈ F, w z * l z := by
        rw [← hwx, map_sum]; simp [map_smul, smul_eq_mul]
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
      linarith
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun z hz =>
      mul_nonneg (hw0 z hz) (by linarith [hle_z z hz]))).mp hsum0
    have hw_zero : ∀ z ∈ F, z ≠ e → w z = 0 := by
      intro z hz hze
      have h1 := hterm z hz
      have h2 : l e - l z ≠ 0 := by linarith [hlt_z z hz hze]
      exact (mul_eq_zero.mp h1).resolve_right h2
    have heF : e ∈ F := (Set.Finite.mem_toFinset hSfin).mpr he
    have hwe1 : w e = 1 := by
      rw [← hw1]
      exact (Finset.sum_eq_single e (fun z hz hze => hw_zero z hz hze)
        (fun h => absurd heF h)).symm
    have hxe : x = e := by
      rw [← hwx, Finset.sum_eq_single e (fun z hz hze => by rw [hw_zero z hz hze, zero_smul])
        (fun h => absurd heF h), hwe1, one_smul]
    rwa [← hxe]
