-- Prove2me | solution 1 for GlobalTheory.Reg.cell_change_birational
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:32:41.167092+00:00
-- url     : https://prove2.me/submissions/78d4b6bf-6546-4736-ba44-513d72c18c32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_Reframe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsLowerMulUpperOfLeadingMinors
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsFlagCoordinatesCellChangeBirational
import Theorems.Thm_GlobalTheory_Reg_CellChange_exists_algEquiv_of_generates
import Theorems.Thm_GlobalTheory_Reg_CellChange_minors_iff
import Theorems.Thm_GlobalTheory_Reg_CellChange_upper_inv
import Theorems.Thm_GlobalTheory_Reg_CellChange_lower_mem_range
import Theorems.Thm_GlobalTheory_Reg_CellChange_lowM_upper
import Theorems.Thm_GlobalTheory_Reg_CellChange_lowM_diag
import Theorems.Thm_GlobalTheory_Reg_CellChange_lowM_entry
import Theorems.Thm_GlobalTheory_Reg_CellChange_lowM_map
import Theorems.Thm_GlobalTheory_Reg_CellChange_lowM_of_lower
import Theorems.Thm_GlobalTheory_Reg_CellChange_generic_minors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
namespace GlobalTheory.Reg
theorem _root_.solution :
    ∀ (κ T : Type) [Field κ] [Infinite κ] [Finite T] (r : T → ℕ) (G : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) κ) (σ : ∀ τ, Equiv.Perm (Fin (r τ))), (∀ τ, IsUnit (G τ).det) → ∃ (e : FractionRing (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ) ≃ₐ[κ] FractionRing (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ)) (b : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) (FractionRing (MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ))), (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) ∧ ∀ τ, (G τ).map (algebraMap κ _) * lowM (fun v => algebraMap (MvPolynomial _ κ) _ (MvPolynomial.X v)) τ = (lowM (fun v => e (algebraMap (MvPolynomial _ κ) _ (MvPolynomial.X v))) τ).submatrix (σ τ).symm id * b τ := by
  intro κ T _ _ _ r G σ hG
  let P := MvPolynomial (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) κ
  let K := FractionRing P
  let A : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) κ := fun τ => (G τ).submatrix (σ τ) id
  have hA : ∀ τ, IsUnit (A τ).det := fun τ => by
    simp only [A]
    rw [Matrix.det_permute]
    exact (((Equiv.Perm.sign (σ τ)).isUnit).map (Int.castRingHom κ)).mul (hG τ)
  have hdec := fun τ => (CellChange.minors_iff ((A τ).map (algebraMap κ K) *
      lowM (fun v => algebraMap P K (MvPolynomial.X v)) τ)).1 (fun k hk => by
    have h := (map_ne_zero_iff (algebraMap P K) (IsFractionRing.injective _ _)).2
      (CellChange.generic_minors A hA τ k hk)
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, Matrix.map_mul, CellChange.lowM_map,
      Matrix.map_map] at h
    exact isUnit_iff_ne_zero.2 h)
  choose l b h0 h1 hb hu h using hdec
  obtain ⟨e, he⟩ := CellChange.exists_algEquiv_of_generates
    (fun v : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) => l v.1 v.2.1.2 v.2.1.1) (fun v => by
      set y : (Σ τ : T, {p : Fin (r τ) × Fin (r τ) // p.1 < p.2}) → K := fun v => l v.1 v.2.1.2 v.2.1.1 with hy
      let F := IntermediateField.adjoin κ (Set.range y)
      obtain ⟨hbi, hbu, hbb⟩ := CellChange.upper_inv _ (hb v.1) (hu v.1)
      obtain ⟨x, hx⟩ := CellChange.lower_mem_range (algebraMap F K)
        ((A v.1)⁻¹.map (algebraMap κ F) * lowM (fun w => (⟨y w, IntermediateField.subset_adjoin _ _ ⟨w, rfl⟩⟩ : F)) v.1)
        (lowM (fun v => algebraMap P K (MvPolynomial.X v)) v.1) (b v.1)⁻¹
        (CellChange.lowM_upper _ _) (CellChange.lowM_diag _ _) hbi hbu (by
          rw [Matrix.map_mul, CellChange.lowM_map, Matrix.map_map]
          change (A v.1)⁻¹.map (algebraMap κ K) * lowM y v.1 = _
          rw [hy, CellChange.lowM_of_lower l v.1 (h0 _) (h1 _), ← Matrix.mul_one (l v.1), ← hbb,
            ← Matrix.mul_assoc (l v.1), ← h, Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul,
            Matrix.nonsing_inv_mul _ (hA _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul])
        v.2.1.2 v.2.1.1
      rw [CellChange.lowM_entry] at hx
      have hx' : (x : K) ∈ F := x.2
      exact hx ▸ hx')
  refine ⟨e, b, fun τ => ⟨hb τ, fun i => (hu τ i).ne_zero⟩, fun τ => ?_⟩
  simp only [he]
  rw [CellChange.lowM_of_lower l τ (h0 τ) (h1 τ)]
  ext i j
  have := congrFun (congrFun (h τ) ((σ τ).symm i)) j
  simpa [A, Matrix.mul_apply] using this
end GlobalTheory.Reg
