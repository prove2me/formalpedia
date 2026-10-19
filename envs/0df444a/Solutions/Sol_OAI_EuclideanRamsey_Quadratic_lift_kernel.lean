-- Prove2me | solution 1 for OAI.EuclideanRamsey.Quadratic.lift_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:07:20.968636+00:00
-- url     : https://prove2.me/submissions/0ad14101-944b-4917-8a2a-9869da2c9c1c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Quadratic.lean:L49-L105
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.Quadratic.lift_kernel. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_NormalCost__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_OrbitAveraging__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CorrectionPaths__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Quadratic

-- ---- from OAI.Combinatorics.EuclideanRamsey.Quadratic ----
namespace OAI

/-! Quadratic row independence gives a tensor lift and the Ramsey property. -/

noncomputable section
open scoped TensorProduct BigOperators RealInnerProductSpace Matrix

namespace EuclideanRamsey.Quadratic

theorem field_rightInverse {F ι ν : Type*} [Field F]
    [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
    (E : Matrix ι ν F) (hE : LinearIndependent F E.row) :
    ∃ S : Matrix ν ι F, E * S = 1 := by
  have hinj : Function.Injective E.vecMulLinear := Matrix.vecMul_injective_iff.mpr hE
  obtain ⟨g, hg⟩ := E.vecMulLinear.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  let S : Matrix ν ι F := fun q j => g (Pi.single q 1) j
  refine ⟨S, ?_⟩
  ext i j
  have hrow : E.vecMulLinear (Pi.single i 1) = E i := by
    ext q
    change (∑ x : ι, (Pi.single i (1 : F) : ι → F) x * E x q) = E i q
    rw [Finset.sum_eq_single i]
    · simp
    · intro x _ hxi
      simp [hxi]
    · simp
  have hgi : g (E i) = Pi.single i 1 := by
    have ht := LinearMap.congr_fun hg (Pi.single i 1)
    simpa only [LinearMap.comp_apply, LinearMap.id_apply, hrow] using ht
  have hsum : (∑ q : ν, E i q • Pi.single q (1 : F)) = E i := by
    ext q
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single q]
    · simp
    · intro x _ hxq
      simp [Ne.symm hxq]
    · simp
  have ht := congrArg (fun x : ν → F => g x j) hsum
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at ht
  change (∑ q, E i q * g (Pi.single q 1) j) = _
  rw [ht, hgi]
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

theorem lift_kernel {F B ι ν : Type*} [Field F] [CommRing B]
    [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
    (μ : B →+* F) (σ : F →+* B) (hsection : ∀ x, μ (σ x) = x)
    (D : Matrix ι ν B) (hrows : LinearIndependent F (D.map μ).row)
    (h : ν → F) (hh : D.map μ *ᵥ h = 0) :
    ∃ z : ν → B, D *ᵥ z = 0 ∧ (fun q => μ (z q)) = h := by
  obtain ⟨S, hS⟩ := field_rightInverse (D.map μ) hrows
  let J : Matrix ν ι B := S.map σ
  let M : Matrix ι ι B := D * J
  let b : ν → B := fun q => σ (h q)
  have hJ : J.map μ = S := by
    ext q i
    exact hsection _
  have hM : M.map μ = 1 := by
    calc
      M.map μ = D.map μ * J.map μ := by
        ext i j
        simp [M, Matrix.mul_apply]
      _ = 1 := by rw [hJ, hS]
  have hdet : μ M.det = 1 := by
    rw [μ.map_det]
    change (M.map μ).det = 1
    rw [hM, Matrix.det_one]
  have hb : (fun q => μ (b q)) = h := by
    funext q
    exact hsection _
  have hDb : (fun i => μ ((D *ᵥ b) i)) = 0 := by
    ext i
    rw [μ.map_mulVec]
    change (D.map μ *ᵥ (fun q => μ (b q))) i = 0
    rw [hb, hh]
    rfl
  let z : ν → B := M.det • b - J *ᵥ (M.adjugate *ᵥ (D *ᵥ b))
  refine ⟨z, ?_, ?_⟩
  · change D *ᵥ (M.det • b - J *ᵥ (M.adjugate *ᵥ (D *ᵥ b))) = 0
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
    change M.det • (D *ᵥ b) - M *ᵥ (M.adjugate *ᵥ (D *ᵥ b)) = 0
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_self]
  · have hAdj : (fun i => μ ((M.adjugate *ᵥ (D *ᵥ b)) i)) = 0 := by
      ext i
      rw [μ.map_mulVec]
      change (M.adjugate.map μ *ᵥ (fun j => μ ((D *ᵥ b) j))) i = 0
      rw [hDb, Matrix.mulVec_zero]
      rfl
    have hCorrection : (fun q => μ ((J *ᵥ (M.adjugate *ᵥ (D *ᵥ b))) q)) = 0 := by
      ext q
      rw [μ.map_mulVec]
      change (J.map μ *ᵥ (fun i => μ ((M.adjugate *ᵥ (D *ᵥ b)) i))) q = 0
      rw [hAdj, Matrix.mulVec_zero]
      rfl
    funext q
    change μ (M.det * b q - (J *ᵥ (M.adjugate *ᵥ (D *ᵥ b))) q) = h q
    rw [map_sub, map_mul, hdet, one_mul, congrFun hCorrection q]
    change μ (b q) - (0 : F) = h q
    rw [sub_zero]
    exact congrFun hb q

end EuclideanRamsey.Quadratic

namespace EuclideanRamsey

end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey OAI.EuclideanRamsey.Quadratic
open scoped TensorProduct BigOperators RealInnerProductSpace Matrix


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.Quadratic.lift_kernel := @_root_.OAI.EuclideanRamsey.Quadratic.lift_kernel
