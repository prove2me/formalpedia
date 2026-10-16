-- Prove2me | solution 1 for OAI.Paper256.positive_map_resolvent_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:26:29.89809+00:00
-- url     : https://prove2.me/submissions/b8817771-7c14-4167-ae43-fb1ee894e8cd

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/MatrixResolvent.lean:L49-L81
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.positive_map_resolvent_isUnit. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit
import Definitions.Def_OAI_Analysis_HyperbolicCones_Coordinates

-- ---- from OAI.Analysis.HyperbolicCones.MatrixResolvent ----
namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open Matrix

namespace Paper256

theorem isUnit_of_adjoint_difference_posDef {n : ℕ} (H M : Mat n ℂ) (δ : ℂ)
    (hδ : δ ≠ 0) (hM : M.PosDef) (hdiff : H - Hᴴ = δ • M) : IsUnit H := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  change Function.Injective H.mulVecLin
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.2
  intro w hw
  change H *ᵥ w = 0 at hw
  by_contra hw0
  have hq : dotProduct (star w) ((H - Hᴴ) *ᵥ w) = 0 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, hw, dotProduct_zero]
    rw [dotProduct_mulVec, vecMul_conjTranspose, star_star, hw, star_zero,
      zero_dotProduct, sub_self]
  rw [hdiff, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hq
  exact (ne_of_gt (hM.dotProduct_mulVec_pos hw0)) ((mul_eq_zero.mp hq).resolve_left hδ)

theorem resolvent_adjoint_difference {n : ℕ} (A : Mat n ℂ) (hA : A.IsHermitian)
    (z : ℂ) (hAz : IsUnit (Matrix.det (z • (1 : Mat n ℂ) - A))) :
    (z • (1 : Mat n ℂ) - A)⁻¹ - ((z • (1 : Mat n ℂ) - A)⁻¹)ᴴ =
      -(z - star z) • (((z • (1 : Mat n ℂ) - A)⁻¹)ᴴ *
        (z • (1 : Mat n ℂ) - A)⁻¹) := by
  let T := z • (1 : Mat n ℂ) - A
  have ht : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv T hAz
  have hts : T⁻¹ᴴ * Tᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, ht, Matrix.conjTranspose_one]
  have hd : Tᴴ - T = -(z - star z) • (1 : Mat n ℂ) := by
    simp only [T, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hA.eq]
    module
  change T⁻¹ - T⁻¹ᴴ = -(z - star z) • (T⁻¹ᴴ * T⁻¹)
  calc
    T⁻¹ - T⁻¹ᴴ = T⁻¹ᴴ * (Tᴴ - T) * T⁻¹ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hts, Matrix.one_mul, Matrix.mul_assoc, ht,
        Matrix.mul_one]
    _ = -(z - star z) • (T⁻¹ᴴ * T⁻¹) := by
      rw [hd, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

theorem positive_map_resolvent_isUnit {n m : ℕ} (A : Mat n ℂ) (B : Mat m ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (Φ : Mat n ℂ →ₗ[ℂ] Mat m ℂ)
    (hΦstar : ∀ X, (Φ X)ᴴ = Φ Xᴴ)
    (hΦpos : ∀ X, X.PosSemidef → (Φ X).PosSemidef)
    (z : ℂ) (hz : z.im ≠ 0) :
    IsUnit (z • (1 : Mat m ℂ) - B - Φ ((z • (1 : Mat n ℂ) - A)⁻¹)) := by
  have hu : IsUnit (z • (1 : Mat n ℂ) - A) := by
    by_contra hn
    apply hz
    apply hA.isSelfAdjoint.im_eq_zero_of_mem_spectrum
    simpa only [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one] using hn
  have hd := resolvent_adjoint_difference A hA z ((Matrix.isUnit_iff_isUnit_det _).1 hu)
  let R := (z • (1 : Mat n ℂ) - A)⁻¹
  let M := (1 : Mat m ℂ) + Φ (Rᴴ * R)
  have hm : M.PosDef := Matrix.PosDef.one.add_posSemidef
    (hΦpos _ (Matrix.posSemidef_conjTranspose_mul_self R))
  refine isUnit_of_adjoint_difference_posDef _ M (z - star z) ?_ hm ?_
  · intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.zero_im] at hi
    apply hz
    linarith
  · have hd' : R - Rᴴ = -(z - star z) • (Rᴴ * R) := hd
    calc
      _ = (z - star z) • (1 : Mat m ℂ) - Φ (R - Rᴴ) := by
        simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
          Matrix.conjTranspose_one, hB.eq, hΦstar, map_sub]
        module
      _ = (z - star z) • M := by
        rw [hd', map_smul]
        dsimp [M]
        module

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open Matrix


theorem solution : type_of% @_root_.OAI.Paper256.positive_map_resolvent_isUnit := @_root_.OAI.Paper256.positive_map_resolvent_isUnit
