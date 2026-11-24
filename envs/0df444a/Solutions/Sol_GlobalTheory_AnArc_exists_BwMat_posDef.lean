-- Prove2me | solution 1 for GlobalTheory.AnArc.exists_BwMat_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:42:38.718135+00:00
-- url     : https://prove2.me/submissions/9061d775-2c88-4ef2-b475-f576f91dc7f7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Theorems.Thm_GlobalTheory_PolarisedLattice_real_pos_of_int_pos
import Theorems.Thm_GlobalTheory_PolarisedLattice_exists_posDef_smul_add
import Theorems.Thm_GlobalTheory_AnArc_Bw_eq
import Theorems.Thm_GlobalTheory_AnArc_Bw_symm
import Theorems.Thm_GlobalTheory_AnArc_BwMat_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Matrix
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution : ∃ T₀ : ℝ, ∀ w : ℂ, T₀ < w.im → (A.BwMat w).PosDef := by
  classical
  let b := Module.Free.chooseBasis ℤ A.X
  let M : Matrix _ _ ℤ := Matrix.of fun i j => A.be (b i) (b j)
  have hM : (M.map (Int.cast : ℤ → ℝ)).PosDef := by
    refine PolarisedLattice.real_pos_of_int_pos M (fun i j => A.be_symm _ _) fun x hx => ?_
    have h0 : ∑ i, x i • b i ≠ 0 := fun h =>
      hx (funext (Fintype.linearIndependent_iff.1 b.linearIndependent x h))
    have := A.be_pos _ h0
    convert this using 1
    simp only [M, dotProduct, mulVec, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum, Matrix.of_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hC : (A.BwMat 0).IsHermitian := by
    ext i j; simp [BwMat_apply, A.Bw_symm 0 (Module.Free.chooseBasis ℤ A.X i)]
  obtain ⟨T₀, hT⟩ := PolarisedLattice.exists_posDef_smul_add hM hC
  refine ⟨T₀, fun w hw => ?_⟩
  convert hT _ hw using 1
  ext i j
  simp [BwMat_apply, Bw_eq, M, b]; ring
end GlobalTheory.AnArc
