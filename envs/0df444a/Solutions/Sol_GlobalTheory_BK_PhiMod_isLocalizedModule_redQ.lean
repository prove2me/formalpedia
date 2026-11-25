-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.isLocalizedModule_redQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:26:32.996286+00:00
-- url     : https://prove2.me/submissions/80315097-6ff9-49aa-9ae9-21a672dccdcd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Theorems.Thm_GlobalTheory_BK_PhiMod_redQ_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
open GlobalTheory.BK.PhiMod
variable {O K l e a ι} (P : PhiMod O K l e a ι)
variable [Fact l.Prime]
variable [NormedAlgebra ℚ_[l] K]
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution (τ : ZMod a) :
    IsLocalizedModule (Submonoid.powers (l : O)) (P.redQ τ) where
  map_units := by
    rintro ⟨_, n, rfl⟩
    rw [Module.End.isUnit_iff]
    have hl : (l : K) ^ n ≠ 0 := pow_ne_zero _ (l_ne_zero l)
    have : ⇑(algebraMap O (Module.End O (ι → K)) ((l : O) ^ n)) = fun y => (l : K) ^ n • y := by
      ext y i
      rw [Module.algebraMap_end_apply]
      simp [Algebra.smul_def]
    rw [this]
    exact (MulAction.toPerm (Units.mk0 _ hl)).bijective
  surj y := by
    choose n b hb using fun i =>
      exists_pow_mul_mem (O := O) l (((P.mxInv τ).map constantCoeff *ᵥ y) i)
    let m := Finset.univ.sup n
    refine ⟨⟨Submodule.Quotient.mk ⟨P.mx τ *ᵥ fun i =>
      C ((l : K) ^ m * ((P.mxInv τ).map constantCoeff *ᵥ y) i), P.mem_extc.2 ⟨_, fun i => ?_, rfl⟩⟩,
      ⟨_, m, rfl⟩⟩, ?_⟩
    · obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ i))
      have : (l : K) ^ m * ((P.mxInv τ).map constantCoeff *ᵥ y) i =
          algebraMap O K ((l : O) ^ c * b i) := by
        rw [map_mul, ← hb, show m = c + n i from hc, pow_add]
        simp [mul_assoc]
      rw [this, ← algebraMap_eq_C]
      exact Subalgebra.algebraMap_mem _ _
    · change ((l : O) ^ m) • y = red0 (P.mx τ *ᵥ _)
      have : (red0 fun i => C ((l : K) ^ m * ((P.mxInv τ).map constantCoeff *ᵥ y) i)) =
          (l : K) ^ m • ((P.mxInv τ).map constantCoeff *ᵥ y) := by
        ext i; simp
      rw [powerSeriesVecReduceModU_mulVec, this, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
      erw [P.matrix_mul_inv_const_eq_one τ]
      ext i
      simp [Algebra.smul_def]
  exists_of_eq h := ⟨1, by rw [P.redQ_injective τ h]⟩
end GlobalTheory.BK.PhiMod
