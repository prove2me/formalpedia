-- Prove2me | solution 1 for GlobalTheory.fderiv_vecMulVec_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:32:10.47694+00:00
-- url     : https://prove2.me/submissions/a3e57e38-6960-4491-95c0-8a14a51d440c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FiniteAbsLeOneMulMemRange
import Theorems.Thm_GlobalTheory_spAct_spDiag_eq
import Theorems.Thm_GlobalTheory_spInvariant_conj
import Theorems.Thm_GlobalTheory_eventually_eq_column
import Theorems.Thm_GlobalTheory_IsSiegel_smul
import Theorems.Thm_GlobalTheory_isOpen_phDom
import Theorems.Thm_GlobalTheory_of_symm_mem_phDom
import Theorems.Thm_GlobalTheory_phSym_eq_self_of_isSymm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spAct_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spDiag_mem_sp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology
open GlobalTheory
variable {g : ℕ} {H : Matrix (Fin g) (Fin g) ℂ → ℂ}
namespace GlobalTheory
theorem _root_.solution (hol : IsHoloSiegel g H) (hH : IsSpInvariant g H)
    (hb : ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ τ ∈ SiegelH (Fin g),
      (τ.map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ‖H τ‖ ≤ K)
    (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) (e : Fin g) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ SiegelH (Fin g)) :
    fderiv ℂ (fun x : Fin g → Fin g → ℂ => H (phSym (of x))) (of.symm τ)
      (of.symm (vecMulVec (imC τ *ᵥ fun l => (U.val e l : ℂ))
        (imC τ *ᵥ fun l => (U.val e l : ℂ)))) = 0 := by
  set w := imC τ *ᵥ fun l => (U.val e l : ℂ) with hw
  have hτ' := spAct_mem (spDiag_mem_sp U) hτ
  have h1 := eventually_eq_column hol hH hb e hτ'
  rw [spAct_spDiag_eq] at h1
  have h2 : (fun i => (((U.val.map (Int.cast : ℤ → ℂ) * τ *
      (U.val.map (Int.cast : ℤ → ℂ))ᵀ) i e).im : ℂ)) = U.val.map (Int.cast : ℤ → ℂ) *ᵥ w := by
    ext i
    rw [Matrix.mul_assoc]
    simp [hw, mul_apply, mulVec, dotProduct, imC]
  have hd : HasDerivAt (fun s : ℂ => (of.symm τ + s • of.symm (vecMulVec w w) : Fin g → Fin g → ℂ))
      (of.symm (vecMulVec w w)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const
      (of.symm (vecMulVec w w) : Fin g → Fin g → ℂ)).const_add (of.symm τ)
  have hn := (isOpen_phDom g).mem_nhds (of_symm_mem_phDom hτ)
  have h3 := (hol.differentiableAt hn).hasFDerivAt.comp_hasDerivAt_of_eq 0 hd (by simp)
  refine h3.unique ((hasDerivAt_const 0 (H τ)).congr_of_eventuallyEq ?_)
  filter_upwards [h1, hd.continuousAt.eventually (p := fun x => x ∈ phDom g) (by simpa using hn)]
    with s hs hm
  have hsym : phSym (of (of.symm τ + s • of.symm (vecMulVec w w))) = τ + s • vecMulVec w w := by
    refine phSym_eq_self_of_isSymm (hτ.1.add (IsSymm.smul ?_ s))
    exact transpose_vecMulVec w w
  have hm' : τ + s • vecMulVec w w ∈ SiegelH (Fin g) := hsym ▸ hm
  rw [Function.comp_apply, hsym, ← spInvariant_conj hH U hm', ← spInvariant_conj hH U hτ, ← hs, h2,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul,
    vecMul_transpose]
end GlobalTheory
