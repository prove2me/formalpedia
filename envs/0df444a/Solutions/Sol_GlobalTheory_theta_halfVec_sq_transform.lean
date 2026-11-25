-- Prove2me | solution 1 for GlobalTheory.theta_halfVec_sq_transform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:41:08.426263+00:00
-- url     : https://prove2.me/submissions/45cad132-b9a2-45a3-8b6b-f98902f13288

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FromBlocksMapIntCastMemSymplecticGroup
import Theorems.Thm_GlobalTheory_symplectic_fromBlocks_relations
import Theorems.Thm_GlobalTheory_exists_theta_multiplier_of_two_dvd
import Theorems.Thm_GlobalTheory_theta_char_transform
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_GlobalTheory_mem_siegelUpperCoords
import Theorems.Thm_GlobalTheory_riemannThetaJointForm_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_eC_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_mulVec_halfVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_ofIntVec_dot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_ofRealVec_halfVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_theta_sq_red
import Theorems.Thm_ReciprocityTheory_PTheta_eC_add
import Theorems.Thm_ReciprocityTheory_PTheta_eC_int
import Theorems.Thm_ReciprocityTheory_PTheta_eC_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero
attribute [local simp] GlobalTheory.mem_siegelUpperCoords
attribute [local simp] GlobalTheory.riemannThetaJointForm_apply



set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
namespace GlobalTheory
theorem _root_.solution (hγ : γ ∈ symplecticGroup (Fin g) ℤ)
    (hb : ∀ i j, 4 ∣ γ.toBlocks₁₂ i j) (hc : ∀ i j, 4 ∣ γ.toBlocks₂₁ i j) {k k' m m' : Fin g → ℤ}
    (hm : ∀ i, m i ≡ (γ.toBlocks₁₁ᵀ *ᵥ k) i [ZMOD 2])
    (hm' : ∀ i, m' i ≡ (γ.toBlocks₂₂ᵀ *ᵥ k') i [ZMOD 2])
    {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) (z : Fin g → ℂ) :
    theta (halfVec k) (halfVec k') (zAct γ τ z) (spAct γ τ) ^ 2 =
      (ZMod.χ₄ (γ.toBlocks₂₂.det : ZMod 4) : ℤ) * (jAut γ τ).det * eC (expArg γ τ z) *
        theta (halfVec m) (halfVec m') z τ ^ 2 := by
  have h24 : (2 : ℤ) ∣ 4 := by norm_num
  obtain ⟨l, -, hl⟩ := exists_theta_multiplier_of_two_dvd hγ (fun i j => h24.trans (hb i j))
    fun i j => h24.trans (hc i j)
  set n := γ.toBlocks₁₁ᵀ *ᵥ k + γ.toBlocks₂₁ᵀ *ᵥ k' with hn
  set n' := γ.toBlocks₁₂ᵀ *ᵥ k + γ.toBlocks₂₂ᵀ *ᵥ k' with hn'
  have hadd (x y : Fin g → ℤ) : halfVec (x + y) = halfVec x + halfVec y := by
    ext i
    simp [halfVec, add_div]
  have key := theta_char_transform hγ hτ (hl τ hτ).1 (p := halfVec n) (q := halfVec n')
    (p' := halfVec k) (q' := halfVec k') (by rw [mulVec_halfVec, mulVec_halfVec, hn, hadd])
    (by rw [mulVec_halfVec, mulVec_halfVec, hn', hadd]) z
  have hc' (i : Fin g) : 4 ∣ (γ.toBlocks₂₁ᵀ *ᵥ k') i :=
    Finset.dvd_sum (s := Finset.univ) fun j _ => (hc j i).mul_right (k' j)
  have hb' (i : Fin g) : 4 ∣ (γ.toBlocks₁₂ᵀ *ᵥ k) i :=
    Finset.dvd_sum (s := Finset.univ) fun j _ => (hb j i).mul_right (k j)
  have e1 : theta (halfVec n) (halfVec n') z τ ^ 2 = theta (halfVec m) (halfVec m') z τ ^ 2 := by
    rw [theta_sq_red n, theta_sq_red m]
    congr 3 with i
    · have h1 : m i % 2 = _ := hm i
      have h2 := hc' i
      rw [h1, hn, Pi.add_apply]
      omega
    · have h1 : m' i % 2 = _ := hm' i
      have h2 := hb' i
      rw [h1, hn', Pi.add_apply]
      omega
  obtain ⟨t, ht⟩ : 4 ∣ k ⬝ᵥ k' - n ⬝ᵥ n' := by
    have r5 := (symplectic_fromBlocks_relations
      (by rwa [fromBlocks_toBlocks] : fromBlocks γ.toBlocks₁₁ γ.toBlocks₁₂ γ.toBlocks₂₁
        γ.toBlocks₂₂ ∈ symplecticGroup (Fin g) ℤ)).2.2.2.2
    have e : k ⬝ᵥ k' = (γ.toBlocks₁₁ᵀ *ᵥ k) ⬝ᵥ (γ.toBlocks₂₂ᵀ *ᵥ k') -
        (γ.toBlocks₁₂ᵀ *ᵥ k) ⬝ᵥ (γ.toBlocks₂₁ᵀ *ᵥ k') := by
      rw [dotProduct_comm k, dotProduct_comm (_ *ᵥ k), dotProduct_comm (_ *ᵥ k),
        mulVec_transpose _ k', mulVec_transpose _ k', ← dotProduct_mulVec, ← dotProduct_mulVec,
        mulVec_mulVec, mulVec_mulVec, ← dotProduct_sub, ← sub_mulVec, r5, one_mulVec]
    have d1 (v : Fin g → ℤ) : 4 ∣ v ⬝ᵥ (γ.toBlocks₁₂ᵀ *ᵥ k) :=
      Finset.dvd_sum fun i _ => (hb' i).mul_left _
    have d2 (v : Fin g → ℤ) : 4 ∣ (γ.toBlocks₂₁ᵀ *ᵥ k') ⬝ᵥ v :=
      Finset.dvd_sum fun i _ => (hc' i).mul_right _
    have d3 := d1 (γ.toBlocks₁₁ᵀ *ᵥ k)
    have d4 := d2 n'
    have d5 := d2 (γ.toBlocks₁₂ᵀ *ᵥ k)
    rw [dotProduct_comm] at d5
    rw [e, hn, add_dotProduct]
    nth_rw 1 [hn']
    rw [dotProduct_add]
    omega
  have e2 : eC ((ofRealVec (halfVec k) ⬝ᵥ ofRealVec (halfVec k') -
      ofRealVec (halfVec n) ⬝ᵥ ofRealVec (halfVec n')) / 2) ^ 2 = 1 := by
    have ht' : ((k ⬝ᵥ k' : ℤ) : ℂ) - (n ⬝ᵥ n' : ℤ) = 4 * t := by exact_mod_cast ht
    rw [eC_pow, ← eC_int t]
    congr 1
    simp only [ofRealVec_halfVec, smul_dotProduct, dotProduct_smul, ofIntVec_dot, smul_eq_mul]
    push_cast
    linear_combination ht' / 4
  have e3 : eC (-expArg γ τ z / 2) ^ 2 * eC (expArg γ τ z) = 1 := by
    rw [eC_pow, ← eC_add, ← eC_zero]
    congr 1
    push_cast
    ring
  have key2 := congrArg (· ^ 2) key
  simp only [mul_pow, e1, e2, (hl τ hτ).2] at key2
  linear_combination eC (expArg γ τ z) * key2 -
    theta (halfVec k) (halfVec k') (zAct γ τ z) (spAct γ τ) ^ 2 * e3
end GlobalTheory
