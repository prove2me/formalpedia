-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.VolK.card_scaled
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:28:00.539724+00:00
-- url     : https://prove2.me/submissions/982f9d06-26b3-4c96-8ad1-af1d4fbf5f78

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureUniformizerMultipleMatricesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureInvertibleIntegralMatrices
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.VolK
namespace GlobalTheory.CompanionTheory.QL.VolK
theorem _root_.solution (q r : ℕ) (hq : 0 < q) :
    (((∏ i : Fin r, (q ^ r - q ^ (i : ℕ)) : ℕ)) : ℝ) * (q : ℝ) ^ (-((r * r : ℕ) : ℤ)) = qE q 1 r := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hq1 : 1 ≤ q := hq
  rw [Fin.prod_univ_eq_prod_range (fun i => q ^ r - q ^ i) r, Nat.cast_prod]
  have h1 : ∀ i ∈ Finset.range r, (((q ^ r - q ^ i : ℕ)) : ℝ)
      = (q : ℝ) ^ r * (1 - (q : ℝ) ^ (-(((r - i : ℕ)) : ℤ))) := by
    intro i hi
    have hi' : i ≤ r := (Finset.mem_range.1 hi).le
    rw [Nat.cast_sub (Nat.pow_le_pow_right hq1 hi'), mul_sub, mul_one]
    push_cast
    congr 1
    rw [← zpow_natCast (q : ℝ) r, ← zpow_add₀ hq0, ← zpow_natCast (q : ℝ) i]
    congr 1
    push_cast [Nat.cast_sub hi']
    ring
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have h2 : ((q : ℝ) ^ r) ^ r * (q : ℝ) ^ (-((r * r : ℕ) : ℤ)) = 1 := by
    rw [← pow_mul, ← zpow_natCast (q : ℝ) (r * r), ← zpow_add₀ hq0]
    simp
  have h3 : ∏ i ∈ Finset.range r, (1 - (q : ℝ) ^ (-(((r - i : ℕ)) : ℤ))) = qE q 1 r := by
    unfold qE
    refine Finset.prod_nbij' (fun i => r - i) (fun s => r - s) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      have := Finset.mem_range.1 hi
      simp only [Finset.mem_Icc]; omega
    · intro s hs
      have := Finset.mem_Icc.1 hs
      simp only [Finset.mem_range]; omega
    · intro i hi
      have := Finset.mem_range.1 hi
      show r - (r - i) = i
      omega
    · intro s hs
      have := Finset.mem_Icc.1 hs
      show r - (r - s) = s
      omega
    · intro i _
      rfl
  rw [h3]
  calc _ = (((q : ℝ) ^ r) ^ r * (q : ℝ) ^ (-((r * r : ℕ) : ℤ))) * qE q 1 r := by ring
    _ = _ := by rw [h2, one_mul]
end GlobalTheory.CompanionTheory.QL.VolK
