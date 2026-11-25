-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.degree_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:12:12.071635+00:00
-- url     : https://prove2.me/submissions/bbc27caa-5ffb-4181-b240-c2435ebf235d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ResidueTheorem
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticResidues
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Theorems.Thm_GroundTheory_Global_Elliptic_nonneg_of_toNat_neg_untopD_eq_zero
import Theorems.Thm_GroundTheory_Global_Elliptic_eq_neg_one_of_toNat_neg_untopD_eq_one
import Theorems.Thm_GroundTheory_Global_Elliptic_finite_support_toNat_neg_torusOrder
import Theorems.Thm_GroundTheory_Global_Elliptic_finsum_torusResidue_eq_zero
import Theorems.Thm_GroundTheory_Global_Elliptic_residue_eq_zero_of_meromorphicOrderAt_nonneg
import Theorems.Thm_GroundTheory_Global_Elliptic_residue_ne_zero_of_meromorphicOrderAt_eq_neg_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {f : ℂ → ℂ} (hf : IsEllipticFunction L f) : degree L f ≠ 1 := by
  classical
  intro h1
  set u : Torus L → ℕ := fun x ↦ (-torusOrder L f x).toNat with hu
  have hfin : (Function.support u).Finite := finite_support_toNat_neg_torusOrder hf
  set s := hfin.toFinset with hs
  have hsum : ∑ x ∈ s, u x = 1 := by
    rw [← finsum_eq_sum_of_support_subset u (by simp [hs])]
    exact h1
  obtain ⟨x₀, hx₀s, hx₀⟩ : ∃ x₀ ∈ s, u x₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [Finset.sum_eq_zero hcon] at hsum
    exact zero_ne_one hsum
  have hsplit := Finset.add_sum_erase s u hx₀s
  rw [hsum] at hsplit
  have hux₀ : u x₀ = 1 := by omega
  have hrest : ∀ x, x ≠ x₀ → u x = 0 := by
    intro x hx
    by_cases hxs : x ∈ s
    · have h0 : ∑ y ∈ s.erase x₀, u y = 0 := by omega
      exact Finset.sum_eq_zero_iff.1 h0 x (Finset.mem_erase.2 ⟨hx, hxs⟩)
    · simpa [hs] using hxs
  have hres := finsum_torusResidue_eq_zero hf
  rw [finsum_eq_single _ x₀ (fun x hx ↦ ?_)] at hres
  · have hord := eq_neg_one_of_toNat_neg_untopD_eq_one hux₀
    exact residue_ne_zero_of_meromorphicOrderAt_eq_neg_one (hf.1 _) hord hres
  · exact residue_eq_zero_of_meromorphicOrderAt_nonneg (hf.1 _)
      (nonneg_of_toNat_neg_untopD_eq_zero (hrest x hx))
end GroundTheory.Global.Elliptic
