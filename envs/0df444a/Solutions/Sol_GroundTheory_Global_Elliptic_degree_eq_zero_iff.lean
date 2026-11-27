-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.degree_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:46:04.125928+00:00
-- url     : https://prove2.me/submissions/f62ab07f-50f9-4205-ac93-eda198a74f94

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ResidueTheorem
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticResidues
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Theorems.Thm_GroundTheory_Global_Elliptic_torusOrder_mk
import Theorems.Thm_GroundTheory_Global_Elliptic_nonneg_of_toNat_neg_untopD_eq_zero
import Theorems.Thm_GroundTheory_Global_Elliptic_toNat_neg_untopD_eq_zero_of_nonneg
import Theorems.Thm_GroundTheory_Global_Elliptic_eventually_nhdsNE_of_eventually_codiscrete
import Theorems.Thm_GroundTheory_Global_Elliptic_finite_support_toNat_neg_torusOrder
import Theorems.Thm_GroundTheory_Global_Elliptic_eq_zero_of_finsum_eq_zero_nat
import Theorems.Thm_GroundTheory_Global_Elliptic_exists_eventuallyEq_const_of_meromorphicOrderAt_nonneg


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
theorem _root_.solution {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    degree L f = 0 ↔ ∃ c : ℂ, f =ᶠ[codiscrete ℂ] fun _ ↦ c := by
  constructor
  · intro h0
    have hall := eq_zero_of_finsum_eq_zero_nat (finite_support_toNat_neg_torusOrder hf) h0
    apply exists_eventuallyEq_const_of_meromorphicOrderAt_nonneg L hf.1 hf.2
    intro z
    have := hall (Torus.mk L z)
    rw [torusOrder_mk hf] at this
    exact nonneg_of_toNat_neg_untopD_eq_zero this
  · rintro ⟨c, hc⟩
    rw [degree]
    have : ∀ x : Torus L, (-torusOrder L f x).toNat = 0 := by
      intro x
      apply toNat_neg_untopD_eq_zero_of_nonneg
      rw [meromorphicOrderAt_congr (eventually_nhdsNE_of_eventually_codiscrete hc x.out)]
      exact analyticAt_const.meromorphicOrderAt_nonneg
    simp [this]
end GroundTheory.Global.Elliptic
