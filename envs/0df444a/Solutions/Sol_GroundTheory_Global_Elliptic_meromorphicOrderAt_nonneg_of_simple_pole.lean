-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.meromorphicOrderAt_nonneg_of_simple_pole
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:54:44.960698+00:00
-- url     : https://prove2.me/submissions/c7e667d7-a480-4558-80e7-d4825f060463

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Theorems.Thm_GroundTheory_Global_Elliptic_Torus_mk_eq_mk_iff
import Theorems.Thm_GroundTheory_Global_Elliptic_degree_ne_one
import Theorems.Thm_GroundTheory_Global_Elliptic_eq_zero_of_finsum_eq_zero_nat
import Theorems.Thm_GroundTheory_Global_Elliptic_finite_support_toNat_neg_torusOrder
import Theorems.Thm_GroundTheory_Global_Elliptic_nonneg_of_toNat_neg_untopD_eq_zero
import Theorems.Thm_GroundTheory_Global_Elliptic_toNat_neg_untopD_eq_zero_of_nonneg
import Theorems.Thm_GroundTheory_Global_Elliptic_torusOrder_mk


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
theorem _root_.solution {f : ℂ → ℂ} (hf : IsEllipticFunction L f)
    {p : ℂ} (hp : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f p)
    (ho : ∀ z, z - p ∉ L.lattice → 0 ≤ meromorphicOrderAt f z) (z : ℂ) :
    0 ≤ meromorphicOrderAt f z := by
  have hdeg : degree L f ≤ 1 := by
    rw [degree, finsum_eq_single _ (Torus.mk L p) (fun x hx ↦ ?_)]
    · rw [torusOrder_mk hf]
      generalize meromorphicOrderAt f p = o at hp
      induction o with
      | top => simp
      | coe n =>
        simp only [WithTop.untopD_coe]
        have : (-1 : ℤ) ≤ n := by exact_mod_cast hp
        omega
    · obtain ⟨y, rfl⟩ := Torus.mk_surjective L x
      rw [torusOrder_mk hf]
      exact toNat_neg_untopD_eq_zero_of_nonneg
        (ho y fun h ↦ hx ((Torus.mk_eq_mk_iff L).2 h))
  have h0 : degree L f = 0 := by
    have := degree_ne_one hf
    omega
  have hall := eq_zero_of_finsum_eq_zero_nat (finite_support_toNat_neg_torusOrder hf) h0
    (Torus.mk L z)
  rw [torusOrder_mk hf] at hall
  exact nonneg_of_toNat_neg_untopD_eq_zero hall
end GroundTheory.Global.Elliptic
