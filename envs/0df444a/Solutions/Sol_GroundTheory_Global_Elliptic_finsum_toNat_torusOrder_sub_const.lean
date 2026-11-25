-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.finsum_toNat_torusOrder_sub_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:47:13.175052+00:00
-- url     : https://prove2.me/submissions/e06dc325-ed9d-471d-939b-a4c6984217a0

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ResidueTheorem
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticResidues
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Theorems.Thm_GroundTheory_Global_Elliptic_finite_support_torusOrder
import Theorems.Thm_GroundTheory_Global_Elliptic_finsum_torusOrder_eq_zero
import Theorems.Thm_GroundTheory_Global_Elliptic_toNat_neg_untopD_sub_const

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
theorem _root_.solution {f : ℂ → ℂ} (hf : IsEllipticFunction L f) (c : ℂ) :
    ∑ᶠ x : Torus L, (torusOrder L (fun z ↦ f z - c) x).toNat = degree L f := by
  classical
  have hg : IsEllipticFunction L (fun z ↦ f z - c) := by
    refine ⟨fun z ↦ ?_, fun z l hl ↦ by simp only [hf.2 z l hl]⟩
    have := hf.1 z
    fun_prop
  set g : ℂ → ℂ := fun z ↦ f z - c with hgdef
  have hfin := finite_support_torusOrder hg
  set s := hfin.toFinset with hs
  have hsupp : Function.support (torusOrder L g) ⊆ ↑s := by simp [hs]
  have hsum := finsum_torusOrder_eq_zero hg
  rw [finsum_eq_sum_of_support_subset _ hsupp] at hsum
  have h1 : ∑ᶠ x, (torusOrder L g x).toNat = ∑ x ∈ s, (torusOrder L g x).toNat :=
    finsum_eq_sum_of_support_subset _ fun x hx ↦ hsupp (by
      simp only [Function.mem_support] at hx ⊢
      omega)
  have hpt : ∀ x, (-torusOrder L f x).toNat = (-torusOrder L g x).toNat := fun x ↦
    (toNat_neg_untopD_sub_const (hf.1 _) c).symm
  have h2 : degree L f = ∑ x ∈ s, (-torusOrder L g x).toNat := by
    rw [degree]
    simp_rw [hpt]
    exact finsum_eq_sum_of_support_subset _ fun x hx ↦ hsupp (by
      simp only [Function.mem_support] at hx ⊢
      omega)
  rw [h1, h2]
  have key : ∀ x, ((torusOrder L g x).toNat : ℤ) - ((-torusOrder L g x).toNat : ℤ) =
      torusOrder L g x := fun x ↦ Int.toNat_sub_toNat_neg _
  have : ((∑ x ∈ s, (torusOrder L g x).toNat : ℕ) : ℤ) =
      ((∑ x ∈ s, (-torusOrder L g x).toNat : ℕ) : ℤ) := by
    push_cast
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    simp only [key]
    exact hsum
  exact_mod_cast this
end GroundTheory.Global.Elliptic
