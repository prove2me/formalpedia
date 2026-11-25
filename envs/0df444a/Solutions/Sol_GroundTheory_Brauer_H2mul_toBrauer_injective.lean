-- Prove2me | solution 1 for GroundTheory.Brauer.H2mul.toBrauer_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:21:27.599686+00:00
-- url     : https://prove2.me/submissions/7a5c29a5-a5f0-41cc-a8a7-2598fe1c7342

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Theorems.Thm_P2M_GroundTheory_Brauer_CrossedProduct_isMulCoboundary__div_of_algEquiv_eec8390b77bb
import Theorems.Thm_GroundTheory_Brauer_nonempty_algEquiv_of_isBrauerEquivalent
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_nonempty_algEquiv_of_isBrauerEquivalent
import Theorems.Thm_GroundTheory_Brauer_H2mul_toBrauer_mk
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_basis_apply
import Theorems.Thm_GroundTheory_Brauer_H2mul_mk_eq_mk_iff
import Theorems.Thm_GroundTheory_Brauer_H2mul_mulEquivH2_mk
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_of_val
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_val_of
import Theorems.Thm_GroundTheory_Brauer_tensorCSA_carrier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Brauer.CrossedProduct.basis_apply
attribute [local simp] GroundTheory.Brauer.H2mul.mulEquivH2_mk
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.of_val
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.val_of
attribute [local simp] GroundTheory.Brauer.tensorCSA_carrier


attribute [local simp] GroundTheory.Brauer.H2mul.toBrauer_mk

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Brauer
open groupCohomology
universe u v
open GroundTheory.Brauer.H2mul
variable (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable {K L}
namespace GroundTheory.Brauer.H2mul
theorem _root_.solution : Function.Injective (toBrauer K L) := by
  intro x y hxy
  induction x using H2mul.induction_on with
  | h c =>
  induction y using H2mul.induction_on with
  | h c' =>
  rw [toBrauer_mk, toBrauer_mk] at hxy
  obtain ⟨e⟩ := CrossedProduct.nonempty_algEquiv_of_isBrauerEquivalent
    (isMulCocycle₂_of_mem c) (isMulCocycle₂_of_mem c') (Quotient.exact hxy)
  exact (mk_eq_mk_iff c c').2 (CrossedProduct.isMulCoboundary₂_div_of_algEquiv _ _ e)
end GroundTheory.Brauer.H2mul
