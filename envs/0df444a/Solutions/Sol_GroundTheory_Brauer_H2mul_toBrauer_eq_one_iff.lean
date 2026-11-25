-- Prove2me | solution 1 for GroundTheory.Brauer.H2mul.toBrauer_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:43:27.748684+00:00
-- url     : https://prove2.me/submissions/59787273-398b-4c5e-b783-d37d9ca30062

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Theorems.Thm_P2M_GroundTheory_Brauer_CrossedProduct_isMulCoboundary__of_mk_eq_one_549104159c63
import Theorems.Thm_P2M_GroundTheory_Brauer_CrossedProduct_mk_eq_one_of_isMulCoboundary__36d289c2feec
import Theorems.Thm_GroundTheory_Brauer_H2mul_toBrauer_mk
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_basis_apply
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
theorem _root_.solution (x : H2mul (L ≃ₐ[K] L) Lˣ) : toBrauer K L x = 1 ↔ x = 1 := by
  induction x using H2mul.induction_on with
  | h c =>
  rw [toBrauer_mk, mk_eq_one_iff]
  exact ⟨CrossedProduct.isMulCoboundary₂_of_mk_eq_one (isMulCocycle₂_of_mem c),
    CrossedProduct.mk_eq_one_of_isMulCoboundary₂ (isMulCocycle₂_of_mem c)⟩
end GroundTheory.Brauer.H2mul
