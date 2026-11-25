-- Prove2me | solution 1 for GlobalTheory.DimCodim.dim_compl_add_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:39:06.026319+00:00
-- url     : https://prove2.me/submissions/9a3cccfc-8f43-42e8-ad85-5940023966ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClosedComplementDimBound
import Theorems.Thm_GlobalTheory_DimCodim_dim_add_le_of_le_coheight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.DimCodim
namespace GlobalTheory.DimCodim
theorem _root_.solution (X : Scheme.{0}) (U : X.Opens) (d : ℕ)
    (hX : topologicalKrullDim X = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hU : ∀ y : X, ringKrullDim (X.presheaf.stalk y) ≤ 1 → y ∈ U) :
    topologicalKrullDim ((U : Set X)ᶜ : Set X) + 1 ≤ (d : WithBot ℕ∞) := by
  have hc : IsClosed ((U : Set X)ᶜ) := U.isOpen.isClosed_compl
  have : QuasiSober ((U : Set X)ᶜ : Set X) := hc.isClosedEmbedding_subtypeVal.quasiSober
  have key : topologicalKrullDim ((U : Set X)ᶜ : Set X) + ((2 : ℕ∞) : WithBot ℕ∞) ≤
      topologicalKrullDim X := by
    apply dim_add_le_of_le_coheight continuous_subtype_val Subtype.val_injective
    intro w
    have hlt : 1 < ringKrullDim (X.presheaf.stalk w.1) :=
      lt_of_not_ge fun h => w.2 (hU _ h)
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight] at hlt
    have h1 : (1 : ℕ∞) < Order.coheight w.1 := by exact_mod_cast hlt
    have := Order.add_one_le_of_lt h1
    exact le_trans (by norm_num) this
  rw [hX] at key
  generalize topologicalKrullDim ((U : Set X)ᶜ : Set X) = D at key ⊢
  induction D using WithBot.recBotCoe with
  | bot => simp
  | coe m =>
    rw [← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_le_coe] at key
    rw [← WithBot.coe_natCast, ← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe]
    induction m using ENat.recTopCoe with
    | top => exfalso; simp at key
    | coe n =>
      norm_cast at key ⊢
      omega
end GlobalTheory.DimCodim
