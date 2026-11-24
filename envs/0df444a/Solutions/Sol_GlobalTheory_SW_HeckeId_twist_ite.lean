-- Prove2me | solution 1 for GlobalTheory.SW.HeckeId.twist_ite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:27:19.762512+00:00
-- url     : https://prove2.me/submissions/6fff7dfe-c4cf-45f4-b2da-e8afff057372

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
import Theorems.Thm_GlobalTheory_SW_TwistAdm_cols_of_cond
import Theorems.Thm_GlobalTheory_SW_TwistAdm_exists_mult
import Theorems.Thm_GlobalTheory_SW_TwistAdm_twist_eq
import Theorems.Thm_GlobalTheory_SW_TwistAdm_twist_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeckeId
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
open Nbr
variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
namespace GlobalTheory.SW.HeckeId
theorem _root_.solution {M R s : ℕ} {φ : Fam E n N} {Y : Lt E N} (hφ : admitted M R φ)
    (hA : Agree (R * M) Y (stdL E N)) {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M)
    (x : Matrix (Fin n) (Fin N) E) (hs : s ≡ 1 [MOD R ^ 2])
    (h : ∀ v ∈ stdL E N, (s : E) • v ∈ Y) : twist R Y φ Λ x =
      if ∀ ξ ∈ Y, (R : E) • (x *ᵥ ξ) ∈ Λ then φ Λ ((s : E) • x) else 0 := by
  split_ifs with h1
  · exact TwistAdm.twist_val hφ hA hΛ x s hs h1 (TwistAdm.cols_of_cond h h1)
  · rw [TwistAdm.twist_eq φ (TwistAdm.exists_mult hφ.pos.2 hA), if_neg h1]
end GlobalTheory.SW.HeckeId
