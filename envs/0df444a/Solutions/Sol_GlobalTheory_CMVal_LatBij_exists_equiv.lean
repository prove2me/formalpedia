-- Prove2me | solution 1 for GlobalTheory.CMVal.LatBij.exists_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:29:30.470701+00:00
-- url     : https://prove2.me/submissions/176ae988-a600-49f1-8a88-a444ea5073d6

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdelicRingClassLatticeOneEqOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmRingClassOrderUnitsEqMaxRealSubfieldUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLatticePointsIntegralIdelesEquiv
import Theorems.Thm_GlobalTheory_CMVal_LatBij_toIdele_surjective
import Theorems.Thm_GlobalTheory_CMVal_LatBij_toIdele_injective
import Theorems.Thm_GlobalTheory_T_cmRingClassOrder_units_eq_maxRealSubfield_units
import Theorems.Thm_GlobalTheory_T_idelicRingClassLattice_one_eq_order


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.LatBij
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.LatBij
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 c : Ideal (OF E)), IsBaseCond 𝔣 → 𝔣 ∣ c → c ≠ ⊥ →
    ∃ e : (Σ q : PicO c, modUnits (lattice c q.out)) ≃
      {z : (Af E)ˣ ⧸ hatOUnits c // ∃ y : (Af E)ˣ, (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits c) = z ∧ (y : Af E) ∈ hatO c},
      ∀ p, ∀ y : (Af E)ˣ, (y : Af E) = algebraMap E (Af E) (p.2.1.out) * (((Quotient.out p.1 : (Af E)ˣ)⁻¹ : (Af E)ˣ) : Af E) →
        (e p).1 = QuotientGroup.mk y := by
  intro E _ _ _ 𝔣 c h𝔣 hc hc0
  refine ⟨Equiv.ofBijective (toIdele c) ⟨toIdele_injective c (GlobalTheory.T.idelicRingClassLattice_one_eq_order E c hc0) (GlobalTheory.T.cmRingClassOrder_units_eq_maxRealSubfield_units E 𝔣 c h𝔣 hc),
    toIdele_surjective c⟩, fun p y hy => ?_⟩
  have : y = diag (rep p.2) * p.1.out⁻¹ := Units.ext hy
  rw [this]
  rfl
end GlobalTheory.CMVal.LatBij
