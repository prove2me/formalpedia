-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.rho_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:57:36.059839+00:00
-- url     : https://prove2.me/submissions/dc891750-8f6c-41b6-bf2b-aa0872a2c5e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteIntegralClosureOfSeparableInvolutionAlgebrStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInjectiveTorusClassesOfIdempotentDecomposiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RhoPowLowerBoundSwappedPairs
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_finite_rhoSet
import Theorems.Thm_GlobalTheory_T_exists_injective_torus_classes_of_idempotent_decomposition


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι) (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S → ∀ k : ℕ, (k + 1) ^ (Fintype.card ι - S.card) ≤ B.rho (algebraMap K.O B.A a ^ k) := by
  intro K B ι _ e π S a hsep ha hF k
  classical
  have hfin := finite_rhoSet K B hsep a ha k
  obtain ⟨f, hf, hint⟩ := GlobalTheory.T.exists_injective_torus_classes_of_idempotent_decomposition K B ι e S a ha hF.1 k
  let g : ({i // i ∉ S} → Fin (k + 1)) → {c : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T //
      IsIntegral K.O ((((Quotient.out c : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)} :=
    fun n => ⟨f n, hint n⟩
  have hg : Function.Injective g := fun n n' h => hf (congrArg Subtype.val h)
  have h := Nat.card_le_card_of_injective g hg
  unfold InvAlg.rho
  refine le_trans (le_of_eq ?_) h
  rw [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl, Fintype.card_coe]
end GlobalTheory.UnitLemma.Desc
