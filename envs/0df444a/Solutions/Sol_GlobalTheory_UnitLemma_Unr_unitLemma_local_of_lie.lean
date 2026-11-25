-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.unitLemma_local_of_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:25:14.345704+00:00
-- url     : https://prove2.me/submissions/efb11f44-d399-44d9-b95c-eb802a1eb973

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnramifiedOddDegreeQuadraticLocalExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayleyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedBaseChangeLatticeCountEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetInvAlgBaseChangeUnramifiedOddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SeparableCharpolyInvAlgBaseChangeUnramifiedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValResultantEqDegreeMulUnramifiedExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardResidueFieldAdjoinUnitaryProdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnramifiedInvolutionFieldEmbeddingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyOverExtIntegralReductionPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaLocalOddResidueOfLieAlgebra
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_prodEquiv_isIso
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_prod_unitary
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_prod_integral
import Theorems.Thm_GlobalTheory_T_card_residueField_adjoin_unitary_prod
import Theorems.Thm_GlobalTheory_T_charpoly_overExt_integral_reduction_pow
import Theorems.Thm_GlobalTheory_T_eta_gramDet_invAlgBaseChangeUnramified_odd
import Theorems.Thm_GlobalTheory_T_exists_unramified_involution_field_embedding
import Theorems.Thm_GlobalTheory_T_exists_unramified_odd_degree_quadratic_local_ext
import Theorems.Thm_GlobalTheory_T_separable_charpoly_invAlgBaseChangeUnramified
import Theorems.Thm_GlobalTheory_T_unitLemma_residually_unipotent_via_cayley
import Theorems.Thm_GlobalTheory_T_unramifiedBaseChange_latticeCount_eq
import Theorems.Thm_GlobalTheory_T_val_resultant_eq_degree_mul_unramifiedExt
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_IsIso_N_eq
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_IsIso_charpoly_eq_of_isIso
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_prod_P


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution : UnitLemmaLie → ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) → InvAlg.Identity B₁ B₂ := by
  intro hL K hK B₁ B₂ hu₁ hu₂ hsep hi₁ hi₂ hl
  have hsepP : (B₁.prod B₂).P.Separable := by rw [Orbit.prod_P]; exact hsep
  have huP := prod_unitary B₁ B₂ hu₁ hu₂
  have hiP := prod_integral B₁ B₂ hi₁ hi₂
  obtain ⟨d, hd, hcard⟩ := GlobalTheory.T.card_residueField_adjoin_unitary_prod K hK B₁ B₂ hu₁ hu₂ hsep hi₁ hi₂ hl
  obtain ⟨K', φ, hq, hc, hv, hodd, hfin, hz⟩ := GlobalTheory.T.exists_unramified_odd_degree_quadratic_local_ext K d hd
  have hU : IsUnrExt K K' d φ := ⟨hq, hc, hv, hodd, hfin⟩
  obtain ⟨ψ, hψ, hσ, hO, s, hs, hres⟩ := GlobalTheory.T.exists_unramified_involution_field_embedding K hK (B₁.prod B₂) huP hsepP hiP hl d hcard K' φ hU hz
  obtain ⟨Q, hQ1, hQ2⟩ := GlobalTheory.T.charpoly_overExt_integral_reduction_pow K K' d φ hU (B₁.prod B₂) ψ hψ hσ hO hl hsepP hiP s hres
  have hiso := prodEquiv_isIso φ B₁ B₂ ψ hψ hσ
  set ψ₁ := (RingHom.fst B₁.A B₂.A).comp ψ with hψ₁
  set ψ₂ := (RingHom.snd B₁.A B₂.A).comp ψ with hψ₂
  have h₁ : ∀ e, ψ₁ (φ e) = algebraMap K.E B₁.A e := fun e => congrArg Prod.fst (hψ e)
  have h₁' : ∀ e, B₁.σ (ψ₁ e) = ψ₁ (K'.c e) := fun e => congrArg Prod.fst (hσ e)
  have h₂ : ∀ e, ψ₂ (φ e) = algebraMap K.E B₂.A e := fun e => congrArg Prod.snd (hψ e)
  have h₂' : ∀ e, B₂.σ (ψ₂ e) = ψ₂ (K'.c e) := fun e => congrArg Prod.snd (hσ e)
  set C₁ := overExt φ B₁ ψ₁ h₁ h₁' with hC₁
  set C₂ := overExt φ B₂ ψ₂ h₂ h₂' with hC₂
  have hPP : C₁.P * C₂.P = (overExt φ (B₁.prod B₂) ψ hψ hσ).P := by
    rw [← Orbit.prod_P, ← hiso.charpoly_eq_of_isIso]
  have hO₁ : ∀ y : K'.O, ψ₁ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B₁.g} : Set B₁.A) := by
    intro y
    have key : ∀ w ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A),
        (w : B₁.A × B₂.A).1 ∈ Algebra.adjoin K.O ({B₁.g} : Set B₁.A) := by
      intro w hw
      induction hw using Algebra.adjoin_induction with
      | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact Algebra.self_mem_adjoin_singleton _ _
      | algebraMap a => exact Subalgebra.algebraMap_mem _ a
      | add x z _ _ hx hz => exact add_mem hx hz
      | mul x z _ _ hx hz => exact mul_mem hx hz
    exact key _ (hO y)
  have hO₂ : ∀ y : K'.O, ψ₂ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B₂.g} : Set B₂.A) := by
    intro y
    have key : ∀ w ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A),
        (w : B₁.A × B₂.A).2 ∈ Algebra.adjoin K.O ({B₂.g} : Set B₂.A) := by
      intro w hw
      induction hw using Algebra.adjoin_induction with
      | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact Algebra.self_mem_adjoin_singleton _ _
      | algebraMap a => exact Subalgebra.algebraMap_mem _ a
      | add x z _ _ hx hz => exact add_mem hx hz
      | mul x z _ _ hx hz => exact mul_mem hx hz
    exact key _ (hO y)
  have hO' : ∀ y : K'.O, (ψ₁.prod ψ₂) (algebraMap K'.O K'.E y) ∈
      Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A) := fun y => hO y
  have hQ : ∃ Q : K'.O[X], Q.map (algebraMap K'.O K'.E) = C₁.P * C₂.P ∧
      Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O (s : K'.O))) ^ Q.natDegree :=
    ⟨Q, hQ1.trans hPP.symm, hQ2⟩

  have hsep' : (C₁.P * C₂.P).Separable := by
    rw [hPP]
    exact GlobalTheory.T.separable_charpoly_invAlgBaseChangeUnramified K K' d φ hU (B₁.prod B₂) ψ hψ hσ hsepP
  have hId := GlobalTheory.T.unitLemma_residually_unipotent_via_cayley hL K' (hodd hK) C₁ C₂ hu₁ hu₂ hsep' s hs hQ

  have hst : ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e)
      (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)),
      (∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) →
      (overExt φ B ψ hψ hσ).stSum = B.stSum := by
    intro B ψ hψ hσ hO'
    unfold InvAlg.stSum
    exact finsum_congr fun k => GlobalTheory.T.unramifiedBaseChange_latticeCount_eq K K' d φ hU B ψ hψ hσ hO' _
  have hkap : InvAlg.kapSum C₁ C₂ = InvAlg.kapSum B₁ B₂ := by
    unfold InvAlg.kapSum
    refine finsum_congr fun k => ?_
    have hN : (C₁.prod C₂).N k.rep = (B₁.prod B₂).N k.rep := by
      rw [← hiso.N_eq]
      exact GlobalTheory.T.unramifiedBaseChange_latticeCount_eq K K' d φ hU (B₁.prod B₂) ψ hψ hσ hO _
    rw [hN]
    congr 1
    set x := (Quot.out k).1 with hx
    have hfix : B₁.σ ((x : (C₁.prod C₂).A).1) = (x : (C₁.prod C₂).A).1 := congrArg Prod.fst (Quot.out k).2
    let x₁ : B₁.Aˣ := Units.map (MonoidHom.fst B₁.A B₂.A) x
    have := GlobalTheory.T.eta_gramDet_invAlgBaseChangeUnramified_odd K K' d φ hU hd B₁ ψ₁ h₁ h₁' x₁ hfix
    exact this
  have hres' := GlobalTheory.T.val_resultant_eq_degree_mul_unramifiedExt K K' d φ hU hd B₁ B₂ ψ₁ ψ₂ h₁ h₁' h₂ h₂' hO' hsep s hQ
  unfold InvAlg.Identity at hId ⊢
  rw [hkap, hst B₁ ψ₁ h₁ h₁' hO₁, hst B₂ ψ₂ h₂ h₂' hO₂] at hId
  rw [← hId, hres', hq]
  congr 1
  obtain ⟨m, rfl⟩ := hd
  push_cast
  rw [show -((2 * (m : ℤ) + 1) * val K'.O (resultant C₁.P C₂.P)) =
      (2 * (m : ℤ) + 1) * (-val K'.O (resultant C₁.P C₂.P)) by ring, zpow_mul]
  congr 1
  rw [show (2 * (m : ℤ) + 1) = ((2 * m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, Odd.neg_pow ⟨m, rfl⟩]
end GlobalTheory.UnitLemma.Unr
