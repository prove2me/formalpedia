-- Prove2me | solution 1 for GlobalTheory.SW.neighbours
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:51:52.908213+00:00
-- url     : https://prove2.me/submissions/345ed051-f4eb-4d97-8be9-3a1dafb23a66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Theorems.Thm_GlobalTheory_SW_Nbr_conjI_conjI
import Theorems.Thm_GlobalTheory_SW_Nbr_good_conj
import Theorems.Thm_GlobalTheory_SW_Nbr_agree_of_le
import Theorems.Thm_GlobalTheory_SW_Nbr_nbOf_spec
import Theorems.Thm_GlobalTheory_SW_Nbr_nbOf_mem
import Theorems.Thm_GlobalTheory_SW_Nbr_eq_nbOf
import Theorems.Thm_GlobalTheory_SW_Nbr_nb_symm
import Theorems.Thm_GlobalTheory_SW_Nbr_nb_count
import Theorems.Thm_GlobalTheory_SW_Nbr_herm_move
import Theorems.Thm_GlobalTheory_SW_Nbr_move_inv
import Theorems.Thm_GlobalTheory_SW_Nbr_nb_move

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
open GlobalTheory GlobalTheory.SW
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n M q : ℕ) (P : Ideal (𝓞 E)), 0 < M → GoodPrime M q P → GoodPrime M q (conjI P) ∧ conjI (conjI P) = P ∧ ∀ Λ ∈ Vset E n M, (Nb M P Λ).Finite ∧ (Nb M P Λ).ncard * (q - 1) = q ^ n - 1 ∧ (∀ Λ' ∈ Vset E n M, Λ' ∈ Nb M P Λ ↔ Λ ∈ Nb M (conjI P) Λ') ∧ (∀ Λ₀ : Lt E n, P • Λ ≤ Λ₀ → Λ₀ ≤ Λ → Λ₀.toAddSubgroup.relIndex Λ.toAddSubgroup = q → ∃! Λ', Λ' ∈ Nb M P Λ ∧ Λ ⊓ Λ' = Λ₀) ∧ (∀ Λ' ∈ Nb M P Λ, ∀ m : ℕ, q.Coprime m → Agree m Λ Λ') ∧ ∀ h ∈ DH E n M, ∀ Λ₁ ∈ Vset E n M, Moves h Λ Λ₁ → ∀ Λ' Λ₁' : Lt E n, Moves h Λ' Λ₁' → (Λ' ∈ Nb M P Λ ↔ Λ₁' ∈ Nb M P Λ₁) := by
  intro E _ _ _ n M q P _ hP
  refine ⟨Nbr.good_conj hP, Nbr.conjI_conjI P, fun Λ h => ⟨(Nbr.nb_count hP h).1, (Nbr.nb_count hP h).2,
    fun Λ' h' => ⟨Nbr.nb_symm hP h, fun H => ?_⟩, fun Λ₀ h1 h2 h3 => ?_, fun Λ' h' m hm => ?_,
    fun g hg Λ₁ h₁ hm Λ' Λ₁' hm' => ?_⟩⟩
  · have := Nbr.nb_symm (Nbr.good_conj hP) h' H
    rwa [Nbr.conjI_conjI] at this
  · refine ⟨Nbr.nbOf P Λ₀, ⟨Nbr.nbOf_mem hP h h1 h2 h3, (Nbr.nbOf_spec hP h h1 h2 h3).2⟩, ?_⟩
    rintro Λ' ⟨h', rfl⟩
    exact Nbr.eq_nbOf hP h h'
  · exact Nbr.agree_of_le hP hm h.2.1 h'.1.2.1 h'.2.1
  · have hg' : g * ccT g = 1 := mul_eq_one_comm.1 hg.1
    refine ⟨Nbr.nb_move hP (Nbr.herm_move hg.1) hg' h₁ hm hm',
      Nbr.nb_move hP (fun x y => ?_) hg.1 h (Nbr.move_inv hg' hm) (Nbr.move_inv hg' hm')⟩
    rw [← Nbr.herm_move hg.1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg', Matrix.one_mulVec,
      Matrix.one_mulVec]
end GlobalTheory.SW
