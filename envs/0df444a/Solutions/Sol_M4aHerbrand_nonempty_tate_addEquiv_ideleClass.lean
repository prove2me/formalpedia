-- Prove2me | solution 1 for M4aHerbrand.nonempty_tate_addEquiv_ideleClass
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/9ccd99a1-8444-5c7f-b7eb-957920b81bd3

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Theorems.Thm_Rep_nonempty_tate_addEquiv_elementwise
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_nonempty_tate_addEquiv_ideleClass

set_option autoImplicit false
set_option maxSynthPendingDepth 3
universe u v w

theorem solution
    {R E F : Type*} [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
    [Algebra R F] [IsFractionRing R F] [Algebra E F] [Fintype (F ≃ₐ[E] F)]
    (D : M4aHerbrand.IdeleGaloisDescent R E F) (σ : F ≃ₐ[E] F) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
    [MulDistribMulAction (F ≃ₐ[E] F) (M4aHerbrand.IdeleClassGroup R F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : M4aHerbrand.IdeleClassGroup R F), g • c = D.classAct g c) :
    Nonempty ((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (M4aHerbrand.IdeleClassGroup R F)).tateH0 ≃+
      Additive ((M4aHerbrand.ideleClassDerive D σ).ker ⧸
        (M4aHerbrand.ideleClassNorm D).range.subgroupOf (M4aHerbrand.ideleClassDerive D σ).ker)) ∧
    Nonempty ((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (M4aHerbrand.IdeleClassGroup R F)).tateHneg1 ≃+
      Additive ((M4aHerbrand.ideleClassNorm D).ker ⧸
        (M4aHerbrand.ideleClassDerive D σ).range.subgroupOf (M4aHerbrand.ideleClassNorm D).ker)) ∧
    Nat.card (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (M4aHerbrand.IdeleClassGroup R F)).tateH0 = Nat.card ((M4aHerbrand.ideleClassDerive D σ).ker ⧸
        (M4aHerbrand.ideleClassNorm D).range.subgroupOf (M4aHerbrand.ideleClassDerive D σ).ker) ∧
    Nat.card (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (M4aHerbrand.IdeleClassGroup R F)).tateHneg1 = Nat.card ((M4aHerbrand.ideleClassNorm D).ker ⧸
        (M4aHerbrand.ideleClassDerive D σ).range.subgroupOf (M4aHerbrand.ideleClassNorm D).ker) := by
  classical
  have hD : ∀ c : M4aHerbrand.IdeleClassGroup R F, M4aHerbrand.ideleClassDerive D σ c = σ • c / c := fun c => by
    rw [hact, div_eq_mul_inv]; rfl
  have hN : ∀ c : M4aHerbrand.IdeleClassGroup R F, M4aHerbrand.ideleClassNorm D c = ∏ τ : F ≃ₐ[E] F, τ • c := fun c => by
    have hi : Fintype.ofFinite (F ≃ₐ[E] F) = ‹Fintype (F ≃ₐ[E] F)› := Subsingleton.elim _ _
    show (@Finset.prod (F ≃ₐ[E] F) _ _ (@Finset.univ _ (Fintype.ofFinite (F ≃ₐ[E] F))) fun τ => D.classAct τ c) = _
    rw [hi]
    exact Finset.prod_congr rfl fun τ _ => (hact τ c).symm
  obtain ⟨⟨e0⟩, ⟨e1⟩⟩ := Rep.nonempty_tate_addEquiv_elementwise σ hσ (M4aHerbrand.ideleClassDerive D σ)
    (M4aHerbrand.ideleClassNorm D) hD hN
  exact ⟨⟨e0⟩, ⟨e1⟩, Nat.card_congr e0.toEquiv, Nat.card_congr e1.toEquiv⟩

end S_M4aHerbrand_nonempty_tate_addEquiv_ideleClass
end P2MW
export P2MW.S_M4aHerbrand_nonempty_tate_addEquiv_ideleClass (solution)
