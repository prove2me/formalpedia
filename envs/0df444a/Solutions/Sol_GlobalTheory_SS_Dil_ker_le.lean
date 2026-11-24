-- Prove2me | solution 1 for GlobalTheory.SS.Dil.ker_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:35:47.348032+00:00
-- url     : https://prove2.me/submissions/519fd3cc-ca41-4d7c-8c35-4bb909c77b8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterization
import Theorems.Thm_GlobalTheory_SS_Dil_exists_lift
import Theorems.Thm_GlobalTheory_SS_Dil_gr_add
import Theorems.Thm_GlobalTheory_SS_Dil_gr_sub
import Theorems.Thm_GlobalTheory_SS_Dil_gr_mul
import Theorems.Thm_GlobalTheory_SS_Dil_gr_C
import Theorems.Thm_GlobalTheory_SS_Dil_gr_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Dil
namespace GlobalTheory.SS.Dil
theorem _root_.solution {R B S : Type} {n : ℕ} [CommRing R] [CommRing B] [CommRing S] [Algebra R B] [Algebra B S]
    (q : MvPolynomial (Fin n) R →ₐ[R] B) (hq : Function.Surjective q) (σ : MvPolynomial (Fin n) R →+* S)
    (hσ : ∀ p, σ p = algebraMap B S (q p)) (N : Submodule S (Fin n → S)) (hN : ∀ f, q f = 0 → gr σ f ∈ N)
    (u : Fin n → S) (hu : ∑ i, u i • dd R B S (q (X i)) = 0) : u ∈ N := by
  let D : B → (Fin n → S) ⧸ N := fun b => N.mkQ (gr σ (Function.surjInv hq b))
  have hD : ∀ p, D (q p) = N.mkQ (gr σ p) := by
    intro p
    apply (Submodule.Quotient.eq N).2
    rw [← gr_sub]
    apply hN
    rw [map_sub, Function.surjInv_eq hq, sub_self]
  obtain ⟨l, hl⟩ := exists_lift (R := R) (S := S) D
    (by
      intro x y
      obtain ⟨x, rfl⟩ := hq x; obtain ⟨y, rfl⟩ := hq y
      rw [← map_add, hD, hD, hD, gr_add, map_add])
    (by
      intro x y
      obtain ⟨x, rfl⟩ := hq x; obtain ⟨y, rfl⟩ := hq y
      rw [← map_mul, hD, hD, hD, gr_mul, map_add, map_smul, map_smul, hσ, hσ])
    (by
      intro r
      rw [← q.commutes, hD, algebraMap_eq, gr_C, map_zero])
  have h := congrArg l hu
  rw [map_sum, map_zero] at h
  simp only [map_smul, dd, hl, hD, gr_X] at h
  simp only [← map_smul, ← map_sum] at h
  have h2 : ∑ i, u i • (Pi.single i 1 : Fin n → S) = u := by
    funext j; simp [Pi.single_apply]
  rw [h2] at h
  exact (Submodule.Quotient.mk_eq_zero N).1 h
end GlobalTheory.SS.Dil
