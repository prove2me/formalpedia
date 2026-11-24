-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.Emb.card_one_eq_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:52:02.652855+00:00
-- url     : https://prove2.me/submissions/230055e0-d826-412a-9dea-c62fd9e0db3d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardOrthonormalFramesHermitianSpaceStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsHermitianCongrToOneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardHermitianRepresentationsResidue
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_gram_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.Emb
variable {E : Type} [CommRing E] {τ : E →+* E}
namespace GlobalTheory.CompanionTheory.UnrDens.Emb
theorem _root_.solution (hτ : ∀ a, τ (τ a) = a) {m n : ℕ} (S : Matrix (Fin m) (Fin m) E)
    (hS : cT τ S = S) (hd : IsUnit S.det) :
    Nat.card {y : Matrix (Fin m) (Fin n) E // cT τ y * S * y = 1} =
      Nat.card {x : Fin n → (Fin m → E) //
        ∀ i j, (HermSp.ofMatrix hτ S hS hd).h (x i) (x j) = if i = j then 1 else 0} := by
  refine Nat.card_congr ⟨fun y => ⟨fun j a => y.1 a j, ?_⟩,
    fun x => ⟨Matrix.of (fun a j => x.1 j a), ?_⟩, ?_, ?_⟩
  · intro i j
    have h := gram_apply hτ S hS hd y.1 j i
    rw [y.2, Matrix.one_apply] at h
    rw [← h]
    simp only [eq_comm]
  · ext i j
    rw [gram_apply hτ S hS hd, Matrix.one_apply]
    have h := x.2 j i
    simp only [eq_comm (a := i)]
    exact h
  · intro y
    apply Subtype.ext
    ext a j
    rfl
  · intro x
    apply Subtype.ext
    funext j a
    rfl
end GlobalTheory.CompanionTheory.UnrDens.Emb
