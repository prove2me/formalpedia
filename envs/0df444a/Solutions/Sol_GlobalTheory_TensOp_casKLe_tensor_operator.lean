-- Prove2me | solution 1 for GlobalTheory.TensOp.casKLe_tensor_operator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:33:01.398485+00:00
-- url     : https://prove2.me/submissions/b3b9b6c8-0992-49a6-b204-294e8f3ece17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ReInnerLeOnImageOfIntertwiningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumNormAddSqLeOfBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CasKIsSymmetricAndFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CompactCasimirLeTensorOperatorRaise
import Theorems.Thm_GlobalTheory_TensOp_core
import Theorems.Thm_GlobalTheory_T_casK_isSymmetric_and_inner_re_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.TensOp
namespace GlobalTheory.TensOp
theorem _root_.solution : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N ι : Type) [NormedAddCommGroup N] [InnerProductSpace ℂ N] [Fintype ι] [DecidableEq ι] (F : Fin n → Fin n → Module.End ℂ N) (φ : ι → M →ₗ[ℂ] N) (A : Fin n → Fin n → Matrix ι ι ℂ) (c s : ℝ), KUnit ε E → KUnit ε F → 0 ≤ c → 0 ≤ s → (∀ a b, ε a = ε b → (A a b).conjTranspose = A b a) → (∀ x : ι → M, ∑ a, ∑ b, (if ε a = ε b then ∑ i, ‖∑ j, A a b i j • x j‖ ^ 2 else 0) ≤ s ^ 2 * ∑ j, ‖x j‖ ^ 2) → (∀ a b, ε a = ε b → ∀ j w, F a b (φ j w) = φ j (E a b w) + ∑ i, A a b i j • φ i w) → ∀ w, CasKLe ε E c w → ∀ j, CasKLe ε F (c + s) (φ j w) := by
  intro M _ _ n ε E N ι _ _ _ _ F φ A c s hE hF hc hs hA hAs hφ w hw j
  obtain ⟨S, hfd, hst, hwS, hb⟩ := hw
  let E' : Fin n → Fin n → Module.End ℂ S := fun a b =>
    if h : ε a = ε b then (E a b).restrict (hst a b h) else 0
  have hE' : ∀ a b, ε a = ε b → ∀ x : S, (E' a b x : M) = E a b x := by
    intro a b h x
    simp [E', h]
  have := core S n ε E' N ι F (fun i => (φ i).comp S.subtype) A c s ?_ hF hc hs hA ?_ ?_ ?_ ⟨w, hwS⟩ j
  · exact this
  · intro a b h x y
    rw [Submodule.coe_inner, Submodule.coe_inner, hE' a b h, hE' b a h.symm, hE a b h]
  · intro x
    have h := hAs (fun i => (x i : M))
    simpa only [Submodule.coe_norm, Submodule.coe_sum, Submodule.coe_smul] using h
  · intro a b h i x
    simp [hE' a b h, hφ a b h]
  · intro x
    have h := hb x x.2
    rw [(GlobalTheory.T.casK_isSymmetric_and_inner_re_eq _ n ε E hE).2] at h
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs with hab
    · rw [← hE' a b hab]; rfl
    · rfl
end GlobalTheory.TensOp
