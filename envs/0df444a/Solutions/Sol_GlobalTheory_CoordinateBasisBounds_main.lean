-- Prove2me | solution 1 for GlobalTheory.CoordinateBasisBounds.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:15:42.819104+00:00
-- url     : https://prove2.me/submissions/a1045470-8153-43a1-9e32-030e8f1d864e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatMulIntegral
import Theorems.Thm_GlobalTheory_CoordinateBasisBounds_coord_bound
import Theorems.Thm_GlobalTheory_CoordinateBasisBounds_basis_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CoordinateBasisBounds
open NumberField
namespace GlobalTheory.CoordinateBasisBounds
theorem _root_.solution : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), Submodule.FG L → Submodule.span E (↑L : Set (Fin n → E)) = ⊤ → ∃ (N : ℕ), (0 : ℕ) < N ∧ (∀ (j : Fin n), (↑N : E) • Pi.single j (1 : E) ∈ L) ∧ ∀ x ∈ L, ∀ (i : Fin n), ∃ (o : NumberField.RingOfIntegers E), (↑N : E) * x i = (Algebra.algebraMap (NumberField.RingOfIntegers E) E : NumberField.RingOfIntegers E → E) o := by
  intro E _ _ n L hL hspan
  obtain ⟨M, hM, hcoord⟩ := GlobalTheory.CoordinateBasisBounds.coord_bound L hL
  choose d hd hdL using fun j : Fin n => GlobalTheory.CoordinateBasisBounds.basis_bound L hspan (Pi.single j (1 : E))
  refine ⟨M * ∏ j, d j, Nat.mul_pos hM (Finset.prod_pos fun j _ => hd j), ?_, ?_⟩
  · intro j
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ j)
    have e : ((M * ∏ j, d j : ℕ) : E) • Pi.single j (1 : E) = (M * k) • ((d j : E) • Pi.single j (1 : E)) := by
      rw [← Nat.cast_smul_eq_nsmul E, smul_smul, hk]; push_cast; ring_nf
    rw [e]
    exact nsmul_mem (hdL j) _
  · intro x hx i
    obtain ⟨o, ho⟩ := hcoord x hx i
    refine ⟨((∏ j, d j : ℕ) : 𝓞 E) * o, ?_⟩
    rw [map_mul, ← ho, map_natCast]; push_cast; ring
end GlobalTheory.CoordinateBasisBounds
