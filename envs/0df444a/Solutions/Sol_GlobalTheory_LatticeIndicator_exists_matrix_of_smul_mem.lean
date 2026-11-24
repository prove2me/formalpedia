-- Prove2me | solution 1 for GlobalTheory.LatticeIndicator.exists_matrix_of_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:38:41.625835+00:00
-- url     : https://prove2.me/submissions/ac5797be-f2df-47a9-bf5d-4e7bc3ece438

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsEqSumIndicatorOfRightInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
open GlobalTheory.LatticeIndicator
namespace GlobalTheory.LatticeIndicator
theorem _root_.solution {O m : Type*} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [Fintype m] [DecidableEq m] {c : O} (hc : c ≠ 0)
    (L : Submodule O (m → O)) (hL : ∀ v, c • v ∈ L) :
    ∃ h : Matrix m m O, h.det ≠ 0 ∧ ∀ v, v ∈ L ↔ ∃ u, v = h *ᵥ u := by
  have hrk : Module.finrank O L = Fintype.card m := by
    apply le_antisymm
    · simpa using L.finrank_le
    · have := LinearMap.finrank_le_finrank_of_injective
        (f := LinearMap.codRestrict L (c • LinearMap.id) hL) (fun v v' h =>
          smul_right_injective _ hc (congrArg Subtype.val h))
      simpa using this
  let b : Module.Basis m O L :=
    (Module.finBasisOfFinrankEq O L hrk).reindex (Fintype.equivFin m).symm
  let h : Matrix m m O := Matrix.of fun i j => (b j : m → O) i
  have hmul : ∀ u : m → O, h *ᵥ u = ((∑ j, u j • b j : L) : m → O) := by
    intro u
    ext i
    simp [h, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hiff : ∀ v, v ∈ L ↔ ∃ u, v = h *ᵥ u := by
    intro v
    refine ⟨fun hv => ⟨b.repr ⟨v, hv⟩, ?_⟩, ?_⟩
    · rw [hmul, b.sum_repr]
    · rintro ⟨u, rfl⟩
      rw [hmul]
      exact Subtype.property _
  refine ⟨h, ?_, hiff⟩
  choose u hu using fun j : m => (hiff _).1 (hL (Pi.single j 1))
  have : h * Matrix.of (fun i j => u j i) = c • (1 : Matrix m m O) := by
    ext i j
    have := congrFun (hu j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply]
      using this.symm
  have hd := congrArg Matrix.det this
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at hd
  intro h0
  rw [h0, zero_mul] at hd
  exact pow_ne_zero _ hc hd.symm
end GlobalTheory.LatticeIndicator
