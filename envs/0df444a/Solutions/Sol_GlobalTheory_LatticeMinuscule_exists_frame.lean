-- Prove2me | solution 1 for GlobalTheory.LatticeMinuscule.exists_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:57:45.777835+00:00
-- url     : https://prove2.me/submissions/e5d25ba2-871d-4768-bd32-595487e7ad76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsMulEqMulDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeElementaryDivisors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.LatticeMinuscule
open Matrix
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {n : ℕ}
namespace GlobalTheory.LatticeMinuscule
theorem _root_.solution [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K]
    (Λ : Submodule R (Fin n → K)) (hfg : Λ.FG)
    (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) :
    ∃ C : Matrix (Fin n) (Fin n) K, IsUnit C.det ∧
      ∀ y, y ∈ Λ ↔ ∃ z : Fin n → R, y = C.mulVec (fun i => algebraMap R K (z i)) := by
  haveI : Submodule.IsLattice K Λ := ⟨hfg, hsp⟩
  have hr : Module.finrank R Λ = n := by
    rw [Submodule.IsLattice.finrank_of_pi K Λ, Fintype.card_fin]
  let b : Module.Basis (Fin n) R Λ := Module.finBasisOfFinrankEq R Λ hr
  have key : ∀ z : Fin n → R,
      ((Pi.basisFun K (Fin n)).toMatrix (b.extendOfIsLattice K)).mulVec
        (fun i => algebraMap R K (z i)) = ((∑ j, z j • b j : Λ) : Fin n → K) := by
    intro z
    funext i
    simp [Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, Algebra.smul_def, mul_comm]
  refine ⟨(Pi.basisFun K (Fin n)).toMatrix (b.extendOfIsLattice K), ?_, fun y => ⟨?_, ?_⟩⟩
  · rw [← Module.Basis.det_apply]; exact Module.Basis.isUnit_det _ _
  · intro hy
    refine ⟨b.repr ⟨y, hy⟩, ?_⟩
    rw [key, b.sum_repr]
  · rintro ⟨z, rfl⟩
    rw [key]
    exact Subtype.prop _
end GlobalTheory.LatticeMinuscule
