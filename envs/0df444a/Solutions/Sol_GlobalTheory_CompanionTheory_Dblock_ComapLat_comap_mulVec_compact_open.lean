-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Dblock.ComapLat.comap_mulVec_compact_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:26:12.043498+00:00
-- url     : https://prove2.me/submissions/0e8af933-d391-4f1a-b763-d3d34b0ed293

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComapMulVecCompactOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Dblock GlobalTheory.CompanionTheory.Dblock.ComapLat
namespace GlobalTheory.CompanionTheory.Dblock.ComapLat
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (g : Matrix (Fin n) (Fin n) k), IsUnit g → ∀ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → IsCompact ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) ∧ IsOpen ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) := by
  intro k _ _ _ _ n g hg A hc ho
  haveI : IsTopologicalRing k := inferInstance
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg
  have hcont : ∀ m : Matrix (Fin n) (Fin n) k, Continuous (fun x : Fin n → k => m.mulVec x) :=
    fun m => continuous_const.matrix_mulVec continuous_id
  have hset : ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k))
      = (fun x : Fin n → k => g.mulVec x) ⁻¹' (A : Set (Fin n → k)) := rfl
  rw [hset]
  refine ⟨?_, ho.preimage (hcont g)⟩
  have himg : (fun x : Fin n → k => g.mulVec x) ⁻¹' (A : Set (Fin n → k))
      = (fun x : Fin n → k => g⁻¹.mulVec x) '' (A : Set (Fin n → k)) := by
    ext x
    constructor
    · intro hx
      refine ⟨g.mulVec x, hx, ?_⟩
      simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g hdet, Matrix.one_mulVec]
    · rintro ⟨y, hy, rfl⟩
      simp only [Set.mem_preimage, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv g hdet,
        Matrix.one_mulVec]
      exact hy
  rw [himg]
  exact hc.image (hcont g⁻¹)
end GlobalTheory.CompanionTheory.Dblock.ComapLat
