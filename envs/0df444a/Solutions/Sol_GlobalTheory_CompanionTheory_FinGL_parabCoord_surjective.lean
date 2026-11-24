-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinGL.parabCoord_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:31:30.555085+00:00
-- url     : https://prove2.me/submissions/5e8f72db-6149-4066-9382-e5fc2a0ced05

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardParabolicSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinGL
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)
namespace GlobalTheory.CompanionTheory.FinGL
theorem _root_.solution : Function.Surjective (parabCoord K b) := by
  rintro ⟨u, g⟩
  let M : Matrix ι ι K := fun i j =>
    if h : b i < b j then u ⟨(i, j), h⟩
    else if h' : b i = b j then (g (b j)).1 ⟨i, h'⟩ ⟨j, rfl⟩ else 0
  have hM : IsBlockUT K b M := by
    intro i j h
    simp [M, not_lt_of_gt h, h.ne']
  have hT : M.BlockTriangular b := fun i j h => hM i j h
  have hblk : ∀ c, M.toSquareBlock b c = (g c).1 := by
    intro c
    ext ⟨i, hi⟩ ⟨j, hj⟩
    subst hj
    have h0 : ¬ b i < b j := by rw [hi]; exact lt_irrefl _
    show M i j = _
    simp only [M]
    rw [dif_neg h0, dif_pos hi]
  have hdet : M.det ≠ 0 := by
    rw [hT.det]
    refine Finset.prod_ne_zero_iff.mpr fun c _ => ?_
    rw [hblk]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (g c).isUnit).ne_zero
  haveI : Invertible M := Matrix.invertibleOfIsUnitDet M (isUnit_iff_ne_zero.mpr hdet)
  let G : GL ι K := Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet
  have hG : (G : Matrix ι ι K) = M := rfl
  have hGi : IsBlockUT K b ((G⁻¹ : GL ι K) : Matrix ι ι K) := by
    rw [Matrix.coe_units_inv, hG]
    exact fun i j h => Matrix.blockTriangular_inv_of_blockTriangular hT h
  refine ⟨⟨G, hM, hGi⟩, ?_⟩
  refine Prod.ext ?_ ?_
  · funext x
    show M x.1.1 x.1.2 = u x
    simp [M, x.2]
  · funext c
    apply Units.ext
    exact hblk c
end GlobalTheory.CompanionTheory.FinGL
