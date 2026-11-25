-- Prove2me | solution 1 for GlobalTheory.LocFlat.PureColPf.Phi_add_colAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:50:54.166406+00:00
-- url     : https://prove2.me/submissions/3b9a8f8e-60d4-44d0-973e-c045ba9ef957

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnIndicatorPureAtSymmetricPosition
import Theorems.Thm_GlobalTheory_LocFlat_PureColPf_coords_entry
import Theorems.Thm_GlobalTheory_LocFlat_PureColPf_mul_pow_lt_of_le
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_Phi_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.PureColPf
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
namespace GlobalTheory.LocFlat.PureColPf
theorem _root_.solution (j c : ℕ) (H : j + 1 + c = s) (r : ℕ) (y : XIx (Fin κ) t (j + 1) → k)
    (hy : y ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ r)⁻¹)
    (z : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) k) :
    (S.T t).Phi j (c + 1) (by omega) (z + colAt (XIx (Fin κ) t j) (c + 1) (r + 1) y) =
      (S.T t).Phi j (c + 1) (by omega) z := by
  let o := stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1) (by omega)
  let o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1 + 1) (by omega)
  have hΦ : ∀ x, (S.T t).Phi j (c + 1) (by omega) x = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      (((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') x).submatrix (ixSucc _ t j) id) := fun _ => rfl
  rw [hΦ, hΦ]
  have e : ((typeFrame S.ϖ o).coords (typeFrame S.ϖ o')
      (z + colAt (XIx (Fin κ) t j) (c + 1) (r + 1) y)).submatrix (ixSucc _ t j) id =
      ((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') z).submatrix (ixSucc _ t j) id +
      ((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') (colAt (XIx (Fin κ) t j) (c + 1) (r + 1) y)).submatrix
        (ixSucc _ t j) id := by
    simp only [LatFrame.coords, Matrix.mul_add, Matrix.add_mul]
    rfl
  rw [e]
  refine TypeDatum.Phi_add _ (S.tame _) _ fun u v => ?_
  change valuation k ((((typeFrame S.ϖ o).bas⁻¹).val * colAt (XIx (Fin κ) t j) (c + 1) (r + 1) y *
    (typeFrame S.ϖ o').bas.val) (o (ixSucc _ t j u)) (o' v)) < 1
  rw [coords_entry]
  generalize o (ixSucc _ t j u) = U
  generalize o' v = V
  rcases U with a | l <;> rcases V with b | q
  · simp [colAt]
  · by_cases hq : q.val = r
    · have := mul_pow_lt_of_le S.unif r (hy a)
      simpa [colAt, hq] using this
    · simp [colAt, hq]
  · simp [colAt]
  · simp [colAt]
end GlobalTheory.LocFlat.PureColPf
