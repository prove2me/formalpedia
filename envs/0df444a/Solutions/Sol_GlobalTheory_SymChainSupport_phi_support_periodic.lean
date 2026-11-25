-- Prove2me | solution 1 for GlobalTheory.SymChainSupport.phi_support_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:26:14.731257+00:00
-- url     : https://prove2.me/submissions/e94df1ed-f171-4baa-94a9-6a3310a0ce03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainPhiSupportPeriodic
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_Phi_add
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_intM_of_Phi_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.SymChainSupport
namespace GlobalTheory.SymChainSupport
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (j c : ℕ) (H : j + c = s) (x z : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k), ((S.T t).Phi j c H x ≠ 0 → IntM ((embA (XIx (Fin κ) t (j + 1)) (GlobalTheory.SplitFlip.diagGL fun i : Fin c => S.ϖ ^ (i.val + 1)))⁻¹.val * x * (embA (XIx (Fin κ) t j) (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => S.ϖ ^ (i.val + 1))).val)) ∧ (MaxM ((embA (XIx (Fin κ) t (j + 1)) (GlobalTheory.SplitFlip.diagGL fun i : Fin c => S.ϖ ^ (i.val + 1)))⁻¹.val * z * (embA (XIx (Fin κ) t j) (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => S.ϖ ^ (i.val + 1))).val) → (S.T t).Phi j c H (x + z) = (S.T t).Phi j c H x) := by
  intro k _ _ _ _ s κ S t _ _ j c H x z
  set o := stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega)
  set o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega)
  set F := typeFrame (k := k) S.ϖ o
  set F' := typeFrame (k := k) S.ϖ o'
  have hPhi : ∀ y, (S.T t).Phi j c H y = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      ((F.coords F' y).submatrix (ixSucc _ t j) id) := fun y => rfl
  constructor
  · intro hx i l
    rw [hPhi] at hx
    have := TypeDatum.intM_of_Phi_ne_zero _ _ hx ((ixSucc _ t j).symm (o.symm i)) (o'.symm l)
    simpa [LatFrame.coords, F, F', typeFrame] using this
  · intro hz
    rw [hPhi, hPhi]
    have e : F.coords F' (x + z) = F.coords F' x + F.coords F' z := by
      unfold LatFrame.coords; rw [Matrix.mul_add, Matrix.add_mul]; rfl
    rw [e]
    exact TypeDatum.Phi_add _ (S.tame _) _ (y := (F.coords F' z).submatrix (ixSucc _ t j) id) fun _ _ => hz _ _
end GlobalTheory.SymChainSupport
