-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.gram_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:39.004065+00:00
-- url     : https://prove2.me/submissions/e97bd1f0-85e6-4da8-8d48-8fe90f06fe04

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens
variable {E : Type} [CommRing E] {τ : E →+* E}
variable {V : Type} [AddCommGroup V] [Module E V]
namespace GlobalTheory.CompanionTheory.UnrDens
theorem _root_.solution (hτ : ∀ a, τ (τ a) = a) {m n : ℕ} (S : Matrix (Fin m) (Fin m) E)
    (hS : cT τ S = S) (hd : IsUnit S.det) (x : Matrix (Fin m) (Fin n) E) (i j : Fin n) :
    (cT τ x * S * x) i j = (HermSp.ofMatrix hτ S hS hd).h (fun a => x a j) (fun a => x a i) := by
  show (cT τ x * S * x) i j = dotProduct (fun a => τ (x a i)) (S.mulVec (fun a => x a j))
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end GlobalTheory.CompanionTheory.UnrDens
