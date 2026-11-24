-- Prove2me | solution 1 for GlobalTheory.JacStages.flatTensorEquiv_tprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:29:11.254365+00:00
-- url     : https://prove2.me/submissions/6834d50c-bd1e-4175-bbd8-912b17cad5c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PiExteriorTensorFlattenedIndexEquivNested
import Theorems.Thm_GlobalTheory_JacStages_flatTensorEquiv_reindex_tprod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages
noncomputable section
open PiTensorProduct Module
open scoped TensorProduct
open GlobalTheory GlobalTheory.JacStages
variable {s : ℕ} {t : Fin s → ℕ}
namespace GlobalTheory.JacStages
theorem _root_.solution (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)]
    [∀ a b, Module ℂ (Y a b)] (x : ∀ p : Σ a, Fin (t a), Y p.1 p.2) :
    flatTensorEquiv Y (tprod ℂ fun c => x (finSigmaFinEquiv.symm c)) =
      tprod ℂ fun a => tprod ℂ fun b => x ⟨a, b⟩ := by
  rw [← flatTensorEquiv_reindex_tprod, reindex_tprod]
end GlobalTheory.JacStages
