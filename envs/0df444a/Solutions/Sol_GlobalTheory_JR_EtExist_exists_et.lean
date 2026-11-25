-- Prove2me | solution 1 for GlobalTheory.JR.EtExist.exists_et
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:02:16.252875+00:00
-- url     : https://prove2.me/submissions/22d0cc98-2689-40f0-8680-074389029352

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyCompactModuleTopology
import Theorems.Thm_GlobalTheory_JR_EtExist_exists_field
import Theorems.Thm_GlobalTheory_JR_EtExist_exists_isGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtExist
variable (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable (K : Type) [CommRing K] [Algebra F K]
namespace GlobalTheory.JR.EtExist
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [GlobalTheory.JR.Unram F E],
    (∃ A : GlobalTheory.JR.Et F E, IsField A.K ∧ IsField A.L ∧ Module.finrank F A.K = 1) ∧
    ∀ (r : ℕ) (p : Fin r → F),
      (Polynomial.X ^ r + ∑ i, Polynomial.C (p i) * Polynomial.X ^ (i : ℕ) : Polynomial F).Separable →
      ∃ (A : GlobalTheory.JR.Et F E) (τ : A.K), A.IsGen τ p :=
  fun F E _ _ _ _ _ => ⟨exists_field F E, exists_isGen F E⟩
end GlobalTheory.JR.EtExist
