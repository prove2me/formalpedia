-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuIwa.adapted_pq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:01:38.353294+00:00
-- url     : https://prove2.me/submissions/9a874640-f32d-4ecd-ad5e-0a498ba51dc6

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IwasawaDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuIwa_pq_val
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuIwa_bq_eq
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuIwa
open Matrix CompanionTheory.Bmu CompanionTheory.D.gk.admitted.CholeskyDecomposition Formalism.QuantumDeterminants
open scoped ComplexOrder MatrixOrder
namespace GlobalTheory.CompanionTheory.BmuIwa
theorem _root_.solution (k r : ℕ) : Adapted (pq k r) (bq k r) (fun _ => 1) where
  invol i := by
    apply Fin.ext
    have := i.2
    rw [pq_val, pq_val]
    split_ifs <;> omega
  mono i j hij := by
    have h : i.val ≤ j.val := hij
    rw [bq_eq, bq_eq]
    split_ifs <;> omega
  neg i := by
    have := i.2
    rw [bq_eq, bq_eq, pq_val]
    split_ifs <;> omega
  fix i hi := by
    apply Fin.ext
    have := i.2
    rw [bq_eq] at hi
    rw [pq_val]
    split_ifs at hi ⊢ <;> omega
  inj i j hi hij := by
    apply Fin.ext
    rw [bq_eq] at hi
    rw [bq_eq, bq_eq] at hij
    split_ifs at hi hij <;> omega
  sq _ := by simp
  star_eq _ := by simp
  symm _ := rfl
  mid _ _ _ _ := rfl
end GlobalTheory.CompanionTheory.BmuIwa
