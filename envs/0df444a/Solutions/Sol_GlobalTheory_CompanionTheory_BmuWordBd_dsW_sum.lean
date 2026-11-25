-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuWordBd.dsW_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:39:38.272935+00:00
-- url     : https://prove2.me/submissions/ec305cec-6673-422b-a58f-2b9d703c8b17

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordLengthBoundOfLinear
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_zero
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuWordBd
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GlobalTheory.CompanionTheory.BmuWordBd
theorem _root_.solution {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] {G : Set (Mat n)}
    {σ : Mat n → (H →L[ℂ] H)} (h : RepOn G σ) {ι : Type*} (s : Finset ι) (v : ι → H)
    (hv : ∀ i, IsSm G σ (v i)) {W : List (Mat n)} (hW : LieW G W) :
    IsSm G σ (∑ i ∈ s, v i) ∧ dsW σ W (∑ i ∈ s, v i) = ∑ i ∈ s, dsW σ W (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨IsSm.zero, by simpa using dsW_smul h (IsSm.zero (G := G) (σ := σ)) (0 : ℂ) hW⟩
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨(hv a).add ih.1, by rw [dsW_add h (hv a) ih.1 hW, ih.2]⟩
end GlobalTheory.CompanionTheory.BmuWordBd
