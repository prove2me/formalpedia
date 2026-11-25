-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuQBound.factor_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:01:44.040251+00:00
-- url     : https://prove2.me/submissions/ca66d9de-3a3f-49ee-a8fd-b1d3408fe8c6

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuotientBoundOfFactorReduceChart
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuQBound
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GlobalTheory.CompanionTheory.BmuQBound
theorem _root_.solution {n : ℕ} {H V ι : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup V] [NormedSpace ℂ V] {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
    (h : RepOn G σ) (B : H → V) (g : ι → Mat n) (c : ι → (V →L[ℂ] V)) (hg : ∀ j, g j ∈ G)
    (hc : ∀ j v, IsSm G σ v → B (σ (g j) v) = c j (B v)) (v : H) (hv : IsSm G σ v) :
    ∀ l : List ι, (l.map g).prod ∈ G ∧ B (σ (l.map g).prod v) = (l.map c).prod (B v) := by
  intro l
  induction l with
  | nil =>
    refine ⟨h.one_mem, ?_⟩
    simp [h.map_one]
  | cons a l ih =>
    obtain ⟨hP, hBP⟩ := ih
    simp only [List.map_cons, List.prod_cons]
    refine ⟨h.mul_mem _ (hg a) _ hP, ?_⟩
    rw [h.apply_mul (hg a) hP, hc a _ (IsSm.apply h hv hP), hBP, ContinuousLinearMap.mul_apply]
end GlobalTheory.CompanionTheory.BmuQBound
