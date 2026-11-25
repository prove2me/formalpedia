-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuDsAd.dsAd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:06:27.176392+00:00
-- url     : https://prove2.me/submissions/b957c0c4-b466-465a-9526-aff7616d6d7c

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DerivedSeriesAdjoint
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuDsAd_ex_mul_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuDsAd_lie_conj
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_differentiableAt
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_cons
import Theorems.Thm_CompanionTheory_D_Upq_Sm_ex_mem_of_lie


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuDsAd
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.BmuDsAd
theorem _root_.solution : DsAd := by
  intro n Hm H _ _ _ σ hσ y hy W hW
  have hyu : IsUnit y := by
    have hyH : yᴴ * Hm * y = Hm := hy
    have h1 : (Hm * yᴴ * Hm) * y = 1 := by
      rw [Matrix.mul_assoc Hm, Matrix.mul_assoc Hm, hyH, hσ.sq]
    exact (Matrix.isUnit_iff_isUnit_det y).2 (Matrix.isUnit_det_of_left_inverse h1)
  have hyH : yᴴ * Hm * y = Hm := hy
  have hL : ∀ W, LieWd Hm W → LieWd Hm (W.map fun X => y⁻¹ * X * y) := by
    intro W hW Z hZ
    obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hZ
    exact lie_conj hyu hyH (hW X hX)
  refine ⟨hL W hW, fun u hu => ?_⟩
  induction W with
  | nil => rfl
  | cons X W ih =>
    have hW' : LieWd Hm W := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    have hX : Lie Hm X := hW X List.mem_cons_self
    have hX' : ∀ t, ex (y⁻¹ * X * y) t ∈ UH Hm := fun t => ex_mem_of_lie (lie_conj hyu hyH hX) t
    have hs : IsSm (UH Hm) σ (dsW σ (W.map fun X => y⁻¹ * X * y) u) :=
      hu.dsW hσ.rep fun Z hZ t => ex_mem_of_lie (hL W hW' Z hZ) t
    rw [List.map_cons, dsW_cons, dsW_cons, ih hW',
      apply_ds hσ.rep hX' hy (hs.differentiableAt hσ.rep hX')]
    unfold ds
    congr 1
    ext t
    rw [← hσ.rep.apply_mul (ex_mem_of_lie hX t) hy, ex_mul_eq hyu]
end GlobalTheory.CompanionTheory.BmuDsAd
