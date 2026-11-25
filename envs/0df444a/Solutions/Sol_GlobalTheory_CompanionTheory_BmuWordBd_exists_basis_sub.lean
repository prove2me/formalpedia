-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuWordBd.exists_basis_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:43:30.501825+00:00
-- url     : https://prove2.me/submissions/2e23ee29-d43e-4610-a45f-b4a66a1e65eb

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordLengthBoundOfLinear

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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : Submodule ℝ E) :
    ∃ (N : ℕ) (b : Fin N → E) (κ : ℝ), 0 ≤ κ ∧ (∀ i, b i ∈ S) ∧
      ∀ X, X ∈ S → ∃ c : Fin N → ℝ, X = ∑ i, c i • b i ∧ ∀ i, |c i| ≤ κ * ‖X‖ := by
  let bS := Module.finBasis ℝ S
  let L : Fin (Module.finrank ℝ S) → (S →L[ℝ] ℝ) := fun i => LinearMap.toContinuousLinearMap (bS.coord i)
  refine ⟨Module.finrank ℝ S, fun i => (bS i : E), ∑ i, ‖L i‖,
    Finset.sum_nonneg (fun i _ => norm_nonneg _), fun i => (bS i).2, ?_⟩
  intro X hX
  refine ⟨fun i => bS.repr ⟨X, hX⟩ i, ?_, ?_⟩
  · calc X = ((⟨X, hX⟩ : S) : E) := rfl
      _ = ((∑ i, bS.repr ⟨X, hX⟩ i • bS i : S) : E) := by rw [bS.sum_repr]
      _ = ∑ i, bS.repr ⟨X, hX⟩ i • (bS i : E) := by simp only [Submodule.coe_sum, Submodule.coe_smul]
  · intro i
    have h1 : |bS.repr ⟨X, hX⟩ i| ≤ ‖L i‖ * ‖X‖ := by
      have := (L i).le_opNorm ⟨X, hX⟩
      simpa [L, Real.norm_eq_abs] using this
    have h2 : ‖L i‖ ≤ ∑ j, ‖L j‖ := Finset.single_le_sum (fun j _ => norm_nonneg (L j)) (Finset.mem_univ i)
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
end GlobalTheory.CompanionTheory.BmuWordBd
