-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselCutLim.tendsto_dsW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:01:28.983857+00:00
-- url     : https://prove2.me/submissions/9f36c207-baa0-4a4a-be10-04eee45e5001

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TruncatedDerivationLimit
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselCutLim_tendsto_cut
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselCutLim_integrable_conj_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselCutLim_lieW_of
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_continuousOn
import Theorems.Thm_CompanionTheory_D_Upq_Sm_contDiff_Lx
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_hasCompactSupport_LW


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff InnerProductSpace ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BesselCutLim
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Hm : Mat n}
  {σ : Mat n → (H →L[ℂ] H)}
namespace GlobalTheory.CompanionTheory.BesselCutLim
theorem _root_.solution (hD : CutDer) (hσ : URep Hm σ) {μ : Measure (PI.MtM n)} (hμ : PI.IsHaarOnM (UH Hm) μ)
    {w : H} (hw : IsSm (UH Hm) σ w)
    (hi : ∀ v, IsSm (UH Hm) σ v → Integrable (fun y : PI.MtM n => ⟪v, σ (Matrix.of y) w⟫_ℂ) μ) {κ : ℂ}
    (hκ : ∀ v, IsSm (UH Hm) σ v →
      ∫ y : PI.MtM n, conj ⟪v, σ (Matrix.of y) w⟫_ℂ • σ (Matrix.of y) w ∂μ = κ • v)
    (W : List (Mat n)) : LieWd Hm W → ∀ ρ : Mat n → ℝ, ContDiff ℝ ∞ ρ → HasCompactSupport ρ →
      ∀ v, IsSm (UH Hm) σ v →
      Tendsto (fun N : ℕ => dsW σ W (cutI σ μ w ((N : ℝ) + 1) ρ v)) atTop (𝓝 ((ρ 0 : ℂ) • κ • dsW σ W v)) := by
  induction W using List.reverseRecOn with
  | nil =>
    intro _ ρ hρ hc v hv
    have h1 := integrable_conj_smul hσ.grp.1 hμ.2.2.1 (hi v hv) (g := fun x => σ x w)
      (SmOn.continuousOn hw) (K := ‖w‖) fun x hx => (hσ.iso x hx w).le
    have h2 := tendsto_cut h1 hρ.continuous hc
    rw [hκ v hv] at h2
    simpa only [dsW, List.foldr_nil, cutI, mul_smul] using h2
  | append_singleton W X ih =>
    intro hWX ρ hρ hc v hv
    have hW : LieWd Hm W := fun Y hY => hWX Y (List.mem_append_left _ hY)
    have hX : Lie Hm X := hWX X (by simp)
    have hX' : LieWd Hm [X] := fun Y hY => by rw [List.mem_singleton.1 hY]; exact hX
    have hv' : IsSm (UH Hm) σ (ds σ X v) := hv.dsW hσ.rep (lieW_of hX')
    have hρ' := contDiff_Lx X hρ
    have hc' : HasCompactSupport (Lx X ρ) := hasCompactSupport_LW hc [X]
    have e : ∀ u, dsW σ (W ++ [X]) u = dsW σ W (ds σ X u) := fun u => by
      simp only [dsW, List.foldr_append, List.foldr_cons, List.foldr_nil]
    have h1 := (ih hW _ hρ' hc' v hv).add (ih hW ρ hρ hc _ hv')
    have h0 : Lx X ρ 0 = 0 := by simp [Lx]
    rw [h0, Complex.ofReal_zero, zero_smul, zero_add] at h1
    rw [e]
    refine h1.congr fun N => ?_
    have hR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    rw [e, (hD n Hm H σ hσ μ hμ w hw _ hR ρ hρ hc v hv).2 X hX,
      dsW_add hσ.rep (hD n Hm H σ hσ μ hμ w hw _ hR _ hρ' hc' v hv).1
        (hD n Hm H σ hσ μ hμ w hw _ hR ρ hρ hc _ hv').1 (lieW_of hW)]
end GlobalTheory.CompanionTheory.BesselCutLim
