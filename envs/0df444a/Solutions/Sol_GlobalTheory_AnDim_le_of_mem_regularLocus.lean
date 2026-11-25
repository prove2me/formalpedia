-- Prove2me | solution 1 for GlobalTheory.AnDim.le_of_mem_regularLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:46:40.591239+00:00
-- url     : https://prove2.me/submissions/54d47387-9661-4689-9224-27c03eba7439

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__LogResolutionProjectiveLine_09840aae280abe50
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PointDimensionLtProjectiveLine_f9cea2a23bf32842
import Theorems.Thm_GlobalTheory_AnDim_injective_fderiv_of_comp
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
open GlobalTheory
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt Filter Topology
noncomputable section
open GlobalTheory.AnDim
variable {d : ℕ} {X : Type} [TopologicalSpace X]
namespace GlobalTheory.AnDim
theorem _root_.solution {A : FinHolAtlas d X} {T : Set X} {n k : ℕ}
    {U : Set (Fin k → ℂ)} {g : (Fin k → ℂ) → X} {j : Fin A.n} (hU : IsOpen U)
    (hmaps : Set.MapsTo g U (T ∩ (A.chart j).source)) (han : AnalyticOnNhd ℂ (A.chart j ∘ g) U)
    {z : Fin k → ℂ} (hz : z ∈ U) (hinj : Function.Injective (fderiv ℂ (A.chart j ∘ g) z))
    (hreg : g z ∈ regularLocus A T n) : k ≤ n := by
  obtain ⟨-, ψ, ⟨hnd, hψ, hT⟩, hx⟩ := hreg
  have hj := (hmaps hz).2
  have hV : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source) :=
    (A.chart j).symm.isOpen_inter_preimage ψ.open_source
  have hzV : (A.chart j ∘ g) z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩
  have hev : ∀ᶠ w in 𝓝 z, w ∈ U ∧ g w ∈ ψ.source := by
    filter_upwards [hU.mem_nhds hz, (han z hz).continuousAt.preimage_mem_nhds (hV.mem_nhds hzV)]
      with w hw hw'
    exact ⟨hw, by simpa [(A.chart j).left_inv (hmaps hw).2] using hw'.2⟩
  have hH : AnalyticAt ℂ (ψ ∘ g) z := by
    refine (((hψ j).1 _ hzV).comp (han z hz)).congr ?_
    filter_upwards [hev] with w hw
    simp [(A.chart j).left_inv (hmaps hw.1).2]
  have hHinj : Function.Injective (fderiv ℂ (ψ ∘ g) z) := by
    refine injective_fderiv_of_comp (G := A.chart j ∘ ψ.symm) hH.differentiableAt
      ((hψ j).2 _ ⟨ψ.map_source hx, by simpa [ψ.left_inv hx] using hj⟩).differentiableAt ?_ hinj
    filter_upwards [hev] with w hw
    simp [ψ.left_inv hw.2]
  have hzero : ∀ (v : Fin k → ℂ) (i : Fin d), n ≤ (i : ℕ) → fderiv ℂ (ψ ∘ g) z v i = 0 := by
    intro v i hi
    have h1 : (fun w => (ψ ∘ g) w i) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [hev] with w hw
      exact (hT.le ⟨(hmaps hw.1).1, hw.2⟩).2 i hi
    have h2 := h1.fderiv_eq (𝕜 := ℂ)
    rw [fderiv_pi (differentiableAt_pi.1 hH.differentiableAt)]
    simp only [ContinuousLinearMap.pi_apply]
    rw [h2]
    simp
  let M : (Fin k → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Fin.castLE hnd)).comp (fderiv ℂ (ψ ∘ g) z).toLinearMap
  have hM : Function.Injective M := by
    intro v w hvw
    refine hHinj (funext fun i => ?_)
    by_cases hi : (i : ℕ) < n
    · exact congrFun hvw ⟨i, hi⟩
    · rw [hzero v i (not_lt.1 hi), hzero w i (not_lt.1 hi)]
  simpa using LinearMap.finrank_le_finrank_of_injective hM
end GlobalTheory.AnDim
