-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgTransfer.ext_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:49:17.394848+00:00
-- url     : https://prove2.me/submissions/5561fd54-5664-4a3b-b109-bb8843d74cda

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CorrESymmCoe
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_qk_spec
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_ext_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_am_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgTransfer
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {G' : Type} [Group G'] [TopologicalSpace G']
variable {Γ K Q : Subgroup G} {Γ' K' : Subgroup G'} {π : Q →* G'} {ι : G' →* Q} {c₀ : G → ℂ}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [IsTopologicalGroup G]
namespace GlobalTheory.CompanionTheory.RgTransfer
theorem _root_.solution {T : Type} [TopologicalSpace T] (hK : IsCompact (K : Set G))
    (hL : IsLevi Γ K Q Γ' K' π ι c₀) {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ)
    {F : T → G' → E →L[ℂ] fixSp K Q π c₀ ρ} (hF : ∀ t, Equi hL ρ (F t))
    (hc : Continuous fun y : T × G' => F y.1 y.2) :
    Continuous fun y : T × G => ext hL ρ (F y.1) y.2 := by
  have hΦ : Continuous fun y : T × Q × K => (am ρ c₀ π y.2.1 y.2.2).comp (F y.1 (π y.2.1)) := by
    refine ((am_cont hL hρ).comp continuous_snd).clm_comp ?_
    exact hc.comp (continuous_fst.prodMk (hL.contπ.comp (continuous_fst.comp continuous_snd)))
  rw [continuous_iff_continuousAt]
  intro y₀
  rw [ContinuousAt, tendsto_iff_ultrafilter]
  intro U hU
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨k₁, -, hk₁⟩ := isCompact_univ.ultrafilter_le_nhds
    (U.map fun y : T × G => kOf hL y.2) (by simp)
  have hk : Tendsto (fun y : T × G => kOf hL y.2) U (𝓝 k₁) := hk₁
  have hU' : Tendsto (fun y : T × G => y) U (𝓝 y₀) := hU
  have hqG : Tendsto (fun y : T × G => y.2 * ((kOf hL y.2 : K) : G)⁻¹) U (𝓝 (y₀.2 * (k₁ : G)⁻¹)) :=
    ((continuous_snd.tendsto y₀).comp hU').mul
      (((continuous_subtype_val.tendsto k₁).comp hk).inv)
  have hqe : ∀ y : T × G, y.2 * ((kOf hL y.2 : K) : G)⁻¹ = (qOf hL y.2 : G) := by
    intro y
    exact mul_inv_eq_of_eq_mul (qk_spec hL y.2)
  simp only [hqe] at hqG
  have hmem : y₀.2 * (k₁ : G)⁻¹ ∈ Q :=
    hL.par.closed.mem_of_tendsto hqG (Eventually.of_forall fun y => (qOf hL y.2).2)
  have hq : Tendsto (fun y : T × G => qOf hL y.2) U (𝓝 (⟨_, hmem⟩ : Q)) :=
    tendsto_subtype_rng.2 hqG
  have hlim := (hΦ.tendsto (y₀.1, (⟨_, hmem⟩ : Q), k₁)).comp
    ((((continuous_fst.tendsto y₀).comp hU').prodMk_nhds (hq.prodMk_nhds hk)))
  have hy : ext hL ρ (F y₀.1) y₀.2 = (am ρ c₀ π ⟨_, hmem⟩ k₁).comp (F y₀.1 (π ⟨_, hmem⟩)) := by
    rw [← ext_eq hL ρ (hF y₀.1)]
    simp
  rw [hy]
  exact hlim
end GlobalTheory.CompanionTheory.RgTransfer
