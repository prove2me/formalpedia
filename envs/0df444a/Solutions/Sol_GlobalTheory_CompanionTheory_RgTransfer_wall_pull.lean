-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgTransfer.wall_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:06:48.57242+00:00
-- url     : https://prove2.me/submissions/58bfec51-59e1-4682-9bfa-0adbb079004e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CorrESymmCoe
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_ext_cont
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_ext_bdd
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_conv_pull
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_summable_eis
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_eis_pull
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_leftGood_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_hOf_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_ht_left

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
variable {A A' B B' : Type} [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup A']
  [NormedSpace ℂ A'] [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup B']
  [NormedSpace ℂ B']
variable {P₁ P₂ : Subgroup G} {P₁' P₂' : Subgroup G'} {c : G → ℂ} {c' : G' → ℂ}
  {η₁ η₂ β : G → ℝ} {η₁' η₂' β' : G' → ℝ}
namespace GlobalTheory.CompanionTheory.RgTransfer
theorem _root_.solution [IsTopologicalGroup G] [LocallyCompactSpace G] [FiniteDimensional ℂ W]
    (hK : IsCompact (K : Set G)) (hL : IsLevi Γ K Q Γ' K' π ι c₀) {ρ : K →* (W →L[ℂ] W)}
    (hρ : Continuous ρ) (hP₁ : IsPull Q P₁ P₁' π c₀ c c') (hP₂ : IsPull Q P₂ P₂' π c₀ c c')
    (hpar₁ : IsPar Γ' K' P₁' c') (hpar₂ : IsPar Γ' K' P₂' c')
    (hη₁ : IsHt Γ' K' P₁' η₁') (hη₂ : IsHt Γ' K' P₂' η₂') (hβ : IsHt Γ' K' P₂' β')
    (hp₁ : PullHt K Q π η₁ η₁') (hp₂ : PullHt K Q π η₂ η₂') (hpβ : PullHt K Q π β β')
    (law₁ : Law K P₁ c ρ) (law₂ : Law K P₂ c ρ) (law₁' : Law K' P₁' c' (resRep hL ρ))
    (law₂' : Law K' P₂' c' (resRep hL ρ)) {M₁ M₂ : ℝ}
    (bd₁ : ∀ g (w : fixSp K Q π c₀ ρ), ‖sec K' P₁' c' (resRep hL ρ) g w‖ ≤ M₁ * ‖w‖)
    (bd₂ : ∀ g (w : fixSp K Q π c₀ ρ), ‖sec K' P₂' c' (resRep hL ρ) g w‖ ≤ M₂ * ‖w‖)
    {L : Submodule ℂ W} {L' : Submodule ℂ (fixSp K Q π c₀ ρ)} (hLL : Corr ρ L L')
    (hC₁ : Corr ρ (secSp K P₁ c ρ) (secSp K' P₁' c' (resRep hL ρ)))
    (hC₂ : Corr ρ (secSp K P₂ c ρ) (secSp K' P₂' c' (resRep hL ρ)))
    {R : ℝ} {D : ℂ → ℂ} {Op' : ℂ → (L' →L[ℂ] secSp K' P₂' c' (resRep hL ρ))}
    {H' : ℂ → G' → (L' →L[ℂ] fixSp K Q π c₀ ρ)}
    (hw : Wall Γ' K' P₁' P₂' c' η₁' η₂' β' (resRep hL ρ) L' R D Op' H')
    (hE : ∀ z (g : G') (k : K') (w : L'), H' z (g * k) w = resRep hL ρ k⁻¹ (H' z g w)) :
    Wall (Γ ⊓ Q) K P₁ P₂ c η₁ η₂ β ρ L R D (fun z => cj (corrE hLL) (corrE hC₂) (Op' z))
      (hOf hL ρ (corrE hLL) H') := by
  haveI : CompleteSpace (fixSp K Q π c₀ ρ) := FiniteDimensional.complete ℂ _
  have hle : ∀ w : L, (w : W) ∈ secSp K P₁ c ρ := by
    intro w
    obtain ⟨h1, h2⟩ := (hLL w).1 w.2
    exact (hC₁ w).2 ⟨h1, hw.le h2⟩
  have hpull : ∀ {η : G → ℝ} {η' : G' → ℝ}, PullHt K Q π η η' → ∀ (q : Q) (k : K),
      η ((q : G) * k) = η' (π q) := fun h q k => h q k k.2
  refine ⟨fun w hw' => hle ⟨w, hw'⟩, hw.pos, fun x hx => ?_, fun x hx => ?_, hw.dEnt, hw.dNe, ?_, fun g => ?_, ?_,
    fun b a g => ?_, fun z hz g w => ?_, fun z hz g w => ?_⟩
  · refine conv_pull hL hP₁ (l' := fun g => x * η₁' g) (fun q k => ?_) (fun γ hγ hγP y => ?_)
      (hw.convR x hx)
    · simp only [hpull hp₁ q k]
    · simp only [ht_left hη₁ hγ hγP y]
  · refine conv_pull hL hP₂ (l' := fun g => β' g - x * η₂' g) (fun q k => ?_) (fun γ hγ hγP y => ?_)
      (hw.convL x hx)
    · simp only [hpull hp₂ q k, hpull hpβ q k]
    · simp only [ht_left hη₂ hγ hγP y, ht_left hβ hγ hγP y]
  · exact leftGood_comp (cj (corrE hLL) (corrE hC₂)) hw.op
  · let T : (L' →L[ℂ] fixSp K Q π c₀ ρ) →L[ℂ] (L →L[ℂ] W) :=
      (ContinuousLinearMap.compL ℂ L _ W (am ρ c₀ π (qOf hL g) (kOf hL g))).comp
        ((ContinuousLinearMap.compL ℂ L L' _).flip (corrE hLL : L →L[ℂ] L'))
    exact T.differentiable.comp (hw.hol (π (qOf hL g)))
  · refine ext_cont hK hL hρ (F := fun z g' => (H' z g').comp (corrE hLL : L →L[ℂ] L'))
      (fun z g m x => hE z g m _) ?_
    exact hw.cont.clm_comp continuous_const
  · refine ext_bdd hK hL hρ {z : ℂ | b ≤ z.re ∧ z.re ≤ a}
      (fun z g' => (H' z g').comp (corrE hLL : L →L[ℂ] L')) (fun g' => ?_) g |>.imp ?_
    · obtain ⟨U, hU, M, hM⟩ := hw.bdd b a g'
      refine ⟨U, hU, M * ‖(corrE hLL : L →L[ℂ] L')‖, fun t ht x hx => ?_⟩
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      exact mul_le_mul_of_nonneg_right (hM t ht.1 ht.2 x hx) (norm_nonneg _)
    · rintro U ⟨hU, M, hM⟩
      exact ⟨hU, M, fun z h1 h2 g' hg' => hM z ⟨h1, h2⟩ g' hg'⟩
  · obtain ⟨q, k, rfl⟩ := exists_qk hL g
    have hv := hw.le (corrE hLL w).2
    have hs := summable_eis (Λ := fun x => z * η₁' x) (l := fun x => z.re * η₁' x) bd₁
      (fun g => by simp) (hw.convR z.re hz) (π q) ((corrE hLL w : L') : fixSp K Q π c₀ ρ)
    have := eis_pull (Λ := fun x => z * η₁ x) (Λ' := fun x => z * η₁' x) hL hP₁ hpar₁ law₁ law₁'
      (fun q k => by simp only [hpull hp₁ q k]) (fun γ hγ hγP y => by simp only [ht_left hη₁ hγ hγP y])
      hv (hle w) q k hs
    rw [hOf_eq hL ρ _ hE, hw.eqR z hz, map_smul]
    exact congrArg (fun u => D z • u) this.symm
  · obtain ⟨q, k, rfl⟩ := exists_qk hL g
    have hv := (Op' z (corrE hLL w)).2
    have hs := summable_eis (Λ := fun x => (β' x : ℂ) - z * η₂' x) (l := fun x => β' x - z.re * η₂' x)
      bd₂ (fun g => by simp) (hw.convL z.re hz) (π q)
      ((Op' z (corrE hLL w) : secSp K' P₂' c' (resRep hL ρ)) : fixSp K Q π c₀ ρ)
    have := eis_pull (Λ := fun x => (β x : ℂ) - z * η₂ x) (Λ' := fun x => (β' x : ℂ) - z * η₂' x) hL hP₂
      hpar₂ law₂ law₂'
      (fun q k => by simp only [hpull hp₂ q k, hpull hpβ q k])
      (fun γ hγ hγP y => by simp only [ht_left hη₂ hγ hγP y, ht_left hβ hγ hγP y])
      hv (cj (corrE hLL) (corrE hC₂) (Op' z) w).2 q k hs
    rw [hOf_eq hL ρ _ hE, hw.eqL z hz]
    exact this.symm
end GlobalTheory.CompanionTheory.RgTransfer
