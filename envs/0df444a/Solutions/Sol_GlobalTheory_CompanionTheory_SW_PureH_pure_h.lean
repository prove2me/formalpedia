-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PureH.pure_h
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:14:03.238818+00:00
-- url     : https://prove2.me/submissions/15b1dfbf-9acf-4318-9e70-45330fd196b2

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneDetHermitianGram
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupProjections
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeStableAlmostEverywhere
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryFiniteSetDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PureH_pureL_act
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PureH_pureL_act_vec
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_block_alg
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_components
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatRat_latV_rational
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PureH
namespace GlobalTheory.CompanionTheory.SW.PureH
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [DecidableEq (HeightOneSpectrum (𝓞 F))] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), ∀ h : HA (AF F) σ (blockOne (algebraMap F E t) J), ∃ (ginf : HA (Ainf F) σ (blockOne (algebraMap F E t) J)) (g : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ (blockOne (algebraMap F E t) J)) (Sh : Finset (HeightOneSpectrum (𝓞 F))), ∀ S, S₁ ⊆ S → (∀ (n : ℕ) (φinf : (Fin (n + 1) → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (X : Fin n → Fin M → AF F ⊗[F] E), pureL b S φinf φ (actW (AF F) σ _ h (consTup X)) = pureL b (S ∪ Sh) (fun Y => φinf (actW (Ainf F) σ _ ginf (consTup Y))) (fun v Y => if v ∈ S then φ v (actW (Fv F v) σ _ (g v) (consTup Y)) else (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (consTup Y))) X) ∧ ∀ (Ψinf : (Fin 1 → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞), pureL b S Ψinf Ψ (actW (AF F) σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) = (Ψinf (actW (Ainf F) σ _ ginf (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) * ∏ v ∈ S, Ψ v (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) * ∏ v ∈ Sh \ S, (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) := by
  intro F E _ _ _ _ _ _ σ hCM M J hJ t ht d b
  have hba := GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg F E σ hCM M J t
  have hJ' : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hba.2.1 hJ.1, by
      rw [hba.1]
      exact mul_ne_zero ((map_ne_zero _).2 ht) hJ.2⟩
  obtain ⟨pinf, p, hcomp, hlat, -⟩ := GlobalTheory.CompanionTheory.SW.HProj.components F E σ hCM (M + 1) _ hJ'
  have hcons := (GlobalTheory.CompanionTheory.SW.LatRat.latV_rational F E σ hCM d b 0 M).2.2
  let S₁ : Finset (HeightOneSpectrum (𝓞 F)) := (Filter.eventually_cofinite.1 hcons).toFinset
  refine ⟨S₁, fun h => ?_⟩
  have hlat' := hlat d b h
  let Sh : Finset (HeightOneSpectrum (𝓞 F)) := (Filter.eventually_cofinite.1 hlat').toFinset
  have hSh : ∀ v, v ∉ Sh → ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → Fv F v ⊗[F] E),
      actW (Fv F v) σ _ (p v h) X ∈ latV b v ↔ X ∈ latV b v := fun v hv => by
    simpa [Sh] using hv
  refine ⟨pinf h, fun v => p v h, Sh, fun S hS => ?_⟩
  have hS' : ∀ v, v ∉ S → ∀ X₀ : Fin 0 → Fin M → Fv F v ⊗[F] E, consTup X₀ ∈ latV b v := by
    intro v hv X₀
    have hv₁ : v ∉ S₁ := fun hm => hv (hS hm)
    have : ∀ X : Fin 0 → Fin M → Fv F v ⊗[F] E, consTup X ∈ latV b v ↔ X ∈ latV b v := by
      simpa [S₁] using hv₁
    exact (this X₀).2 fun a => a.elim0
  have hinf := fun (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E) => (hcomp n h X).1
  have hfin := fun (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F)) =>
    (hcomp n h X).2 v
  exact ⟨fun n φinf φ X => pureL_act b σ _ h (pinf h) (fun v => p v h) S Sh hinf hfin hSh hS' φinf φ X,
    fun Ψinf Ψ => pureL_act_vec b σ _ h (pinf h) (fun v => p v h) S Sh hinf hfin hSh hS' Ψinf Ψ⟩
end GlobalTheory.CompanionTheory.SW.PureH
