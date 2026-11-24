-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.MeasProj.proj_props
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:09:23.039923+00:00
-- url     : https://prove2.me/submissions/9498a17e-256a-4254-9a82-caf6a31a1da0

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjections
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_MeasProj_continuous_mapTup
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_MeasProj_continuous_fstA
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_MeasProj_continuous_sndA
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_MeasProj_continuous_evalV
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_MeasProj_isCompact_latV
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_MeasProj_isOpen_latV
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_MeasProj_isOpen_intOff
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_MeasProj_eventually_mem_latV
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_MeasProj_ext_proj
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_MeasProj_exists_glue
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_MeasProj_continuous_sizeTup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.MeasProj
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.MeasProj
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), Continuous (projInf : (Fin n → Fin M → AF F ⊗[F] E) → _) ∧ Continuous (projFin : (Fin n → Fin M → AF F ⊗[F] E) → _) ∧ (∀ v, Continuous (projV v : (Fin n → Fin M → Af F ⊗[F] E) → _)) ∧ (∀ v, IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) ∧ IsOpen (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E))) ∧ (∀ S, IsOpen (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E))) ∧ (∀ X : (Fin n → Fin M → Af F ⊗[F] E), ∀ᶠ v in Filter.cofinite, projV v X ∈ latV b v) ∧ (∀ X Y : (Fin n → Fin M → AF F ⊗[F] E), projInf X = projInf Y → (∀ v, projV v (projFin X) = projV v (projFin Y)) → X = Y) ∧ (∀ (Y : (Fin n → Fin M → Ainf F ⊗[F] E)) (Z : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ᶠ v in Filter.cofinite, Z v ∈ latV b v) → ∃ X : (Fin n → Fin M → AF F ⊗[F] E), projInf X = Y ∧ ∀ v, projV v (projFin X) = Z v) ∧ Continuous (sizeTup b : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ) := by
  intro F E _ _ _ _ _ σ _ d b n M
  exact ⟨continuous_mapTup b (fstA F) continuous_fstA, continuous_mapTup b (sndA F) continuous_sndA,
    fun v => continuous_mapTup b (evalV F v) (continuous_evalV v),
    fun v => ⟨isCompact_latV b v, isOpen_latV b v⟩, fun S => isOpen_intOff b S,
    fun X => eventually_mem_latV b X, fun X Y => ext_proj b X Y,
    fun Y Z h => exists_glue b Y Z h, continuous_sizeTup b⟩
end GlobalTheory.CompanionTheory.SW.MeasProj
