-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThetaUD.term_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:54:53.737928+00:00
-- url     : https://prove2.me/submissions/44b70cee-dc6c-4e83-b0fe-0eaf85759bfc

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ThetaFunctionModularity
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThetaUD_gauss_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThetaUD
variable {F : Type} [Field F] [NumberField F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.SW.ThetaUD
theorem _root_.solution (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ)
    (φ : (ι → A F) → ℂ) (τ : InfinitePlace F → ℂ) (a : F) (x : ι → F) :
    thTerm B ρ P gf gi (opD 1 (algebraMap F (A F) a) φ) (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) x =
      thTerm B ρ P gf gi φ τ (a • x) := by
  unfold thTerm opD
  rw [gauss_sq B ρ P τ (fun w => ρ w a)]
  have h1 : (algebraMap F (A F) a • gf *ᵥ fun j => algebraMap F (A F) (x j)) =
      gf *ᵥ fun j => algebraMap F (A F) ((a • x) j) := by
    rw [← Matrix.mulVec_smul]
    congr 1
    funext j
    simp
  have h2 : (fun w => ρ w a • gi w *ᵥ fun j => ρ w (x j)) =
      fun w => gi w *ᵥ fun j => ρ w ((a • x) j) := by
    funext w
    rw [← Matrix.mulVec_smul]
    congr 1
    funext j
    simp
  rw [h1, h2]
  simp
end GlobalTheory.CompanionTheory.SW.ThetaUD
