-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PureH.pureL_act_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:28:59.4579+00:00
-- url     : https://prove2.me/submissions/fc387b80-8a57-4f28-be74-e06786d19470

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneDetHermitianGram
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupProjections
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeStableAlmostEverywhere
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryFiniteSetDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PureH_consTup_empty
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PureH_prod_union_split
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PureH_pureL_act
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
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  [DecidableEq (HeightOneSpectrum (𝓞 F))]
variable {d M : ℕ} (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E)
  (Jp : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (h : HA (AF F) σ Jp) (ginf : HA (Ainf F) σ Jp)
  (g : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ Jp) (S Sh : Finset (HeightOneSpectrum (𝓞 F)))
include b
namespace GlobalTheory.CompanionTheory.SW.PureH
theorem _root_.solution
    (hinf : ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E),
      projInf (actW (AF F) σ Jp h X) = actW (Ainf F) σ Jp ginf (projInf X))
    (hfin : ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F)),
      projV v (projFin (actW (AF F) σ Jp h X)) = actW (Fv F v) σ Jp (g v) (projV v (projFin X)))
    (hSh : ∀ v, v ∉ Sh → ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → Fv F v ⊗[F] E),
      actW (Fv F v) σ Jp (g v) X ∈ latV b v ↔ X ∈ latV b v)
    (hS : ∀ v, v ∉ S → ∀ X₀ : Fin 0 → Fin M → Fv F v ⊗[F] E, consTup X₀ ∈ latV b v)
    (Ψinf : (Fin 1 → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞)
    (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) :
    pureL b S Ψinf Ψ (actW (AF F) σ Jp h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) =
      (Ψinf (actW (Ainf F) σ Jp ginf (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) *
        ∏ v ∈ S, Ψ v (actW (Fv F v) σ Jp (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) *
        ∏ v ∈ Sh \ S, (latV b v).indicator 1
          (actW (Fv F v) σ Jp (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) := by
  let X₀ : Fin 0 → Fin M → AF F ⊗[F] E := fun a => a.elim0
  have h1 := pureL_act (n := 0) b σ Jp h ginf g S Sh hinf hfin hSh hS Ψinf Ψ X₀
  have hmem : X₀ ∈ intOff b (S ∪ Sh) := fun v _ a => a.elim0
  unfold pureL at h1
  rw [Set.indicator_of_mem hmem] at h1
  rw [consTup_empty] at h1
  simp only [consTup_empty] at h1
  rw [prod_union_split S Sh _ _ (fun v => v ∈ S) (fun _ => Iff.rfl)] at h1
  rw [mul_assoc]
  unfold pureL
  exact h1
end GlobalTheory.CompanionTheory.SW.PureH
