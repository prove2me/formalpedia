-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LDL.oH_isOpenEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:28:58.705177+00:00
-- url     : https://prove2.me/submissions/c81de7aa-2742-44f5-871f-db276de50117

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraPropertiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOpenChartDiagonalUnipotent
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LDL_gram_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LDL
variable {R K : Type} [CommRing R] [CommRing K]
variable (ι : R →+* K) (τ : K →+* K)
variable {ι τ}
variable [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace K] [IsTopologicalRing K]
variable {ι : R →+* K} {τ : K →+* K}
namespace GlobalTheory.CompanionTheory.SW.LDL
theorem _root_.solution {lev : K → R} (hι : Continuous ι) (hτ : Continuous τ) (hlev : Continuous lev)
    (hττ : ∀ x, τ (τ x) = x) (hτι : ∀ r, τ (ι r) = ι r) (hlι : ∀ r, lev (ι r) = r)
    (hfix : ∀ y, τ y = y → ∃ r, y = ι r) (hU : IsOpenEmbedding (Units.val : Rˣ → R)) (n : ℕ) :
    IsOpenEmbedding (oH ι τ hττ hτι n) := by
  induction n with
  | zero =>
    haveI : IsEmpty (Up 0) := ⟨fun p => (p.1.1).elim0⟩
    haveI : Unique ((Fin 0 → Rˣ) × (Up 0 → K)) :=
      ⟨⟨(fun i => i.elim0, fun p => isEmptyElim p)⟩, fun x =>
        Prod.ext (funext fun i => i.elim0) (funext fun p => isEmptyElim p)⟩
    haveI : Unique (Hm τ 0) :=
      ⟨⟨⟨0, fun a => a.elim0⟩⟩, fun S => Subtype.ext (Subsingleton.elim _ _)⟩
    have h : oH ι τ hττ hτι 0 = Homeomorph.homeomorphOfUnique _ _ := Subsingleton.elim _ _
    rw [h]
    exact (Homeomorph.homeomorphOfUnique _ _).isOpenEmbedding
  | succ n ih =>
    have h : oH ι τ hττ hτι (n + 1) =
        (eH hι hτ hlev hττ hτι hlι hfix n) ∘ (Prod.map Units.val id) ∘ (shear hι hτ hττ hτι n) ∘
          (Prod.map id (Prod.map id (oH ι τ hττ hτι n))) ∘ (eD n) := by
      funext x
      apply Subtype.ext
      exact gram_split hτι x.1 x.2
    rw [h]
    exact (eH hι hτ hlev hττ hτι hlι hfix n).isOpenEmbedding.comp
      ((hU.prodMap .id).comp ((shear hι hτ hττ hτι n).isOpenEmbedding.comp
        ((IsOpenEmbedding.id.prodMap (IsOpenEmbedding.id.prodMap ih)).comp (eD n).isOpenEmbedding)))
end GlobalTheory.CompanionTheory.SW.LDL
