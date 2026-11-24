-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.MeasProj.isOpen_intOff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:28:06.967563+00:00
-- url     : https://prove2.me/submissions/ce8aea9a-594f-4a21-97c1-7a927eaa36d7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjections
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_MeasProj_continuous_sndA
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_MeasProj_coord_projFin
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_MeasProj_projV_mem_latV_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TopK_isHomeomorph_coord
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.MeasProj
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.MeasProj
theorem _root_.solution {d n M : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E)) := by
  have hA : IsOpen {x : Af F | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _)
      (p := fun v => v ∉ S)
  have hE : (intOff b S : Set (Fin n → Fin M → AF F ⊗[F] E)) = ⋂ a, ⋂ i, ⋂ k,
      (fun X : Fin n → Fin M → AF F ⊗[F] E =>
        sndA F ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k)) ⁻¹'
        {x : Af F | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F} := by
    ext X
    simp only [intOff, Set.mem_setOf_eq, projV_mem_latV_iff, coord_projFin, Set.mem_iInter,
      Set.mem_preimage]
    exact ⟨fun h a i k v hv => h v hv a i k, fun h v hv a i k => h a i k v hv⟩
  rw [hE]
  refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i =>
    isOpen_iInter_of_finite fun k => hA.preimage (continuous_sndA.comp ?_)
  exact (continuous_apply k).comp ((TopK.isHomeomorph_coord (AF F) b).continuous.comp
    ((continuous_apply i).comp (continuous_apply a)))
end GlobalTheory.CompanionTheory.SW.MeasProj
