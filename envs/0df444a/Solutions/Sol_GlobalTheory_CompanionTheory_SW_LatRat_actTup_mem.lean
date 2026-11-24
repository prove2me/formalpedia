-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LatRat.actTup_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:08:17.569247+00:00
-- url     : https://prove2.me/submissions/a73022fd-cff9-4d9c-9e1c-1b91fa55da30

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeStableAlmostEverywhere
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatRat_mul_mem_latR
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatRat_sum_mem_latR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatRat
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.LatRat
theorem _root_.solution {d M n : ℕ} {b : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    {g : GL (Fin M) E} (hg : ∀ i j, Good b v ((g : Matrix (Fin M) (Fin M) E) i j))
    {X : Fin n → Fin M → Fv F v ⊗[F] E} (hX : X ∈ latV b v) :
    actTup (Fv F v) (bc (inclR (Fv F v)) g) X ∈ latV b v := by
  intro a i
  have h : actTup (Fv F v) (bc (inclR (Fv F v)) g) X a i =
      ∑ j, X a j * inclR (Fv F v) ((g : Matrix (Fin M) (Fin M) E) i j) := by
    simp only [actTup, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [h]
  exact sum_mem_latR _ _ (fun j _ => mul_mem_latR (hg i j) (fun k => hX a j k))
end GlobalTheory.CompanionTheory.SW.LatRat
