-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HProj.eventually_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:22:36.141849+00:00
-- url     : https://prove2.me/submissions/f9c5d6be-1382-4d6a-b331-607933d8dd6d

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjectionsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupProjections
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_ev_int
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_repr_one_tmul

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HProj
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
namespace GlobalTheory.CompanionTheory.SW.HProj
theorem _root_.solution (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (1 : Fv F v ⊗[F] E) ∈ Lv b v := by
  have hc : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k,
      algebraMap F (Fv F v) (b.repr 1 k) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => ev_int _
  filter_upwards [hc] with v hv k
  rw [Algebra.TensorProduct.one_def, repr_one_tmul]
  exact hv k
end GlobalTheory.CompanionTheory.SW.HProj
