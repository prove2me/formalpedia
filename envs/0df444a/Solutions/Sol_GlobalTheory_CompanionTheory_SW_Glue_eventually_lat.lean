-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Glue.eventually_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:18:57.172895+00:00
-- url     : https://prove2.me/submissions/fc90d9f1-6f3d-411d-ab08-ddc17c988c37

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleLocalGlobalProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Glue_crd_v

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix RestrictedProduct
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Glue
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
variable {d M n : ℕ} (b : Module.Basis (Fin d) F E)
namespace GlobalTheory.CompanionTheory.SW.Glue
theorem _root_.solution (X : Fin n → Fin M → AF F ⊗[F] E) :
    ∀ᶠ v in Filter.cofinite, projV v (projFin X) ∈ latV b v := by
  have h : ∀ (a : Fin n) (i : Fin M) (k : Fin d), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin X) a i) k ∈
        v.adicCompletionIntegers F := by
    intro a i k
    have h0 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
        pV v ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k) ∈
          v.adicCompletionIntegers F :=
      ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).2.2
    exact h0.mono fun v hv => by rwa [crd_v]
  have h' := Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun i =>
    Filter.eventually_all.2 (h a i)
  exact h'
end GlobalTheory.CompanionTheory.SW.Glue
