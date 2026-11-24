-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Glue.continuous_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:18:54.699335+00:00
-- url     : https://prove2.me/submissions/5ee21ce1-1677-4069-b5e8-522a3e953b4c

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleLocalGlobalProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Glue_repr_map
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Glue_continuous_repr

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
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
namespace GlobalTheory.CompanionTheory.SW.Glue
theorem _root_.solution {R' : Type} [CommRing R'] [Algebra F R'] [TopologicalSpace R']
    [IsTopologicalRing R'] (φ : R →ₐ[F] R') (hφ : Continuous φ) {d : ℕ}
    (b : Module.Basis (Fin d) F E) :
    Continuous fun y : R ⊗[F] E => Algebra.TensorProduct.map φ (AlgHom.id F E) y := by
  rw [← (coH R' b).comp_continuous_iff]
  refine continuous_pi fun k => ?_
  have : (fun y : R ⊗[F] E => ((coH R' b) ∘ fun y : R ⊗[F] E =>
      Algebra.TensorProduct.map φ (AlgHom.id F E) y) y k) =
      fun y => φ ((Algebra.TensorProduct.basis R b).repr y k) := by
    funext y
    exact repr_map φ b y k
  rw [this]
  exact hφ.comp (continuous_repr R b k)
end GlobalTheory.CompanionTheory.SW.Glue
