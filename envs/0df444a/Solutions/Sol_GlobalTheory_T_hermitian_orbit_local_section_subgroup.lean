-- Prove2me | solution 1 for GlobalTheory.T.hermitian_orbit_local_section_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:37:15.953002+00:00
-- url     : https://prove2.me/submissions/e7fcd254-a4c1-4ebb-b084-540d8ffc0b84

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOrbitLocalSectionSubgroup
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOrbitLocalSectionSubgroupStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_tri_slice


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (S : HermR R σ n), IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det → ∃ (Q : Subgroup (GL (Fin n) (R ⊗[F] E))) (o : Q → HermR R σ n), LocallyCompactSpace Q ∧ SecondCountableTopology Q ∧ IsOpenEmbedding o ∧ ∀ x : Q, (o x : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) ((x : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * ((x : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.tri_slice | exact GlobalTheory.CompanionTheory.SW.tri_slice | (intros; apply GlobalTheory.CompanionTheory.SW.tri_slice <;> assumption)
end _root_.GlobalTheory.T
