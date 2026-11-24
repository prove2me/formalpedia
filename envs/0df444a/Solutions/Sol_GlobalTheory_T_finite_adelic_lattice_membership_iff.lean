-- Prove2me | solution 1 for GlobalTheory.T.finite_adelic_lattice_membership_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:09:32.84326+00:00
-- url     : https://prove2.me/submissions/55f7abab-65c0-4bf3-b78e-10ef17e666e5

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteAdelicLatticeMembershipIff
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteAdelicLatticeMembershipIffStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_Lat_natCast_mul_mem_latV_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (d M : ℕ) (b : Module.Basis (Fin d) F E) (a : ℕ) (X : Fin 1 → Fin M → Af F ⊗[F] E), (∀ v, (fun p i => (a : Fv F v ⊗[F] E) * projV v X p i) ∈ latV b v) ↔ ∀ i v, ((a : Af F) * cv (Af F) b (X 0) i) v ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.Lat.natCast_mul_mem_latV_iff | exact GlobalTheory.CompanionTheory.SW.BB.Lat.natCast_mul_mem_latV_iff | (intros; apply GlobalTheory.CompanionTheory.SW.BB.Lat.natCast_mul_mem_latV_iff <;> assumption)
end _root_.GlobalTheory.T
