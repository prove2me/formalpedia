-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThetaUD.form_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:35:02.93287+00:00
-- url     : https://prove2.me/submissions/a9ecef61-e06e-4da6-8f38-5798a10d39ed

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ThetaFunctionModularity

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
namespace GlobalTheory.CompanionTheory.SW.ThetaUD
theorem _root_.solution {R S ι : Type} [CommRing R] [CommRing S] [Fintype ι] (f : R →+* S) (Q : Matrix ι ι R)
    (x : ι → R) : (fun j => f (x j)) ⬝ᵥ (Q.map f *ᵥ fun j => f (x j)) = f (x ⬝ᵥ (Q *ᵥ x)) := by
  rw [RingHom.map_dotProduct]
  congr 1
  funext i
  exact (RingHom.map_mulVec f Q x i).symm
end GlobalTheory.CompanionTheory.SW.ThetaUD
