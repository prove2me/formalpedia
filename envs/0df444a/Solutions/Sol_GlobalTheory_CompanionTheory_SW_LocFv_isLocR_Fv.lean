-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:50:07.541003+00:00
-- url     : https://prove2.me/submissions/1140225b-db69-41e0-88eb-0251bb5c619a

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocFv_isLocR_of_ultrametric
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LocF_proper_d65cdbdea1a5


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LocFv
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
namespace GlobalTheory.CompanionTheory.SW.LocFv
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), IsLocR (Fv F v) := by
  intro F _ _ v
  letI : NontriviallyNormedField (v.adicCompletion F) :=
    Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
  haveI : IsUltrametricDist (v.adicCompletion F) :=
    inferInstanceAs (@IsUltrametricDist (v.adicCompletion F)
      (Valued.toNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))).toDist)
  haveI : ProperSpace (v.adicCompletion F) := Formalism.BasicNotions.Examples₂.LocF.proper v
  have h2 : (2 : v.adicCompletion F) ≠ 0 := two_ne_zero
  exact isLocR_of_ultrametric (v.adicCompletion F) h2
end GlobalTheory.CompanionTheory.SW.LocFv
