-- Prove2me | solution 1 for GlobalTheory.AbCoh.mem_map_span_singleton_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:17:31.085169+00:00
-- url     : https://prove2.me/submissions/aa783bac-cd87-48fd-9161-1223a764ed48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullSurjectiveAndKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveDeformationAffineSections
import Theorems.Thm_GlobalTheory_AbLaw_SecOnR_smul_def


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AbCoh
namespace GlobalTheory.AbCoh
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (t : R) (b : S) :
    b ∈ (Ideal.span {t}).map (algebraMap R S) ↔ ∃ c : S, b = t • c := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, by rw [Algebra.smul_def, _root_.mul_comm]⟩
  · rintro ⟨c, rfl⟩; exact ⟨c, by rw [Algebra.smul_def, _root_.mul_comm]⟩
end GlobalTheory.AbCoh
