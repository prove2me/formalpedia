-- Prove2me | solution 1 for GlobalTheory.PerfectPairing.Val.mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:19:39.521701+00:00
-- url     : https://prove2.me/submissions/32d36521-70bc-4638-bfda-0afaa915fa35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubWeilOneLeft
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsReducedTorsionGeometricFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinRepExistsIsPullbackSpec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAlgHomLocalizationAugmentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CardAlgHomReducedTraceSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsUnitDetPairingOfBicharacterOfDvdTraceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubWeilPerfectOfGeneric
import Theorems.Thm_GlobalTheory_UU_CubWeil_mul_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.PerfectPairing
variable {O : Type} [CommRing O]
variable {A : Over (Sp O)} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L) (n : ℕ)
  {S S' : Type} [CommRing S] [Algebra O S] [CommRing S'] [Algebra O S']
variable {c n} {x x' y y' : specO O S ⟶ A} {s s' : S}
namespace GlobalTheory.PerfectPairing
namespace Val
theorem _root_.solution (h : Val c n x y s) (h' : Val c n x' y s') : Val c n (x * x') y (s * s') := by
  obtain ⟨ζ, h, rfl⟩ := h
  obtain ⟨ζ', h', rfl⟩ := h'
  exact ⟨_, h.mul_left h', map_mul _ _ _⟩
end Val
end GlobalTheory.PerfectPairing
