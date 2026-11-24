-- Prove2me | solution 1 for GlobalTheory.WeilIsogeny.exists_theta_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:15:42.958067+00:00
-- url     : https://prove2.me/submissions/56f06d69-0086-40a2-ba34-5c0eb281cca5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_GenMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenMovePow
import Theorems.Thm_GlobalTheory_WeilIsogeny_exists_gen_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeilIsogeny
open CommutatorPairing
variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
namespace GlobalTheory.WeilIsogeny
theorem _root_.solution (d : ℕ) {n : ℤ} {T : Over S} (θ : ThetaGrp A L n T) :
    ∃ θ' : ThetaGrp A L (n * d) T, θ'.pt = θ.pt ∧ ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ A) (z : Z.left) (J),
      thetaVal θ' t a z J = thetaVal θ t a z J ^ d := by
  obtain ⟨u, hu, hv⟩ := exists_gen_pow (L := L) (K := Fin 2) (φ := ![(snd T A).left, (translPt A θ.pt).left])
    (ε := ![n, -n]) (ε' := ![n * d, -(n * d)]) d (fun k => by fin_cases k <;> simp) θ.φ θ.isGen
  exact ⟨⟨θ.pt, u, hu⟩, rfl, fun Z t a z J => hv _ _ z J⟩
end GlobalTheory.WeilIsogeny
