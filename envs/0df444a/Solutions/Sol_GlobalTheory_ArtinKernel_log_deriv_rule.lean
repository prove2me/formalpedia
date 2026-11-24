-- Prove2me | solution 1 for GlobalTheory.ArtinKernel.log_deriv_rule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:59:11.038623+00:00
-- url     : https://prove2.me/submissions/c035cb23-752f-411a-8d14-5805d5e9cd8c

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfLogDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TranslationFixingBundleArtinPointEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.ArtinKernel
open GlobalTheory.TangentOrigin
variable {R : Type} [CommRing R] [Algebra ℂ R] [IsLocalRing R] [Module.Finite ℂ R]
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
omit [IsLocalRing R] [Module.Finite ℂ R]
namespace GlobalTheory.ArtinKernel
theorem _root_.solution (ρ : R →ₐ[ℂ] ℂ) (κ : R →ₗ[ℂ] ℂ) {F F' G : R} {g₀ d : ℂ} (e : F * algebraMap ℂ R g₀ = G * F')
    (hρ : ρ G = g₀) (k : κ (F' * G) = ρ F' * d + ρ G * κ F') (n₀ : g₀ ≠ 0) (n₁ : ρ F' ≠ 0) :
    g₀ * (κ F * (ρ F)⁻¹) = d + g₀ * (κ F' * (ρ F')⁻¹) := by
  have e1 := congrArg ρ e
  have e2 := congrArg κ e
  rw [map_mul, map_mul, hρ, AlgHom.commutes, mul_comm] at e1
  have e3 : ρ F = ρ F' := mul_left_cancel₀ n₀ e1
  rw [mul_comm G, k, hρ, Algebra.algebraMap_eq_smul_one, mul_smul_comm, _root_.mul_one,
    map_smul, smul_eq_mul] at e2
  rw [e3]
  field_simp
  linear_combination e2
end GlobalTheory.ArtinKernel
