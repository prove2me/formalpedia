-- Prove2me | solution 1 for GlobalTheory.ArtinKernel.exists_derivation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:14:34.989892+00:00
-- url     : https://prove2.me/submissions/46d46f15-4897-4708-89ec-9318ea044cef

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnFamPtAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfLogDeriv
import Theorems.Thm_GlobalTheory_ArtinKernel_exists_functional


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
namespace GlobalTheory.ArtinKernel
theorem _root_.solution (ρ : R →ₐ[ℂ] ℂ) (hρ : ∀ r, ρ r = 0 → r ∈ IsLocalRing.maximalIdeal R)
    {J : Type*} (s : J → R) (hs : ∃ i, s i ≠ algebraMap ℂ R (ρ (s i))) :
    ∃ κ : R →ₗ[ℂ] ℂ, κ 1 = 0 ∧ (∃ i, κ (s i) ≠ 0) ∧
      ∀ i r, κ (r * s i) = ρ r * κ (s i) + ρ (s i) * κ r := by
  obtain ⟨lam, ⟨i₀, hi₀⟩, hlam⟩ := exists_functional (fun i => s i - algebraMap ℂ R (ρ (s i)))
    (by obtain ⟨i, hi⟩ := hs; exact ⟨i, sub_ne_zero.2 hi⟩)
  have hm : ∀ r : R, r - algebraMap ℂ R (ρ r) ∈ IsLocalRing.maximalIdeal R := fun r =>
    hρ _ (by rw [map_sub, AlgHom.commutes]; simp)
  have hkey : ∀ i r, lam (r * s i) = ρ r * (lam (s i) - ρ (s i) * lam 1) + ρ (s i) * lam r := by
    intro i r
    have h := hlam i _ (hm r)
    beta_reduce at h
    rw [sub_mul, map_sub, sub_eq_zero, Algebra.algebraMap_eq_smul_one (ρ r), smul_mul_assoc, _root_.one_mul,
      map_smul, smul_eq_mul] at h
    have e1 : r * s i = r * (s i - algebraMap ℂ R (ρ (s i))) + ρ (s i) • r := by
      rw [Algebra.algebraMap_eq_smul_one, mul_sub, mul_smul_comm, _root_.mul_one]
      abel
    have e3 : lam (s i - algebraMap ℂ R (ρ (s i))) = lam (s i) - ρ (s i) * lam 1 := by
      rw [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
    rw [e1, map_add, h, e3, map_smul, smul_eq_mul]
  refine ⟨lam - lam 1 • ρ.toLinearMap, by simp, ⟨i₀, ?_⟩, ?_⟩
  · have e : (lam - lam 1 • ρ.toLinearMap) (s i₀) = lam (s i₀ - algebraMap ℂ R (ρ (s i₀))) := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_mul,
        map_sub, Algebra.algebraMap_eq_smul_one, map_smul]
      ring
    rw [e]
    exact hi₀
  · intro i r
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_mul, map_mul]
    rw [hkey]
    ring
end GlobalTheory.ArtinKernel
