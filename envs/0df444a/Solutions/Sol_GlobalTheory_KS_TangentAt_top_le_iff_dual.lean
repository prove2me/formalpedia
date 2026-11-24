-- Prove2me | solution 1 for GlobalTheory.KS.TangentAt.top_le_iff_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:28:18.061877+00:00
-- url     : https://prove2.me/submissions/10a91943-56fc-4509-bfbf-7ea193cef4c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationIffDualNumberPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationUniformisedAbelianVarietyUniqueVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.TangentAt
private theorem mem_prime_dualNumber_iff_fst_eq_zero (p : Ideal (DualNumber ℂ)) (hp : p.IsPrime) (x : DualNumber ℂ) :
    x ∈ p ↔ x.fst = 0 := by
  constructor
  · intro hx
    by_contra hne
    exact hp.ne_top (Ideal.eq_top_of_isUnit_mem p hx
      (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 hne)))
  · intro h0
    have hsq : x * x = 0 := by
      ext <;> simp [h0]
    exact hp.mem_of_pow_mem 2 (by rw [pow_two, hsq]; exact p.zero_mem)
variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L g)
end GlobalTheory.KS.TangentAt
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.TangentAt
namespace GlobalTheory.KS.TangentAt
theorem _root_.solution {X : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ X) (U : X.Opens) :
    ⊤ ≤ v ⁻¹ᵁ U ↔ ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v) ⁻¹ᵁ U := by
  constructor
  · intro hv x _
    exact hv (Set.mem_univ ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base x))
  · intro hv y _
    let x : ↥(Sp ℂ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
    have e : (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base x = y := by
      apply PrimeSpectrum.ext
      ext a
      exact (mem_prime_dualNumber_iff_fst_eq_zero _ (PrimeSpectrum.isPrime _) a).trans
        (mem_prime_dualNumber_iff_fst_eq_zero _ (show PrimeSpectrum (DualNumber ℂ) from y).isPrime a).symm
    have hx : v.base ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base x) ∈ U := hv (Set.mem_univ x)
    rw [e] at hx
    exact hx
end GlobalTheory.KS.TangentAt
