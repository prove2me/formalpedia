-- Prove2me | solution 1 for GlobalTheory.ArtinKernel.differentiableOn_famPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:31:39.205936+00:00
-- url     : https://prove2.me/submissions/b4a9393b-377f-4f11-9d5c-14bea425e23c

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfMulPeriod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnFamPtAffine
import Theorems.Thm_P2M_GlobalTheory_ArtinKernel_evalPt__eq_aeda6690487c
import Theorems.Thm_GlobalTheory_ArtinKernel_famPt_mem
import Theorems.Thm_GlobalTheory_ArtinKernel_differentiableOn_famPt_affine
import Theorems.Thm_GlobalTheory_TangentOrigin_evalPt_res


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
variable {R : Type} [CommRing R] [Algebra ℂ R]
variable {A : Over (Sp ℂ)}
variable [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
variable [Module.Finite ℂ R]
namespace GlobalTheory.ArtinKernel
theorem _root_.solution {U : A.left.Opens} {V : (spO R ⊗ A).left.Opens}
    (hV : (snd (spO R) A).left ⁻¹ᵁ U ≤ V) (f : Γ((spO R ⊗ A).left, V)) (lam : R →ₗ[ℂ] ℂ) :
    DifferentiableOn ℂ (fun z => lam (evalPt' (R := R) (famPt u R z).left V f))
      {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U} := by
  apply differentiableOn_of_locally_differentiableOn
  intro z hz
  obtain ⟨q0⟩ : Nonempty (PrimeSpectrum ℂ) := inferInstance
  have hp : (u.ex z).left.base q0 ∈ U := hz (show q0 ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  obtain ⟨U', hU'aff, hpU', hU'U⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp A.left.isBasis_affineOpens hp
  refine ⟨{w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ U'}, (u.hol U' 1).1, ?_, ?_⟩
  · intro q _
    rw [Subsingleton.elim (α := PrimeSpectrum ℂ) q q0]
    exact hpU'
  · have hle : (snd (spO R) A).left ⁻¹ᵁ U' ≤ V := ((snd (spO R) A).left.preimage_mono hU'U).trans hV
    refine ((differentiableOn_famPt_affine u hU'aff (resG _ hle f) lam).mono Set.inter_subset_right).congr ?_
    intro w hw
    have h1 : ⊤ ≤ (famPt u R w).left ⁻¹ᵁ ((snd (spO R) A).left ⁻¹ᵁ U') := famPt_mem u w hw.2
    have h2 : ⊤ ≤ (famPt u R w).left ⁻¹ᵁ V :=
      (famPt_mem u w hw.1).trans ((famPt u R w).left.preimage_mono hV)
    simp only [evalPt'_eq _ h1, evalPt'_eq _ h2, evalPt_res _ hle h2 h1]
end GlobalTheory.ArtinKernel
