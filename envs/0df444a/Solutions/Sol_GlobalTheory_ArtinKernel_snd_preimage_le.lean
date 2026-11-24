-- Prove2me | solution 1 for GlobalTheory.ArtinKernel.snd_preimage_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:14:37.244796+00:00
-- url     : https://prove2.me/submissions/e7be19a1-7ad2-4b45-9063-4842453eda30

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
import Theorems.Thm_GlobalTheory_ArtinKernel_subsingleton_primeSpectrum
import Theorems.Thm_GlobalTheory_ArtinKernel_surjective_residue_slice


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
namespace GlobalTheory.ArtinKernel
theorem _root_.solution (ρ : R →ₐ[ℂ] ℂ) (x : spO R ⟶ A) (hx : resPt ρ ≫ x = 1) (i : L.ι) :
    (snd (spO R) A).left ⁻¹ᵁ L.U i ≤ (Out.translDiff A L x).U (fun _ => i) := by
  have := subsingleton_primeSpectrum (R := R)
  have e1 : lift (toUnit A ≫ resPt ρ) (𝟙 A) ≫ lift (fst (spO R) A ≫ x) (snd (spO R) A) ≫ μ = 𝟙 A := by
    rw [← Category.assoc, comp_lift, lift_fst_assoc, lift_snd, Category.assoc, hx, MonObj.comp_one,
      ← Hom.mul_def, _root_.one_mul]
  have e2 : lift (toUnit A ≫ resPt ρ) (𝟙 A) ≫ snd (spO R) A = 𝟙 A := lift_snd _ _
  intro p hp
  obtain ⟨a, rfl⟩ := surjective_residue_slice (A := A) ρ p
  have q1 : (lift (fst (spO R) A ≫ x) (snd (spO R) A) ≫ μ).left
      ((lift (toUnit A ≫ resPt ρ) (𝟙 A)).left a) = a := by
    have h1 := congrArg (fun φ : A ⟶ A => φ.left a) e1
    simpa using h1
  have q2 : (snd (spO R) A).left ((lift (toUnit A ≫ resPt ρ) (𝟙 A)).left a) = a := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e2]
    rfl
  have ha : a ∈ L.U i := by
    have h3 : (snd (spO R) A).left ((lift (toUnit A ≫ resPt ρ) (𝟙 A)).left a) ∈ L.U i := hp
    rwa [q2] at h3
  unfold Out.translDiff LB.LinComb LB.wchart
  rw [← SetLike.mem_coe]
  simp only [TopologicalSpace.Opens.coe_mk, Set.mem_iInter, Set.mem_preimage]
  intro k
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [q1]
    exact ha
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [q2]
    exact ha
end GlobalTheory.ArtinKernel
