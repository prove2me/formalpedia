-- Prove2me | solution 1 for GlobalTheory.ArtinKernel.first_order_transl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:14:35.740243+00:00
-- url     : https://prove2.me/submissions/66c14c06-3923-4141-874a-1892369c678f

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
import Theorems.Thm_GlobalTheory_ArtinKernel_ex_translBy
import Theorems.Thm_GlobalTheory_ArtinKernel_evalPt_appLE


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
theorem _root_.solution (ρ : R →ₐ[ℂ] ℂ) (x : spO R ⟶ A) (κ : R →ₗ[ℂ] ℂ) (w : Fin g → ℂ)
    (hκ : ∀ (W : A.left.Opens) (h : ⊤ ≤ x.left ⁻¹ᵁ W) (f : Γ(A.left, W)),
        (∀ r, κ (r * evalPt (R := R) x.left W h f) =
          ρ r * κ (evalPt (R := R) x.left W h f) + ρ (evalPt (R := R) x.left W h f) * κ r) ∧
        κ (evalPt (R := R) x.left W h f) = fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 w)
    (z : Fin g → ℂ) (W : A.left.Opens) (h : ⊤ ≤ (x ≫ translBy u z).left ⁻¹ᵁ W) (f : Γ(A.left, W)) (r : R) :
    κ (r * evalPt (R := R) (x ≫ translBy u z).left W h f) =
      ρ r * fderiv ℂ (fun y => valAt' (u.ex y).left W f) z w +
        ρ (evalPt (R := R) (x ≫ translBy u z).left W h f) * κ r := by
  set T := (translBy u z).left with hT
  have hcomp : (x ≫ translBy u z).left = x.left ≫ T := Over.comp_left ..
  have h' : ⊤ ≤ x.left ⁻¹ᵁ (T ⁻¹ᵁ W) := by
    have h0 := h
    rw [hcomp] at h0
    exact h0
  let f' := (T.appLE W (T ⁻¹ᵁ W) le_rfl).hom f
  have hev : evalPt (R := R) x.left (T ⁻¹ᵁ W) h' f' = evalPt (R := R) (x ≫ translBy u z).left W h f :=
    evalPt_appLE x.left T _ hcomp.symm W _ le_rfl h' h f
  have hfun : (fun y => valAt' (u.ex y).left (T ⁻¹ᵁ W) f') = fun y => valAt' (u.ex (y + z)).left W f := by
    funext y
    have hy := ex_translBy u z y
    by_cases hm : ⊤ ≤ (u.ex y).left ⁻¹ᵁ (T ⁻¹ᵁ W)
    · have hm' : ⊤ ≤ (u.ex (y + z)).left ⁻¹ᵁ W := by rw [← hy]; exact hm
      rw [valAt'_eq_evalPt _ _ hm, valAt'_eq_evalPt _ _ hm']
      exact evalPt_appLE _ T _ hy W _ le_rfl hm hm' f
    · have hm' : ¬ ⊤ ≤ (u.ex (y + z)).left ⁻¹ᵁ W := by rw [← hy]; exact hm
      simp only [valAt', dif_neg hm, dif_neg hm']
  have hsh := fderiv_comp_add_right (𝕜 := ℂ) (f := fun v => valAt' (u.ex v).left W f) (x := 0) z
  simp only [zero_add] at hsh
  obtain ⟨h1, h2⟩ := hκ (T ⁻¹ᵁ W) h' f'
  rw [← hev, h1 r, h2, hfun, hsh]
end GlobalTheory.ArtinKernel
