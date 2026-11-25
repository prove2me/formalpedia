-- Prove2me | solution 1 for GlobalTheory.SS.isFrame_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:07:47.971699+00:00
-- url     : https://prove2.me/submissions/b9c5336d-e500-4b33-af42-8982b48dcc1f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Theorems.Thm_GlobalTheory_SS_jac_pderiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SS
variable (R : Type) [CommRing R] {K : Type} [Field K] [Algebra R K]
variable {R} {A A' : Over (Sp K)}
variable {B : Type} [CommRing B] [Algebra K B]
namespace GlobalTheory.SS
theorem _root_.solution (n : ℕ) :
    IsFrame (A := Over.mk (spMap (algebraMap K (MvPolynomial (Fin n) K))))
      (fun i : Fin n => VF.ofDerivation (MvPolynomial.pderiv i)) := by
  refine ⟨?_, fun x => ⟨⊤, fun j => fnOn _ ⊤ (MvPolynomial.X j), trivial, ?_⟩⟩
  · rw [Fintype.card_fin]
    have hA : Algebra.IsStandardSmoothOfRelativeDimension n K (MvPolynomial (Fin n) K) := by
      let v : PEmpty.{1} → MvPolynomial (Fin n) K := PEmpty.elim
      let P0 := Algebra.PreSubmersivePresentation.naive (v := v) (PEmpty.elim : PEmpty.{1} → Fin n)
        (fun a => a.elim)
      let P : Algebra.SubmersivePresentation K _ (Fin n) PEmpty.{1} := ⟨P0, by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_isEmpty, map_one]
        exact isUnit_one⟩
      have hI : Ideal.span (Set.range v) = ⊥ := by simp [v]
      let e : (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range v)) ≃ₐ[K] MvPolynomial (Fin n) K :=
        (Ideal.quotientEquivAlgOfEq K hI).trans
          (AlgEquiv.ofRingEquiv (f := RingEquiv.quotientBot _) (fun r => RingEquiv.quotientBot_mk _))
      exact (P.ofAlgEquiv e).isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])
    show SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin n) K))))
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mpr hA)
  · rw [jac_pderiv]; exact isUnit_one
end GlobalTheory.SS
