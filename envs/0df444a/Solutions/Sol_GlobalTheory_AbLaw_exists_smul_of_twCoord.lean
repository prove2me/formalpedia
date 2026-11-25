-- Prove2me | solution 1 for GlobalTheory.AbLaw.exists_smul_of_twCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:27:21.353826+00:00
-- url     : https://prove2.me/submissions/89cbd0c6-8b44-49f1-a27b-fb2a3bf3b14a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulOfTwCoord
import Theorems.Thm_P2M_GlobalTheory_GrSum_apply_eq_eval_Hom_mul_5e4d976ba5d8
import Theorems.Thm_GlobalTheory_GrSum_of_mem_grading


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory
namespace GlobalTheory
namespace AbLaw
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y) (hx : ∀ V : Y.Opens, OperatorsCommute (ι := Fin (m + 1)) (A := fun t => SecOnR f (tw M H t) V) fun i t => SecOnR.mulSec f M t (s i) V) (V : Y.Opens) (F : MvPolynomial (Fin (m + 1)) R) (d t t' : ℤ) (y : SecOn (tw M H t) V), F ∈ polyGrading (Fin (m + 1)) R d → t' = t + d → ∃ y' : SecOn (tw M H t') V, F • GrSum.of (hx V) t (SecOnR.of f _ V y) = GrSum.of (hx V) t' (SecOnR.of f _ V y') ∧ ∀ (p : M.ι) (l : H.ι), SecOn.twCoord y' p l = rs Y (inf_le_right.trans inf_le_right : V ⊓ (M.U p ⊓ H.U l) ≤ H.U l) (MvPolynomial.eval₂Hom (cst f (H.U l)) (fun j => (s j).f l) F) * SecOn.twCoord y p l := by
  intro R _ Y f H m s M hx V F d t t' y hF ht
  subst ht
  obtain ⟨a, ha⟩ := (GrSum.mem_grading (hx V)).1
    (grSMul_mem (GrSum.grading (hx V)) hF (GrSum.of_mem_grading (hx V) t (SecOnR.of f _ V y)))
  refine ⟨(SecOnR.of f _ V).symm a, ha.symm, fun p l => ?_⟩
  have h₀ : V ⊓ (M.U p ⊓ H.U l) ≤ H.U l := inf_le_right.trans inf_le_right
  have e := GrSum.apply_eq_eval₂Hom_mul (hx V) (cst f (V ⊓ (M.U p ⊓ H.U l)))
    (fun j => rs Y h₀ ((s j).f l))
    (fun n z => SecOn.twCoord ((SecOnR.of f _ V).symm z) p l) (fun _ _ _ => rfl)
    (fun n r z => SecOnR.coord_base_smul r z (p, l)) (fun _ _ _ => rfl) F ha.symm
  refine e.trans (congrArg (· * SecOn.twCoord y p l) ?_)
  rw [MvPolynomial.map_eval₂Hom]
  congr 2
  exact RingHom.ext fun r => (rs_cst f h₀ r).symm
end AbLaw
end GlobalTheory
