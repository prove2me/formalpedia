-- Prove2me | solution 1 for GlobalTheory.UnRep.Compare.eq_zero_of_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:58:07.218179+00:00
-- url     : https://prove2.me/submissions/bceee872-45e0-4b2c-b632-7039fb969cff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSplitPlaceOfSplitPl
import Theorems.Thm_GlobalTheory_UnRep_Compare_evalAt_apply
import Theorems.Thm_GlobalTheory_UnRep_Compare_loc_tmul
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.Compare
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.UnRep.Compare
theorem _root_.solution {x : RA F E} (h : ∀ v, loc E v x = 0) : x = 0 := by
  let b := Module.Basis.ofVectorSpace F E
  have key : ∀ (v : HeightOneSpectrum (𝓞 F)) (i) (y : RA F E),
      (Algebra.TensorProduct.basis (FiniteAdeleRing (𝓞 F) F) b).repr y i v =
        (Algebra.TensorProduct.basis (v.adicCompletion F) b).repr (loc E v y) i := by
    intro v i y
    rw [← evalAt_apply]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      rw [loc_tmul, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]
      simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes,
        evalAt_apply v a]
    | add s t hs ht => simp only [map_add, Finsupp.add_apply, hs, ht]
  apply (Algebra.TensorProduct.basis (FiniteAdeleRing (𝓞 F) F) b).repr.injective
  ext i : 1
  refine DFunLike.ext _ _ fun v => ?_
  rw [key, h, map_zero, map_zero]
  rfl
end GlobalTheory.UnRep.Compare
