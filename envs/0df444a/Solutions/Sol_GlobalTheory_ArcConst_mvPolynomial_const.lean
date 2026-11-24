-- Prove2me | solution 1 for GlobalTheory.ArcConst.mvPolynomial_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:59:12.857873+00:00
-- url     : https://prove2.me/submissions/80e527f9-8eaf-4513-ba85-98bfe9a51b20

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsIntegralElemOfIsAlgebraicInt
import Theorems.Thm_GlobalTheory_ArcConst_AlgZ_map
import Theorems.Thm_GlobalTheory_ArcConst_AlgZ_sub
import Theorems.Thm_GlobalTheory_ArcConst_isIntegralElem_of_isAlgebraic_int
import Theorems.Thm_GlobalTheory_ArcConst_isUnit_of_isIntegralElem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
noncomputable section
open GlobalTheory GlobalTheory.ArcConst
namespace GlobalTheory.ArcConst
theorem _root_.solution {σ L : Type} [Field L] [CharZero L] {P : MvPolynomial σ L} (hP : AlgZ P) :
    ∃ y : L, P = MvPolynomial.C y ∧ AlgZ y := by
  refine ⟨MvPolynomial.constantCoeff P, ?_, hP.map (MvPolynomial.constantCoeff (R := L) (σ := σ))⟩
  by_contra hne
  have h1 : AlgZ (MvPolynomial.C (σ := σ) (MvPolynomial.constantCoeff P)) :=
    (hP.map (MvPolynomial.constantCoeff (R := L) (σ := σ))).map (MvPolynomial.C (σ := σ) (R := L))
  have h2 := isUnit_of_isIntegralElem _
    (isIntegralElem_of_isAlgebraic_int (MvPolynomial.C (σ := σ) (R := L)) (hP.sub h1)) (sub_ne_zero.2 hne)
  have h3 := h2.map (MvPolynomial.constantCoeff (R := L) (σ := σ))
  simp at h3
end GlobalTheory.ArcConst
