-- Prove2me | solution 1 for GlobalTheory.covolume_span_basis_eq_sqrt_det_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:53.786262+00:00
-- url     : https://prove2.me/submissions/b096c2b4-df77-4122-880a-8fec81155008

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Theorems.Thm_GlobalTheory_det_gram_eq_normSq_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder InnerProductSpace MatrixOrder
open Module Submodule MeasureTheory Matrix
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
variable [MeasurableSpace E] [BorelSpace E]
namespace GlobalTheory
theorem _root_.solution [DecidableEq ι] (b : Basis ι ℝ E) :
    ZLattice.covolume (span ℤ (Set.range b)) = √(gram ℝ b).det := by
  let o : OrthonormalBasis ι ℝ E := (stdOrthonormalBasis ℝ E).reindex
    (Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm).symm
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
      (ZSpan.isAddFundamentalDomain b volume),
    ZSpan.measureReal_fundamentalDomain b volume o.toBasis,
    measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
    det_gram_eq_normSq_det o, measureReal_def, o.coe_toBasis, o.volume_parallelepiped]
  simp [Real.sqrt_sq_eq_abs]
end GlobalTheory
