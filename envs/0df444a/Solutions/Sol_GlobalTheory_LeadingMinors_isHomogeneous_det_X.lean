-- Prove2me | solution 1 for GlobalTheory.LeadingMinors.isHomogeneous_det_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:59:53.009428+00:00
-- url     : https://prove2.me/submissions/d53be0fa-4798-4bc4-9605-9c95cb329d87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CoeffProdLeadingMinors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.LeadingMinors
open MvPowerSeries
namespace GlobalTheory.LeadingMinors
namespace _root_.GlobalTheory.LeadingMinors
theorem _root_.solution {k σ ι : Type*} [CommRing k] [Fintype ι]
    [DecidableEq ι] (v : ι → ι → σ) :
    (Matrix.of fun a i : ι => (MvPolynomial.X (v a i) : MvPolynomial σ k)).det.IsHomogeneous
      (Fintype.card ι) := by
  rw [← MvPolynomial.mem_homogeneousSubmodule, Matrix.det_apply]
  refine Submodule.sum_mem _ fun e _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  rw [MvPolynomial.mem_homogeneousSubmodule]
  have h := MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun i => (Matrix.of fun a i : ι => (MvPolynomial.X (v a i) : MvPolynomial σ k)) (e i) i)
    (fun _ => 1) fun i _ => MvPolynomial.isHomogeneous_X k _
  simpa using h
end _root_.GlobalTheory.LeadingMinors
end GlobalTheory.LeadingMinors
