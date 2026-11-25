-- Prove2me | solution 1 for GlobalTheory.finite_neg_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:07:15.974847+00:00
-- url     : https://prove2.me/submissions/861310fc-d066-49cc-9367-bc7c964c075c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfMonomialBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMonomialBasisCechCubePolynomialGradingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexPolyGradingFiniteExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (ι : Type) [Fintype ι] (n : ℤ) :
    {a : {a : ι → ℤ // ∑ i, a i = n} |
      Finset.univ.filter (fun i => a.1 i < 0) = Finset.univ}.Finite := by
  classical
  refine Set.Finite.subset ((Set.finite_Icc (fun _ : ι => n) (fun _ => 0)).preimage
    Subtype.val_injective.injOn) ?_
  rintro ⟨a, ha⟩ h
  have h' : ∀ i, a i < 0 := fun i => Finset.filter_eq_self.1 h i (Finset.mem_univ i)
  refine ⟨fun i => ?_, fun i => (h' i).le⟩
  have := Finset.add_sum_erase Finset.univ a (Finset.mem_univ i)
  have h2 : ∑ j ∈ Finset.univ.erase i, a j ≤ 0 := Finset.sum_nonpos fun j _ => (h' j).le
  change n ≤ a i
  omega
end GlobalTheory
