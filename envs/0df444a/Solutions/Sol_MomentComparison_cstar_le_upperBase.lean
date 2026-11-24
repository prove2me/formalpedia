-- Prove2me | solution 1 for MomentComparison.cstar_le_upperBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:26:28.521797+00:00
-- url     : https://prove2.me/submissions/b4768823-d484-41b8-8201-7e8288735133

module
public import Definitions.Def_MomentComparison_Pairing
public import Definitions.Def_MomentComparison_Conformal
public import Definitions.Def_MomentComparison_Hypercontractivity
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Data.Real.ConjExponents
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_Upper
public import Theorems.Thm_MomentComparison_cstar_le_upperBase_of_estimates
public import Theorems.Thm_MomentComparison_complexNoise_contract
public import Theorems.Thm_MomentComparison_polynomialGrowth


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison
namespace MomentComparison
theorem _root_.solution : Cstar ≤ upperBase :=
  cstar_le_upperBase_of_estimates
    (fun _ hp _ f _ hw => complexNoise_contract hp hw f)
    (fun _ hp _ _ hP _ hM hbound => polynomialGrowth hp hP hM hbound)
end MomentComparison
