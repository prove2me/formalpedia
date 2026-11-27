-- Prove2me | solution 1 for MohP3.Q_le_P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:12:44.656455+00:00
-- url     : https://prove2.me/submissions/eefba8bb-1e53-4f44-a0dc-e8fbbf4b65ce

module
public import Definitions.Def_MohP3_Defs
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_Certificate
public import Theorems.Thm_MohP3_Gen_Q_le_P


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution : Q ≤ P := Gen.Q_le_P x y z
end MohP3
