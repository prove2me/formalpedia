-- Prove2me | solution 1 for MohP3.iota_ofNat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:53:26.223972+00:00
-- url     : https://prove2.me/submissions/31cbc345-b6aa-4c30-8fd7-8dda58524fe5

module
public import Definitions.Def_MohP3_Certificate
public import Definitions.Def_MohP3_Closure

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution (n : ℕ) [n.AtLeastTwo] :
    iota (no_index (OfNat.ofNat n)) = OfNat.ofNat n := map_ofNat iota n
end MohP3
