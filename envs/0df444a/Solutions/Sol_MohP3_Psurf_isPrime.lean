-- Prove2me | solution 1 for MohP3.Psurf_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:32:21.785559+00:00
-- url     : https://prove2.me/submissions/117729e3-3f96-462b-94fb-4114ae11f7b5

module
public import Definitions.Def_MohP3_Global
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_Height

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution : Psurf.IsPrime := RingHom.ker_isPrime sigma
end MohP3
