-- Prove2me | solution 1 for MohP3.mem_Psurf_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:02:41.028445+00:00
-- url     : https://prove2.me/submissions/a848598d-96c6-468a-b2ec-ad00b5a68338

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
theorem _root_.solution {g : R} : g ∈ Psurf ↔ sigma g = 0 := Iff.rfl
end MohP3
