-- Prove2me | solution 1 for OAI.SevenEighths.InverseInitialMarkedReserve.shifted_capacity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:48.58804+00:00
-- url     : https://prove2.me/submissions/47578e7f-7ee9-4152-9a9c-9ac5e48c14e9

import Definitions.Def_OAI_NumberTheory_DirichletL_Endpoint
import Definitions.Def_OAI_NumberTheory_DirichletL_Inversion_InitialMarkedReserve

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseInitialMarkedReserve
namespace OAI.SevenEighths.InverseInitialMarkedReserve
theorem _root_.solution (ρ gap η r r' ell G:ℝ)
    (hρ:0<ρ)(hρmax:ρ≤1/4)(hgap:2*gap≤ρ)
    (hη:0<η)(hηmax:η≤1/7)(hr:0≤r)(hell:0≤ell)
    (_hG:0≤G)(hGmax:G≤ell)(hlo:r-η≤r')(hhi:r'≤r)
    (hfirst:r+2*ell<1)(hsecond:2*r+8*ell<3):
    0≤1+ρ ∧ 1+ρ≤2 ∧ -2≤r'+ell-2*G ∧
      r'+2*ell≤(1+ρ)-2*gap ∧
      2*r'+8*ell≤3*(1+ρ)-2*gap ∧
      r'+ell+7*η≤2:=by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith
end OAI.SevenEighths.InverseInitialMarkedReserve
