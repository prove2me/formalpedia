-- Prove2me | solution 1 for KernelRank.expPolyAnnihilator_monic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:34:08.419831+00:00
-- url     : https://prove2.me/submissions/07c3e29a-21fd-41d8-9e52-fdf0fad28570

import Definitions.Def_KernelRankLean_Differential
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_ComplexRank

set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {ι : Type*} [Fintype ι] (P : ι → ℂ[X]) (rate : ι → ℂ) :
    (expPolyAnnihilator P rate).Monic :=
  monic_prod_of_monic _ _ fun i _ => (monic_X_sub_C (rate i)).pow _
end KernelRank
