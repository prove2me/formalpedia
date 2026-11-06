-- Prove2me | solution 1 for OAI.SevenEighths.PeriodicThetaRegularity.theta_locallyIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:14:12.986758+00:00
-- url     : https://prove2.me/submissions/c0d20edd-a6cc-425f-beb6-417f0ddd96f2

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
import Definitions.Def_OAI_NumberTheory_DirichletL_PeriodicThetaRegularity

set_option autoImplicit false
open OAI
noncomputable section
open Set Filter Asymptotics MeasureTheory
open scoped Topology BigOperators
open OAI.SevenEighths OAI.SevenEighths.PeriodicThetaRegularity
open ThetaProduct EisensteinTheta HeckeTheta
namespace OAI.SevenEighths.PeriodicThetaRegularity
theorem _root_.solution {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    LocallyIntegrableOn (theta w) (Ioi 0) :=
  (theta_continuous w).locallyIntegrableOn measurableSet_Ioi
end OAI.SevenEighths.PeriodicThetaRegularity
