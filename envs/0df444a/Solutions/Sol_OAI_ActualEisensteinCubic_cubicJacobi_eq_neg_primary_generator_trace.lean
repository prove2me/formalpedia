-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicJacobi_eq_neg_primary_generator_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:07:34.62731+00:00
-- url     : https://prove2.me/submissions/fbcb192a-3653-4bc7-913d-cb402bc16c6d

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_ActualEisensteinCubic_traceLambda_sq_dvd_iff
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicJacobi_eq_neg_primary_generator_of_principal

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : traceLambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : traceLambda ^ 2 ∣ p - 1) :
    jacobiSum (cubicChar P (hgood_from_trace P hgood))
      (cubicChar P (hgood_from_trace P hgood)) = -p := by
  let hgood' : lambda ∉ P := hgood_from_trace P hgood
  simpa only using cubicJacobi_eq_neg_primary_generator_of_principal
    P hgood' p hP ((traceLambda_sq_dvd_iff (p - 1)).mp hprimary)
end OAI.ActualEisensteinCubic
