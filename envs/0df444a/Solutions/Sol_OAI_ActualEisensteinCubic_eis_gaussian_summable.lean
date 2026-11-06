-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.eis_gaussian_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:48:03.789211+00:00
-- url     : https://prove2.me/submissions/d02715ab-35b8-4ccd-9a05-e16874e8fc8e

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Theorems.Thm_OAI_ActualEisensteinCoordinates_eval_coords
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_eval_norm_sq
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_RankTwoPoisson_eis_gauss_summable
import Theorems.Thm_OAI_ShortDraftLatticeCount_coords_eval
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
namespace OAI.ActualEisensteinCubic
theorem _root_.solution {η : ℝ} (hη : 0 < η) :
    Summable (fun z : O => Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
      (‖eisEmbedding z‖ ^ 2 : ℂ))) := by
  have hbase := RankTwoPoisson.eis_gauss_summable hη
  have hcomp : Summable (fun z : O =>
      RankTwoPoisson.eisGauss η (latticeCoordEquiv z)) :=
    (latticeCoordEquiv.summable_iff).2 hbase
  convert hcomp using 1
  funext z
  let p := ActualEisensteinCoordinates.coords z
  have hz : z = ActualEisensteinCoordinates.eval p.1 p.2 :=
    (ActualEisensteinCoordinates.eval_coords z).symm
  rw [hz]
  have hnormC : ((‖eisEmbedding
      (ActualEisensteinCoordinates.eval p.1 p.2)‖ : ℂ)^2) =
      ((p.1*p.1-p.1*p.2+p.2*p.2 : ℤ) : ℂ) := by
    exact_mod_cast eisEmbedding_eval_norm_sq p.1 p.2
  rw [hnormC]
  change _ = RankTwoPoisson.eisGauss η
    (ActualEisensteinCoordinates.coords
      (ActualEisensteinCoordinates.eval p.1 p.2))
  rw [ShortDraftLatticeCount.coords_eval]
  dsimp [RankTwoPoisson.eisGauss, RankTwoPoisson.eisQ]
  congr 1
  push_cast
  ring
end OAI.ActualEisensteinCubic
