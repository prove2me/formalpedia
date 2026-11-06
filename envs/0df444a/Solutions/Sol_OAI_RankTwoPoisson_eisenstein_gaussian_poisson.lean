-- Prove2me | solution 1 for OAI.RankTwoPoisson.eisenstein_gaussian_poisson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:29:09.015414+00:00
-- url     : https://prove2.me/submissions/b49057c7-75d0-4393-bf0a-1e2f7c2d79a8

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Theorems.Thm_OAI_RankTwoPoisson_eis_gauss_summable
import Theorems.Thm_OAI_RankTwoPoisson_eisenstein_gaussian_poisson_iterated
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


section
namespace OAI
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
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE
end ActualEisensteinCubic
namespace PowerExtraction
end PowerExtraction
namespace ActualEisensteinCubic
end ActualEisensteinCubic
namespace PowerExtraction
end PowerExtraction
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace GaussianAbelPartition
open ConcreteTraceCRT ConcreteBreveE ActualEisensteinCubic
end GaussianAbelPartition
namespace ActualEisensteinCubic
end ActualEisensteinCubic
namespace GaussianFiberEquiv
open ActualEisensteinCubic
end GaussianFiberEquiv
namespace RankTwoPoisson
open Real
private theorem dualTerm_eq_eisGauss {t : ℝ} (ht : 0 < t) (k l : ℤ) :
    dualTerm t (k,l) = eisGauss (4 / (3 * t)) (k,-l) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  dsimp [dualTerm, cg, eisGauss, eisQ]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  field_simp [ht0]
  ring
private theorem dualTerm_summable {t : ℝ} (ht : 0 < t) :
    Summable (dualTerm t) := by
  have htd : 0 < 4 / (3 * t) := by positivity
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have h := (e.summable_iff).2 (eis_gauss_summable htd)
  apply h.congr
  intro z
  change eisGauss (4 / (3 * t)) (z.1, -z.2) = dualTerm t z
  exact (dualTerm_eq_eisGauss ht z.1 z.2).symm
end RankTwoPoisson
end
end OAI
end

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
open OAI.RankTwoPoisson
open Real
namespace OAI.RankTwoPoisson
theorem _root_.solution {t : ℝ} (ht : 0 < t) :
    (∑' z : ℤ × ℤ, eisGauss t z) =
      (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
        (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, eisGauss (4 / (3 * t)) z := by
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have hdual : (∑' z : ℤ × ℤ, dualTerm t z) =
      ∑' z : ℤ × ℤ, eisGauss (4 / (3 * t)) z := by
    calc
      (∑' z : ℤ × ℤ, dualTerm t z) =
          ∑' z : ℤ × ℤ, eisGauss (4 / (3 * t)) (e z) := by
        apply tsum_congr
        intro z
        exact dualTerm_eq_eisGauss ht z.1 z.2
      _ = ∑' z : ℤ × ℤ, eisGauss (4 / (3 * t)) z :=
        Equiv.tsum_eq e _
  calc
    (∑' z : ℤ × ℤ, eisGauss t z) =
        (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' l : ℤ, dualTerm t (k,l)) :=
      eisenstein_gaussian_poisson_iterated ht
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
          (∑' z : ℤ × ℤ, dualTerm t z) := by
      rw [(dualTerm_summable ht).tsum_prod]
    _ = _ := by rw [hdual]
end OAI.RankTwoPoisson
