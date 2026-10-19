-- Prove2me | solution 1 for OAI.StrictInverseFirstPower.ae_base_positive_le_weighted
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:20:36.671026+00:00
-- url     : https://prove2.me/submissions/69f3d897-73b6-45c0-8bcc-97f61d0af72c

import Mathlib
import Definitions.Def_OAIQWSIFP000
import Theorems.Thm_OAI_StrictInverseFirstPower_ae_bad_base_positive_zero

section
-- module Solutions.OAIQW_StrictInverseFirstPower.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.CriticalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
namespace StrictInverseFirstPower
noncomputable section

lemma criticalHeight_pos {k : ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hk : 0 < k) (hz : 0 < z.im) (hF : deriv F z ≠ 0) :
    0 < criticalHeight k F z := by
  exact mul_pos (mul_pos hk (Real.rpow_pos_of_pos hz _)) (norm_pos_iff.mpr (inv_ne_zero hF))

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.RankPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma availableRankPartner_spec (k : ℝ) (p : AvailableRankPair k) :
    RankPairRelation k p.1 (availableRankPartner k p) := Classical.choose_spec p.2

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.TransportPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma sourcePair_apply (k : ℝ) (q : sourcePairingDomain k) :
    availableSource k (sourcePair k q) = q.1 := q.2.choose_spec

lemma sourcePartner_of_mem (k : ℝ) {q : DiskFamily × UpperHalfPlane}
    (hq : q ∈ sourcePairingDomain k) : sourcePartner k q = sourcePartnerOn k ⟨q,hq⟩ := by
  classical
  simp only [sourcePartner,dite_eq_left hq]

lemma sourcePartner_spec (k : ℝ) {f : DiskFamily} {z : UpperHalfPlane}
    (hq : (f,z) ∈ sourcePairingDomain k) :
    GoodPair k (f,criticalMap k (halfPlaneFunction f) z) ∧
    0 < jacobianExpression k (halfPlaneFunction f) z ∧
    jacobianExpression k (halfPlaneFunction f) (sourcePartner k (f,z)) < 0 ∧
    criticalMap k (halfPlaneFunction f) (sourcePartner k (f,z)) =
      criticalMap k (halfPlaneFunction f) z ∧
    criticalHeight k (halfPlaneFunction f) z <
      criticalHeight k (halfPlaneFunction f) (sourcePartner k (f,z)) := by
  let p := sourcePair k ⟨(f,z),hq⟩
  have hp := availableRankPartner_spec k p
  have hsource := sourcePair_apply k ⟨(f,z),hq⟩
  have hf : p.1.1.1.1 = f := congrArg Prod.fst hsource
  have hz : p.1.1.2 = z := congrArg Prod.snd hsource
  have hξ : p.1.1.1.2 = criticalMap k (halfPlaneFunction f) z := by
    rw [← hp.1.1,hf,hz]
  have hr : sourcePartner k (f,z) = availableRankPartner k p := sourcePartner_of_mem k hq
  have hg := p.1.2
  change GoodPair k (p.1.1.1.1,p.1.1.1.2) at hg
  simp only [RankPairRelation,signedCriticalFiber,mem_ofPred_eq] at hp
  rw [hf,hz,hξ] at hp
  rw [hf,hξ] at hg
  rw [hr]
  exact ⟨hg,hp.1.2,hp.2.1.2,hp.2.1.1,hp.2.2.2⟩

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.PairingCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma partnerRatio_gt_one {k : ℝ} (hk : 0 < k) {q : DiskFamily × UpperHalfPlane}
    (hq : q ∈ sourcePairingDomain k) : 1 < partnerRatio k q := by
  have hs := sourcePartner_spec k hq
  have hp : 0 < criticalHeight k (halfPlaneFunction q.1) q.2 := criticalHeight_pos hk q.2.im_pos (halfPlaneFunction_deriv_ne_zero q.1 q.2.im_pos)
  rw [partnerRatio,ite_eq_left hq]
  have hd : 1 < criticalHeight k (halfPlaneFunction q.1) (sourcePartner k q) /
      criticalHeight k (halfPlaneFunction q.1) q.2 := (one_lt_div hp).mpr hs.2.2.2.2
  exact one_lt_pow₀ hd (by norm_num)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.StrictTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma ae_base_positive_le_weighted_oai (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hβ : 0 ≤ β) (hlaw : AffineProbabilityLaw μ β) :
    ∀ᵐ f ∂(μ : Measure DiskFamily),
      ENNReal.ofReal (jacobianPart ((β+2)/3) f true UpperHalfPlane.I) ≤
      ENNReal.ofReal (jacobianPart ((β+2)/3) f true UpperHalfPlane.I) *
        ENNReal.ofReal (partnerRatio ((β+2)/3) (f,UpperHalfPlane.I)) := by
  let k := (β+2)/3
  have hk : 0 < k := by dsimp [k]; linarith
  filter_upwards [ae_bad_base_positive_zero μ β hβ hlaw] with f hf
  by_cases hD : (f,UpperHalfPlane.I)∈sourcePairingDomain k
  · have hc : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (partnerRatio k (f,UpperHalfPlane.I)) := by
      exact_mod_cast ENNReal.ofReal_le_ofReal (partnerRatio_gt_one hk hD).le
    simpa only [mul_one] using mul_le_mul' (le_refl (ENNReal.ofReal (jacobianPart k f true UpperHalfPlane.I))) hc
  · simp only [hf hD,ENNReal.ofReal_zero,zero_mul,le_refl]

end
end StrictInverseFirstPower

end

end OAI
end

theorem solution : type_of% @OAI.StrictInverseFirstPower.ae_base_positive_le_weighted_oai := @OAI.StrictInverseFirstPower.ae_base_positive_le_weighted_oai
