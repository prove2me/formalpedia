-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Sampling.tsum_eq_sum_fin
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:52:28.079319+00:00
-- url     : https://prove2.me/submissions/7f4bcbdb-e455-4e5a-acdc-ec80614dc230

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/SamplingEnergy.lean:L178-L197
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Sampling.tsum_eq_sum_fin. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Definitions.Def_OAI_Analysis_Littlewood_IntervalPacking
import Definitions.Def_OAI_Analysis_Littlewood_SamplingTail
import Definitions.Def_OAI_Analysis_Littlewood_SamplingEnergy

-- ---- from OAI.Analysis.Littlewood.SamplingEnergy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace AsymptoticallyMinimalLittlewood.Sampling
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail

lemma tsum_eq_sum_fin {N : ℕ} (f : ℤ → ℂ)
    (hf : ∀ k : ℤ, k<0 ∨ (N : ℤ)≤k → f k=0) :
    (∑' k : ℤ, f k)=∑ k : Fin N, f k.val := by
  classical
  let s : Finset ℤ := Finset.univ.image (fun k : Fin N ↦ (k.val : ℤ))
  have hz (k : ℤ) (hk : k∉s) : f k=0 := by
    apply hf
    by_contra he
    push Not at he
    apply hk
    have hknat : k.toNat<N := by omega
    exact Finset.mem_image.mpr ⟨⟨k.toNat,hknat⟩,Finset.mem_univ _,by
      change (k.toNat : ℤ)=k
      exact Int.toNat_of_nonneg (by omega)⟩
  rw [tsum_eq_sum hz]
  exact Finset.sum_image (by
    intro i _ j _ he
    apply Fin.ext
    change (i.val : ℤ)=(j.val : ℤ) at he
    exact_mod_cast he)

end
end AsymptoticallyMinimalLittlewood.Sampling

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Sampling
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Sampling.tsum_eq_sum_fin := @_root_.OAI.AsymptoticallyMinimalLittlewood.Sampling.tsum_eq_sum_fin
