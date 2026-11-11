-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.low_candidate_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:18:23.667465+00:00
-- url     : https://prove2.me/submissions/c4a432bd-d715-43d6-b542-b7fb40fa1667

import Mathlib
import Definitions.Def_Q238K051
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCanonicalSurplus_produce_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryMetricSurplus_run_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_LocalSearch_optimum_attained_exact_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_LocalSearch_optimum_attained_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_StrictnessGapPos
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Surplus
open MetricKMedianRecovery.LocalSearch MetricKMedianRecovery.Anchoring

lemma strictnessGap_le_one {T : ℝ} (hT : 0 < T) : strictnessGap T ≤ 1 := by
  have hd : 1 ≤ 200*(T+2) := by linarith
  have ht : 0 < 200*(T+2) := by positivity
  have hq : 1/(200*(T+2)) ≤ (1:ℝ) := (div_le_iff₀ ht).mpr (by nlinarith only [hd])
  have hq0 : 0 ≤ 1/(200*(T+2)) := by positivity
  unfold strictnessGap
  nlinarith

end MetricKMedianRecovery.Surplus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_IndexedCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseSurplusProducer
open PhaseOriginalLedger LocalSearch Anchoring Surplus
variable {V : Type*} [MetricSpace V] [DecidableEq V]

lemma countConstant_ge_ten : (10:ℝ) ≤ countConstant (1/100) := by
  unfold countConstant
  have hh : 0 ≤ (600/(1/100:ℝ))*(2:ℝ)^(rounds (1/100)-1) := by positivity
  linarith only [hh]

end MetricKMedianRecovery.PhaseSurplusProducer

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Produce
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V]

omit [PseudoMetricSpace V] in
lemma mem_feasibleSets (F S : Finset V) (r : ℕ) :
    S ∈ feasibleSets F r ↔ S ⊆ F ∧ S.Nonempty ∧ S.card ≤ r := by
  simp only [feasibleSets,Finset.mem_filter,Finset.mem_powerset]
lemma optimum_nonneg (F D : Finset V) (r : ℕ) : 0 ≤ optimum F D r := by
  unfold optimum
  split_ifs with h
  · exact Finset.le_inf' h _ (fun _ _ => cost_nonneg _ _)
  · rfl
lemma optimum_le (F D S : Finset V) (r : ℕ) (hSF : S ⊆ F)
    (hS : S.Nonempty) (hSr : S.card ≤ r) : optimum F D r ≤ cost D S := by
  have hm : S ∈ feasibleSets F r := (mem_feasibleSets F S r).mpr ⟨hSF,hS,hSr⟩
  rw [optimum,dite_eq_left ⟨S,hm⟩]
  exact Finset.inf'_le _ hm
lemma optimum_antitone (F D : Finset V) (hF : F.Nonempty) {a b : ℕ}
    (ha : 0 < a) (hab : a ≤ b) : optimum F D b ≤ optimum F D a := by
  obtain ⟨O,hOF,hO,hOa,hcost⟩ := optimum_attained_s238 F D hF a ha
  exact (optimum_le F D O b hOF hO (hOa.trans hab)).trans_eq hcost

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LowCandidate
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.IntegralAssembly
open LocalSearch Anchoring Completion Sampling Surplus FiniteSampling IntegralCandidates

lemma gamma_le_strict : gamma ≤ strictnessGap (200*countConstant (1/100))/100 := min_le_right _ _

end MetricKMedianRecovery.IntegralAssembly

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralDispatchGuarantee
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricSurplus
open LocalSearch Anchoring Surplus
variable {n : ℕ} [MetricSpace (Fin n)]
attribute [local irreducible] run BinaryCanonicalSurplus.run
lemma low_candidate_s238_oai (δ : Fin n→ Fin n→ℕ) (F D : Finset (Fin n))
    (k L M N C : ℕ) (v : ℚ) (hD : D.Nonempty) (hL : 0<L) (hk : 2*L<k) (hkF : k≤ F.card)
    (hN : N=D.card+F.card) (hM : 0<M) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (hfar : ∀ i∈F,∀ p∈D,1≤ dist i p) (hdiam : ∀ p∈D,∀ i∈F,δ p i≤ M)
    (hcap : ∀ p∈D,∀ i∈F,δ p i≤ Rounding.cap D.card (IntegralAssembly.gamma/16))
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)≤1/12)
    (hvc : (v:ℝ)≤ strictnessGap (200*countConstant (1/100))/1000)
    (hsmall : (v:ℝ)^2≤ strictnessGap (200*countConstant (1/100))/(6*(200*countConstant (1/100)+2)))
    (hsize : 2/(N:ℝ)≤ strictnessGap (200*countConstant (1/100))/200)
    (herror : (N:ℝ)^2/2^N≤(v:ℝ))
    (hfree : 3*(HistoryPhaseBound.limit v ((M:ℝ)+8*(D.card:ℝ)*(M:ℝ))+1)≤ L)
    (hC : 2≤(1+v^2)^C) :
    ∃ S : Finset (Fin n),run v C (pack (fun i j=>(δ i j:ℚ)) D F M (k-L) L)=BinaryFinSet.encode S ∧
      S⊆F ∧ S.Nonempty ∧ S.card=k ∧ WidthLocalMin F D S 5 ∧
      ∀ xi : ℝ,0≤ xi→ xi≤1→ optimum F D (k-2*L)≤(1+xi)*optimum F D k→
        cost D S≤(2-IntegralAssembly.gamma)*(1+xi)*optimum F D k := by
  have hsymm (i j : Fin n) : δ i j=δ j i := by exact_mod_cast ((hδ i j).trans ((dist_comm i j).trans (hδ j i).symm))
  obtain ⟨S,he,hSF,hS,hSc,hlocal,hcost⟩:=BinaryCanonicalSurplus.produce_s238 (fun i j=>δ j i) F D
    (k-L) L M N C v hD (by omega) (by omega) hN hM
    (fun p _ i _=>(hδ i p).trans (dist_comm _ _)) (fun i j=>hδ i (SortedIndex.enum D j)) hfar
    (fun p hp i hi=>by rw [hsymm];exact hdiam p hp i hi)
    (fun p hp i hi=>by rw [hsymm];exact hcap p hp i hi)
    hv hv1 hvc hsmall hsize herror hfree hC
  have hcard : S.card=k := by omega
  refine ⟨S,?_,hSF,hS,hcard,hlocal,?_⟩
  · rw [run_pack_s238];exact he
  intro xi hxi hxi1 hsens
  have hF : F.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨O,hOF,_,hOc,hOcost⟩:=optimum_attained_exact_s238 F D hF (k-L) (by omega) (by omega)
  obtain ⟨H,hHF,hH,hHc,hHcost⟩:=optimum_attained_exact_s238 F D hF (k-2*L) (by omega) (by omega)
  have hanti : optimum F D k≤ cost D O := by
    rw [hOcost];exact optimum_antitone F D hF (by omega) (by omega)
  have hHO : cost D H≤(1+xi)*cost D O := by
    rw [hHcost];exact hsens.trans (mul_le_mul_of_nonneg_left hanti (by linarith))
  have hSO:=hcost O H xi hOF hOc hHF hH (by omega) hHO hxi1
  have hOH : cost D O≤ optimum F D (k-2*L) := by
    rw [hOcost];exact optimum_antitone F D hF (by omega) (by omega)
  have hT : 0<200*countConstant (1/100) := by linarith [PhaseSurplusProducer.countConstant_ge_ten]
  have hc:=strictnessGap_le_one hT
  have hP:=optimum_nonneg F D k
  calc
    cost D S≤(2-strictnessGap (200*countConstant (1/100))/100)*cost D O := hSO
    _≤(2-strictnessGap (200*countConstant (1/100))/100)*((1+xi)*optimum F D k) :=
      mul_le_mul_of_nonneg_left (hOH.trans hsens) (by linarith)
    _≤(2-IntegralAssembly.gamma)*(1+xi)*optimum F D k := by
      have hg:=IntegralAssembly.gamma_le_strict
      nlinarith [mul_le_mul_of_nonneg_right (by linarith : 2-strictnessGap (200*countConstant (1/100))/100≤2-IntegralAssembly.gamma)
        (mul_nonneg (by linarith : 0≤1+xi) hP)]
end MetricKMedianRecovery.BitMachine.BinaryMetricSurplus

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.low_candidate_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.low_candidate_s238_oai
