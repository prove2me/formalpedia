-- Prove2me | solution 1 for OAI.MetricKMedian.Preparation.RationalSuppliers.Data.scan_certificate_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:23:36.061604+00:00
-- url     : https://prove2.me/submissions/492ebbcc-0a9f-4e7c-8ccd-c963ee430461

import Mathlib
import Definitions.Def_OAIQ035K047
import Theorems.Thm_OAI_MetricKMedian_FixedBatch_RationalParameters_roundCounts_spec_s35

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSelect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSelect
variable {α : Type}

theorem best_spec (P : α → Bool) (cost : α → ℚ) (L : List α) :
    (best P cost L=none ↔ ∀ a∈L,P a=false) ∧
    ∀ a, best P cost L=some a → a∈L ∧ P a=true ∧ ∀ b∈L,P b=true → cost a ≤ cost b := by
  induction L with
  | nil => simp [best]
  | cons a L ih =>
    by_cases ha : P a=true
    · cases hb : best P cost L with
      | none =>
        have hL := ih.1.mp hb
        simp only [best,ha,ite_true,hb]
        constructor
        · simp only [Option.some_ne_none,List.mem_cons,false_iff]
          intro hh
          have := hh a (Or.inl rfl)
          simp [ha] at this
        · intro b h
          have he : a=b := Option.some.inj h
          subst b
          refine ⟨List.mem_cons_self,ha,?_⟩
          intro b hmem hP
          rcases List.mem_cons.mp hmem with he | he
          · subst b; exact le_rfl
          · have hf := hL b he
            rw [hP] at hf
            contradiction
      | some b =>
        obtain ⟨hbmem,hbP,hmin⟩ := ih.2 b hb
        simp only [best,ha,ite_true,hb]
        constructor
        · simp only [Option.some_ne_none,List.mem_cons,false_iff]
          intro hh
          have := hh a (Or.inl rfl)
          simp [ha] at this
        · intro z hz
          by_cases hab : cost a ≤ cost b
          · simp only [ite_eq_left hab,Option.some.injEq] at hz
            subst z
            refine ⟨List.mem_cons_self,ha,?_⟩
            intro z hz hP
            rcases List.mem_cons.mp hz with he | he
            · subst z; exact le_rfl
            · exact hab.trans (hmin z he hP)
          · simp only [ite_eq_right hab,Option.some.injEq] at hz
            subst z
            refine ⟨List.mem_cons_of_mem a hbmem,hbP,?_⟩
            intro z hz hP
            rcases List.mem_cons.mp hz with he | he
            · subst z; exact le_of_lt (lt_of_not_ge hab)
            · exact hmin z he hP
    · have haf : P a=false := Bool.eq_false_iff.mpr ha
      simp only [best,haf,Bool.false_eq_true,ite_false]
      constructor
      · rw [ih.1]
        constructor
        · intro h b hb
          rcases List.mem_cons.mp hb with he | he
          · subst b; exact haf
          · exact h b he
        · intro h b hb
          exact h b (List.mem_cons_of_mem a hb)
      · intro b hb
        obtain ⟨hbmem,hbP,hmin⟩ := ih.2 b hb
        refine ⟨List.mem_cons_of_mem a hbmem,hbP,?_⟩
        intro z hz hP
        rcases List.mem_cons.mp hz with he | he
        · subst z
          rw [haf] at hP
          contradiction
        · exact hmin z he hP

end MetricKMedian.SparseSelect
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalImageCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Completion.Rational
open Finset
variable {F H : Type} [DecidableEq H] {j : ℕ}

theorem score_image (d : Fin j → H → ℚ) (f : F → H) (O : Finset F) :
    score d (O.image f)=score (fun c a => d c (f a)) O := by
  unfold score
  apply sum_congr rfl
  intro c _
  by_cases hO : O.Nonempty
  · rw [dite_eq_left (hO.image f),dite_eq_left hO]
    simp only [image_image]
    rfl
  · have hI : ¬(O.image f).Nonempty := by simpa only [image_nonempty] using hO
    rw [dite_eq_right hO,dite_eq_right hI]

end MetricKMedian.Completion.Rational
namespace MetricKMedian.SparseSelect
variable {α : Type}

theorem best_of_witness (P : α → Bool) (cost : α → ℚ) (L : List α)
    (a : α) (ha : a∈L) (hP : P a=true) :
    ∃ b, best P cost L=some b ∧ b∈L ∧ P b=true ∧ cost b ≤ cost a := by
  cases hb : best P cost L with
  | none =>
    have hh := (best_spec P cost L).1.mp hb a ha
    rw [hP] at hh
    contradiction
  | some b =>
    obtain ⟨hbmem,hbP,hbcost⟩ := (best_spec P cost L).2 b hb
    exact ⟨b,rfl,hbmem,hbP,hbcost a ha hP⟩

end MetricKMedian.SparseSelect
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_RationalPreparedScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState Completion.Rational
variable {τ : ℝ} (q : RationalParameters τ)
variable {F H X : Type} [LinearOrder F] [Fintype F] [DecidableEq H]
  [PseudoMetricSpace X] {j : ℕ}

theorem candidate_mem (d₀ : H → H → ℚ) (d : Fin j → H → ℚ) (orig : F → H)
    (ns : List (F → ℕ)) (n : F → ℕ) (hn : n∈ns) (O : Finset F)
    (hO : q.roundCounts (fun a b => d₀ (orig a) (orig b)) (fun c a => d c (orig a)) n=some O) :
    O.image orig∈q.countCandidates d₀ d orig ns := by
  apply List.mem_flatMap.mpr
  refine ⟨n,hn,?_⟩
  rw [hO]
  simp

theorem roundList_spec (hτ : τ<1) (hj : 0<j)
    (d₀ : H → H → ℚ) (d : Fin j → H → ℚ)
    (location : H → X) (client : Fin j → X)
    (hd₀ : ∀ f a, dist (location f) (location a)=(d₀ f a:ℝ))
    (hd : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
    (orig : F → H) (ns : List (F → ℕ)) (B : ℚ)
    (n : F → ℕ) (hn : n∈ns) (hcap : ∀ a, n a ≤ q.Δ)
    (hm : 1 ≤ ∑ a, (q.g:ℝ)*(n a:ℝ))
    (hbudget : (∑ a, (q.g:ℝ)*(n a:ℝ))+(q.allowance:ℝ) ≤ (B:ℝ))
    (r : Fin j → F → ℝ) (hr0 : ∀ c a, 0 ≤ r c a)
    (hr1 : ∀ c a, r c a ≤ (q.g:ℝ)*(n a:ℝ)) (hrsum : ∀ c, ∑ a, r c a=1) :
    ∃ O : Finset H, q.roundList d₀ d orig ns B=some O ∧ O.Nonempty ∧
      (O.card:ℝ) ≤ (B:ℝ) ∧
      (score d O:ℝ) ≤ ((1+2/Real.exp 1+τ)/(1-τ))*(∑ c,∑ a, r c a*(d c (orig a):ℝ)) := by
  obtain ⟨U,hU,hUn,hUc,hUcost⟩ := q.roundCounts_spec_s35 hτ hj
    (fun a b => d₀ (orig a) (orig b)) (fun c a => d c (orig a))
    (location ∘ orig) client (fun a b => hd₀ (orig a) (orig b)) (fun c a => hd c (orig a))
    n hcap hm r hr0 hr1 hrsum
  have hmem := q.candidate_mem d₀ d orig ns n hn U hU
  have hcard : ((U.image orig).card:ℝ) ≤ (B:ℝ) :=
    (Nat.cast_le.mpr card_image_le).trans (hUc.trans hbudget)
  have hGood : candidateGood B (U.image orig)=true := by
    apply decide_eq_true
    exact ⟨hUn.image orig,by exact_mod_cast hcard⟩
  obtain ⟨O,hO,_hOm,hOG,hOC⟩ := SparseSelect.best_of_witness (candidateGood B) (score d)
    (q.countCandidates d₀ d orig ns) (U.image orig) hmem hGood
  have hOG' := of_decide_eq_true hOG
  refine ⟨O,hO,hOG'.1,by exact_mod_cast hOG'.2,?_⟩
  have hC : (score d O:ℝ) ≤ (score (fun c a => d c (orig a)) U:ℝ) := by
    exact_mod_cast (hOC.trans_eq (score_image d orig U))
  exact hC.trans hUcost

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_RationalSupplierScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars

namespace Data
variable {f n j : ℕ} {τ : ℝ} (D : Data f n) (qR : FixedBatch.RationalParameters τ)

theorem score_reindex {X : Type} [PseudoMetricSpace X]
    (dc : Fin j → Fin f → ℚ) (i : Fin f → X) (client : Fin j → X)
    (hdc : ∀ c a, dist (client c) (i a)=(dc c a:ℝ))
    (r : Fin j → Physical (Fin f) (Fin n) → ℝ) :
    (∑ c, ∑ a : Fin (f+n*f), r c (physicalIndex a)*(dc c (original a):ℝ))=
      (∑ c,∑ a, r c a*dist (client c) (Sum.elim i (fun ti => i ti.2) a)) := by
  apply sum_congr rfl
  intro c _
  have hd : ∀ a : Fin (f+n*f), (dc c (original a):ℝ)=
      dist (client c) (Sum.elim i (fun ti => i ti.2) (physicalIndex a)) := by
    intro a
    rw [← hdc]
    unfold original
    cases physicalIndex a <;> rfl
  simp only [hd]
  exact (physicalIndex (f:=f) (n:=n)).sum_comp
    (fun a => r c a*dist (client c) (Sum.elim i (fun ti => i ti.2) a))

theorem scan_certificate_s35_oai {X : Type} [PseudoMetricSpace X]
    (hτ : τ<1) (hj : 0<j)
    (df : Fin f → Fin f → ℚ) (dc : Fin j → Fin f → ℚ)
    (i : Fin f → X) (client : Fin j → X)
    (hdf : ∀ a b, dist (i a) (i b)=(df a b:ℝ))
    (hdc : ∀ c a, dist (client c) (i a)=(dc c a:ℝ))
    (B : ℚ) (ns : List (Fin (f+n*f) → ℕ)) (n₀ : Physical (Fin f) (Fin n) → ℕ)
    (N : Fin (f+n*f) → ℕ) (hN : N∈ns)
    (heq : ∀ a, N a=n₀ (physicalIndex a))
    (hcap : ∀ a, n₀ a ≤ qR.Δ)
    (hm : 1 ≤ ∑ a, (qR.g:ℝ)*(n₀ a:ℝ))
    (hB : (∑ a, (qR.g:ℝ)*(n₀ a:ℝ))+(qR.allowance:ℝ) ≤ (B:ℝ))
    (r : Fin j → Physical (Fin f) (Fin n) → ℝ)
    (hr : ∀ c, (∀ a, 0 ≤ r c a ∧ r c a ≤ (qR.g:ℝ)*(n₀ a:ℝ)) ∧
      (∑ a, r c a)=1) :
    ∃ O : Finset (Fin f), qR.roundList df dc (original (f:=f) (n:=n)) ns B=some O ∧ O.Nonempty ∧
      (O.card:ℝ) ≤ (B:ℝ) ∧
      (Completion.Rational.score dc O:ℝ) ≤ ((1+2/Real.exp 1+τ)/(1-τ))*
        (∑ c,∑ a, r c a*dist (client c) (Sum.elim i (fun ti => i ti.2) a)) := by
  have hmass : (∑ a, (qR.g:ℝ)*(N a:ℝ)) = ∑ a, (qR.g:ℝ)*(n₀ a:ℝ) := by
    simp only [heq]
    exact (physicalIndex (f:=f) (n:=n)).sum_comp (fun a => (qR.g:ℝ)*(n₀ a:ℝ))
  obtain ⟨O,hO,hOn,hOc,hOs⟩ := qR.roundList_spec hτ hj df dc i client hdf hdc (original (f:=f) (n:=n))
    (ns) B N hN (by intro a; rw [heq]; exact hcap (physicalIndex a))
    (by rwa [hmass]) (by rwa [hmass]) (fun c a => r c (physicalIndex a))
    (fun c a => (hr c).1 (physicalIndex a) |>.1)
    (fun c a => by rw [heq]; exact ((hr c).1 (physicalIndex a)).2)
    (fun c => ((physicalIndex (f:=f) (n:=n)).sum_comp (r c)).trans (hr c).2)
  refine ⟨O,hO,hOn,hOc,?_⟩
  rwa [score_reindex dc i client hdc r] at hOs

end Data
end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Preparation.RationalSuppliers.Data.scan_certificate_s35_oai := @OAI.MetricKMedian.Preparation.RationalSuppliers.Data.scan_certificate_s35_oai
