-- Prove2me | solution 1 for OAI.MetricKMedian.Preparation.RationalSuppliers.Data.scan_feasible_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:42:09.741402+00:00
-- url     : https://prove2.me/submissions/f44c44e6-3778-40a0-a1a9-7d5cf41bf88f

import Mathlib
import Definitions.Def_OAIQ053K078
import Theorems.Thm_OAI_MetricKMedian_FixedBatch_RationalParameters_roundCounts_spec_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSelect
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
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalImageCost
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RationalPreparedScan
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
  obtain ⟨U,hU,hUn,hUc,hUcost⟩ := q.roundCounts_spec_s53 hτ hj
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
-- module Solutions.OAIQ053_KM.KMedian_Probability_FiniteJoint
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

theorem support_joint (μ : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ) (z : Ω × Ξ)
    (h : 0 < (joint μ κ).weight z) : 0 < μ.weight z.1 ∧ 0 < (κ z.1).weight z.2 := by
  exact ⟨pos_of_mul_pos_left h ((κ z.1).nonneg z.2), pos_of_mul_pos_right h (μ.nonneg z.1)⟩

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSupplierSupport
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.SparseIntegerLaw
variable {α β : Type}

theorem bindIndexed_contains (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (a : Fin μ.length) (b : Fin (κ a).length) :
    ∃ i : Fin (μ.bindIndexed κ).length, (μ.bindIndexed κ).states[i.val]=(κ a).states[b.val] := by
  let e : (Σ a : Fin μ.length, Fin (κ a).length) ≃ Fin (∑ a, (κ a).length) := finSigmaFinEquiv
  refine ⟨e ⟨a,b⟩,?_⟩
  simp only [bindIndexed,Vector.getElem_ofFn]
  change (fun z : Σ a : Fin μ.length, Fin (κ a).length => (κ z.1).states[z.2.val])
    (e.symm (e ⟨a,b⟩))=_
  rw [e.symm_apply_apply]

end MetricKMedian.SparseIntegerLaw
namespace MetricKMedian.SparsePrepared
open Finset
variable {n m f : ℕ}

theorem contains_encoded (D : Fin m → Finset (Fin n)) (a q : Fin m → ℚ) (Δ : ℕ)
    (P : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (p : Fin n → ℚ)
    (ha : ∀ e, 0 ≤ a e ∧ a e ≤ 1) (hq : ∀ e, 0 ≤ q e)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ t, 0 < p t) (hm : ∀ t, ∑ i∈P t,y i=p t)
    (b : Fin (SparseOuterLaw.law D a q ha hq).length) (ξ : Fin n → Finset (Fin f))
    (hξ : 0 < (SparseRescaledInner.encodedLaw P y p
      (total D q Δ (SparseOuterLaw.law D a q ha hq).states[b.val])).weight ξ) :
    ∃ i : Fin (law D a q Δ P y p ha hq).length,
      (law D a q Δ P y p ha hq).states[i.val]=
        ((SparseOuterLaw.law D a q ha hq).states[b.val],
          SparseBundleEncoding.decode (SparseRescaledInner.piece P y p
            (total D q Δ (SparseOuterLaw.law D a q ha hq).states[b.val])) ξ) := by
  let ν := SparseOuterLaw.law D a q ha hq
  let K := total D q Δ ν.states[b.val]
  have hK : ∀ t, K t ≤ Δ := total_le _ _ _ _
  obtain ⟨c,_hc,hc⟩ := SparseBundleEncoding.support (SparseRescaledInner.piece P y p K) K Δ
    (fun i t => ⟨SparseRescaledInner.piece_nonnegative P y p K hy hp i t,
      SparseRescaledInner.piece_cap P y p K Δ hy hp hm hK i t⟩)
    (SparseRescaledInner.piece_sum P y p K hp hm) ξ hξ
  obtain ⟨i,hi⟩ := ν.bindIndexed_contains (fun a => kernel D q Δ P y p ν.states[a.val]) b c
  refine ⟨i,hi.trans ?_⟩
  simp only [kernel,SparseIntegerLaw.map,Vector.getElem_map]
  change (ν.states[b.val],(SparseBundles.law (SparseRescaledInner.piece P y p K)).states[c.val])=_
  rw [← hc]

end MetricKMedian.SparsePrepared
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars
variable {f n : ℕ}

theorem coupled_support (y : Fin f → ℚ) (P A : Fin n → Finset (Fin f))
    (p c : Fin n → ℚ) (γ g : ℚ) (Δ : ℕ)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ t, 0 < p t)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (hm : ∀ t, ∑ i ∈ P t, y i=p t) (hc : ∀ t, ∑ i ∈ A t, y i=c t)
    (hc0 : ∀ t, 0 ≤ c t) (hc1 : ∀ t, c t ≤ 1/8) (hunit : ∀ t, p t+c t=1)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hg : 0 < g) (heven : Even Δ) (hgrid : g*(Δ:ℚ)=1) :
    let L := coupled y P A p c γ g Δ hy hp hP hm hc hc0 hc1 hunit hγ hγ1 hg heven hgrid;
    let μ := SparsePrepared.law (D A) a (q y P A c γ g) Δ P y p a_bounds
      (q_nonneg y P A c γ g hy hc0 hγ.le hg.le);
    ∀ z : L.Ω × (Fin n → Finset (Fin f)), 0 < (L.ν.joint L.κ).weight z →
      ∃ b : Fin μ.length, ∀ i,
        counts y P A c γ g μ.states[b.val] i=physicalCount L z (physicalIndex i) := by
  intro L μ z hz
  have hz' := L.ν.support_joint L.κ z hz
  obtain ⟨b,hb⟩ := SparsePrepared.contains_encoded (D A) a (q y P A c γ g) Δ P y p
    a_bounds (q_nonneg y P A c γ g hy hc0 hγ.le hg.le) hy hp hm z.1 z.2 hz'.2
  refine ⟨b,?_⟩
  intro i
  change counts y P A c γ g (SparsePrepared.law _ _ _ _ _ _ _ _ _).states[b.val] i=_
  rw [hb]
  dsimp only [counts,physicalCount,L,coupled,CoupledLaw.reindexStars,CoupledLaw.castWeights,
    SparsePrepared.coupled,SparseRescaledInner.encodedCount]
  rfl

end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RationalSupplierScan
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

theorem tables_support (heven : Even qR.Δ)
    (z : (D.coupled qR heven).Ω × (Fin n → Finset (Fin f)))
    (hz : 0 < ((D.coupled qR heven).ν.joint (D.coupled qR heven).κ).weight z) :
    ∃ N ∈ D.tables qR, ∀ a, N a=physicalCount (D.coupled qR heven) z (physicalIndex a) := by
  obtain ⟨b,hb⟩ := coupled_support D.y D.P D.A D.p D.c D.γ qR.g qR.Δ
    D.hy D.hp D.hP D.hm D.hc D.hc0 D.hc1 D.hunit D.hγ D.hγ1
    (FixedParameters.positive qR) heven (FixedParameters.grid qR) z hz
  refine ⟨counts D.y D.P D.A D.c D.γ qR.g (D.law qR).states[b.val],?_,hb⟩
  apply List.mem_map.mpr
  exact ⟨(D.law qR).states[b.val],Vector.mem_toList_iff.mpr (Vector.getElem_mem b.isLt),rfl⟩

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

theorem scan_certificate {X : Type} [PseudoMetricSpace X]
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

theorem scan_feasible_s53_oai {X : Type} [PseudoMetricSpace X]
    (heven : Even qR.Δ) (hτ : τ<1) (hj : 0<j)
    (df : Fin f → Fin f → ℚ) (dc : Fin j → Fin f → ℚ)
    (i : Fin f → X) (client : Fin j → X)
    (hdf : ∀ a b, dist (i a) (i b)=(df a b:ℝ))
    (hdc : ∀ c a, dist (client c) (i a)=(dc c a:ℝ))
    (B : ℚ) (z : (D.coupled qR heven).Ω × (Fin n → Finset (Fin f)))
    (hz : 0 < ((D.coupled qR heven).ν.joint (D.coupled qR heven).κ).weight z)
    (hcap : ∀ a, physicalCount (D.coupled qR heven) z a ≤ qR.Δ)
    (hm : 1 ≤ ∑ a, (qR.g:ℝ)*(physicalCount (D.coupled qR heven) z a:ℝ))
    (hB : (∑ a, (qR.g:ℝ)*(physicalCount (D.coupled qR heven) z a:ℝ))+(qR.allowance:ℝ) ≤ (B:ℝ))
    (r : Fin j → Physical (Fin f) (Fin n) → ℝ)
    (hr : ∀ c, (∀ a, 0 ≤ r c a ∧ r c a ≤ (qR.g:ℝ)*(physicalCount (D.coupled qR heven) z a:ℝ)) ∧
      (∑ a, r c a)=1) :
    ∃ O : Finset (Fin f), D.scan qR df dc B=some O ∧ O.Nonempty ∧
      (O.card:ℝ) ≤ (B:ℝ) ∧
      (Completion.Rational.score dc O:ℝ) ≤ ((1+2/Real.exp 1+τ)/(1-τ))*
        (∑ c,∑ a, r c a*dist (client c) (Sum.elim i (fun ti => i ti.2) a)) := by
  obtain ⟨N,hN,heq⟩ := D.tables_support qR heven z hz
  exact scan_certificate qR hτ hj df dc i client hdf hdc B (D.tables qR)
    (physicalCount (D.coupled qR heven) z) N hN heq hcap hm hB r hr

end Data
end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Preparation.RationalSuppliers.Data.scan_feasible_s53_oai := @OAI.MetricKMedian.Preparation.RationalSuppliers.Data.scan_feasible_s53_oai
