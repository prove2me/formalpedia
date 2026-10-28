-- Prove2me | solution 1 for OAI.SharpRamseyFive.SelectedTuple.eventually_high_prepared_impossible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:46:06.561449+00:00
-- url     : https://prove2.me/submissions/ee4ee42a-24b7-4411-9562-0307a05ab675

import Mathlib
import Definitions.Def_OAIQ060R004
import Theorems.Thm_OAI_SharpRamseyFive_SelectedTuple_high_prepared_round

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Beta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ParameterHierarchy
open Filter Asymptotics
open scoped Topology

lemma beta_pos {η : ℝ} (h : 0 < η) : 0 < beta η := by unfold beta; positivity

end SharpRamseyFive.ParameterHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_HighRoundNumbers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real
open scoped Topology
noncomputable section
lemma high_integer_ranges {σ q D η c : ℝ} (hη : 0<η) (hσ : 1≤σ) (hq : 2≤q)
    (hc : 0 < c) (hD : σ^beta η≤D)
    (hscale : D*σ^(3000*beta η) ≤ c*σ/4) (n : ℕ)
    (hlen : c*q*σ^(1+η)≤n) :
    let T:=⌊q*D*σ^(3000*beta η)⌋₊
    let rem:=n-T
    let h:=⌈q*σ^beta η⌉₊
    0<n ∧ 0<T ∧ 0 < rem ∧ n≤2*rem ∧ rem+T≤n ∧
      q*D*σ^(3000*beta η)/2≤T ∧ q*σ^(1+η/2)/(2/c) ≤ rem ∧
      q*σ^beta η≤h ∧ (h:ℝ)≤2*q*σ^beta η := by
  dsimp only
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hqpos : 0<q := by linarith
  have hb:=beta_pos hη
  have hD1 : 1≤D := (Real.one_le_rpow hσ hb.le).trans hD
  have hp : 1≤σ^(3000*beta η) := Real.one_le_rpow hσ (by positivity)
  let x:=q*D*σ^(3000*beta η)
  have hx : 2≤x := by
    calc
      2 ≤ q := hq
      _ = q*1*1 := by ring
      _ ≤ _ := by dsimp [x];gcongr
  have hσhi : σ≤σ^(1+η) := by
    nth_rw 1 [←Real.rpow_one σ]
    exact Real.rpow_le_rpow_of_exponent_le hσ (by linarith)
  have hT : (⌊x⌋₊:ℝ)≤x := Nat.floor_le (by linarith)
  have hTx := Nat.lt_floor_add_one x
  have hThalf : x/2≤(⌊x⌋₊:ℝ) := by linarith
  have hxn : x≤(n:ℝ)/4 := by
    calc
      _ = q*(D*σ^(3000*beta η)) := by dsimp [x];ring
      _ ≤ q*(c*σ/4) := mul_le_mul_of_nonneg_left hscale hqpos.le
      _ ≤ q*(c*σ^(1+η)/4) := by gcongr
      _ ≤ _ := by nlinarith [hlen]
  have hTn : 2*⌊x⌋₊≤n := by
    have hh : (2:ℝ)*⌊x⌋₊≤n := by linarith
    exact_mod_cast hh
  have hn0 : 0<n := by
    have : 0<(n:ℝ) := (by positivity : 0 < c*q*σ^(1+η)).trans_le hlen
    exact_mod_cast this
  have hTpos : 0<⌊x⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hTle : ⌊x⌋₊≤n := by omega
  have hrem : (n:ℝ)/2≤((n-⌊x⌋₊:ℕ):ℝ) := by
    rw [Nat.cast_sub hTle]
    have hh : (2:ℝ)*⌊x⌋₊≤n := by exact_mod_cast hTn
    linarith
  have hlrem : q*σ^(1+η/2)/(2/c)≤((n-⌊x⌋₊:ℕ):ℝ) := by
    apply le_trans _ hrem
    have hpow : σ^(1+η/2)≤σ^(1+η) := Real.rpow_le_rpow_of_exponent_le hσ (by linarith)
    calc
      _ = c*q*σ^(1+η/2)/2 := by field_simp
      _ ≤ c*q*σ^(1+η)/2 := by gcongr
      _ ≤ _ := by linarith
  have hsm : 1≤q*σ^beta η := by
    have := Real.one_le_rpow hσ hb.le
    nlinarith
  have hceil := Nat.le_ceil (q*σ^beta η)
  have hceilhi := Nat.ceil_lt_add_one (by linarith : 0≤q*σ^beta η)
  dsimp only [x] at hTn hTpos hTle hThalf hlrem
  exact ⟨hn0,hTpos,by omega,by omega,by omega,hThalf,hlrem,hceil,by linarith⟩
end
end SharpRamseyFive.ParameterHierarchy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Law
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical

variable {α β : Type*} [Fintype α] [Fintype β]

lemma atom_bound_entropy (p : Law α) (A : ℝ)
    (hpa : ∀ a,p a ≤ A) : -Real.log A ≤ entropy p := by
  have hsum : (∑ a,p a*Real.log (p a)) ≤ Real.log A := by
    calc
      _ ≤ ∑ a,p a*Real.log A := Finset.sum_le_sum fun a _ => by
        by_cases h : p a=0
        · simp [h]
        · exact mul_le_mul_of_nonneg_left
            (Real.log_le_log (lt_of_le_of_ne (p.nonneg a) (Ne.symm h)) (hpa a)) (p.nonneg a)
      _ = Real.log A := by rw [←Finset.sum_mul,p.sum_one,one_mul]
  exact neg_le_neg hsum

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_HighSampleDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.HighSamples
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] in
theorem highDomain_card (hdim : finrank K V=5) {n t : ℕ}
    (x : Fin t→Fin n→SampleFlag (K:=K) (V:=V)) :
    (highDomain x).card≤Fintype.card (ℙ K (Dual K V)) := by
  apply Finset.card_le_card_of_injOn Prod.snd (t:=Finset.univ)
    (fun _ _=>Finset.mem_univ _) ?_
  intro z hz w hw he
  have hz':=(Finset.mem_filter.mp hz).2
  have hw':=(Finset.mem_filter.mp hw).2
  have hd := Subspace.finrank_add_finrank_dualCoannihilator_eq (sampleSpan x z.2)
  rw [hdim] at hd
  have hl : finrank K (sampleSpan x z.2).dualCoannihilator≤1 := by omega
  have hzl : z.1.submodule=(sampleSpan x z.2).dualCoannihilator :=
    Submodule.eq_of_le_of_finrank_eq hz'.2 (by
      have hh:=Submodule.finrank_mono hz'.2
      rw [z.1.finrank_submodule] at hh ⊢
      omega)
  have hwl : w.1.submodule=(sampleSpan x z.2).dualCoannihilator := by
    have hwc : w.1.submodule≤(sampleSpan x z.2).dualCoannihilator := he ▸ hw'.2
    apply Submodule.eq_of_le_of_finrank_eq hwc
    have hh:=Submodule.finrank_mono hwc
    rw [w.1.finrank_submodule] at hh ⊢
    omega
  exact Prod.ext (Projectivization.submodule_injective (hzl.trans hwl.symm)) he

end
end SharpRamseyFive.HighSamples

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Hits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped BigOperators Classical
variable {α : Type*} [Fintype α]

lemma event_markov (p : Law α) (w : α → ℝ) (hw : ∀ a,0≤w a) (t : ℝ)
    (E : Finset α) (hE : ∀ a∈E,t≤w a) :
    t*eventMass p E≤∑ a,p a*w a := by
  rw [eventMass,Finset.mul_sum]
  calc
    _ ≤ ∑ a∈E,p a*w a := Finset.sum_le_sum fun a ha => by
      simpa only [mul_comm t] using mul_le_mul_of_nonneg_left (hE a ha) (p.nonneg a)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ =>
      mul_nonneg (p.nonneg a) (hw a))

end
open scoped BigOperators Classical

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_ReverseCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {A : Type*} [Fintype A]

lemma eventMass_filter_partition (p : Law A) (P : A→Prop) :
    eventMass p (Finset.univ.filter P)+
      eventMass p (Finset.univ.filter fun a=>¬P a)=1 := by
  simp only [eventMass,Finset.sum_filter,←Finset.sum_add_distrib]
  convert p.sum_one using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

lemma markov_success (p : Law A) (w : A→ℝ) (hw : ∀a,0 ≤ w a)
    (M : ℝ) (hM : 0 < M) (hmean : ∑a,p a*w a ≤ M/10) :
    (9:ℝ)/10 ≤ eventMass p (Finset.univ.filter fun a=>w a ≤ M) := by
  have hbad := event_markov p w hw M (Finset.univ.filter fun a=>¬w a ≤ M)
    (fun a ha=>(lt_of_not_ge (Finset.mem_filter.mp ha).2).le)
  have hp := eventMass_filter_partition p (fun a=>w a ≤ M)
  have hh : eventMass p (Finset.univ.filter fun a=>¬w a ≤ M) ≤ 1/10 := by
    apply (mul_le_mul_iff_of_pos_left hM).mp
    exact hbad.trans (by simpa [div_eq_mul_inv] using hmean)
  linarith

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_UnusedRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]

lemma mean_smul (p : Law α) (c : ℝ) (f : α → ℝ) : mean p (fun a => c * f a) = c * mean p f := by
  simp only [mean, Finset.mul_sum, mul_left_comm]
lemma mean_finset_sum {ι : Type*} (p : Law α) (s : Finset ι) (f : ι → α → ℝ) :
    mean p (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, mean p (f i) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm
lemma mean_sum {ι : Type*} [Fintype ι] (p : Law α) (f : ι → α → ℝ) :
    mean p (fun a => ∑ i, f i a) = ∑ i, mean p (f i) := mean_finset_sum p Finset.univ f
end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Streams_SelectedTuple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open scoped BigOperators Classical
open FiniteEntropy
variable {α ι : Type*} [Fintype α] [Fintype ι]

lemma completion_count (I : Finset ι) (v : I → α) :
    (Finset.univ.filter fun s : ι → α => ∀ i : I,s i.val = v i).card =
      Fintype.card α ^ (Fintype.card ι-I.card) := by
  classical
  have he := Fintype.card_congr (completionEquiv I v)
  rw [Fintype.card_fun,Fintype.card_subtype_compl,Fintype.card_coe] at he
  simpa only [Fintype.card_subtype] using he

variable {N l : ℕ}

lemma matching_count (I : {I : Finset (Fin N) // I.card=l}) (f : Fin l → α) :
    (matching I f).card = Fintype.card α ^ (N-l) := by
  let e := I.val.orderIsoOfFin I.property
  have he : matching I f = Finset.univ.filter fun s : Fin N → α =>
      ∀ i : I.val,s i.val = f (e.symm i) := by
    ext s
    simp only [matching,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro hs i
      have h := hs (e.symm i)
      have hi : I.val.orderEmbOfFin I.property (e.symm i) = i.val :=
        congrArg Subtype.val (e.apply_symm_apply i)
      rwa [hi] at h
    · intro hs j
      have h := hs (e j)
      change s (I.val.orderEmbOfFin I.property j) = f (e.symm (e j)) at h
      simpa only [e.symm_apply_apply] using h
  rw [he]
  convert (completion_count I.val (fun i => f (e.symm i))) using 1
  · congr
    exact Subsingleton.elim _ _
  · simp only [Fintype.card_fin,I.property]

lemma position_set_count : Fintype.card {I : Finset (Fin N) // I.card=l} = N.choose l := by
  classical
  have he : (Finset.univ.filter fun I : Finset (Fin N) => I.card=l) =
      Finset.univ.powersetCard l := by ext I; simp
  rw [Fintype.card_subtype,he,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]

theorem occurrence_count (f : Fin l → α) :
    (occurrences (N := N) f).card ≤ N.choose l * Fintype.card α^(N-l) := by
  calc
    _ ≤ ∑ I : {I : Finset (Fin N) // I.card=l},(matching I f).card :=
      Finset.card_biUnion_le
    _ = _ := by simp only [matching_count,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,position_set_count,Nat.cast_id]

theorem selected_atom [Nonempty α] (hl : l ≤ N)
    (p : Law ((Fin N → α) × (Fin l → α))) (C : ℝ) (hC : 0 ≤ C)
    (hstream : ∀ s,first p s ≤ C/(Fintype.card α:ℝ)^N)
    (rev : (Fin l → α) → (Fin l → α))
    (hselect : ∀ s f,0 < p (s,f) →
      s ∈ occurrences f ∨ s ∈ occurrences (rev f)) (f : Fin l → α) :
    second p f ≤ 2*C*(N.choose l:ℝ)/(Fintype.card α:ℝ)^l := by
  classical
  let E := occurrences (N := N) f ∪ occurrences (N := N) (rev f)
  have hm : 0 < (Fintype.card α:ℝ) := by exact_mod_cast Fintype.card_pos
  have hmass : second p f ≤ ∑ s∈E,first p s := by
    change (∑ s,p (s,f)) ≤ _
    calc
      _ ≤ ∑ s,if s∈E then first p s else 0 := by
        apply Finset.sum_le_sum
        intro s _
        by_cases hs : s ∈ E
        · simp only [hs,ite_true]
          exact le_first p s f
        · simp only [hs,ite_false]
          apply le_of_not_gt
          intro hp
          exact hs (Finset.mem_union.mpr (hselect s f hp))
      _ = _ := by rw [←Finset.sum_filter,Finset.filter_univ_mem]
  have hc : E.card ≤ 2*(N.choose l*Fintype.card α^(N-l)) := by
    exact (Finset.card_union_le _ _).trans ((add_le_add (occurrence_count f)
      (occurrence_count (rev f))).trans_eq (by ring))
  have hc' : (E.card:ℝ) ≤ 2*((N.choose l:ℝ)*(Fintype.card α:ℝ)^(N-l)) := by
    exact_mod_cast hc
  calc
    second p f ≤ ∑ s∈E,first p s := hmass
    _ ≤ ∑ _s∈E,C/(Fintype.card α:ℝ)^N := Finset.sum_le_sum fun s _ => hstream s
    _ = (E.card:ℝ)*(C/(Fintype.card α:ℝ)^N) := by simp
    _ ≤ 2*((N.choose l:ℝ)*(Fintype.card α:ℝ)^(N-l))*(C/(Fintype.card α:ℝ)^N) :=
      mul_le_mul_of_nonneg_right hc' (div_nonneg hC (pow_nonneg hm.le _))
    _ = _ := by
      have he : (Fintype.card α:ℝ)^N = (Fintype.card α:ℝ)^(N-l)*(Fintype.card α:ℝ)^l := by
        rw [←pow_add,Nat.sub_add_cancel hl]
      rw [he]
      field_simp

theorem selected_entropy [Nonempty α] (hl : l ≤ N)
    (p : Law ((Fin N → α) × (Fin l → α))) (C : ℝ) (hC : 0 ≤ C)
    (hstream : ∀ s,first p s ≤ C/(Fintype.card α:ℝ)^N)
    (rev : (Fin l → α) → (Fin l → α))
    (hselect : ∀ s f,0 < p (s,f) →
      s ∈ occurrences f ∨ s ∈ occurrences (rev f)) :
    -Real.log (2*C*(N.choose l:ℝ)/(Fintype.card α:ℝ)^l) ≤ entropy (second p) :=
  atom_bound_entropy (second p) _ (selected_atom hl p C hC hstream rev hselect)

end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_OrderedExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β κ : Type*} [Fintype α] [Fintype β] [Fintype κ]

theorem extraction_probability {n l : ℕ} (p : Law α) (S : α→Finset (Fin n))
    (hl : l<n)
    (hm : mean p (fun a=>((S a)ᶜ.card:ℝ))≤((n:ℝ)-l)/10) :
    (9:ℝ)/10≤eventMass p (Finset.univ.filter fun a=>l≤(S a).card) := by
  have hz : 0<(n:ℝ)-l := sub_pos.mpr (by exact_mod_cast hl)
  have h := markov_success p (fun a=>((S a)ᶜ.card:ℝ))
    (fun _=>Nat.cast_nonneg _) ((n:ℝ)-l) hz hm
  have he : (Finset.univ.filter fun a=>((S a)ᶜ.card:ℝ)≤(n:ℝ)-l)=
      (Finset.univ.filter fun a=>l≤(S a).card) := by
    ext a
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.card_compl,Fintype.card_fin]
    have hs : (S a).card≤n := by simpa using Finset.card_le_univ (S a)
    rw [Nat.cast_sub hs]
    constructor
    · intro hh
      have hh' : (l:ℝ)≤(S a).card := by linarith
      exact_mod_cast hh'
    · intro hh
      have hh' : (l:ℝ)≤(S a).card := by exact_mod_cast hh
      linarith
  rwa [he] at h

theorem extracted_domains {n l : ℕ} (hl : l≤n) (p : Law α)
    (x : α→Fin n→β) (S : α→Finset (Fin n)) (ctx : α→κ) (D : κ→Finset β)
    (hdom : ∀ a,0<p a→∀ i∈S a,x a i∈D (ctx a))
    (hE : 0<eventMass p (Finset.univ.filter fun a=>l≤(S a).card)) :
    ∀ z,0< map (conditionOn p _ hE) (fun a=>(ctx a,retainedTuple hl (x a) (S a))) z →
      ∀ i,z.2 i∈D z.1 := by
  intro z hz i
  obtain ⟨a,ha,rfl⟩:=map_positive _ _ z hz
  obtain ⟨he,hp⟩:=conditionOn_positive p _ hE a ha
  exact hdom a hp _ (retainedIndices_mem hl _ (Finset.mem_filter.mp he).2 i)

theorem context_tuple_entropy {ι : Type*} [Fintype ι] (p : Law (κ×(ι→β))) (D : κ→Finset β)
    (L M : ℝ) (hctx : entropy (first p)≤L)
    (hs : ∀ z,0<p z→∀ i,z.2 i∈D z.1)
    (hc : ∀ c,0<first p c→Real.log (D c).card≤M) :
    entropy (second p)≤L+Fintype.card ι*M := by
  have he : entropy p≤L+Fintype.card ι*M := by
    rw [entropy_chain]
    apply add_le_add hctx
    calc
      _ ≤ ∑ c,first p c*((Fintype.card ι:ℝ)*M) := by
        apply Finset.sum_le_sum
        intro c _
        by_cases hz : 0<first p c
        · apply mul_le_mul_of_nonneg_left _ ((first p).nonneg c)
          have hd : InDomains (fiber p c) (fun _=>D c) := by
            intro x hx i
            exact hs (c,x) (by rw [mass_eq_first_mul_fiber];exact mul_pos hz hx) i
          have ht:=totalCorrelation_nonneg (fiber p c)
          have hm : (∑ i:ι,entropy (map (fiber p c) (fun x=>x i)))≤Fintype.card ι*M := by
            calc
              _ ≤ ∑ i:ι,M := Finset.sum_le_sum fun i _=>hd.entropy_cap M (fun _=>hc c hz) i
              _ = _ := by simp
          dsimp only [totalCorrelation] at ht
          linarith
        · have hzero : first p c=0 := le_antisymm (le_of_not_gt hz) ((first p).nonneg c)
          simp [hzero]
      _ = _ := by rw [←Finset.sum_mul,(first p).sum_one,one_mul]
  have hh := entropy_map_le p Prod.snd
  have hmap : map p Prod.snd=second p := by
    ext b
    simp only [map,second,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_eq_single b]
    · rw [ite_eq_left rfl]
    · intro a _ ha
      rw [ite_eq_right ha]
    · intro hb
      exact (hb (Finset.mem_univ b)).elim
  rw [hmap] at hh
  exact hh.trans he

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.extractedFinDecEq
theorem extracted_entropy {n l : ℕ} (hl : l≤n) (p : Law α)
    (x : α→Fin n→β) (S : α→Finset (Fin n)) (ctx : α→κ) (D : κ→Finset β)
    (hdom : ∀ a,0<p a→∀ i∈S a,x a i∈D (ctx a))
    (hE : 0<eventMass p (Finset.univ.filter fun a=>l≤(S a).card))
    (L M : ℝ)
    (hctx : entropy (map (conditionOn p _ hE) ctx)≤L)
    (hc : ∀ c,Real.log (D c).card≤M) :
    entropy (map (conditionOn p _ hE) (fun a=>retainedTuple hl (x a) (S a)))≤L+l*M := by
  have hh := context_tuple_entropy (pair (conditionOn p _ hE) ctx
    (fun a=>retainedTuple hl (x a) (S a))) D L M
    (by simpa only [first_pair] using hctx)
    (extracted_domains hl p x S ctx D hdom hE) (fun c _=>hc c)
  simpa only [second_pair,Fintype.card_fin] using hh

omit [Fintype β] in
lemma log_card_le {N : ℕ} (hN : 1≤N) (S : Finset β) (hS : S.card≤N) :
    Real.log S.card≤Real.log N := by
  by_cases hz : S.card=0
  · rw [hz,Nat.cast_zero,Real.log_zero]
    exact Real.log_nonneg (by exact_mod_cast hN)
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz) (by exact_mod_cast hS)

end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FiniteKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

lemma map_adaptive_source (p : Law α) (x : α→β) (q : β→Law γ) :
    map (adaptiveLaw p (fun a=>q (x a))) (fun z=>(x z.1,z.2))=
      adaptiveLaw (map p x) q := by
  apply Law.ext_mean
  intro f
  rw [mean_map,mean_adaptive,mean_adaptive,mean_map]

lemma liftObserved_joint (p : Law α) (x : α→β) (q : Law (β×γ))
    (hq : first q=map p x) :
    map (liftObserved p x q) (fun z=>(x z.1,z.2))=q := by
  rw [liftObserved,map_adaptive_source,←hq,adaptive_reconstruct]

end

open scoped Classical BigOperators
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β] [Nonempty A]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.blockHistIndexDecEq
attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.blockHistSubtypeDecEq
theorem history_posterior_mean (p : Law (((B×A)⊕T)→β)) (S : B→Finset A)
    (n : ℕ) (x : ((B×A)⊕T)→β) :
    mean (historyLaw p S n) (fun h=>historyPosterior p h x)=p x := by
  induction n generalizing p S with
  | zero =>
    change mean (uniformType Unit) (fun _ => p x) = p x
    exact mean_const _ _
  | succ n ih =>
    change mean (sigmaLaw (freshBlockLaw S) fun s=>
      adaptiveLaw (first (reveal p (representativeSet s))) fun a=>
        historyLaw (fiber (reveal p (representativeSet s)) a) (eraseBlock S s) n)
      (fun h=>historyPosterior (fiber (reveal p (representativeSet h.1)) h.2.1) h.2.2 x)=p x
    rw [mean_sigma]
    have hpoint (s : B→A) : mean (adaptiveLaw (first (reveal p (representativeSet s))) fun a=>
        historyLaw (fiber (reveal p (representativeSet s)) a) (eraseBlock S s) n)
        (fun z=>historyPosterior (fiber (reveal p (representativeSet s)) z.1) z.2 x)=p x := by
      rw [mean_adaptive]
      simp_rw [ih]
      change (∑ a,first (reveal p (representativeSet s)) a*
        fiber (reveal p (representativeSet s)) a x)=p x
      simp_rw [←mass_eq_first_mul_fiber]
      exact congrArg (fun r : Law (((B×A)⊕T)→β)=>r x) (second_reveal p _)
    simp_rw [hpoint]
    exact mean_const _ _

end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_UniformHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

open scoped Classical BigOperators
variable {B A T β κ : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]
  [Fintype κ] [Nonempty A]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.historyProducerIndexDecEq
local instance historyProducerSubtypeDecEq_rdb4fb9_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
lemma mean_historyPosterior (p : Law (((B×A)⊕T)→β)) (S : B→Finset A)
    (n : ℕ) (f : (((B×A)⊕T)→β)→ℝ) :
    mean (historyLaw p S n) (fun h=>mean (historyPosterior p h) f)=mean p f := by
  change mean (historyLaw p S n) (fun h=>∑ x,historyPosterior p h x*f x)=_
  rw [mean_sum]
  unfold mean at ⊢
  apply Finset.sum_congr rfl
  intro x _
  have he := mean_smul (historyLaw p S n) (f x) (fun h=>historyPosterior p h x)
  rw [history_posterior_mean] at he
  simpa only [mean,mul_comm] using he

lemma preRoundTuple_context_tuple (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (n : ℕ) :
    map (preRoundTupleLaw μ p S n) (fun z=>(z.1.1.1,z.2))=adaptiveLaw μ p := by
  apply Law.ext_mean
  intro f
  rw [mean_map]
  simp only [preRoundTupleLaw,preRoundLaw,mean_adaptive]
  simp_rw [mean_const,mean_historyPosterior]

variable {Ω : Type} [Fintype Ω]

lemma historyObservation_first (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (n : ℕ) :
    first (historyObservationLaw μ p S n)=adaptiveLaw μ p := by
  have hf {X Y : Type} [Fintype X] [Fintype Y] (r : Law (X×Y)) :
      first r=map r Prod.fst := by
    apply Law.ext
    funext x
    simp only [first,map,Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp
  rw [hf,historyObservationLaw, map_comp]
  exact preRoundTuple_context_tuple μ p S n

lemma originalHistory_joint (P : Law Ω) (context : Ω→κ) (tuple : Ω→((B×A)⊕T)→β)
    (S : κ→B→Finset A) (n : ℕ) :
    map (originalHistoryLaw P context tuple S n)
      (fun z=>(((context z.1,z.2.1),z.2.2),tuple z.1))=
      preRoundTupleLaw (first (pair P context tuple)) (fiber (pair P context tuple)) S n := by
  let q:=historyObservationLaw (first (pair P context tuple)) (fiber (pair P context tuple)) S n
  have hq : first q=map P (fun ω=>(context ω,tuple ω)) := by
    dsimp [q]
    rw [historyObservation_first,adaptive_reconstruct]
    rfl
  have he:=liftObserved_joint P (fun ω=>(context ω,tuple ω)) q hq
  have hm:=congrArg (fun r=>map r (fun z=>(((z.1.1,z.2.1),z.2.2),z.1.2))) he
  dsimp [q] at hm
  rw [map_comp,historyObservationLaw,map_comp] at hm
  change map (originalHistoryLaw P context tuple S n)
    (fun z=>(((context z.1,z.2.1),z.2.2),tuple z.1))=
      map (preRoundTupleLaw (first (pair P context tuple)) (fiber (pair P context tuple)) S n) id at hm
  rwa [map_id] at hm

end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ConditionalSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
noncomputable section
variable {α β κ τ : Type*} [Fintype α] [Fintype β] [Fintype κ] [Fintype τ]

omit [Fintype β] in
lemma mem_coveredPositions {n : ℕ} (x : Fin n→β) (D : Finset β) (i : Fin n) :
    i∈coveredPositions x D ↔ x i∈D := by
  simp only [coveredPositions,Finset.mem_filter,Finset.mem_univ,true_and]

end
end

open SharpRamseyFive.Windows
open scoped Classical BigOperators

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_DeletionNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real
open scoped Topology
noncomputable section

lemma deletion_budget_monomial {σ q D k budget rounds rem C Cb Cc Cn b η : ℝ}
    (hσ : 1≤σ) (hq : 0<q) (hD : 0<D) (hk : 0≤k)
    (hCb : 0≤Cb) (hCc : 0≤Cc) (hCn : 0<Cn)
    (hb : budget≤Cb*k*D*σ^(-b))
    (hr : q*D*σ^(3000*b)/2 ≤ rounds)
    (hn : q*σ^(1+η/2)/Cn ≤ rem) (hC : C≤Cc*σ*k) :
    budget/(D*σ^b)+(2*budget/rounds+C/rem)/(σ^(-2000*b)/q)≤
      k*(Cb*σ^(-2*b)+4*Cb*σ^(-1001*b)+Cc*Cn*σ^(2000*b-η/2)) := by
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hround : 0<q*D*σ^(3000*b)/2 := by positivity
  have hrem : 0<q*σ^(1+η/2)/Cn := by positivity
  have hd : 0<D*σ^b := by positivity
  have he : 0<σ^(-2000*b)/q := by positivity
  have h1 : budget/(D*σ^b)≤Cb*k*σ^(-2*b) := by
    calc
      _ ≤ (Cb*k*D*σ^(-b))/(D*σ^b) := div_le_div_of_nonneg_right hb hd.le
      _ = Cb*k*(σ^(-b)/σ^b) := by field_simp
      _ = _ := by rw [←Real.rpow_sub hs];congr 2;ring
  have h2 : (2*budget/rounds)/(σ^(-2000*b)/q)≤4*Cb*k*σ^(-1001*b) := by
    have ht : 2*budget/rounds≤(2*(Cb*k*D*σ^(-b)))/(q*D*σ^(3000*b)/2) := by
      apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) (hround.trans_le hr).le).trans
      exact div_le_div_of_nonneg_left (by positivity) hround hr
    calc
      _ ≤ ((2*(Cb*k*D*σ^(-b)))/(q*D*σ^(3000*b)/2))/(σ^(-2000*b)/q) :=
        div_le_div_of_nonneg_right ht he.le
      _ =4*Cb*k*(σ^(-b)/(σ^(3000*b)*σ^(-2000*b))) := by field_simp;ring
      _ = _ := by rw [←Real.rpow_add hs,←Real.rpow_sub hs];congr 2;ring
  have h3 : (C/rem)/(σ^(-2000*b)/q)≤Cc*Cn*k*σ^(2000*b-η/2) := by
    have ht : C/rem≤(Cc*σ*k)/(q*σ^(1+η/2)/Cn) := by
      apply (div_le_div_of_nonneg_right hC (hrem.trans_le hn).le).trans
      exact div_le_div_of_nonneg_left (by positivity) hrem hn
    calc
      _ ≤ ((Cc*σ*k)/(q*σ^(1+η/2)/Cn))/(σ^(-2000*b)/q) :=
        div_le_div_of_nonneg_right ht he.le
      _ = Cc*Cn*k*(σ/(σ^(1+η/2)*σ^(-2000*b))) := by field_simp
      _ = _ := by
        rw [←Real.rpow_add hs]
        nth_rw 1 [←Real.rpow_one σ]
        rw [←Real.rpow_sub hs]
        congr 2
        ring
  rw [add_div]
  calc
    _ ≤ Cb*k*σ^(-2*b)+ (4*Cb*k*σ^(-1001*b)+Cc*Cn*k*σ^(2000*b-η/2)) :=
      add_le_add h1 (add_le_add h2 h3)
    _ = _ := by ring

theorem eventually_deletion_budget {η : ℝ} (hη : 0<η) (Cb Cc Cn ε : ℝ)
    (hCb : 0≤Cb) (hCc : 0≤Cc) (hCn : 0<Cn) (hε : 0<ε) :
    ∀ᶠ σ : ℝ in atTop,∀q D k budget rounds rem C : ℝ,
      0<q→0<D→0≤k→budget≤Cb*k*D*σ^(-beta η)→
      q*D*σ^(3000*beta η)/2 ≤ rounds→q*σ^(1+η/2)/Cn ≤ rem→C≤Cc*σ*k→
      budget/(D*σ^beta η)+(2*budget/rounds+C/rem)/(σ^(-2000*beta η)/q)≤ε*k := by
  have hb:=beta_pos hη
  have h1 : 0<2*beta η := by positivity
  have h2 : 0<1001*beta η := by positivity
  have h3 : 0<η/2-2000*beta η := by unfold beta;linarith
  have ht : Tendsto (fun σ : ℝ=>Cb*σ^(-2*beta η)+4*Cb*σ^(-1001*beta η)+
      Cc*Cn*σ^(2000*beta η-η/2)) atTop (𝓝 0) := by
    convert ((tendsto_rpow_neg_atTop h1).const_mul Cb).add
      ((tendsto_rpow_neg_atTop h2).const_mul (4*Cb)) |>.add
      ((tendsto_rpow_neg_atTop h3).const_mul (Cc*Cn)) using 1 <;> ring_nf
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually_lt_const hε] with σ hσ hsmall
  intro q D k budget rounds rem C hq hD hk hb hr hn hC
  exact (deletion_budget_monomial hσ hq hD hk hCb hCc hCn hb hr hn hC).trans
    (by simpa [mul_comm] using mul_le_mul_of_nonneg_left hsmall.le hk)
end
end SharpRamseyFive.ParameterHierarchy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_StageState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open scoped Classical BigOperators
open FiniteEntropy
noncomputable section
variable {α β γ Ω κ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype Ω] [Fintype κ]

namespace SelectedStream
variable {N n : ℕ} {admissible : (Fin N→α)→Prop}

theorem entropy_lower [Nonempty α] (hn : n≤N)
    (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible) :
    -Real.log (2*S.density*(N.choose n:ℝ)/(Fintype.card α:ℝ)^n)≤
      entropy (map S.law S.tuple) := by
  have hh:=selected_entropy hn (pair S.law S.stream
    (fun a=>sourceSequence S.reverse S.view (S.tuple a))) S.density S.density_nonneg
    (by simpa only [first_pair] using S.density_bound) id (by
      intro s f hp
      obtain ⟨a,ha,he⟩:=map_positive S.law
        (fun a=>(S.stream a,sourceSequence S.reverse S.view (S.tuple a))) (s,f) hp
      cases he
      exact Or.inl (S.selected a ha))
  simp only [second_pair] at hh
  have he:=entropy_map_le (map S.law S.tuple) (sourceSequence S.reverse S.view)
  rw [map_comp] at he
  exact hh.trans he

end SelectedStream
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_AllWindowBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance boundsBDE_rdb4fb9_1 (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.boundsIDE
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V))) ]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
  {w n : ℕ} [Nonempty (Fin n)] (p : Law (Slots w n→FlagPair K V))
  (u : Slots w n→ℝ) (sel : Fin w×Bool→Fin n) (E : Finset (Fin w))
  {s : ℝ} (W : ∀hE : E.Nonempty,ReciprocalWindows p u sel (survivingOriginal E hE) s)
  (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5)

lemma log_card_of_card_bound {A : Type*} (E : Finset A) (C M : ℝ)
    (hC : (E.card:ℝ)≤C) (hM : 0≤M) (hlog : Real.log C≤M) : Real.log E.card≤M := by
  by_cases he : E.card=0
  · simpa only [he,Nat.cast_zero,Real.log_zero] using hM
  · have hp : (0:ℝ)<E.card := by exact_mod_cast Nat.pos_of_ne_zero he
    exact (Real.log_le_log hp hC).trans hlog
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FlagAlphabetLogs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma point_card_le_two (hd : finrank K V=5) :
    (Fintype.card (ℙ K V):ℝ)≤2*(Nat.card K:ℝ)^4 := by
  have he : (Fintype.card (ℙ K V):ℝ)=∑i∈Finset.range 5,(Nat.card K:ℝ)^i := by
    rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hd]
    push_cast
    rfl
  rw [he]
  have hq : (2:ℝ)≤Nat.card K := by exact_mod_cast Finite.one_lt_card (α:=K)
  have ht:=q_mul_geometric_bound (Nat.card K:ℝ) hq 5
  have hq0 : (0:ℝ)<Nat.card K := by linarith
  have hh : (Nat.card K:ℝ)*(∑i∈Finset.range 5,(Nat.card K:ℝ)^i)≤
      (Nat.card K:ℝ)*(2*(Nat.card K:ℝ)^4) := by nlinarith [ht]
  exact (mul_le_mul_iff_right₀ hq0).mp hh

omit [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma point_log_card (hd : finrank K V=5) (σ : ℝ)
    (hσ : 0≤σ) (hq : Real.exp σ=Nat.card K) :
    Real.log (Fintype.card (ℙ K V))≤4*σ+Real.log 2 := by
  have hq0 : (0:ℝ)<Nat.card K := by rw [←hq];exact Real.exp_pos _
  have hlog : Real.log (2*(Nat.card K:ℝ)^4)=4*σ+Real.log 2 := by
    rw [Real.log_mul (by norm_num) (pow_pos hq0 _).ne',Real.log_pow,←hq,Real.log_exp]
    ring
  have ht:=log_card_of_card_bound (Finset.univ : Finset (ℙ K V))
    (2*(Nat.card K:ℝ)^4) (4*σ+Real.log 2) (by simpa using point_card_le_two hd)
    (by have := Real.log_nonneg (show (1:ℝ)≤2 by norm_num);positivity) hlog.le
  simpa only [Finset.card_univ] using ht

omit [FiniteDimensional K V] in
lemma flagPair_log_card (hd : finrank K V=5) (σ : ℝ)
    (hσ : 0≤σ) (hq : Real.exp σ=Nat.card K) :
    Real.log (Fintype.card (FlagPair K V))≤8*σ+Real.log 4 := by
  have hp:=point_card_le_two hd
  have hb:=point_card_le_two (K:=K) (V:=Dual K V) (by simpa using hd)
  have hq0 : (0:ℝ)<Nat.card K := by rw [←hq];exact Real.exp_pos _
  have hcap : (Fintype.card (FlagPair K V):ℝ)≤4*(Nat.card K:ℝ)^8 := by
    have hh:=mul_le_mul hp hb (Nat.cast_nonneg _) (by positivity)
    simpa only [FlagPair,Fintype.card_prod,Nat.cast_mul] using hh.trans_eq (by ring)
  have hlog : Real.log (4*(Nat.card K:ℝ)^8)=8*σ+Real.log 4 := by
    rw [Real.log_mul (by norm_num) (pow_pos hq0 _).ne',Real.log_pow,←hq,Real.log_exp]
    ring
  have ht:=log_card_of_card_bound (Finset.univ : Finset (FlagPair K V))
    (4*(Nat.card K:ℝ)^8) (8*σ+Real.log 4) (by simpa using hcap)
    (by have := Real.log_nonneg (show (1:ℝ)≤4 by norm_num);positivity) hlog.le
  simpa only [Finset.card_univ] using ht

end
end SharpRamseyFive.Marking

namespace SharpRamseyFive.SelectedTuple
open FiniteEntropy
open scoped Classical BigOperators
noncomputable section

lemma log_choose_le (N n : ℕ) (hn : 0<n) (hnN : n≤N) :
    Real.log (N.choose n)≤(n:ℝ)*(Real.log N-Real.log n+1) := by
  have hp : (0:ℝ)<n := by exact_mod_cast hn
  have hN : (0:ℝ)<N := by exact_mod_cast (lt_of_lt_of_le hn hnN)
  have hf : (0:ℝ)<n.factorial := by exact_mod_cast n.factorial_pos
  have hc : (0:ℝ)<N.choose n := by exact_mod_cast Nat.choose_pos hnN
  have h1:=Real.log_le_log hc (Nat.choose_le_pow_div (α:=ℝ) n N)
  rw [Real.log_div (pow_pos hN _).ne' hf.ne',Real.log_pow] at h1
  have h2:=Real.log_le_log (div_pos (pow_pos hp _) hf)
    (Real.pow_div_factorial_le_exp (n:ℝ) hp.le n)
  rw [Real.log_div (pow_pos hp _).ne' hf.ne',Real.log_pow,Real.log_exp] at h2
  nlinarith

variable {α β Ω : Type*} [Fintype α] [Fintype β] [Fintype Ω] [Nonempty α]
variable {N n : ℕ} {admissible : (Fin N→α)→Prop}

omit [Fintype β] [Nonempty α] in
lemma SelectedStream.density_pos (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible) :
    0<S.density := by
  have hx : 0<∑ s,map S.law S.stream s := by rw [(map S.law S.stream).sum_one]; norm_num
  obtain ⟨s,_,hs⟩:=Finset.sum_pos_iff_of_nonneg (fun s _=>(map S.law S.stream).nonneg s) |>.mp hx
  have hp:=lt_of_lt_of_le hs (S.density_bound s)
  exact (div_pos_iff.mp hp).resolve_right
    (fun h=>(pow_nonneg (Nat.cast_nonneg _) _).not_gt h.2) |>.1

theorem SelectedStream.entropy_lower_explicit (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible)
    (hn : 0<n) (hnN : n≤N) :
    (n:ℝ)*(Real.log (Fintype.card α)-Real.log N+Real.log n-1)-Real.log (2*S.density)≤
      entropy (map S.law S.tuple) := by
  have hα : (0:ℝ)<Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hc : (0:ℝ)<N.choose n := by exact_mod_cast Nat.choose_pos hnN
  have hd : 0<2*S.density := mul_pos (by norm_num) S.density_pos
  have h:=S.entropy_lower hnN
  rw [Real.log_div (mul_pos hd hc).ne' (pow_pos hα _).ne',
    Real.log_mul hd.ne' hc.ne',Real.log_pow] at h
  have hb:=log_choose_le N n hn hnN
  apply le_trans _ h
  have hh:=add_le_add_right (neg_le_neg hb)
    ((n:ℝ)*Real.log (Fintype.card α)-Real.log (2*S.density))
  convert hh using 1 <;> ring

theorem SelectedStream.flag_entropy_lower (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible)
    (σ : ℝ) (hσ : 0<σ) (hn : 0<n) (hnN : n≤N)
    (hα : 7*σ≤Real.log (Fintype.card α))
    (hN : (N:ℝ)≤Real.exp (4*σ)*σ) :
    4*σ*n+(n:ℝ)*(Real.log n-σ-Real.log σ-1)-Real.log (2*S.density)≤
      entropy (map S.law S.tuple) := by
  have hNpos : (0:ℝ)<N := by exact_mod_cast (lt_of_lt_of_le hn hnN)
  have hlogN:=Real.log_le_log hNpos hN
  rw [Real.log_mul (Real.exp_pos _).ne' hσ.ne',Real.log_exp] at hlogN
  have nn : (0:ℝ)≤n := Nat.cast_nonneg _
  have h:=S.entropy_lower_explicit hn hnN
  nlinarith

theorem SelectedStream.flag_entropy_lower_fraction
    (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible)
    (σ η c C : ℝ) (hσ : 0<σ) (hc : 0 < c) (hC : S.density≤C)
    (hn : 0<n) (hnN : n≤N) (hα : 7*σ≤Real.log (Fintype.card α))
    (hN : (N:ℝ)≤Real.exp (4*σ)*σ)
    (hlen : c*Real.exp σ*σ^(1+η)≤n) :
    4*σ*n+η*n*Real.log σ+(n:ℝ)*(Real.log c-1)-Real.log (2*C)≤
      entropy (map S.law S.tuple) := by
  have hp : 0 < c*Real.exp σ*σ^(1+η) := mul_pos (mul_pos hc (Real.exp_pos _))
    (Real.rpow_pos_of_pos hσ _)
  have hlogn:=Real.log_le_log hp hlen
  rw [Real.log_mul (mul_pos hc (Real.exp_pos _)).ne'
      (Real.rpow_pos_of_pos hσ _).ne',
    Real.log_mul hc.ne' (Real.exp_pos _).ne',Real.log_exp,
    Real.log_rpow hσ] at hlogn
  have hlogC:=Real.log_le_log (mul_pos (by norm_num : (0:ℝ)<2) S.density_pos)
    (mul_le_mul_of_nonneg_left hC (by norm_num))
  have h:=S.flag_entropy_lower σ hσ hn hnN hα hN
  have nn : (0:ℝ)≤n := Nat.cast_nonneg _
  nlinarith
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_HighEntropyNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real
open scoped Topology
noncomputable section

theorem eventually_high_entropy_contradiction {η : ℝ} (hη : 0<η)
    (c C : ℝ) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop,∀ (q n h E : ℝ),q=Real.exp σ→
      c*q*σ^(1+η)≤n→0≤h→h≤2*q*σ^beta η→
      4*σ*n+η*n*Real.log σ+n*(Real.log c-1)-Real.log (2*C)≤E→
      E≤3*h*(8*σ+Real.log 4)+n*(4*σ+Real.log 2)→False := by
  have hb : 0<η-beta η := by unfold beta;linarith
  have ht : Tendsto (fun σ : ℝ=>6*(8+Real.log 4)*σ^(-(η-beta η))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop hb).const_mul (6*(8+Real.log 4))
  have hexp : Tendsto (fun σ : ℝ=>c*Real.exp σ) atTop atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop hc
  have hlog : Tendsto (fun σ : ℝ=>η*Real.log σ) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop hη
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually_lt_const hc,
    hexp.eventually_ge_atTop (Real.log (2*C)),
    hlog.eventually_gt_atTop (Real.log 2+3-Real.log c)] with σ hσ ht he hg
  intro q n h E hq hn hh0 hh hlo hhi
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hq0 : 0<q := hq ▸Real.exp_pos σ
  have hp : 1≤σ^(1+η) := Real.one_le_rpow hσ (by linarith)
  have hn0 : 0<n := (by positivity : 0 < c*q*σ^(1+η)).trans_le hn
  have he' : Real.log (2*C)≤n := by
    calc
      _ ≤ c*q := by simpa only [hq] using he
      _ ≤ c*q*σ^(1+η) := le_mul_of_one_le_right (by positivity) hp
      _ ≤ n := hn
  have hm : 3*h*(8*σ+Real.log 4)≤n := by
    have hl4 : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
    calc
      _ ≤3*(2*q*σ^beta η)*((8+Real.log 4)*σ) := by gcongr; nlinarith
      _ =(6*(8+Real.log 4)*σ^(-(η-beta η)))*(q*σ^(1+η)) := by
        rw [show 3*(2*q*σ^beta η)*((8+Real.log 4)*σ)=
          6*(8+Real.log 4)*q*(σ^beta η*σ^(1:ℝ)) by rw [Real.rpow_one];ring]
        rw [show (6*(8+Real.log 4)*σ^(-(η-beta η)))*(q*σ^(1+η))=
          6*(8+Real.log 4)*q*(σ^(-(η-beta η))*σ^(1+η)) by ring]
        rw [←Real.rpow_add hs,←Real.rpow_add hs]
        congr 2
        ring
      _ ≤c*(q*σ^(1+η)) := mul_le_mul_of_nonneg_right ht.le (by positivity)
      _ ≤n := by simpa only [mul_assoc] using hn
  have hg' := mul_lt_mul_of_pos_right hg hn0
  nlinarith
end
end SharpRamseyFive.ParameterHierarchy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_OriginalHistoryPrivate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {B A T β κ Ω Θ : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]
  [Fintype κ] [Fintype Ω] [Fintype Θ] [Nonempty A]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.historyPrivateIDE
lemma originalHistory_mean (P : Law Ω) (context : Ω→κ) (tuple : Ω→((B×A)⊕T)→β)
    (S : κ→B→Finset A) (n : ℕ)
    (F : ((κ×BlockHistory B A T β n)×(B→A))→(((B×A)⊕T)→β)→ℝ) :
    mean (originalHistoryLaw P context tuple S n)
      (fun z=>F (((context z.1,z.2.1),z.2.2)) (tuple z.1))=
    mean (preRoundLaw (first (pair P context tuple)) (fiber (pair P context tuple)) S n)
      (fun z=>mean (historyPosterior (fiber (pair P context tuple) z.1.1) z.1.2) (F z)) := by
  have h:=congrArg (fun p=>mean p (fun z=>F z.1 z.2))
    (originalHistory_joint P context tuple S n)
  simpa only [mean_map,preRoundTupleLaw,mean_adaptive] using h

end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Streams_HighActualExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.HighSamples
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype Ω] [Fintype κ]

attribute [local instance] OAI.SharpRamseyFive.HighSamples.highExtractionFinDecEq
omit [Finite K] in
theorem high_extracted_entropy (hdim : finrank K V=5) {m l h : ℕ} (hl : l ≤ m)
    (p : Law Ω) (x : Ω→Fin m→SampleFlag (K:=K) (V:=V))
    (samples : Ω→Fin 3→Fin h→SampleFlag (K:=K) (V:=V))
    (hE : 0<eventMass p (Finset.univ.filter fun a=>l≤(coveredPositions (x a) (highDomain (samples a))).card)) :
    entropy (map (conditionOn p _ hE) (fun a=>retainedTuple hl (x a)
      (coveredPositions (x a) (highDomain (samples a)))))≤
      3*h*Real.log (Fintype.card (SampleFlag (K:=K) (V:=V)))+
        l*Real.log (Fintype.card (ℙ K (Dual K V))) := by
  have hd : 0<finrank K (Dual K V) := by simp [hdim]
  let : Nontrivial (Dual K V) := Module.nontrivial_of_finrank_pos hd
  have hQ : 1≤Fintype.card (ℙ K (Dual K V)) := Fintype.card_pos
  apply extracted_entropy hl p x
    (fun a=>coveredPositions (x a) (highDomain (samples a))) samples highDomain
    (fun a _ i hi=>(mem_coveredPositions _ _ _).mp hi) hE
  · have hc:=entropy_le_log_card (map (conditionOn p _ hE) samples)
    simpa only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,
      mul_assoc,mul_left_comm,mul_comm] using hc
  · intro t
    exact log_card_le hQ _ (highDomain_card hdim t)

end
end SharpRamseyFive.HighSamples

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_HistoryPrivateStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking
open scoped Classical LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype Ω] [Fintype κ] [Fintype α]
  {N w n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}

attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.hpsBDE
local instance hpsTDE_rdb4fb9_1 : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.hpsIDE
omit [Finite K] [FiniteDimensional K V] in
lemma historyStream_law (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (elig : κ→Fin w×Bool→Finset (Fin n)) (steps : ℕ) :
    (historyStream S ctx elig steps).law=originalHistoryLaw S.law ctx (windowTuple S) elig steps := rfl

end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_HighWindowStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking HighSamples
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}

attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.hwsBDE
local instance hwsTDE_rdb4fb9_1 : DecidableEq (Fin 1×Fin (2*n)) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.hwsIDE
variable (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (1*(4*n)) admissible)
  (ctx : Ω→κ) (elig : κ→Fin 1×Bool→Finset (Fin n)) (steps r' : ℕ) (s : ℝ) (h : ℕ)

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma highSampleStream_loss_mean :
    mean (highSampleStream S ctx elig steps r' s h).law
      (fun z=>((coveredPositions ((highSampleStream S ctx elig steps r' s h).tuple z)
        (highDomain z.2))ᶜ.card:ℝ))=
    mean (adaptiveLaw (preRoundTupleLaw (first (pair S.law ctx (windowTuple S)))
      (fiber (pair S.law ctx (windowTuple S))) elig steps)
      (fun z=>highFourSampler (fiber (pair S.law ctx (windowTuple S))) r' s h z.1))
      (fun z=>((coveredPositions (fun t=>z.1.2 (Sum.inr (0,t))) (highDomain z.2))ᶜ.card:ℝ)) := by
  dsimp only [highSampleStream,SelectedStream.augment,SelectedStream.reindex]
  rw [historyStream_law,mean_adaptive]
  have he:=originalHistory_mean S.law ctx (windowTuple S) elig steps
    (fun z x=>mean (highFourSampler (fiber (pair S.law ctx (windowTuple S))) r' s h z)
      (fun v=>((coveredPositions (fun t=>x (Sum.inr (0,t))) (highDomain v))ᶜ.card:ℝ)))
  simp only [preRoundTupleLaw,mean_adaptive]
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg (mean _)
  funext z
  rfl

omit [Finite K] [Fintype (ℙ K (Dual K (Dual K V)))] in
theorem highSampleStream_extract (hdim : finrank K V=5) {l : ℕ} (hl : l<2*n)
    (hloss : mean (adaptiveLaw (preRoundTupleLaw (first (pair S.law ctx (windowTuple S)))
      (fiber (pair S.law ctx (windowTuple S))) elig steps)
      (fun z=>highFourSampler (fiber (pair S.law ctx (windowTuple S))) r' s h z.1))
      (fun z=>((coveredPositions (fun t=>z.1.2 (Sum.inr (0,t))) (highDomain z.2))ᶜ.card:ℝ))≤
        ((2*n:ℝ)-l)/10) :
    ∃ hE : 0<eventMass (highSampleStream S ctx elig steps r' s h).law
      (Finset.univ.filter fun z=>l≤(coveredPositions ((highSampleStream S ctx elig steps r' s h).tuple z)
        (highDomain z.2)).card),
      let S':=((highSampleStream S ctx elig steps r' s h).restrict _ hE).extract hl.le
        (fun z=>coveredPositions ((highSampleStream S ctx elig steps r' s h).tuple z) (highDomain z.2))
      S'.density≤(10/9)*S.density ∧
      entropy (map S'.law S'.tuple)≤3*h*Real.log (Fintype.card (FlagPair K V))+
        l*Real.log (Fintype.card (ℙ K (Dual K V))) := by
  let T:=highSampleStream S ctx elig steps r' s h
  let E:=Finset.univ.filter (fun z=>l≤(coveredPositions (T.tuple z) (highDomain z.2)).card)
  have hp : (9:ℝ)/10≤eventMass T.law E := by
    apply extraction_probability _ _ hl
    convert (highSampleStream_loss_mean S ctx elig steps r' s h).trans_le hloss using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Nat.cast_mul,Nat.cast_ofNat]
  have hE : 0<eventMass T.law E := lt_of_lt_of_le (by norm_num) hp
  refine ⟨hE,?_,?_⟩
  · change S.density/eventMass T.law E≤(10/9)*S.density
    calc
      _ ≤S.density/(9/10) := div_le_div_of_nonneg_left S.density_nonneg (by norm_num) hp
      _ =_ := by ring
  · convert high_extracted_entropy hdim hl.le T.law T.tuple (fun z=>z.2) hE using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    exact Subsingleton.elim _ _
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_HighNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Filter Asymptotics Real ParameterHierarchy FiniteEntropy
open scoped Topology
noncomputable section

lemma high_bad_uniform {σ D b C : ℝ} (hσ : 1≤σ) (_ : 0<b)
    (hD : σ^b≤D) (hC : 0≤C) :
    highBadMass (D*σ^(3*b)) (D*σ^b) C≤
      Real.exp (-σ^(4*b))+51*σ^(-2*b)+(50*C+Real.log 2+32)/σ^(4*b) := by
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hd : 0<D := (Real.rpow_pos_of_pos hs b).trans_le hD
  have hlow : σ^(4*b)≤D*σ^(3*b) := by
    calc
      _ = σ^b*σ^(3*b) := by rw [←Real.rpow_add hs];congr 1;ring
      _ ≤_ := mul_le_mul_of_nonneg_right hD (by positivity)
  have he : (D*σ^b)/(D*σ^(3*b))=σ^(-2*b) := by
    rw [mul_div_mul_left _ _ hd.ne',←Real.rpow_sub hs]
    congr 1
    ring
  have hc : 0≤50*C+Real.log 2+32 := by have := Real.log_nonneg (by norm_num : (1:ℝ)≤2);positivity
  have hc' := div_le_div_of_nonneg_left hc (Real.rpow_pos_of_pos hs _) hlow
  unfold highBadMass
  calc
    _ =Real.exp (-(D*σ^(3*b)))+51*((D*σ^b)/(D*σ^(3*b)))+
      (50*C+Real.log 2+32)/(D*σ^(3*b)) := by ring
    _ ≤_ := by rw [he];gcongr

lemma high_four_variance {q s σ : ℝ} {r' : ℕ} (hq : 1≤q)
    (he : Real.exp σ=q) (hr : 2 ≤ r') (hs : 2*s≤σ/2) :
    64*q^5*(2*Real.exp s/q^r')*(Real.exp s/q^4)≤128*Real.exp (-σ/2) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hp := pow_le_pow_right₀ hq hr
  calc
    _ ≤64*q^5*(2*Real.exp s/q^2)*(Real.exp s/q^4) := by gcongr
    _ =128*(Real.exp s*Real.exp s/q) := by field_simp;ring
    _ =128*Real.exp (2*s-σ) := by rw [Real.exp_sub,←Real.exp_add,he];congr 2;congr 1;ring
    _ ≤_ := by gcongr;linarith

lemma high_four_growth {q σ b : ℝ} {h : ℕ} (hq : 1≤q)
    (hl : q*σ^b≤h) :
    (1-1/(5*q))^h≤Real.exp (-(σ^b)/5) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hnon : 0≤1-1/(5*q) := by
    have hh : 1/(5*q)≤1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  calc
    _ ≤(Real.exp (-(1/(5*q))))^h := pow_le_pow_left₀ hnon (Real.one_sub_le_exp_neg _) h
    _ = Real.exp (-(h:ℝ)/(5*q)) := by rw [←Real.exp_nat_mul];congr 1;ring
    _ ≤_ := by
      apply Real.exp_le_exp.mpr
      have hh : σ^b/5≤(h:ℝ)/(5*q) := (le_div_iff₀ (by positivity)).mpr (by nlinarith [hl])
      simpa only [neg_div] using neg_le_neg hh

lemma high_four_conflict {σ q b : ℝ} {h : ℕ} (hσ : 0<σ) (hq : 0<q)
    (hh : (h:ℝ)≤2*q*σ^b) :
    12*h*(σ^(-2000*b)/q)≤24*σ^(-1999*b) := by
  calc
    _ ≤12*(2*q*σ^b)*(σ^(-2000*b)/q) := by gcongr
    _ =24*(σ^b*σ^(-2000*b)) := by field_simp;ring
    _ =_ := by rw [←Real.rpow_add hσ];congr 2;ring

lemma highFourLoss_bound {σ D b : ℝ} {q r' h : ℕ}
    (hσ : 1≤σ) (hb : 0<b) (hD : σ^b≤D) (hq : 1≤q)
    (he : Real.exp σ=q) (hr : 2 ≤ r') (hs : 2*(D*σ^(3*b))≤σ/2)
    (hl : (q:ℝ)*σ^b≤h) (hh : (h:ℝ)≤2*q*σ^b) :
    highFourLoss q r' h (D*σ^(3*b)) (D*σ^b) (σ^(-2000*b)/q)≤
      Real.exp (-σ^(4*b))+51*σ^(-2*b)+(50*153+Real.log 2+32)/σ^(4*b)+
      128*Real.exp (-σ/2)+3*Real.exp (-(σ^b)/5)+24*σ^(-1999*b) := by
  unfold highFourLoss
  have hq' : (1:ℝ)≤q := by exact_mod_cast hq
  apply add_le_add
  · apply add_le_add
    · exact add_le_add (high_bad_uniform hσ hb hD (by norm_num)) (high_four_variance hq' he hr hs)
    · exact mul_le_mul_of_nonneg_left (high_four_growth hq' hl) (by norm_num)
  · exact high_four_conflict (zero_lt_one.trans_le hσ) (zero_lt_one.trans_le hq') hh

theorem eventually_high_four_loss {η : ℝ} (hη : 0<η) (ρ : ℝ) (hρ : 0<ρ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (q r' h : ℕ),σ^beta η≤D→D≤σ^(1-η/2)→
      1≤q→Real.exp σ=q→2 ≤ r'→(q:ℝ)*σ^beta η≤h→(h:ℝ)≤2*q*σ^beta η→
      highFourLoss q r' h (D*σ^(3*beta η)) (D*σ^beta η) (σ^(-2000*beta η)/q)≤ρ := by
  have hb:=beta_pos hη
  have hpow:=tendsto_rpow_atTop hb
  have h4 : 0<4*beta η := by positivity
  have ht1 := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_rpow_atTop h4)
  have ht2 := (tendsto_rpow_neg_atTop (by positivity : 0<2*beta η)).const_mul 51
  have ht3 : Tendsto (fun σ : ℝ=>(50*153+Real.log 2+32)/σ^(4*beta η)) atTop (𝓝 0) :=
    (tendsto_rpow_atTop h4).const_div_atTop _
  have ht4 : Tendsto (fun σ : ℝ=>128*Real.exp (-σ/2)) atTop (𝓝 0) := by
    have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<2))
    simpa only [Function.comp_apply,id_eq,neg_div,mul_zero] using ht.const_mul 128
  have ht5 : Tendsto (fun σ : ℝ=>3*Real.exp (-(σ^beta η)/5)) atTop (𝓝 0) := by
    have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hpow.atTop_div_const (by norm_num : (0:ℝ)<5))
    simpa only [Function.comp_apply,id_eq,neg_div,mul_zero] using ht.const_mul 3
  have ht6 := (tendsto_rpow_neg_atTop (by positivity : 0<1999*beta η)).const_mul 24
  have ht:=((((ht1.add ht2).add ht3).add ht4).add ht5).add ht6
  simp only [Function.comp_apply,mul_zero,add_zero] at ht
  have he : 0<η/2-3*beta η := by unfold beta;linarith
  have hsmall:=(tendsto_rpow_neg_atTop he).eventually_lt_const (by norm_num : (0:ℝ)<1/4)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually_lt_const hρ,hsmall] with σ hσ hρ' hsmall
  intro D q r' h hlo hhi hq heq hr hhlo hhhi
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hDsmall : 2*(D*σ^(3*beta η))≤σ/2 := by
    have hl : D*σ^(3*beta η)≤σ*σ^(-(η/2-3*beta η)) := by
      calc
        _ ≤σ^(1-η/2)*σ^(3*beta η) := mul_le_mul_of_nonneg_right hhi (by positivity)
        _ =_ := by
          rw [←Real.rpow_add hs]
          nth_rw 2 [←Real.rpow_one σ]
          rw [←Real.rpow_add hs]
          congr 1
          ring
    nlinarith [mul_lt_mul_of_pos_left hsmall hs]
  exact (highFourLoss_bound hσ hb hlo hq heq hr hDsmall hhlo hhhi).trans (by simpa only [neg_mul] using hρ'.le)
end
end

open Filter Real ParameterHierarchy FiniteEntropy
open scoped Topology
noncomputable section

lemma eventually_stage_scale {η : ℝ} (_ : 0<η) (a δ : ℝ)
    (ha : a*beta η<η/2) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀D : ℝ,D≤σ^(1-η/2)→D*σ^(a*beta η)≤δ*σ := by
  have he : 0<η/2-a*beta η := sub_pos.mpr ha
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_neg_atTop he).eventually_lt_const hδ] with σ hσ ht
  intro D hD
  have hs : 0<σ := zero_lt_one.trans_le hσ
  calc
    _ ≤ σ^(1-η/2)*σ^(a*beta η) := mul_le_mul_of_nonneg_right hD (by positivity)
    _ = σ^(-(η/2-a*beta η))*σ := by
      rw [←Real.rpow_add hs,show 1-η/2+a*beta η= -(η/2-a*beta η)+1 by ring,
        Real.rpow_add hs,Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right ht.le hs.le

lemma highBadMass_le_highFourLoss (q r' h : ℕ) (hq : 1≤q) (s d ε : ℝ) (he : 0≤ε) :
    highBadMass s d 153≤highFourLoss q r' h s d ε := by
  have hq' : (1:ℝ)≤q := by exact_mod_cast hq
  have hh : 0<5*(q:ℝ) := by linarith
  have hz : 0≤1-1/(5*(q:ℝ)) := sub_nonneg.mpr ((div_le_one hh).mpr (by linarith))
  unfold highFourLoss
  have h1 : 0≤64*(q:ℝ)^5*(2*Real.exp s/(q:ℝ)^r')*(Real.exp s/(q:ℝ)^4) := by positivity
  have h2 : 0≤3*(1-1/(5*(q:ℝ)))^h := by positivity
  have h3 : 0≤12*h*ε := by positivity
  linarith

lemma high_small_geometry {q s ε : ℝ} (hq : 0<q)
    (h1 : 80*Real.exp s≤q) (h2 : 256*Real.exp (2*s)≤q)
    (h3 : 640032*(ε*q)<1) :
    2*q^2*(2*Real.exp s/q^4)≤1/(20*q) ∧
    64*q^5*(Real.exp s/q^3)*(Real.exp s/q^3)≤(1:ℝ)/4 ∧
    80004*ε<1/(8*q) := by
  refine ⟨?_,?_,?_⟩
  · apply (le_div_iff₀ (by positivity : 0<20*q)).mpr
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg q)]
  · have he : Real.exp (2*s)=Real.exp s*Real.exp s := by rw [two_mul,Real.exp_add]
    rw [he] at h2
    have hh : 64*q^5*(Real.exp s/q^3)*(Real.exp s/q^3)=64*Real.exp s*Real.exp s/q := by field_simp
    rw [hh]
    exact (div_le_iff₀ hq).mpr (by linarith)
  · apply (lt_div_iff₀ (by positivity : 0<8*q)).mpr
    nlinarith

theorem eventually_high_geometry {η : ℝ} (hη : 0<η) :
    ∀ᶠ σ : ℝ in atTop,∀D : ℝ,D≤σ^(1-η/2)→
      2*(Real.exp σ)^2*(2*Real.exp (D*σ^(3*beta η))/(Real.exp σ)^4)≤1/(20*Real.exp σ) ∧
      64*(Real.exp σ)^5*(Real.exp (D*σ^(3*beta η))/(Real.exp σ)^3)*
        (Real.exp (D*σ^(3*beta η))/(Real.exp σ)^3)≤(1:ℝ)/4 ∧
      80004*(σ^(-2000*beta η)/Real.exp σ)<1/(8*Real.exp σ) := by
  have ha : 3*beta η<η/2 := by unfold beta;linarith
  have ht : Tendsto (fun σ : ℝ=>640032*σ^(-2000*beta η)) atTop (𝓝 0) := by
    have hb : 0<2000*beta η := by exact mul_pos (by norm_num) (beta_pos hη)
    simpa only [neg_mul,mul_zero] using (tendsto_rpow_neg_atTop hb).const_mul 640032
  filter_upwards [eventually_stage_scale hη 3 (1/4) ha (by norm_num),
    eventually_ge_atTop (4*Real.log 256),eventually_ge_atTop (0:ℝ),
    ht.eventually_lt_const (by norm_num : (0:ℝ)<1)] with σ hscale hσ hσ0 he
  intro D hD
  have hs:=hscale D hD
  apply high_small_geometry (Real.exp_pos σ)
  · calc
      _ ≤256*Real.exp (D*σ^(3*beta η)) := mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_nonneg _)
      _ =Real.exp (Real.log 256+D*σ^(3*beta η)) := by rw [Real.exp_add,Real.exp_log (by norm_num)]
      _ ≤_ := Real.exp_le_exp.mpr (by linarith)
  · calc
      _ =Real.exp (Real.log 256+2*(D*σ^(3*beta η))) := by rw [Real.exp_add,Real.exp_log (by norm_num)]
      _ ≤_ := Real.exp_le_exp.mpr (by linarith)
  · simpa only [div_mul_cancel₀ _ (Real.exp_ne_zero σ)] using he
end

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Streams_HighSampleContradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple

section
open Module ProjectiveIncidence FiniteEntropy Windows Marking HighSamples Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section

local instance hscBDE_rdb4fb9_1 : DecidableEq (Fin 1×Bool) := Classical.decEq _
local instance hscTDE_rdb4fb9_1 (n : ℕ) : DecidableEq (Fin 1×Fin (2*n)) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.hscIDE
theorem eventually_high_sample_impossible {η : ℝ} (hη : 0<η) (c C : ℝ) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop,∀ (K V Ω κ α : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α] [Nonempty α],
    ∀ (N n l steps r' h : ℕ) [Nonempty (Fin n)] (admissible : (Fin N→α)→Prop)
      (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (1*(4*n)) admissible)
      (ctx : Ω→κ) (elig : κ→Fin 1×Bool→Finset (Fin n)) (s : ℝ),
      finrank K V=5→1≤σ→Real.exp σ=Nat.card K→
      7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→l≤N→l<2*n→
      c*Real.exp σ*σ^(1+η)≤l→S.density≤C→(h:ℝ)≤2*Real.exp σ*σ^beta η→
      mean (adaptiveLaw (preRoundTupleLaw (first (pair S.law ctx (windowTuple S)))
        (fiber (pair S.law ctx (windowTuple S))) elig steps)
        (fun z=>highFourSampler (fiber (pair S.law ctx (windowTuple S))) r' s h z.1))
        (fun z=>((coveredPositions (fun t=>z.1.2 (Sum.inr (0,t))) (highDomain z.2))ᶜ.card:ℝ))≤
          ((2*n:ℝ)-l)/10→False := by
  filter_upwards [eventually_high_entropy_contradiction hη c ((10/9)*C) hc] with σ hnum
  intro K V Ω κ α _ _ _ _ _ _ _ _ _ _ _ _ N n l steps r' h _ admissible S ctx elig s
    hd hσ hq hα hN hlN hl hlen hC hh hloss
  obtain ⟨hE,hden,hent⟩:=highSampleStream_extract S ctx elig steps r' s h hd hl hloss
  let T:=highSampleStream S ctx elig steps r' s h
  let S':=(T.restrict _ hE).extract hl.le
    (fun z=>coveredPositions (T.tuple z) (highDomain z.2))
  have hlenpos : 0<(l:ℝ) := (by positivity : 0 < c*Real.exp σ*σ^(1+η)).trans_le hlen
  have hl0 : 0<l := by exact_mod_cast hlenpos
  have hden' : S'.density≤(10/9)*C := hden.trans (mul_le_mul_of_nonneg_left hC (by norm_num))
  have hlo:=S'.flag_entropy_lower_fraction σ η c ((10/9)*C)
    (zero_lt_one.trans_le hσ) hc hden' hl0 hlN hα hN hlen
  have hhi : entropy (map S'.law S'.tuple)≤3*h*(8*σ+Real.log 4)+(l:ℝ)*(4*σ+Real.log 2) := by
    apply hent.trans
    exact add_le_add
      (mul_le_mul_of_nonneg_left (flagPair_log_card hd σ (zero_le_one.trans hσ) hq) (by positivity))
      (mul_le_mul_of_nonneg_left (point_log_card (K:=K) (V:=Dual K V)
        (by simpa using hd) σ (zero_le_one.trans hσ) hq) (by positivity))
  exact hnum (Real.exp σ) l h (entropy (map S'.law S'.tuple)) rfl hlen
    (Nat.cast_nonneg _) hh hlo hhi
end
end

open Module ProjectiveIncidence FiniteEntropy Windows Marking HighSamples
open scoped Classical BigOperators LinearAlgebra.Projectivization

end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Streams_SelectedLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple

section
open FiniteEntropy
noncomputable section
variable {Ω α β : Type} [Fintype Ω] [Fintype α] [Fintype β]
  {N n : ℕ} {admissible : (Fin N→α)→Prop}
omit [Fintype β] in
lemma SelectedStream.length_le_source (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible) : n≤N := by
  obtain ⟨z,hz⟩:=S.law.exists_positive
  obtain ⟨e,he⟩:=(mem_occurrences_iff _ _).mp (S.selected z hz)
  have h:=Fintype.card_le_of_injective e e.injective
  simpa only [Fintype.card_fin] using h
end
end

open Module ProjectiveIncidence FiniteEntropy Windows Marking HighSamples Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section

theorem eventually_high_prepared_impossible_oai {η : ℝ} (hη : 0<η) (c C Cb : ℝ)
    (hc : 0 < c) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (K V Ω κ α : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))] [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
      [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α] [Nonempty α],
    ∀ (N n r' : ℕ) [Nonempty (Fin n)] (admissible : (Fin N→α)→Prop)
      (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (1*(4*n)) admissible)
      (ctx : Ω→κ) (D J B M : ℝ) (P : Prepared S ctx J B M),
      finrank K V=5→1≤σ→Real.exp σ=Nat.card K→
      7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→
      c*Real.exp σ*σ^(1+η)≤n→S.density≤C→
      σ^beta η≤D→D≤σ^(1-η/2)→B≤Cb*n*D*σ^(-beta η)→4*σ≤J→
      2 ≤ r' → r' ≤ 4→(∀a,0 < map S.law ctx a→∀i,HighCaps (P.domain a i) 4 r')→False := by
  have ha : 3000*beta η<η/2 := by unfold beta;linarith
  filter_upwards [eventually_high_sample_impossible hη c C hc,
    eventually_deletion_budget hη Cb 0 (2/c) (1/1000) hCb le_rfl (by positivity) (by norm_num),
    eventually_high_four_loss hη (1/1000) (by norm_num),eventually_high_geometry hη,
    eventually_stage_scale hη 3000 (c/4) ha (by positivity)] with σ hcontra hdel hfour hgeom hscale
  intro K V Ω κ α _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N n r' _ admissible S ctx D J B M P
    hd hσ hq hα hN hlen hC hD hDhi hB hJ hrlo hrhi hcap
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hqp : 2≤Nat.card K := Nat.succ_le_of_lt (Finite.one_lt_card (α:=K))
  have hqr : (2:ℝ)≤Nat.card K := by exact_mod_cast hqp
  have hqpos : (0:ℝ)<Nat.card K := by linarith
  have hDpos : 0<D := (Real.rpow_pos_of_pos hs _).trans_le hD
  have hσeq : Real.log (Nat.card K)=σ := by rw [←hq,Real.log_exp]
  let T:=⌊(Nat.card K:ℝ)*D*σ^(3000*beta η)⌋₊
  let rem:=n-T
  let h:=⌈(Nat.card K:ℝ)*σ^beta η⌉₊
  obtain ⟨hn,hT,hrem,hnrem,hroom,hTlo,hremlo,hhlo,hhhi⟩:=
    high_integer_ranges hη hσ hqr hc hD (by nlinarith [hscale D hDhi]) n (by simpa only [hq] using hlen)
  have hfour':=hfour D (Nat.card K) r' h hD hDhi (by omega) hq hrlo hhlo hhhi
  have hgeom':=hgeom D hDhi
  rw [hq] at hgeom'
  have hbudget:=hdel (Nat.card K) D n B T rem 0 hqpos hDpos (Nat.cast_nonneg _) hB hTlo hremlo (by simp)
  simp only [zero_div,add_zero] at hbudget
  have hε : 0<σ^(-2000*beta η)/(Nat.card K:ℝ) := by positivity
  have hbad : highBadMass (D*σ^(3*beta η)) (D*σ^beta η) 153≤(1:ℝ)/4 :=
    (highBadMass_le_highFourLoss (Nat.card K) r' h (by omega) _ _ _ hε.le).trans
      (hfour'.trans (by norm_num))
  obtain ⟨i,hi⟩:=high_prepared_round hd S ctx J B M P r' hrhi hcap T rem hT hrem hnrem hroom
    (D*σ^beta η) (D*σ^(3*beta η)) (σ^(-2000*beta η)/(Nat.card K:ℝ))
    (by simpa only [hσeq] using hJ) (by positivity) (by positivity) hε hbad hgeom'.1 h
  have hlN : n≤N := by have:=S.length_le_source;omega
  apply hcontra K V Ω κ α N n n i.val r' h admissible S ctx (fun _ _=>Finset.univ)
    (D*σ^(3*beta η)) hd hσ hq hα hN hlN (by omega) hlen hC
    (by simpa only [hq] using hhhi)
  apply hi.trans
  have hm:=mul_le_mul_of_nonneg_left hfour' (by positivity : (0:ℝ)≤2*n)
  have hd':=mul_le_mul_of_nonneg_left hbudget (by norm_num : (0:ℝ)≤5)
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at *
  nlinarith [(Nat.cast_nonneg n : (0:ℝ)≤n)]
end

end SharpRamseyFive.SelectedTuple

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.SelectedTuple.eventually_high_prepared_impossible_oai := @OAI.SharpRamseyFive.SelectedTuple.eventually_high_prepared_impossible_oai
