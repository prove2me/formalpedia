-- Prove2me | solution 1 for OAI.SharpRamseyFive.SelectedTuple.eventually_reciprocal_coded_stage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:48:40.811433+00:00
-- url     : https://prove2.me/submissions/095e91ba-ce42-4de4-a5e0-35abe9c165c2

import Mathlib
import Definitions.Def_OAIQ060R004
import Theorems.Thm_OAI_SharpRamseyFive_Marking_eventually_actual_reciprocal_loss
import Theorems.Thm_OAI_SharpRamseyFive_ProjectiveIncidence_eventually_allWindow_cost
import Theorems.Thm_OAI_SharpRamseyFive_SelectedTuple_reciprocal_prepared_round_sharp

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_FinsetEquivPositions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive
open scoped Classical
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
lemma mem_equivPositions (e : A≃B) (S : Finset A) (i : B) :
    i∈equivPositions e S ↔ e.symm i∈S := by
  simp [equivPositions]
lemma equivPositions_compl_card (e : A≃B) (S : Finset A) :
    (equivPositions e S)ᶜ.card=Sᶜ.card := by
  rw [Finset.card_compl,Finset.card_compl]
  simp only [equivPositions,Finset.card_map,Fintype.card_congr e]
end
end SharpRamseyFive

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
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_BlockSelected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

open scoped Classical BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem fix_independent_table (p : Law α) (tables : Law β) (E : β→Finset α)
    (c : ℝ) (havg : c≤ mean tables (fun t=>eventMass p (E t))) :
    ∃ t,0<tables t ∧ c≤eventMass p (E t) := by
  obtain ⟨t,ht,he⟩:=mean_exists_ge tables (fun t=>eventMass p (E t))
  exact ⟨t,ht,havg.trans he⟩
end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_CapDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype B]

lemma cap_subset (R : A→B→Prop) (U : Finset A) {n : ℕ} (q : ℝ) (row : Fin n→B) :
    cap R U q row⊆U := Finset.filter_subset _ _

end SharpRamseyFive.ReverseCap

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MessageWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.MessageWeights
open scoped BigOperators
universe u v

lemma log_card_weight (A : Type u) [Fintype A] :
    (∑_a : A,Real.exp (-Real.log (Fintype.card A:ℝ)))≤1 := by
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  by_cases h : Fintype.card A=0
  · simp [h]
  · have hp : (0:ℝ)<Fintype.card A := by exact_mod_cast Nat.pos_of_ne_zero h
    rw [Real.exp_neg,Real.exp_log hp]
    exact le_of_eq (mul_inv_cancel₀ hp.ne')

lemma sigma_weight_le (A : Type u) [Fintype A] (B : A→Type v) [∀a,Fintype (B a)]
    (c : A→ℝ) (d : ∀a,B a→ℝ)
    (hc : (∑a,Real.exp (-c a))≤1) (hd : ∀a,(∑b,Real.exp (-d a b))≤1) :
    (∑m : Sigma B,Real.exp (-(c m.1+d m.1 m.2)))≤1 := by
  rw [Fintype.sum_sigma]
  apply le_trans _ hc
  apply Finset.sum_le_sum
  intro a _
  simp only [neg_add,Real.exp_add,←Finset.mul_sum]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hd a) (Real.exp_pos (-c a)).le

lemma sigma_header_weight (A : Type u) [Fintype A] (B : A→Type v) [∀a,Fintype (B a)]
    (d : ∀a,B a→ℝ) (hd : ∀a,(∑b,Real.exp (-d a b))≤1) :
    (∑m : Sigma B,Real.exp (-(Real.log (Fintype.card A:ℝ)+d m.1 m.2)))≤1 :=
  sigma_weight_le A B _ d (log_card_weight A) hd
lemma sum_bit_weight (A : Type u) (B : Type v) [Fintype A] [Fintype B]
    (c : A→ℝ) (d : B→ℝ)
    (hc : (∑a,Real.exp (-c a))≤1) (hd : (∑b,Real.exp (-d b))≤1) :
    (∑m : A⊕B,Real.exp (-(Real.log 2+Sum.elim c d m)))≤1 := by
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr,neg_add,Real.exp_add,←Finset.mul_sum,
    Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2)]
  simp only [Real.exp_neg] at hc hd
  norm_num only [invOf_eq_inv, inv_mul_eq_div] at *
  linarith only [hc,hd]

end SharpRamseyFive.MessageWeights

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_AmbientPublicTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

lemma cap_inter (R : A→B→Prop) (U : Finset A) {n : ℕ} (q : ℝ) (row : Fin n→B) :
    U∩cap R Finset.univ q row=cap R U q row := by
  ext a
  simp [cap]

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FreshPublicFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
variable {A : Type*}
lemma acceptedIndex_decode {n : ℕ} (E : Finset A) (t : Fin n→A) :
    Option.map t (acceptedIndex E t)=firstAccepted E t :=
  Classical.choose_spec (exists_accepted_index E t)
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

lemma freshEncoded_decoded (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (n : ℕ) (q M : ℝ) (t : FreshTape W n q) :
    Option.map (freshDecoded R W n q t) (freshEncoded R S U C W hCW n q M t)=
      Option.map (cap R Finset.univ q)
        (firstAccepted (validationRows R S U C n q M)
          (t ⟨C.card,Nat.lt_succ_of_le (Finset.card_le_card hCW)⟩)) := by
  unfold freshEncoded freshDecoded
  rw [←acceptedIndex_decode]
  simp only [Option.map_map]
  rfl

end SharpRamseyFive.ReverseCap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_BaseSmallLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open Module
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma incidences_bidual (S : Finset (ℙ K V)) (T : Finset (ℙ K (Dual K V))) :
    incidences T (S.map bidualPoint.toEmbedding)=incidences S T := by
  have hh : (incidences T (S.map bidualPoint.toEmbedding):ℝ)=(incidences S T:ℝ) := by
    rw [incidences_eq_sum,incidences_eq_sum,Finset.sum_comm]
    simp only [Finset.sum_map,Equiv.toEmbedding_apply,incidenceEntry,incident_bidual]
  exact_mod_cast hh

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_TwoAmbientCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]


lemma incidence_density_le {d : ℕ} (hd : 1≤d) :
    (Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d≤1/(Nat.card K:ℝ) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hQ : (0:ℝ)<Q (Nat.card K) d := by exact_mod_cast Q_pos (Nat.card K) d
  apply (div_le_div_iff₀ hQ hq).mpr
  rw [one_mul,Q_recurrence hd]
  push_cast
  nlinarith

lemma reciprocal_rectangle_flags (hdim : finrank K V=5)
    (U : Finset (ℙ K V)) (W : Finset (ℙ K (Dual K V)))
    (C b : ℝ) (hC : 1≤C) (hb : 0≤b)
    (hprod : (U.card:ℝ)*W.card≤C*(Nat.card K:ℝ)^5*Real.exp b) :
    (incidences U W:ℝ)≤2*C*(Nat.card K:ℝ)^4*Real.exp b := by
  let q : ℝ := Nat.card K
  have hq : 0<q := by dsimp [q];exact_mod_cast Nat.card_pos (α:=K)
  have hmix := incidence_mixing (d:=4) hdim (by norm_num) U W
  norm_num only [Nat.reduceSub] at hmix
  have hden := incidence_density_le (K:=K) (d:=4) (by norm_num)
  norm_num only [Nat.reduceSub] at hden
  have hmean := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hden
    (show (0:ℝ)≤U.card by positivity)) (show (0:ℝ)≤W.card by positivity)
  have hmain : (1/q)*(U.card:ℝ)*W.card≤C*q^4*Real.exp b := by
    rw [show (1/q)*(U.card:ℝ)*W.card=((U.card:ℝ)*W.card)/q by ring]
    apply (div_le_iff₀ hq).mpr
    simpa only [show C*q^4*Real.exp b*q=C*q^5*Real.exp b by ring] using hprod
  have hcb : 1≤C*Real.exp b := by
    have he : 1≤Real.exp b := Real.one_le_exp_iff.mpr hb
    nlinarith
  have hcb2 : C*Real.exp b≤(C*Real.exp b)^2 := by nlinarith
  have hbase := mul_le_mul_of_nonneg_left hprod (pow_nonneg hq.le 3)
  have hupper := mul_le_mul_of_nonneg_left hcb2 (pow_nonneg hq.le 8)
  have hsquare : q^3*(U.card:ℝ)*W.card≤(C*q^4*Real.exp b)^2 := by
    dsimp [q] at hbase
    nlinarith only [hbase,hupper]
  have hsqrt : Real.sqrt (q^3*(U.card:ℝ)*W.card)≤C*q^4*Real.exp b :=
    (Real.sqrt_le_left (by positivity)).mpr hsquare
  have hm := le_abs_self ((incidences U W:ℝ)-
    (Q (Nat.card K) 3:ℝ)/Q (Nat.card K) 4*U.card*W.card)
  change |(incidences U W:ℝ)-
    (Q (Nat.card K) 3:ℝ)/Q (Nat.card K) 4*U.card*W.card|≤
      Real.sqrt (q^3*(U.card:ℝ)*W.card) at hmix
  change (Q (Nat.card K) 3:ℝ)/Q (Nat.card K) 4*U.card*W.card≤(1/q)*U.card*W.card at hmean
  linarith

lemma reciprocal_cap_product (Q a b x y C D loss : ℝ)
    (hQ : 0<Q) (ha : 0<a) (hb : 0<b) (_hx : 0≤x) (hy : 0≤y)
    (hC : 0≤C) (hD : 0≤D) (hp : Q*Real.exp (-loss)≤a*b)
    (hxc : x≤C*Q/b) (hyc : y≤D*Q/a) :
    x*y≤C*D*Q*Real.exp loss := by
  have hx' := (le_div_iff₀ hb).mp hxc
  have hy' := (le_div_iff₀ ha).mp hyc
  have hxy := mul_le_mul hx' hy' (mul_nonneg hy ha.le) (mul_nonneg hC hQ.le)
  have hp' : Q≤a*b*Real.exp loss := by
    have hh := mul_le_mul_of_nonneg_right hp (Real.exp_pos loss).le
    rw [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one] at hh
    exact hh
  have hh := mul_le_mul_of_nonneg_left hp' (mul_nonneg hC hD)
  have hh' := mul_le_mul_of_nonneg_right hh hQ.le
  have hab : 0<a*b := mul_pos ha hb
  apply (mul_le_mul_iff_left₀ hab).mp
  nlinarith only [hxy,hh']

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_AmbientPairPublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma ambientPair_prefixes (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (W : Finset (ℙ K V))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB : ℝ) (t : AmbientPairTape K V H q)
    (m : AmbientPairMessage UB W H q t)
    (hm : ambientPairEncoded A UA B UB W H nA nB q MA MB t=some m) :
    universalFreshEncoded (fun b a=>Incident a b) B UB (A∩W) W Finset.inter_subset_right H nB q MB t.1=some m.1 ∧
    let Y := universalFreshDecoded (fun b a=>Incident a b) W H q t.1 m.1
    ValidCap B UB MB (UB∩Y) ∧
    universalFreshEncoded Incident A UA (B∩(UB∩Y)) (UB∩Y) Finset.inter_subset_right H nA q MA t.2=some m.2 := by
  unfold ambientPairEncoded at hm
  cases hf : universalFreshEncoded (fun b a=>Incident a b) B UB (A∩W) W Finset.inter_subset_right H nB q MB t.1 with
  | none => simp [hf] at hm
  | some f =>
    rw [hf] at hm
    change (if _hv : ValidCap B UB MB _ then _ else none)=some m at hm
    split_ifs at hm with hv
    obtain ⟨g,hg,he⟩ := Option.map_eq_some_iff.mp hm
    subst m
    exact ⟨rfl,hv,hg⟩
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FourFinitePredictor
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeTapeFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma finiteNode_prefixes (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB c M : ℝ) (t : FiniteNodeTape pred H q)
    (m : FiniteNodeMessage pred UB H q t)
    (hm : finiteNodeEncoded pred A UA B UB H nA nB q MA MB c M t=some m) :
    pred.encoded A B t.1=some m.1 ∧ CaptureBound A UA c M (pred.decoded t.1 m.1) ∧
    ambientPairEncoded A UA B UB (pred.decoded t.1 m.1) H nA nB q MA MB t.2=some m.2 := by
  unfold finiteNodeEncoded at hm
  cases hf : pred.encoded A B t.1 with
  | none => simp [hf] at hm
  | some f =>
    rw [hf] at hm
    change (if _hc : CaptureBound A UA c M _ then _ else none)=some m at hm
    split_ifs at hm with hc
    obtain ⟨g,hg,he⟩ := Option.map_eq_some_iff.mp hm
    subst m
    exact ⟨rfl,hc,hg⟩
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_PrimitiveMessageWeights
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeTapeFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpRamseyFive.ReverseCap
open MessageWeights
open scoped Classical BigOperators
variable {B : Type} [Fintype B]
omit [Fintype B] in
lemma universalFresh_weight (W : Finset B) (H : ℕ) (q : ℝ) :
    (∑m : UniversalFreshMessage W H q,Real.exp (-universalFreshCost W H q m))≤1 := by
  have hh := sigma_header_weight (Fin (H+1)) (fun n : Fin (H+1)=>FreshMessage W n q)
    (fun n m=>Real.log (W.card+1:ℝ)+Real.log (Fintype.card (Fin (cardCutoff q m.1 W.card n)):ℝ))
    (fun n=>by
      simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] using
        sigma_header_weight (Fin (W.card+1)) (fun k : Fin (W.card+1)=>Fin (cardCutoff q k W.card n))
          (fun k _=>Real.log (Fintype.card (Fin (cardCutoff q k W.card n)):ℝ))
          (fun k=>log_card_weight _))
  simpa only [universalFreshCost,Fintype.card_fin,Nat.cast_add,Nat.cast_one,add_assoc] using hh
end SharpRamseyFive.ReverseCap
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence MessageWeights
open scoped Classical BigOperators LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
omit [Finite K] [FiniteDimensional K V] in
lemma baseFinite_weight (U : Finset (ℙ K V)) (P τ : ℝ) :
    (∑m : BaseMessage U P τ,Real.exp (-baseFiniteCost U P τ m))≤1 := by
  simpa only [baseFiniteCost,Fintype.card_fin,Nat.cast_add,Nat.cast_one] using
    sigma_header_weight (Fin (Fintype.card (ℙ K V)+1)) (fun n : Fin (Fintype.card (ℙ K V)+1)=>baseAlphabet U n P τ)
      (fun n _=>Real.log (Fintype.card (baseAlphabet U n P τ):ℝ)) (fun n=>log_card_weight _)
omit [Finite K] [FiniteDimensional K V] in
lemma scoreFinite_weight [Fintype V] (U : Finset (ℙ K V)) (σ P τ : ℝ) :
    (∑m : ScoredMessage U σ P τ,Real.exp (-scoreFiniteCost U σ P τ m))≤1 := by
  simpa only [scoreFiniteCost,Fintype.card_fin,Nat.cast_add,Nat.cast_one] using
    sigma_header_weight (Fin (Fintype.card (ℙ K V)+1)) (fun n : Fin (Fintype.card (ℙ K V)+1)=>ScoredPayload U n σ P τ)
      (fun n _=>Real.log (Fintype.card (ScoredPayload U n σ P τ):ℝ)) (fun n=>log_card_weight _)
end SharpRamseyFive.ScoreGeometry
namespace SharpRamseyFive.ProjectiveIncidence
open Module MessageWeights ReverseCap ScoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
omit [Finite K] [FiniteDimensional K V] in
lemma ambientPair_weight (UB : Finset (ℙ K (Dual K V))) (W : Finset (ℙ K V)) (H : ℕ) (q : ℝ)
    (t : AmbientPairTape K V H q) :
    (∑m : AmbientPairMessage UB W H q t,Real.exp (-ambientPairCost UB W H q t m))≤1 := by
  exact sigma_weight_le _ _ _ _ (universalFresh_weight W H q) (fun _=>universalFresh_weight _ H q)
end SharpRamseyFive.ProjectiveIncidence

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveRestriction MessageWeights ReverseCap
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal

lemma FinitePredictor.normalized_transform {A B C D : Type}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (p : FinitePredictor A B) (e : A↪C) (h : Finset C→Finset D→Finset A×Finset B)
    (hp : p.Normalized) : (p.transform e h).Normalized := hp

lemma FinitePredictor.normalized_family {A B I : Type}
    [Fintype A] [Fintype B] [Fintype I] (p : I→FinitePredictor A B)
    (s : Finset A→Finset B→I) (hp : ∀i,(p i).Normalized) :
    (FinitePredictor.family p s).Normalized := by
  intro t
  let (i : I) : Fintype ((p i).Message (t i)) := (p i).messageFintype (t i)
  exact sigma_header_weight I (fun i=>(p i).Message (t i))
    (fun i m=>(p i).cost (t i) m) (fun i=>hp i (t i))

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma reversedBase_weight (UT : Finset (ℙ K (Dual K V))) (P τ : ℝ) (H : ℕ) (q : ℝ)
    (t : ReversedBaseTape UT P τ H q) :
    (∑m : ReversedBaseMessage UT P τ H q t,Real.exp (-reversedBaseCost UT P τ H q t m))≤1 := by
  exact sigma_weight_le _ _ _ _ (baseFinite_weight UT P τ) (fun _=>universalFresh_weight _ H q)
omit [Finite K] [FiniteDimensional K V] in
lemma twoPublic_weight (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (H : ℕ) (q : ℝ) (t : TwoPublicTape U UT P τ H q) :
    (∑m : TwoPublicMessage U UT P τ H q t,Real.exp (-twoPublicCost U UT P τ H q t m))≤1 := by
  convert sum_bit_weight _ _ _ _ (baseFinite_weight U P τ) (reversedBase_weight UT P τ H q t.2) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext m
  cases m <;> rfl
omit [Finite K] in
lemma orientedFinite_weight
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (d H : ℕ) (q P c B : ℝ) (hf : f.Normalized) (hr : r.Normalized) :
    (orientedFinitePredictor f r U UT d H q P c B).Normalized := by
  intro t
  have hs := sigma_weight_le (r.Message t.2.1)
    (fun m=>UniversalFreshMessage (r.decoded t.2.1 m) H q)
    (r.cost t.2.1) (fun m u=>universalFreshCost (r.decoded t.2.1 m) H q u)
    (hr t.2.1) (fun _=>universalFresh_weight _ H q)
  convert sum_bit_weight _ _ _ _ (hf t.1) hs using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext m
  cases m <;> rfl
end SharpRamseyFive.ScoreGeometry
namespace SharpRamseyFive.ProjectiveRestriction
open Module ProjectiveIncidence ScoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)]
omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma planePublic_weight (A : Submodule K V) [Fintype (ℙ K A)]
    [Fintype (ℙ K (Dual K A))] [Fintype (ℙ K (Dual K (Dual K A)))]
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V))) (P τ : ℝ) (k : ℕ)
    (t : PlanePublicTape A U UT P τ k) :
    (∑m : PlanePublicMessage A U UT P τ k t,Real.exp (-planePublicCost A U UT P τ k t m))≤1 :=
  twoPublic_weight _ _ _ _ _ _ t
end SharpRamseyFive.ProjectiveRestriction
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveRestriction MessageWeights
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal
variable {K : Type} [Field K] [Finite K] [Fintype K]
  [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K A)]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K A))]
  [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K (Dual K A)))]
lemma threeLocal_weight (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ) (br : ThreePublicIndex K σ)
    (t : ThreeLocalTape U UT σ P τ br) :
    (∑m : ThreeLocalMessage U UT σ P τ br t,Real.exp (-threeLocalCost U UT σ P τ br t m))≤1 := by
  rcases br with b|b
  · exact baseFinite_weight U P τ
  · rcases b with b|b
    · exact scoreFinite_weight U σ P τ
    · exact planePublic_weight _ U UT P τ _ t
lemma threePublic_weight (U : Finset (ℙ K (Fin 4→K)))
    (UT : Finset (ℙ K (Dual K (Fin 4→K)))) (σ P τ : ℝ)
    (t : ThreePublicTape U UT σ P τ) :
    (∑m : ThreePublicMessage U UT σ P τ t,Real.exp (-threePublicCost U UT σ P τ t m))≤1 :=
  sigma_header_weight _ _ _ (fun br=>threeLocal_weight U UT σ P τ br (t br))
end SharpRamseyFive.ScoreGeometry
end

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveRestriction MessageWeights
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
lemma threeFinite_weight (hd : finrank K V=4) (σ : ℝ)
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    (threeFinitePredictor hd σ U UT P τ R L₀).Normalized := by
  let : Fintype K := Fintype.ofFinite _
  let : Finite (Dual K (Fin 4→K)) := Module.finite_of_finite K
  let : Fintype (ℙ K (Fin 4→K)) := Fintype.ofFinite _
  let : Fintype (ℙ K (Dual K (Fin 4→K))) := Fintype.ofFinite _
  let (A : Submodule K (Fin 4→K)) : Finite (Dual K A) := Module.finite_of_finite K
  let (A : Submodule K (Fin 4→K)) : Finite (Dual K (Dual K A)) := Module.finite_of_finite K
  let (A : Submodule K (Fin 4→K)) : Fintype (ℙ K A) := Fintype.ofFinite _
  let (A : Submodule K (Fin 4→K)) : Fintype (ℙ K (Dual K A)) := Fintype.ofFinite _
  let (A : Submodule K (Fin 4→K)) : Fintype (ℙ K (Dual K (Dual K A))) := Fintype.ofFinite _
  unfold threeFinitePredictor
  try dsimp only
  intro t
  exact threePublic_weight _ _ σ P τ t
lemma threeOrientedFinite_weight [Fintype (ℙ K (Dual K (Dual K V)))]
    (hd : finrank K V=4) (σ : ℝ)
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    (threeOrientedFinitePredictor hd σ U UT P τ R L₀).Normalized := by
  exact orientedFinite_weight _ _ _ _ _ _ _ _ _ _
    (threeFinite_weight _ _ _ _ _ _ _ _) (threeFinite_weight _ _ _ _ _ _ _ _)
end SharpRamseyFive.ScoreGeometry
namespace SharpRamseyFive.ProjectiveRestriction
open Module ProjectiveIncidence ScoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
lemma threeFlatFinite_weight (A : Submodule K V) (hA : finrank K A=4) (σ : ℝ)
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (τ P : ℝ) (R : ℕ) (L₀ : ℝ≥0) (k : ℕ) :
    (threeFlatFinitePredictor A hA σ U UT τ P R L₀ k).Normalized := by
  let : Finite A := Module.finite_of_finite K
  let : Finite (Dual K A) := Module.finite_of_finite K
  let : Finite (Dual K (Dual K A)) := Module.finite_of_finite K
  let : Fintype (ℙ K A) := Fintype.ofFinite _
  let : Fintype (ℙ K (Dual K A)) := Fintype.ofFinite _
  let : Fintype (ℙ K (Dual K (Dual K A))) := Fintype.ofFinite _
  unfold threeFlatFinitePredictor
  try dsimp only
  apply FinitePredictor.normalized_transform
  exact threeOrientedFinite_weight _ _ _ _ _ _ _ _
end SharpRamseyFive.ProjectiveRestriction
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveRestriction MessageWeights
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal
variable {K : Type} [Field K] [Finite K] [Fintype K]
  [Fintype (ℙ K (Fin 5→K))] [Fintype (ℙ K (Dual K (Fin 5→K)))]
  [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K A)]
  [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K (Dual K A))]
  [∀ A : Submodule K (Fin 5→K),Fintype (ℙ K (Dual K (Dual K A)))]
lemma fourLocal_weight (U : Finset (ℙ K (Fin 5→K)))
    (UT : Finset (ℙ K (Dual K (Fin 5→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (br : FourPublicIndex K σ) : (fourLocalPredictor U UT σ P τ R L₀ br).Normalized := by
  rcases br with b|b
  · intro t;exact baseFinite_weight U P τ
  · rcases b with b|b
    · intro t;exact scoreFinite_weight U σ P τ
    · rcases b with b|b
      · intro t;exact planePublic_weight _ U UT P τ _ t
      · exact threeFlatFinite_weight _ _ σ U UT τ P R L₀ _
lemma fourCertified_weight (U : Finset (ℙ K (Fin 5→K)))
    (UT : Finset (ℙ K (Dual K (Fin 5→K)))) (σ P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    (fourCertifiedPredictor U UT σ P τ R L₀).Normalized :=
  FinitePredictor.normalized_family _ _ (fourLocal_weight U UT σ P τ R L₀)
end SharpRamseyFive.ScoreGeometry
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveRestriction MessageWeights
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
lemma fourFinite_weight (hd : finrank K V=5) (σ : ℝ)
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) :
    (fourFinitePredictor hd σ U UT P τ R L₀).Normalized := by
  let : Fintype K := Fintype.ofFinite _
  let : Finite (Dual K (Fin 5→K)) := Module.finite_of_finite K
  let : Fintype (ℙ K (Fin 5→K)) := Fintype.ofFinite _
  let : Fintype (ℙ K (Dual K (Fin 5→K))) := Fintype.ofFinite _
  let (A : Submodule K (Fin 5→K)) : Finite (Dual K A) := Module.finite_of_finite K
  let (A : Submodule K (Fin 5→K)) : Finite (Dual K (Dual K A)) := Module.finite_of_finite K
  let (A : Submodule K (Fin 5→K)) : Fintype (ℙ K A) := Fintype.ofFinite _
  let (A : Submodule K (Fin 5→K)) : Fintype (ℙ K (Dual K A)) := Fintype.ofFinite _
  let (A : Submodule K (Fin 5→K)) : Fintype (ℙ K (Dual K (Dual K A))) := Fintype.ofFinite _
  unfold fourFinitePredictor
  try dsimp only
  apply FinitePredictor.normalized_transform
  exact fourCertified_weight _ _ σ P τ R L₀
end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_FiniteNodeSent
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeTapeFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]
lemma freshEncoded_valid (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (n : ℕ) (q M : ℝ) (t : FreshTape W n q)
    (m : FreshMessage W n q) (hm : freshEncoded R S U C W hCW n q M t=some m) :
    ValidCap S U M (U∩freshDecoded R W n q t m) := by
  have hh := freshEncoded_decoded R S U C W hCW n q M t
  rw [hm,Option.map_some] at hh
  obtain ⟨row,hr,he⟩ := Option.map_eq_some_iff.mp hh.symm
  have hi := (firstAccepted_index _ _ hr).choose_spec.2
  rw [←he,cap_inter]
  exact ⟨cap_subset _ _ _ _,(Finset.mem_filter.mp hi).2.2⟩

lemma universalFreshEncoded_valid (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (H : ℕ) (n : Fin (H+1)) (q M : ℝ)
    (t : UniversalFresh B H q) (m : UniversalFreshMessage W H q)
    (hm : universalFreshEncoded R S U C W hCW H n q M t=some m) :
    ValidCap S U M (U∩universalFreshDecoded R W H q t m) := by
  unfold universalFreshEncoded at hm
  split_ifs at hm with hW
  obtain ⟨f,hf,he⟩ := Option.map_eq_some_iff.mp hm
  subst m
  simp only [universalFreshDecoded,dite_eq_left hW]
  exact freshEncoded_valid R S U C W hCW n q M _ f hf
end SharpRamseyFive.ReverseCap

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma finiteNode_sent_valid (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (A UA : Finset (ℙ K V)) (B UB : Finset (ℙ K (Dual K V)))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB c M : ℝ)
    (t : FiniteNodeTape pred H q) (m : FiniteNodeMessage pred UB H q t)
    (hm : finiteNodeEncoded pred A UA B UB H nA nB q MA MB c M t=some m) :
    ValidCap B UB MB (UB∩(finiteNodeDecoded pred UB H q t m).1) ∧
    ValidCap A UA MA (UA∩(finiteNodeDecoded pred UB H q t m).2) := by
  have hp := (finiteNode_prefixes pred A UA B UB H nA nB q MA MB c M t m hm).2.2
  have hh := ambientPair_prefixes A UA B UB (pred.decoded t.1 m.1) H nA nB q MA MB t.2 m.2 hp
  exact ⟨hh.2.1,universalFreshEncoded_valid _ _ _ _ _ _ _ _ _ _ _ _ hh.2.2⟩
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_GuardedNodeSent
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

lemma guardedNode_sent_valid (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ M : ℝ) (hδ : 0<δ)
    (t : FiniteNodeTape pred (1000*(Nat.card K)^2) (Nat.card K))
    (m : FiniteNodeMessage pred UB (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : guardedNodeEncoded pred σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ M hδ t=some m) :
    OriginalNodeReady A₀ UA B₀ UB δ τ ∧
    ValidCap (B₀∩UB) UB ((320/c+320)*(Nat.card K:ℝ)^5/(A₀∩UA).card)
      (UB∩(finiteNodeDecoded pred UB (1000*(Nat.card K)^2) (Nat.card K) t m).1) ∧
    ValidCap (A₀∩UA) UA ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/(B₀∩UB).card)
      (UA∩(finiteNodeDecoded pred UB (1000*(Nat.card K)^2) (Nat.card K) t m).2) := by
  unfold guardedNodeEncoded at hm
  split_ifs at hm with hr
  exact ⟨hr,finiteNode_sent_valid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm⟩

lemma guardedNode_original_capture (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ M : ℝ) (hδ : 0<δ)
    (t : FiniteNodeTape pred (1000*(Nat.card K)^2) (Nat.card K))
    (m : FiniteNodeMessage pred UB (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : guardedNodeEncoded pred σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ M hδ t=some m) :
    (9/10:ℝ)*δ*A₀.card≤(A₀∩(UA∩(finiteNodeDecoded pred UB (1000*(Nat.card K)^2) (Nat.card K) t m).2)).card ∧
    (9/10:ℝ)*δ*B₀.card≤(B₀∩(UB∩(finiteNodeDecoded pred UB (1000*(Nat.card K)^2) (Nat.card K) t m).1)).card := by
  obtain ⟨hr,hB,hA⟩ := guardedNode_sent_valid pred σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ M hδ t m hm
  have ha := hA.2.2
  have hb := hB.2.2
  simp only [Finset.inter_assoc,Finset.inter_left_idem] at ha hb
  constructor
  · nlinarith [hr.1]
  · nlinarith [hr.2.1]
end

open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_TreeWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpRamseyFive.MessageWeights
open scoped BigOperators
universe u v
lemma prod_weight_le (A : Type u) (B : Type v) [Fintype A] [Fintype B]
    (c : A→ℝ) (d : B→ℝ)
    (hc : (∑a,Real.exp (-c a))≤1) (hd : (∑b,Real.exp (-d b))≤1) :
    (∑m : A×B,Real.exp (-(c m.1+d m.2)))≤1 := by
  rw [Fintype.sum_prod_type]
  apply le_trans _ hc
  apply Finset.sum_le_sum
  intro a _
  simp only [neg_add,Real.exp_add,←Finset.mul_sum]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hd (Real.exp_pos (-c a)).le
lemma option_bit_weight (A : Type u) [Fintype A] (c : A→ℝ)
    (hc : (∑a,Real.exp (-c a))≤1) :
    (∑m : Option A,Real.exp (-(Real.log 2+m.elim 0 c)))≤1 := by
  rw [Fintype.sum_option]
  simp only [Option.elim_none,Option.elim_some,add_zero,neg_add,Real.exp_add,
    ←Finset.mul_sum,Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2)]
  simp only [Real.exp_neg] at hc
  norm_num only [invOf_eq_inv, inv_mul_eq_div] at *
  linarith only [hc]
end SharpRamseyFive.MessageWeights
namespace SharpRamseyFive.TreeCodec
open BinaryTree MessageWeights
open scoped Classical BigOperators
universe u v w z
variable {A : Type u} {C : Type v} [Fintype C]
  (Ω : A→C→Type w) (M : ∀a c,Ω a c→Type z)
  (left right : ∀a c t,M a c t→C)

omit [Fintype C] in
lemma slotCost_weight [∀a c t,Fintype (M a c t)]
    (lc : ∀a c t,M a c t→ℝ)
    (hw : ∀a c t,(∑m : M a c t,Real.exp (-lc a c t m))≤1)
    (b : BinaryTree A) (ω : Tape Ω b) (c : C) :
    (∑m : Message Ω M left right b ω c,Real.exp (-slotCost Ω M left right lc b ω c m))≤1 := by
  induction b generalizing c with
  | nil =>
    change (∑_m : PUnit, Real.exp (-(0:ℝ)))≤1
    simp
  | node a l r hl hr =>
    change (∑m : Option ((m : M a c (ω.1 c)) ×
      Message Ω M left right l ω.2.1 (left a c (ω.1 c) m) ×
      Message Ω M left right r ω.2.2 (right a c (ω.1 c) m)),
      Real.exp (-slotCost Ω M left right lc (.node a l r) ω c m))≤1
    have hh := sigma_weight_le (M a c (ω.1 c))
      (fun m=>Message Ω M left right l ω.2.1 (left a c (ω.1 c) m) ×
        Message Ω M left right r ω.2.2 (right a c (ω.1 c) m))
      (lc a c (ω.1 c))
      (fun m x=>slotCost Ω M left right lc l ω.2.1 (left a c (ω.1 c) m) x.1+
        slotCost Ω M left right lc r ω.2.2 (right a c (ω.1 c) m) x.2)
      (hw a c (ω.1 c)) (fun m=>prod_weight_le _ _ _ _ (hl ω.2.1 _) (hr ω.2.2 _))
    have hh' := option_bit_weight _ _ hh
    convert hh' using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext m
    cases m with
    | none => simp [slotCost]
    | some m => simp [slotCost,add_assoc]

end SharpRamseyFive.TreeCodec
end

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry MessageWeights BinaryTree
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
omit [Finite K] [FiniteDimensional K V] in
lemma finiteNode_weight (p : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (UB : Finset (ℙ K (Dual K V))) (H : ℕ) (q : ℝ) (hp : p.Normalized)
    (t : FiniteNodeTape p H q) :
    (∑m : FiniteNodeMessage p UB H q t,Real.exp (-finiteNodeCost p UB H q t m))≤1 := by
  exact sigma_weight_le _ _ _ _ (hp t.1) (fun m=>ambientPair_weight UB (p.decoded t.1 m) H q t.2)
variable [Fintype (ℙ K (Dual K (Dual K V)))]
omit [Finite K] in
lemma orientedNode_weight
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (UA : Finset (ℙ K V)) (UB : Finset (ℙ K (Dual K V))) (H : ℕ) (q : ℝ)
    (hf : f.Normalized) (hr : r.Normalized) (t : OrientedNodeTape f r H q) :
    (∑m : OrientedNodeMessage f r UA UB H q t,Real.exp (-orientedNodeCost f r UA UB H q t m))≤1 := by
  convert sum_bit_weight _ _ _ _ (finiteNode_weight f UB H q hf t.1)
    (finiteNode_weight r (UA.map bidualPoint.toEmbedding) H q hr t.2) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext m
  cases m <;> rfl
variable {ι : Type}
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
omit [Finite K] in
lemma orientedPivotTree_weight (hf : ∀C,(f C).Normalized) (hr : ∀C,(r C).Normalized)
    (b : BinaryTree ι) (ω : OrientedPivotTreeTape f r b) (C : PivotContext K V) :
    (∑m : OrientedPivotTreeMessage f r b ω C,Real.exp (-orientedPivotSlotCost f r b ω C m))≤1 := by
  let : ∀(_ : ι) C t,Fintype (OrientedPivotMessage f r C t) := fun _ _ _=>inferInstance
  exact TreeCodec.slotCost_weight _ _ _ _ _
    (fun _ C t=>orientedNode_weight (f C) (r C) C.1 C.2 _ _ (hf C) (hr C) t) b ω C

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MessageCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.MessageWeights
open FiniteEntropy
open scoped Classical BigOperators
universe u
variable {A : Type u} [Fintype A]

lemma entropy_le_cost (p : Law A) (c : A→ℝ) (hc : (∑a,Real.exp (-c a))≤1) :
    entropy p≤∑a,p a*c a := by
  have hh := entropy_le_cross_subprob p (fun a=>Real.exp (-c a))
    (fun _=>Real.exp_pos _) hc
  simpa only [Real.log_exp,mul_neg,Finset.sum_neg_distrib,neg_neg] using hh
lemma entropy_le_bound (p : Law A) (c : A→ℝ) (hc : (∑a,Real.exp (-c a))≤1)
    (B : ℝ) (hB : ∀a,0<p a→c a≤B) : entropy p≤B := by
  apply (entropy_le_cost p c hc).trans
  calc
    _ ≤ ∑a,p a*B := Finset.sum_le_sum (fun a _=>by
      by_cases hp : p a=0
      · simp [hp]
      · exact mul_le_mul_of_nonneg_left (hB a (lt_of_le_of_ne (p.nonneg _) (Ne.symm hp))) (p.nonneg a))
    _ = B := by rw [←Finset.sum_mul,p.sum_one,one_mul]
end SharpRamseyFive.MessageWeights

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

end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_CountedExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

open scoped Classical BigOperators
open MessageWeights SelectedTuple
noncomputable section
variable {α β κ Ω Θ : Type*} [Fintype α] [Fintype β] [Fintype κ] [Fintype Ω] [Fintype Θ]

local instance fixedFinDecEq_r324473_1 (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
lemma independent_event_average (p : Law Ω) (tables : Law Θ) (E : Θ→Finset Ω) :
    eventMass (adaptiveLaw p (fun _=>tables))
      (Finset.univ.filter fun z=>z.1∈E z.2)=mean tables (fun t=>eventMass p (E t)) := by
  simp only [eventMass,Finset.sum_filter,adaptiveLaw,Fintype.sum_prod_type,mean]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [←Finset.sum_filter,Finset.mul_sum]
  simp only [Finset.filter_univ_mem]
  apply Finset.sum_congr rfl
  intro a _
  ring

end

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ContextDescription
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
open SelectedTuple MessageWeights

noncomputable section
variable {Ω β Θ α : Type*} [Fintype Ω] [Fintype β] [Fintype Θ] [Fintype α]

attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.dependentTableFinDecEq
theorem fixed_table_stage_dependent {N n l w : ℕ} {admissible : (Fin N→α)→Prop}
    (hl : l<n) (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible)
    (tables : Law Θ) (κ : Θ→Type*) [∀ t,Fintype (κ t)]
    (positions : Θ→Ω→Finset (Fin n))
    (ctx : (t : Θ)→Ω→κ t) (D : (t : Θ)→κ t→Fin w→Finset β)
    (slot : Ω→Fin n→Fin w) (hslot : ∀ a,Monotone (slot a))
    (cost : (t : Θ)→κ t→ℝ) (L M : ℝ)
    (hweight : ∀ t,(∑ m,Real.exp (-cost t m))≤1)
    (hcost : ∀ t a,0<S.law a→cost t (ctx t a)≤L)
    (hcap : ∀ t a,0<S.law a→∀ j,Real.log (D t (ctx t a) j).card≤M)
    (hdom : ∀ t a,0<S.law a→∀ i∈positions t a,S.tuple a i∈D t (ctx t a) (slot a i))
    (hloss : mean (adaptiveLaw S.law (fun _=>tables))
      (fun z=>((positions z.2 z.1)ᶜ.card:ℝ))≤((n:ℝ)-l)/10) :
    ∃ (t : Θ) (hE : 0<eventMass S.law (Finset.univ.filter fun a=>l≤(positions t a).card)),
      (9:ℝ)/10≤eventMass S.law (Finset.univ.filter fun a=>l≤(positions t a).card) ∧
      let S':=(S.restrict _ hE).extract hl.le (positions t)
      S'.density≤(10/9)*S.density ∧
      Nonempty (ContextDescription (κ:=κ t×RunAssignment l w) S'.law S'.tuple
        (L+w*Real.log (l+1)) M) := by
  let E:=fun t=>Finset.univ.filter (fun a=>l≤(positions t a).card)
  have he:=extraction_probability (adaptiveLaw S.law (fun _=>tables))
    (fun z=>positions z.2 z.1) hl (by simpa only [Finset.card_compl] using hloss)
  have heq : (Finset.univ.filter fun z : Ω×Θ=>l≤(positions z.2 z.1).card)=
      (Finset.univ.filter fun z : Ω×Θ=>z.1∈E z.2) := by
    ext z
    simp only [E,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [heq,independent_event_average] at he
  obtain ⟨t,_,ht⟩:=fix_independent_table S.law tables E (9/10) he
  have hE : 0<eventMass S.law (E t) := lt_of_lt_of_le (by norm_num) ht
  refine ⟨t,hE,ht,?_,⟨?_⟩⟩
  · change S.density/eventMass S.law (E t)≤(10/9)*S.density
    have h:=div_le_div_of_nonneg_left S.density_nonneg (by norm_num : (0:ℝ)<9/10) ht
    calc
      _ ≤ S.density/(9/10) := h
      _ = _ := by ring
  · apply countedDescription hl.le S.law S.tuple (positions t) (ctx t) (D t) slot hslot
      (hdom t) hE L M _ (hcap t)
    apply entropy_le_bound _ (cost t) (hweight t)
    intro m hm
    obtain ⟨a,ha,rfl⟩:=map_positive (conditionOn S.law _ hE) (ctx t) m hm
    exact hcost t a (conditionOn_positive S.law _ hE a ha).2
end
end SharpRamseyFive.FiniteEntropy

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
local instance historyProducerSubtypeDecEq_r324473_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
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
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_History
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {B A T β κ : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]
  [Fintype κ] [Nonempty A]
attribute [local instance] OAI.SharpRamseyFive.FiniteEntropy.historySupportIndexDecEq
lemma marginal_support_subset {I γ : Type*} [Fintype I] [Fintype γ]
    (p : Law (I→γ)) (D : I→Finset γ) (hp : InDomains p D) (i : I) :
    support (map p (fun x=>x i))⊆D i := by
  intro b hb
  obtain ⟨x,hx,rfl⟩:=map_positive p (fun x=>x i) b ((mem_support _ _).mp hb)
  exact hp x hx i
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MarkedActualBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {Ω κ α β I : Type} [Fintype Ω] [Fintype κ] [Fintype α] [Fintype β] [Fintype I]

lemma pair_fiber_pred (p : Law Ω) (ctx : Ω→κ) (x : Ω→α) (P : α→Prop)
    (hP : ∀z,0<p z→P (x z)) (c : κ) (hc : 0<first (pair p ctx x) c) :
    ∀y,0<fiber (pair p ctx x) c y→P y := by
  intro y hy
  obtain ⟨z,hz,he,rfl⟩:=fiber_pair_source p ctx x c y hc hy
  exact hP z hz

end
end SharpRamseyFive.FiniteEntropy

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

lemma originalHistory_private_mean (P : Law Ω) (context : Ω→κ) (tuple : Ω→((B×A)⊕T)→β)
    (S : κ→B→Finset A) (n : ℕ)
    (Γ : ((κ×BlockHistory B A T β n)×(B→A))→Type) [∀h,Fintype (Γ h)]
    (privateLaw : ∀h,Law (Γ h)) (tables : Law Θ)
    (F : (h : (κ×BlockHistory B A T β n)×(B→A))→(((B×A)⊕T)→β)→Γ h→Θ→ℝ) :
    let H := fun z : Ω×(BlockHistory B A T β n×(B→A))=>((context z.1,z.2.1),z.2.2)
    mean (adaptiveLaw (sigmaLaw (originalHistoryLaw P context tuple S n)
      (fun z=>privateLaw (H z))) (fun _=>tables))
      (fun z=>F (H z.1.1) (tuple z.1.1.1) z.1.2 z.2)=
    mean (preRoundLaw (first (pair P context tuple)) (fiber (pair P context tuple)) S n)
      (fun h=>mean (historyPosterior (fiber (pair P context tuple) h.1.1) h.1.2)
        (fun x=>mean (privateLaw h) (fun v=>mean tables (F h x v)))) := by
  dsimp only
  rw [mean_adaptive,mean_sigma]
  convert originalHistory_mean P context tuple S n
    (fun h x=>mean (privateLaw h) (fun v=>mean tables (F h x v))) using 1
  all_goals try with_reducible_and_instances rfl
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ReadyRefinement
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap ScoreGeometry Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization Topology
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma ready_trimmed_product (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (τ b : ℝ) (hr : OriginalNodeReady A₀ UA B₀ UB (9/10) τ)
    (hp : (Nat.card K:ℝ)^5*Real.exp (-b)≤(A₀.card:ℝ)*B₀.card) :
    (Nat.card K:ℝ)^5*Real.exp (-(b+1))≤((A₀∩UA).card:ℝ)*(B₀∩UB).card := by
  have hmul := mul_le_mul hr.1 hr.2.1
    (show (0:ℝ)≤(9/10:ℝ)*B₀.card by positivity) (Nat.cast_nonneg (A₀∩UA).card)
  have he : Real.exp (-1)≤(81:ℝ)/100 := by
    rw [Real.exp_neg]
    rw [←one_div]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    have h := Real.add_one_le_exp (1:ℝ)
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left he
    (show (0:ℝ)≤(Nat.card K:ℝ)^5*Real.exp (-b) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤81/100)
  rw [neg_add,Real.exp_add]
  nlinarith only [hmul,h1,h2]

omit [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma ready_bidual (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V))) (δ τ : ℝ) :
    OriginalNodeReady B₀ UB (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) δ τ ↔
      OriginalNodeReady A₀ UA B₀ UB δ τ := by
  simp only [OriginalNodeReady,←Finset.map_inter,Finset.card_map,incidences_bidual]
  constructor <;> rintro ⟨h1,h2,h3⟩ <;> refine ⟨h2,h1,?_⟩ <;> nlinarith only [h3]

end

open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

omit [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
    [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma bidual_inter_card (A UA : Finset (ℙ K V)) (Y : Finset (ℙ K (Dual K (Dual K V)))) :
    (A.map bidualPoint.toEmbedding∩(UA.map bidualPoint.toEmbedding∩Y)).card=
      (A∩(UA∩Y.map bidualPoint.symm.toEmbedding)).card := by
  have he : A.map bidualPoint.toEmbedding∩(UA.map bidualPoint.toEmbedding∩Y)=
      (A∩(UA∩Y.map bidualPoint.symm.toEmbedding)).map bidualPoint.toEmbedding := by
    ext x
    simp
  rw [he,Finset.card_map]

theorem orientedGuardedNode_original_capture
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ P : ℝ) (hδ : 0<δ)
    (t : OrientedNodeTape f r (1000*(Nat.card K)^2) (Nat.card K))
    (m : OrientedNodeMessage f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : orientedGuardedNodeEncoded f r σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ P hδ t=some m) :
    OriginalNodeReady A₀ UA B₀ UB δ τ ∧
    (9/10:ℝ)*δ*A₀.card≤
      (A₀∩(UA∩(orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m).2)).card ∧
    (9/10:ℝ)*δ*B₀.card≤
      (B₀∩(UB∩(orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m).1)).card := by
  unfold orientedGuardedNodeEncoded at hm
  split_ifs at hm with hAB
  · obtain ⟨m',hm',rfl⟩ := Option.map_eq_some_iff.mp hm
    have hv := (guardedNode_sent_valid f σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ
      (((A₀∩UA).card:ℝ)*Real.exp (10*P)) hδ t.1 m' hm').1
    exact ⟨hv,guardedNode_original_capture f σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ
      (((A₀∩UA).card:ℝ)*Real.exp (10*P)) hδ t.1 m' hm'⟩
  · obtain ⟨m',hm',rfl⟩ := Option.map_eq_some_iff.mp hm
    have hv := (guardedNode_sent_valid r σ hσ hq (by simpa using hd) B₀ UB
      (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) hB₀ hA₀.map c δ τ
      (((B₀∩UB).card:ℝ)*Real.exp (10*P)) hδ t.2 m' hm').1
    have hh := guardedNode_original_capture r σ hσ hq (by simpa using hd) B₀ UB
      (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) hB₀ hA₀.map c δ τ
      (((B₀∩UB).card:ℝ)*Real.exp (10*P)) hδ t.2 m' hm'
    refine ⟨(ready_bidual A₀ UA B₀ UB δ τ).mp hv,?_,hh.1⟩
    simpa only [Finset.card_map,bidual_inter_card,orientedNodeDecoded,reverseNodePair] using hh.2

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OrientedNodeCaps
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry PivotTree
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

omit [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma bidual_cap_card (UA : Finset (ℙ K V)) (Y : Finset (ℙ K (Dual K (Dual K V)))) :
    (UA.map bidualPoint.toEmbedding∩Y).card=(UA∩Y.map bidualPoint.symm.toEmbedding).card := by
  simpa only [Finset.inter_assoc,Finset.inter_left_idem] using bidual_inter_card UA UA Y

theorem orientedGuardedNode_caps
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ P : ℝ) (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ)
    (t : OrientedNodeTape f r (1000*(Nat.card K)^2) (Nat.card K))
    (m : OrientedNodeMessage f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : orientedGuardedNodeEncoded f r σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ P hδ t=some m) :
    ((UA∩(orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m).2).card:ℝ)≤
      (320/c+320)*((Nat.card K:ℝ)^5)/(B₀∩UB).card ∧
    ((UB∩(orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m).1).card:ℝ)≤
      (320/c+320)*((Nat.card K:ℝ)^5)/(A₀∩UA).card := by
  have hC : (320/((9:ℝ)/10)+320)≤320/c+320 := by
    have hh : (320:ℝ)/((9:ℝ)/10)≤320/c := div_le_div_of_nonneg_left (by norm_num) hc hc9
    linarith only [hh]
  have hM (n : ℕ) : (320/((9:ℝ)/10)+320)*((Nat.card K:ℝ)^5)/n≤
      (320/c+320)*((Nat.card K:ℝ)^5)/n :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) (Nat.cast_nonneg n)
  unfold orientedGuardedNodeEncoded at hm
  split_ifs at hm with hAB
  · obtain ⟨m',hm',rfl⟩ := Option.map_eq_some_iff.mp hm
    obtain ⟨_,hB,hA⟩ := guardedNode_sent_valid f σ hσ hq hd A₀ UA B₀ UB hA₀ hB₀ c δ τ
      (((A₀∩UA).card:ℝ)*Real.exp (10*P)) hδ t.1 m' hm'
    exact ⟨hA.2.1.trans (hM _),hB.2.1⟩
  · obtain ⟨m',hm',rfl⟩ := Option.map_eq_some_iff.mp hm
    obtain ⟨_,hA,hB⟩ := guardedNode_sent_valid r σ hσ hq (by simpa using hd) B₀ UB
      (A₀.map bidualPoint.toEmbedding) (UA.map bidualPoint.toEmbedding) hB₀ hA₀.map c δ τ
      (((B₀∩UB).card:ℝ)*Real.exp (10*P)) hδ t.2 m' hm'
    constructor
    · simpa only [orientedNodeDecoded,reverseNodePair,bidual_cap_card] using hA.2.1
    · have hh := hB.2.1
      simp only [←Finset.map_inter,Finset.card_map] at hh
      exact hh.trans (hM _)

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OrientedNodeProcess
attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

theorem orientedGuardedNode_flags
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c τ P b : ℝ)
    (hc : 0 < c) (hc9 : c≤9/10) (hb : 0≤b)
    (hp : (Nat.card K:ℝ)^5*Real.exp (-b)≤(A₀.card:ℝ)*B₀.card)
    (t : OrientedNodeTape f r (1000*(Nat.card K)^2) (Nat.card K))
    (m : OrientedNodeMessage f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : orientedGuardedNodeEncoded f r σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀ c (9/10) τ P
      (by norm_num) t=some m) :
    (incidences
      (UA∩(orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m).2)
      (UB∩(orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t m).1):ℝ)≤
      2*((320/c+320)^2)*(Nat.card K:ℝ)^4*Real.exp (b+1) := by
  have hready := (orientedGuardedNode_original_capture f r σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀
    c (9/10) τ P (by norm_num) t m hm).1
  obtain ⟨hAcap,hBcap⟩ := orientedGuardedNode_caps f r σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀
    c (9/10) τ P hc hc9 (by norm_num) t m hm
  have hnA := nonempty_of_positive_trim _ _ hA₀ (9/10) (by norm_num) hready.1
  have hnB := nonempty_of_positive_trim _ _ hB₀ (9/10) (by norm_num) hready.2.1
  have hC : 1≤320/c+320 := by
    have hh : 0≤320/c := by positivity
    linarith only [hh]
  have hC2 : 1≤(320/c+320)^2 := by nlinarith only [hC]
  apply reciprocal_rectangle_flags hd _ _ _ (b+1) hC2 (by linarith only [hb])
  have hQ : (0:ℝ)<(Nat.card K:ℝ)^5 := by rw [←hq]; positivity
  have hh := reciprocal_cap_product ((Nat.card K:ℝ)^5) (A₀∩UA).card (B₀∩UB).card _ _
    (320/c+320) (320/c+320) (b+1) hQ
    (by exact_mod_cast hnA.card_pos) (by exact_mod_cast hnB.card_pos)
    (by positivity) (by positivity) (by linarith only [hC]) (by linarith only [hC])
    (ready_trimmed_product A₀ UA B₀ UB τ b hready hp) hAcap hBcap
  simpa only [pow_two] using hh

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_TreeDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.TreeCodec
open FiniteEntropy BinaryTree
open scoped Classical
universe u v w z s
variable {A : Type u} {C : Type v} [Fintype C]
  (Ω : A→C→Type w) [∀ a c,Fintype (Ω a c)]
  (M : ∀ a c,Ω a c→Type z) (left right : ∀ a c t,M a c t→C)
  {D : Type s}

omit [Fintype C] [∀ a c, Fintype (Ω a c)] in
theorem decodedAt_encoded (enc : ∀ a c t,Option (M a c t))
    (out : ∀ a c t,M a c t→D) (b : BinaryTree A) (ω : Tape Ω b) (c : C)
    (j : Address b) :
    decodedAt Ω M left right out b ω c (encoded Ω M left right enc b ω c) j =
      observe Ω M left right enc out b ω c j := by
  induction b generalizing c with
  | nil => exact nomatch j
  | node a l r ihl ihr =>
    rcases j with j | (j | j)
    · cases he:enc a c (ω.1 c) <;> simp [decodedAt,encoded,observe,probe,he]
    · cases he:enc a c (ω.1 c) <;> simp [decodedAt,encoded,observe,probe,he,ihl]
    · cases he:enc a c (ω.1 c) <;> simp [decodedAt,encoded,observe,probe,he,ihr]

omit [Fintype C] [∀ a c, Fintype (Ω a c)] in
theorem observe_invariant (enc : ∀ a c t,Option (M a c t))
    (out : ∀ a c t,M a c t→D) (Valid : C→Prop) (P : A→D→Prop)
    (hl : ∀ a c t m,Valid c→enc a c t=some m→Valid (left a c t m))
    (hr : ∀ a c t m,Valid c→enc a c t=some m→Valid (right a c t m))
    (ho : ∀ a c t m,Valid c→enc a c t=some m→P a (out a c t m))
    (b : BinaryTree A) (ω : Tape Ω b) (c : C) (hc : Valid c)
    (j : Address b) (d : D) (h : observe Ω M left right enc out b ω c j=some d) :
    P (label b j) d := by
  induction b generalizing c with
  | nil => exact nomatch j
  | node a l r ihl ihr =>
    cases he:enc a c (ω.1 c) with
    | none =>
      rcases j with j | (j | j) <;> simp [observe,probe,he] at h
    | some m =>
      rcases j with j | (j | j)
      · simp only [observe,probe,he,Option.map_some,Option.some.injEq] at h
        subst d
        exact ho a c (ω.1 c) m hc he
      · exact ihl _ (left a c (ω.1 c) m) (hl a c (ω.1 c) m hc he) j
          (by simpa [observe,probe,he] using h)
      · exact ihr _ (right a c (ω.1 c) m) (hr a c (ω.1 c) m hc he) j
          (by simpa [observe,probe,he] using h)
end SharpRamseyFive.TreeCodec

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_OrientedTreeDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec
open scoped Classical LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
variable {I : Type}

theorem orientedPublicDomain_card
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5)
    (A₀ : I→Finset (ℙ K V)) (B₀ : I→Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i,(A₀ i).Nonempty) (hB₀ : ∀ i,(B₀ i).Nonempty)
    (c τ P b : ℝ) (hc : 0 < c) (hc9 : c≤9/10) (hb : 0≤b)
    (hp : ∀ i,(Nat.card K:ℝ)^5*Real.exp (-b)≤(A₀ i).card*(B₀ i).card)
    (tree : BinaryTree I) (ω : OrientedPivotTreeTape f r tree) (C : PivotContext K V)
    (j : Address tree) :
    ((orientedPublicDomain f r tree ω C
      (orientedPivotTreeEncoded f r σ hσ hq hd.le A₀ B₀ hA₀ hB₀ c (9/10) τ P
        (by norm_num) tree ω C) j).card:ℝ)≤
      2*((320/c+320)^2)*(Nat.card K:ℝ)^4*Real.exp (b+1) := by
  let enc:=fun i C t=>orientedGuardedNodeEncoded (f C) (r C) σ hσ hq hd.le
      (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c (9/10) τ P (by norm_num) t
  let obs:=observe (fun _ : I=>OrientedPivotTape f r) (fun _ : I=>OrientedPivotMessage f r)
    (fun _=>orientedPivotLeft f r) (fun _=>orientedPivotRight f r) enc
    (fun _=>orientedNodeDomain f r) tree ω C j
  have he : orientedPublicDomain f r tree ω C
      (orientedPivotTreeEncoded f r σ hσ hq hd.le A₀ B₀ hA₀ hB₀ c (9/10) τ P
        (by norm_num) tree ω C) j=obs.getD ∅ := by
    exact congrArg (fun d=>d.getD ∅) (decodedAt_encoded _ _ _ _ enc
      (fun _=>orientedNodeDomain f r) tree ω C j)
  rw [he]
  cases ho:obs with
  | none => simp only [Option.getD_none,Finset.card_empty,Nat.cast_zero]; positivity
  | some d =>
    simp only [Option.getD_some]
    exact observe_invariant _ _ _ _ enc (fun _=>orientedNodeDomain f r)
      (fun _=>True) (fun _ d=>(d.card:ℝ)≤2*((320/c+320)^2)*(Nat.card K:ℝ)^4*Real.exp (b+1))
      (fun _ _ _ _ _ _=>True.intro) (fun _ _ _ _ _ _=>True.intro)
      (fun i C t m _ hm=>orientedGuardedNode_flags (f C) (r C) σ hσ hq hd
        (A₀ i) C.1 (B₀ i) C.2 (hA₀ i) (hB₀ i) c τ P b hc hc9 hb (hp i) t m hm)
      tree ω C True.intro j d ho

end
end

open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree MessageWeights
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V → FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V → FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))

omit [Finite K] in
lemma variableTree_weight {w : ℕ} (t : VariableTreeTape f r w) (C : PivotContext K V)
    (hf : ∀ C,(f C).Normalized) (hr : ∀ C,(r C).Normalized) :
    (∑ a : VariableTreeMessage f r t C,Real.exp (-variableTreeCost f r t C a)) ≤ 1 := by
  simpa only [variableTreeCost,Fintype.card_fin,Nat.cast_add,Nat.cast_one] using
    sigma_header_weight (Fin (w+1))
      (fun m=>OrientedPivotTreeMessage f r (finiteBalanced m.val) (t m) C)
      (fun m=>orientedPivotSlotCost f r (finiteBalanced m.val) (t m) C)
      (fun _=>orientedPivotTree_weight f r hf hr _ _ _)

lemma variableTreeDomain_card {w : ℕ} (t : VariableTreeTape f r w) (C : PivotContext K V)
    (m : Fin (w+1)) (σ : ℝ) (hσ : 1 ≤ σ) (hq : Real.exp σ=Nat.card K)
    (hd : finrank K V=5)
    (A₀ : Fin (m.val+1)→Finset (ℙ K V)) (B₀ : Fin (m.val+1)→Finset (ℙ K (Dual K V)))
    (hA₀ : ∀ i,(A₀ i).Nonempty) (hB₀ : ∀ i,(B₀ i).Nonempty)
    (c τ P b : ℝ) (hc : 0 < c) (hc9 : c ≤ 9/10) (hb : 0 ≤ b)
    (hp : ∀ i,(Nat.card K:ℝ)^5*Real.exp (-b) ≤ (A₀ i).card*(B₀ i).card)
    (j : Fin (w+1)) :
    ((variableTreeDomain f r t C
      (variableTreeEncoded f r t C m σ hσ hq hd.le A₀ B₀ hA₀ hB₀ c (9/10) τ P (by norm_num)) j).card:ℝ) ≤
      2*((320/c+320)^2)*(Nat.card K:ℝ)^4*Real.exp (b+1) := by
  unfold variableTreeDomain variableTreeEncoded
  dsimp only
  split_ifs with h
  · exact orientedPublicDomain_card f r σ hσ hq hd A₀ B₀ hA₀ hB₀ c τ P b hc hc9 hb hp
      _ _ C _
  · simp only [Finset.card_empty,Nat.cast_zero]
    positivity

end

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_EmptyVariableTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
omit [Finite K] in
lemma variableTreeEmpty_domain {w : ℕ} (t : VariableTreeTape f r w) (C : PivotContext K V)
    (j : Fin (w+1)) : variableTreeDomain f r t C (variableTreeEmpty f r t C) j=∅ := by
  simp [variableTreeDomain,variableTreeEmpty]
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_SurvivorRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.PivotTree
open scoped Classical
noncomputable section
variable {w : ℕ}

lemma survivorRank_monotone (E : Finset (Fin w)) : Monotone (survivorRank E) := by
  intro i j hij
  apply Finset.card_le_card
  intro u hu
  simp only [Finset.mem_filter] at hu ⊢
  exact ⟨hu.1,lt_of_lt_of_le hu.2 hij⟩

end
end SharpRamseyFive.PivotTree

namespace SharpRamseyFive.Windows
open PivotTree
open scoped Classical
noncomputable section
lemma middleFirst_monotone (w n : ℕ) :
    Monotone (fun i : Fin (w*(2*n))=>(finProdFinEquiv.symm i : Fin w×Fin (2*n)).1) := by
  intro i j hij
  let a := (finProdFinEquiv.symm i : Fin w×Fin (2*n))
  let b := (finProdFinEquiv.symm j : Fin w×Fin (2*n))
  have hi : i.val=a.1.val*(2*n)+a.2.val := by
    calc
      _ = (finProdFinEquiv a).val := congrArg Fin.val (finProdFinEquiv.apply_symm_apply i).symm
      _ = _ := by change a.2.val+(2*n)*a.1.val=_;ring
  have hj : j.val=b.1.val*(2*n)+b.2.val := by
    calc
      _ = (finProdFinEquiv b).val := congrArg Fin.val (finProdFinEquiv.apply_symm_apply j).symm
      _ = _ := by change b.2.val+(2*n)*b.1.val=_;ring
  have h : a.1.val≤b.1.val := by
    by_contra hn
    have hg : (b.1.val+1)*(2*n)≤a.1.val*(2*n) := Nat.mul_le_mul_right (2*n) (by omega)
    have hb:=b.2.isLt
    have hij' : a.1.val*(2*n)+a.2.val≤b.1.val*(2*n)+b.2.val := by
      simpa only [Fin.le_def,hi,hj] using hij
    nlinarith
  exact h

lemma middleRank_monotone {w n : ℕ} (E : Finset (Fin w)) :
    Monotone (fun i : Fin (w*(2*n))=>survivorRank E
      (finProdFinEquiv.symm i : Fin w×Fin (2*n)).1) :=
  (survivorRank_monotone E).comp (middleFirst_monotone w n)
end
end SharpRamseyFive.Windows

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalLevelProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
omit [Finite K] [FiniteDimensional K V] in
lemma ReciprocalLevels.first_size {p : Law (FlagPair K V)} {u s : ℝ}
    (L : ReciprocalLevels p u s) (A : Finset (ℙ K V)) (hA : 0<L.firstLaw A) :
    Real.exp (5*Real.log (Nat.card K)-u-s)/2≤(A.card:ℝ) := by
  have h:=(L.first_good A hA).2.2.1
  have he : Real.exp (5*Real.log (Nat.card K)-u)*Real.exp (-s)=
      Real.exp (5*Real.log (Nat.card K)-u-s) := by rw [←Real.exp_add]; congr 1
  nlinarith [Real.exp_pos (5*Real.log (Nat.card K)-u-s)]
omit [Finite K] [FiniteDimensional K V] in
lemma ReciprocalLevels.second_size {p : Law (FlagPair K V)} {u s : ℝ}
    (L : ReciprocalLevels p u s) (B : Finset (ℙ K (Dual K V))) (hB : 0<L.secondLaw B) :
    Real.exp (u-s)/2≤(B.card:ℝ) := by
  have h:=(L.second_good B hB).2.2.1
  have he : Real.exp u*Real.exp (-s)=Real.exp (u-s) := by rw [←Real.exp_add]; congr 1
  nlinarith [Real.exp_pos (u-s)]

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_WindowVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section

theorem pivot_support_product (q u v k d a b : ℝ) (hq : 0<q)
    (hdrop : u-v≤d)
    (ha : Real.exp (5*Real.log q-u-k)/2≤a)
    (hb : Real.exp (v-k)/2≤b) :
    q^5*Real.exp (-d-2*k)/4≤a*b := by
  have he : Real.exp (5*Real.log q-u-k)/2*(Real.exp (v-k)/2)=
      q^5*Real.exp (v-u-2*k)/4 := by
    rw [div_mul_div_comm,←Real.exp_add]
    have hx : (5*Real.log q-u-k)+(v-k)=5*Real.log q+(v-u-2*k) := by ring
    have hfive : Real.exp (5*Real.log q)=Real.exp (Real.log q)^5 := by
      simpa using Real.exp_nat_mul (Real.log q) 5
    rw [hx,Real.exp_add,hfive,Real.exp_log hq]
    norm_num
  have hle := mul_le_mul ha hb (by positivity : 0≤Real.exp (v-k)/2)
    ((by positivity : 0≤Real.exp (5*Real.log q-u-k)/2).trans ha)
  rw [he] at hle
  refine le_trans ?_ hle
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_WindowLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  {w r : ℕ} [Nonempty (Fin r)]

namespace ReciprocalWindows
local instance windowLevelsBlockDE_r324473_1 : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.windowLevelsIndexDE
variable {p : Law (Slots w r→FlagPair K V)} {u : Slots w r→ℝ}
  {sel : (Fin w×Bool)→Fin r} {e : I→Fin w} {s : ℝ}
  (W : ReciprocalWindows p u sel e s)

omit [FiniteDimensional K V] [Nonempty (Fin r)] in
lemma support_product (k : ℝ) (hdrop : ∀ i,u (earlySlot sel (e i))-u (lateSlot sel (e i)) ≤ k)
    (i : I) (A : Finset (ℙ K V)) (B : Finset (ℙ K (Dual K V))) :
    (Nat.card K:ℝ)^5*Real.exp (-(k+2*s+Real.log 4)) ≤
      ((W.firstSupport i A).card:ℝ)*(W.secondSupport i B).card := by
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  have hh:=pivot_support_product (Nat.card K) (u (earlySlot sel (e i))) (u (lateSlot sel (e i)))
    s k (W.firstSupport i A).card (W.secondSupport i B).card hq (hdrop i)
    ((W.early i).first_size _ ((W.early i).firstLaw.repair_positive A))
    ((W.late i).second_size _ ((W.late i).secondLaw.repair_positive B))
  have he : Real.exp (-(k+2*s+Real.log 4))=Real.exp (-k-2*s)/4 := by
    rw [show -(k+2*s+Real.log 4)=(-k-2*s)-Real.log 4 by ring,
      Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<4)]
  simpa only [he,mul_div_assoc] using hh

end ReciprocalWindows

end
end SharpRamseyFive.Marking

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
local instance hpsTDE_r324473_1 : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.hpsIDE
omit [Finite K] [FiniteDimensional K V] in
lemma historyPrivateStream_mean {Θ : Type} [Fintype Θ]
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (elig : κ→Fin w×Bool→Finset (Fin n)) (steps : ℕ)
    (Γ : WindowHistory κ K V w n steps→Type) [∀h,Fintype (Γ h)] (q : ∀h,Law (Γ h))
    (tables : Law Θ)
    (F : (h : WindowHistory κ K V w n steps)→(Slots w n→FlagPair K V)→Γ h→Θ→ℝ) :
    mean (adaptiveLaw (historyPrivateStream S ctx elig steps Γ q).law (fun _=>tables))
      (fun z=>F (actualWindowHistory ctx steps z.1.1) (windowTuple S z.1.1.1) z.1.2 z.2)=
    mean (preRoundLaw (first (pair S.law ctx (windowTuple S))) (fiber (pair S.law ctx (windowTuple S))) elig steps)
      (fun h=>mean (windowPosterior (fiber (pair S.law ctx (windowTuple S))) h)
        (fun x=>mean (q h) (fun v=>mean tables (F h x v)))) := by
  exact originalHistory_private_mean S.law ctx (windowTuple S) elig steps Γ q tables F
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_WindowPosterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype Ω] [Fintype κ] [Fintype α] {N w n : ℕ} [Nonempty (Fin n)]
  {admissible : (Fin N→α)→Prop}

local instance wpBDE_r324473_1 : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance wpTDE_r324473_1 : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.wpSDE
omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin n)] in
lemma window_posterior_domains (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (D : κ→Fin (w*(4*n))→Finset (FlagPair K V))
    (hD : ∀z,0<S.law z→∀i,S.tuple z i∈D (ctx z) i) :
    ∀c,0<first (pair S.law ctx (windowTuple S)) c→
      InDomains (fiber (pair S.law ctx (windowTuple S)) c) (fun i=>D c (slotEmbedding i)) := by
  exact pair_fiber_domains S.law ctx (windowTuple S) _ (fun z hz i=>hD z hz (slotEmbedding i))

omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin n)] in
lemma window_posterior_consistent (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (hcons : ∀z,0<S.law z→TupleConsistent (S.tuple z)) :
    ∀c,0<first (pair S.law ctx (windowTuple S)) c→∀x,0<fiber (pair S.law ctx (windowTuple S)) c x→
      ∀i j,slotEmbedding i < slotEmbedding j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2 := by
  apply pair_fiber_pred
  intro z hz i j hij
  exact hcons z hz _ _ hij
omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin n)] in
lemma window_posterior_incident (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (hinc : ∀z,0<S.law z→TupleIncident (S.tuple z)) :
    ∀c,0<first (pair S.law ctx (windowTuple S)) c→∀x,0<fiber (pair S.law ctx (windowTuple S)) c x→
      ∀i,Incident (x i).1 (x i).2 := by
  apply pair_fiber_pred
  intro z hz i
  exact hinc z hz _
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_StreamGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype Ω] [Fintype κ] [Fintype α]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}
omit [FiniteDimensional K V] in
lemma Prepared.geometric {S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible}
    {ctx : Ω→κ} {J B M : ℝ} (P : Prepared S ctx J B M) : Geometric S M :=
  ⟨P.incident,P.consistent,P.occupancy⟩
namespace Geometric
variable {S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible} {M : ℝ}
omit [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma restrict (P : Geometric S M) (E : Finset Ω) (hE : 0<eventMass S.law E) :
    Geometric (S.restrict E hE) M := by
  have hp : ∀z,0<(S.restrict E hE).law z→0<S.law z :=
    fun z hz=>(conditionOn_positive S.law E hE z hz).2
  exact ⟨fun z hz=>P.incident z (hp z hz),fun z hz=>P.consistent z (hp z hz),
    fun z hz=>P.occupancy z (hp z hz)⟩
omit [FiniteDimensional K V] in
lemma reindex (P : Geometric S M) (e : Fin l↪o Fin n) : Geometric (S.reindex e) M :=
  ⟨fun z hz i=>P.incident z hz (e i),
    fun z hz i j hij=>P.consistent z hz (e i) (e j) (e.strictMono hij),
    fun z hz=>occupancy_reindex _ e e.injective M (P.occupancy z hz)⟩
omit [FiniteDimensional K V] in
lemma extract (P : Geometric S M) (hl : l≤n) (pos : Ω→Finset (Fin n)) :
    Geometric (S.extract hl pos) M := by
  have hsub (z : Ω) : ∃e : Fin l↪o Fin n,∀i,S.tuple z (e i)=(S.extract hl pos).tuple z i :=
    (mem_occurrences_iff _ _).mp (retainedTuple_occurs hl (S.tuple z) (pos z))
  constructor
  · intro z hz
    obtain ⟨e,he⟩:=hsub z
    intro i
    rw [←he i]
    exact P.incident z hz (e i)
  · intro z hz
    obtain ⟨e,he⟩:=hsub z
    intro i j hij
    rw [←he i,←he j]
    exact P.consistent z hz (e i) (e j) (e.strictMono hij)
  · intro z hz
    obtain ⟨e,he⟩:=hsub z
    have hh:=occupancy_reindex (S.tuple z) e e.injective M (P.occupancy z hz)
    simpa only [he] using hh
omit [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma augment (P : Geometric S M) (q : Ω→Law κ) : Geometric (S.augment q) M := by
  have hp : ∀z,0<(S.augment q).law z→0<S.law z.1 := by
    intro z hz
    change 0<S.law z.1*q z.1 z.2 at hz
    exact ((mul_pos_iff.mp hz).resolve_right (fun h=>(S.law.nonneg _).not_gt h.1)).1
  exact ⟨fun z hz=>P.incident z.1 (hp z hz),fun z hz=>P.consistent z.1 (hp z hz),
    fun z hz=>P.occupancy z.1 (hp z hz)⟩
omit [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma augmentSigma {Γ : Ω→Type} [∀z,Fintype (Γ z)] (P : Geometric S M) (q : ∀z,Law (Γ z)) :
    Geometric (S.augmentSigma q) M := by
  have hp : ∀z,0<(S.augmentSigma q).law z→0<S.law z.1 :=
    fun z hz=>(sigmaLaw_positive S.law q z hz).1
  exact ⟨fun z hz=>P.incident z.1 (hp z hz),fun z hz=>P.consistent z.1 (hp z hz),
    fun z hz=>P.occupancy z.1 (hp z hz)⟩
end Geometric

attribute [instance] CodedStream.finiteSample CodedStream.finiteCode
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_WindowStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking PivotTree MessageWeights ReverseCap ScoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N w n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.awsBDE
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.awsTDE
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.awsIDE
variable (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
  (ctx : Ω→κ) (elig : κ→Fin w×Bool→Finset (Fin n)) (steps : ℕ)

variable (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
  (u : WindowHistory κ K V w n steps→Slots w n→ℝ)
  (E : WindowHistory κ K V w n steps→Finset (Fin w)) {s : ℝ}
  (W : ∀h,∀he : (E h).Nonempty,ReciprocalWindows (windowPosterior (windowFiber S ctx) h)
    (u h) h.2 (survivingOriginal (E h) he) s)
  (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
  (c δ τ P : ℝ) (hδ : 0<δ)

lemma actualWindow_loss_mean (bad : WindowHistory κ K V w n steps→Slots w n→ℝ) :
    mean (adaptiveLaw (levelWindowStream S ctx elig steps u E W).law (fun _=>variableTreeLaw f r w))
      (fun z=>((actualWindowPositions S ctx steps f r u E W σ hσ hq hd c δ τ P hδ bad z.2 z.1)ᶜ.card:ℝ))=
    mean (preRoundLaw (first (pair S.law ctx (windowTuple S))) (windowFiber S ctx) elig steps)
      (fun h=>mean (allWindowExperiment f r (windowPosterior (windowFiber S ctx) h)
        (u h) h.2 (E h) (W h)) (fun z=>
          ((allWindowPositions f r (windowPosterior (windowFiber S ctx) h) (u h) h.2 (E h) (W h)
            σ hσ hq hd c δ τ P hδ (bad h) z.2.2 (z.1,z.2.1))ᶜ.card:ℝ))) := by
  unfold actualWindowPositions
  simp only [equivPositions_compl_card]
  have h:=historyPrivateStream_mean S ctx elig steps
    (fun h=>WindowLevelsData (K:=K) (V:=V) (E h).card)
    (fun h=>allWindowLevelLaw (windowPosterior (windowFiber S ctx) h) (u h) h.2 (E h) (W h))
    (variableTreeLaw f r w)
    (fun h x v t=>((allWindowPositions f r (windowPosterior (windowFiber S ctx) h)
      (u h) h.2 (E h) (W h) σ hσ hq hd c δ τ P hδ (bad h) t (x,v))ᶜ.card:ℝ))
  simpa only [levelWindowStream,allWindowExperiment,mean_adaptive] using h

theorem actualWindow_stage {l : ℕ} (hl : l<w*(2*n))
    (bad : WindowHistory κ K V w n steps→Slots w n→ℝ)
    (L M : ℝ) (hf : ∀C,(f C).Normalized) (hr : ∀C,(r C).Normalized)
    (hcost : ∀h,∀v : WindowLevelsData (K:=K) (V:=V) (E h).card,∀t,
      variableTreeCost f r t (Finset.univ,Finset.univ)
        (allWindowEncoded f r (windowPosterior (windowFiber S ctx) h) (u h) h.2 (E h) (W h)
          σ hσ hq hd c δ τ P hδ t v)≤L)
    (hcap : ∀h,∀v : WindowLevelsData (K:=K) (V:=V) (E h).card,∀t j,
      Real.log (variableTreeDomain f r t (Finset.univ,Finset.univ)
        (allWindowEncoded f r (windowPosterior (windowFiber S ctx) h) (u h) h.2 (E h) (W h)
          σ hσ hq hd c δ τ P hδ t v) j).card≤M)
    (hloss : mean (preRoundLaw (first (pair S.law ctx (windowTuple S))) (windowFiber S ctx) elig steps)
      (fun h=>mean (allWindowExperiment f r (windowPosterior (windowFiber S ctx) h)
        (u h) h.2 (E h) (W h)) (fun z=>
          ((allWindowPositions f r (windowPosterior (windowFiber S ctx) h) (u h) h.2 (E h) (W h)
            σ hσ hq hd c δ τ P hδ (bad h) z.2.2 (z.1,z.2.1))ᶜ.card:ℝ)))≤
      ((w*(2*n):ℝ)-l)/10) :
    ∃ (t : VariableTreeTape f r w)
      (hE : 0<eventMass (levelWindowStream S ctx elig steps u E W).law
        (Finset.univ.filter fun z=>l≤(actualWindowPositions S ctx steps f r u E W
          σ hσ hq hd c δ τ P hδ bad t z).card)),
      let S':=((levelWindowStream S ctx elig steps u E W).restrict _ hE).extract hl.le
        (actualWindowPositions S ctx steps f r u E W σ hσ hq hd c δ τ P hδ bad t)
      S'.density≤(10/9)*S.density ∧
      Nonempty (ContextDescription
        (κ:=VariableTreeMessage f r t (Finset.univ,Finset.univ)×RunAssignment l (w+1))
        S'.law S'.tuple (L+(w+1)*Real.log (l+1)) M) := by
  obtain ⟨t,hE,_,hden,hdesc⟩:=fixed_table_stage_dependent hl
    (levelWindowStream S ctx elig steps u E W) (variableTreeLaw f r w)
    (fun t=>VariableTreeMessage f r t (Finset.univ,Finset.univ))
    (actualWindowPositions S ctx steps f r u E W σ hσ hq hd c δ τ P hδ bad)
    (actualWindowEncoded S ctx steps f r u E W σ hσ hq hd c δ τ P hδ)
    (fun t=>variableTreeDomain f r t (Finset.univ,Finset.univ))
    (fun z i=>survivorRank (E (actualWindowHistory ctx steps z.1))
      (finProdFinEquiv.symm i : Fin w×Fin (2*n)).1)
    (fun _=>middleRank_monotone _)
    (fun t=>variableTreeCost f r t (Finset.univ,Finset.univ)) L M
    (fun t=>variableTree_weight f r t _ hf hr)
    (fun t z _=>hcost _ z.2 t) (fun t z _ j=>hcap _ z.2 t j) (by
      intro t z _ i hi
      rw [actualWindowPositions,mem_equivPositions] at hi
      exact (Finset.mem_filter.mp hi).2.2.2) (by
      convert (actualWindow_loss_mean S ctx elig steps f r u E W σ hσ hq hd c δ τ P hδ bad).trans_le hloss using 1
      · apply congrArg (mean _)
        funext z
        congr 2
        ext i
        simp only [Finset.mem_compl]
      · simp only [Nat.cast_mul,Nat.cast_ofNat])
  refine ⟨t,hE,hden,?_⟩
  simpa only [Nat.cast_add,Nat.cast_one] using hdesc
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_CodedWindowStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking PivotTree MessageWeights ReverseCap ScoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N w n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}
local instance cwsBDE_r324473_1 : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.cwsTDE
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.cwsIDE
variable (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
  (ctx : Ω→κ) (elig : κ→Fin w×Bool→Finset (Fin n)) (steps : ℕ)
  (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
  (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
  (u : WindowHistory κ K V w n steps→Slots w n→ℝ)
  (E : WindowHistory κ K V w n steps→Finset (Fin w)) {s : ℝ}
  (W : ∀h,∀he : (E h).Nonempty,ReciprocalWindows (windowPosterior (windowFiber S ctx) h)
    (u h) h.2 (survivingOriginal (E h) he) s)
  (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
  (c δ τ P : ℝ) (hδ : 0<δ)
omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma levelWindowStream_geometric {M : ℝ} (hG : Geometric S M) :
    Geometric (levelWindowStream S ctx elig steps u E W) M := by
  exact ((hG.augment _).reindex (middleEmbedding w n)).augmentSigma _
theorem actualWindow_coded {l : ℕ} (hl : l<w*(2*n))
    (bad : WindowHistory κ K V w n steps→Slots w n→ℝ)
    (L J M : ℝ) (hG : Geometric S M) (hf : ∀C,(f C).Normalized) (hr : ∀C,(r C).Normalized)
    (hcost : ∀h,∀v : WindowLevelsData (K:=K) (V:=V) (E h).card,∀t,
      variableTreeCost f r t (Finset.univ,Finset.univ)
        (allWindowEncoded f r (windowPosterior (windowFiber S ctx) h) (u h) h.2 (E h) (W h)
          σ hσ hq hd c δ τ P hδ t v)≤L)
    (hcap : ∀h,∀v : WindowLevelsData (K:=K) (V:=V) (E h).card,∀t j,
      Real.log (variableTreeDomain f r t (Finset.univ,Finset.univ)
        (allWindowEncoded f r (windowPosterior (windowFiber S ctx) h) (u h) h.2 (E h) (W h)
          σ hσ hq hd c δ τ P hδ t v) j).card≤J)
    (hloss : mean (preRoundLaw (first (pair S.law ctx (windowTuple S))) (windowFiber S ctx) elig steps)
      (fun h=>mean (allWindowExperiment f r (windowPosterior (windowFiber S ctx) h)
        (u h) h.2 (E h) (W h)) (fun z=>
          ((allWindowPositions f r (windowPosterior (windowFiber S ctx) h) (u h) h.2 (E h) (W h)
            σ hσ hq hd c δ τ P hδ (bad h) z.2.2 (z.1,z.2.1))ᶜ.card:ℝ)))≤
      ((w*(2*n):ℝ)-l)/10) :
    Nonempty (CodedStream (K:=K) (V:=V) N l admissible ((10/9)*S.density)
      (L+(w+1)*Real.log (l+1)) J M) := by
  obtain ⟨t,hE,hden,⟨C⟩⟩:=actualWindow_stage S ctx elig steps f r u E W σ hσ hq hd c δ τ P hδ
    hl bad L J hf hr hcost hcap hloss
  refine ⟨{ sample:=_ ,stream:=_ ,code:=_ ,description:=C,density_bound:=hden,geometric:=?_ }⟩
  exact ((levelWindowStream_geometric S ctx elig steps u E W hG).restrict _ hE).extract hl.le _
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
local instance boundsBDE_r324473_1 (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
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

omit [Nonempty (Fin n)] in
lemma surviving_domain_card (hE : E.Nonempty) (k c τ P : ℝ) (hc : 0 < c) (hc9 : c≤9/10)
    (hb : 0≤k+2*s+Real.log 4)
    (hdrop : ∀v∈E,u (earlySlot sel v)-u (lateSlot sel v)≤k)
    (t : VariableTreeTape f r w) (z : WindowLevelsData (K:=K) (V:=V) E.card)
    (j : Fin (w+1)) :
    ((variableTreeDomain f r t (Finset.univ,Finset.univ)
      (survivingEncoded f r p u sel E hE (W hE) σ hσ hq hd.le c (9/10) τ P (by norm_num) t z) j).card:ℝ)≤
    2*((320/c+320)^2)*(Nat.card K:ℝ)^4*Real.exp ((k+2*s+Real.log 4)+1) := by
  exact variableTreeDomain_card f r t (Finset.univ,Finset.univ)
    ⟨E.card,Nat.lt_succ_of_le (by simpa using Finset.card_le_univ E)⟩ σ hσ hq hd
    (fun i=>(W hE).firstSupport i (z.1 i)) (fun i=>(W hE).secondSupport i (z.2 i))
    (fun i=>(W hE).first_nonempty i _) (fun i=>(W hE).second_nonempty i _)
    c τ P (k+2*s+Real.log 4) hc hc9 hb
    (fun i=>(W hE).support_product k
      (fun v=>hdrop _ (survivingOriginal_mem E hE v)) i (z.1 i) (z.2 i)) j

omit [Nonempty (Fin n)] in
theorem allWindow_domain_card (k c τ P : ℝ) (hc : 0 < c) (hc9 : c≤9/10)
    (hb : 0≤k+2*s+Real.log 4)
    (hdrop : ∀v∈E,u (earlySlot sel v)-u (lateSlot sel v)≤k)
    (t : VariableTreeTape f r w) (z : WindowLevelsData (K:=K) (V:=V) E.card)
    (j : Fin (w+1)) :
    ((variableTreeDomain f r t (Finset.univ,Finset.univ)
      (allWindowEncoded f r p u sel E W σ hσ hq hd.le c (9/10) τ P (by norm_num) t z) j).card:ℝ)≤
    2*((320/c+320)^2)*(Nat.card K:ℝ)^4*Real.exp ((k+2*s+Real.log 4)+1) := by
  unfold allWindowEncoded
  split_ifs with hE
  · exact surviving_domain_card f r p u sel E W σ hσ hq hd hE k c τ P hc hc9 hb hdrop t z j
  · rw [variableTreeEmpty_domain]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

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
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalDomainCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module ProjectiveIncidence FiniteEntropy Windows
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype I]

omit [Finite K] [FiniteDimensional K V] in
lemma endpoint_support_domains (p : Law (I→FlagPair K V)) (D : I→Finset (FlagPair K V))
    (hp : InDomains p D) (i : I) :
    support (FiniteEntropy.first (map p (fun x=>x i)))⊆(D i).image Prod.fst ∧
    support (FiniteEntropy.second (map p (fun x=>x i)))⊆(D i).image Prod.snd := by
  constructor
  · intro a ha
    obtain ⟨z,hz,rfl⟩:=map_positive (map p (fun x=>x i)) Prod.fst a (by simpa only [map_fst] using (mem_support _ _).mp ha)
    exact Finset.mem_image.mpr ⟨z,marginal_support_subset p D hp i ((mem_support _ _).mpr hz),rfl⟩
  · intro a ha
    obtain ⟨z,hz,rfl⟩:=map_positive (map p (fun x=>x i)) Prod.snd a (by simpa only [map_snd] using (mem_support _ _).mp ha)
    exact Finset.mem_image.mpr ⟨z,marginal_support_subset p D hp i ((mem_support _ _).mpr hz),rfl⟩

omit [Finite K] [FiniteDimensional K V] in
lemma ReciprocalCaps.of_domains (p : Law (I→FlagPair K V)) (D : I→Finset (FlagPair K V))
    (u : I→ℝ) (C : ℝ) (hp : InDomains p D)
    (hinc : ∀x,0<p x→∀i,Incident (x i).1 (x i).2)
    (hcap : ∀i,ForwardCaps (D i) (u i))
    (hflag : ∀i,((D i).card:ℝ)≤C*(Nat.card K:ℝ)^4) : ReciprocalCaps p u C := by
  refine ⟨hinc,?_,?_,?_⟩
  · intro i
    exact (Nat.cast_le.mpr (Finset.card_le_card (endpoint_support_domains p D hp i).1)).trans (hcap i).1
  · intro i
    exact (Nat.cast_le.mpr (Finset.card_le_card (endpoint_support_domains p D hp i).2)).trans (hcap i).2
  · intro i
    exact (Nat.cast_le.mpr (Finset.card_le_card (marginal_support_subset p D hp i))).trans (hflag i)

end
end

open Module ProjectiveIncidence FiniteEntropy Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical LinearAlgebra.Projectivization BigOperators

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_WindowCodeDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy Windows ReverseCap ScoreGeometry PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance wcdBDE_r324473_1 (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.Marking.wcdIDE
lemma codeDomain_log {q σ k s : ℝ} (hq : 0<q) (hσ : 0≤σ) (he : Real.log q=σ)
    (hb : 0≤k+2*s+Real.log 4) :
    0≤4*σ+codeDomainSlack k s ∧
    Real.log (2*((320/((9:ℝ)/100000)+320)^2)*q^4*Real.exp ((k+2*s+Real.log 4)+1))=
      4*σ+codeDomainSlack k s := by
  have hc : 0≤Real.log (2*(320/((9:ℝ)/100000)+320)^2) := Real.log_nonneg (by norm_num)
  constructor
  · unfold codeDomainSlack;linarith
  · rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_mul (by norm_num) (by positivity),
      Real.log_pow,he,Real.log_exp]
    dsimp [codeDomainSlack]
    ring
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V))) ]
lemma allWindow_domain_log
    (f : PivotContext K V→FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : PivotContext K V→FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    {w n : ℕ} [Nonempty (Fin n)] (p : Law (Slots w n→FlagPair K V))
    (u : Slots w n→ℝ) (sel : Fin w×Bool→Fin n) (E : Finset (Fin w))
    {s : ℝ} (W : ∀hE : E.Nonempty,ReciprocalWindows p u sel (survivingOriginal E hE) s)
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5)
    (k τ P : ℝ) (hb : 0≤k+2*s+Real.log 4)
    (hdrop : ∀v∈E,u (earlySlot sel v)-u (lateSlot sel v)≤k)
    (t : VariableTreeTape f r w) (z : WindowLevelsData (K:=K) (V:=V) E.card)
    (j : Fin (w+1)) :
    Real.log (variableTreeDomain f r t (Finset.univ,Finset.univ)
      (allWindowEncoded f r p u sel E W σ hσ hq hd.le (9/100000) (9/10) τ P (by norm_num) t z) j).card≤
      4*σ+codeDomainSlack k s := by
  have hlog:=codeDomain_log (q:=(Nat.card K:ℝ)) (σ:=σ) (k:=k) (s:=s)
    (by rw [←hq];positivity) (zero_le_one.trans hσ) (by rw [←hq,Real.log_exp]) hb
  exact log_card_of_card_bound _ _ _
    (allWindow_domain_card f r p u sel E W σ hσ hq hd k (9/100000) τ P
      (by norm_num) (by norm_num) hb hdrop t z j) hlog.1 hlog.2.le
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalSharpRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple

open Module ProjectiveIncidence FiniteEntropy Windows Marking PivotTree MessageWeights ReverseCap ScoreGeometry
open ParameterHierarchy Filter
open scoped Classical BigOperators LinearAlgebra.Projectivization Topology NNReal
noncomputable section

local instance rpsBDE_r324473_1 (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance rpsTDE_r324473_1 (w n : ℕ) : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.rpsIDE
theorem eventually_reciprocal_coded_stage_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb C₀ ρ : ℝ) (hCb : 0≤Cb) (hC : 0≤C₀) (hρ : 0<ρ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D k J lo hi B M width : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q₀ : ℕ) (K V Ω κ α : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α],
    ∀ (_hd : finrank K V=5) (_hq3 : 3≤Nat.card K) (N w n H rounds rem l : ℕ) [Nonempty (Fin n)]
      (admissible : (Fin N→α)→Prop)
      (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
      (ctx : Ω→κ) (PS : Prepared S ctx J B M)
      (u : κ→Slots w n→ℝ) (b : Fin 7)
      (_hforward : ∀c,0<FiniteEntropy.map S.law ctx c→∀i,ForwardCaps (PS.domain c (slotEmbedding i)) (u c i))
      (_hflag : ∀c,0<FiniteEntropy.map S.law ctx c→∀i,((PS.domain c (slotEmbedding i)).card:ℝ)≤C₀*(Nat.card K:ℝ)^4)
      (_hu : ∀c,0<FiniteEntropy.map S.law ctx c→∀i,lo≤u c i ∧ u c i≤hi)
      (_hband : ∀c,0<FiniteEntropy.map S.law ctx c→∀i,BandCondition (Real.log (Nat.card K)) width (u c i) b)
      (_hlohi : lo≤hi) (_hk : 0<k) (_hJ : 4*Real.log (Nat.card K)≤J)
      (_hσ : 1≤σ) (_hq : Real.exp σ=Nat.card K),
      Nat.card K=q₀ → Range η σ D R → (L₀:ℝ)=L η σ D →
      0 < rounds → 0 < rem → n≤2*rem → rem+rounds≤n → l<w*(2*n) →
      0≤M → 2≤D*σ^(2*beta η) →
      Real.log 32+width+3*(D*σ^(2*beta η))<Real.log (Nat.card K) →
      Real.log 32+3*(D*σ^(2*beta η))<width →
      0≤k+2*(D*σ^(2*beta η))+Real.log 4 →
      k+2*(D*σ^(2*beta η))+Real.log 4≤Cb*D*σ^(6*beta η) →
      w<2^H → (H:ℝ)≤σ^beta η →
      reciprocalBadMass (D*σ^(2*beta η)) (D*σ^beta η) C₀≤1/2 →
      2*(D*σ^beta η+Real.log 32+Real.log 33+2*(Real.log (5*Real.log (Nat.card K)+1)+1))/(D*σ^(2*beta η))+
        2*Real.exp 1*reciprocalBadMass (D*σ^(2*beta η)) (D*σ^beta η) C₀≤1/2 →
      ((4*Real.exp 1)^2*80004)*(σ^(-2000*beta η)/Real.exp σ)≤1/(4*(Nat.card K:ℝ)) →
      5*(B/(D*σ^beta η)+(2*B/rounds+(if b.val%2=0 then (4*(w*(4*n):ℝ)*M)/rem else 0))/(σ^(-2000*beta η)/Real.exp σ))+
        (2*n:ℝ)*((hi-lo+2*(w:ℝ)*(2*(D*σ^(2*beta η))+Real.log 64))/k)+(w*(2*n):ℝ)*ρ≤
        ((w*(2*n):ℝ)-l)/10 →
      Nonempty (CodedStream (K:=K) (V:=V) N l admissible ((10/9)*S.density)
        (windowCodeBudget σ (Nat.card K) (P η σ D R) (k+2*(D*σ^(2*beta η))+Real.log 4) w H+
          (w+1)*Real.log (l+1)) (4*σ+codeDomainSlack k (D*σ^(2*beta η))) M) := by
  filter_upwards [eventually_actual_reciprocal_loss hη hη' Cb C₀ ρ hCb hC hρ,
    eventually_allWindow_cost hη hη' Cb hCb] with σ hloss hcost
  intro D k J lo hi B M width R L₀ q₀ K V Ω κ α _ _ _ _ _ _ _ _ _ _ _ _ hd hq3 N w n H rounds rem l _
    admissible S ctx PS u b hforward hflag hu hband hlohi hk hJ hσ hq hcard hrange hL
    hrounds hrem hn hroom hl hM hs hsmall hwide hb0 hbhi hw hH hmass hend hε hnum
  have hD : 0<D := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hσ) _).trans_le hrange.dlo
  let f:=fun C : PivotContext K V=>fourFinitePredictor hd σ C.1 C.2
    (P η σ D R) (σ^(-800*beta η)) R L₀
  let r:=fun C : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
    (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding)
      (P η σ D R) (σ^(-800*beta η)) R L₀
  obtain ⟨i,hbad⟩:=reciprocal_prepared_round_sharp hd S ctx J B M PS rounds rem hrounds hrem hroom
    (D*σ^beta η) (D*σ^(2*beta η)) (σ^(-2000*beta η)/Real.exp σ) width
    (by positivity) hs (by positivity) hM u b hband hsmall hwide
  let μ:=first (pair S.law ctx (windowTuple S))
  let p:=fiber (pair S.law ctx (windowTuple S))
  let elig:=fun _ : κ=>fun _ : Fin w×Bool=>(Finset.univ : Finset (Fin n))
  have hh : ∀c,0<μ c→0<FiniteEntropy.map S.law ctx c := by intro c hc;simpa only [μ,first_pair] using hc
  have hcaps : ∀c,0<μ c→ReciprocalCaps (p c) (u c) C₀ := by
    intro c hc
    exact ReciprocalCaps.of_domains (p c) (fun j=>PS.domain c (slotEmbedding j)) (u c) C₀
      (window_posterior_domains S ctx PS.domain PS.contains c hc)
      (window_posterior_incident S ctx PS.incident c hc) (hforward c (hh c hc)) (hflag c (hh c hc))
  have hroom' : ∀c,0<μ c→∀b,rem+i.val≤(elig c b).card := by
    intro c hc b
    simpa only [elig,Finset.card_univ,Fintype.card_fin] using
      (Nat.add_le_add_left (Nat.le_of_lt i.isLt) rem).trans hroom
  obtain ⟨W,hW⟩:=hloss D k J lo hi _ R L₀ q₀ K V κ hd hq3 w n H i.val rem μ p elig u hcaps
    (window_posterior_consistent S ctx PS.consistent) (fun c hc=>hu c (hh c hc))
    hlohi hk hJ hσ hq hcard hrange hL hb0 hbhi hw hH hmass hend hε hrem hn hroom' hbad
  let E:=actualWindowSet μ p u J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ) (D*σ^(2*beta η)) k (steps:=i.val)
  have hdrop : ∀h,∀v∈E h,u h.1.1 (earlySlot h.2 v)-u h.1.1 (lateSlot h.2 v)≤k := by
    intro h v hv
    dsimp only [E,actualWindowSet] at hv
    split_ifs at hv with hp
    · exact (Finset.mem_filter.mp hv).2
    · exact False.elim (Finset.notMem_empty v hv)
  apply actualWindow_coded S ctx elig i.val f r (fun h=>u h.1.1) E W σ hσ hq hd.le
    (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) hl
    (preRoundBad μ p elig i.val J (D*σ^beta η) (σ^(-2000*beta η)/Real.exp σ)
      (historyCollision p u (D*σ^(2*beta η))))
    (windowCodeBudget σ (Nat.card K) (P η σ D R) (k+2*(D*σ^(2*beta η))+Real.log 4) w H)
    (4*σ+codeDomainSlack k (D*σ^(2*beta η))) M PS.geometric
  · intro C
    exact fourFinite_weight hd σ C.1 C.2 (P η σ D R) (σ^(-800*beta η)) R L₀
  · intro C
    exact fourFinite_weight (K:=K) (V:=Dual K V) (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding) (P η σ D R) (σ^(-800*beta η)) R L₀
  · intro h v t
    exact hcost D k (D*σ^(2*beta η)) R L₀ q₀ K V hd w n H (windowPosterior p h) (u h.1.1)
      h.2 (E h) (W h) hσ hq hcard hrange hL hb0 hbhi (hdrop h) hw t v
  · intro h v t j
    exact allWindow_domain_log f r (windowPosterior p h) (u h.1.1) h.2 (E h) (W h)
      σ hσ hq hd k (σ^(-1000*beta η)) (P η σ D R) hb0 (hdrop h) t v j
  · exact hW.trans hnum
end

end SharpRamseyFive.SelectedTuple

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.SelectedTuple.eventually_reciprocal_coded_stage_oai := @OAI.SharpRamseyFive.SelectedTuple.eventually_reciprocal_coded_stage_oai
