-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.run_initial_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:12:07.840248+00:00
-- url     : https://prove2.me/submissions/a654506b-d6f2-407b-9e06-d98b4e755aec

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K043
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledLoop_pack_length_bound_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledStep_run_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalCoupledMerge_transition_valid_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace Signed
lemma encode_length (z : ℤ) : (encode z).length=z.natAbs.size+1 := by
  simp only [encode,List.length_cons,Nat.size_eq_bits_len]
end Signed
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Height
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalHeight
open scoped BigOperators

lemma Height.mono {q : ℚ} {b c : ℕ} (h : Height q b) (hc : b ≤ c) : Height q c :=
  ⟨h.1.trans (Nat.pow_le_pow_right (by norm_num) hc),h.2.trans (Nat.pow_le_pow_right (by norm_num) hc)⟩

end MetricKMedianRecovery.RationalHeight

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryRational
lemma encode_length (q : ℚ) : (encode q).length=2*(q.num.natAbs.size+1)+1+q.den.size := by
  simp only [encode,pairBits_length,Signed.encode_length,←Nat.size_eq_bits_len]
lemma input_height (q : ℚ) : RationalHeight.Height q (encode q).length := by
  rw [encode_length]
  constructor
  · apply Nat.le_of_lt
    apply Nat.size_le.mp
    omega
  · apply Nat.le_of_lt
    apply Nat.size_le.mp
    omega
end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MergeCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeCompletion
open PhaseSequence PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma attains_zero {loc : D → X} {F B Q : Finset X} {v lam : ℝ} {q c : ℕ}
    (h : Attains loc F B Q v lam q 0 c) : c = (Q ∩ F).card := by
  obtain ⟨T,hT,_,_,hc⟩ := h
  have he : T = [] := List.length_eq_zero_iff.mp hT
  simpa only [he,after] using hc.symm

end MetricKMedianRecovery.PhaseMergeCompletion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ImagePhaseUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [Fintype D] [PseudoMetricSpace X] in
lemma image_phase_union (Q : Finset X) (H : List X) (r : X → X) :
    Q.image r ∪ (H.map r).toFinset = (Q ∪ H.toFinset).image r := by
  ext x
  simp only [Finset.mem_union,Finset.mem_image,List.mem_toFinset,List.mem_map]
  aesop

omit [Fintype D] [PseudoMetricSpace X] in
lemma after_map (Q : Finset X) (T : List (List X)) (r : X → X) :
    after (Q.image r) (T.map (List.map r)) = (after Q T).image r := by
  induction T generalizing Q with
  | nil => rfl
  | cons H T ih =>
    simp only [List.map_cons,after,image_phase_union]
    exact ih _

omit [Fintype D] [PseudoMetricSpace X] in
lemma paid_image (F Q : Finset X) (r : X → X) (hinj : Function.Injective r)
    (hfix : ∀ i ∈ F, r i = i) :
    (Q.image r ∩ F).card = (Q ∩ F).card := by
  have heq : Q.image r ∩ F = (Q ∩ F).image r := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxQ,hxF⟩ := Finset.mem_inter.mp hx
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hxQ
      have haeq : r a = a := hinj (hfix (r a) hxF)
      exact Finset.mem_image.mpr ⟨a,Finset.mem_inter.mpr ⟨ha,haeq ▸ hxF⟩,rfl⟩
    · intro hx
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨a,(Finset.mem_inter.mp ha).1,rfl⟩,
        (hfix a (Finset.mem_inter.mp ha).2).symm ▸ (Finset.mem_inter.mp ha).2⟩
  rw [heq,Finset.card_image_of_injective _ hinj]

end MetricKMedianRecovery.PhaseHistoryTransfer

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Coupled
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseCountCrossing PhaseMergeInvariant
universe uD uX
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma Coupled.zero_false {loc : D → X} {F : Finset X} {v eta lo hi : ℝ} {q k : ℕ}
    (h : Coupled loc F v eta lo hi q 0 k) : False := by
  have ha := attains_zero h.new_tail
  have hb := attains_zero h.old_tail
  have he := PhaseHistoryTransfer.after_map ∅ h.P h.r
  simp only [Finset.image_empty] at he
  rw [he,paid_image F (after ∅ h.P) h.r h.inj h.fixed] at ha
  have hab : h.a = h.b := ha.trans hb.symm
  have hs := h.sandwich
  unfold Sandwich at hs
  omega

end MetricKMedianRecovery.PhaseCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LeafOrder
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [DecidableEq V] {d : ℕ}

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

lemma Certified.zero_false {loc : Fin d → V} {F : Finset V} {v eta lo hi : ℝ}
    {q k : ℕ} {s : State V} (h : Certified loc F v eta lo hi q 0 k s) : False :=
  h.coupled.zero_false

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopInvariant
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves RationalHeight
variable {V : Type*} [LinearOrder V] {d : ℕ}

lemma transition_value (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v M : ℚ) (N precision k : ℕ) (f : Frame V) :
    (transition loc distance F v M N precision k f).value loc distance F v M N precision k=
      f.value loc distance F v M N precision k := by
  rcases f with ⟨q,n,o⟩
  cases o with
  | inl o=>rfl
  | inr s=>
    cases n with
    | zero=>rfl
    | succ n=>
      rfl
lemma iterate_value (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v M : ℚ) (N precision k j : ℕ) (f : Frame V) :
    ((transition loc distance F v M N precision k)^[j] f).value loc distance F v M N precision k=
      f.value loc distance F v M N precision k := by
  induction j with
  | zero=>rfl
  | succ j ih=>rw [Function.iterate_succ_apply',transition_value,ih]

lemma iterate_stopped (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v M : ℚ) (N precision k j : ℕ) (f : Frame V) (hn : f.n≤j) :
    ((transition loc distance F v M N precision k)^[j] f).Stopped := by
  induction j generalizing f with
  | zero=>
    rcases f with ⟨q,n,o⟩
    cases o <;> simp only [Function.iterate_zero_apply,Frame.Stopped]
    exact Nat.eq_zero_of_le_zero hn
  | succ j ih=>
    rcases f with ⟨q,n,o⟩
    cases o with
    | inl o=>
      rw [Function.iterate_fixed (show transition loc distance F v M N precision k ⟨q,n,.inl o⟩=⟨q,n,.inl o⟩ from rfl)]
      trivial
    | inr s=>
      cases n with
      | zero=>
        rw [Function.iterate_fixed (show transition loc distance F v M N precision k ⟨q,0,.inr s⟩=⟨q,0,.inr s⟩ from rfl)]
        rfl
      | succ n=>
        rw [Function.iterate_succ_apply]
        exact ih _ (by simpa only [transition] using Nat.le_of_succ_le_succ hn)

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

lemma valid_stopped_output {loc : Fin d→V} {F : Finset V} {v eta lo hi : ℝ} {total k h p : ℕ}
    {f : Frame V} (hf : f.Valid loc F v eta lo hi total k h p) (hs : f.Stopped) :
    ∃ o,f.out=.inl o := by
  rcases f with ⟨q,n,o⟩
  cases o with
  | inl o=>exact ⟨o,rfl⟩
  | inr s=>
    change n=0 at hs
    subst n
    exact hf.2.1.zero_false.elim
end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopMachine
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledLoop
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryCoupled (stateBits outcomeBits outputBits)
variable {m d : ℕ} [PseudoMetricSpace (Fin m)]
attribute [local instance] RationalLeaves.metric
lemma step_pack (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset (Fin m))
    (Q₀ : Finset (Label (Fin m))) (v z M : ℚ) (N precision total k h p : ℕ)
    (eta lo hi : ℝ) (f : Frame (Fin m)) (hf : f.Valid loc F v eta lo hi total k h p)
    (hv : (0:ℝ)<v) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0≤eta) :
    step (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0)
      (20*N*M) precision k f)=
      pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0)
        (20*N*M) precision k (transition loc distance F v M N precision k f) := by
  rcases f with ⟨q,n,o⟩
  cases o with
  | inl o=>
    simp only [step,pack,outcomeBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
      extractPrefix_pairBits,ite_true, if_true,transition]
  | inr s=>
    cases n with
    | zero=>
      simp only [step,pack,outcomeBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
        extractPrefix_pairBits,List.cons_ne_self,ite_false, if_false,List.replicate_zero,ite_true, if_true,transition]
    | succ n=>
      have hh:=BinaryCoupledStep.run_pack_s238 distance loc hmetric F Q₀ v z M N n q precision k s eta lo hi hf.2.1 hv hv1 hlo heta
      have hin : input (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0)
          (20*N*M) precision k ⟨q,n+1,.inr s⟩)=
          BinaryCoupledStep.pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0)
            n q (20*N*M) precision k s := by
        simp only [input,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
          List.tail_replicate,outcomeBits,discardPrefix_pairBits,BinaryCoupledStep.pack,Nat.add_sub_cancel]
      have hactive : step (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0)
          (20*N*M) precision k ⟨q,n+1,.inr s⟩)=
          next (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0)
            (20*N*M) precision k ⟨q,n+1,.inr s⟩) := by
        simp only [step,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
          outcomeBits,extractPrefix_pairBits,List.cons_ne_self,ite_false, if_false,List.replicate_succ,List.cons_ne_nil]
      rw [hactive]
      simp only [next,hin,hh]
      simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
        transition,List.replicate_succ,List.tail_cons]
end MetricKMedianRecovery.BitMachine.BinaryCoupledLoop

namespace MetricKMedianRecovery.RationalHeight
lemma Height.le_pow {b : ℚ} {H : ℕ} (hb : Height b H) : b ≤ (2^H:ℕ) := by
  have hnum : (b.num:ℚ) ≤ (b.num.natAbs:ℚ) := by simpa only [Nat.cast_natAbs,Int.cast_abs] using le_abs_self (b.num:ℚ)
  have hN : (b.num.natAbs:ℚ) ≤ (2^H:ℕ) := by exact_mod_cast hb.1
  have hden : (1:ℚ) ≤ b.den := by exact_mod_cast b.den_pos
  have hnonneg : (0:ℚ) ≤ (2^H:ℕ) := by positivity
  rw [←Rat.num_div_den b]
  apply (div_le_iff₀ (by exact_mod_cast b.den_pos : (0:ℚ)<b.den)).mpr
  nlinarith
lemma Height.ceil_le_pow {b : ℚ} {H : ℕ} (hb : Height b H) : Nat.ceil b ≤ 2^H := by
  exact Nat.ceil_le.mpr hb.le_pow
lemma Height.clog_ceil {b : ℚ} {H : ℕ} (hb : Height b H) : Nat.clog 2 (Nat.ceil b) ≤ H :=
  (Nat.clog_le_iff_le_pow (by decide)).mpr hb.ceil_le_pow
end MetricKMedianRecovery.RationalHeight
namespace MetricKMedianRecovery.CanonicalLengthSearch
open RationalHeight
lemma heightBudget_le {b : ℚ} {precision H L : ℕ} (hb : Height b H) (hH : H ≤ L) (hp : precision ≤ L) :
    heightBudget b precision H ≤ 8*L+3 := by
  have hh:=hb.clog_ceil
  simp only [heightBudget,PriceBisection.iterations,sub_zero]
  omega
end MetricKMedianRecovery.CanonicalLengthSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopSize
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledLoop
open WordOperations WordList BinaryArithmetic RationalLeaves RationalHeight CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryCoupled (stateBits outcomeBits outputBits)
lemma components (base : List Bool) (b : ℚ) (precision k : ℕ) {m : ℕ} (f : Frame (Fin m)) :
    base.length ≤ (pack base b precision k f).length ∧
    f.q+f.n ≤ (pack base b precision k f).length ∧
    (BinaryRational.encode b).length ≤ (pack base b precision k f).length ∧
    precision ≤ (pack base b precision k f).length ∧
    k.bits.length ≤ (pack base b precision k f).length := by
  simp only [pack,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    List.length_cons,List.length_nil,List.length_replicate]
  omega
lemma base_dimension {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
    m ≤ (BinaryFiniteContext.pack distance loc F Q v z lam).length := by
  have h:=length_le_encode (List.ofFn (fun i : Fin m=>RationalMatrix.rowEncode (distance i)))
  simp only [List.length_ofFn] at h
  change m ≤ (Rectangular.encode distance).length at h
  simp only [BinaryFiniteContext.pack,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    List.length_cons,List.length_nil]
  omega

attribute [local instance] RationalLeaves.metric
end MetricKMedianRecovery.BitMachine.BinaryCoupledLoop

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledLoop
open WordOperations WordList BinaryArithmetic RationalLeaves RationalHeight CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryCoupled (stateBits outcomeBits outputBits)
variable {m d : ℕ} [PseudoMetricSpace (Fin m)]
attribute [local instance] RationalLeaves.metric
attribute [local irreducible] BinaryCoupledStep.run
lemma run_pack (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset (Fin m))
    (Q₀ : Finset (Label (Fin m))) (v z M : ℚ) (eta lo hi : ℝ) (N precision q n k : ℕ)
    (hF : F.Nonempty) (hM : 0<M) (hN : 3 ≤ N)
    (hv : (0:ℝ)<v) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0 ≤ eta)
    (hhi : hi ≤ 8*N*(M:ℝ)) (hprecision : (1/(2:ℚ)^precision:ℚ) ≤ eta)
    (hdiam : ∀ i∈F,∀ j,dist i (loc j) ≤ (M:ℝ))
    (s : State (Fin m)) (hc : Certified loc F v eta lo hi q n k s)
    (hkey : s.correction.Keys q)
    (hr : let x := pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0) (20*N*M) precision k ⟨q,n,.inr s⟩;
      s.Resources F q (CanonicalLengthSearch.heightBudget (20*N*M) precision x.length) x.length) :
    run (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0)
      (20*N*M) precision k ⟨q,n,.inr s⟩)=
      outputBits (CanonicalCoupledMerge.run loc distance F v M N precision k q n s) := by
  let base:=BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0
  let f : Frame (Fin m):=⟨q,n,.inr s⟩
  let x:=pack base (20*N*M) precision k f
  let L:=x.length
  let H:=CanonicalLengthSearch.heightBudget (20*N*M) precision L
  let tr:=transition loc distance F v M N precision k
  have hcomponents:=components base (20*N*M) precision k f
  change base.length ≤ L ∧ q+n ≤ L ∧ (BinaryRational.encode (20*N*M)).length ≤ L ∧ precision ≤ L ∧ k.bits.length ≤ L at hcomponents
  have hfar : Height (20*N*M) L := (BinaryRational.input_height _).mono hcomponents.2.2.1
  have hh : H ≤ 8*L+3:=CanonicalLengthSearch.heightBudget_le hfar le_rfl hcomponents.2.2.2.1
  have hm : m ≤ L:=(base_dimension distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0).trans hcomponents.1
  have hgood : ∀ j,(tr^[j] f).Valid loc F v eta lo hi (q+n) k H L := by
    intro j
    induction j with
    | zero=>exact ⟨rfl,hc,hr,hkey⟩
    | succ j ih=>
      rw [Function.iterate_succ_apply']
      exact transition_valid_s238 loc distance hmetric F v M eta lo hi N precision (q+n) k L L
        hF hM hN hv hv1 hlo heta hhi hprecision hdiam hfar _ ih
  have he : ∀ j,step^[j] x=pack base (20*N*M) precision k (tr^[j] f) := by
    intro j
    induction j with
    | zero=>rfl
    | succ j ih=>
      rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply']
      exact step_pack distance loc hmetric F Q₀ v z M N precision (q+n) k H L eta lo hi _ (hgood j) hv hv1 hlo heta
  have hbound : ∀ j,(step^[j] x).length ≤ capPoly.eval L := by
    intro j
    rw [he]
    exact pack_length_bound_s238 (hgood j) hcomponents.2.1 hm hh hcomponents.1 hcomponents.2.2.1
      hcomponents.2.2.2.1 hcomponents.2.2.2.2
  have hstate : stateRun x=pack base (20*N*M) precision k (tr^[n] f) := by
    simp only [stateRun,Function.comp_apply,iterationInput]
    rw [BoundedIteration.run_eq]
    · have hfield : field 1 x=List.replicate n true := by
        simp only [x,pack,f,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
      rw [hfield,List.length_replicate,he]
    · intro j _
      rw [capacity.word_length]
      exact hbound j
  obtain ⟨o,ho⟩:=valid_stopped_output (hgood n) (iterate_stopped loc distance F v M N precision k n f (le_refl n))
  have hval : o=CanonicalCoupledMerge.run loc distance F v M N precision k q n s := by
    have hh:=iterate_value loc distance F v M N precision k n f
    change (tr^[n] f).value loc distance F v M N precision k=f.value loc distance F v M N precision k at hh
    simpa only [Frame.value,ho,f] using hh
  change run x=_
  simp only [run,Function.comp_apply,hstate,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    ho,outcomeBits,discardPrefix_pairBits,hval]
end MetricKMedianRecovery.BitMachine.BinaryCoupledLoop

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_StartResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [DecidableEq V]
omit [DecidableEq V] in
lemma BankBound.empty (F : Finset V) (h key size : ℕ) : BankBound F h key size ∅ :=
  ⟨by simp,by simp,by intro c hc; simp at hc,by simp⟩
end MetricKMedianRecovery.RationalLeaves

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves RationalHeight
variable {V : Type*} [LinearOrder V] {d : ℕ}

omit [LinearOrder V] in
lemma initial_resources (F : Finset V) (h p : ℕ) (l u : ℚ)
    (T U : List (List (Label V))) (hl : Height l p) (hu : Height u p) :
    (initial l u T U).Resources F 0 h p :=
  ⟨BankBound.empty F h _ _,True.intro,hl,hu⟩

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_InitialLoop
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledLoop
open WordOperations WordList BinaryArithmetic RationalLeaves RationalHeight CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryCoupled (stateBits outcomeBits outputBits)
lemma initial_prices_length {m : ℕ} (base : List Bool) (b l u : ℚ) (precision k total : ℕ)
    (T U : List (List (Label (Fin m)))) :
    (BinaryRational.encode l).length ≤ (pack base b precision k ⟨0,total,.inr (initial l u T U)⟩).length ∧
    (BinaryRational.encode u).length ≤ (pack base b precision k ⟨0,total,.inr (initial l u T U)⟩).length := by
  simp only [pack,outcomeBits,stateBits,CanonicalCoupledMerge.initial,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    List.length_cons,List.length_nil,List.length_replicate,pairBits_length]
  omega
variable {m d : ℕ} [PseudoMetricSpace (Fin m)]
attribute [local instance] RationalLeaves.metric
lemma run_initial_s238_oai (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset (Fin m))
    (v M l u : ℚ) (eta lo hi : ℝ) (N precision total k : ℕ)
    (hF : F.Nonempty) (hM : 0<M) (hN : 3 ≤ N)
    (hv : (0:ℝ)<v) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0 ≤ eta)
    (hhi : hi ≤ 8*N*(M:ℝ)) (hprecision : (1/(2:ℚ)^precision:ℚ) ≤ eta)
    (hdiam : ∀ i∈F,∀ j,dist i (loc j) ≤ (M:ℝ))
    (T U : List (List (Label (Fin m)))) (hc : Certified loc F v eta lo hi 0 total k (initial l u T U)) :
    run (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) ∅ v 0 0)
      (20*N*M) precision k ⟨0,total,.inr (initial l u T U)⟩)=
      outputBits (CanonicalCoupledMerge.run loc distance F v M N precision k 0 total (initial l u T U)) := by
  apply run_pack distance loc hmetric F ∅ v 0 M eta lo hi N precision 0 total k
    hF hM hN hv hv1 hlo heta hhi hprecision hdiam _ hc
  · trivial
  · dsimp only
    apply initial_resources
    · exact (BinaryRational.input_height l).mono (initial_prices_length _ _ _ _ _ _ _ _ _).1
    · exact (BinaryRational.input_height u).mono (initial_prices_length _ _ _ _ _ _ _ _ _).2
end MetricKMedianRecovery.BitMachine.BinaryCoupledLoop

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.run_initial_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.run_initial_s238_oai
