-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_source_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:06:51.954836+00:00
-- url     : https://prove2.me/submissions/c1476c24-0da2-433e-a377-4471002a9c9d

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L031
import Definitions.Def_Q238L037
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchTape_Count_cut_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRandomizedBranch_source_run_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRecovery_atBranch_context_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_TensorEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySeed
lemma raw_tensorEquiv (ds : List ℕ) (b : ℕ) (s : Fin (count ds b)→Bool) :
    raw (tensorEquiv ds b s)=List.ofFn s := by
  induction ds with
  | nil=>rfl
  | cons n ns ih=>
    change Fin (n*count ns b)→Bool at s
    change (List.ofFn (fun i:Fin n=>raw (tensorEquiv ns b (fun j=>s (finProdFinEquiv (i,j)))))).flatten =
      List.ofFn (s:Fin (n*count ns b)→Bool)
    simp only [ih]
    conv_rhs => rw [List.ofFn_mul]
    congr 2
    funext i
    congr 1
    funext j
    congr 1
    apply Fin.ext
    change j.val+count ns b*i.val=i.val*count ns b+j.val
    ring
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape
open BinarySeed
variable (q a b L : ℕ)
lemma tensorPair_raw (s : Fin (M q a b L+K a b)→Bool) :
    BinarySeed.raw ((tensorPair q a b L s).1)++BinarySeed.raw ((tensorPair q a b L s).2)=List.ofFn s := by
  change BinarySeed.raw (tensorEquiv _ b _ )++BinarySeed.raw (tensorEquiv _ b _)=List.ofFn s
  rw [raw_tensorEquiv,raw_tensorEquiv]
  rw [List.ofFn_add]
  rfl
lemma raw_layout (s : Fin (M q a b L+K a b)→Bool) : raw q a b L (layout q a b L s)=List.ofFn s := by
  unfold raw layout
  rw [Equiv.trans_apply,Equiv.apply_symm_apply]
  exact tensorPair_raw q a b L s
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchSeedLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchTape
open BinarySeed BinaryObservableBranch
lemma colorTensor_colors (n : ℕ) (s : Fin (colorCount n)→Bool) :
    colorTensor (colors n s)=tensorEquiv [n] 2 s := by
  funext i
  exact Equiv.symm_apply_apply _ _
lemma labelTensor_labels (n b : ℕ) (s : Fin (labelCount n b)→Bool) :
    labelTensor (labels n b s)=tensorEquiv [n] (Nat.clog 2 b) s := by
  funext i
  exact Equiv.symm_apply_apply _ _
lemma raw_colors (n : ℕ) (s : Fin (colorCount n)→Bool) :
    BinarySeed.raw (colorTensor (colors n s))=List.ofFn s := by
  rw [colorTensor_colors]
  exact raw_tensorEquiv [n] 2 s
lemma raw_labels (n b : ℕ) (s : Fin (labelCount n b)→Bool) :
    BinarySeed.raw (labelTensor (labels n b s))=List.ofFn s := by
  rw [labelTensor_labels]
  exact raw_tensorEquiv [n] (Nat.clog 2 b) s
lemma split_raw (a b : ℕ) (s : Fin (a+b)→Bool) :
    List.ofFn ((split a b s).1)++List.ofFn ((split a b s).2)=List.ofFn s := by
  rw [List.ofFn_add]
  rfl
lemma raw_layout (n b p : ℕ) (s : Fin (count n b p)→Bool) : raw (layout n b p s)=List.ofFn s := by
  unfold raw layout
  simp only [Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map_fst,Prod.map_snd,raw_colors,raw_labels,
    BinaryCategorical.Tape.raw_layout]
  rw [split_raw,split_raw]
end MetricKMedianRecovery.BitMachine.BinaryBranchTape

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_FairPrefix
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
lemma take_ofFn_cast {n N : ℕ} (h : n≤N) (seed : Fin N→Bool) :
    (List.ofFn seed).take n=List.ofFn (fun i:Fin n=>seed (Fin.castLE h i)) := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_ofFn,min_eq_left h]
  · intro i hi hj
    simp only [List.getElem_take,List.getElem_ofFn]
    rfl
end MetricKMedianRecovery.FiniteSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch.Prefix
open WordOperations BinaryBranchContext
lemma source_run (A : ℝ) : ∃ d : ℕ, ∀ {n b K : ℕ} (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (colors0 : Fin n→Fin 3)
    (label0 : Fin n→Fin b) (q c : ℕ) (extra : List Bool) (r0 y0 : Fin n) (N : ℕ),
    N≤extra.length → (b:ℝ)≤A*Real.log ((N:ℝ)+2) → (hb0 : 0<b) →
    (hK : BinaryBranchTape.count n b s.leaves.length≤K) → ∀ seed : Fin K→Bool,
    run d (pairBits (pack δ D F S Δ s colors0 label0 q c extra,List.ofFn seed))=
    let seed':=BinaryBranchTape.layout n b s.leaves.length (fun i=>seed (Fin.castLE hK i))
    BinaryFinSet.encode (BinaryObservableBranch.output δ D F S Δ s (fun i=>ColorLabel.color (seed'.1.1 i))
      (fun i=>ColorLabel.label b hb0 (seed'.1.2 i)) q c r0 y0 seed'.2) := by
  obtain ⟨d,hd⟩:=BinaryRandomizedBranch.source_run_s238r A
  refine ⟨d,?_⟩
  intro n b K δ D F S Δ s colors0 label0 q c extra r0 y0 N hN hb hb0 hK seed
  rw [run,Function.comp_apply,BinaryBranchTape.Count.cut_pack_s238r,FiniteSampling.take_ofFn_cast hK,
    ←BinaryBranchTape.raw_layout]
  exact hd δ D F S Δ s colors0 label0 q c extra r0 y0 N hN hb hb0 _
end MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch.Prefix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_RecoveryTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryBranchTape
open BinaryOpeningPayment (field field_encode)
attribute [local irreducible] atBranch atZero context zeroContext
  BinaryRandomizedBranch.Prefix.run BinaryRandomizedZeroBranch.Prefix.run
  BinaryObservableBranch.output BinaryZeroBranch.output ColorLabel.label ColorLabel.color
  BinaryBranchTape.layout BinaryRandomizedZeroBranch.layout
lemma atBranch_source_s238r_oai (A : ℝ) : ∃ d : ℕ, ∀ {n m H : ℕ} (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (extra : List Bool)
    (r0 y0 : Fin n) (N : ℕ), N≤extra.length → (m:ℝ)≤A*Real.log ((N:ℝ)+2) →
    (hn : n≤H) → (hm : m≤H) → (hp : s.leaves.length≤H) →
    ∀ (q c : Fin (n+1)) (b : Fin m) (seed : Fin (tapeSize H)→Bool),
    atBranch d (pairBits (pack δ D F S Δ s m extra (List.ofFn seed),choiceBits q.val c.val b.val))=
      let seed':=positiveSeed hn hm hp b seed
      BinaryFinSet.encode (BinaryObservableBranch.output δ D F S Δ s (fun i=>ColorLabel.color (seed'.1.1 i))
        (fun i=>ColorLabel.label (b.val+1) (by omega) (seed'.1.2 i)) q.val c.val r0 y0 seed'.2) := by
  obtain ⟨d,hd⟩:=BinaryRandomizedBranch.Prefix.source_run A
  refine ⟨d,?_⟩
  intro n m H δ D F S Δ s extra r0 y0 N hN hlog hn hm hp q c b seed
  have hblog : ((b.val+1:ℕ):ℝ)≤A*Real.log ((N:ℝ)+2) :=
    (by exact_mod_cast Nat.succ_le_of_lt b.isLt : ((b.val+1:ℕ):ℝ)≤ m).trans hlog
  rw [atBranch_context_s238r]
  simpa only [positiveSeed] using hd (b:=b.val+1) (K:=tapeSize H) δ D F S Δ s
    (fun _=>(0:Fin 3)) (fun _=>(0:Fin (b.val+1))) q.val c.val extra r0 y0 N hN hblog (by omega)
    (BinaryBranchTape.count_bound hn ((Nat.succ_le_of_lt b.isLt).trans hm) hp) seed

end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_source_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.atBranch_source_s238r_oai
