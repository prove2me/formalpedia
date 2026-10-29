-- Prove2me | solution 1 for OAI.ContingencyTables.CountingPositiveProgram.value_source_sameLaw
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T04:52:58.911023+00:00
-- url     : https://prove2.me/submissions/2d0197e7-f6aa-44d3-bafa-140dfde0778b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A009
import Theorems.Thm_OAI_ContingencyTables_CompanionPhaseContinuation_run_sameLaw
import Theorems.Thm_OAI_ContingencyTables_CompanionRestartProgram_output_native_sameLaw

section
-- module Solutions.OAIQ089_CT.MatroidCounting_CommonBases
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CommonBasesFPRAS

section

section

open scoped BigOperators Classical
lemma uniformAverage_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (f : Y → ℝ) : uniformAverage (fun x => f (e x))=uniformAverage f := by
  rw [uniformAverage,uniformAverage,e.sum_comp,Fintype.card_congr e]
lemma uniformAverage_const {X : Type*} [Fintype X] [Nonempty X] (r : ℝ) :
    uniformAverage (fun _ : X => r)=r := by
  have h : (Fintype.card X:ℝ)≠0 := by exact_mod_cast ne_of_gt (Fintype.card_pos)
  simp [uniformAverage,h]
lemma uniformAverage_prod {X Y : Type*} [Fintype X] [Fintype Y] (f : X × Y → ℝ) :
    uniformAverage f=uniformAverage (fun x => uniformAverage (fun y => f (x,y))) := by
  simp only [uniformAverage,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul]
  rw [← Finset.sum_div]
  ring
lemma uniformAverage_fin_succ {X : Type*} [Fintype X] (D : ℕ)
    (f : (Fin (D+1) → X) → ℝ) :
    uniformAverage f=uniformAverage (fun x => uniformAverage (fun rest => f (Fin.cons x rest))) := by
  rw [← uniformAverage_equiv (Fin.consEquiv (fun _ : Fin (D+1) => X)) f,uniformAverage_prod]
  rfl

open scoped BigOperators Classical

end

open scoped BigOperators Classical

open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped Classical

open scoped Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped Classical

end

end CommonBasesFPRAS

open CommonBasesFPRAS

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteLawMoments
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Expectations of concrete finite-word output laws -/

namespace ContingencyTables.FiniteLawMoments

open CommonBasesFPRAS ResidualMixture FirstSuccess
open scoped BigOperators Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

lemma expectation_map [DecidableEq Y] (p : RationalLaw X) (draw : X → Y) (g : Y → ℝ) :
    expectation (mapLaw p draw) g=expectation p (fun x => g (draw x)) := by
  unfold expectation mapLaw
  simp only [Rat.cast_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  calc
    _ = ∑ y : Y,if draw x=y then (p.mass x:ℝ)*g y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp
    _ = _ := by simp

lemma expectation_uniform [Nonempty X] (g : X → ℝ) :
    expectation (uniformLaw (α := X)) g=uniformAverage g := by
  unfold expectation uniformLaw uniformMass uniformAverage
  simp only [Rat.cast_div,Rat.cast_one,Rat.cast_natCast]
  rw [←Finset.mul_sum]
  ring

lemma word_expectation [Nonempty X] [DecidableEq Y] (draw : X → Y) (g : Y → ℝ) :
    uniformAverage (fun x => g (draw x))=expectation (mapLaw (uniformLaw (α := X)) draw) g := by
  rw [expectation_map,expectation_uniform]

end ContingencyTables.FiniteLawMoments

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_InitialFactorialBits
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperFibreNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One finite Boolean word for the actual initial transversal

The word is split into disjoint cell blocks; each block chooses a size
and then a subset of that size. The total variation errors add before
the exact paired-transversal encoding is applied.
-/

namespace ContingencyTables.InitialFactorialBits

open CommonBasesFPRAS ResidualMixture FirstSuccess FairBits TwoLiftStates
open FixedCardinalityMixture InitialFactorialLaw InitialTransversals
open CompanionFactorialApplication
open scoped BigOperators Classical
noncomputable section

variable {q : ℕ}

theorem drawChoices_law (b : Fin q → ℕ) (B : ℕ) :
    mapLaw (uniformLaw (α := Fin (bitCount b B) → Bool)) (drawChoices b B)=
      piLaw (fun i => mapLaw (uniformLaw (α := Fin (drawBits B (b i)) → Bool))
        (subsetDraw B (b i))) := by
  have he := map_equiv (wordEquiv b B)
    (uniformLaw (α := Fin (bitCount b B) → Bool))
    (fun words i => subsetDraw B (b i) (words i))
  rw [uniform_equiv,←pi_uniformLaw,pi_mapLaw] at he
  exact he.symm

theorem bitCount_eq (b : Fin q → ℕ) (B : ℕ) :
    bitCount b B=(q+∑ i,b i)*B := by
  simp only [bitCount,drawBits,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,←Finset.sum_mul]
  simp only [Nat.cast_id]
  ring

theorem bitCount_bound (b : Fin q → ℕ) (B W : ℕ) (hb : ∀ i,b i≤W) :
    bitCount b B≤q*(W+1)*B := by
  rw [bitCount_eq]
  apply Nat.mul_le_mul_right
  have hs : (∑ i,b i)≤q*W := by
    calc
      _ ≤ ∑ _i : Fin q,W := Finset.sum_le_sum (fun i _ => hb i)
      _ = q*W := by simp
  nlinarith

end
end ContingencyTables.InitialFactorialBits

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitialDraw
attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual bounded-word initialization of the companion trace

The output is in the literal `PlainIndex` used by the trace chain. Its
ideal rational law is exactly the source's phase-zero law; the bounded
word implementation is within 2^(-h), with an explicit word length.
-/

namespace ContingencyTables.CompanionInitialDraw

open CommonBasesFPRAS ResidualMixture FirstSuccess TwoLiftStates
open CompanionFactorialApplication InitialFactorialLaw InitialFactorialBits
open RealKernelApproximation
open scoped BigOperators Classical
noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma cellCount_bound (A : Instance I J) : Fintype.card (SmallCell A)≤A.d := by
  exact (Fintype.card_le_of_injective (fun s : SmallCell A => s.val) Subtype.val_injective).trans
    (by simpa only [Fintype.card_prod] using A.hcard)

lemma cellCapacity_bound (A : Instance I J) (i : Fin (Fintype.card (SmallCell A))) :
    cellCapacity A i≤A.W :=
  (A.hsmall _ _ ((cellEnum A).symm i).property).le

theorem initialBits_bound (A : Instance I J) (B : ℕ) :
    initialBits A B≤A.d*(A.W+1)*B := by
  have hh := bitCount_bound (cellCapacity A) B A.W (cellCapacity_bound A)
  exact hh.trans (Nat.mul_le_mul_right B
    (Nat.mul_le_mul_right (A.W+1) (cellCount_bound A)))

end
end ContingencyTables.CompanionInitialDraw

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_TreeFraction
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma normalize_repr (x : Fraction) : normalize x=repr (val x) := by
  by_cases hd : x.2=0
  · simp [normalize,repr,val,hd]
  · have he : val x=mkRat (x.1:Int) x.2 := by simp [val,Rat.mkRat_eq_div]
    simp only [normalize,hd,↓reduceIte,he,repr,Rat.num_mkRat,Rat.den_mkRat]
    simp [Nat.gcd_comm,←Int.natCast_ediv]

lemma val_nonneg (x : Fraction) : 0≤val x := by unfold val; positivity
lemma val_repr {q : ℚ} (h : 0≤q) : val (repr q)=q := by
  have hn : 0≤q.num := by exact Rat.num_nonneg.mpr h
  have he : (q.num.natAbs : ℤ)=q.num := Int.natAbs_of_nonneg hn
  change (q.num.natAbs:ℚ)/(q.den:ℚ)=q
  rw [←Int.cast_natCast q.num.natAbs,he]
  exact Rat.num_div_den q

lemma normalize_val (x : Fraction) : val (normalize x)=val x := by
  rw [normalize_repr]
  exact val_repr (val_nonneg x)

lemma normalize_den_pos (x : Fraction) : 0<(normalize x).2 := by
  rw [normalize_repr]; exact (val x).pos

lemma mul_val (x y : Fraction) : val (mul (x,y))=val x*val y := by
  rw [mul,normalize_val]
  simp only [val,Nat.cast_mul]
  exact (div_mul_div_comm _ _ _ _).symm

lemma add_val (x y : Fraction) (hx : x.2≠0) (hy : y.2≠0) :
    val (add (x,y))=val x+val y := by
  rw [add,normalize_val]
  simp only [val,Nat.cast_add,Nat.cast_mul]
  rw [div_add_div (x.1:ℚ) (y.1:ℚ) (b:=(x.2:ℚ)) (d:=(y.2:ℚ))
    (by exact_mod_cast hx) (by exact_mod_cast hy)]
  ring

lemma div_val (x y : Fraction) : val (div (x,y))=val x/val y := by
  rw [div,normalize_val]
  simp only [val,Nat.cast_mul]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BooleanChunkProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial partition of a supplied Boolean word into fixed-width rows -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

lemma wordChunk_ofFn {n k : ℕ} (bits : Fin (n*k) → Bool) (i : Fin n) :
    wordChunk ((k,List.ofFn bits),i.val)=
      List.ofFn (fun j : Fin k => bits (finProdFinEquiv (i,j))) := by
  have hbound : k ≤ n*k-i.val*k := by
    apply Nat.le_sub_of_add_le
    simpa only [Nat.succ_mul,Nat.add_comm] using
      Nat.mul_le_mul_right k (Nat.succ_le_of_lt i.isLt)
  apply List.ext_getElem
  · simp only [wordChunk,List.length_take,List.length_drop,List.length_ofFn,min_eq_left hbound]
  · intro j _ _
    simp only [wordChunk,List.getElem_take,List.getElem_drop,List.getElem_ofFn]
    apply congrArg bits
    apply Fin.ext
    change i.val*k+j=j+k*i.val
    ac_rfl

theorem wordChunks_ofFn {n k : ℕ} (hk : 0<k) (bits : Fin (n*k) → Bool) :
    wordChunks (k,List.ofFn bits)=
      List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin k => bits (finProdFinEquiv (i,j)))) := by
  have hrows : completeWordRows (k,List.ofFn bits)=List.range n := by
    simp only [completeWordRows,List.length_ofFn,Nat.mul_div_cancel _ hk]
  unfold wordChunks
  rw [hrows]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    have hin : i<n := by simpa only [List.length_map,List.length_range] using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact wordChunk_ofFn bits ⟨i,hin⟩

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_DependentWordProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting a binary word at input-dependent coordinate widths -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

open scoped BigOperators

lemma take_ofFn_sum {q : ℕ} (width : Fin q → ℕ) (i : Fin q) :
    ((List.ofFn width).take i.val).sum=∑ j : Fin i.val,width (Fin.castLE i.isLt.le j) := by
  rw [←Fin.ofFn_take_eq_take_ofFn i.isLt.le,List.sum_ofFn]
  rfl

theorem dependentChunk_ofFn {q : ℕ} (width : Fin q → ℕ)
    (bits : Fin (∑ i,width i) → Bool) (i : Fin q) :
    dependentChunk ((List.ofFn width,List.ofFn bits),i.val)=
      List.ofFn (fun j : Fin (width i) => bits (finSigmaFinEquiv ⟨i,j⟩)) := by
  have hw : (List.ofFn width).getD i.val 0=width i := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,dite_true,Option.getD_some,Fin.eta]
  have hb : ((List.ofFn width).take i.val).sum+width i≤∑ j,width j := by
    by_cases hi : width i=0
    · rw [hi,Nat.add_zero,←List.sum_ofFn]
      exact (List.take_sublist i.val (List.ofFn width)).sum_le_sum (fun _ _ => Nat.zero_le _)
    · have hh := (finSigmaFinEquiv (⟨i,⟨width i-1,by omega⟩⟩ : Sigma (fun i => Fin (width i)))).isLt
      rw [finSigmaFinEquiv_apply,←take_ofFn_sum] at hh
      dsimp only at hh
      omega
  have hlen : width i≤(∑ j,width j)-((List.ofFn width).take i.val).sum :=
    Nat.le_sub_of_add_le (by omega)
  apply List.ext_getElem
  · simp only [dependentChunk,chunkStart,List.length_take,List.length_drop,List.length_ofFn,hw,
      min_eq_left hlen]
  · intro j hj _
    simp only [dependentChunk,chunkStart,List.getElem_take,List.getElem_drop,List.getElem_ofFn]
    apply congrArg bits
    apply Fin.ext
    simp only [finSigmaFinEquiv_apply,take_ofFn_sum]

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScaledWordProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary execution of the bounded quotient draw -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

theorem scaledWordValue_ofFn (M k : ℕ) (hM : 0<M) (bits : Fin k → Bool) :
    scaledWordValue (M,List.ofFn bits)=(FairBits.scaledBitInteger M k hM bits).val := by
  simp only [scaledWordValue,List.length_ofFn,bitValue_eq_word]
  rfl

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FixedCardinalityProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary arithmetic for sequential subset inclusion

The rational inclusion threshold is computed by an integer product and
quotient. In particular the denominator is never expanded into a
unary loop; the only exponential integer has the supplied word length
as its binary length.
-/

namespace ContingencyTables.FixedCardinalityProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

noncomputable section

theorem inclusion_threshold (B n k : ℕ) :
    FairBits.rationalThreshold B (FixedCardinalityLaw.headProbability n k)=
      2^B*min k (n+1)/(n+1) := by
  let M := 2^B*min k (n+1)
  have hd : ((n+1:ℕ):ℚ)≠0 := by positivity
  have he : (2:ℚ)^B*FixedCardinalityLaw.headProbability n k=
      (M:ℚ)/(n+1:ℕ) := by
    simp only [FixedCardinalityLaw.headProbability,M,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
      Nat.cast_add,Nat.cast_one]
    ring
  change ⌊(2:ℚ)^B*FixedCardinalityLaw.headProbability n k⌋₊=_
  rw [he]
  have hh := Nat.mul_cast_floor_div_cancel (R := ℚ) (n := n+1) (by omega)
    ((M:ℚ)/(n+1:ℕ))
  simpa only [div_mul_cancel₀ _ hd,Nat.floor_natCast] using hh.symm

/-- The executable natural-number comparison is exactly the inclusion
decision in the finite Boolean law. -/
theorem includeCode_ofFn (B n k : ℕ) (bits : Fin B → Bool) :
    includeCode ((n+1,k),List.ofFn bits)=FixedCardinalityBits.headDraw B n k bits := by
  simp only [includeCode,List.length_ofFn,bitValue_eq_word,FixedCardinalityBits.headDraw,
    FairBits.rationalThresholdAccept,inclusion_threshold]

end
end ContingencyTables.FixedCardinalityProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FixedCardinalityFold
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial sequential list program for the subset draw

The accumulator retains the remaining population and requested size,
and records one inclusion bit per input word. Both counters decrease;
only the output list grows. The final program reverses that list once.
-/

namespace ContingencyTables.FixedCardinalityProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

lemma fold_output (words : List (List Bool)) (n k : ℕ) (acc : List Bool) :
    (words.foldl (fun s word => advance (word,s)) ((n,k),acc)).2=
      (sampleWords n k words).reverse++acc := by
  induction words generalizing n k acc with
  | nil => simp [sampleWords]
  | cons w ws ih =>
    rw [List.foldl_cons]
    change (ws.foldl (fun s word => advance (word,s))
      ((n-1,if includeCode ((n,k),w) then k-1 else min k (n-1)),
        includeCode ((n,k),w)::acc)).2=_
    rw [ih]
    simp only [sampleWords,List.reverse_cons,List.append_assoc,List.singleton_append]

lemma drawWords_eq (n k : ℕ) (words : List (List Bool)) :
    drawWords ((n,k),words)=sampleWords n k words := by
  unfold drawWords
  rw [fold_output]
  simp

noncomputable section

theorem sampleWords_ofFn (B n k : ℕ) (words : Fin n → Fin B → Bool) :
    sampleWords n k (List.ofFn (fun i => List.ofFn (words i)))=
      List.ofFn (FixedCardinalityBits.draw B n k words) := by
  induction n generalizing k with
  | zero => simp [sampleWords,FixedCardinalityBits.draw]
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [sampleWords,includeCode_ofFn,Nat.add_sub_cancel]
    rw [ih]
    simp only [FixedCardinalityBits.draw,FixedCardinalityLaw.remaining,List.ofFn_succ,
      Fin.cons_zero,Fin.cons_succ]
    rfl

/-- The polynomial list program has exactly the proved sequential
finite-word semantics, including empty populations. -/
theorem drawWords_ofFn (B n k : ℕ) (words : Fin n → Fin B → Bool) :
    drawWords ((n,k),List.ofFn (fun i => List.ofFn (words i)))=
      List.ofFn (FixedCardinalityBits.draw B n k words) := by
  rw [drawWords_eq]
  exact sampleWords_ofFn B n k words

end
end ContingencyTables.FixedCardinalityProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FixedCardinalityFlat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A flat-word program for a local initial subset

The first B bits select the size. The remaining word is partitioned
into B-bit inclusion rows, so the input list bounds the number of loop
iterations even on malformed inputs.
-/

namespace ContingencyTables.FixedCardinalityProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms

noncomputable section
open FairBits FixedCardinalityBits FixedCardinalityMixture

lemma splitWord_append (B L : ℕ) (bits : Fin (B+L) → Bool) :
    List.ofFn bits=List.ofFn (splitWordEquiv B L bits).1++List.ofFn (splitWordEquiv B L bits).2 := by
  have hfirst : (splitWordEquiv B L bits).1=fun i => bits (Fin.castAdd L i) := by
    funext i
    apply congrArg bits
    apply Fin.ext
    rfl
  have hsecond : (splitWordEquiv B L bits).2=fun i => bits (Fin.natAdd B i) := by
    funext i
    apply congrArg bits
    apply Fin.ext
    rfl
  rw [hfirst,hsecond]
  exact List.ofFn_add (f := bits)

lemma splitWord_take (B L : ℕ) (bits : Fin (B+L) → Bool) :
    (List.ofFn bits).take B=List.ofFn (splitWordEquiv B L bits).1 := by
  rw [splitWord_append]
  simp

lemma splitWord_drop (B L : ℕ) (bits : Fin (B+L) → Bool) :
    (List.ofFn bits).drop B=List.ofFn (splitWordEquiv B L bits).2 := by
  rw [splitWord_append]
  simp

private theorem subsetCode_ofFn_raw (B n : ℕ) (hB : 0<B)
    (bits : Fin (B+n*B) → Bool) :
    subsetCode ((n,B),List.ofFn bits)=List.ofFn (vectorDraw B n bits) := by
  unfold subsetCode
  dsimp only
  rw [splitWord_take,splitWord_drop,scaledWordValue_ofFn (n+1) B (Nat.succ_pos n)]
  rw [wordChunks_ofFn hB,drawWords_ofFn]
  rfl

/-- Every local subset output bit agrees with the finite-word draw
with the sequential subset law. -/
theorem subsetCode_ofFn (B n : ℕ) (hB : 0<B)
    (bits : Fin (drawBits B n) → Bool) :
    subsetCode ((n,B),List.ofFn bits)=List.ofFn (vectorDraw B n bits) :=
  subsetCode_ofFn_raw B n hB bits

end
end ContingencyTables.FixedCardinalityProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_InitialChoiceProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial independent-cell initialization program

The capacities are a supplied list. A polynomial index scan extracts
each disjoint variable-width word block and runs the local subset
program. The resulting rows are exactly the independent cell choices
in the initial finite-word law.
-/

namespace ContingencyTables.InitialChoiceProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open DensePrograms FixedCardinalityProgram

noncomputable section
open FixedCardinalityMixture InitialFactorialBits
open scoped BigOperators

lemma widths_ofFn {q : ℕ} (b : Fin q → ℕ) (B : ℕ) :
    widths (List.ofFn b,B)=List.ofFn (fun i => drawBits B (b i)) := by
  unfold widths
  rw [List.map_ofFn]
  rfl

theorem cellCode_ofFn {q : ℕ} (b : Fin q → ℕ) (B : ℕ) (hB : 0<B)
    (bits : Fin (bitCount b B) → Bool) (i : Fin q) :
    cellCode (((List.ofFn b,B),List.ofFn bits),i.val)=
      List.ofFn (FixedCardinalityMixture.vectorDraw B (b i) (wordEquiv b B bits i)) := by
  unfold cellCode
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,dite_true,
    Option.getD_some,Fin.eta,widths_ofFn]
  have hd := dependentChunk_ofFn (fun i => drawBits B (b i)) bits i
  have he := congrArg (fun block : List Bool => subsetCode ((b i,B),block)) hd
  exact he.trans (subsetCode_ofFn B (b i) hB (wordEquiv b B bits i))

/-- The executable product of cell programs gives exactly the Boolean
rows whose support is the initial independent choice vector. -/
theorem choiceCode_ofFn {q : ℕ} (b : Fin q → ℕ) (B : ℕ) (hB : 0<B)
    (bits : Fin (bitCount b B) → Bool) :
    choiceCode ((List.ofFn b,B),List.ofFn bits)=
      List.ofFn (fun i => List.ofFn (vectorDraw B (b i) (wordEquiv b B bits i))) := by
  apply List.ext_getElem
  · simp only [choiceCode,indices,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    have hiq : i<q := by
      simpa only [choiceCode,indices,List.length_map,List.length_range,List.length_ofFn] using hi
    simp only [choiceCode,indices,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact cellCode_ofFn b B hB bits ⟨i,hiq⟩

end
end ContingencyTables.InitialChoiceProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CanonicalInitialEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical paired-label order for the initial binary program

The order is the explicit list of cells, then their copies, then the
two sides of each pair. The code is obtained directly from the sampled
Boolean rows, so no enumeration of the set-valued state space occurs.
-/

namespace ContingencyTables.CanonicalInitialEncoding

open MatchingFPRAS MatchingFPRAS.TreeTyped
open CommonBasesFPRAS InitialTransversals FixedCardinalityMixture InitialFactorialBits
open scoped BigOperators Classical

noncomputable section
variable {q : ℕ} (b : Fin q → ℕ)

lemma coordinateOrder : List.ofFn (coordinateEquiv b).symm=pairOrder b := by
  change List.ofFn (pairOrder b).get=pairOrder b
  exact List.ofFn_get (pairOrder b)

lemma encodeSet_eq_map (S : Set (Copy b×Bool)) :
    CompanionArithmeticProposal.encodeSet (coordinateEquiv b) S=
      (pairOrder b).map (fun p => if p∈S then 1 else 0) := by
  have h := congrArg (List.map (fun p => if p∈S then (1:ℕ) else 0)) (coordinateOrder b)
  rw [List.map_ofFn] at h
  exact h

lemma pairedCode_eq_map (v : ∀ i,Fin (b i) → Bool) :
    pairedCode (List.ofFn (fun i => List.ofFn (v i)))=
      (pairOrder b).map (fun p => if p∈encode b (fun i => subsetEquiv (b i) (v i)) then 1 else 0) := by
  simp only [pairedCode,pairOrder,copyOrder,List.sigma,List.product,List.ofFn_eq_map,
    List.flatten_eq_flatMap,List.flatMap_map,List.flatMap_assoc,List.map_flatMap,List.map_map]
  apply List.flatMap_congr
  intro i _
  simp only [id_eq,List.flatMap_map,Function.comp_def]
  apply List.flatMap_congr
  intro k _
  cases hv : v i k <;>
    simp [pairValue,subsetEquiv,hv]

/-- The explicit paired list order gives the same encoded set as the
semantic local choices, including cells of capacity zero. -/
theorem pairedCode_encode (v : ∀ i,Fin (b i) → Bool) :
    pairedCode (List.ofFn (fun i => List.ofFn (v i)))=
      CompanionArithmeticProposal.encodeSet (coordinateEquiv b)
        (encode b (fun i => subsetEquiv (b i) (v i))) := by
  rw [encodeSet_eq_map]
  exact pairedCode_eq_map b v

theorem initialCode_ofFn (B : ℕ) (hB : 0<B) (bits : Fin (bitCount b B) → Bool) :
    initialCode ((List.ofFn b,B),List.ofFn bits)=
      CompanionArithmeticProposal.encodeSet (coordinateEquiv b) (encode b (drawChoices b B bits)) := by
  unfold initialCode
  rw [InitialChoiceProgram.choiceCode_ofFn b B hB bits]
  exact pairedCode_encode b (fun i => FixedCardinalityMixture.vectorDraw B (b i) (wordEquiv b B bits i))

end
end ContingencyTables.CanonicalInitialEncoding

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCellCatalogProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the companion's retained small-cell capacities

The program scans the rectangular cell list determined by the two
margin-list lengths, then tests the binary cell bound against W. It
does not enumerate up to the numeric value of a capacity.
-/

namespace ContingencyTables.CompanionCellCatalog

open MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms

noncomputable section
open CompanionFactorialApplication
open scoped Classical
variable {m n : ℕ}

lemma capacities_eq (A : Instance (Fin m) (Fin n)) :
    capacities (input A)=List.ofFn (fun i => A.b ((cellEquiv A) i).val.1 ((cellEquiv A) i).val.2) := by
  apply List.ext_getElem
  · simp only [capacities,List.length_map,List.length_ofFn]
  · intro i hi hj
    have hi' : i<(catalog (input A)).length := by simpa only [List.length_ofFn] using hj
    simp only [capacities,List.getElem_map,List.getElem_ofFn]
    have he := catalogCell_coordinates A ⟨i,hi'⟩
    change entry (input A,(catalog (input A))[i]'hi')=
      A.b (catalogCell A ⟨i,hi'⟩).val.1 (catalogCell A ⟨i,hi'⟩).val.2
    rw [←he]
    exact entry_input A _ _

end
end ContingencyTables.CompanionCellCatalog

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionComputedInitial
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Initialization from the computed small-cell catalog

The proof-level equivalence follows the actual catalog program. It is
used only to identify the output of the binary list initializer with a
paired transversal and to transfer its distributional error bound.
-/

namespace ContingencyTables.CompanionComputedInitial

open MatchingFPRAS.TreeTyped CompanionFactorialApplication
open InitialTransversals InitialFactorialBits CompanionInitialDraw
open FirstSuccess ResidualMixture TwoLiftStates CommonBasesFPRAS
open CompanionArithmeticProposal
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (A : Instance (Fin m) (Fin n))

lemma encodeSet_reindex (S : Set (Labels A×Bool)) :
    encodeSet (coordinateOrder A) S=
      encodeSet (CanonicalInitialEncoding.coordinateEquiv (capacities A))
        ((pairOrder A).symm ⁻¹' S) := rfl

lemma draw_preimage (B : ℕ) (bits : Fin (wordLength A B) → Bool) :
    (pairOrder A).symm ⁻¹' (initialDraw A B bits).val.val=
      encode (capacities A) (drawChoices (capacities A) B bits) := by
  ext p
  rcases p with ⟨⟨i,k⟩,side⟩
  have hc := Equiv.piCongrLeft'_symm_apply_apply
    (fun s : SmallCell A => Finset (Fin (A.b s.val.1 s.val.2)))
    (cellOrder A) (drawChoices (capacities A) B bits) i
  cases side
  · change k∈(choiceEquiv (fun s : SmallCell A => A.b s.val.1 s.val.2)
      (cellOrder A) (drawChoices (capacities A) B bits)) ((cellOrder A).symm i) ↔
        k∈drawChoices (capacities A) B bits i
    exact Iff.of_eq (congrArg (fun S => k∈S) hc)
  · change k∉(choiceEquiv (fun s : SmallCell A => A.b s.val.1 s.val.2)
      (cellOrder A) (drawChoices (capacities A) B bits)) ((cellOrder A).symm i) ↔
        k∉drawChoices (capacities A) B bits i
    exact Iff.of_eq (congrArg (fun S => k∉S) hc)

/-- The complete program computes the semantic initializer with the
coordinate order recovered from the program's own catalog. -/
theorem initialProgram_eq (B : ℕ) (hB : 0<B) (bits : Fin (wordLength A B) → Bool) :
    initialProgram ((CompanionCellCatalog.input A,B),List.ofFn bits)=
      encodeSet (coordinateOrder A) (initialDraw A B bits).val.val := by
  unfold initialProgram
  rw [CompanionCellCatalog.capacities_eq]
  rw [encodeSet_reindex,draw_preimage]
  exact CanonicalInitialEncoding.initialCode_ofFn (capacities A) B hB bits

end
end ContingencyTables.CompanionComputedInitial

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PairedCatalogProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing paired-coordinate metadata from a binary profile

Consecutive coordinates are paired by the bounded list scan
(0,1),(2,3),.... This is the exact metadata of the canonical paired-label
order, rather than a catalog supplied as an external oracle.
-/

namespace ContingencyTables.PairedCatalogProgram

open MatchingFPRAS.TreeTyped ProfilePrograms

lemma pairList_product {α : Type*} (xs : List α) : pairList xs=xs.product [false,true] := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change (a,false)::(a,true)::pairList xs=(a,false)::(a,true)::xs.product [false,true]
    rw [ih]

lemma pairList_get_even {α : Type*} (xs : List α) (i : ℕ) (hi : i<xs.length) :
    (pairList xs)[2*i]'(by rw [pairList_length]; omega)=(xs[i],false) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [pairList,Nat.mul_succ,List.getElem_cons_succ] using
        ih i (Nat.lt_of_succ_lt_succ hi)

lemma pairList_get_odd {α : Type*} (xs : List α) (i : ℕ) (hi : i<xs.length) :
    (pairList xs)[2*i+1]'(by rw [pairList_length]; omega)=(xs[i],true) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [pairList,Nat.mul_succ,List.getElem_cons_succ,Nat.add_assoc] using
        ih i (Nat.lt_of_succ_lt_succ hi)

noncomputable section
open CanonicalInitialEncoding InitialTransversals CompanionArithmeticProposal
open scoped Classical
variable {q : ℕ} (b : Fin q → ℕ)

lemma coordinate_false (i : Fin (copyOrder b).length) :
    (CanonicalInitialEncoding.coordinateEquiv b (labelOrder b i,false)).val=2*i.val := by
  have hl : (pairOrder b).length=2*(copyOrder b).length := by
    change ((copyOrder b).product [false,true]).length=2*(copyOrder b).length
    rw [←pairList_product]
    exact pairList_length _
  let k : Fin (pairOrder b).length := ⟨2*i.val,by rw [hl]; omega⟩
  have hk : (CanonicalInitialEncoding.coordinateEquiv b).symm k=(labelOrder b i,false) := by
    change (pairOrder b)[k.val]=((copyOrder b)[i.val],false)
    simpa only [pairOrder,←pairList_product,k] using pairList_get_even (copyOrder b) i.val i.isLt
  have he := congrArg (fun a => (CanonicalInitialEncoding.coordinateEquiv b a).val) hk
  simpa only [Equiv.apply_symm_apply,k] using he.symm

lemma coordinate_true (i : Fin (copyOrder b).length) :
    (CanonicalInitialEncoding.coordinateEquiv b (labelOrder b i,true)).val=2*i.val+1 := by
  have hl : (pairOrder b).length=2*(copyOrder b).length := by
    change ((copyOrder b).product [false,true]).length=2*(copyOrder b).length
    rw [←pairList_product]
    exact pairList_length _
  let k : Fin (pairOrder b).length := ⟨2*i.val+1,by rw [hl]; omega⟩
  have hk : (CanonicalInitialEncoding.coordinateEquiv b).symm k=(labelOrder b i,true) := by
    change (pairOrder b)[k.val]=((copyOrder b)[i.val],true)
    simpa only [pairOrder,←pairList_product,k] using pairList_get_odd (copyOrder b) i.val i.isLt
  have he := congrArg (fun a => (CanonicalInitialEncoding.coordinateEquiv b a).val) hk
  simpa only [Equiv.apply_symm_apply,k] using he.symm

/-- Every state encoded in the canonical order has exactly the pair
catalog computed by the polynomial consecutive-coordinate scan. -/
theorem catalog_encode (S : Set (Copy b×Bool)) :
    catalog (encodeSet (CanonicalInitialEncoding.coordinateEquiv b) S)=
      List.ofFn (fun i : Fin (copyOrder b).length =>
        ((CanonicalInitialEncoding.coordinateEquiv b (labelOrder b i,false)).val,
          (CanonicalInitialEncoding.coordinateEquiv b (labelOrder b i,true)).val)) := by
  have hl : (pairOrder b).length=2*(copyOrder b).length := by
    change ((copyOrder b).product [false,true]).length=2*(copyOrder b).length
    rw [←pairList_product]
    exact pairList_length _
  simp only [catalog,encodeSet,List.length_ofFn,hl]
  rw [Nat.mul_div_cancel_left _ (by decide : 0<2)]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,indexPair,
      coordinate_false,coordinate_true]

end
end ContingencyTables.PairedCatalogProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMultiplierMatrixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full multiplier update and abort test as list programs

Only the polynomial list of labelled pairs is traversed. Every matrix
entry is updated from the actual plain and defect counts of the stored
trajectory. The count check includes every off-diagonal labelled type.
-/

namespace ContingencyTables.CompanionMultiplierMatrixProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open CompanionPhaseCounts CompanionMultiplierProgram CompanionOrderedProposal CompanionTraceProgram
open CompanionFactorialApplication CompanionArithmeticProposal CompanionRationalUpdates
open CommonBasesFPRAS
open scoped Classical

noncomputable section
open TwoLiftStates
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {p m : ℕ} (g : Fin p ≃ Labels A)
  (e : (Labels A×Bool) ≃ Fin m)

lemma readEntry_code (w : Fin p → Fin p → TreeFraction.Fraction) (i j : Fin p) :
    readEntry (matrixCode w,(i.val,j.val))=w i j := by
  simp only [readEntry,matrixCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    i.isLt,j.isLt,dite_true,Option.getD_some,Fin.eta]

end
end ContingencyTables.CompanionMultiplierMatrixProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMultiplierAgreement
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Only canonical pair entries affect the executed chain

The finite matrix stores one entry per pair of labels. Values of the
mathematical multiplier on arbitrary noncanonical coordinate pairs
do not affect any weight call, acceptance decision, or capped return.
-/

namespace ContingencyTables.CompanionMultiplierAgreement

open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionOracleDensity CompanionWeightOracle TwoLiftStates GridBoundary
open CompanionBooleanPhase (State stepBits)
open scoped Classical

noncomputable section

lemma rationalMultiplier_congr {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (gs : List (Γ × Γ)) (w w' : (Γ × Γ) → (Γ × Γ) → ℚ)
    (hw : ∀ p ∈ gs, ∀ q ∈ gs, w p q=w' p q) (S : Set Γ) :
    rationalMultiplier gs w S=rationalMultiplier gs w' S := by
  unfold rationalMultiplier
  split_ifs with h
  · exact hw _ h.choose_spec.choose_spec.1 _ h.choose_spec.choose_spec.2.1
  · rfl

variable {I J : Type} [Fintype I] [Fintype J]

lemma agree_on_pairs (A : Instance I J) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') :
    ∀ p ∈ (pairs : List (Pair A)), ∀ q ∈ (pairs : List (Pair A)), w p q=w' p q := by
  intro p hp q hq
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hp
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hq
  exact hw a b

lemma multiplier_eq (A : Instance I J) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') (S : Set (Labels A × Bool)) :
    rationalMultiplier pairs w S=rationalMultiplier pairs w' S :=
  rationalMultiplier_congr pairs w w' (agree_on_pairs A w w' hw) S

lemma evaluatedWeight_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K j : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') (S : Set (Labels A × Bool)) (bits : WeightWord A C K j xi) :
    RootedOracleAcceptance.evaluatedWeight A R C K j hK hW xi v w S bits=
      RootedOracleAcceptance.evaluatedWeight A R C K j hK hW xi v w' S bits := by
  unfold RootedOracleAcceptance.evaluatedWeight
  rw [multiplier_eq A w w' hw]

lemma acceptance_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K j : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') :
    RootedOracleAcceptance.acceptance A R C K j hK hW xi v w=
      RootedOracleAcceptance.acceptance A R C K j hK hW xi v w' := by
  funext S T bits
  unfold RootedOracleAcceptance.acceptance
  rw [evaluatedWeight_eq A R C K j hK hW xi v w w' hw,
    evaluatedWeight_eq A R C K j hK hW xi v w w' hw]

lemma arithmeticFinish_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K j k : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') :
    RootedArithmeticStep.finish A R C K j k hK hW xi v w=
      RootedArithmeticStep.finish A R C K j k hK hW xi v w' := by
  funext S U bits
  unfold RootedArithmeticStep.finish
  rw [acceptance_eq A R C K j hK hW xi v w w' hw]

lemma arithmeticStep_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K j k : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') :
    RootedArithmeticStep.step A R C K j k hK hW xi v w=
      RootedArithmeticStep.step A R C K j k hK hW xi v w' := by
  funext S bits
  unfold RootedArithmeticStep.step
  rw [arithmeticFinish_eq A R C K j k hK hW xi v w w' hw]

lemma recordedWalk_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K j k N n : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') :
    RootedArithmeticStep.recordedWalk A R C K j k N n hK hW xi v w=
      RootedArithmeticStep.recordedWalk A R C K j k N n hK hW xi v w' := by
  funext S bits
  unfold RootedArithmeticStep.recordedWalk
  rw [arithmeticStep_eq A R C K j k hK hW xi v w w' hw]

lemma return_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K j k n : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') :
    RootedCappedReturn.returnWordDefault A R C K j k n hK hW xi v w=
      RootedCappedReturn.returnWordDefault A R C K j k n hK hW xi v w' := by
  funext S bits
  unfold RootedCappedReturn.returnWordDefault RootedTraceWords.returnWord
  rw [recordedWalk_eq A R C K j k (n+1) (n+1) hK hW xi v w w' hw]

lemma returns_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K j k n t : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') :
    RootedReturnWords.booleanReturns A R C K j k n t hK hW xi v w=
      RootedReturnWords.booleanReturns A R C K j k n t hK hW xi v w' := by
  funext S bits
  unfold RootedReturnWords.booleanReturns
  rw [return_eq A R C K j k n hK hW xi v w w' hw]

end
end ContingencyTables.CompanionMultiplierAgreement

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRestartAgreement
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restart histories depend only on stored canonical pair entries -/
namespace ContingencyTables.FirstSuccess
open scoped Classical
noncomputable section

theorem varyingWalk_congr_prefix {X : Type*} [Fintype X] [DecidableEq X]
    (width : ℕ → ℕ)
    (f g : (i : ℕ) → X → (Fin (width i) → Bool) → X)
    (x : X) (n : ℕ) (h : ∀ i,i < n → f i=g i)
    (bits : VaryingWords width n) :
    varyingWalk width f x n bits=varyingWalk width g x n bits := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [varyingWalk]
    rw [ih (fun i hi => h i (by omega)) (Fin.init bits),h n (by omega)]

end
end ContingencyTables.FirstSuccess

namespace ContingencyTables.CompanionMultiplierAgreement
open CompanionFactorialApplication CompanionRationalUpdates CompanionOracleDensity
open CompanionBooleanPhase (State stepBits)
open TwoLiftStates GridBoundary
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

theorem observedStates_eq (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K j k N : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (w w' : Pair A → Pair A → ℚ)
    (hw : Agree A w w') :
    RootedPhaseExperiment.observedStates A R C K j k N hK hW xi v w=
      RootedPhaseExperiment.observedStates A R C K j k N hK hW xi v w' := by
  funext S bits i
  unfold RootedPhaseExperiment.observedStates
  rw [recordedWalk_eq A R C K j k N N hK hW xi v w w' hw]

end
end ContingencyTables.CompanionMultiplierAgreement

namespace ContingencyTables.RootedRestartWords
open CommonBasesFPRAS CompanionFactorialApplication CompanionRationalUpdates
open CompanionOracleDensity CompanionWeightOracle TwoLiftStates GridBoundary FirstSuccess
open scoped BigOperators Classical
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

theorem stages_agree (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L k cap j : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K)
    (w w' : ℕ → Pair A → Pair A → ℚ)
    (hw : ∀ i,i < j → CompanionMultiplierAgreement.Agree A (w (i+1)) (w' (i+1)))
    (S : PlainIndex (pairs : List (Pair A)))
    (bits : Fin (∑ i : Fin j,stageWidth A C K H L k cap xi i.val) → Bool) :
    stages A R C K H L k cap j hK hW xi v w S bits=
      stages A R C K H L k cap j hK hW xi v w' S bits := by
  unfold stages
  apply varyingWalk_congr_prefix
  intro i hi
  exact CompanionMultiplierAgreement.returns_eq A R C K (i+1) k cap
    (CompanionTargetMixing.restartTime A H L) hK hW xi v (w (i+1)) (w' (i+1)) (hw i hi)

theorem initializedStages_agree (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (C K H L k cap h j : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K)
    (w w' : ℕ → Pair A → Pair A → ℚ)
    (hw : ∀ i,i < j → CompanionMultiplierAgreement.Agree A (w (i+1)) (w' (i+1)))
    (bits : Fin (initialStageBits A C K H L k cap h j xi) → Bool) :
    initializedStages A R C K H L k cap h j hK hW xi v w bits=
      initializedStages A R C K H L k cap h j hK hW xi v w' bits := by
  unfold initializedStages
  exact stages_agree A R C K H L k cap j hK hW xi v w w' hw _ _

end
end ContingencyTables.RootedRestartWords

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCanonicalHistory
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical multiplier entries determine the projected phase history

The extension uses only the first label of a raw coordinate pair. Its values
away from canonical pairs need not match the original multiplier.
-/
namespace ContingencyTables.CompanionCanonicalHistory
open CompanionFactorialApplication CompanionRationalUpdates CompanionMultiplierAgreement
open CommonBasesFPRAS TwoLiftStates GridBoundary
open CompanionPhaseWords (Stored phaseBits)
open scoped Classical
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {p : ℕ} (g : Fin p ≃ Labels A)

theorem project_eq_iff (s t : Stored A) :
    project A g s=project A g t ↔ Agree A s.multiplier t.multiplier ∧ s.estimate=t.estimate := by
  constructor
  · intro h
    constructor
    · intro a b
      have he := congrFun (congrFun (congrArg Prod.fst h) (g.symm a)) (g.symm b)
      simpa only [project,CompanionPhaseFinishProgram.storedView,Equiv.apply_symm_apply] using he
    · exact congrArg Prod.snd h
  · rintro ⟨hw,he⟩
    apply Prod.ext
    · funext i j
      exact hw (g i) (g j)
    · exact he

theorem learn_agree (w w' : Pair A→Pair A→ℚ) (hw : Agree A w w')
    (states : List (Set (Labels A×Bool))) :
    Agree A (rationalLearn pairs w states) (rationalLearn pairs w' states) := by
  intro a b
  by_cases h : pair a∈(pairs : List (Pair A)) ∧ pair b∈(pairs : List (Pair A)) ∧ pair a≠pair b
  · simp only [rationalLearn,h,hw a b]
  · simp only [rationalLearn,h,ite_false,hw a b]

theorem update_project_eq (R : RootedCompletion.Selection A.T) (C K j N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (CompanionOracleDensity.dimension A)) K)
    (s t : Stored A) (h : project A g s=project A g t)
    (states : Fin N→Set (Labels A×Bool)) (bits : Fin (phaseBits A C K j N xi)→Bool) :
    (RootedPhaseWords.update A R C K j N hK hW xi v s states bits).map (project A g)=
      (RootedPhaseWords.update A R C K j N hK hW xi v t states bits).map (project A g) := by
  obtain ⟨hw,he⟩ := (project_eq_iff A g s t).mp h
  unfold RootedPhaseWords.update
  split_ifs
  · simp only [Option.map_some]
    apply congrArg Option.some
    apply (project_eq_iff A g _ _).mpr
    exact ⟨learn_agree A s.multiplier t.multiplier hw _,congrArg (fun e => e*_) he⟩
  · rfl

theorem trial_project_eq (R : RootedCompletion.Selection A.T) (C K j k N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (CompanionOracleDensity.dimension A)) K)
    (s t : Stored A) (h : project A g s=project A g t)
    (S : CompanionBooleanPhase.State A) (bits : RootedPhaseTrial.TrialWords A C K j k N xi) :
    (RootedPhaseTrial.trial A R C K j k N hK hW xi v s S bits).map (project A g)=
      (RootedPhaseTrial.trial A R C K j k N hK hW xi v t S bits).map (project A g) := by
  have hw := ((project_eq_iff A g s t).mp h).1
  unfold RootedPhaseTrial.trial
  rw [observedStates_eq A R C K j k N hK hW xi v s.multiplier t.multiplier hw]
  exact update_project_eq A g R C K j (N+1) hK hW xi v s t h _ _

theorem restart_project_eq (R : RootedCompletion.Selection A.T)
    (C K H L j k n N h : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (CompanionOracleDensity.dimension A)) K)
    (w w' : ℕ→Pair A→Pair A→ℚ) (e e' : ℚ)
    (hw : ∀ i,i ≤ j → Agree A (w i) (w' i)) (he : e=e')
    (bits : RootedRestartTrial.Words A C K H L j k n N h xi) :
    (RootedRestartTrial.run A R C K H L j k n N h hK hW xi v w e bits).map (project A g)=
      (RootedRestartTrial.run A R C K H L j k n N h hK hW xi v w' e' bits).map (project A g) := by
  have hi := RootedRestartWords.initializedStages_agree A R C K H L k n h j hK hW xi v w w'
    (fun i hi => hw (i+1) (by omega)) bits.1
  unfold RootedRestartTrial.run
  rw [hi]
  exact trial_project_eq A g R C K j k N hK hW xi v ⟨w j,e⟩ ⟨w' j,e'⟩
    ((project_eq_iff A g _ _).mpr ⟨hw j le_rfl,he⟩) _ _

theorem lookup_project_eq (history history' : List (Stored A))
    (h : history.map (project A g)=history'.map (project A g)) (i : ℕ) :
    project A g (RootedStoredHistory.lookup A history i)=
      project A g (RootedStoredHistory.lookup A history' i) := by
  cases i with
  | zero => rfl
  | succ i =>
    have he := congrArg (fun xs : List (Canonical (p := p)) =>
      xs.getD i (project A g (RootedStoredEstimate.initialStored A))) h
    simpa only [RootedStoredHistory.lookup,List.getD_map] using he

private theorem project_getD (a b : Option (Stored A)) (s t : Stored A)
    (h : a.map (project A g)=b.map (project A g)) (he : project A g s=project A g t) :
    project A g (a.getD s)=project A g (b.getD t) := by
  cases a <;> cases b <;> simp_all

theorem step_project_eq (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (history history' : List (Stored A))
    (hh : history.map (project A g)=history'.map (project A g)) (bits : RootedPhaseHistory.Word A s) :
    project A g (RootedPhaseHistory.step A R s history bits)=
      project A g (RootedPhaseHistory.step A R s history' bits) := by
  have hlen : history.length=history'.length := by
    simpa only [List.length_map] using congrArg List.length hh
  have hold := lookup_project_eq A g history history' hh history'.length
  dsimp only [RootedPhaseHistory.step]
  rw [hlen]
  split_ifs with hj
  · apply project_getD A g _ _ _ _ _ hold
    apply restart_project_eq A g R s.C s.K s.H s.L history'.length s.k s.n s.N s.h
      s.hK s.hW s.xi s.v
    · intro i _
      exact ((project_eq_iff A g _ _).mp (lookup_project_eq A g history history' hh i)).1
    · exact ((project_eq_iff A g _ _).mp hold).2
  · exact hold

theorem step_project (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (history : List (Stored A)) (bits : RootedPhaseHistory.Word A s) :
    project A g (RootedPhaseHistory.step A R s history bits)=
      canonicalStep A g R s (history.map (project A g)) bits := by
  apply step_project_eq A g R s history ((history.map (project A g)).map (extend A g))
  simp only [List.map_map,Function.comp_def,project_extend]

end
end ContingencyTables.CompanionCanonicalHistory

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteObservableTransport
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact transport of finite experiments with rational outputs

Output values need not form a finite type. Equality against every real
observable is preserved by deterministic postprocessing and by the
independent arrays used in the counting estimator.
-/

namespace ContingencyTables.FiniteObservableTransport

open CommonBasesFPRAS
open scoped Classical

noncomputable section
variable {X Y U V Z W : Type*}
variable [Fintype X] [Fintype Y] [Fintype U] [Fintype V]

lemma SameLaw.map {f : X → Z} {g : Y → Z} (h : SameLaw f g) (F : Z → W) :
    SameLaw (fun x => F (f x)) (fun y => F (g y)) := by
  intro phi
  exact h (fun z => phi (F z))

lemma SameLaw.prod {f : X → Z} {g : Y → Z} {a : U → W} {b : V → W}
    (hfg : SameLaw f g) (hab : SameLaw a b) :
    SameLaw (fun x : X×U => (f x.1,a x.2)) (fun y : Y×V => (g y.1,b y.2)) := by
  intro phi
  rw [uniformAverage_prod,uniformAverage_prod]
  have hinner (x : X) :
      uniformAverage (fun u : U => phi (f x,a u))=
        uniformAverage (fun v : V => phi (f x,b v)) :=
    hab (fun w => phi (f x,w))
  simp_rw [hinner]
  exact hfg (fun z => uniformAverage (fun v : V => phi (z,b v)))

end
end ContingencyTables.FiniteObservableTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCanonicalHistoryLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete source estimator factors through canonical stored entries -/
namespace ContingencyTables.CompanionCanonicalHistory
open CompanionFactorialApplication CommonBasesFPRAS GridBoundary FiniteObservableTransport
open CompanionPhaseWords (Stored)
open scoped Classical
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {p : ℕ} (g : Fin p ≃ Labels A)

lemma advance_project (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (history : List (Stored A)) (bits : RootedPhaseHistory.Word A s) :
    (sourceAdvance A R s history bits).map (project A g)=
      canonicalAdvance A g R s (history.map (project A g)) bits := by
  simp only [sourceAdvance,canonicalAdvance,List.map_append,List.map_singleton,step_project]

lemma fold_project (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (words : List (RootedPhaseHistory.Word A s)) (history : List (Stored A)) :
    (words.foldl (sourceAdvance A R s) history).map (project A g)=
      words.foldl (canonicalAdvance A g R s) (history.map (project A g)) := by
  induction words generalizing history with
  | nil => rfl
  | cons word words ih =>
    rw [List.foldl_cons,List.foldl_cons,ih,advance_project]

theorem decoded_project (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (words : List (RootedPhaseHistory.Word A s)) :
    (RootedPhaseHistory.decoded A R s words).map (project A g)=canonicalDecoded A g R s words :=
  fold_project A g R s words []

lemma lookup_project (history : List (Stored A)) (i : ℕ) :
    project A g (RootedStoredHistory.lookup A history i)=
      canonicalLookup A g (history.map (project A g)) i := by
  cases i with
  | zero => rfl
  | succ i => exact (List.getD_map history (RootedStoredEstimate.initialStored A)
      (project A g)).symm

theorem estimate_project (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (words : Fin s.H→RootedPhaseHistory.Word A s) :
    RootedCountingWords.estimate A R s words=canonicalEstimate A g R s words := by
  change (project A g (RootedStoredHistory.lookup A
    (RootedPhaseHistory.decoded A R s (List.ofFn words)) s.H)).2=_
  rw [lookup_project,decoded_project]
  rfl

end
end ContingencyTables.CompanionCanonicalHistory

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPhaseSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit scalar schedules for the adaptive counting phases

Every precision and sample length below is a rational or natural arithmetic
expression. In particular the dyadic exponents use a polynomial reciprocal
allowance, so no real logarithm is evaluated by the algorithm.
-/

namespace ContingencyTables.CountingPhaseSchedule

open scoped BigOperators

lemma precision_pos (H tau N n : ℕ) (eta : ℚ) : 0 < precision H tau N n eta := by
  unfold precision
  omega

lemma noise_pos (H tau N n : ℕ) (eta : ℚ) : 0 < noise H tau N n eta := by
  unfold noise
  exact one_div_pos.mpr (by exact_mod_cast precision_pos H tau N n eta)

end ContingencyTables.CountingPhaseSchedule

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingOracleScheduleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary arithmetic for the counting oracle sample schedule -/

namespace ContingencyTables.CountingOracleScheduleProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma ceiling_val (e : Fraction) : ceiling e=⌈TreeFraction.val e⌉₊ := by
  by_cases h : e.2=0
  · simp only [ceiling,OffsetCountPrograms.ceilQuotient,TreeFraction.val,h,Nat.div_zero,
      Nat.cast_zero,div_zero,Nat.ceil_zero]
  · exact OffsetCountPrograms.ceilQuotient_eq e.1 e.2 (Nat.pos_of_ne_zero h)

lemma natural_val (n : ℕ) : TreeFraction.val (natural n)=(n:ℚ) := by
  simp only [natural,TreeFraction.val,Nat.cast_one,div_one]

lemma sampleCount_val (j : ℕ) (delta failure : Fraction) :
    sampleCount (j,(delta,failure))=
      CompanionOracleDensity.sampleCount j (TreeFraction.val delta) (TreeFraction.val failure) := by
  rw [sampleCount,ceiling_val,sampleRatio,TreeFraction.div_val,sampleBase,natural_val,
    sampleDenominator,TreeFraction.mul_val,TreeFraction.mul_val]
  unfold CompanionOracleDensity.sampleCount
  congr 1
  push_cast
  ring

lemma offsetAccuracy_val (d : ℕ) (delta : Fraction) :
    offsetAccuracy (d,delta)=⌈4096*(d:ℚ)/TreeFraction.val delta⌉₊ := by
  rw [offsetAccuracy,ceiling_val,offsetRatio,TreeFraction.div_val,offsetBase,natural_val]
  simp only [Nat.cast_mul,Nat.cast_ofNat]


lemma oracleTime_val (M B : ℕ) (theta : Fraction) :
    oracleTime ((M,B),theta)=⌈(M:ℚ)*((B:ℚ)+16/TreeFraction.val theta)⌉₊ := by
  have he : (timeExtra ((M,B),theta)).2 ≠ 0 := by
    exact (TreeFraction.normalize_den_pos _).ne'
  rw [oracleTime,ceiling_val,timeTotal,TreeFraction.add_val _ _ (by change (1:ℕ) ≠ 0; decide) he,
    timeBase,natural_val,timeExtra,TreeFraction.div_val,timeNumerator,natural_val]
  congr 1
  push_cast
  ring

lemma oracleTime_instance {I J : Type} [Fintype I] [Fintype J]
    (A : CompanionFactorialApplication.Instance I J) (C K : ℕ) (theta : Fraction) :
    oracleTime ((2*(10000*A.d^2*K)^2,
      CompanionOracleDensity.rationalHeight A C+A.d*K+2),theta)=
      CompanionOracleDensity.oracleTime A C K 1 (TreeFraction.val theta) := by
  rw [oracleTime_val,CompanionOracleDensity.oracleTime]
  rw [←CountingTerminalSchedule.natCeil_ratCast]
  congr 1
  simp only [CompanionOracleDensity.mixingConstant,CompanionOracleDensity.rationalHeight,
    CompanionOracleDensity.height,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,
    Rat.cast_mul,Rat.cast_add,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_pow]
  ring

end ContingencyTables.CountingOracleScheduleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScalarScheduleProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed arithmetic circuits for the scalar counting schedules

These circuits only read a fixed finite list and perform binary addition
and multiplication. Their syntax describes the fixed program, not a
numeric loop selected by the input.
-/

namespace ContingencyTables.ScalarScheduleProgram
open MatchingFPRAS.TreeTyped

lemma Expr.eval_pow (a : Expr) (n : ℕ) (xs : List ℕ) :
    (a.pow n).eval xs=(a.eval xs)^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Expr.pow,Expr.eval,ih,pow_succ]


@[simp] lemma Expr.eval_power (a : Expr) (n : ℕ) (xs : List ℕ) :
    (a^n).eval xs=(a.eval xs)^n := Expr.eval_pow a n xs


end ContingencyTables.ScalarScheduleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPhaseScalarProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed arithmetic circuits for the phase scalar controls -/

namespace ContingencyTables.CountingPhaseScalarProgram
open ScalarScheduleProgram
open MatchingFPRAS.TreeTyped

lemma observationNumerator_value (P W H T N R L : ℕ) :
    observationNumerator.eval [P,W,H,T,N,R,L]=
      1024*(H+1)*CountingPhaseSchedule.observationCoefficient P W := by
  simp [observationNumerator,observable,p,w,h,Expr.eval,
    CountingPhaseSchedule.observationCoefficient,CountingPhaseSchedule.observable]

lemma precisionBase_value (P W H T N R L : ℕ) :
    precisionBase.eval [P,W,H,T,N,R,L]=
      1024*(H+1)*CountingPhaseSchedule.noiseCoefficient H T N R+1 := by
  simp [precisionBase,h,tau,observations,returns,Expr.eval,CountingPhaseSchedule.noiseCoefficient]

lemma initialPrecision_value (P W H T N R L : ℕ) :
    initialPrecision.eval [P,W,H,T,N,R,L]=CountingPhaseSchedule.initialPrecision H := by
  simp [initialPrecision,h,Expr.eval,CountingPhaseSchedule.initialPrecision]

end ContingencyTables.CountingPhaseScalarProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPhaseParametersProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable rational controls for the adaptive counting phases -/

namespace ContingencyTables.CountingPhaseParametersProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
open CountingOracleScheduleProgram ScalarScheduleProgram

lemma tolerance_val (P W H T N R L : ℕ) (e : Fraction) :
    TreeFraction.val (tolerance ([P,W,H,T,N,R,L],e))=
      CountingPhaseSchedule.tolerance H (TreeFraction.val e) := by
  rw [tolerance,TreeFraction.div_val,scalarFraction,natural_val]
  simp [scalar,toleranceDenominator,CountingPhaseScalarProgram.h,Expr.eval,
    CountingPhaseSchedule.tolerance]

lemma observations_val (P W H T N R L : ℕ) (e : Fraction) :
    observations ([P,W,H,T,N,R,L],e)=
      CountingPhaseSchedule.observations P W H
        (CountingPhaseSchedule.tolerance H (TreeFraction.val e)) := by
  rw [observations,ceiling_val,observationRatio,TreeFraction.div_val,
    scalarFraction,natural_val,toleranceSquare,TreeFraction.mul_val,tolerance_val]
  change ⌈((CountingPhaseScalarProgram.observationNumerator.eval [P,W,H,T,N,R,L]:ℕ):ℚ)/
    (CountingPhaseSchedule.tolerance H (TreeFraction.val e)*
      CountingPhaseSchedule.tolerance H (TreeFraction.val e))⌉₊+1= _
  rw [CountingPhaseScalarProgram.observationNumerator_value]
  simp only [CountingPhaseSchedule.observations,Nat.cast_mul,Nat.cast_ofNat,
    Nat.cast_add,Nat.cast_one,pow_two]

lemma precision_val (P W H T N R L : ℕ) (e : Fraction) :
    precision ([P,W,H,T,N,R,L],e)=
      CountingPhaseSchedule.precision H T N R
        (CountingPhaseSchedule.tolerance H (TreeFraction.val e)) := by
  rw [precision,reciprocalCeiling,ceiling_val,reciprocalTolerance,TreeFraction.div_val,tolerance_val]
  simp only [TreeFraction.val,Nat.cast_one,div_one]
  change CountingPhaseScalarProgram.precisionBase.eval [P,W,H,T,N,R,L]+
    ⌈1/CountingPhaseSchedule.tolerance H (TreeFraction.val e)⌉₊= _
  rw [CountingPhaseScalarProgram.precisionBase_value]
  simp only [CountingPhaseSchedule.precision,TreeFraction.val]
  omega

lemma noise_val (P W H T N R L : ℕ) (e : Fraction) :
    TreeFraction.val (noise ([P,W,H,T,N,R,L],e))=
      CountingPhaseSchedule.noise H T N R
        (CountingPhaseSchedule.tolerance H (TreeFraction.val e)) := by
  simp only [noise,TreeFraction.val,Nat.cast_one,precision_val,CountingPhaseSchedule.noise]

end ContingencyTables.CountingPhaseParametersProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMetropolisSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The binary dense program realizes the exact finite transition -/

namespace ContingencyTables.DensePrograms
open GridBoundary FairBits
open scoped Classical

noncomputable section

lemma ofFn_split_take {p k : ℕ} (bits : Fin (p+k) → Bool) :
    (List.ofFn bits).take p=List.ofFn ((splitWordEquiv p k bits).1) := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_ofFn,Nat.min_eq_left (Nat.le_add_right p k)]
  · intro i hi hj
    simp only [List.getElem_take,List.getElem_ofFn]
    rfl

lemma ofFn_split_drop {p k : ℕ} (bits : Fin (p+k) → Bool) :
    (List.ofFn bits).drop p=List.ofFn ((splitWordEquiv p k bits).2) := by
  apply List.ext_getElem
  · simp only [List.length_drop,List.length_ofFn,Nat.add_sub_cancel_left]
  · intro i hi hj
    simp only [List.getElem_drop,List.getElem_ofFn]
    apply congrArg bits
    apply Fin.ext
    change p+i=p+i
    rfl

end
end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_NaturalBlockProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded scans of natural-number blocks

Numeric widths select bounded slices of the supplied list. They never
control an allocation, so malformed widths preserve polynomial cost.
-/

namespace ContingencyTables.NaturalBlockProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

lemma block_splitLengths (widths values : List ℕ) (i : ℕ) :
    block ((widths,values),i)=(widths.splitLengths values).getD i [] := by
  induction widths generalizing values i with
  | nil => simp [block,start]
  | cons w ws ih =>
    cases i with
    | zero => simp [block,start,List.splitLengths_cons]
    | succ i =>
      simpa only [block,start,List.take_succ_cons,List.sum_cons,List.getD_cons_succ,
        List.splitLengths_cons,List.drop_drop,Nat.add_comm] using ih (values.drop w) i

theorem blocks_eq_splitLengths (widths values : List ℕ) :
    blocks (widths,values)=widths.splitLengths values := by
  apply List.ext_getElem
  · simp [blocks,indices]
  · intro i hi hj
    have hiw : i < widths.length := by
      simpa only [blocks,indices,List.length_map,List.length_range] using hi
    simp only [blocks,indices,List.getElem_map,List.getElem_range]
    have h := block_splitLengths widths values i
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some] using h

lemma splitLengths_flatten (rows : List (List ℕ)) :
    (rows.map List.length).splitLengths rows.flatten=rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simpa only [List.map_cons,List.flatten_cons,List.splitLengths_cons,
      List.take_left,List.drop_left] using congrArg (List.cons row) ih

/-- A literal list of rows is recovered exactly from its stored row
lengths and its flattened code, including rows of length zero. -/
theorem blocks_flatten (rows : List (List ℕ)) :
    blocks (rows.map List.length,rows.flatten)=rows := by
  rw [blocks_eq_splitLengths,splitLengths_flatten]

end ContingencyTables.NaturalBlockProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PairedProfileProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reading the two cell counts from the actual paired code

The block widths come from the stored capacity list. Each count scans
only supplied code entries and clips them to one, including on malformed
input. No numeric capacity controls an unbounded allocation.
-/

namespace ContingencyTables.PairedProfileProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

lemma interleave_flatMap (xs : List (ℕ × ℕ)) :
    interleave xs=xs.flatMap (fun p => [p.1,p.2]) := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    change p.1 :: p.2 :: interleave xs=p.1 :: p.2 :: xs.flatMap (fun p => [p.1,p.2])
    rw [ih]

end ContingencyTables.PairedProfileProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_PairedProfileSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed paired counts are the manuscript's literal profile -/

namespace ContingencyTables.PairedProfileSemantics

open PairedProfileProgram CanonicalInitialEncoding InitialTransversals
open CompanionArithmeticProposal CompanionFactorialApplication
open scoped BigOperators Classical

noncomputable section

variable {q : ℕ} (b : Fin q → ℕ)

lemma cellRows_lengths (S : Set (Copy b × Bool)) :
    (cellRows b S).map List.length=(List.ofFn b).map width := by
  simp only [cellRows,List.map_ofFn,Function.comp_def,interleave_length,List.length_ofFn,width]

lemma cellRows_flatten (S : Set (Copy b × Bool)) :
    (cellRows b S).flatten=encodeSet (coordinateEquiv b) S := by
  rw [encodeSet_eq_map]
  simp only [cellRows,interleave_flatMap,pairOrder,copyOrder,List.sigma,List.product,
    List.ofFn_eq_map,List.flatten_eq_flatMap,List.flatMap_map,List.map_flatMap,
    List.flatMap_assoc,List.map_map]
  apply List.flatMap_congr
  intro i _
  simp only [id_eq,Function.comp_def]
  apply List.flatMap_congr
  intro k _
  rfl

lemma rows_encode (S : Set (Copy b × Bool)) :
    rows (List.ofFn b,encodeSet (coordinateEquiv b) S)=cellRows b S := by
  rw [rows,←cellRows_lengths b S,←cellRows_flatten b S]
  exact NaturalBlockProgram.blocks_flatten _

end
end ContingencyTables.PairedProfileSemantics

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedBinDrawLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed bin program has the analysed independent law

The execution order is the computed free-cell catalog.  The mathematical
law uses another enumeration.  Dependent word equivalences identify their
independent Boolean inputs, while preserving each physical cell's draw.
-/

namespace ContingencyTables.RootedBinDrawLaw

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity FirstSuccess ResidualMixture FairBits
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

attribute [local instance] OAI.ContingencyTables.RootedBinDrawLaw.freeCellDecidableEq
lemma wordBits_eq (A : Instance (Fin m) (Fin n)) (h : ℕ) :
    wordBits A h=binWordBits A h := by
  unfold wordBits binWordBits
  apply Fintype.sum_equiv (RootedCatalogGrid.coordinateEquiv A)
  intro i
  simp only [RootedCatalogGrid.coordinateEquiv,Equiv.trans_apply,
    Equiv.apply_symm_apply]

end
end ContingencyTables.RootedBinDrawLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorWordLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite-word law of the executed selected-root weight oracle -/

namespace ContingencyTables.RootedEstimatorWordProgram

open MatchingFPRAS CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity RootedEstimatorLayoutProgram CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

lemma scheduledWordWidth (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (delta failure : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    wordWidth (scheduledContext A C K j delta failure z v)=
      estimatorWordBits A C K j delta failure := by
  change j*(sampleCount j delta failure*ratioWidth
    (scheduledContext A C K j delta failure z v))+
    sampleCount j delta failure*(correctionWalkWidth
      (scheduledContext A C K j delta failure z v)+
        RootedEstimatorLayoutProgram.binWidth (scheduledContext A C K j delta failure z v))=_
  simp only [scheduledContext,ratioWidth_data,correctionWalkWidth_data,binWidth_data,
    RootedBinDrawLaw.wordBits_eq,estimatorWordBits,oracleIntegerBits]

end
end ContingencyTables.RootedEstimatorWordProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleConfigProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing a phase's physical oracle configuration

Numeric schedules use binary arithmetic. The supplied reserve bounds
the two materialized precision markers; no binary natural controls an
unbounded list allocation.
-/

namespace ContingencyTables.RootedOracleConfigProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram
open CountingOracleScheduleProgram DensePrograms

attribute [local irreducible] output

attribute [local irreducible] context

attribute [local irreducible] contextWidth

noncomputable section
open CompanionFactorialApplication GridBoundary CompanionOracleDensity
open scoped Classical
variable {m n : ℕ}

lemma fields_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    fields (data A C K j xi z v reserve)=[A.d,K,rationalHeight A C,j] := by
  have hh : 10*(C*(A.d*A.d))*(A.W+1)=10*C*A.d^2*(A.W+1) := by ring
  exact congrArg (fun h => [A.d,K,h,j]) hh

lemma inner_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    TreeFraction.val (inner (data A C K j xi z v reserve))=
      innerTolerance (TreeFraction.val xi/2) j := by
  rw [inner,TreeFraction.div_val,natural_val,scalar,fields_data]
  simp only [relativeDenominator,phase,Expr.eval,List.getD_cons_zero,List.getD_cons_succ,
    Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  unfold innerTolerance
  dsimp only [data]
  field_simp
  ring

lemma repeats_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    repeats (data A C K j xi z v reserve)=CommonBasesFPRAS.repetitionCount (TreeFraction.val xi) := by
  simp only [repeats,normalizedNoise,data,TreeFraction.normalize_repr,TreeFraction.repr,
    CommonBasesFPRAS.repetitionCount]

end
end ContingencyTables.RootedOracleConfigProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleConfigSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact schedules in the computed weight-oracle configuration -/

namespace ContingencyTables.RootedOracleConfigProgram

open MatchingFPRAS CompanionFactorialApplication CompanionOracleDensity GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma scalar_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (reserve : List Bool) (e : ScalarScheduleProgram.Expr) :
    scalar e (data A C K j xi z v reserve)=e.eval [A.d,K,rationalHeight A C,j] := by
  rw [scalar,fields_data]

lemma timeInput_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    timeInput (data A C K j xi z v reserve)=
      (2*(10000*A.d^2*K)^2,rationalHeight A C+A.d*K+2) := by
  simp only [timeInput,scalar_data,mixing,allowance,dim,grid,height,
    ScalarScheduleProgram.Expr.eval_power,ScalarScheduleProgram.Expr.eval,List.getD_cons_zero,List.getD_cons_succ]

lemma correction_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    TreeFraction.val (correction (data A C K j xi z v reserve))=
      correctionTheta (innerTolerance (TreeFraction.val xi/2) j) := by
  rw [correction,TreeFraction.div_val,inner_data]
  simp only [TreeFraction.val,Nat.cast_ofNat,Nat.cast_one,div_one,correctionTheta,Rat.cast_div,Rat.cast_ofNat]

lemma samples_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    samples (data A C K j xi z v reserve)=sampleCount j (innerTolerance (TreeFraction.val xi/2) j) 1 := by
  unfold samples
  rw [CountingOracleScheduleProgram.sampleCount_val,inner_data]
  simp only [data,TreeFraction.val,Nat.cast_one,div_one]

lemma ratioTime_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    ratioTime (data A C K j xi z v reserve)=
      oracleTime A C K 1 (innerTolerance (TreeFraction.val xi/2) j) := by
  rw [ratioTime,timeInput_data,CountingOracleScheduleProgram.oracleTime_instance,inner_data]

lemma correctionTime_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    correctionTime (data A C K j xi z v reserve)=
      oracleTime A C K 1 (correctionTheta (innerTolerance (TreeFraction.val xi/2) j)) := by
  rw [correctionTime,timeInput_data,CountingOracleScheduleProgram.oracleTime_instance,correction_data]

lemma offsetAccuracy_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    offsetAccuracy (data A C K j xi z v reserve)=
      CompanionOracleDensity.offsetAccuracy A (innerTolerance (TreeFraction.val xi/2) j) := by
  rw [offsetAccuracy,CountingOracleScheduleProgram.offsetAccuracy_val,inner_data,scalar_data]
  rfl

lemma context_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    context (data A C K j xi z v reserve)=
      RootedEstimatorMedianProgram.context A C K j (TreeFraction.val xi) z v := by
  unfold context output schedule
  rw [samples_data,ratioTime_data,correctionTime_data,offsetAccuracy_data]
  rfl

lemma output_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    output (data A C K j xi z v reserve)=
      RootedLabelWeightProgram.config A C K j (TreeFraction.val xi) (TreeFraction.val xi) z v
        (reserve.take (rootDegree (data A C K j xi z v reserve)))
        (reserve.take (depth (data A C K j xi z v reserve))) := by
  have hc := context_data A C K j xi z v reserve
  have hr := repeats_data A C K j xi z v reserve
  change ((context _,repeats _),markers _)=_
  rw [hc,hr]
  rfl

lemma rootDegree_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    rootDegree (data A C K j xi z v reserve)=
      PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (TreeFraction.val xi/2) j)) := by
  rw [rootDegree,CountingOracleScheduleProgram.ceiling_val,TreeFraction.div_val,inner_data]
  unfold PowerOfTwoApproximation.rootDegree roundingTolerance
  congr 1
  simp only [TreeFraction.val,Nat.cast_ofNat,Nat.cast_one,div_one,div_div_eq_mul_div]
  ring

lemma depth_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    depth (data A C K j xi z v reserve)=
      PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (TreeFraction.val xi/2) j)) := by
  rw [depth,rootDegree_data]
  rfl

lemma wordWidth_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    wordWidth (data A C K j xi z v reserve)=
      medianEstimatorBits A C K j (TreeFraction.val xi) (TreeFraction.val xi) := by
  rw [wordWidth,contextWidth,context_data,repeats_data,
    RootedEstimatorMedianProgram.context,RootedEstimatorWordProgram.scheduledWordWidth]
  rfl

end
end ContingencyTables.RootedOracleConfigProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseContextProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing a phase configuration from immutable prepared data

The reserve is used only through its length. All precision-marker bits
are false, so the physical configuration is independent of the random
contents of the word that provides its bounded allocation.
-/

namespace ContingencyTables.CompanionPhaseContextProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma falseReserve_eq (z : Input) : falseReserve z=List.replicate z.2.length false := by
  unfold falseReserve
  induction z.2 with
  | nil => rfl
  | cons b bs ih => simpa only [List.map_cons,List.length_cons,List.replicate_succ] using congrArg (List.cons false) ih

noncomputable section
open CompanionFactorialApplication CompanionOracleDensity GridBoundary
open scoped Classical
variable {m n : ℕ}

lemma config_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (reserve : List Bool) :
    config (data A C K j parameters z v reserve)=
      RootedOracleConfigProgram.output (RootedOracleConfigProgram.data A C K j
        (CountingPhaseParametersProgram.noise parameters) z v (List.replicate reserve.length false)) := by
  unfold config configInput noise data
  rw [falseReserve_eq]
  rfl

end
end ContingencyTables.CompanionPhaseContextProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteObservableReindex
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite-observable transports at word and law boundaries -/

namespace ContingencyTables.FiniteObservableTransport

open CommonBasesFPRAS ResidualMixture FirstSuccess
open scoped Classical
noncomputable section

lemma SameLaw.word_length {a b : ℕ} (h : a=b) {Y Z : Type*} [Fintype Y]
    (f : List Bool → Z) (g : Y → Z)
    (hf : SameLaw (fun xs : Fin a → Bool => f (List.ofFn xs)) g) :
    SameLaw (fun xs : Fin b → Bool => f (List.ofFn xs)) g := by
  cases h
  exact hf

lemma SameLaw.of_mapLaw_eq {X Y Z : Type*} [Fintype X] [Nonempty X]
    [Fintype Y] [Nonempty Y] [Fintype Z] [DecidableEq Z]
    (f : X → Z) (g : Y → Z)
    (h : mapLaw (uniformLaw (α := X)) f=mapLaw (uniformLaw (α := Y)) g) :
    SameLaw f g := by
  intro phi
  rw [FiniteLawMoments.word_expectation,FiniteLawMoments.word_expectation,h]

end
end ContingencyTables.FiniteObservableTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_InitialDrawReindex
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact invariance of the finite initializer under computed cell order -/

namespace ContingencyTables.InitialFactorialBits

open CommonBasesFPRAS ResidualMixture FirstSuccess FixedCardinalityMixture
open InitialTransversals CompanionFactorialApplication
open scoped BigOperators Classical
noncomputable section
variable {C : Type*} [Fintype C] {q : ℕ}

/-- Reordering the independent cell words changes no finite initializer
law, including its finite-precision bias. -/
theorem transversalDraw_law (b : C → ℕ) (e : C ≃ Fin q) (B : ℕ) :
    mapLaw (uniformLaw (α := Fin (bitCount (fun i => b (e.symm i)) B) → Bool))
      (transversalDraw b e B)=
        equivLaw (plainEquivChoices b).symm (finiteChoiceLaw b B) := by
  let E := (choiceEquiv b e).trans (plainEquivChoices b).symm
  have he := mapLaw_equiv_output E
    (uniformLaw (α := Fin (bitCount (fun i => b (e.symm i)) B) → Bool))
    (drawChoices (fun i => b (e.symm i)) B)
  rw [drawChoices_law] at he
  change mapLaw _ (fun bits => E (drawChoices _ B bits))=_
  refine he.trans ?_
  apply RationalLaw.ext
  funext S
  change (∏ i : Fin q,
    (mapLaw (uniformLaw (α := Fin (drawBits B (b (e.symm i))) → Bool))
      (subsetDraw B (b (e.symm i)))).mass ((plainEquivChoices b S) (e.symm i)))=
    ∏ c,(mapLaw (uniformLaw (α := Fin (drawBits B (b c)) → Bool))
      (subsetDraw B (b c))).mass ((plainEquivChoices b S) c)
  symm
  apply Fintype.prod_equiv e
  intro c
  exact congrArg (fun c =>
    (mapLaw (uniformLaw (α := Fin (drawBits B (b c)) → Bool))
      (subsetDraw B (b c))).mass ((plainEquivChoices b S) c)) (e.symm_apply_apply c).symm

end
end ContingencyTables.InitialFactorialBits

namespace ContingencyTables.CompanionComputedInitial

open CommonBasesFPRAS ResidualMixture FirstSuccess CompanionFactorialApplication
open InitialFactorialBits FiniteObservableTransport
open scoped Classical
noncomputable section
variable {m n : ℕ}

theorem initialDraw_law (A : Instance (Fin m) (Fin n)) (B : ℕ) :
    mapLaw (uniformLaw (α := Fin (wordLength A B) → Bool)) (initialDraw A B)=
      mapLaw (uniformLaw (α := Fin (CompanionInitialDraw.initialBits A B) → Bool))
        (CompanionInitialDraw.draw A B) := by
  let b := fun s : SmallCell A => A.b s.val.1 s.val.2
  let E := CompanionInitialDraw.indexEquiv A
  have h₁ := mapLaw_equiv_output E
    (uniformLaw (α := Fin (bitCount (fun i => b ((cellOrder A).symm i)) B) → Bool))
    (transversalDraw b (cellOrder A) B)
  have h₂ := mapLaw_equiv_output E
    (uniformLaw (α := Fin (bitCount (fun i => b ((CompanionInitialDraw.cellEnum A).symm i)) B) → Bool))
    (transversalDraw b (CompanionInitialDraw.cellEnum A) B)
  have ht : mapLaw (uniformLaw (α := Fin (bitCount (fun i => b ((cellOrder A).symm i)) B) → Bool))
      (transversalDraw b (cellOrder A) B)=
      mapLaw (uniformLaw (α := Fin (bitCount (fun i => b ((CompanionInitialDraw.cellEnum A).symm i)) B) → Bool))
        (transversalDraw b (CompanionInitialDraw.cellEnum A) B) :=
    (transversalDraw_law b (cellOrder A) B).trans
      (transversalDraw_law b (CompanionInitialDraw.cellEnum A) B).symm
  exact h₁.trans ((congrArg (equivLaw E) ht).trans h₂.symm)

theorem initialProgram_sameLaw (A : Instance (Fin m) (Fin n)) (B : ℕ) (hB : 0 < B) :
    SameLaw (fun bits : Fin (wordLength A B) → Bool =>
      initialProgram ((CompanionCellCatalog.input A,B),List.ofFn bits))
      (fun bits : Fin (CompanionInitialDraw.initialBits A B) → Bool =>
        CompanionArithmeticProposal.encodeSet (coordinateOrder A)
          (CompanionInitialDraw.draw A B bits).val.val) := by
  have h := (SameLaw.of_mapLaw_eq (initialDraw A B) (CompanionInitialDraw.draw A B)
    (initialDraw_law A B)).map (fun S => CompanionArithmeticProposal.encodeSet (coordinateOrder A) S.val.val)
  intro phi
  simpa only [initialProgram_eq A B hB] using h phi

end
end ContingencyTables.CompanionComputedInitial

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartInitializer
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed finite initializer used before every restart experiment -/
namespace ContingencyTables.CompanionRestartInitializer
open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram DensePrograms

noncomputable section
open CompanionFactorialApplication CompanionOracleDensity GridBoundary
open CompanionComputedInitial CompanionArithmeticProposal FiniteObservableTransport
open scoped BigOperators Classical
variable {m n : ℕ}

lemma cellInput_data (A : Instance (Fin m) (Fin n)) (C K H T N R L : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    cellInput (data A C K H T N R L epsilon z v)=CompanionCellCatalog.input A := rfl

lemma precision_data (A : Instance (Fin m) (Fin n)) (C K H T N R L : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    precision (data A C K H T N R L epsilon z v)=
      CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H) := by
  simp [precision,scalar,fields,data,RootedOracleWalkProgram.data,
    initialBound,initialExponent,Expr.eval,CompanionInitialDraw.precision,CountingPhaseSchedule.initialPrecision]

lemma width_data (A : Instance (Fin m) (Fin n)) (C K H T N R L : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    width (data A C K H T N R L epsilon z v)=
      CompanionComputedInitial.wordLength A
        (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H)) := by
  unfold width capacities
  rw [cellInput_data,CompanionCellCatalog.capacities_eq,precision_data]
  rw [InitialChoiceProgram.widths_ofFn,List.sum_ofFn]
  rfl

theorem output_sameLaw (A : Instance (Fin m) (Fin n)) (C K H T N R L : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    let B := CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H)
    SameLaw (fun bits : Fin (CompanionComputedInitial.wordLength A B) → Bool =>
      output (data A C K H T N R L epsilon z v,List.ofFn bits))
      (fun bits => encodeSet (coordinateOrder A) (CompanionInitialDraw.draw A B bits).val.val) := by
  dsimp only
  have hB : 0 < CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H) := by
    unfold CompanionInitialDraw.precision CountingPhaseSchedule.initialPrecision
    omega
  have h := initialProgram_sameLaw A
    (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H)) hB
  intro phi
  convert h phi using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg CommonBasesFPRAS.uniformAverage
  funext bits
  dsimp only
  rw [output,prepare,cellInput_data,precision_data]

end
end ContingencyTables.CompanionRestartInitializer

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionEvaluatedWeightLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-width laws for the two physical Metropolis weight calls -/

namespace ContingencyTables.CompanionEvaluatedWeightProgram

open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial
open CompanionArithmeticProposal CompanionOracleDensity CompanionWeightOracle
open CompanionMultiplierMatrixProgram GridBoundary CommonBasesFPRAS FiniteObservableTransport
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma queryWidth (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    repetitionCount xi*RootedEstimatorLayoutProgram.wordWidth
      (RootedEstimatorMedianProgram.context A C K j xi z v)=medianEstimatorBits A C K j xi xi := by
  rw [RootedEstimatorMedianProgram.context,RootedEstimatorWordProgram.scheduledWordWidth]
  rfl

end
end ContingencyTables.CompanionEvaluatedWeightProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMetropolisWordSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The flat physical transition has the proved phase-step law -/

namespace ContingencyTables.CompanionMetropolisWordProgram

open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionOracleDensity CompanionWeightOracle
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram CommonBasesFPRAS
open CompanionBooleanPhase (State)
open FiniteObservableTransport TwoLiftStates GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma proposalWidth_code (A : Instance (Fin m) (Fin n))
    (frame : CompanionMetropolisProgram.Frame) (k : ℕ) (S : Set (Labels A × Bool)) (bits : List Bool) :
    proposalWidth (packed frame k (encodeSet (coordinateOrder A) S) bits)=
      CompanionBooleanPhase.proposalBits A := by
  have hc := Fintype.card_congr (coordinateOrder A)
  simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin] at hc
  have hd : (CanonicalInitialEncoding.pairOrder (capacities A)).length/2=Fintype.card (Labels A) := by omega
  simp only [proposalWidth,packed,encodeSet,List.length_ofFn,hd,CompanionBooleanPhase.proposalBits]

lemma queryWidth_config (A : Instance (Fin m) (Fin n)) (C K j k : ℕ) (xi : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (w : FractionMatrix) (code : List ℕ) (bits : List Bool) :
    queryWidth (packed (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,w) k code bits)=
      medianEstimatorBits A C K j xi xi := by
  exact CompanionEvaluatedWeightProgram.queryWidth A C K j xi z v

end
end ContingencyTables.CompanionMetropolisWordProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTransitionWidth
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the exact companion transition word length -/

namespace ContingencyTables.CompanionTransitionWidth

open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram
open CompanionMetropolisWordProgram

attribute [local irreducible] proposalWidth queryWidth

lemma width_eq (z : Input) : width z=1+(proposalWidth z+((queryWidth z+queryWidth z)+z.1.1.2)) := by
  rfl

noncomputable section
open CompanionFactorialApplication CompanionComputedInitial CompanionArithmeticProposal
open CompanionOracleDensity CompanionWeightOracle GridBoundary
variable {m n : ℕ}

theorem width_config (A : Instance (Fin m) (Fin n)) (C K j k : ℕ) (xi : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (w : CompanionMultiplierMatrixProgram.FractionMatrix)
    (S : Set (Labels A × Bool)) (bits : List Bool) :
    width (packed (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,w)
      k (encodeSet (coordinateOrder A) S) bits)=CompanionBooleanPhase.stepBits A C K j k xi := by
  rw [width_eq,proposalWidth_code,queryWidth_config]
  rfl

end
end ContingencyTables.CompanionTransitionWidth

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact disjoint-word semantics of the physical restart loop -/
namespace ContingencyTables.CompanionRestartProgram
open FirstSuccess FiniteObservableTransport MatchingFPRAS DensePrograms CommonBasesFPRAS
open scoped BigOperators Classical

lemma widths_ofFn (base : List Stage×List ℕ) (bits : List Bool) :
    widths (base,bits)=List.ofFn (fun i : Fin base.1.length => widthAt base i.val) := by
  unfold widths indices
  rw [DirectedBFSCode.range_eq_map]
  simp only [List.map_map,Function.comp_def]
  change (List.finRange base.1.length).map (fun i => widthAt base i.val)=_
  exact List.ofFn_eq_map.symm

lemma next_detached (base : List Stage×List ℕ) (allBits : List Bool) (i : ℕ) (code : List ℕ) :
    next (i,((base,allBits),code))=
      detachedStep base i code (stageWord ((base,allBits),i)) := rfl

lemma walk_eq (input : Input) (is : List ℕ) (code : List ℕ) :
    walk ((input,code),is)=
      (input,is.foldl (fun code i => next (i,(input,code))) code) := by
  induction is generalizing code with
  | nil => rfl
  | cons i is ih =>
    simpa only [walk,List.foldl_cons,advance] using ih (next (i,(input,code)))

end ContingencyTables.CompanionRestartProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRepeatedReturnLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The physical return loop has the actual repeated-return law -/

namespace ContingencyTables.CompanionRepeatedReturnProgram

open MatchingFPRAS CommonBasesFPRAS FirstSuccess ResidualMixture
open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle
open CompanionComputedInitial CompanionComputedProposal CompanionArithmeticProposal
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram
open FiniteObservableTransport TwoLiftStates GridBoundary
open scoped Classical

noncomputable section
variable {m n : ℕ}

lemma blockWidth_data (A : Instance (Fin m) (Fin n)) (C K j k cap : ℕ) (xi : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : Set (Labels A × Bool)) :
    blockWidth (fixedData A C K j k cap xi z v degree depth w S)=
      (cap+1)*CompanionBooleanPhase.stepBits A C K j k xi := by
  unfold blockWidth widthInput fixedData
  dsimp only
  exact congrArg (fun width : ℕ => (cap+1)*width)
    (CompanionTransitionWidth.width_config A C K j k xi z v degree depth (matrixCode w) S [])

end
end ContingencyTables.CompanionRepeatedReturnProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartStageLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed restart stage is the literal finite-word return law -/
namespace ContingencyTables.CompanionRestartStageProgram
open MatchingFPRAS CommonBasesFPRAS CompanionFactorialApplication
open CompanionOracleDensity CompanionWeightOracle CompanionComputedInitial
open CompanionComputedProposal CompanionArithmeticProposal CompanionMultiplierMatrixProgram
open CompanionEvaluatedWeightProgram
open FiniteObservableTransport TwoLiftStates GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma config_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool)
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : Set (Labels A×Bool)) :
    CompanionPhaseContextProgram.config (context (data A C K j parameters z v reserve w S))=
      RootedLabelWeightProgram.config A C K j
        (TreeFraction.val (CountingPhaseParametersProgram.noise parameters))
        (TreeFraction.val (CountingPhaseParametersProgram.noise parameters)) z v
        (degree A C K j parameters z v reserve) (depth A C K j parameters z v reserve) := by
  unfold context data
  rw [CompanionPhaseContextProgram.config_data,RootedOracleConfigProgram.output_data]
  rfl

lemma fixed_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool)
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : Set (Labels A×Bool)) :
    fixed (data A C K j parameters z v reserve w S)=
      CompanionRepeatedReturnProgram.fixedData A C K j
        (CountingPhaseParametersProgram.precision parameters)
        (CountingPhaseParametersProgram.scalar (.input 5) parameters)
        (TreeFraction.val (CountingPhaseParametersProgram.noise parameters)) z v
        (degree A C K j parameters z v reserve) (depth A C K j parameters z v reserve) w S := by
  unfold fixed frame
  rw [config_data]
  rfl

theorem width_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool)
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : Set (Labels A×Bool)) :
    width (data A C K j parameters z v reserve w S)=
      CountingPhaseParametersProgram.scalar (.input 3) parameters*
        ((CountingPhaseParametersProgram.scalar (.input 5) parameters+1)*
          CompanionBooleanPhase.stepBits A C K j (CountingPhaseParametersProgram.precision parameters)
            (TreeFraction.val (CountingPhaseParametersProgram.noise parameters))) := by
  unfold width
  rw [fixed_data,CompanionRepeatedReturnProgram.blockWidth_data]
  rfl

end
end ContingencyTables.CompanionRestartStageProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartDataLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete stored-matrix restart experiment -/
namespace ContingencyTables.CompanionRestartProgram
open MatchingFPRAS CommonBasesFPRAS FirstSuccess FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram
open CompanionOracleDensity CompanionWeightOracle TwoLiftStates GridBoundary
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ}

lemma request_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : Set (Labels A×Bool))
    (i : Fin j) :
    request ((baseData A C K j parameters z v reserve w S,[]),i.val)=
      CompanionRestartStageProgram.data A C K (i.val+1) parameters z v reserve (w (i.val+1)) S := by
  unfold request baseData stagesData
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,dite_true,Option.getD_some]
  rfl

theorem widthAt_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : Set (Labels A×Bool))
    (i : Fin j) :
    widthAt (baseData A C K j parameters z v reserve w S) i.val=
      sourceWidth A C K parameters i.val := by
  unfold widthAt indexedWidth
  rw [request_data,CompanionRestartStageProgram.width_data]
  rfl

end
end ContingencyTables.CompanionRestartProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartScheduleSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact deterministic restart budgets for the source experiment -/
namespace ContingencyTables.CompanionRestartSchedule
open MatchingFPRAS CompanionFactorialApplication CompanionOracleDensity
open CompanionComputedInitial GridBoundary FirstSuccess
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ}

lemma configInput_data (A : Instance (Fin m) (Fin n)) (C K H T N R L i : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    configInput (CompanionRestartInitializer.data A C K H T N R L epsilon z v,i)=
      RootedOracleConfigProgram.data A C K (i+1)
        (CountingPhaseParametersProgram.noise ([Fintype.card (Labels A),A.W,H,T,N,R,L],epsilon)) z v [] := rfl

lemma queryWidth_data (A : Instance (Fin m) (Fin n)) (C K H T N R L i : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    queryWidth (CompanionRestartInitializer.data A C K H T N R L epsilon z v,i)=
      CompanionOracleDensity.medianEstimatorBits A C K (i+1)
        (TreeFraction.val (CountingPhaseParametersProgram.noise ([Fintype.card (Labels A),A.W,H,T,N,R,L],epsilon)))
        (TreeFraction.val (CountingPhaseParametersProgram.noise ([Fintype.card (Labels A),A.W,H,T,N,R,L],epsilon))) := by
  rw [queryWidth,configInput_data,RootedOracleConfigProgram.wordWidth_data]

lemma proposalWidth_data (A : Instance (Fin m) (Fin n)) (C K H T N R L i : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    proposalWidth (CompanionRestartInitializer.data A C K H T N R L epsilon z v,i)=
      CompanionBooleanPhase.proposalBits A := by
  simp only [proposalWidth,scalar,CompanionRestartInitializer.data,
    CountingPhaseParametersProgram.scalar,ScalarScheduleProgram.Expr.eval,
    List.getD_cons_zero,CompanionBooleanPhase.proposalBits,pow_two]

theorem stageWidth_data (A : Instance (Fin m) (Fin n)) (C K H T N R L i : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    stageWidth (CompanionRestartInitializer.data A C K H T N R L epsilon z v,i)=
      CompanionRestartProgram.sourceWidth A C K
        ([Fintype.card (Labels A),A.W,H,T,N,R,L],epsilon) i := by
  unfold stageWidth
  change T*((R+1)*(1+(proposalWidth (CompanionRestartInitializer.data A C K H T N R L epsilon z v,i)+
    ((queryWidth (CompanionRestartInitializer.data A C K H T N R L epsilon z v,i)+
      queryWidth (CompanionRestartInitializer.data A C K H T N R L epsilon z v,i))+
        CountingPhaseParametersProgram.precision ([Fintype.card (Labels A),A.W,H,T,N,R,L],epsilon)))))=_
  rw [proposalWidth_data,queryWidth_data]
  rfl

theorem restartWidth_data (A : Instance (Fin m) (Fin n)) (C K H T N R L : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (history : List CompanionPhaseFinishProgram.Stored) :
    restartWidth (CompanionRestartInitializer.data A C K H T N R L epsilon z v,history)=
      ∑ i : Fin history.length,CompanionRestartProgram.sourceWidth A C K
        ([Fintype.card (Labels A),A.W,H,T,N,R,L],epsilon) i.val := by
  unfold restartWidth indices
  rw [DirectedBFSCode.range_eq_map]
  simp only [List.map_map,Function.comp_def]
  rw [←List.ofFn_eq_map,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  exact stageWidth_data A C K H T N R L i.val epsilon z v

lemma initialWidths_eq (A : Instance (Fin m) (Fin n)) (B : ℕ) :
    CompanionComputedInitial.wordLength A B=CompanionInitialDraw.initialBits A B := by
  unfold CompanionComputedInitial.wordLength CompanionInitialDraw.initialBits InitialFactorialBits.bitCount
  calc
    _ = ∑ s : SmallCell A,FixedCardinalityMixture.drawBits B (A.b s.val.1 s.val.2) :=
      Fintype.sum_equiv (CompanionComputedInitial.cellOrder A).symm _ _ (fun _ => rfl)
    _ = _ := (Fintype.sum_equiv (CompanionInitialDraw.cellEnum A).symm _ _ (fun _ => rfl)).symm

end
end ContingencyTables.CompanionRestartSchedule

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitializedRestartSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal inputs and disjoint slices of initialized restarts -/
namespace ContingencyTables.CompanionInitializedRestartProgram
open MatchingFPRAS CommonBasesFPRAS FairBits DensePrograms
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram
open CompanionOracleDensity GridBoundary
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ}

lemma stages_data (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (estimates : Fin j → TreeFraction.Fraction) (bits : List Bool) :
    stages (data A C K H T N R L j epsilon z v w estimates bits)=
      CompanionRestartProgram.stagesData A C K j
        ([Fintype.card (Labels A),A.W,H,T,N,R,L],epsilon) z v (List.replicate bits.length false) w := by
  unfold stages indices data
  rw [List.length_ofFn,DirectedBFSCode.range_eq_map]
  simp only [List.map_map,Function.comp_def]
  rw [←List.ofFn_eq_map]
  apply congrArg List.ofFn
  funext i
  unfold stageAt reserve
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,dite_true,Option.getD_some,
    List.map_const']
  rfl

lemma initialWidth_data (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (estimates : Fin j → TreeFraction.Fraction) (bits : List Bool) :
    initialWidth (data A C K H T N R L j epsilon z v w estimates bits)=
      wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H)) :=
  CompanionRestartInitializer.width_data A C K H T N R L epsilon z v

 /-- Exact physical splitting: the initializer sees the first block,
 the restart loop sees the remaining block, and all markers are fixed. -/
theorem output_split (A : Instance (Fin m) (Fin n)) (C K H T N R L j s : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (estimates : Fin j → TreeFraction.Fraction)
    (bits : Fin (wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+s) → Bool) :
    output (data A C K H T N R L j epsilon z v w estimates (List.ofFn bits))=
      CompanionRestartProgram.output
        ((CompanionRestartProgram.stagesData A C K j
          ([Fintype.card (Labels A),A.W,H,T,N,R,L],epsilon) z v
          (List.replicate (wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+s) false) w,
          CompanionRestartInitializer.output
            (CompanionRestartInitializer.data A C K H T N R L epsilon z v,
              List.ofFn (splitWordEquiv
                (wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))) s bits).1)),
          List.ofFn (splitWordEquiv
            (wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))) s bits).2) := by
  unfold output prepare initialCode initialInput
  rw [stages_data,initialWidth_data,List.length_ofFn]
  dsimp only [data]
  rw [ofFn_split_take,ofFn_split_drop]

end
end ContingencyTables.CompanionInitializedRestartProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartNativeLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common native bit width for all initial plain states -/
namespace ContingencyTables.CompanionRestartProgram
open MatchingFPRAS CommonBasesFPRAS FirstSuccess FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionEvaluatedWeightProgram
open CompanionOracleDensity TwoLiftStates GridBoundary
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ}

lemma widthSum_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (parameters : CountingPhaseParametersProgram.Input) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : Set (Labels A×Bool)) :
    (∑ i : Fin (baseData A C K j parameters z v reserve w S).1.length,
      widthAt (baseData A C K j parameters z v reserve w S) i.val)=sumBits A C K j parameters := by
  have hn : (baseData A C K j parameters z v reserve w S).1.length=j := by
    simp only [baseData,stagesData,List.length_ofFn]
  rw [hn]
  exact Finset.sum_congr rfl (fun i _ => widthAt_data A C K j parameters z v reserve w S i)

end
end ContingencyTables.CompanionRestartProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartPadding
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unused tail bits do not alter the executed restart stages -/
namespace ContingencyTables.DensePrograms
open scoped BigOperators

lemma prefix_sum_add_width_le {q : ℕ} (width : Fin q → ℕ) (i : Fin q) :
    ((List.ofFn width).take i.val).sum+width i ≤ ∑ j,width j := by
  by_cases hi : width i=0
  · rw [hi,Nat.add_zero,←List.sum_ofFn]
    exact (List.take_sublist i.val (List.ofFn width)).sum_le_sum (fun _ _ => Nat.zero_le _)
  · have h := (finSigmaFinEquiv (⟨i,⟨width i-1,by omega⟩⟩ : Sigma (fun i => Fin (width i)))).isLt
    rw [finSigmaFinEquiv_apply,←take_ofFn_sum] at h
    dsimp only at h
    omega

theorem dependentChunk_take_sum {q : ℕ} (width : Fin q → ℕ)
    (bits : List Bool) (i : Fin q) :
    dependentChunk ((List.ofFn width,bits.take (∑ j,width j)),i.val)=
      dependentChunk ((List.ofFn width,bits),i.val) := by
  have hw : (List.ofFn width).getD i.val 0=width i := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,dite_true,Option.getD_some,Fin.eta]
  have hb := prefix_sum_add_width_le width i
  dsimp only [dependentChunk,chunkStart]
  rw [hw,List.drop_take,List.take_take,min_eq_left (by omega)]

end ContingencyTables.DensePrograms

namespace ContingencyTables.CompanionRestartProgram
open CommonBasesFPRAS FirstSuccess DensePrograms FiniteObservableTransport
open scoped BigOperators Classical

lemma stageWord_take_sum (base : List Stage×List ℕ) (bits : List Bool)
    (i : Fin base.1.length) :
    stageWord ((base,bits.take (∑ j : Fin base.1.length,widthAt base j.val)),i.val)=
      stageWord ((base,bits),i.val) := by
  unfold stageWord
  rw [widths_ofFn,widths_ofFn]
  exact dependentChunk_take_sum (fun i : Fin base.1.length => widthAt base i.val) bits i

private lemma foldl_eq_on {A B : Type*} (f g : B → A → B) (xs : List A)
    (h : ∀ a,a ∈ xs → ∀ b,f b a=g b a) (b : B) : xs.foldl f b=xs.foldl g b := by
  induction xs generalizing b with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.foldl_cons]
    rw [h a (by simp) b]
    exact ih (fun a ha b => h a (by simp [ha]) b) _

theorem output_take_sum (base : List Stage×List ℕ) (bits : List Bool) :
    output (base,bits.take (∑ i : Fin base.1.length,widthAt base i.val))=
      output (base,bits) := by
  unfold output
  rw [walk_eq,walk_eq]
  change (List.range base.1.length).foldl
      (fun code i => next (i,((base,bits.take (∑ j : Fin base.1.length,widthAt base j.val)),code))) base.2=
    (List.range base.1.length).foldl (fun code i => next (i,((base,bits),code))) base.2
  apply foldl_eq_on
  intro i hi code
  have hlt : i < base.1.length := List.mem_range.mp hi
  rw [next_detached,next_detached,stageWord_take_sum base bits ⟨i,hlt⟩]

end ContingencyTables.CompanionRestartProgram

namespace ContingencyTables.FiniteObservableTransport
open CommonBasesFPRAS FairBits
open scoped Classical
noncomputable section

theorem SameLaw.append_unused {Y Z : Type*} [Fintype Y] {n : ℕ}
    {f : (Fin n → Bool) → Z} {g : Y → Z} (h : SameLaw f g) (t : ℕ) :
    SameLaw (fun bits : Fin (n+t) → Bool => f (splitWordEquiv n t bits).1) g := by
  intro phi
  have he := uniformAverage_equiv (splitWordEquiv n t)
    (fun p : (Fin n → Bool)×(Fin t → Bool) => phi (f p.1))
  refine he.trans ?_
  rw [uniformAverage_prod]
  simp only [uniformAverage_const]
  exact h phi

theorem restart_append_sameLaw {Y : Type*} [Fintype Y]
    (base : List CompanionRestartProgram.Stage×List ℕ) (n : ℕ)
    (hn : (∑ i : Fin base.1.length,CompanionRestartProgram.widthAt base i.val)=n)
    (g : Y → List ℕ)
    (h : SameLaw (fun bits : Fin n → Bool =>
      CompanionRestartProgram.output (base,List.ofFn bits)) g) (t : ℕ) :
    SameLaw (fun bits : Fin (n+t) → Bool =>
      CompanionRestartProgram.output (base,List.ofFn bits)) g := by
  have hp := h.append_unused t
  have he (bits : Fin (n+t) → Bool) :
      CompanionRestartProgram.output (base,List.ofFn bits)=
        CompanionRestartProgram.output (base,List.ofFn (splitWordEquiv n t bits).1) := by
    have hs := (CompanionRestartProgram.output_take_sum base (List.ofFn bits)).symm
    rw [hn,DensePrograms.ofFn_split_take] at hs
    exact hs
  intro phi
  simp_rw [he]
  exact hp phi

end
end ContingencyTables.FiniteObservableTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteEncodedBind
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Composing exact laws through a noninjective state encoding -/
namespace ContingencyTables.FiniteObservableTransport
open CommonBasesFPRAS FairBits
open scoped Classical
noncomputable section

theorem encoded_bind {A B U V C Z W : Type*}
    [Fintype A] [Fintype B] [Fintype U] [Fintype V]
    (f : A → C) (g : B → Z) (e : Z → C) (F : C → U → W) (G : Z → V → W)
    (hinit : SameLaw f (fun b => e (g b))) (hstep : ∀ z,SameLaw (F (e z)) (G z)) :
    SameLaw (fun p : A×U => F (f p.1) p.2) (fun p : B×V => G (g p.1) p.2) := by
  intro phi
  rw [uniformAverage_prod,uniformAverage_prod]
  have hi := hinit (fun c => uniformAverage (fun u : U => phi (F c u)))
  refine hi.trans ?_
  apply congrArg uniformAverage
  funext b
  exact hstep (g b) phi

theorem flat_encoded_bind {C Z W : Type*} (a b c d : ℕ)
    (f : (Fin a → Bool) → C) (g : (Fin c → Bool) → Z) (e : Z → C)
    (F : C → (Fin b → Bool) → W) (G : Z → (Fin d → Bool) → W)
    (hinit : SameLaw f (fun bits => e (g bits))) (hstep : ∀ z,SameLaw (F (e z)) (G z)) :
    SameLaw (fun bits : Fin (a+b) → Bool =>
      F (f (splitWordEquiv a b bits).1) (splitWordEquiv a b bits).2)
      (fun bits : Fin (c+d) → Bool =>
        G (g (splitWordEquiv c d bits).1) (splitWordEquiv c d bits).2) := by
  have h := encoded_bind f g e F G hinit hstep
  intro phi
  have hl := uniformAverage_equiv (splitWordEquiv a b)
    (fun p : (Fin a → Bool)×(Fin b → Bool) => phi (F (f p.1) p.2))
  have hr := uniformAverage_equiv (splitWordEquiv c d)
    (fun p : (Fin c → Bool)×(Fin d → Bool) => phi (G (g p.1) p.2))
  exact hl.trans ((h phi).trans hr.symm)

end
end ContingencyTables.FiniteObservableTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitializedRestartLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact law of the complete executed initializer and restart prefix -/
namespace ContingencyTables.CompanionInitializedRestartProgram
open MatchingFPRAS CommonBasesFPRAS FirstSuccess FairBits FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionEvaluatedWeightProgram
open CompanionOracleDensity TwoLiftStates GridBoundary
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ}

 /-- The actual list program has the complete finite-word law, including
 every initialization bias, rejected return and fallback. -/
theorem output_padded_sameLaw (A : Instance (Fin m) (Fin n)) (C K H T N R L j padding : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (epsilon : TreeFraction.Fraction)
    (hxi : 0 < TreeFraction.val (CountingPhaseParametersProgram.noise (parameters A H T N R L epsilon)))
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (estimates : Fin j → TreeFraction.Fraction)
    (hdegree : ∀ i : Fin j,RootedOracleConfigProgram.rootDegree
      (CompanionRestartStageProgram.oracleData A C K (i.val+1) (parameters A H T N R L epsilon) z v
        (List.replicate (wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
          (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding)) false)) ≤
      wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
        (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding))
    (hdepth : ∀ i : Fin j,RootedOracleConfigProgram.depth
      (CompanionRestartStageProgram.oracleData A C K (i.val+1) (parameters A H T N R L epsilon) z v
        (List.replicate (wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
          (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding)) false)) ≤
      wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
        (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding)) :
    SameLaw (fun bits : Fin (wordLength A
        (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
      (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding)) → Bool =>
      output (data A C K H T N R L j epsilon z v w estimates (List.ofFn bits)))
      (fun bits => encodeSet (coordinateOrder A) (model A C K H T N R L j epsilon hK hW v w bits).val.val) := by
  let B := CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H)
  let p := parameters A H T N R L epsilon
  let n := CompanionRestartProgram.sumBits A C K j p
  let reserve := List.replicate (wordLength A B+(n+padding)) false
  let stageList := CompanionRestartProgram.stagesData A C K j p z v reserve w
  let init := fun bits : Fin (wordLength A B) → Bool => CompanionRestartInitializer.output
    (CompanionRestartInitializer.data A C K H T N R L epsilon z v,List.ofFn bits)
  let realInit := CompanionInitialDraw.draw A B
  let encode := fun S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A)) =>
    encodeSet (coordinateOrder A) S.val.val
  let run := fun code (bits : Fin (n+padding) → Bool) =>
    CompanionRestartProgram.output ((stageList,code),List.ofFn bits)
  let realRun := fun S (bits : Fin n → Bool) => encode (varyingWalk
    (CompanionRestartProgram.sourceWidth A C K p)
    (CompanionRestartProgram.sourceStep A C K p hK hW v w) S j
    (varyingWordEquiv (CompanionRestartProgram.sourceWidth A C K p) j bits))
  have hi : SameLaw init (fun bits => encode (realInit bits)) :=
    CompanionRestartInitializer.output_sameLaw A C K H T N R L epsilon z v
  have hs : ∀ S,SameLaw (run (encode S)) (realRun S) := by
    intro S
    have hn := CompanionRestartProgram.widthSum_data A C K j p z v reserve w S.val.val
    have hh := CompanionRestartProgram.output_native_sameLaw A C K j hC hj hK hW hB p hxi z v reserve
      (fun i => by simpa only [reserve,List.length_replicate] using hdegree i)
      (fun i => by simpa only [reserve,List.length_replicate] using hdepth i) w S
    exact restart_append_sameLaw (CompanionRestartProgram.baseData A C K j p z v reserve w S.val.val)
      n hn (realRun S) hh padding
  have hf := flat_encoded_bind (wordLength A B) (n+padding) (CompanionInitialDraw.initialBits A B) n
    init realInit encode run realRun hi hs
  intro phi
  have h := hf phi
  have he : (fun bits : Fin (wordLength A B+(n+padding)) → Bool =>
      output (data A C K H T N R L j epsilon z v w estimates (List.ofFn bits)))=
      (fun bits => run (init (splitWordEquiv (wordLength A B) (n+padding) bits).1)
        (splitWordEquiv (wordLength A B) (n+padding) bits).2) := by
    funext bits
    exact output_split A C K H T N R L j (n+padding) epsilon z v w estimates bits
  rw [he]
  exact h

end
end ContingencyTables.CompanionInitializedRestartProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteWordJointPadding
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Padding preserves the joint law with every unused suffix bit -/
namespace ContingencyTables.FiniteObservableTransport
open CommonBasesFPRAS FairBits
open scoped BigOperators Classical
noncomputable section

theorem SameLaw.append_joint {Z : Type*} {n q : ℕ}
    {f : (Fin n → Bool) → Z} {g : (Fin q → Bool) → Z}
    (h : SameLaw f g) (t : ℕ) :
    SameLaw (fun bits : Fin (n+t) → Bool =>
        (f (splitWordEquiv n t bits).1,(splitWordEquiv n t bits).2))
      (fun bits : Fin (q+t) → Bool =>
        (g (splitWordEquiv q t bits).1,(splitWordEquiv q t bits).2)) := by
  have hp := h.prod (show SameLaw (fun bits : Fin t → Bool => bits) (fun bits : Fin t → Bool => bits)
    from fun _ => rfl)
  intro phi
  have hl := uniformAverage_equiv (splitWordEquiv n t)
    (fun p : (Fin n → Bool)×(Fin t → Bool) => phi (f p.1,p.2))
  have hr := uniformAverage_equiv (splitWordEquiv q t)
    (fun p : (Fin q → Bool)×(Fin t → Bool) => phi (g p.1,p.2))
  exact hl.trans ((hp phi).trans hr.symm)

theorem restart_append_joint_sameLaw
    (base : List CompanionRestartProgram.Stage×List ℕ) (n q : ℕ)
    (hn : (∑ i : Fin base.1.length,CompanionRestartProgram.widthAt base i.val)=n)
    (g : (Fin q → Bool) → List ℕ)
    (h : SameLaw (fun bits : Fin n → Bool =>
      CompanionRestartProgram.output (base,List.ofFn bits)) g) (t : ℕ) :
    SameLaw (fun bits : Fin (n+t) → Bool =>
        (CompanionRestartProgram.output (base,List.ofFn bits),(splitWordEquiv n t bits).2))
      (fun bits : Fin (q+t) → Bool =>
        (g (splitWordEquiv q t bits).1,(splitWordEquiv q t bits).2)) := by
  have hp := h.append_joint t
  have he (bits : Fin (n+t) → Bool) :
      CompanionRestartProgram.output (base,List.ofFn bits)=
        CompanionRestartProgram.output (base,List.ofFn (splitWordEquiv n t bits).1) := by
    have hs := (CompanionRestartProgram.output_take_sum base (List.ofFn bits)).symm
    rw [hn,DensePrograms.ofFn_split_take] at hs
    exact hs
  intro phi
  simp_rw [he]
  exact hp phi

/-- Flattening the first two independent blocks preserves their joint
law with the untouched third block. -/
theorem nested_word_joint {Z : Type*} (a b t : ℕ)
    (f : (Fin a → Bool) → (Fin b → Bool) → Z) :
    SameLaw (fun bits : Fin (a+(b+t)) → Bool =>
      (f (splitWordEquiv a (b+t) bits).1
        (splitWordEquiv b t (splitWordEquiv a (b+t) bits).2).1,
        (splitWordEquiv b t (splitWordEquiv a (b+t) bits).2).2))
      (fun bits : (Fin (a+b) → Bool)×(Fin t → Bool) =>
        (f (splitWordEquiv a b bits.1).1 (splitWordEquiv a b bits.1).2,bits.2)) := by
  intro phi
  have houter := uniformAverage_equiv (splitWordEquiv a (b+t))
    (fun p : (Fin a → Bool)×(Fin (b+t) → Bool) =>
      phi (f p.1 (splitWordEquiv b t p.2).1,(splitWordEquiv b t p.2).2))
  have hinner (u : Fin a → Bool) := uniformAverage_equiv (splitWordEquiv b t)
    (fun p : (Fin b → Bool)×(Fin t → Bool) => phi (f u p.1,p.2))
  have hfirst := uniformAverage_equiv (splitWordEquiv a b)
    (fun p : (Fin a → Bool)×(Fin b → Bool) =>
      uniformAverage (fun tail : Fin t → Bool => phi (f p.1 p.2,tail)))
  rw [uniformAverage_prod] at hfirst
  rw [uniformAverage_prod]
  refine houter.trans ?_
  rw [uniformAverage_prod]
  calc
    _ = uniformAverage (fun u : Fin a → Bool =>
        uniformAverage (fun v : Fin b → Bool =>
          uniformAverage (fun tail : Fin t → Bool => phi (f u v,tail)))) := by
      apply congrArg uniformAverage
      funext u
      exact (hinner u).trans (uniformAverage_prod _)
    _ = _ := hfirst.symm

end
end ContingencyTables.FiniteObservableTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitializedRestartJoint
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint restart law with the unused trajectory and query suffix -/
namespace ContingencyTables.CompanionInitializedRestartProgram
open MatchingFPRAS CommonBasesFPRAS FirstSuccess FairBits FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionEvaluatedWeightProgram
open CompanionOracleDensity TwoLiftStates GridBoundary
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ}

theorem output_joint_sameLaw (A : Instance (Fin m) (Fin n)) (C K H T N R L j padding : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (epsilon : TreeFraction.Fraction)
    (hxi : 0 < TreeFraction.val (CountingPhaseParametersProgram.noise (parameters A H T N R L epsilon)))
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (estimates : Fin j → TreeFraction.Fraction)
    (hdegree : ∀ i : Fin j,RootedOracleConfigProgram.rootDegree
      (CompanionRestartStageProgram.oracleData A C K (i.val+1) (parameters A H T N R L epsilon) z v
        (List.replicate (wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
          (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding)) false)) ≤
      wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
        (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding))
    (hdepth : ∀ i : Fin j,RootedOracleConfigProgram.depth
      (CompanionRestartStageProgram.oracleData A C K (i.val+1) (parameters A H T N R L epsilon) z v
        (List.replicate (wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
          (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding)) false)) ≤
      wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
        (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding)) :
    SameLaw (fun bits : Fin (wordLength A
        (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
      (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding)) → Bool =>
      (output (data A C K H T N R L j epsilon z v w estimates (List.ofFn bits)),
        (splitWordEquiv (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon))
          padding (splitWordEquiv
            (wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H)))
            (CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)+padding) bits).2).2))
      (fun bits =>
        (encodeSet (coordinateOrder A) (jointModel A C K H T N R L j padding epsilon hK hW v w bits).1.val.val,
          (jointModel A C K H T N R L j padding epsilon hK hW v w bits).2)) := by
  let B := CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H)
  let p := parameters A H T N R L epsilon
  let n := CompanionRestartProgram.sumBits A C K j p
  let reserve := List.replicate (wordLength A B+(n+padding)) false
  let stageList := CompanionRestartProgram.stagesData A C K j p z v reserve w
  let init := fun bits : Fin (wordLength A B) → Bool => CompanionRestartInitializer.output
    (CompanionRestartInitializer.data A C K H T N R L epsilon z v,List.ofFn bits)
  let realInit := CompanionInitialDraw.draw A B
  let encode := fun S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A)) =>
    encodeSet (coordinateOrder A) S.val.val
  let run := fun code (bits : Fin (n+padding) → Bool) =>
    (CompanionRestartProgram.output ((stageList,code),List.ofFn bits),(splitWordEquiv n padding bits).2)
  let sourceRun := fun S (bits : Fin n → Bool) => encode (varyingWalk
    (CompanionRestartProgram.sourceWidth A C K p)
    (CompanionRestartProgram.sourceStep A C K p hK hW v w) S j
    (varyingWordEquiv (CompanionRestartProgram.sourceWidth A C K p) j bits))
  let realRun := fun S (bits : Fin (n+padding) → Bool) =>
    (sourceRun S (splitWordEquiv n padding bits).1,(splitWordEquiv n padding bits).2)
  have hi : SameLaw init (fun bits => encode (realInit bits)) :=
    CompanionRestartInitializer.output_sameLaw A C K H T N R L epsilon z v
  have hs : ∀ S,SameLaw (run (encode S)) (realRun S) := by
    intro S
    have hn := CompanionRestartProgram.widthSum_data A C K j p z v reserve w S.val.val
    have hh := CompanionRestartProgram.output_native_sameLaw A C K j hC hj hK hW hB p hxi z v reserve
      (fun i => by simpa only [reserve,List.length_replicate] using hdegree i)
      (fun i => by simpa only [reserve,List.length_replicate] using hdepth i) w S
    exact restart_append_joint_sameLaw (CompanionRestartProgram.baseData A C K j p z v reserve w S.val.val)
      n n hn (sourceRun S) hh padding
  have hf := flat_encoded_bind (wordLength A B) (n+padding) (CompanionInitialDraw.initialBits A B) (n+padding)
    init realInit encode run realRun hi hs
  intro phi
  have h := hf phi
  have he : (fun bits : Fin (wordLength A B+(n+padding)) → Bool =>
      (output (data A C K H T N R L j epsilon z v w estimates (List.ofFn bits)),
        (splitWordEquiv n padding (splitWordEquiv (wordLength A B) (n+padding) bits).2).2))=
      (fun bits => run (init (splitWordEquiv (wordLength A B) (n+padding) bits).1)
        (splitWordEquiv (wordLength A B) (n+padding) bits).2) := by
    funext bits
    apply Prod.ext
    · exact output_split A C K H T N R L j (n+padding) epsilon z v w estimates bits
    · rfl
  rw [he]
  exact h

theorem jointModel_sameLaw (A : Instance (Fin m) (Fin n)) (C K H T N R L j padding : ℕ)
    (epsilon : TreeFraction.Fraction) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ → LabelIndex A → LabelIndex A → TreeFraction.Fraction) :
    SameLaw (fun bits =>
      (encodeSet (coordinateOrder A) (jointModel A C K H T N R L j padding epsilon hK hW v w bits).1.val.val,
        (jointModel A C K H T N R L j padding epsilon hK hW v w bits).2))
      (fun bits :
        (Fin (CompanionInitialDraw.initialBits A
          (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
          CompanionRestartProgram.sumBits A C K j (parameters A H T N R L epsilon)) → Bool)×
          (Fin padding → Bool) =>
        (encodeSet (coordinateOrder A) (model A C K H T N R L j epsilon hK hW v w bits.1).val.val,bits.2)) := by
  let B := CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H)
  let p := parameters A H T N R L epsilon
  let widths := CompanionRestartProgram.sourceWidth A C K p
  exact nested_word_joint (CompanionInitialDraw.initialBits A B)
    (CompanionRestartProgram.sumBits A C K j p) padding
    (fun initBits stageBits => encodeSet (coordinateOrder A)
      (varyingWalk widths (CompanionRestartProgram.sourceStep A C K p hK hW v w)
        (CompanionInitialDraw.draw A B initBits) j (varyingWordEquiv widths j stageBits)).val.val)


end
end ContingencyTables.CompanionInitializedRestartProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionObservationQueriesLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact independent laws for the executed observation queries -/
namespace ContingencyTables.CompanionObservationQueriesProgram
open MatchingFPRAS DensePrograms GridBoundary FairBits CommonBasesFPRAS FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionArithmeticProposal
open CompanionOracleDensity CompanionWeightOracle
open scoped Classical
noncomputable section
attribute [local irreducible] queryWidth queryPair RootedLabelWeightProgram.output
  RootedLabelWeightProgram.config RootedEstimatorMedianProgram.context RootedEstimatorLayoutProgram.wordWidth

variable {m n : ℕ}
lemma queryWidth_config (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : ℚ)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) :
    queryWidth (RootedLabelWeightProgram.config A C K j xi xi z v degree depth)=
      medianEstimatorBits A C K j xi xi := by
  unfold queryWidth RootedLabelWeightProgram.config
  exact CompanionEvaluatedWeightProgram.queryWidth A C K j xi z v

lemma blockWidth_phaseConfigs (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : ℚ)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth nextDegree nextDepth : List Bool) :
    blockWidth (phaseConfigs A C K j xi z v degree depth nextDegree nextDepth)=
      CompanionPhaseWords.observationBits A C K j xi := by
  unfold blockWidth phaseConfigs CompanionPhaseWords.observationBits
  rw [queryWidth_config,queryWidth_config]

end
end ContingencyTables.CompanionObservationQueriesProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOuterPhaseSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal data and slices of a complete adaptive phase -/
namespace ContingencyTables.CompanionOuterPhaseProgram
open MatchingFPRAS CommonBasesFPRAS CompanionFactorialApplication CompanionComputedInitial
open CompanionComputedProposal CompanionArithmeticProposal CompanionEvaluatedWeightProgram
open CompanionMultiplierMatrixProgram CompanionOracleDensity GridBoundary
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ}

lemma phase_data (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ→LabelIndex A→LabelIndex A→TreeFraction.Fraction)
    (E : ℕ→TreeFraction.Fraction) (bits : List Bool) :
    phase (data A C K H T N R L j epsilon z v w E bits)=j := by
  simp only [phase,history,data,List.length_ofFn]

lemma old_data (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ→LabelIndex A→LabelIndex A→TreeFraction.Fraction)
    (E : ℕ→TreeFraction.Fraction) (bits : List Bool) :
    old (data A C K H T N R L j epsilon z v w E bits)=(matrixCode (w j),E j) := by
  rw [old,phase_data]
  cases j with
  | zero => rfl
  | succ j =>
    simp only [Nat.add_one_ne_zero,ite_false,history,data,Nat.add_sub_cancel,
      List.getD_eq_getElem?_getD,List.getElem?_ofFn,Nat.lt_succ_self,dite_true,Option.getD_some]

lemma restartInput_data (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ→LabelIndex A→LabelIndex A→TreeFraction.Fraction)
    (E : ℕ→TreeFraction.Fraction) (bits : List Bool) :
    restartInput (data A C K H T N R L j epsilon z v w E bits)=
      CompanionInitializedRestartProgram.data A C K H T N R L j epsilon z v w
        (fun i => E (i.val+1)) bits := rfl

lemma configAt_data (A : Instance (Fin m) (Fin n)) (C K H T N R L j i : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ→LabelIndex A→LabelIndex A→TreeFraction.Fraction)
    (E : ℕ→TreeFraction.Fraction) (bits : List Bool) :
    configAt i (data A C K H T N R L j epsilon z v w E bits)=
      RootedLabelWeightProgram.config A C K (j+i)
        (TreeFraction.val (CountingPhaseParametersProgram.noise
          (CompanionInitializedRestartProgram.parameters A H T N R L epsilon)))
        (TreeFraction.val (CountingPhaseParametersProgram.noise
          (CompanionInitializedRestartProgram.parameters A H T N R L epsilon))) z v
        (CompanionRestartStageProgram.degree A C K (j+i)
          (CompanionInitializedRestartProgram.parameters A H T N R L epsilon) z v bits)
        (CompanionRestartStageProgram.depth A C K (j+i)
          (CompanionInitializedRestartProgram.parameters A H T N R L epsilon) z v bits) := by
  unfold configAt contextInput
  rw [phase_data]
  change CompanionPhaseContextProgram.config (CompanionPhaseContextProgram.data A C K (j+i)
    (CompanionInitializedRestartProgram.parameters A H T N R L epsilon) z v (reserve _))=_
  rw [CompanionPhaseContextProgram.config_data,RootedOracleConfigProgram.output_data]
  simp only [reserve,data,List.map_const',List.length_replicate,
    CompanionRestartStageProgram.degree,CompanionRestartStageProgram.depth,
    CompanionRestartStageProgram.oracleData]



lemma restartWidth_data (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ→LabelIndex A→LabelIndex A→TreeFraction.Fraction)
    (E : ℕ→TreeFraction.Fraction) (bits : List Bool) :
    restartWidth (data A C K H T N R L j epsilon z v w E bits)=
      wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
        CompanionRestartProgram.sumBits A C K j
          (CompanionInitializedRestartProgram.parameters A H T N R L epsilon) := by
  unfold restartWidth restartRequest
  change CompanionRestartSchedule.width (CompanionRestartInitializer.data A C K H T N R L epsilon z v,_)=_
  rw [CompanionRestartSchedule.width,CompanionRestartInitializer.width_data,
    CompanionRestartSchedule.restartWidth_data]
  rw [show (history (data A C K H T N R L j epsilon z v w E bits)).length=j from
    phase_data A C K H T N R L j epsilon z v w E bits]
  rfl

end
end ContingencyTables.CompanionOuterPhaseProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionLabelMetadataProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering each paired label's cell and capacity

The multiplicities come from the actual bounded profile blocks. A
large numeric capacity never causes an allocation beyond the supplied
profile code. On a canonical code, the resulting order is exactly the
copy order used by the initializer and arithmetic proposals.
-/

namespace ContingencyTables.CompanionLabelMetadataProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open PairedProfileProgram PairedFactorialProgram

lemma labelRow_eq (i : ℕ) (xs : List ℕ) :
    labelRow (i,xs)=List.replicate (xs.length/2) (i,xs.length/2) := by
  simp only [labelRow,indices,pairCount,List.map_const',List.length_range]

noncomputable section
open CanonicalInitialEncoding InitialTransversals PairedProfileSemantics
open CompanionArithmeticProposal CompanionFactorialApplication
open scoped Classical
variable {q : ℕ} (b : Fin q → ℕ)

lemma indexedRow_encode (S : Set (Copy b × Bool)) (i : Fin q) :
    indexedRow ((List.ofFn b,encodeSet (coordinateEquiv b) S),i.val)=
      List.replicate (b i) (i.val,b i) := by
  unfold indexedRow rowInput
  rw [rows_encode]
  have he : (cellRows b S).getD i.val []=interleave (List.ofFn (fun k : Fin (b i) =>
      (if (⟨i,k⟩,false) ∈ S then 1 else 0,if (⟨i,k⟩,true) ∈ S then 1 else 0))) := by
    simp [cellRows,List.getD_eq_getElem?_getD]
  rw [he]
  rw [labelRow_eq,interleave_length,List.length_ofFn]
  simp only [Nat.mul_div_cancel_left _ (by decide : 0 < 2)]

lemma output_encode (S : Set (Copy b × Bool)) :
    output (List.ofFn b,encodeSet (coordinateEquiv b) S)=
      (copyOrder b).map (fun p => (p.1.val,b p.1)) := by
  unfold output NaturalBlockProgram.indices
  rw [List.length_ofFn]
  have he : (List.range q).map (fun i => indexedRow ((List.ofFn b,encodeSet (coordinateEquiv b) S),i))=
      List.ofFn (fun i : Fin q => List.replicate (b i) (i.val,b i)) := by
    conv_rhs => rw [List.ofFn_eq_map]
    rw [DirectedBFSCode.range_eq_map]
    simp only [List.map_map,Function.comp_def]
    change (List.finRange q).map (fun i => indexedRow ((List.ofFn b,encodeSet (coordinateEquiv b) S),i.val)) =
      (List.finRange q).map (fun i => List.replicate (b i) (i.val,b i))
    apply List.map_congr_left
    intro i _
    exact indexedRow_encode b S i
  rw [he]
  simp only [copyOrder,List.sigma,List.map_flatMap,List.map_map,List.ofFn_eq_map,
    List.flatten_eq_flatMap,List.flatMap_map,Function.comp_def,id_eq]
  apply List.flatMap_congr
  intro i _
  simp only [List.map_const',List.length_finRange]

end
end ContingencyTables.CompanionLabelMetadataProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitialMatrixProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the initial canonical multiplier matrix -/

namespace ContingencyTables.CompanionInitialMatrixProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped CompanionMultiplierMatrixProgram

lemma entry_val (a b : Metadata) :
    TreeFraction.val (entry (a,b))=
      if a.1=b.1 then 6 else 6*((a.2:ℚ)+1)/((b.2:ℚ)+2) := by
  unfold entry sameCell
  by_cases h : a.1=b.1
  · simp only [h,decide_true,ite_true, if_true,TreeFraction.val,Nat.cast_ofNat,Nat.cast_one,div_one]
  · simp only [h,decide_false,Bool.false_eq_true,ite_false]
    rw [TreeFraction.normalize_val]
    simp only [TreeFraction.val,numerator,denominator,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]

lemma matrix_ofFn {p : ℕ} (f : Fin p → Metadata) :
    matrix (List.ofFn f)=matrixCode (fun i j => entry (f i,f j)) := by
  simp only [matrix,row,matrixCode,List.map_ofFn,Function.comp_def]

noncomputable section
open CanonicalInitialEncoding InitialTransversals CompanionArithmeticProposal
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionRationalUpdates TwoLiftStates
open scoped Classical

variable {q : ℕ} (b : Fin q → ℕ)

lemma metadata_code (S : Set (Copy b × Bool)) :
    CompanionLabelMetadataProgram.output (List.ofFn b,encodeSet (coordinateEquiv b) S)=
      List.ofFn (metadataAt b) := by
  rw [CompanionLabelMetadataProgram.output_encode]
  let f : Copy b → Metadata := fun p => (p.1.val,b p.1)
  change (copyOrder b).map f=List.ofFn (fun i => f ((copyOrder b)[i.val]))
  exact (List.ofFn_getElem_eq_map (copyOrder b) f).symm

theorem output_code (S : Set (Copy b × Bool)) :
    output (List.ofFn b,encodeSet (coordinateEquiv b) S)=
      matrixCode (fun i j => entry (metadataAt b i,metadataAt b j)) := by
  rw [output,metadata_code,matrix_ofFn]

variable {m n : ℕ} (A : Instance (Fin m) (Fin n))

lemma pairLabels_cell (i : Fin (CanonicalInitialEncoding.copyOrder (capacities A)).length) :
    cellOrder A (pairLabels A i).1=(PairedCatalogProgram.labelOrder (capacities A) i).1 := by
  change cellOrder A ((cellOrder A).symm (PairedCatalogProgram.labelOrder (capacities A) i).1)=_
  exact (cellOrder A).apply_symm_apply _

lemma metadata_cell_iff (i j : Fin (CanonicalInitialEncoding.copyOrder (capacities A)).length) :
    (metadataAt (capacities A) i).1=(metadataAt (capacities A) j).1 ↔
      (pairLabels A i).1=(pairLabels A j).1 := by
  constructor
  · intro h
    apply (cellOrder A).injective
    rw [pairLabels_cell,pairLabels_cell]
    exact Fin.ext h
  · intro h
    have he := congrArg (fun s => (cellOrder A s).val) h
    simpa only [pairLabels_cell,metadataAt] using he

lemma metadata_capacity (i : Fin (CanonicalInitialEncoding.copyOrder (capacities A)).length) :
    (metadataAt (capacities A) i).2=A.b (pairLabels A i).1.val.1 (pairLabels A i).1.val.2 := by
  change capacities A (PairedCatalogProgram.labelOrder (capacities A) i).1=_
  rw [←pairLabels_cell]
  unfold capacities
  rw [Equiv.symm_apply_apply]

theorem initialEntries_val (i j : Fin (CanonicalInitialEncoding.copyOrder (capacities A)).length) :
    TreeFraction.val (initialEntries A i j)=
      CompanionRationalUpdates.initial A (pair (pairLabels A i)) (pair (pairLabels A j)) := by
  unfold initialEntries
  rw [entry_val]
  simp only [CompanionRationalUpdates.initial,TwoLiftStates.pair]
  simp only [metadata_cell_iff,metadata_capacity]
  by_cases h : (pairLabels A i).1=(pairLabels A j).1 <;> simp only [h,ite_true, if_true,ite_false]

theorem output_physical (S : Set (Labels A × Bool)) :
    output (List.ofFn (capacities A),encodeSet (coordinateOrder A) S)=
      matrixCode (initialEntries A) := by
  rw [encodeSet_reindex,output_code]
  rfl

end
end ContingencyTables.CompanionInitialMatrixProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitialStoredProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal initial count and stored multiplier matrix

The integer count is the product of the free-cell ranges and the small-cell
ranges. Both lists come from the executed forest and cell catalogs.
-/
namespace ContingencyTables.CompanionInitialStoredProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms

noncomputable section
open CompanionFactorialApplication CompanionComputedInitial ForestAssignmentSplit
open CompanionArithmeticProposal
open scoped BigOperators Classical
variable {m n : ℕ} (A : Instance (Fin m) (Fin n))

lemma rangeAt_data (ij : Fin m×Fin n) :
    rangeAt (RootedForestCatalog.data A,(ij.1.val,ij.2.val))=A.b ij.1 ij.2+1 := by
  unfold rangeAt RootedForestCatalog.data
  rw [matrixEntry_code]

lemma freeRanges_data : freeRanges (RootedForestCatalog.data A)=
    List.ofFn (fun i => A.b (RootedForestCatalog.freeEquiv A i).val.1
      (RootedForestCatalog.freeEquiv A i).val.2+1) := by
  unfold freeRanges
  conv_lhs => rw [←List.ofFn_get (RootedForestCatalog.catalog (RootedForestCatalog.data A,false))]
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply,List.get_eq_getElem]
  have h := RootedForestCatalog.catalogCell_coordinates A false i
  change ((RootedForestCatalog.freeEquiv A i).val.1.val,
    (RootedForestCatalog.freeEquiv A i).val.2.val)=_ at h
  rw [←h]
  exact rangeAt_data A _

theorem total_data (S : Set (Labels A×Bool)) :
    TreeFraction.val (total (data A S))=RootedStoredEstimate.initialTotal A := by
  unfold total data freeProduct smallProduct
  rw [freeRanges_data]
  simp only [List.prod_ofFn,List.map_ofFn,TreeFraction.val,Nat.cast_one,div_one,
    Nat.cast_mul,Nat.cast_prod]
  unfold RootedStoredEstimate.initialTotal
  congr 1
  · exact Fintype.prod_equiv (RootedForestCatalog.freeEquiv A) _ _ (fun _ => rfl)
  · exact Fintype.prod_equiv (cellOrder A).symm _ _ (fun _ => rfl)

theorem output_matrix (S : Set (Labels A×Bool)) :
    (output (data A S)).1=CompanionMultiplierMatrixProgram.matrixCode
      (CompanionInitialMatrixProgram.initialEntries A) :=
  CompanionInitialMatrixProgram.output_physical A S

end
end ContingencyTables.CompanionInitialStoredProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionStoredRepresentation
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact square-matrix representations along the physical phase loop

Successful updates construct every entry in catalog order. Aborted updates
retain the previous stored value, so the same representation supports the
readback used in the projected history law.
-/
namespace ContingencyTables.CompanionStoredRepresentation
open MatchingFPRAS CompanionMultiplierMatrixProgram

theorem readback {p : ℕ} {M : FractionMatrix} (h : MatrixRep p M) :
    matrixCode (entries p M)=M := by
  obtain ⟨w,rfl⟩ := h
  have he : entries p (matrixCode w)=w := by
    funext i j
    exact readEntry_code w i j
  rw [he]

theorem stored_readback {p : ℕ} {s : CompanionPhaseFinishProgram.Stored}
    (h : StoredRep p s) : (matrixCode (entries p s.1),s.2)=s := by
  exact Prod.ext (readback h) rfl

private theorem map_range_ofFn {α : Type} (f : ℕ→α) (p : ℕ) :
    (List.range p).map f=List.ofFn (fun i : Fin p => f i.val) := by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]

theorem updateMatrix_rep (z : CompanionMultiplierMatrixProgram.Input) :
    MatrixRep z.1.1.length (updateMatrix z) := by
  refine ⟨fun i j => updateEntry (z,(i.val,j.val)),?_⟩
  simp only [updateMatrix,updateRow,rowEntry,indices,map_range_ofFn,matrixCode]

theorem finish_output_rep (z : CompanionPhaseFinishProgram.Input)
    (s : CompanionPhaseFinishProgram.Stored)
    (h : CompanionPhaseFinishProgram.output z=some s) :
    StoredRep z.1.1.1.1.length s := by
  unfold CompanionPhaseFinishProgram.output at h
  split_ifs at h
  · cases Option.some.inj h
    exact updateMatrix_rep z.1.1

theorem observed_output_rep (z : CompanionObservedUpdateProgram.Input)
    (s : CompanionPhaseFinishProgram.Stored)
    (h : CompanionObservedUpdateProgram.output z=some s) :
    StoredRep z.1.2.1.1.1.length s :=
  finish_output_rep (CompanionObservedUpdateProgram.finishInput z) s h

theorem trial_output_rep (z : CompanionPhaseTrialProgram.Input)
    (s : CompanionPhaseFinishProgram.Stored)
    (h : CompanionPhaseTrialProgram.output z=some s) :
    StoredRep (CompanionPhaseTrialProgram.catalogue z).length s :=
  observed_output_rep (CompanionPhaseTrialProgram.updateInput z) s h

theorem trial_getD_rep {p : ℕ} (z : CompanionPhaseTrialProgram.Input)
    (old : CompanionPhaseFinishProgram.Stored) (hold : StoredRep p old)
    (hlen : (CompanionPhaseTrialProgram.catalogue z).length=p) :
    StoredRep p ((CompanionPhaseTrialProgram.output z).getD old) := by
  cases h : CompanionPhaseTrialProgram.output z with
  | none => simpa only [Option.getD_none] using hold
  | some s =>
    simpa only [Option.getD_some,hlen] using trial_output_rep z s h

theorem old_rep {p : ℕ} (z : CompanionOuterPhaseProgram.Input)
    (hinit : StoredRep p z.1.1.2)
    (hh : ∀ s∈z.1.2,StoredRep p s) :
    StoredRep p (CompanionOuterPhaseProgram.old z) := by
  unfold CompanionOuterPhaseProgram.old CompanionOuterPhaseProgram.phase
    CompanionOuterPhaseProgram.history
  split_ifs with he
  · exact hinit
  · have hi : z.1.2.length-1 < z.1.2.length := by omega
    rw [List.getD_eq_getElem _ _ hi]
    exact hh _ (List.getElem_mem hi)

theorem outer_output_rep {p : ℕ} (z : CompanionOuterPhaseProgram.Input)
    (hinit : StoredRep p z.1.1.2)
    (hh : ∀ s∈z.1.2,StoredRep p s)
    (hlen : (CompanionPhaseTrialProgram.catalogue
      (CompanionOuterPhaseProgram.trialInput z)).length=p) :
    StoredRep p (CompanionOuterPhaseProgram.output z) :=
  trial_getD_rep (CompanionOuterPhaseProgram.trialInput z)
    (CompanionOuterPhaseProgram.old z) (old_rep z hinit hh) hlen

noncomputable section
open CompanionFactorialApplication
open scoped Classical
variable {m n : ℕ} (A : Instance (Fin m) (Fin n))

theorem initial_output_rep (S : Set (Labels A×Bool)) :
    StoredRep (CanonicalInitialEncoding.copyOrder (CompanionComputedInitial.capacities A)).length
      (CompanionInitialStoredProgram.output (CompanionInitialStoredProgram.data A S)) :=
  ⟨CompanionInitialMatrixProgram.initialEntries A,CompanionInitialStoredProgram.output_matrix A S⟩

end
end ContingencyTables.CompanionStoredRepresentation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionHistoryReadback
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reading a represented physical history as source matrix data -/
namespace ContingencyTables.CompanionHistoryReadback
open MatchingFPRAS CompanionMultiplierMatrixProgram CompanionStoredRepresentation
open CompanionFactorialApplication CompanionComputedInitial CompanionEvaluatedWeightProgram
open GridBoundary
open scoped Classical
noncomputable section

lemma getD_rep {p : ℕ} (history : List Stored) (initial : Stored)
    (hi : StoredRep p initial) (hh : ∀ s∈history,StoredRep p s) (i : ℕ) :
    StoredRep p (history.getD i initial) := by
  by_cases h : i < history.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hh _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact hi

lemma lookup_rep {p : ℕ} (initial : Stored) (history : List Stored)
    (hi : StoredRep p initial) (hh : ∀ s∈history,StoredRep p s) (i : ℕ) :
    StoredRep p (lookup initial history i) := by
  cases i with
  | zero => exact hi
  | succ i => exact getD_rep history initial hi hh i

theorem lookup_readback {p : ℕ} (initial : Stored) (history : List Stored)
    (hi : StoredRep p initial) (hh : ∀ s∈history,StoredRep p s) (i : ℕ) :
    (matrixCode (matrixAt p initial history i),estimateAt initial history i)=
      lookup initial history i :=
  stored_readback (lookup_rep initial history hi hh i)

theorem initial_readback {p : ℕ} (initial : Stored) (history : List Stored)
    (hi : StoredRep p initial) :
    (matrixCode (matrixAt p initial history 0),estimateAt initial history 0)=initial :=
  stored_readback hi

theorem history_readback {p : ℕ} (initial : Stored) (history : List Stored)
    (hi : StoredRep p initial) (hh : ∀ s∈history,StoredRep p s) :
    List.ofFn (fun i : Fin history.length =>
      (matrixCode (matrixAt p initial history (i.val+1)),estimateAt initial history (i.val+1)))=
      history := by
  apply List.ext_getElem
  · exact List.length_ofFn
  · intro i _ hj
    simp only [List.getElem_ofFn]
    have h := lookup_readback initial history hi hh (i+1)
    change (matrixCode (matrixAt p initial history (i+1)),estimateAt initial history (i+1))=
      history.getD i initial at h
    rw [List.getD_eq_getElem _ _ hj] at h
    exact h

theorem view_lookup (p : ℕ) (initial : Stored) (history : List Stored) (i : ℕ) :
    CompanionPhaseFinishProgram.view (p := p) (lookup initial history i)=
      viewLookup (CompanionPhaseFinishProgram.view (p := p) initial)
        (history.map (CompanionPhaseFinishProgram.view (p := p))) i := by
  cases i with
  | zero => rfl
  | succ i => exact (List.getD_map history initial
      (CompanionPhaseFinishProgram.view (p := p))).symm

theorem old_eq_lookup (fixed : CompanionOuterHistoryProgram.Fixed) (history : List Stored)
    (bits : List Bool) :
    CompanionOuterPhaseProgram.old ((fixed,history),bits)=lookup fixed.2 history history.length := by
  cases history with
  | nil => rfl
  | cons s history =>
    change (s::history).getD history.length default=(s::history).getD history.length fixed.2
    rw [List.getD_eq_getElem _ _ (by simp : history.length < (s::history).length),
      List.getD_eq_getElem _ _ (by simp : history.length < (s::history).length)]

theorem view_old (p : ℕ) (fixed : CompanionOuterHistoryProgram.Fixed) (history : List Stored)
    (bits : List Bool) :
    CompanionPhaseFinishProgram.view (p := p) (CompanionOuterPhaseProgram.old ((fixed,history),bits))=
      viewLookup (CompanionPhaseFinishProgram.view (p := p) fixed.2)
        (history.map (CompanionPhaseFinishProgram.view (p := p))) history.length := by
  rw [old_eq_lookup,view_lookup]

theorem view_old_canonical {I J : Type} [Fintype I] [Fintype J]
    (A : Instance I J) {p : ℕ} (g : Fin p ≃ Labels A)
    (fixed : CompanionOuterHistoryProgram.Fixed) (history : List Stored) (bits : List Bool)
    (hi : CompanionPhaseFinishProgram.view (p := p) fixed.2=
      CompanionCanonicalHistory.project A g (RootedStoredEstimate.initialStored A)) :
    CompanionPhaseFinishProgram.view (p := p) (CompanionOuterPhaseProgram.old ((fixed,history),bits))=
      CompanionCanonicalHistory.canonicalLookup A g
        (history.map (CompanionPhaseFinishProgram.view (p := p))) history.length := by
  rw [view_old,hi]
  rfl

variable {m n : ℕ}

theorem outer_data_readback (A : Instance (Fin m) (Fin n)) (C K H T N R L : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (initial : Stored) (history : List Stored)
    (hi : StoredRep (CanonicalInitialEncoding.copyOrder (capacities A)).length initial)
    (hh : ∀ s∈history,StoredRep (CanonicalInitialEncoding.copyOrder (capacities A)).length s)
    (bits : List Bool) :
    CompanionOuterPhaseProgram.data A C K H T N R L history.length epsilon z v
      (matrixAt (CanonicalInitialEncoding.copyOrder (capacities A)).length initial history)
      (estimateAt initial history) bits=
      (((CompanionRestartInitializer.data A C K H T N R L epsilon z v,initial),history),bits) := by
  unfold CompanionOuterPhaseProgram.data
  rw [initial_readback initial history hi,history_readback initial history hi hh]

end
end ContingencyTables.CompanionHistoryReadback

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuing an adaptive phase from its initialized profile -/
namespace ContingencyTables.CompanionPhaseContinuation
open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram
open CompanionOracleDensity CompanionWeightOracle GridBoundary FiniteObservableTransport CommonBasesFPRAS TwoLiftStates
open scoped Classical
noncomputable section

lemma outer_eq (z : CompanionOuterPhaseProgram.Input) :
    CompanionOuterPhaseProgram.output z=
      run (CompanionOuterPhaseProgram.configAt 0 z,CompanionOuterPhaseProgram.configAt 1 z)
        (CompanionOuterPhaseProgram.old z) (CompanionOuterPhaseProgram.precision z)
        (CompanionOuterPhaseProgram.observations z) (CompanionOuterPhaseProgram.startCode z)
        (CompanionOuterPhaseProgram.afterRestart z) := rfl

end
end ContingencyTables.CompanionPhaseContinuation

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartContinuation
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binding a restart law to its independent phase continuation -/
namespace ContingencyTables.FiniteObservableTransport
open CommonBasesFPRAS
noncomputable section

theorem joint_encoded_bind {A B U V C Z W : Type*}
    [Fintype A] [Fintype B] [Fintype U] [Fintype V]
    (f : A → C×U) (g : B → Z) (e : Z → C)
    (F : C → U → W) (G : Z → V → W)
    (hinit : SameLaw f (fun p : B×U => (e (g p.1),p.2)))
    (hstep : ∀ z,SameLaw (F (e z)) (G z)) :
    SameLaw (fun a => F (f a).1 (f a).2) (fun p : B×V => G (g p.1) p.2) := by
  intro phi
  have hi := hinit (fun p => phi (F p.1 p.2))
  refine hi.trans ?_
  rw [uniformAverage_prod,uniformAverage_prod]
  apply congrArg uniformAverage
  funext b
  exact hstep (g b) phi

end
end ContingencyTables.FiniteObservableTransport

namespace ContingencyTables.CompanionOuterPhaseProgram
open MatchingFPRAS CommonBasesFPRAS CompanionFactorialApplication CompanionComputedInitial
open CompanionComputedProposal CompanionArithmeticProposal CompanionEvaluatedWeightProgram
open CompanionMultiplierMatrixProgram CompanionOracleDensity GridBoundary FiniteObservableTransport
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma output_data_run (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ→LabelIndex A→LabelIndex A→TreeFraction.Fraction)
    (E : ℕ→TreeFraction.Fraction) (reserve bits : List Bool)
    (hlen : bits.length=reserve.length) :
    output (data A C K H T N R L j epsilon z v w E bits)=
      CompanionPhaseContinuation.run (configs A C K H T N R L j epsilon z v reserve)
        (matrixCode (w j),E j)
        (CountingPhaseParametersProgram.precision
          (CompanionInitializedRestartProgram.parameters A H T N R L epsilon))
        (CountingPhaseParametersProgram.observations
          (CompanionInitializedRestartProgram.parameters A H T N R L epsilon))
        (CompanionInitializedRestartProgram.output
          (CompanionInitializedRestartProgram.data A C K H T N R L j epsilon z v w
            (fun i => E (i.val+1)) bits))
        (bits.drop (wordLength A
          (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
          CompanionRestartProgram.sumBits A C K j
            (CompanionInitializedRestartProgram.parameters A H T N R L epsilon))) := by
  rw [CompanionPhaseContinuation.outer_eq,configAt_data,configAt_data,old_data]
  unfold startCode afterRestart
  rw [restartInput_data,restartWidth_data]
  simp only [Nat.add_zero]
  unfold configs CompanionObservationQueriesProgram.phaseConfigs
  simp only [CompanionRestartStageProgram.degree,CompanionRestartStageProgram.depth,
    CompanionRestartStageProgram.oracleData,hlen]
  rfl

end
end ContingencyTables.CompanionOuterPhaseProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOuterPhaseLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Law of an executed outer phase, including its initialized restart -/
namespace ContingencyTables.CompanionOuterPhaseProgram
open MatchingFPRAS CommonBasesFPRAS FirstSuccess FairBits CompanionFactorialApplication
open CompanionComputedInitial CompanionComputedProposal CompanionArithmeticProposal
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram CompanionOracleDensity
open GridBoundary FiniteObservableTransport TwoLiftStates
open scoped Classical
noncomputable section
variable {m n : ℕ}

attribute [local irreducible] CompanionInitializedRestartProgram.output
  CompanionInitializedRestartProgram.model CompanionInitializedRestartProgram.jointModel
  CompanionPhaseContinuation.run CompanionOuterPhaseProgram.output

theorem output_sameLaw (A : Instance (Fin m) (Fin n)) (C K H T N R L j padding : ℕ)
    (hC : 0<C) (hj : j+1 ≤ rationalHeight A C) (hK : 1≤K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (epsilon : TreeFraction.Fraction)
    (hxi : 0<TreeFraction.val (CountingPhaseParametersProgram.noise
      (CompanionInitializedRestartProgram.parameters A H T N R L epsilon)))
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (reserve : List Bool)
    (hlen : reserve.length=phaseWordWidth A C K H T N R L j epsilon z v reserve padding)
    (hdegree : ∀ i,i ≤ j+1 → PowerOfTwoApproximation.rootDegree
      (roundingTolerance (innerTolerance (TreeFraction.val (CountingPhaseParametersProgram.noise
        (CompanionInitializedRestartProgram.parameters A H T N R L epsilon))/2) i)) ≤ reserve.length)
    (hdepth : ∀ i,i ≤ j+1 → PowerOfTwoApproximation.depth
      (roundingTolerance (innerTolerance (TreeFraction.val (CountingPhaseParametersProgram.noise
        (CompanionInitializedRestartProgram.parameters A H T N R L epsilon))/2) i)) ≤ reserve.length)
    (old : CompanionPhaseWords.Stored A)
    (w : ℕ→LabelIndex A→LabelIndex A→TreeFraction.Fraction)
    (E : ℕ→TreeFraction.Fraction)
    (hw : ∀ a b,TreeFraction.val (w j a b)=old.multiplier (pair (pairLabels A a)) (pair (pairLabels A b)))
    (hE : TreeFraction.val (E j)=old.estimate) :
    let p := CompanionInitializedRestartProgram.parameters A H T N R L epsilon
    let xi := TreeFraction.val (CountingPhaseParametersProgram.noise p)
    let k := CountingPhaseParametersProgram.precision p
    let obs := CountingPhaseParametersProgram.observations p
    SameLaw (fun bits : Fin (phaseWordWidth A C K H T N R L j epsilon z v reserve padding)→Bool =>
      CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)
        (output (data A C K H T N R L j epsilon z v w E (List.ofFn bits))))
      (fun bits : (Fin (CompanionInitialDraw.initialBits A
          (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
          CompanionRestartProgram.sumBits A C K j p)→Bool)×RootedPhaseTrial.TrialWords A C K j k obs xi =>
        CompanionPhaseFinishProgram.storedView A (pairLabels A)
          ((RootedPhaseTrial.trial A (RootedCompletion.rowColumn A.T) C K j k obs hK hW xi
            (RootedCatalogGrid.gridEquiv A K v) old
            (CompanionInitializedRestartProgram.model A C K H T N R L j epsilon hK hW v w bits.1).val
            bits.2).getD old)) := by
  dsimp only
  let p := CompanionInitializedRestartProgram.parameters A H T N R L epsilon
  let xi := TreeFraction.val (CountingPhaseParametersProgram.noise p)
  let k := CountingPhaseParametersProgram.precision p
  let obs := CountingPhaseParametersProgram.observations p
  let a := wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))
  let b := CompanionRestartProgram.sumBits A C K j p
  let tail := tailWidth A C K H T N R L j epsilon z v reserve padding
  let cs := configs A C K H T N R L j epsilon z v reserve
  let project := CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)
  have hd (i : ℕ) (hi : i ≤ j+1) :
      (CompanionRestartStageProgram.degree A C K i p z v reserve).length=
        PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) i)) := by
    unfold CompanionRestartStageProgram.degree CompanionRestartStageProgram.oracleData
    rw [List.length_take,List.length_replicate,RootedOracleConfigProgram.rootDegree_data,
      min_eq_left (hdegree i hi)]
  have ht (i : ℕ) (hi : i ≤ j+1) :
      (CompanionRestartStageProgram.depth A C K i p z v reserve).length=
        PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) i)) := by
    unfold CompanionRestartStageProgram.depth CompanionRestartStageProgram.oracleData
    rw [List.length_take,List.length_replicate,RootedOracleConfigProgram.depth_data,
      min_eq_left (hdepth i hi)]
  have hi := CompanionInitializedRestartProgram.output_joint_sameLaw A C K H T N R L j tail
    hC (by omega) hK hW hB epsilon hxi z v w (fun i => E (i.val+1))
    (fun i => by
      unfold CompanionRestartStageProgram.oracleData
      rw [RootedOracleConfigProgram.rootDegree_data]
      exact (hdegree (i.val+1) (by omega)).trans_eq hlen)
    (fun i => by
      unfold CompanionRestartStageProgram.oracleData
      rw [RootedOracleConfigProgram.depth_data]
      exact (hdepth (i.val+1) (by omega)).trans_eq hlen)
  have hi' := fun phi => (hi phi).trans
    ((CompanionInitializedRestartProgram.jointModel_sameLaw A C K H T N R L j tail
      epsilon hK hW v w) phi)
  let F := fun code (bits : Fin tail→Bool) =>
    project (CompanionPhaseContinuation.run cs (matrixCode (w j),E j) k obs code (List.ofFn bits))
  let G := fun (S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A)))
      (bits : RootedPhaseTrial.TrialWords A C K j k obs xi) =>
    CompanionPhaseFinishProgram.storedView A (pairLabels A)
      ((RootedPhaseTrial.trial A (RootedCompletion.rowColumn A.T) C K j k obs hK hW xi
        (RootedCatalogGrid.gridEquiv A K v) old S.val bits).getD old)
  have hs (S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A))) :
      SameLaw (F (encodeSet (coordinateOrder A) S.val.val)) (G S) :=
    CompanionPhaseContinuation.run_sameLaw padding A C K j k obs hC hj hK hW hB xi hxi z v
      (CompanionRestartStageProgram.degree A C K j p z v reserve)
      (CompanionRestartStageProgram.depth A C K j p z v reserve)
      (CompanionRestartStageProgram.degree A C K (j+1) p z v reserve)
      (CompanionRestartStageProgram.depth A C K (j+1) p z v reserve)
      (hd j (by omega)) (ht j (by omega)) (hd (j+1) le_rfl) (ht (j+1) le_rfl)
      old (w j) (E j) hw hE S.val
  have hh := joint_encoded_bind _
    (CompanionInitializedRestartProgram.model A C K H T N R L j epsilon hK hW v w)
    (fun S => encodeSet (coordinateOrder A) S.val.val) F G hi' hs
  intro phi
  have he (bits : Fin (a+(b+tail))→Bool) :
      project (output (data A C K H T N R L j epsilon z v w E (List.ofFn bits)))=
      F (CompanionInitializedRestartProgram.output
        (CompanionInitializedRestartProgram.data A C K H T N R L j epsilon z v w
          (fun i => E (i.val+1)) (List.ofFn bits)))
        (splitWordEquiv b tail (splitWordEquiv a (b+tail) bits).2).2 := by
    dsimp only [F]
    rw [output_data_run A C K H T N R L j epsilon z v w E reserve (List.ofFn bits)
      (by rw [List.length_ofFn]; exact hlen.symm)]
    congr 2
    rw [←List.drop_drop,DensePrograms.ofFn_split_drop,DensePrograms.ofFn_split_drop]
  change uniformAverage (fun bits : Fin (a+(b+tail))→Bool =>
    phi (project (output (data A C K H T N R L j epsilon z v w E (List.ofFn bits)))))=_
  simp_rw [he]
  exact hh phi

end
end ContingencyTables.CompanionOuterPhaseProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOuterWidths
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed phase widths and the source history word

The supplied precision markers do not contribute to the number of oracle
bits. After identifying the computed scalar controls, the complete phase
width is the source width plus its unused padding.
-/
namespace ContingencyTables.CompanionOuterWidths
open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial
open CompanionOracleDensity GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma configs_blockWidth (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    CompanionObservationQueriesProgram.blockWidth
      (CompanionOuterPhaseProgram.configs A C K H T N R L j epsilon z v reserve)=
      CompanionPhaseWords.observationBits A C K j
        (TreeFraction.val (CountingPhaseParametersProgram.noise
          (CompanionInitializedRestartProgram.parameters A H T N R L epsilon))) := by
  unfold CompanionOuterPhaseProgram.configs
  exact CompanionObservationQueriesProgram.blockWidth_phaseConfigs A C K j _ z v _ _ _ _

lemma initialWidth_eq (A : Instance (Fin m) (Fin n)) (C K H N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) :
    wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
      CompanionRestartProgram.sumBits A C K j
        (CompanionInitializedRestartProgram.parameters A H
          (CompanionTargetMixing.restartTime A H L) N R L epsilon)=
      RootedRestartWords.initialStageBits A C K H L
        (CountingPhaseParametersProgram.precision
          (CompanionInitializedRestartProgram.parameters A H
            (CompanionTargetMixing.restartTime A H L) N R L epsilon))
        R (CountingPhaseSchedule.initialPrecision H) j
        (TreeFraction.val (CountingPhaseParametersProgram.noise
          (CompanionInitializedRestartProgram.parameters A H
            (CompanionTargetMixing.restartTime A H L) N R L epsilon))) := by
  rw [CompanionRestartSchedule.initialWidths_eq]
  rfl

theorem phaseWidth_source (A : Instance (Fin m) (Fin n))
    (s : RootedPhaseHistory.Settings A) (N j : ℕ) (epsilon : TreeFraction.Fraction)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) s.K)
    (reserve : List Bool) (padding : ℕ)
    (hk : CountingPhaseParametersProgram.precision
      (CompanionInitializedRestartProgram.parameters A s.H
        (CompanionTargetMixing.restartTime A s.H s.L) N s.n s.L epsilon)=s.k)
    (hN : CountingPhaseParametersProgram.observations
      (CompanionInitializedRestartProgram.parameters A s.H
        (CompanionTargetMixing.restartTime A s.H s.L) N s.n s.L epsilon)=s.N)
    (hh : CountingPhaseSchedule.initialPrecision s.H=s.h)
    (hxi : TreeFraction.val (CountingPhaseParametersProgram.noise
      (CompanionInitializedRestartProgram.parameters A s.H
        (CompanionTargetMixing.restartTime A s.H s.L) N s.n s.L epsilon))=s.xi) :
    phaseWidth A s.C s.K s.H (CompanionTargetMixing.restartTime A s.H s.L)
      N s.n s.L j epsilon z v reserve padding=RootedPhaseHistory.width A s j+padding := by
  unfold phaseWidth tailWidth
  rw [configs_blockWidth]
  rw [←Nat.add_assoc,initialWidth_eq]
  simp only [hk,hN,hh,hxi,RootedPhaseHistory.width,CompanionPhaseWords.phaseBits,Nat.add_assoc]

end
end ContingencyTables.CompanionOuterWidths

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCanonicalPhaseLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The projected law of one complete physical counting phase -/
namespace ContingencyTables.CompanionCanonicalPhaseLaw
open MatchingFPRAS CommonBasesFPRAS FirstSuccess FairBits FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram CompanionCanonicalHistory
open CompanionHistoryReadback CompanionStoredRepresentation CompanionOracleDensity
open CompanionRationalUpdates TwoLiftStates GridBoundary
open scoped Classical
noncomputable section

lemma prefix_sameLaw {Z : Type*} {k N : ℕ} (hk : k ≤ N) (f : (Fin k→Bool)→Z) :
    SameLaw (fun bits : Fin N→Bool => f (prefixWord hk bits)) f := by
  intro phi
  have he := uniformAverage_equiv (paddingWordEquiv hk)
    (fun p : (Fin k→Bool)×(Fin (N-k)→Bool) => phi (f p.1))
  simp only [paddingWordEquiv_fst] at he
  rw [uniformAverage_prod] at he
  simpa only [uniformAverage_const] using he

theorem canonicalStep_sameLaw {I J : Type} [Fintype I] [Fintype J]
    (A : Instance I J) {p : ℕ} (g : Fin p ≃ Labels A)
    (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (history : List (Canonical (p := p))) (hj : history.length < s.H) :
    SameLaw (fun bits : RootedPhaseHistory.Word A s => canonicalStep A g R s history bits)
      (canonicalResult A g R s history history.length) := by
  let f := fun bits : Fin (RootedPhaseHistory.width A s history.length)→Bool =>
    canonicalResult A g R s history history.length (RootedPhaseHistory.split A s history.length bits)
  have hp := prefix_sameLaw (RootedPhaseHistory.width_le A s history.length hj) f
  intro phi
  have he := uniformAverage_equiv (RootedPhaseHistory.split A s history.length)
    (fun bits => phi (canonicalResult A g R s history history.length bits))
  have hf (bits : RootedPhaseHistory.Word A s) :
      canonicalStep A g R s history bits=
        f (prefixWord (RootedPhaseHistory.width_le A s history.length hj) bits) := by
    unfold canonicalStep RootedPhaseHistory.step
    rw [show (history.map (extend A g)).length=history.length from List.length_map _]
    rw [dite_eq_left hj]
    rfl
  simp_rw [hf]
  exact (hp phi).trans he

private theorem project_getD {I J : Type} [Fintype I] [Fintype J]
    (A : Instance I J) {p : ℕ} (g : Fin p ≃ Labels A)
    (a b : Option (CompanionPhaseWords.Stored A)) (s t : CompanionPhaseWords.Stored A)
    (h : a.map (project A g)=b.map (project A g)) (he : project A g s=project A g t) :
    project A g (a.getD s)=project A g (b.getD t) := by
  cases a <;> cases b <;> simp_all

variable {m n : ℕ}

theorem rawSettings_eq (A : Instance (Fin m) (Fin n)) (s : RootedPhaseHistory.Settings A)
    (N : ℕ) (epsilon : TreeFraction.Fraction)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) s.K)
    (hk : CountingPhaseParametersProgram.precision
      (CompanionInitializedRestartProgram.parameters A s.H
        (CompanionTargetMixing.restartTime A s.H s.L) N s.n s.L epsilon)=s.k)
    (hN : CountingPhaseParametersProgram.observations
      (CompanionInitializedRestartProgram.parameters A s.H
        (CompanionTargetMixing.restartTime A s.H s.L) N s.n s.L epsilon)=s.N)
    (hh : CountingPhaseSchedule.initialPrecision s.H=s.h)
    (hxi : TreeFraction.val (CountingPhaseParametersProgram.noise
      (CompanionInitializedRestartProgram.parameters A s.H
        (CompanionTargetMixing.restartTime A s.H s.L) N s.n s.L epsilon))=s.xi)
    (hv : RootedCatalogGrid.gridEquiv A s.K v=s.v) :
    rawSettings A s.C s.K s.H N s.n s.L epsilon s.hK s.hW v=s := by
  cases s
  dsimp only at hk hN hh hxi hv ⊢
  unfold rawSettings
  congr 1

lemma sourceStored_project (A : Instance (Fin m) (Fin n))
    (initial : CompanionPhaseFinishProgram.Stored) (history : List CompanionPhaseFinishProgram.Stored)
    (i : ℕ) :
    project A (pairLabels A) (sourceStored A initial history i)=
      CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)
        (lookup initial history i) := by
  apply Prod.ext
  · funext a b
    simp only [project,CompanionPhaseFinishProgram.storedView,sourceStored,sourceWeights,pair,
      Equiv.symm_apply_apply,matrixAt,entries,CompanionPhaseFinishProgram.view]
  · rfl

lemma sourceStored_lookup (A : Instance (Fin m) (Fin n))
    (initial : CompanionPhaseFinishProgram.Stored) (history : List CompanionPhaseFinishProgram.Stored)
    (hi : CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)
      initial=project A (pairLabels A) (RootedStoredEstimate.initialStored A)) (i : ℕ) :
    project A (pairLabels A) (sourceStored A initial history i)=
      project A (pairLabels A) (RootedStoredHistory.lookup A
        ((history.map (CompanionPhaseFinishProgram.view
          (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length))).map (extend A (pairLabels A))) i) := by
  rw [sourceStored_project,view_lookup,CompanionCanonicalHistory.lookup_project]
  simp only [List.map_map,Function.comp_def,project_extend]
  rw [hi]
  rfl

lemma readbackResult_eq (A : Instance (Fin m) (Fin n)) (s : RootedPhaseHistory.Settings A)
    (initial : CompanionPhaseFinishProgram.Stored) (history : List CompanionPhaseFinishProgram.Stored)
    (hi : CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)
      initial=project A (pairLabels A) (RootedStoredEstimate.initialStored A))
    (bits : RootedRestartTrial.Words A s.C s.K s.H s.L history.length s.k s.n s.N s.h s.xi) :
    readbackResult A s initial history bits=
      canonicalResult A (pairLabels A) (RootedCompletion.rowColumn A.T) s
        (history.map (CompanionPhaseFinishProgram.view
          (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length))) history.length bits := by
  let hs := (history.map (CompanionPhaseFinishProgram.view
    (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length))).map (extend A (pairLabels A))
  have hp (i : ℕ) := sourceStored_lookup A initial history hi i
  have ho := restart_project_eq A (pairLabels A) (RootedCompletion.rowColumn A.T)
    s.C s.K s.H s.L history.length s.k s.n s.N s.h s.hK s.hW s.xi s.v
    (fun i => (sourceStored A initial history i).multiplier)
    (fun i => (RootedStoredHistory.lookup A hs i).multiplier)
    (sourceStored A initial history history.length).estimate
    (RootedStoredHistory.lookup A hs history.length).estimate
    (fun i _ => ((project_eq_iff A (pairLabels A) _ _).mp (hp i)).1)
    (((project_eq_iff A (pairLabels A) _ _).mp (hp history.length)).2) bits
  exact project_getD A (pairLabels A) _ _ _ _ ho (hp history.length)

theorem output_sameLaw (A : Instance (Fin m) (Fin n)) (C K H N R L W : ℕ)
    (epsilon : TreeFraction.Fraction) (hC : 0 < C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hxi : 0 < TreeFraction.val (CountingPhaseParametersProgram.noise
      (CompanionInitializedRestartProgram.parameters A H
        (CompanionTargetMixing.restartTime A H L) N R L epsilon)))
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (initial : CompanionPhaseFinishProgram.Stored) (history : List CompanionPhaseFinishProgram.Stored)
    (hj : history.length < H) (hphase : history.length+1 ≤ rationalHeight A C)
    (hwidth : RootedPhaseHistory.totalWidth A (rawSettings A C K H N R L epsilon hK hW v) ≤ W)
    (hdegree : ∀ i,i ≤ history.length+1 → PowerOfTwoApproximation.rootDegree
      (roundingTolerance (innerTolerance
        ((rawSettings A C K H N R L epsilon hK hW v).xi/2) i)) ≤ W)
    (hdepth : ∀ i,i ≤ history.length+1 → PowerOfTwoApproximation.depth
      (roundingTolerance (innerTolerance
        ((rawSettings A C K H N R L epsilon hK hW v).xi/2) i)) ≤ W)
    (hinit : StoredRep (CanonicalInitialEncoding.copyOrder (capacities A)).length initial)
    (hh : ∀ q∈history,StoredRep (CanonicalInitialEncoding.copyOrder (capacities A)).length q)
    (hi : CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)
      initial=project A (pairLabels A) (RootedStoredEstimate.initialStored A)) :
    let s := rawSettings A C K H N R L epsilon hK hW v
    SameLaw (fun bits : Fin W→Bool =>
      CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)
        (CompanionOuterPhaseProgram.output
          (((CompanionRestartInitializer.data A C K H
            (CompanionTargetMixing.restartTime A H L) N R L epsilon z v,initial),history),List.ofFn bits)))
      (fun bits : RootedPhaseHistory.Word A s => canonicalStep A (pairLabels A)
        (RootedCompletion.rowColumn A.T) s
        (history.map (CompanionPhaseFinishProgram.view
          (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length))) bits) := by
  dsimp only
  let s := rawSettings A C K H N R L epsilon hK hW v
  let j := history.length
  let t := CompanionTargetMixing.restartTime A H L
  let reserve := List.replicate W false
  let padding := W-RootedPhaseHistory.width A s j
  let w := matrixAt (CanonicalInitialEncoding.copyOrder (capacities A)).length initial history
  let E := estimateAt initial history
  let view := CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)
  have hbound : RootedPhaseHistory.width A s j ≤ W :=
    (RootedPhaseHistory.width_le A s j hj).trans hwidth
  have hsize : CompanionOuterPhaseProgram.phaseWordWidth A C K H t N R L j
      epsilon z v reserve padding=W := by
    have h := CompanionOuterWidths.phaseWidth_source A s N j epsilon z v reserve padding
      rfl rfl rfl rfl
    change CompanionOuterPhaseProgram.phaseWordWidth A C K H t N R L j
      epsilon z v reserve padding=RootedPhaseHistory.width A s j+padding at h
    exact h.trans (Nat.add_sub_of_le hbound)
  have hw (a b : LabelIndex A) : TreeFraction.val (w j a b)=
      (sourceStored A initial history j).multiplier (pair (pairLabels A a)) (pair (pairLabels A b)) := by
    simp only [sourceStored,sourceWeights,pair,Equiv.symm_apply_apply]
    rfl
  have hbase := CompanionOuterPhaseProgram.output_sameLaw A C K H t N R L j padding
    hC hphase hK hW hB epsilon hxi z v reserve
    (by simpa only [reserve,List.length_replicate] using hsize.symm)
    (fun i hi => by rw [List.length_replicate]; exact hdegree i hi)
    (fun i hi => by rw [List.length_replicate]; exact hdepth i hi)
    (sourceStored A initial history j) w E hw rfl
  have hsource : SameLaw
      (fun bits : Fin (CompanionOuterPhaseProgram.phaseWordWidth A C K H t N R L j
        epsilon z v reserve padding)→Bool => view
          (CompanionOuterPhaseProgram.output
            (CompanionOuterPhaseProgram.data A C K H t N R L j epsilon z v w E (List.ofFn bits))))
      (readbackResult A s initial history) := hbase
  have hp := SameLaw.word_length hsize
    (fun bs => view (CompanionOuterPhaseProgram.output
      (CompanionOuterPhaseProgram.data A C K H t N R L j epsilon z v w E bs)))
    (readbackResult A s initial history) hsource
  have hphysical : SameLaw
      (fun bits : Fin W→Bool => view (CompanionOuterPhaseProgram.output
        (((CompanionRestartInitializer.data A C K H t N R L epsilon z v,initial),history),List.ofFn bits)))
      (readbackResult A s initial history) := by
    intro phi
    have hd (bits : Fin W→Bool) :
        CompanionOuterPhaseProgram.data A C K H t N R L j epsilon z v w E (List.ofFn bits)=
          (((CompanionRestartInitializer.data A C K H t N R L epsilon z v,initial),history),List.ofFn bits) :=
      outer_data_readback A C K H t N R L epsilon z v initial history hinit hh _
    simpa only [hd] using hp phi
  have href : SameLaw (readbackResult A s initial history)
      (canonicalResult A (pairLabels A) (RootedCompletion.rowColumn A.T) s
        (history.map view) j) := by
    intro phi
    apply congrArg uniformAverage
    funext bits
    rw [readbackResult_eq A s initial history hi bits]
  have hc := canonicalStep_sameLaw A (pairLabels A) (RootedCompletion.rowColumn A.T) s
    (history.map view) (by rw [List.length_map]; exact hj)
  rw [List.length_map] at hc
  intro phi
  exact (hphysical phi).trans ((href phi).trans (hc phi).symm)

end
end ContingencyTables.CompanionCanonicalPhaseLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteSameLawSupport
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise support transfer for finite uniform experiments -/
namespace ContingencyTables.FiniteObservableTransport
open CommonBasesFPRAS
open scoped BigOperators Classical
noncomputable section

theorem SameLaw.property {X Y Z : Type*} [Fintype X] [Fintype Y]
    {f : X→Z} {g : Y→Z} (h : SameLaw f g) (P : Z→Prop)
    (hg : ∀ y,P (g y)) (x : X) : P (f x) := by
  by_contra hx
  let bad : Z→ℝ := fun z => if P z then 0 else 1
  have he := h bad
  have hz : uniformAverage (fun y => bad (g y))=0 := by
    simp only [bad,hg,ite_true, if_true,uniformAverage,Finset.sum_const_zero,zero_div]
  rw [hz] at he
  have hnonneg (t : X) : 0 ≤ bad (f t) := by
    dsimp only [bad]
    split_ifs <;> norm_num
  have hsum : (∑ t : X,bad (f t))=0 := by
    rcases (div_eq_zero_iff).mp he with he'|he'
    · exact he'
    · have hc : Fintype.card X≠0 := by
        let : Nonempty X := ⟨x⟩
        exact Fintype.card_ne_zero
      exact False.elim (hc (by exact_mod_cast he'))
  have hb := Finset.single_le_sum (fun t _ => hnonneg t) (Finset.mem_univ x)
  rw [hsum] at hb
  simp only [bad,hx,ite_false] at hb
  norm_num at hb

theorem SameLaw.exists_preimage {X Y Z : Type*} [Fintype X] [Fintype Y]
    {f : X→Z} {g : Y→Z} (h : SameLaw f g) (x : X) : ∃ y,g y=f x :=
  h.property (fun z => ∃ y,g y=z) (fun y => ⟨y,rfl⟩) x

end
end ContingencyTables.FiniteObservableTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartSupport
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every executed restart has the canonical paired catalog

Finite uniform words have positive mass individually. The proved padded
restart law therefore gives a valid encoded source state on every word,
including words on which one of the return attempts uses its fallback.
-/
namespace ContingencyTables.CompanionInitializedRestartProgram
open MatchingFPRAS CommonBasesFPRAS FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionEvaluatedWeightProgram
open CompanionOracleDensity TwoLiftStates GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma catalog_length_encode (A : Instance (Fin m) (Fin n)) (S : Set (Labels A×Bool)) :
    (PairedCatalogProgram.catalog (encodeSet (coordinateOrder A) S)).length=
      (CanonicalInitialEncoding.copyOrder (capacities A)).length := by
  rw [encodeSet_reindex,PairedCatalogProgram.catalog_encode]
  exact List.length_ofFn

lemma catalog_length_of_supported (A : Instance (Fin m) (Fin n)) (code : List ℕ)
    (h : ∃ S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A)),
      code=encodeSet (coordinateOrder A) S.val.val) :
    (PairedCatalogProgram.catalog code).length=
      (CanonicalInitialEncoding.copyOrder (capacities A)).length := by
  obtain ⟨S,rfl⟩ := h
  exact catalog_length_encode A S.val.val

lemma outer_trial_catalog (z : CompanionOuterPhaseProgram.Input) :
    CompanionPhaseTrialProgram.catalogue (CompanionOuterPhaseProgram.trialInput z)=
      PairedCatalogProgram.catalog (CompanionOuterPhaseProgram.startCode z) := rfl

theorem outer_output_rep_of_supported (A : Instance (Fin m) (Fin n))
    (z : CompanionOuterPhaseProgram.Input)
    (hinit : CompanionStoredRepresentation.StoredRep
      (CanonicalInitialEncoding.copyOrder (capacities A)).length z.1.1.2)
    (hh : ∀ s∈z.1.2,CompanionStoredRepresentation.StoredRep
      (CanonicalInitialEncoding.copyOrder (capacities A)).length s)
    (hs : ∃ S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A)),
      CompanionOuterPhaseProgram.startCode z=encodeSet (coordinateOrder A) S.val.val) :
    CompanionStoredRepresentation.StoredRep
      (CanonicalInitialEncoding.copyOrder (capacities A)).length
      (CompanionOuterPhaseProgram.output z) := by
  apply CompanionStoredRepresentation.outer_output_rep z hinit hh
  rw [outer_trial_catalog]
  exact catalog_length_of_supported A _ hs

end
end ContingencyTables.CompanionInitializedRestartProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCanonicalPhaseSupport
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Representation preservation for every executed counting phase

The restart support statement is obtained from its actual finite-word law.
The remaining trajectory and observation words may be unused padding for
that law; their presence still supplies the required precision markers.
-/
namespace ContingencyTables.CompanionCanonicalPhaseSupport
open MatchingFPRAS CommonBasesFPRAS FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionEvaluatedWeightProgram CompanionStoredRepresentation CompanionHistoryReadback
open CompanionCanonicalPhaseLaw CompanionOracleDensity GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma restart_prefix_le (A : Instance (Fin m) (Fin n)) (C K H N R L W j : ℕ)
    (epsilon : TreeFraction.Fraction) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (hj : j < H)
    (hwidth : RootedPhaseHistory.totalWidth A (rawSettings A C K H N R L epsilon hK hW v) ≤ W) :
    CompanionComputedInitial.wordLength A
        (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
      CompanionRestartProgram.sumBits A C K j
        (CompanionInitializedRestartProgram.parameters A H
          (CompanionTargetMixing.restartTime A H L) N R L epsilon) ≤ W := by
  let s := rawSettings A C K H N R L epsilon hK hW v
  calc
    _ = RootedRestartWords.initialStageBits A C K H L s.k R s.h j s.xi :=
      CompanionOuterWidths.initialWidth_eq A C K H N R L j epsilon
    _ ≤ RootedPhaseHistory.width A s j := Nat.le_add_right _ _
    _ ≤ RootedPhaseHistory.totalWidth A s := RootedPhaseHistory.width_le A s j hj
    _ ≤ W := hwidth

theorem output_rep (A : Instance (Fin m) (Fin n)) (C K H N R L W : ℕ)
    (epsilon : TreeFraction.Fraction) (hC : 0 < C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hxi : 0 < TreeFraction.val (CountingPhaseParametersProgram.noise
      (CompanionInitializedRestartProgram.parameters A H
        (CompanionTargetMixing.restartTime A H L) N R L epsilon)))
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (initial : CompanionPhaseFinishProgram.Stored) (history : List CompanionPhaseFinishProgram.Stored)
    (hj : history.length < H) (hphase : history.length+1 ≤ rationalHeight A C)
    (hwidth : RootedPhaseHistory.totalWidth A (rawSettings A C K H N R L epsilon hK hW v) ≤ W)
    (hdegree : ∀ i,i ≤ history.length+1 → PowerOfTwoApproximation.rootDegree
      (roundingTolerance (innerTolerance
        ((rawSettings A C K H N R L epsilon hK hW v).xi/2) i)) ≤ W)
    (hdepth : ∀ i,i ≤ history.length+1 → PowerOfTwoApproximation.depth
      (roundingTolerance (innerTolerance
        ((rawSettings A C K H N R L epsilon hK hW v).xi/2) i)) ≤ W)
    (hinit : StoredRep (CanonicalInitialEncoding.copyOrder (capacities A)).length initial)
    (hh : ∀ q∈history,StoredRep (CanonicalInitialEncoding.copyOrder (capacities A)).length q)
    (bits : Fin W→Bool) :
    StoredRep (CanonicalInitialEncoding.copyOrder (capacities A)).length
      (CompanionOuterPhaseProgram.output
        (((CompanionRestartInitializer.data A C K H
          (CompanionTargetMixing.restartTime A H L) N R L epsilon z v,initial),history),List.ofFn bits)) := by
  let t := CompanionTargetMixing.restartTime A H L
  let j := history.length
  let p := CompanionInitializedRestartProgram.parameters A H t N R L epsilon
  let a := wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))
  let b := CompanionRestartProgram.sumBits A C K j p
  let padding := W-(a+b)
  let w := matrixAt (CanonicalInitialEncoding.copyOrder (capacities A)).length initial history
  let E := estimateAt initial history
  have hprefix : a+b ≤ W := restart_prefix_le A C K H N R L W j epsilon hK hW v hj hwidth
  have hlen : a+(b+padding)=W := by
    rw [←Nat.add_assoc]
    exact Nat.add_sub_of_le hprefix
  have hl := CompanionInitializedRestartProgram.output_padded_sameLaw A C K H t N R L j padding
    hC (by omega) hK hW hB epsilon hxi z v w (fun i => E (i.val+1))
    (fun i => by
      unfold CompanionRestartStageProgram.oracleData
      rw [RootedOracleConfigProgram.rootDegree_data]
      exact (hdegree (i.val+1) (by omega)).trans_eq hlen.symm)
    (fun i => by
      unfold CompanionRestartStageProgram.oracleData
      rw [RootedOracleConfigProgram.depth_data]
      exact (hdepth (i.val+1) (by omega)).trans_eq hlen.symm)
  have hl' := SameLaw.word_length hlen
    (fun bs => CompanionInitializedRestartProgram.output
      (CompanionInitializedRestartProgram.data A C K H t N R L j epsilon z v w
        (fun i => E (i.val+1)) bs)) _ hl
  obtain ⟨sourceBits,hs⟩ := hl'.exists_preimage bits
  have hd := outer_data_readback A C K H t N R L epsilon z v initial history hinit hh (List.ofFn bits)
  apply CompanionInitializedRestartProgram.outer_output_rep_of_supported A _ hinit hh
  refine ⟨CompanionInitializedRestartProgram.model A C K H t N R L j epsilon hK hW v w sourceBits,?_⟩
  rw [←hd]
  change CompanionInitializedRestartProgram.output
    (CompanionOuterPhaseProgram.restartInput
      (CompanionOuterPhaseProgram.data A C K H t N R L j epsilon z v w E (List.ofFn bits)))=_
  rw [CompanionOuterPhaseProgram.restartInput_data]
  exact hs.symm

end
end ContingencyTables.CompanionCanonicalPhaseSupport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteBoundedProjectedHistory
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projected adaptive laws up to the prescribed number of phases -/
namespace ContingencyTables.FiniteObservableTransport
open CommonBasesFPRAS
open scoped Classical
noncomputable section

theorem bounded_projected_foldl_sameLaw {C Z U V : Type*} [Fintype U] [Fintype V]
    (F : C→U→C) (G : Z→V→Z) (e : C→Z) (Valid : C→Prop)
    (size : C→ℕ) (H : ℕ)
    (hsize : ∀ c u,size (F c u)=size c+1)
    (hvalid : ∀ c,Valid c→size c<H→∀ u,Valid (F c u))
    (hstep : ∀ c,Valid c→size c<H→SameLaw (fun u => e (F c u)) (G (e c)))
    (c : C) (hc : Valid c) (N : ℕ) (hN : size c+N≤H) :
    SameLaw (fun us : Fin N→U => e ((List.ofFn us).foldl F c))
      (fun vs : Fin N→V => (List.ofFn vs).foldl G (e c)) := by
  intro phi
  induction N generalizing c phi with
  | zero => simp only [List.ofFn_zero,List.foldl_nil,uniformAverage_const]
  | succ N ih =>
    have hlt : size c<H := by omega
    rw [uniformAverage_fin_succ,uniformAverage_fin_succ]
    simp only [List.ofFn_cons,List.foldl_cons]
    have h := hstep c hc hlt (fun z => uniformAverage (fun vs : Fin N→V =>
      phi ((List.ofFn vs).foldl G z)))
    have hl : uniformAverage (fun u : U => uniformAverage (fun us : Fin N→U =>
        phi (e ((List.ofFn us).foldl F (F c u)))))=
        uniformAverage (fun u : U => uniformAverage (fun vs : Fin N→V =>
          phi ((List.ofFn vs).foldl G (e (F c u))))) := by
      apply congrArg uniformAverage
      funext u
      apply ih (F c u) (hvalid c hc hlt u)
      rw [hsize]
      omega
    exact hl.trans h

end
end ContingencyTables.FiniteObservableTransport

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionProjectedHistory
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lifting executed phase laws through the complete adaptive history -/
namespace ContingencyTables.CompanionProjectedHistory
open MatchingFPRAS CommonBasesFPRAS FiniteObservableTransport
open CompanionFactorialApplication CompanionStoredRepresentation
open CompanionCanonicalHistory
open scoped Classical
noncomputable section

lemma fold_eq (fixed : CompanionOuterHistoryProgram.Fixed) {W : ℕ}
    (words : List (Fin W→Bool)) (history : List Stored) :
    ((words.map List.ofFn).foldl
      (fun state bits => CompanionOuterHistoryProgram.advance (bits,state)) (fixed,history))=
      (fixed,words.foldl (advance fixed) history) := by
  induction words generalizing history with
  | nil => rfl
  | cons word words ih =>
    simpa only [List.map_cons,List.foldl_cons,advance,CompanionOuterHistoryProgram.advance,
      CompanionOuterHistoryProgram.next,CompanionOuterHistoryProgram.phaseInput] using
      ih (advance fixed history word)

lemma storedHistory_eq (fixed : CompanionOuterHistoryProgram.Fixed) {W : ℕ}
    (words : List (Fin W→Bool)) :
    CompanionOuterHistoryProgram.storedHistory (fixed,words.map List.ofFn)=
      words.foldl (advance fixed) [] := by
  exact congrArg Prod.snd (fold_eq fixed words [])

lemma fold_length (fixed : CompanionOuterHistoryProgram.Fixed) {W : ℕ}
    (words : List (Fin W→Bool)) (history : List Stored) :
    (words.foldl (advance fixed) history).length=history.length+words.length := by
  induction words generalizing history with
  | nil => simp only [List.foldl_nil,List.length_nil,Nat.add_zero]
  | cons word words ih =>
    rw [List.foldl_cons,ih]
    simp only [advance,List.length_append,List.length_cons,List.length_nil,List.length_cons]
    omega

variable {I J : Type} [Fintype I] [Fintype J]

theorem history_sameLaw (A : Instance I J) {p W : ℕ} (g : Fin p ≃ Labels A)
    (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (fixed : CompanionOuterHistoryProgram.Fixed)
    (hrep : ∀ history : List Stored,(∀ x∈history,StoredRep p x)→history.length < s.H→
      ∀ bits : Fin W→Bool,StoredRep p (CompanionOuterPhaseProgram.output ((fixed,history),List.ofFn bits)))
    (hstep : ∀ history : List Stored,(∀ x∈history,StoredRep p x)→history.length < s.H→
      SameLaw (fun bits : Fin W→Bool => CompanionPhaseFinishProgram.view (p := p)
        (CompanionOuterPhaseProgram.output ((fixed,history),List.ofFn bits)))
        (canonicalStep A g R s (history.map (CompanionPhaseFinishProgram.view (p := p))))) :
    SameLaw (fun words : Fin s.H→(Fin W→Bool) =>
      (CompanionOuterHistoryProgram.storedHistory
        (fixed,(List.ofFn words).map List.ofFn)).map (CompanionPhaseFinishProgram.view (p := p)))
      (fun words : Fin s.H→RootedPhaseHistory.Word A s =>
        canonicalDecoded A g R s (List.ofFn words)) := by
  let F : List Stored→(Fin W→Bool)→List Stored := advance fixed
  let G := canonicalAdvance A g R s
  let e := List.map (CompanionPhaseFinishProgram.view (p := p))
  let Valid := fun history : List Stored => ∀ x∈history,StoredRep p x
  have hv : ∀ history,Valid history→history.length < s.H→∀ bits,Valid (F history bits) := by
    intro history hh hlt bits x hx
    rcases List.mem_append.mp hx with hx|hx
    · exact hh x hx
    · have he : x=CompanionOuterPhaseProgram.output ((fixed,history),List.ofFn bits) := by
        simpa only [List.mem_singleton] using hx
      subst x
      exact hrep history hh hlt bits
  have hs : ∀ history,Valid history→history.length < s.H→
      SameLaw (fun bits => e (F history bits)) (G (e history)) := by
    intro history hh hlt
    have h := (hstep history hh hlt).map (fun x => e history++[x])
    intro phi
    simpa only [e,F,G,advance,canonicalAdvance,List.map_append,List.map_singleton] using h phi
  have h := bounded_projected_foldl_sameLaw F G e Valid List.length s.H
    (fun history bits => by simp only [F,advance,List.length_append,List.length_cons,List.length_nil])
    hv hs [] (by simp [Valid]) s.H (by simp)
  intro phi
  simpa only [storedHistory_eq,e,F,G,canonicalDecoded,List.map_nil] using h phi

theorem output_sameLaw (A : Instance I J) {p W : ℕ} (g : Fin p ≃ Labels A)
    (R : RootedCompletion.Selection A.T) (s : RootedPhaseHistory.Settings A)
    (fixed : CompanionOuterHistoryProgram.Fixed)
    (hinit : CompanionPhaseFinishProgram.view (p := p) fixed.2=
      project A g (RootedStoredEstimate.initialStored A))
    (hrep : ∀ history : List Stored,(∀ x∈history,StoredRep p x)→history.length < s.H→
      ∀ bits : Fin W→Bool,StoredRep p (CompanionOuterPhaseProgram.output ((fixed,history),List.ofFn bits)))
    (hstep : ∀ history : List Stored,(∀ x∈history,StoredRep p x)→history.length < s.H→
      SameLaw (fun bits : Fin W→Bool => CompanionPhaseFinishProgram.view (p := p)
        (CompanionOuterPhaseProgram.output ((fixed,history),List.ofFn bits)))
        (canonicalStep A g R s (history.map (CompanionPhaseFinishProgram.view (p := p))))) :
    SameLaw (fun words : Fin s.H→(Fin W→Bool) =>
      TreeFraction.val (CompanionOuterHistoryProgram.output
        (fixed,(List.ofFn words).map List.ofFn)).2)
      (RootedCountingWords.estimate A R s) := by
  have h := (history_sameLaw A g R s fixed hrep hstep).map
    (fun history => (canonicalLookup A g history s.H).2)
  have he (words : Fin s.H→(Fin W→Bool)) :
      TreeFraction.val (CompanionOuterHistoryProgram.output
        (fixed,(List.ofFn words).map List.ofFn)).2=
      (canonicalLookup A g
        ((CompanionOuterHistoryProgram.storedHistory
          (fixed,(List.ofFn words).map List.ofFn)).map (CompanionPhaseFinishProgram.view (p := p))) s.H).2 := by
    change (CompanionPhaseFinishProgram.view (p := p)
      (CompanionOuterPhaseProgram.old ((fixed,
        CompanionOuterHistoryProgram.storedHistory (fixed,(List.ofFn words).map List.ofFn)),[]))).2=_
    have hh := CompanionHistoryReadback.view_old_canonical A g fixed
      (CompanionOuterHistoryProgram.storedHistory (fixed,(List.ofFn words).map List.ofFn)) [] hinit
    have hl : (CompanionOuterHistoryProgram.storedHistory
        (fixed,(List.ofFn words).map List.ofFn)).length=s.H := by
      rw [storedHistory_eq,fold_length]
      simp only [List.length_nil,List.length_ofFn,Nat.zero_add]
    rw [hh,hl]
  intro phi
  simp_rw [he]
  exact (h phi).trans (by
    apply congrArg uniformAverage
    funext words
    rw [estimate_project]
    rfl)

end
end ContingencyTables.CompanionProjectedHistory

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionScaleSizes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit sizes at the companion's bounded-capacity scale

The unary copy labels are used only below the chosen cutoff, not below
the original binary-encoded capacities. These estimates retain the
cutoff dependency and then substitute the paper's actual polynomial
scale. The initial precision is bounded without executing a real log.
-/

namespace ContingencyTables.CompanionScaleSizes

open CompanionFactorialApplication CompanionInitialDraw
open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J]

lemma precision_le (A : Instance I J) (h : ℕ) :
    precision A h≤A.d*(3*A.W+1)+1+h := by
  unfold precision
  apply Nat.add_le_add_right
  exact Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)

theorem initialBits_polynomial_bound (A : Instance I J) (h : ℕ) :
    initialBits A (precision A h)≤
      A.d*(A.W+1)*(A.d*(3*A.W+1)+1+h) := by
  exact (initialBits_bound A (precision A h)).trans
    (Nat.mul_le_mul_left _ (precision_le A h))

end ContingencyTables.CompanionScaleSizes

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingOracleWordBounds
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial word sizes for the executed density oracle -/

namespace ContingencyTables.CountingOracleWordBounds
open CompanionFactorialApplication CompanionOracleDensity GridBoundary
open Polynomial
open scoped BigOperators Classical
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

lemma binWordBits_bound (A : Instance I J) (h : ℕ) :
    binWordBits A h ≤ A.d*(CountingTerminalSchedule.capacityBits A+1+4*(h+A.d)) := by
  have hb (i : Fin (dimension A)) :
      Nat.clog 2 (freeRange A (index A i)+1) ≤ CountingTerminalSchedule.capacityBits A+1 := by
    let t := index A i
    have hs : (A.b t.val.1 t.val.2+1).size ≤ CountingTerminalSchedule.capacityBits A := by
      change (A.b t.val.1 t.val.2+1).size ≤ ∑ a : I×J,(A.b a.1 a.2+1).size
      exact Finset.single_le_sum (f := fun a : I×J => (A.b a.1 a.2+1).size)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (t.val.1,t.val.2))
    have hp := Nat.lt_size_self (A.b t.val.1 t.val.2+1)
    apply Nat.clog_le_of_le_pow
    have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hs
    change A.b t.val.1 t.val.2+1+1 ≤ 2^(CountingTerminalSchedule.capacityBits A+1)
    rw [pow_succ]
    omega
  unfold binWordBits
  calc
    _ ≤ ∑ _i : Fin (dimension A),
        (CountingTerminalSchedule.capacityBits A+1+4*(h+A.d)) := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.add_le_add_right (hb i) _
    _ = dimension A*(CountingTerminalSchedule.capacityBits A+1+4*(h+A.d)) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (ForestScaledPenalty.free_card_le A)

lemma oracle_time_bound (A : Instance I J) (C K E : ℕ) (theta : ℚ)
    (hE : 1/theta ≤ (E:ℚ)) :
    oracleTime A C K 1 theta ≤
      2*(10000*A.d^2*K)^2*(rationalHeight A C+A.d*K+2+16*E) := by
  unfold oracleTime
  apply Nat.ceil_le.mpr
  have ht : (1:ℝ)/(theta:ℝ) ≤ (E:ℝ) := by exact_mod_cast hE
  have hh := mul_le_mul_of_nonneg_left
    (add_le_add_left (mul_le_mul_of_nonneg_left ht (show (0:ℝ) ≤ 16 by norm_num))
      (height A C+(A.d:ℝ)*K+2))
    (show 0 ≤ mixingConstant A K by unfold mixingConstant; positivity)
  convert hh using 1 <;>
    simp only [mixingConstant,←rationalHeight_cast A C,Nat.cast_mul,Nat.cast_add,
      Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] <;> ring

lemma samples_bound (j E : ℕ) (delta : ℚ) (hd : 0 < delta)
    (hE : 1/delta ≤ (E:ℚ)) : sampleCount j delta 1 ≤ 65536*(j+1)*E^2 := by
  unfold sampleCount
  apply Nat.ceil_le.mpr
  have he0 : 0 ≤ 1/delta := (one_div_pos.mpr hd).le
  have hs : (1/delta)^2 ≤ (E:ℚ)^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hs (show (0:ℚ) ≤ 65536*(j+1) by positivity)
  convert hh using 1 <;> first | rfl | (push_cast; ring)

lemma offset_bound (A : Instance I J) (E : ℕ) (delta : ℚ)
    (hE : 1/delta ≤ (E:ℚ)) : offsetAccuracy A delta ≤ 4096*A.d*E := by
  unfold offsetAccuracy
  apply Nat.ceil_le.mpr
  have hh := mul_le_mul_of_nonneg_left hE (show (0:ℚ) ≤ 4096*A.d by positivity)
  convert hh using 1 <;> first | rfl | (push_cast; ring)

lemma oracle_time_uniform (A : Instance I J) (C K M E : ℕ) (theta : ℚ)
    (hd : A.d ≤ M) (hK : K ≤ M) (hH : rationalHeight A C ≤ M)
    (hE : 1/theta ≤ ((256*E:ℕ):ℚ)) :
    oracleTime A C K 1 theta ≤ timeBound M E := by
  apply (oracle_time_bound A C K (256*E) theta hE).trans
  unfold timeBound
  apply Nat.mul_le_mul
  · exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left
      (Nat.mul_le_mul (Nat.mul_le_mul_left 10000 (Nat.pow_le_pow_left hd 2)) hK) 2)
  · have hk := Nat.mul_le_mul hd hK
    omega

lemma estimator_bound (A : Instance I J) (C K j M E : ℕ) (delta : ℚ)
    (hd : A.d ≤ M) (hK : K ≤ M) (hH : rationalHeight A C ≤ M)
    (hj : j ≤ M) (hL : CountingTerminalSchedule.capacityBits A ≤ M)
    (hdelta : 0 < delta) (hE : 1/delta ≤ (E:ℚ)) :
    estimatorWordBits A C K j delta 1 ≤ estimatorBound M E := by
  have hE' : 1/delta ≤ ((256*E:ℕ):ℚ) := hE.trans (by exact_mod_cast (show E ≤ 256*E by omega))
  have ht := oracle_time_uniform A C K M E delta hd hK hH hE'
  have hcorr : 1/(delta/256) ≤ ((256*E:ℕ):ℚ) := by
    have hh := mul_le_mul_of_nonneg_left hE (show (0:ℚ) ≤ 256 by norm_num)
    convert hh using 1 <;> first | rfl | (push_cast; field_simp)
  have htc : oracleTime A C K 1 (correctionTheta delta) ≤ timeBound M E := by
    simpa only [correctionTheta,Rat.cast_div,Rat.cast_ofNat] using
      oracle_time_uniform A C K M E (delta/256) hd hK hH hcorr
  have hs : sampleCount j delta 1 ≤ sampleBound M E :=
    (samples_bound j E delta hdelta hE).trans (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left 65536 (Nat.add_le_add_right hj 1)))
  have ha : offsetAccuracy A delta ≤ 4096*M*E :=
    (offset_bound A E delta hE).trans (Nat.mul_le_mul_right E (Nat.mul_le_mul_left 4096 hd))
  have hb : binWordBits A (offsetAccuracy A delta) ≤ binBound M E := by
    apply (binWordBits_bound A _).trans
    unfold binBound
    exact Nat.mul_le_mul hd (Nat.add_le_add (Nat.add_le_add_right hL 1)
      (Nat.mul_le_mul_left 4 (Nat.add_le_add ha hd)))
  have hw : oracleStepBits A C ≤ 9*M := by
    have hl : Nat.clog 2 (8*A.d) ≤ 8*A.d :=
      Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
    unfold oracleStepBits
    omega
  unfold estimatorWordBits estimatorBound oracleIntegerBits
  exact Nat.add_le_add (Nat.mul_le_mul hj (Nat.mul_le_mul hs (Nat.mul_le_mul ht hw)))
    (Nat.mul_le_mul hs (Nat.add_le_add (Nat.mul_le_mul htc hw) hb))

lemma estimatorPolynomial_eval (M : ℕ) :
    estimatorPolynomial.eval M=estimatorBound M (400*(M+1)*M) := by
  simp only [estimatorPolynomial,samplePolynomial,timePolynomial,innerPolynomial,binPolynomial,
    estimatorBound,sampleBound,timeBound,binBound,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]

lemma median_bound_separate (A : Instance I J) (C K j M : ℕ) (xi delta : ℚ)
    (hd : A.d ≤ M) (hK : K ≤ M) (hH : rationalHeight A C ≤ M)
    (hj : j ≤ M) (hL : CountingTerminalSchedule.capacityBits A ≤ M)
    (hxi : 0 < xi) (hi : 1/xi ≤ (M:ℚ))
    (hr : CommonBasesFPRAS.repetitionCount delta ≤ 64*(M+1)) :
    medianEstimatorBits A C K j xi delta ≤ medianPolynomial.eval M := by
  have hdelta : 0 < innerTolerance (xi/2) j := by unfold innerTolerance; positivity
  have heq : 1/innerTolerance (xi/2) j=(400:ℚ)*(j+1)*(1/xi) := by
    unfold innerTolerance
    field_simp
    ring
  have he : 1/innerTolerance (xi/2) j ≤ ((400*(M+1)*M:ℕ):ℚ) := by
    rw [heq]
    have hh := mul_le_mul
      (show (400:ℚ)*(j+1) ≤ 400*(M+1) by exact_mod_cast Nat.mul_le_mul_left 400 (Nat.add_le_add_right hj 1))
      hi (one_div_pos.mpr hxi).le (by positivity)
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using hh
  have hb := estimator_bound A C K j M (400*(M+1)*M) (innerTolerance (xi/2) j)
    hd hK hH hj hL hdelta he
  unfold medianEstimatorBits
  rw [medianPolynomial,Polynomial.eval_mul,Polynomial.eval_mul,Polynomial.eval_add,
    Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one,estimatorPolynomial_eval]
  exact Nat.mul_le_mul hr hb

lemma median_bound (A : Instance I J) (C K j M : ℕ) (xi : ℚ)
    (hd : A.d ≤ M) (hK : K ≤ M) (hH : rationalHeight A C ≤ M)
    (hj : j ≤ M) (hL : CountingTerminalSchedule.capacityBits A ≤ M)
    (hxi : 0 < xi) (hi : 1/xi ≤ (M:ℚ))
    (hr : CommonBasesFPRAS.repetitionCount xi ≤ 64*(M+1)) :
    medianEstimatorBits A C K j xi xi ≤ medianPolynomial.eval M :=
  median_bound_separate A C K j M xi xi hd hK hH hj hL hxi hi hr

end
end ContingencyTables.CountingOracleWordBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingMarkerBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial space for the executed power-approximation markers -/
namespace ContingencyTables.CountingMarkerBounds
open CompanionOracleDensity Polynomial
noncomputable section

lemma inner_inverse_bound (j M : ℕ) (xi : ℚ) (hj : j ≤ M)
    (hxi : 0 < xi) (hi : 1/xi ≤ (M:ℚ)) :
    1/innerTolerance (xi/2) j ≤ ((400*(M+1)*M:ℕ):ℚ) := by
  have heq : 1/innerTolerance (xi/2) j=(400:ℚ)*(j+1)*(1/xi) := by
    unfold innerTolerance
    field_simp
    ring
  rw [heq]
  have hh := mul_le_mul
    (show (400:ℚ)*(j+1) ≤ 400*(M+1) by exact_mod_cast Nat.mul_le_mul_left 400 (Nat.add_le_add_right hj 1))
    hi (one_div_pos.mpr hxi).le (by positivity)
  simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using hh

lemma degree_bound (j M : ℕ) (xi : ℚ) (hj : j ≤ M)
    (hxi : 0 < xi) (hi : 1/xi ≤ (M:ℚ)) :
    PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)) ≤
      512*(400*(M+1)*M) := by
  unfold PowerOfTwoApproximation.rootDegree roundingTolerance
  apply Nat.ceil_le.mpr
  have hh := mul_le_mul_of_nonneg_left (inner_inverse_bound j M xi hj hxi hi)
    (show (0:ℚ) ≤ 512 by norm_num)
  convert hh using 1
  · field_simp
    ring
  · push_cast
    rfl

lemma padding_bound (j M : ℕ) (xi : ℚ) (hj : j ≤ M)
    (hxi : 0 < xi) (hi : 1/xi ≤ (M:ℚ)) :
    PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j))+
      PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)) ≤
        paddingPolynomial.eval M := by
  have hd := degree_bound j M xi hj hxi hi
  have hdepth : PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)) ≤
      PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)) :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
  simp only [paddingPolynomial,Polynomial.eval_mul,Polynomial.eval_add,
    Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  have heq : 409600*(M+1)*M=2*(512*(400*(M+1)*M)) := by ring
  rw [heq]
  omega

end
end ContingencyTables.CountingMarkerBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingWordsBound
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial bound for the complete adaptive counting word

The bound includes every reserved restart, oracle and observation word,
including the words unused on unsuccessful paths.
-/

namespace ContingencyTables.CountingWordsBound
open CompanionFactorialApplication CompanionOracleDensity RootedPhaseHistory
open CountingOracleWordBounds Polynomial
open scoped BigOperators Classical
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

lemma bitCount_bound (A : Instance I J) (s : Settings A) (M : ℕ)
    (hd : A.d ≤ M) (hW : A.W ≤ M) (hK : s.K ≤ M) (hH : s.H ≤ M)
    (hk : s.k ≤ M) (hn : s.n ≤ M) (hN : s.N ≤ M) (hh : s.h ≤ M)
    (hheight : rationalHeight A s.C ≤ M)
    (hcapacity : CountingTerminalSchedule.capacityBits A ≤ M)
    (hlabels : Fintype.card (Labels A) ≤ M)
    (htau : CompanionTargetMixing.restartTime A s.H s.L ≤ M)
    (hxi : 0 < s.xi) (hinverse : 1/s.xi ≤ (M:ℚ))
    (hrepeats : CommonBasesFPRAS.repetitionCount s.xi ≤ 64*(M+1)) :
    RootedCountingWords.bitCount A s ≤ wordPolynomial.eval M := by
  have hmedian (j : ℕ) (hj : j ≤ s.H) :
      medianEstimatorBits A s.C s.K j s.xi s.xi ≤ medianPolynomial.eval M :=
    median_bound A s.C s.K j M s.xi hd hK hheight (hj.trans hH) hcapacity hxi hinverse hrepeats
  have hstep (j : ℕ) (hj : j ≤ s.H) :
      CompanionBooleanPhase.stepBits A s.C s.K j s.k s.xi ≤ stepPolynomial.eval M := by
    have hm := hmedian j hj
    have hp : CompanionBooleanPhase.proposalBits A ≤ M^2 :=
      (Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)).trans
        (Nat.pow_le_pow_left hlabels 2)
    simp only [stepPolynomial,Polynomial.eval_add,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_one]
    unfold CompanionBooleanPhase.stepBits
    omega
  have hstage (i : ℕ) (hi : i+1 ≤ s.H) :
      RootedRestartWords.stageWidth A s.C s.K s.H s.L s.k s.n s.xi i ≤ stagePolynomial.eval M := by
    simp only [RootedRestartWords.stageWidth,CompanionReturnWords.returnBits,
      stagePolynomial,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    exact Nat.mul_le_mul htau (Nat.mul_le_mul (Nat.add_le_add_right hn 1) (hstep (i+1) hi))
  have hinitial : CompanionInitialDraw.initialBits A (CompanionInitialDraw.precision A s.h) ≤
      initialPolynomial.eval M := by
    apply (CompanionScaleSizes.initialBits_polynomial_bound A s.h).trans
    simp only [initialPolynomial,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_ofNat,
      Polynomial.eval_X,Polynomial.eval_one]
    exact Nat.mul_le_mul (Nat.mul_le_mul hd (Nat.add_le_add_right hW 1))
      (Nat.add_le_add (Nat.add_le_add_right
        (Nat.mul_le_mul hd (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hW) 1)) 1) hh)
  have hwidth (j : ℕ) (hj : j < s.H) : width A s j ≤ phasePolynomial.eval M := by
    have hsum : (∑ i : Fin j,RootedRestartWords.stageWidth A s.C s.K s.H s.L s.k s.n s.xi i.val) ≤
        M*stagePolynomial.eval M := by
      calc
        _ ≤ ∑ _i : Fin j,stagePolynomial.eval M :=
          Finset.sum_le_sum (fun i _ => hstage i.val (by omega))
        _ = j*stagePolynomial.eval M := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    have hobs : CompanionPhaseWords.phaseBits A s.C s.K j (s.N+1) s.xi ≤
        (M+1)*(medianPolynomial.eval M+medianPolynomial.eval M) := by
      unfold CompanionPhaseWords.phaseBits CompanionPhaseWords.observationBits
      exact Nat.mul_le_mul (Nat.add_le_add_right hN 1)
        (Nat.add_le_add (hmedian j (by omega)) (hmedian (j+1) (by omega)))
    simp only [width,RootedRestartWords.initialStageBits,phasePolynomial,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_one]
    exact Nat.add_le_add (Nat.add_le_add hinitial hsum)
      (Nat.add_le_add (Nat.mul_le_mul hN (hstep j (by omega))) hobs)
  have htotal : totalWidth A s ≤ M*phasePolynomial.eval M := by
    calc
      _ ≤ ∑ _j : Fin s.H,phasePolynomial.eval M := Finset.sum_le_sum (fun j _ => hwidth j.val j.isLt)
      _ = s.H*phasePolynomial.eval M := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hH
  simp only [RootedCountingWords.bitCount,wordPolynomial,Polynomial.eval_mul,Polynomial.eval_X]
  exact Nat.mul_le_mul hH htotal

end
end ContingencyTables.CountingWordsBound

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionUniformPhaseWidth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A computed common padded width for every adaptive phase

All bounds are fixed arithmetic circuits. No numeric phase count controls
an unbounded preprocessing loop.
-/
namespace ContingencyTables.CompanionUniformPhaseWidth
open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram

theorem width_value (z : Input) :
    width z=CountingWordsBound.wordPolynomial.eval (measure z)+
      CountingMarkerBounds.paddingPolynomial.eval (measure z)+2*measure z+1 := by
  simp only [width,widthExpression,phaseExpression,initialExpression,stageExpression,stepExpression,
    medianExpression,estimatorExpression,sampleExpression,timeExpression,binExpression,innerExpression,x,
    Expr.eval_power,Expr.eval,CountingWordsBound.wordPolynomial,CountingWordsBound.phasePolynomial,
    CountingWordsBound.initialPolynomial,CountingWordsBound.stagePolynomial,CountingWordsBound.stepPolynomial,
    CountingOracleWordBounds.medianPolynomial,CountingOracleWordBounds.estimatorPolynomial,
    CountingOracleWordBounds.samplePolynomial,CountingOracleWordBounds.timePolynomial,
    CountingOracleWordBounds.binPolynomial,CountingOracleWordBounds.innerPolynomial,
    CountingMarkerBounds.paddingPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one,List.getD_cons_zero]

theorem width_pos (z : Input) : 0 < width z := by rw [width_value]; omega

end ContingencyTables.CompanionUniformPhaseWidth

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingLabelCountProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the actual number of factorial labels

Only retained capacities are summed; the program does not expand any
capacity into a list of labels to obtain the phase controls.
-/

namespace ContingencyTables.CountingLabelCountProgram
open MatchingFPRAS.TreeTyped

open CompanionFactorialApplication
open scoped BigOperators Classical
variable {m n : ℕ}

lemma catalogInput_data (A : Instance (Fin m) (Fin n)) :
    catalogInput (RootedForestCatalog.data A)=CompanionCellCatalog.input A := rfl

lemma count_data (A : Instance (Fin m) (Fin n)) :
    count (RootedForestCatalog.data A)=Fintype.card (Labels A) := by
  rw [count,capacities,catalogInput_data,CompanionCellCatalog.capacities_eq,List.sum_ofFn]
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact Fintype.sum_equiv (CompanionCellCatalog.cellEquiv A) _ _ (fun _ => rfl)

end ContingencyTables.CountingLabelCountProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_ComputedCountingParameters
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting schedules computed from the original bounded margins

The capacity-bit sum is formed after the executed endpoint translation.
All remaining dimensions, precisions, cutoffs and phase counts use the
proved rational/natural formulas. No numeric schedule hypothesis is
left to an external caller.
-/

namespace ContingencyTables.ComputedCountingParameters

open CompanionFactorialApplication CompanionOracleDensity RootedPhaseHistory GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

lemma data_dimension (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    (data hEK r c b hne epsilon he).d=dimensionAllowance (m:=m) (n:=n) := rfl

lemma binCount_cast (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    (binCount r c b epsilon:ℝ)=binWidth (data hEK r c b hne epsilon he)
      (coefficient r c b epsilon) := by
  simp only [binCount,binWidth,data_dimension,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]

lemma phases_height (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    phases r c b epsilon=rationalHeight (data hEK r c b hne epsilon he)
      (coefficient r c b epsilon) := rfl

end
end ContingencyTables.ComputedCountingParameters

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPublicWordBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete counting word is polynomial in the original input -/

namespace ContingencyTables.CountingPublicWordBound
open CompanionFactorialApplication CountingPublicInputBounds Polynomial
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma reciprocal_controls (k M : ℕ) (hk : 0 < k) (hM : k ≤ M) :
    0 < (1/(k:ℚ)) ∧ 1/(1/(k:ℚ)) ≤ (M:ℚ) ∧
      CommonBasesFPRAS.repetitionCount (1/(k:ℚ)) ≤ 64*(M+1) := by
  have hkq : (0:ℚ) < k := by exact_mod_cast hk
  refine ⟨one_div_pos.mpr hkq,?_,?_⟩
  · simpa only [one_div_one_div] using (show (k:ℚ) ≤ M by exact_mod_cast hM)
  · unfold CommonBasesFPRAS.repetitionCount
    rw [one_div,Rat.inv_natCast_den_of_pos hk,Nat.size_eq_bits_len]
    exact Nat.mul_le_mul_left 64 (Nat.add_le_add_right
      ((Nat.size_le.mpr Nat.lt_two_pow_self).trans hM) 1)

end
end ContingencyTables.CountingPublicWordBound

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionUniformPhaseBounds
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed common width covers every actual phase and marker -/
namespace ContingencyTables.CompanionUniformPhaseWidth
open MatchingFPRAS CompanionFactorialApplication CompanionOracleDensity
open RootedPhaseHistory GridBoundary
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ}

lemma fields_data (A : Instance (Fin m) (Fin n)) (s : Settings A)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) s.K)
    (hk : CountingPhaseParametersProgram.precision
      ([Fintype.card (Labels A),A.W,s.H,CompanionTargetMixing.restartTime A s.H s.L,s.N,s.n,s.L],epsilon)=s.k)
    (hh : s.h=CountingPhaseSchedule.initialPrecision s.H) :
    fields (data A s epsilon z v)=
      [A.d,s.K,rationalHeight A s.C,0,Fintype.card (Labels A),A.W,s.H,
        CompanionTargetMixing.restartTime A s.H s.L,s.N,s.n,s.L,s.k,s.h] := by
  have ho : oracleInput (data A s epsilon z v)=RootedOracleConfigProgram.data A s.C s.K 0
      (CountingPhaseParametersProgram.noise
        ([Fintype.card (Labels A),A.W,s.H,CompanionTargetMixing.restartTime A s.H s.L,s.N,s.n,s.L],epsilon))
      z v [] := rfl
  unfold fields rawFields
  rw [ho,RootedOracleConfigProgram.fields_data]
  change [A.d,s.K,rationalHeight A s.C,0]++
    [Fintype.card (Labels A),A.W,s.H,CompanionTargetMixing.restartTime A s.H s.L,s.N,s.n,s.L]++
      [CountingPhaseParametersProgram.precision
        ([Fintype.card (Labels A),A.W,s.H,CompanionTargetMixing.restartTime A s.H s.L,s.N,s.n,s.L],epsilon),
        CountingPhaseScalarProgram.initialPrecision.eval
          [Fintype.card (Labels A),A.W,s.H,CompanionTargetMixing.restartTime A s.H s.L,s.N,s.n,s.L]]=_
  rw [hk,CountingPhaseScalarProgram.initialPrecision_value,←hh]
  rfl

theorem width_covers (A : Instance (Fin m) (Fin n)) (s : Settings A)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) s.K)
    (hk : CountingPhaseParametersProgram.precision
      ([Fintype.card (Labels A),A.W,s.H,CompanionTargetMixing.restartTime A s.H s.L,s.N,s.n,s.L],epsilon)=s.k)
    (hh : s.h=CountingPhaseSchedule.initialPrecision s.H)
    (hxi : s.xi=1/(s.k:ℚ)) (hkpos : 0 < s.k) (hHpos : 0 < s.H)
    (hcap : CountingTerminalSchedule.capacityBits A ≤ s.L) :
    totalWidth A s ≤ width (data A s epsilon z v) ∧
      (∀ j,j ≤ s.H →
        PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (s.xi/2) j))+
          PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (s.xi/2) j)) ≤
            width (data A s epsilon z v)) ∧
      2*Fintype.card (Labels A) ≤ width (data A s epsilon z v) := by
  let M := measure (data A s epsilon z v)
  have hs : ∀ x,x ∈ [A.d,s.K,rationalHeight A s.C,0,Fintype.card (Labels A),A.W,s.H,
      CompanionTargetMixing.restartTime A s.H s.L,s.N,s.n,s.L,s.k,s.h] → x ≤ M := by
    intro x hx
    have hmem : x ∈ fields (data A s epsilon z v) := by
      rw [fields_data A s epsilon z v hk hh]
      exact hx
    exact (List.le_sum_of_mem hmem).trans (Nat.le_succ _)
  have hd : A.d ≤ M := hs _ (by simp)
  have hK : s.K ≤ M := hs _ (by simp)
  have hheight : rationalHeight A s.C ≤ M := hs _ (by simp)
  have hp : Fintype.card (Labels A) ≤ M := hs _ (by simp)
  have hW : A.W ≤ M := hs _ (by simp)
  have hH : s.H ≤ M := hs _ (by simp)
  have ht : CompanionTargetMixing.restartTime A s.H s.L ≤ M := hs _ (by simp)
  have hN : s.N ≤ M := hs _ (by simp)
  have hn : s.n ≤ M := hs _ (by simp)
  have hL : s.L ≤ M := hs _ (by simp)
  have hkM : s.k ≤ M := hs _ (by simp)
  have hhM : s.h ≤ M := hs _ (by simp)
  have hr := CountingPublicWordBound.reciprocal_controls s.k M hkpos hkM
  have hx0 : 0 < s.xi := by rw [hxi]; exact hr.1
  have hxiM : 1/s.xi ≤ (M:ℚ) := by rw [hxi]; exact hr.2.1
  have hrepeats : CommonBasesFPRAS.repetitionCount s.xi ≤ 64*(M+1) := by
    rw [hxi]
    exact hr.2.2
  have hb := CountingWordsBound.bitCount_bound A s M hd hW hK hH hkM hn hN hhM hheight
    (hcap.trans hL) hp ht hx0 hxiM hrepeats
  have htotal : totalWidth A s ≤ RootedCountingWords.bitCount A s := by
    change totalWidth A s ≤ s.H*totalWidth A s
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (totalWidth A s) hHpos
  have hb' := htotal.trans hb
  dsimp only [M] at hb' hp
  simp only [width_value]
  refine ⟨hb'.trans (by omega),?_,?_⟩
  · intro j hj
    have hm := CountingMarkerBounds.padding_bound j M s.xi (hj.trans hH) hx0 hxiM
    dsimp only [M] at hm
    exact hm.trans (by omega)
  · omega

end
end ContingencyTables.CompanionUniformPhaseWidth

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingCoefficientProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The terminal coefficient computed with binary natural arithmetic -/

namespace ContingencyTables.CountingCoefficientProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.TreeFraction Polynomial
open OffsetCountPrograms DensePrograms

lemma precision_val (e : Fraction) (hn : 0 < e.1) :
    precision e=CountingTerminalSchedule.precision (val e) := by
  unfold precision CountingTerminalSchedule.precision
  rw [ceilQuotient_eq e.2 e.1 hn]
  congr 2
  simp only [val,one_div,inv_div]

lemma allowance_val (L d : ℕ) (e : Fraction) (hn : 0 < e.1) :
    allowance ((L,d),e)=CountingTerminalSchedule.allowance L d (val e) := by
  simp only [allowance,CountingTerminalSchedule.allowance,precision_val e hn]

lemma coefficient_val (L d : ℕ) (e : Fraction) (hn : 0 < e.1) (hd : 0 < e.2) :
    coefficient ((L,d),e)=CountingTerminalSchedule.coefficient L d (val e) := by
  unfold coefficient
  rw [ceilQuotient_eq _ _ hn]
  unfold CountingTerminalSchedule.coefficient
  rw [←allowance_val L d e hn]
  congr 1
  simp only [numerator,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,val]
  field_simp

end ContingencyTables.CountingCoefficientProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingBaseProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the capacity-bit and dimension inputs to the counting schedule -/

namespace ContingencyTables.CountingBaseProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
open NetworkVertexCode

lemma half_val (e : TreeFraction.Fraction) : TreeFraction.val (half e)=TreeFraction.val e/2 := by
  simp only [half,TreeFraction.val,Nat.cast_mul,Nat.cast_ofNat]
  ring

lemma capacityBits_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    capacityBits (data r c b)=ComputedCountingParameters.capacityBits r c b := by
  unfold capacityBits
  rw [TightenedInputProgram.compute_code]
  simp only [data,ResidualGraphProgram.natCode,List.map_flatten,List.map_ofFn,Function.comp_def,
    List.sum_flatten,List.sum_ofFn,cellBits,ComputedCountingParameters.capacityBits,
    Fintype.sum_prod_type]

lemma dimension_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    dimension (data r c b)=ComputedCountingParameters.dimensionAllowance (m:=m) (n:=n) := by
  simp only [dimension,data,List.length_ofFn,ComputedCountingParameters.dimensionAllowance]

lemma coefficient_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0 < epsilon) :
    coefficient (data r c b,TreeFraction.repr epsilon)=
      ComputedCountingParameters.coefficient r c b epsilon := by
  unfold coefficient frame
  rw [capacityBits_data,dimension_data]
  have hn : 0 < (half (TreeFraction.repr epsilon)).1 := by
    change 0 < epsilon.num.natAbs
    exact Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr he))
  have hd : 0 < (half (TreeFraction.repr epsilon)).2 := by
    change 0 < 2*epsilon.den
    exact Nat.mul_pos (by decide) epsilon.pos
  rw [CountingCoefficientProgram.coefficient_val _ _ _ hn hd,half_val,
    TreeFraction.val_repr he.le]
  rfl

end ContingencyTables.CountingBaseProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingTerminalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed terminal grid width, cutoff and phase count -/

namespace ContingencyTables.CountingTerminalProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma binCount_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0 < epsilon) :
    binCount (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      ComputedCountingParameters.binCount r c b epsilon := by
  unfold binCount base
  rw [CountingBaseProgram.coefficient_data r c b epsilon he,
    CountingBaseProgram.dimension_data]
  unfold ComputedCountingParameters.binCount
  ring

lemma cutoff_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0 < epsilon) :
    cutoff (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      ComputedCountingParameters.cutoff r c b epsilon := by
  unfold cutoff
  rw [CountingBaseProgram.dimension_data,binCount_data r c b epsilon he]
  rfl

lemma phases_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0 < epsilon) :
    phases (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      ComputedCountingParameters.phases r c b epsilon := by
  unfold phases base
  rw [CountingBaseProgram.coefficient_data r c b epsilon he,
    CountingBaseProgram.dimension_data,cutoff_data r c b epsilon he]
  unfold ComputedCountingParameters.phases
  ring

end ContingencyTables.CountingTerminalProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ComputedForestCode
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed forest retains its literal adjacency-list code -/

namespace ContingencyTables.ComputedLargeForest
open SimpleGraph MaximumForest ForestCapacity ForestGreedySemantics
open FiniteGraphRootProgram LargeEdgeCatalogProgram
open scoped Classical

variable {m n : ℕ}

private lemma code_congr {N : ℕ} (G H : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (h : G=H) : graphCode G=graphCode H := by
  subst H
  apply congrArg (@graphCode N G)
  exact Subsingleton.elim _ _

lemma computed_code (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (W : ℕ) (hW : 1 ≤ W) :
    graphCode ((computed r c b W).comap finSumFinEquiv.symm)=
      ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W) := by
  obtain ⟨F,hF,_⟩ := iterate_optimal (graph b W) ⊥ (capacities b)
    (catalog (NetworkVertexCode.data r c b,W)) (catalog_correct r c b W)
    (capacity_positive b W hW) (MaximumForestExchange.bottom_extendible _ _)
    ((m+n)*(m+n)) (by
      have hb := unordered_pair_budget (n:=m+n)
      omega)
  have hzero (d : DecidableRel (⊥ : SimpleGraph (Fin (m+n))).Adj) :
      @graphCode (m+n) ⊥ d=ForestGreedyProgram.emptyGraph (NetworkVertexCode.data r c b,W) := by
    symm
    simp only [ForestGreedyProgram.emptyGraph,vertexCount_code,DirectedBFSCode.range_eq_map,
      ←List.ofFn_eq_map,List.map_ofFn,graphCode]
    apply congrArg List.ofFn
    funext v
    simp [adjacencyRow]
  have hout : ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W)=graphCode F := by
    unfold ForestGreedyProgram.forest ForestGreedyProgram.prepare
    rw [←hzero (fun a b => Classical.propDecidable _),execute_iterate,graphCode_length]
    exact congrArg Prod.fst hF
  have hc : (computed r c b W).comap finSumFinEquiv.symm=
      decoded (ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W)) := by
    ext u v
    change (decoded (ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W))).Adj
      (vertexEquiv (finSumFinEquiv.symm u)) (vertexEquiv (finSumFinEquiv.symm v)) ↔ _
    simp only [vertexEquiv,Equiv.apply_symm_apply]
  have he : (computed r c b W).comap finSumFinEquiv.symm=F := by
    simpa only [hout,decoded_graphCode] using hc
  exact (code_congr _ _ he).trans hout.symm

end ContingencyTables.ComputedLargeForest

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ComputedRootedInput
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rooted-oracle metadata from the executed original-input preprocessing -/

namespace ContingencyTables.ComputedRootedInput
open MatchingFPRAS MatchingFPRAS.TreeTyped
open DensePrograms NetworkVertexCode

open scoped Classical
variable {m n : ℕ}

lemma catalogData_instance (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (W : ℕ) (hW : 2 ≤ W) :
    catalogData (data r c b,W)=RootedForestCatalog.data
      (ComputedCompanionInstance.instanceData hEK r c b hne W hW) := by
  unfold catalogData forestFrame
  rw [TightenedInputProgram.compute_code]
  unfold RootedForestCatalog.data ComputedCompanionInstance.instanceData
  rw [ComputedLargeForest.computed_code _ _ _ W (by omega)]
  simp only [data,Int.toNat_natCast,ResidualGraphProgram.natCode,matrixCode]

lemma baseline_instance (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (W : ℕ) (hW : 2 ≤ W) :
    TightenedInputProgram.baseline (data r c b)=matrixCode
      (fun i j => ((ComputedCompanionInstance.instanceData hEK r c b hne W hW).X i j).toNat) := by
  obtain ⟨Y,hY,_,_⟩ := TightenedInputProgram.baseline_correct hEK r c b hne
  rw [hY]
  unfold matrixCode
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  simp only [ComputedCompanionInstance.instanceData,ComputedCompanionInstance.baseline,
    hY,ResidualGraphProgram.natCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    i.isLt,j.isLt,dite_true,Option.getD_some,Fin.eta,Int.toNat_natCast]

end ContingencyTables.ComputedRootedInput

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingComputedSettings
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing every scalar control from the original bounded table -/

namespace ContingencyTables.CountingComputedSettings
open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram
open CountingPhaseScalarProgram

open CompanionFactorialApplication
open scoped Classical
variable {m n : ℕ}

lemma catalog_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    catalog (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      RootedForestCatalog.data (ComputedCountingParameters.data hEK r c b hne epsilon he) := by
  unfold catalog
  rw [CountingTerminalProgram.cutoff_data r c b epsilon he]
  exact ComputedRootedInput.catalogData_instance hEK r c b hne _ _

lemma labelCount_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    labelCount (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he)) := by
  rw [labelCount,catalog_data hEK r c b hne epsilon he,CountingLabelCountProgram.count_data]

lemma basic_values (P W H L : ℕ) :
    vector controlExpressions [P,W,H,0,0,0,L]=
      [P,W,H,4*CountingPhaseSchedule.observable P W*(H+P+L+5),0,
        CountingPhaseSchedule.returnCap P H (4*CountingPhaseSchedule.observable P W*(H+P+L+5)),L] := by
  simp [vector,controlExpressions,CountingPhaseScalarProgram.p,CountingPhaseScalarProgram.w,
    CountingPhaseScalarProgram.h,capacityBits,restartTime,observable,fullReturnCap,Expr.eval,
    CountingPhaseSchedule.observable,CountingPhaseSchedule.returnCap]

lemma fillObservations_values (P W H T N R L : ℕ) (e : CountingOracleScheduleProgram.Fraction) :
    fillObservations ([P,W,H,T,N,R,L],e)=
      ([P,W,H,T,CountingPhaseSchedule.observations P W H
        (CountingPhaseSchedule.tolerance H (TreeFraction.val e)),R,L],e) := by
  simp [fillObservations,CountingPhaseParametersProgram.observations_val]

end ContingencyTables.CountingComputedSettings

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingSettingsCorrect
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed controls are the proven counting schedule -/

namespace ContingencyTables.CountingComputedSettings
open MatchingFPRAS CompanionFactorialApplication
open CountingPhaseParametersProgram
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma parameters_values (z : Input) (P W H L : ℕ)
    (hz : preliminary z=[P,W,H,0,0,0,L]) :
    parameters z=
      (let T := 4*CountingPhaseSchedule.observable P W*(H+P+L+5)
       let eta := CountingPhaseSchedule.tolerance H (TreeFraction.val z.2/2)
       ([P,W,H,T,CountingPhaseSchedule.observations P W H eta,
         CountingPhaseSchedule.returnCap P H T,L],CountingBaseProgram.half z.2)) := by
  unfold parameters basic
  rw [hz,basic_values,fillObservations_values,CountingBaseProgram.half_val]

lemma parameters_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
    parameters (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      ([Fintype.card (Labels A),A.W,s.H,CompanionTargetMixing.restartTime A s.H s.L,
        s.N,s.n,s.L],CountingBaseProgram.half (TreeFraction.repr epsilon)) := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let H := ComputedCountingParameters.phases r c b epsilon
  let L := ComputedCountingParameters.capacityBits r c b
  have hp : preliminary (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      [Fintype.card (Labels A),A.W,H,0,0,0,L] := by
    unfold preliminary
    rw [labelCount_data hEK r c b hne epsilon he,
      CountingTerminalProgram.cutoff_data r c b epsilon he,
      CountingTerminalProgram.phases_data r c b epsilon he,CountingBaseProgram.capacityBits_data]
    rfl
  rw [parameters_values _ _ _ _ _ hp,TreeFraction.val_repr he.le]
  have ht : 4*CountingPhaseSchedule.observable (Fintype.card (Labels A)) A.W*
      (H+Fintype.card (Labels A)+L+5)=CompanionTargetMixing.restartTime A H L := by
    simp only [CountingPhaseSchedule.observable,CompanionTargetMixing.restartTime,
      CompanionTrace.time,CompanionTrace.integerConstant]
    ring
  dsimp only
  rw [ht]
  rfl

lemma precision_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    precision (parameters (NetworkVertexCode.data r c b,TreeFraction.repr epsilon))=
      (ComputedCountingParameters.settings hEK r c b hne epsilon he).k := by
  rw [parameters_data hEK r c b hne epsilon he,precision_val,
    CountingBaseProgram.half_val,TreeFraction.val_repr he.le]
  rfl

lemma noise_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    TreeFraction.val (noise (parameters (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)))=
      (ComputedCountingParameters.settings hEK r c b hne epsilon he).xi := by
  rw [parameters_data hEK r c b hne epsilon he,noise_val,
    CountingBaseProgram.half_val,TreeFraction.val_repr he.le]
  rfl

end
end ContingencyTables.CountingComputedSettings

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPreparedState
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the immutable rooted state from the public bounded input -/

namespace ContingencyTables.CountingPreparedState
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

open CompanionFactorialApplication ForestAssignmentSplit
open scoped Classical
variable {m n : ℕ}

lemma demand_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    demand (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      RootedDemandProgram.data (ComputedCountingParameters.data hEK r c b hne epsilon he)
        (fun _ _ => 0) (ComputedCountingParameters.data hEK r c b hne epsilon he).b := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  have hc : catalog (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=RootedForestCatalog.data A :=
    CountingComputedSettings.catalog_data hEK r c b hne epsilon he
  have hb : baseline (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      matrixCode (fun i j => (A.X i j).toNat) := by
    exact ComputedRootedInput.baseline_instance hEK r c b hne _ (ComputedCountingParameters.cutoff_two r c b epsilon he)
  have hcap : capacity (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=matrixCode A.b := by
    rw [capacity,hc]
    rfl
  have hz : zeroMatrix (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=matrixCode (fun (_ : Fin m) (_ : Fin n) => 0) := by
    rw [zeroMatrix,hcap]
    simp only [matrixCode,List.map_ofFn,Function.comp_def]
  unfold demand RootedDemandProgram.data
  rw [hc,hb,hz,hcap]

lemma state_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let C := ComputedCountingParameters.coefficient r c b epsilon
    let K := ComputedCountingParameters.binCount r c b epsilon
    state (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      RootedOracleWalkProgram.data A C 0 K (fun _ => 0)
        (start A K (ComputedCountingParameters.binCount_pos r c b epsilon he)) := by
  dsimp only
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  have hp : parameters (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      ((A.d,A.W),(ComputedCountingParameters.coefficient r c b epsilon,0)) := by
    unfold parameters
    rw [CountingBaseProgram.dimension_data,CountingTerminalProgram.cutoff_data r c b epsilon he,
      CountingBaseProgram.coefficient_data r c b epsilon he]
    rfl
  have hz : ForestCountIdentification.smallX A.small (fun _ => 0)=(fun _ _ => 0) := by
    funext i j
    simp [ForestCountIdentification.smallX]
  have hq : (fun i j => A.b i j-ForestCountIdentification.smallY A.small (fun _ => 0) i j)=A.b := by
    funext i j
    simp [ForestCountIdentification.smallY]
  unfold state RootedOracleWalkProgram.data
  rw [CountingTerminalProgram.binCount_data r c b epsilon he,hp,hz,hq,demand_data hEK r c b hne epsilon he]
  apply congrArg (fun coords => ((ComputedCountingParameters.binCount r c b epsilon,
    (((A.d,A.W),(ComputedCountingParameters.coefficient r c b epsilon,0)),
      RootedDemandProgram.data A (fun _ _ => 0) A.b)),coords))
  unfold zeroGrid catalog
  rw [CountingComputedSettings.catalog_data hEK r c b hne epsilon he]
  simp [DensePrograms.gridNatCode,start,GridBoundary.corner,RootedCatalogGrid.freeCount]

lemma start_transport (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let K := ComputedCountingParameters.binCount r c b epsilon
    RootedCatalogGrid.gridEquiv A K
      (start A K (ComputedCountingParameters.binCount_pos r c b epsilon he))=
        ComputedCountingParameters.start hEK r c b hne epsilon he := by
  rfl

end ContingencyTables.CountingPreparedState

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingAdaptiveInputSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed initial record is the literal adaptive counting record -/
namespace ContingencyTables.CountingAdaptiveInputProgram
open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionMultiplierMatrixProgram TwoLiftStates GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

theorem prepared_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (reserve : List Bool) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
    prepared ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),reserve)=
      CompanionRestartInitializer.data A s.C s.K s.H
        (CompanionTargetMixing.restartTime A s.H s.L) s.N s.n s.L
        (CountingBaseProgram.half (TreeFraction.repr epsilon)) (fun _ => 0)
        (CountingPreparedState.start A s.K (ComputedCountingParameters.binCount_pos r c b epsilon he)) := by
  dsimp only
  unfold prepared CountingPreparedState.output
  rw [CountingPreparedState.state_data hEK r c b hne epsilon he,
    CountingComputedSettings.parameters_data hEK r c b hne epsilon he]
  rfl

lemma zeroCode_data (x : Input) (A : Instance (Fin m) (Fin n))
    (hw : labelWidth x=2*Fintype.card (Labels A))
    (hr : 2*Fintype.card (Labels A) ≤ x.2.length) :
    zeroCode x=encodeSet (coordinateOrder A) ∅ := by
  have hcard : (CanonicalInitialEncoding.pairOrder (CompanionComputedInitial.capacities A)).length=
      2*Fintype.card (Labels A) := by
    have h := (Fintype.card_congr (coordinateOrder A)).symm
    simpa only [Fintype.card_fin,Fintype.card_prod,Fintype.card_bool,Nat.mul_comm] using h
  have he : ProfilePrograms.setProfile (coordinateSet (coordinateOrder A) ∅)=
      (fun _ => (0:ℕ)) := by
    funext i
    simp only [ProfilePrograms.setProfile,coordinateSet,Set.mem_preimage,Set.mem_empty_iff_false,ite_false]
  rw [zeroCode,List.map_const',List.length_take,hw,min_eq_left hr,encodeSet,he,List.ofFn_const,hcard]

lemma initialInput_data (x : Input) (A : Instance (Fin m) (Fin n))
    (C K H T N R L : ℕ) (epsilon : TreeFraction.Fraction)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (hp : prepared x=CompanionRestartInitializer.data A C K H T N R L epsilon z v)
    (hc : CountingPreparedState.catalog x.1=RootedForestCatalog.data A)
    (hw : labelWidth x=2*Fintype.card (Labels A))
    (hr : 2*Fintype.card (Labels A) ≤ x.2.length) :
    initialInput x=CompanionInitialStoredProgram.data A ∅ := by
  have hb : capacities x=List.ofFn (CompanionComputedInitial.capacities A) := by
    unfold capacities CompanionRestartInitializer.capacities
    rw [hp,CompanionRestartInitializer.cellInput_data,CompanionCellCatalog.capacities_eq]
    rfl
  unfold initialInput CompanionInitialStoredProgram.data
  rw [hc,hb,zeroCode_data x A hw hr]

theorem initial_view (x : Input) (A : Instance (Fin m) (Fin n))
    (C K H T N R L : ℕ) (epsilon : TreeFraction.Fraction)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (hp : prepared x=CompanionRestartInitializer.data A C K H T N R L epsilon z v)
    (hc : CountingPreparedState.catalog x.1=RootedForestCatalog.data A)
    (hw : labelWidth x=2*Fintype.card (Labels A))
    (hr : 2*Fintype.card (Labels A) ≤ x.2.length) :
    CompanionPhaseFinishProgram.view (initial x)=
      CompanionPhaseFinishProgram.storedView A (pairLabels A) (RootedStoredEstimate.initialStored A) := by
  rw [initial,initialInput_data x A C K H T N R L epsilon z v hp hc hw hr]
  apply Prod.ext
  · funext i j
    change TreeFraction.val (readEntry ((CompanionInitialStoredProgram.output
      (CompanionInitialStoredProgram.data A ∅)).1,(i.val,j.val)))=_
    rw [CompanionInitialStoredProgram.output_matrix,readEntry_code]
    exact CompanionInitialMatrixProgram.initialEntries_val A i j
  · exact CompanionInitialStoredProgram.total_data A ∅

end
end ContingencyTables.CountingAdaptiveInputProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingAdaptiveReserve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initializer uses only the length of its reserved word -/
namespace ContingencyTables.CountingAdaptiveInputProgram
open MatchingFPRAS

lemma zeroCode_eq_of_length_eq (x : CountingBaseProgram.Input) (a b : List Bool)
    (h : a.length=b.length) : zeroCode (x,a)=zeroCode (x,b) := by
  simp only [zeroCode,List.map_const',List.length_take,labelWidth,h]

lemma initialInput_eq_of_length_eq (x : CountingBaseProgram.Input) (a b : List Bool)
    (h : a.length=b.length) : initialInput (x,a)=initialInput (x,b) := by
  change (CountingPreparedState.catalog x,(capacities (x,a),zeroCode (x,a)))=
    (CountingPreparedState.catalog x,(capacities (x,b),zeroCode (x,b)))
  rw [zeroCode_eq_of_length_eq x a b h]
  rfl

theorem output_eq_of_length_eq (x : CountingBaseProgram.Input) (a b : List Bool)
    (h : a.length=b.length) : output (x,a)=output (x,b) := by
  have hi := initialInput_eq_of_length_eq x a b h
  apply Prod.ext
  · rfl
  · exact congrArg CompanionInitialStoredProgram.output hi

theorem output_ofFn (x : CountingBaseProgram.Input) (N : ℕ) (bits : Fin N→Bool) :
    output (x,List.ofFn bits)=output (x,List.replicate N false) :=
  output_eq_of_length_eq x _ _ (by simp only [List.length_ofFn,List.length_replicate])

end ContingencyTables.CountingAdaptiveInputProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPositiveProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One executed positive-label counting run

The supplied word is partitioned into equally padded phase words. The phase
count only truncates a supplied list, so malformed scalar inputs do
not create an unbounded loop.
-/
namespace ContingencyTables.CountingPositiveProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

attribute [local irreducible] historyInput

theorem phaseWidth_pos (req : Request) : 0 < phaseWidth req :=
  CompanionUniformPhaseWidth.width_pos _

theorem words_ofFn (req : Request) (bits : Fin (bitCount req)→Bool) :
    words (req,List.ofFn bits)=List.ofFn (fun i : Fin (phaseCount req) =>
      List.ofFn (fun j : Fin (phaseWidth req) => bits (finProdFinEquiv (i,j)))) := by
  change (wordChunks (phaseWidth req,List.ofFn bits)).take (phaseCount req)=_
  have hc := wordChunks_ofFn (n := phaseCount req) (k := phaseWidth req) (phaseWidth_pos req) bits
  apply (congrArg (fun xs : List (List Bool) => xs.take (phaseCount req)) hc).trans
  exact List.take_of_length_le (by simp only [List.length_ofFn]; exact le_rfl)

end ContingencyTables.CountingPositiveProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPositiveSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-input semantics of the positive counting adapter -/
namespace ContingencyTables.CountingPositiveProgram
open MatchingFPRAS CompanionFactorialApplication CompanionComputedProposal GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

theorem prepared_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (delta : TreeFraction.Fraction) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
    prepared ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta)=
      CompanionUniformPhaseWidth.data A s
        (CountingBaseProgram.half (TreeFraction.repr epsilon)) (fun _ => 0)
        (CountingPreparedState.start A s.K (ComputedCountingParameters.binCount_pos r c b epsilon he)) := by
  exact CountingAdaptiveInputProgram.prepared_data hEK r c b hne epsilon he []

theorem phaseCount_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (delta : TreeFraction.Fraction) :
    phaseCount ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta)=
      (ComputedCountingParameters.settings hEK r c b hne epsilon he).H := by
  unfold phaseCount
  rw [prepared_data hEK r c b hne epsilon he delta]
  rfl

theorem start_ofFn (req : Request) (N : ℕ) (bits : Fin N→Bool) :
    start (req,List.ofFn bits)=start (req,List.replicate N false) :=
  CountingAdaptiveInputProgram.output_ofFn req.1 N bits

theorem start_view (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (delta : TreeFraction.Fraction) (bits : List Bool)
    (hlen : 2*Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he)) ≤ bits.length) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    CompanionPhaseFinishProgram.view
      ((start (((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta),bits)).2)=
      CompanionPhaseFinishProgram.storedView A (pairLabels A) (RootedStoredEstimate.initialStored A) := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
  let x : CountingAdaptiveInputProgram.Input :=
    ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),bits)
  have hp := CountingAdaptiveInputProgram.prepared_data hEK r c b hne epsilon he bits
  have hc : CountingPreparedState.catalog x.1=RootedForestCatalog.data A :=
    CountingComputedSettings.catalog_data hEK r c b hne epsilon he
  have hw : CountingAdaptiveInputProgram.labelWidth x=2*Fintype.card (Labels A) := by
    unfold CountingAdaptiveInputProgram.labelWidth
    rw [CountingComputedSettings.labelCount_data hEK r c b hne epsilon he]
  exact CountingAdaptiveInputProgram.initial_view x A s.C s.K s.H
    (CompanionTargetMixing.restartTime A s.H s.L) s.N s.n s.L
    (CountingBaseProgram.half (TreeFraction.repr epsilon)) (fun _ => 0)
    (CountingPreparedState.start A s.K (ComputedCountingParameters.binCount_pos r c b epsilon he))
    hp hc hw hlen

theorem output_ofFn (req : Request) (bits : Fin (bitCount req)→Bool) :
    output (req,List.ofFn bits)=
      (CompanionOuterHistoryProgram.output
        (start (req,List.ofFn bits),List.ofFn (fun i : Fin (phaseCount req) =>
          List.ofFn (fun j : Fin (phaseWidth req) => bits (finProdFinEquiv (i,j)))))).2 := by
  unfold output finalStored historyInput
  rw [words_ofFn]

theorem phases_pos (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    0 < (ComputedCountingParameters.settings hEK r c b hne epsilon he).H := by
  have hC := ComputedCountingParameters.coefficient_pos r c b epsilon he
  have hd : 0 < ComputedCountingParameters.dimensionAllowance (m := m) (n := n) := by
    unfold ComputedCountingParameters.dimensionAllowance
    omega
  change 0 < ComputedCountingParameters.phases r c b epsilon
  unfold ComputedCountingParameters.phases
  positivity

theorem phaseWidth_covers (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (delta : TreeFraction.Fraction) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
    let W := phaseWidth ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta)
    RootedPhaseHistory.totalWidth A s ≤ W ∧
      (∀ j,j ≤ s.H →
        PowerOfTwoApproximation.rootDegree
            (CompanionOracleDensity.roundingTolerance (CompanionOracleDensity.innerTolerance (s.xi/2) j))+
          PowerOfTwoApproximation.depth
            (CompanionOracleDensity.roundingTolerance (CompanionOracleDensity.innerTolerance (s.xi/2) j)) ≤ W) ∧
      2*Fintype.card (Labels A) ≤ W := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
  let e := CountingBaseProgram.half (TreeFraction.repr epsilon)
  let v := CountingPreparedState.start A s.K
    (ComputedCountingParameters.binCount_pos r c b epsilon he)
  have hk := CountingComputedSettings.precision_data hEK r c b hne epsilon he
  rw [CountingComputedSettings.parameters_data hEK r c b hne epsilon he] at hk
  have hp : 0 < s.k := CountingPhaseSchedule.precision_pos _ _ _ _ _
  have hc := CompanionUniformPhaseWidth.width_covers A s e (fun _ => 0) v hk
    (show s.h=CountingPhaseSchedule.initialPrecision s.H from rfl)
    (show s.xi=1/(s.k:ℚ) from rfl) hp
    (phases_pos hEK r c b hne epsilon he) (le_refl _)
  have hw := congrArg CompanionUniformPhaseWidth.width
    (prepared_data hEK r c b hne epsilon he delta)
  change phaseWidth ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta)=
    CompanionUniformPhaseWidth.width (CompanionUniformPhaseWidth.data A s e (fun _ => 0) v) at hw
  dsimp only
  rw [hw]
  exact hc

theorem initialReserve_le (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (delta : TreeFraction.Fraction) :
    2*Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he)) ≤
      bitCount ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta) := by
  have hc := (phaseWidth_covers hEK r c b hne epsilon he delta).2.2
  have hH := phases_pos hEK r c b hne epsilon he
  unfold bitCount
  rw [phaseCount_data hEK r c b hne epsilon he delta]
  exact hc.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right _ hH)

end
end ContingencyTables.CountingPositiveProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingActualInitialization
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical physical initialization on the original bounded-table input -/
namespace ContingencyTables.CountingPositiveProgram
open MatchingFPRAS CompanionFactorialApplication CompanionComputedProposal GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

theorem start_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon)
    (delta : TreeFraction.Fraction) (bits : List Bool)
    (hlen : 2*Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he)) ≤ bits.length) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
    start (((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta),bits)=
      (CompanionRestartInitializer.data A s.C s.K s.H
        (CompanionTargetMixing.restartTime A s.H s.L) s.N s.n s.L
        (CountingBaseProgram.half (TreeFraction.repr epsilon)) (fun _ => 0)
        (CountingPreparedState.start A s.K (ComputedCountingParameters.binCount_pos r c b epsilon he)),
       CompanionInitialStoredProgram.output (CompanionInitialStoredProgram.data A ∅)) := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
  let x : CountingAdaptiveInputProgram.Input :=
    ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),bits)
  have hp := CountingAdaptiveInputProgram.prepared_data hEK r c b hne epsilon he bits
  have hc : CountingPreparedState.catalog x.1=RootedForestCatalog.data A :=
    CountingComputedSettings.catalog_data hEK r c b hne epsilon he
  have hw : CountingAdaptiveInputProgram.labelWidth x=2*Fintype.card (Labels A) := by
    unfold CountingAdaptiveInputProgram.labelWidth
    rw [CountingComputedSettings.labelCount_data hEK r c b hne epsilon he]
  apply Prod.ext hp
  change CountingAdaptiveInputProgram.initial x=_
  unfold CountingAdaptiveInputProgram.initial
  rw [CountingAdaptiveInputProgram.initialInput_data x A s.C s.K s.H
    (CompanionTargetMixing.restartTime A s.H s.L) s.N s.n s.L
    (CountingBaseProgram.half (TreeFraction.repr epsilon)) (fun _ => 0)
    (CountingPreparedState.start A s.K (ComputedCountingParameters.binCount_pos r c b epsilon he))
    hp hc hw hlen]

end
end ContingencyTables.CountingPositiveProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingActualSettings
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed original-input controls are exactly the source settings -/
namespace ContingencyTables.CountingActualSettings
open MatchingFPRAS CompanionFactorialApplication CompanionOracleDensity GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}
variable (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
variable (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
variable (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon)
local notation "A" => ComputedCountingParameters.data hEK r c b hne epsilon he
local notation "s" => ComputedCountingParameters.settings hEK r c b hne epsilon he
local notation "e" => CountingBaseProgram.half (TreeFraction.repr epsilon)
local notation "v" => CountingPreparedState.start A (RootedPhaseHistory.Settings.K s)
  (ComputedCountingParameters.binCount_pos r c b epsilon he)
local notation "p" => CompanionInitializedRestartProgram.parameters A (RootedPhaseHistory.Settings.H s)
  (CompanionTargetMixing.restartTime A (RootedPhaseHistory.Settings.H s) (RootedPhaseHistory.Settings.L s))
  (RootedPhaseHistory.Settings.N s) (RootedPhaseHistory.Settings.n s) (RootedPhaseHistory.Settings.L s) e

lemma precision : CountingPhaseParametersProgram.precision p=(s).k := by
  have h := CountingComputedSettings.precision_data hEK r c b hne epsilon he
  rw [CountingComputedSettings.parameters_data hEK r c b hne epsilon he] at h
  exact h

lemma observations : CountingPhaseParametersProgram.observations p=(s).N := by
  unfold CompanionInitializedRestartProgram.parameters
  rw [CountingPhaseParametersProgram.observations_val,CountingBaseProgram.half_val,
    TreeFraction.val_repr he.le]
  rfl

lemma noise : TreeFraction.val (CountingPhaseParametersProgram.noise p)=(s).xi := by
  have h := CountingComputedSettings.noise_data hEK r c b hne epsilon he
  rw [CountingComputedSettings.parameters_data hEK r c b hne epsilon he] at h
  exact h

lemma noise_pos : 0<TreeFraction.val (CountingPhaseParametersProgram.noise p) := by
  rw [noise hEK r c b hne epsilon he]
  exact CountingPhaseSchedule.noise_pos _ _ _ _ _

lemma raw_settings : CompanionCanonicalPhaseLaw.rawSettings A (s).C (s).K (s).H (s).N (s).n (s).L
    e (s).hK (s).hW v=s := by
  apply CompanionCanonicalPhaseLaw.rawSettings_eq
  · exact precision hEK r c b hne epsilon he
  · exact observations hEK r c b hne epsilon he
  · rfl
  · exact noise hEK r c b hne epsilon he
  · exact CountingPreparedState.start_transport hEK r c b hne epsilon he

lemma coefficient_pos : 0<(s).C := ComputedCountingParameters.coefficient_pos r c b epsilon he

lemma height : (s).H ≤ rationalHeight A (s).C :=
  (ComputedCountingParameters.phases_height hEK r c b hne epsilon he).le

lemma bin_width : ((s).K:ℝ)=binWidth A (s).C :=
  ComputedCountingParameters.binCount_cast hEK r c b hne epsilon he

end
end ContingencyTables.CountingActualSettings

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingActualPhase
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed phases with the controls computed from the original input -/
namespace ContingencyTables.CountingActualPhase
open MatchingFPRAS CommonBasesFPRAS FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionStoredRepresentation CompanionCanonicalHistory CompanionOracleDensity GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma phase_bounds (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (delta : TreeFraction.Fraction) (j : ℕ)
    (hj : j < (ComputedCountingParameters.settings hEK r c b hne epsilon he).H) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
    let W := CountingPositiveProgram.phaseWidth ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta)
    RootedPhaseHistory.totalWidth A s ≤ W ∧ j+1 ≤ rationalHeight A s.C ∧
      (∀ i,i ≤ j+1 → PowerOfTwoApproximation.rootDegree
        (roundingTolerance (innerTolerance (s.xi/2) i)) ≤ W) ∧
      (∀ i,i ≤ j+1 → PowerOfTwoApproximation.depth
        (roundingTolerance (innerTolerance (s.xi/2) i)) ≤ W) := by
  dsimp only
  have hc := CountingPositiveProgram.phaseWidth_covers hEK r c b hne epsilon he delta
  have hj' : j+1 ≤ (ComputedCountingParameters.settings hEK r c b hne epsilon he).H :=
    Nat.succ_le_of_lt hj
  refine ⟨hc.1,hj'.trans (CountingActualSettings.height hEK r c b hne epsilon he),?_,?_⟩
  · intro i hi
    have hm := hc.2.1 i (hi.trans hj')
    omega
  · intro i hi
    have hm := hc.2.1 i (hi.trans hj')
    omega

theorem output_rep (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (delta : TreeFraction.Fraction) (initial : CompanionPhaseFinishProgram.Stored)
    (hinit : StoredRep (CanonicalInitialEncoding.copyOrder
      (capacities (ComputedCountingParameters.data hEK r c b hne epsilon he))).length initial)
    (history : List CompanionPhaseFinishProgram.Stored)
    (hh : ∀ q∈history,StoredRep (CanonicalInitialEncoding.copyOrder
      (capacities (ComputedCountingParameters.data hEK r c b hne epsilon he))).length q)
    (hj : history.length < (ComputedCountingParameters.settings hEK r c b hne epsilon he).H)
    (bits : Fin (CountingPositiveProgram.phaseWidth
      ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta))→Bool) :
    StoredRep (CanonicalInitialEncoding.copyOrder
      (capacities (ComputedCountingParameters.data hEK r c b hne epsilon he))).length
      (CompanionOuterPhaseProgram.output
        ((fixed hEK r c b hne epsilon he initial,history),List.ofFn bits)) := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
  let e := CountingBaseProgram.half (TreeFraction.repr epsilon)
  let v := CountingPreparedState.start A s.K (ComputedCountingParameters.binCount_pos r c b epsilon he)
  let W := CountingPositiveProgram.phaseWidth ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta)
  have hr : CompanionCanonicalPhaseLaw.rawSettings A s.C s.K s.H s.N s.n s.L e s.hK s.hW v=s :=
    CountingActualSettings.raw_settings hEK r c b hne epsilon he
  have hb := phase_bounds hEK r c b hne epsilon he delta history.length hj
  have hwidth : RootedPhaseHistory.totalWidth A
      (CompanionCanonicalPhaseLaw.rawSettings A s.C s.K s.H s.N s.n s.L e s.hK s.hW v) ≤ W := by
    rw [hr]
    exact hb.1
  have hd : ∀ i,i ≤ history.length+1 → PowerOfTwoApproximation.rootDegree
      (roundingTolerance (innerTolerance
        ((CompanionCanonicalPhaseLaw.rawSettings A s.C s.K s.H s.N s.n s.L e s.hK s.hW v).xi/2) i)) ≤ W := by
    rw [hr]
    exact hb.2.2.1
  have ht : ∀ i,i ≤ history.length+1 → PowerOfTwoApproximation.depth
      (roundingTolerance (innerTolerance
        ((CompanionCanonicalPhaseLaw.rawSettings A s.C s.K s.H s.N s.n s.L e s.hK s.hW v).xi/2) i)) ≤ W := by
    rw [hr]
    exact hb.2.2.2
  exact CompanionCanonicalPhaseSupport.output_rep A s.C s.K s.H s.N s.n s.L W e
    (CountingActualSettings.coefficient_pos hEK r c b hne epsilon he) s.hK s.hW
    (CountingActualSettings.bin_width hEK r c b hne epsilon he)
    (CountingActualSettings.noise_pos hEK r c b hne epsilon he)
    (fun _ => 0) v initial history hj hb.2.1 hwidth hd ht hinit hh bits

theorem output_sameLaw (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (delta : TreeFraction.Fraction) (initial : CompanionPhaseFinishProgram.Stored)
    (hinit : StoredRep (CanonicalInitialEncoding.copyOrder
      (capacities (ComputedCountingParameters.data hEK r c b hne epsilon he))).length initial)
    (hi : CompanionPhaseFinishProgram.view
      (p := (CanonicalInitialEncoding.copyOrder
        (capacities (ComputedCountingParameters.data hEK r c b hne epsilon he))).length) initial=
      project (ComputedCountingParameters.data hEK r c b hne epsilon he)
        (pairLabels (ComputedCountingParameters.data hEK r c b hne epsilon he))
        (RootedStoredEstimate.initialStored (ComputedCountingParameters.data hEK r c b hne epsilon he)))
    (history : List CompanionPhaseFinishProgram.Stored)
    (hh : ∀ q∈history,StoredRep (CanonicalInitialEncoding.copyOrder
      (capacities (ComputedCountingParameters.data hEK r c b hne epsilon he))).length q)
    (hj : history.length < (ComputedCountingParameters.settings hEK r c b hne epsilon he).H) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
    SameLaw (fun bits : Fin (CountingPositiveProgram.phaseWidth
      ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta))→Bool =>
      CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)
        (CompanionOuterPhaseProgram.output
          ((fixed hEK r c b hne epsilon he initial,history),List.ofFn bits)))
      (fun bits : RootedPhaseHistory.Word A s => canonicalStep A (pairLabels A)
        (RootedCompletion.rowColumn A.T) s
        (history.map (CompanionPhaseFinishProgram.view
          (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length))) bits) := by
  dsimp only
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
  let e := CountingBaseProgram.half (TreeFraction.repr epsilon)
  let v := CountingPreparedState.start A s.K (ComputedCountingParameters.binCount_pos r c b epsilon he)
  let W := CountingPositiveProgram.phaseWidth ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta)
  have hr : CompanionCanonicalPhaseLaw.rawSettings A s.C s.K s.H s.N s.n s.L e s.hK s.hW v=s :=
    CountingActualSettings.raw_settings hEK r c b hne epsilon he
  have hb := phase_bounds hEK r c b hne epsilon he delta history.length hj
  have hwidth : RootedPhaseHistory.totalWidth A
      (CompanionCanonicalPhaseLaw.rawSettings A s.C s.K s.H s.N s.n s.L e s.hK s.hW v) ≤ W := by
    rw [hr]
    exact hb.1
  have hd : ∀ i,i ≤ history.length+1 → PowerOfTwoApproximation.rootDegree
      (roundingTolerance (innerTolerance
        ((CompanionCanonicalPhaseLaw.rawSettings A s.C s.K s.H s.N s.n s.L e s.hK s.hW v).xi/2) i)) ≤ W := by
    rw [hr]
    exact hb.2.2.1
  have ht : ∀ i,i ≤ history.length+1 → PowerOfTwoApproximation.depth
      (roundingTolerance (innerTolerance
        ((CompanionCanonicalPhaseLaw.rawSettings A s.C s.K s.H s.N s.n s.L e s.hK s.hW v).xi/2) i)) ≤ W := by
    rw [hr]
    exact hb.2.2.2
  have h := CompanionCanonicalPhaseLaw.output_sameLaw A s.C s.K s.H s.N s.n s.L W e
    (CountingActualSettings.coefficient_pos hEK r c b hne epsilon he) s.hK s.hW
    (CountingActualSettings.bin_width hEK r c b hne epsilon he)
    (CountingActualSettings.noise_pos hEK r c b hne epsilon he)
    (fun _ => 0) v initial history hj hb.2.1 hwidth hd ht hinit hh hi
  dsimp only at h
  rw [hr] at h
  exact h

end
end ContingencyTables.CountingActualPhase

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPositiveWordLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Flattening the positive run while preserving its complete output law -/
namespace ContingencyTables.CountingPositiveProgram
open MatchingFPRAS CommonBasesFPRAS GridBoundary FiniteObservableTransport
open scoped Classical
noncomputable section

theorem output_sameLaw (req : Request) :
    SameLaw (fun bits : Fin (bitCount req)→Bool => output (req,List.ofFn bits))
      (independentOutput req) := by
  intro phi
  have he := uniformAverage_equiv (gridWordEquiv (phaseCount req) (phaseWidth req))
    (fun words => phi (independentOutput req words))
  have hp : (fun bits : Fin (bitCount req)→Bool => phi (output (req,List.ofFn bits)))=
      (fun bits => phi (independentOutput req
        (gridWordEquiv (phaseCount req) (phaseWidth req) bits))) := by
    funext bits
    rw [output_ofFn,start_ofFn]
    rfl
  rw [hp]
  exact he

theorem value_sameLaw (req : Request) :
    SameLaw (fun bits : Fin (bitCount req)→Bool => TreeFraction.val (output (req,List.ofFn bits)))
      (fun words => TreeFraction.val (independentOutput req words)) :=
  (output_sameLaw req).map TreeFraction.val

end
end ContingencyTables.CountingPositiveProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingHistoryApplication
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual original-input counting program has the source history law -/
namespace ContingencyTables.CountingPositiveProgram
open MatchingFPRAS CommonBasesFPRAS CompanionFactorialApplication GridBoundary FiniteObservableTransport
open scoped Classical
noncomputable section
variable {m n : ℕ}

attribute [local irreducible] CountingPositiveProgram.output CompanionOuterHistoryProgram.output
  CompanionOuterPhaseProgram.output

theorem value_source_sameLaw_oai (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0<epsilon) :
    SameLaw
      (fun bits : Fin (bitCount (CountingDirectProgram.request r c b epsilon delta))→Bool =>
        TreeFraction.val (output (CountingDirectProgram.request r c b epsilon delta,List.ofFn bits)))
      (RootedCountingWords.flatEstimate (ComputedCountingParameters.data hEK r c b hne epsilon he)
        (ComputedCountingWords.root hEK r c b hne epsilon he)
        (ComputedCountingParameters.settings hEK r c b hne epsilon he)) := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
  let req := CountingDirectProgram.request r c b epsilon delta
  let initial := CompanionInitialStoredProgram.output (CompanionInitialStoredProgram.data A ∅)
  let fixed := CountingActualPhase.fixed hEK r c b hne epsilon he initial
  let reserve := List.replicate (bitCount req) false
  have hlen : 2*Fintype.card (Labels A) ≤ reserve.length := by
    rw [List.length_replicate]
    exact initialReserve_le hEK r c b hne epsilon he (TreeFraction.repr delta)
  have hstart : start (req,reserve)=fixed :=
    start_data hEK r c b hne epsilon he (TreeFraction.repr delta) reserve hlen
  have hi := start_view hEK r c b hne epsilon he (TreeFraction.repr delta) reserve hlen
  change CompanionPhaseFinishProgram.view (start (req,reserve)).2 = _ at hi
  rw [hstart] at hi
  have hrep : CompanionStoredRepresentation.StoredRep
      (CanonicalInitialEncoding.copyOrder (CompanionComputedInitial.capacities A)).length initial :=
    CompanionStoredRepresentation.initial_output_rep A ∅
  have h := CompanionProjectedHistory.output_sameLaw A (CompanionComputedProposal.pairLabels A)
    (ComputedCountingWords.root hEK r c b hne epsilon he) s fixed hi
    (fun history hh hj => CountingActualPhase.output_rep hEK r c b hne epsilon he
      (TreeFraction.repr delta) initial hrep history hh hj)
    (fun history hh hj => CountingActualPhase.output_sameLaw hEK r c b hne epsilon he
      (TreeFraction.repr delta) initial hrep hi history hh hj)
  have hc : phaseCount req=s.H := phaseCount_data hEK r c b hne epsilon he (TreeFraction.repr delta)
  have hw := value_sameLaw req
  unfold independentOutput at hw
  rw [hstart,hc] at hw
  simp only [List.map_ofFn,Function.comp_def] at h
  intro phi
  have hf := uniformAverage_equiv (gridWordEquiv s.H (RootedPhaseHistory.totalWidth A s))
    (fun words => phi (RootedCountingWords.estimate A
      (ComputedCountingWords.root hEK r c b hne epsilon he) s words))
  exact (hw phi).trans ((h phi).trans hf.symm)

end
end ContingencyTables.CountingPositiveProgram

end OAI
end

theorem solution : type_of% @OAI.ContingencyTables.CountingPositiveProgram.value_source_sameLaw_oai := @OAI.ContingencyTables.CountingPositiveProgram.value_source_sameLaw_oai
