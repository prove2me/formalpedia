-- Prove2me | solution 1 for OAI.CommonBasesFPRAS.MachineCode.frozen_machine
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T01:34:24.589894+00:00
-- url     : https://prove2.me/submissions/4fcdecde-bc29-4930-94b8-1e7fd4ebc3da

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_OAIQ2Mt000
import Theorems.Thm_OAI_CommonBasesFPRAS_MachineCode_output_certificate

section
-- module Solutions.OAIQ2_Mat.MatroidCounting_CommonBases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CommonBasesFPRAS

section

open scoped BigOperators Classical

open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped Classical

open scoped Classical

lemma polynomial_recipe_bounds (n e f E T : ℕ) (hT : 0<T)
    (hn : n≤T) (he : e≤T) (hf : f≤T) (hE : E≤T) :
    let L := 2*n*(n+(e+5))
    let N := 10^14*(L+1)^3*n^14*E^2+1
    L≤14*T^2 ∧ N≤10^18*T^22 ∧
    drawWordBound n N L≤10^20*T^24 ∧
    algorithmDrawBound n N L≤10^21*T^24 ∧
    64*(f+1)≤128*T := by
  dsimp only
  let L := 2*n*(n+(e+5))
  let N := 10^14*(L+1)^3*n^14*E^2+1
  have hp (i j : ℕ) (hij : i≤j) : T^i≤T^j := Nat.pow_le_pow_right hT hij
  have hone (j : ℕ) : 1≤T^j := Nat.one_le_pow _ _ hT
  have he' : e+5≤6*T := by omega
  have hL : L≤14*T^2 := by
    dsimp [L]
    calc
      _ ≤ 2*T*(T+6*T) := by gcongr
      _ = _ := by ring
  have hL1 : L+1≤15*T^2 := by have hh := hone 2; omega
  have hN : N≤10^18*T^22 := by
    dsimp [N]
    calc
      _ ≤ 10^14*(15*T^2)^3*T^14*T^2+1 := by gcongr ; norm_num
      _ ≤ _ := by have hh := hone 22; nlinarith
  have htau : 20*n^4*(n*(L+1)+2)≤340*T^7 := by
    calc
      _ ≤ 20*T^4*(T*(15*T^2)+2) := by gcongr
      _ ≤ _ := by have hh := hp 4 7 (by omega); nlinarith
  have hcap : restartCap n L≤10^9*T^13 := by
    unfold restartCap
    calc
      _ ≤ 2000*(15*T^2)^2*T^2*(340*T^7) := by gcongr
      _ ≤ _ := by nlinarith [Nat.zero_le (T^13)]
  have hcap1 : restartCap n L+1≤2*10^9*T^13 := by have hh := hone 13; omega
  have hB : phaseDrawBound n N L≤10^19*T^22 := by
    unfold phaseDrawBound
    calc
      _ ≤ 1+3*(14*T^2)*(2*10^9*T^13)*(340*T^7)+3*(10^18*T^22) := by gcongr
      _ ≤ _ := by have hh := hone 22; nlinarith
  have hM : algorithmDrawBound n N L≤10^21*T^24 := by
    unfold algorithmDrawBound
    calc
      _ ≤ (10^19*T^22)*(15*T^2) := by gcongr
      _ ≤ _ := by nlinarith [Nat.zero_le (T^24)]
  have hH : drawWordBound n N L≤10^20*T^24 := by
    unfold drawWordBound
    calc
      _ ≤ 2*(2+(10^18*T^22)*(14*T^2)+(2*T)*(T*(14*T^2)))+T^2+T+4 := by gcongr
      _ ≤ _ := by
        have h1 := hone 24
        have h2 := hp 2 24 (by omega)
        have h4 := hp 4 24 (by omega)
        have h3 := hp 1 24 (by omega)
        simp only [pow_one] at h3
        nlinarith
  exact ⟨hL,hN,hH,hM,by omega⟩

theorem fairBitCount_polynomial (n : ℕ) (ε δ : ℚ) :
    fairBitCount n ε δ≤10^66*(bitResourceParameter n ε δ)^73 := by
  let T := bitResourceParameter n ε δ
  have hT : 0<T := by dsimp [T,bitResourceParameter]; omega
  have hn : n≤T := by dsimp [T,bitResourceParameter]; omega
  have he : ε.den.bits.length≤T := by dsimp [T,bitResourceParameter]; omega
  have hf : δ.den.bits.length≤T := by dsimp [T,bitResourceParameter]; omega
  have hE : ⌈ε⁻¹⌉₊≤T := by dsimp [T,bitResourceParameter]; omega
  have hh := polynomial_recipe_bounds n ε.den.bits.length δ.den.bits.length ⌈ε⁻¹⌉₊ T hT hn he hf hE
  dsimp only at hh
  let L := annealLength n (accuracyExponent ε)
  let N := sampleCount n L ε
  have hH : drawWordBound n N L≤10^20*T^24 := hh.2.2.1
  have hM : algorithmDrawBound n N L≤10^21*T^24 := hh.2.2.2.1
  have hR : repetitionCount δ≤128*T := hh.2.2.2.2
  have hD : algorithmDrawBound n N L+6≤10^22*T^24 := by
    have hone : 1≤T^24 := Nat.one_le_pow _ _ hT
    omega
  change repetitionCount δ*drawWordBound n N L*(algorithmDrawBound n N L+6)*algorithmDrawBound n N L≤10^66*T^73
  calc
    _ ≤ (128*T)*(10^20*T^24)*(10^22*T^24)*(10^21*T^24) := by gcongr
    _ ≤ _ := by nlinarith [Nat.zero_le (T^73)]

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

section

variable {k n : ℕ}
lemma pairRegisters_a (R : Fin (k+8) → List Bool) (a b : Fin (k+8)) (h : a≠b)
    (xs ys : List Bool) : pairRegisters R a b xs ys a=xs := by simp [pairRegisters,h]
lemma pairRegisters_b (R : Fin (k+8) → List Bool) (a b : Fin (k+8))
    (xs ys : List Bool) : pairRegisters R a b xs ys b=ys := by simp [pairRegisters]
lemma pairRegisters_update_a (R : Fin (k+8) → List Bool) (a b : Fin (k+8)) (h : a≠b)
    (xs ys zs : List Bool) : Function.update (pairRegisters R a b xs ys) a zs =pairRegisters R a b zs ys := by
  funext i
  by_cases ha : i=a
  · subst i; simp [pairRegisters,h]
  · by_cases hb : i=b
    · subst i; simp [pairRegisters,ha]
    · simp [pairRegisters,ha,hb]
lemma pairRegisters_update_b (R : Fin (k+8) → List Bool) (a b : Fin (k+8))
    (xs ys zs : List Bool) : Function.update (pairRegisters R a b xs ys) b zs =pairRegisters R a b xs zs := by
  simp [pairRegisters]
lemma execution_add {s : ℕ} (P : Program k s) (O : IndependenceOracle n)
    (c : MachineConfig k s) (bits : ℕ → Bool) (t u : ℕ) :
    execution P O c bits (t+u)=execution P O (execution P O c bits t) (fun i => bits (t+i)) u := by
  induction u with
  | zero => rfl
  | succ u ih =>
    change machineStep P O (bits (t+u)) (execution P O c bits (t+u))=
      machineStep P O (bits (t+u)) (execution P O (execution P O c bits t) (fun i => bits (t+i)) u)
    rw [ih]
lemma leadingOnes_le (xs : List Bool) : leadingOnes xs≤xs.length := by
  induction xs with
  | nil => simp [leadingOnes]
  | cons b xs ih => cases b <;> simp [leadingOnes,List.length_cons] ; omega
lemma replicate_append_false (m : ℕ) (xs : List Bool) :
    List.replicate m false ++ false::xs=List.replicate (m+1) false++xs := by
  rw [List.replicate_succ']; simp
lemma increment_carry (a b : Fin (k+8)) (hab : a≠b) (O : IndependenceOracle n)
    (R : Fin (k+8) → List Bool) (xs ys : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution (incrementProgram a b) O (workConfig (pairRegisters R a b xs ys) 0 q c) bits
      (2*leadingOnes xs+2)=
    workConfig (pairRegisters R a b (carryTail xs) (List.replicate (leadingOnes xs) false++ys))
      3 q (c+2*leadingOnes xs+2) := by
  induction xs generalizing ys c bits with
  | nil =>
    simp [leadingOnes,carryTail,execution,machineStep,incrementProgram,workConfig,
      pairRegisters_a _ _ _ hab,pairRegisters_update_a _ _ _ hab]
  | cons x xs ih =>
    cases x with
    | false =>
      simp [leadingOnes,carryTail,execution,machineStep,incrementProgram,workConfig,
        pairRegisters_a _ _ _ hab,pairRegisters_update_a _ _ _ hab]
    | true =>
      have ht : execution (incrementProgram a b) O (workConfig (pairRegisters R a b (true::xs) ys) 0 q c) bits 2 =
          workConfig (pairRegisters R a b xs (false::ys)) 0 q (c+2) := by
        simp [execution,machineStep,incrementProgram,workConfig,
          pairRegisters_a _ _ _ hab,pairRegisters_b,pairRegisters_update_a _ _ _ hab,pairRegisters_update_b]
      rw [leadingOnes,show 2*(leadingOnes xs+1)+2=2+(2*leadingOnes xs+2) by omega,execution_add,ht,ih]
      simp only [carryTail,replicate_append_false]
      congr 1 ; omega
lemma increment_restore (a b : Fin (k+8)) (hab : a≠b) (O : IndependenceOracle n)
    (R : Fin (k+8) → List Bool) (m : ℕ) (xs : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution (incrementProgram a b) O (workConfig (pairRegisters R a b xs (List.replicate m false)) 3 q c) bits
      (2*m+1)=workConfig (pairRegisters R a b (List.replicate m false++xs) []) 5 q (c+2*m+1) := by
  induction m generalizing xs c bits with
  | zero =>
    simp [execution,machineStep,incrementProgram,workConfig,pairRegisters_b]
  | succ m ih =>
    have ht : execution (incrementProgram a b) O
        (workConfig (pairRegisters R a b xs (List.replicate (m+1) false)) 3 q c) bits 2 =
        workConfig (pairRegisters R a b (false::xs) (List.replicate m false)) 3 q (c+2) := by
      simp [execution,machineStep,incrementProgram,workConfig,List.replicate_succ,
        pairRegisters_b,pairRegisters_a _ _ _ hab,pairRegisters_update_b,pairRegisters_update_a _ _ _ hab]
    rw [show 2*(m+1)+1=2+(2*m+1) by omega,execution_add,ht,ih,replicate_append_false]
    congr 1 ; omega
lemma incrementBits_correct (xs : List Bool) : binaryValue (incrementBits xs)=binaryValue xs+1 := by
  induction xs with
  | nil => simp [incrementBits,leadingOnes,carryTail,binaryValue]
  | cons x xs ih =>
    cases x with
    | false => simp [incrementBits,leadingOnes,carryTail,binaryValue,Nat.add_comm]
    | true =>
      have he : incrementBits (true::xs)=false::incrementBits xs := by simp [incrementBits,leadingOnes,carryTail,List.replicate_succ]
      rw [he,binaryValue,binaryValue,ih]
      simp; omega

theorem increment_block (a b : Fin (k+8)) (hab : a≠b) (O : IndependenceOracle n)
    (R : Fin (k+8) → List Bool) (xs : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution (incrementProgram a b) O (workConfig (pairRegisters R a b xs []) 0 q c) bits
      (4*leadingOnes xs+3)=
      workConfig (pairRegisters R a b (incrementBits xs) []) 5 q (c+4*leadingOnes xs+3) ∧
    4*leadingOnes xs+3≤4*xs.length+3 ∧ binaryValue (incrementBits xs)=binaryValue xs+1 := by
  refine ⟨?_,by have h := leadingOnes_le xs; omega,incrementBits_correct xs⟩
  rw [show 4*leadingOnes xs+3=(2*leadingOnes xs+2)+(2*leadingOnes xs+1) by omega,execution_add,
    increment_carry a b hab]
  simp only [List.append_nil]
  rw [increment_restore a b hab]
  simp only [incrementBits]
  congr 1 ; omega

end

section

variable {k s t n : ℕ}
lemma machineStep_relabel (P : Program k s) (Q : Program k t) (e : Fin (s+1) → Fin (t+1))
    (O : IndependenceOracle n) (b : Bool) (c : MachineConfig k s)
    (h : Q (e c.control)=(P c.control).relabel e) :
    machineStep Q O b (relabelConfig e c)=relabelConfig e (machineStep P O b c) := by
  cases hc : c.output with
  | some z => simp [machineStep,relabelConfig,hc]
  | none =>
    cases hp : P c.control with
    | push i b j => simp [machineStep,relabelConfig,hc,h,hp,Instruction.relabel]
    | pop i x y z =>
      cases hl : c.registers i with
      | nil => simp [machineStep,relabelConfig,hc,h,hp,Instruction.relabel,hl]
      | cons a l => cases a <;> simp [machineStep,relabelConfig,hc,h,hp,Instruction.relabel,hl]
    | coin x y => cases b <;> simp [machineStep,relabelConfig,hc,h,hp,Instruction.relabel]
    | query w i x y =>
      by_cases hl : (c.registers i).length=n
      · simp [machineStep,relabelConfig,hc,h,hp,Instruction.relabel,hl,apply_ite]
      · simp [machineStep,relabelConfig,hc,h,hp,Instruction.relabel,hl]
    | halt => simp [machineStep,relabelConfig,hc,h,hp,Instruction.relabel]
lemma machineStep_none_pre (P : Program k s) (O : IndependenceOracle n) (b : Bool) (c : MachineConfig k s)
    (h : (machineStep P O b c).output=none) : c.output=none := by
  cases hc : c.output with
  | none => rfl
  | some z => simp [machineStep,hc] at h
lemma machineStep_none_not_halt (P : Program k s) (O : IndependenceOracle n) (b : Bool) (c : MachineConfig k s)
    (h : (machineStep P O b c).output=none) : P c.control≠.halt := by
  have hc := machineStep_none_pre P O b c h
  intro hh
  simp [machineStep,hc,hh] at h
lemma execution_relabel (P : Program k s) (Q : Program k t) (e : Fin (s+1) → Fin (t+1))
    (h : ∀ i,Q (e i)=(P i).relabel e) (O : IndependenceOracle n)
    (c : MachineConfig k s) (bits : ℕ → Bool) (u : ℕ) :
    execution Q O (relabelConfig e c) bits u=relabelConfig e (execution P O c bits u) := by
  induction u with
  | zero => rfl
  | succ u ih =>
    simp only [execution,ih]
    exact machineStep_relabel P Q e O _ _ (h _)
lemma execution_relabel_before_halt (P : Program k s) (Q : Program k t)
    (e : Fin (s+1) → Fin (t+1)) (exit : Fin (s+1)) (hexit : P exit=.halt)
    (h : ∀ i,i≠exit → Q (e i)=(P i).relabel e) (O : IndependenceOracle n)
    (c : MachineConfig k s) (bits : ℕ → Bool) (u : ℕ)
    (hu : (execution P O c bits u).output=none) :
    execution Q O (relabelConfig e c) bits u=relabelConfig e (execution P O c bits u) := by
  induction u with
  | zero => rfl
  | succ u ih =>
    have hn := machineStep_none_pre P O (bits u) (execution P O c bits u) hu
    have hh := machineStep_none_not_halt P O (bits u) (execution P O c bits u) hu
    have he : (execution P O c bits u).control≠exit := by intro he; rw [he,hexit] at hh; exact hh rfl
    simp only [execution,ih hn]
    exact machineStep_relabel P Q e O _ _ (h _ he)
lemma concatProgram_first (P : Program k s) (Q : Program k t) (i : Fin (s+1)) (hi : i≠lastLabel s) :
    concatProgram P Q (firstLabel s t i)=(P i).relabel (firstLabel s t) := by
  have hil : i.val<s := by
    have hh : i.val≠s := by intro he; apply hi; exact Fin.ext he
    omega
  simp [concatProgram,firstLabel,hil]
lemma concat_first_run (P : Program k s) (Q : Program k t) (hexit : P (lastLabel s)=.halt)
    (O : IndependenceOracle n) (c : MachineConfig k s) (bits : ℕ → Bool) (u : ℕ)
    (hu : (execution P O c bits u).output=none) :
    execution (concatProgram P Q) O (relabelConfig (firstLabel s t) c) bits u=
      relabelConfig (firstLabel s t) (execution P O c bits u) :=
  execution_relabel_before_halt P _ _ _ hexit (concatProgram_first P Q) O c bits u hu
lemma concat_second_run (P : Program k s) (Q : Program k t)
    (O : IndependenceOracle n) (c : MachineConfig k t) (bits : ℕ → Bool) (u : ℕ) :
    execution (concatProgram P Q) O (relabelConfig (secondLabel s t) c) bits u=
      relabelConfig (secondLabel s t) (execution Q O c bits u) :=
  execution_relabel Q _ _ (concatProgram_second P Q) O c bits u

lemma link_exit (c : MachineConfig k s) (hc : c.control=lastLabel s) :
    relabelConfig (firstLabel s t) c=relabelConfig (secondLabel s t) (restartControl c 0) := by
  cases c
  simp_all [relabelConfig,firstLabel,secondLabel,restartControl,lastLabel]

theorem concat_run (P : Program k s) (Q : Program k t) (hexit : P (lastLabel s)=.halt)
    (O : IndependenceOracle n) (c : MachineConfig k s) (bits : ℕ → Bool) (u v : ℕ)
    (hu : (execution P O c bits u).output=none)
    (hc : (execution P O c bits u).control=lastLabel s) :
    execution (concatProgram P Q) O (relabelConfig (firstLabel s t) c) bits (u+v)=
      relabelConfig (secondLabel s t)
        (execution Q O (restartControl (execution P O c bits u) 0) (fun i => bits (u+i)) v) := by
  rw [execution_add,concat_first_run P Q hexit O c bits u hu,link_exit _ hc,
    concat_second_run]

end

section
variable {k n : ℕ}
lemma tripleRegisters_a (R : Fin (k+8) → List Bool) (a b d : Fin (k+8))
    (hab : a≠b) (had : a≠d) (xs ys zs : List Bool) : tripleRegisters R a b d xs ys zs a=xs := by
  simp [tripleRegisters,pairRegisters,hab,had]
lemma tripleRegisters_b (R : Fin (k+8) → List Bool) (a b d : Fin (k+8))
    (hbd : b≠d) (xs ys zs : List Bool) : tripleRegisters R a b d xs ys zs b=ys := by
  simp [tripleRegisters,pairRegisters,hbd]
lemma tripleRegisters_d (R : Fin (k+8) → List Bool) (a b d : Fin (k+8))
    (xs ys zs : List Bool) : tripleRegisters R a b d xs ys zs d=zs := by
  simp [tripleRegisters]
lemma tripleRegisters_update_a (R : Fin (k+8) → List Bool) (a b d : Fin (k+8))
    (hab : a≠b) (had : a≠d) (xs ys zs ws : List Bool) :
    Function.update (tripleRegisters R a b d xs ys zs) a ws=tripleRegisters R a b d ws ys zs := by
  funext i
  by_cases ha : i=a
  · subst i; simp [tripleRegisters,pairRegisters,hab,had]
  · by_cases hb : i=b
    · subst i; by_cases hbd : b=d <;> simp [tripleRegisters,pairRegisters,ha,hbd,Ne.symm had]
    · by_cases hd : i=d
      · subst i; simp [tripleRegisters,pairRegisters,ha]
      · simp [tripleRegisters,pairRegisters,ha,hb,hd]
lemma tripleRegisters_update_b (R : Fin (k+8) → List Bool) (a b d : Fin (k+8))
    (hbd : b≠d) (xs ys zs ws : List Bool) :
    Function.update (tripleRegisters R a b d xs ys zs) b ws=tripleRegisters R a b d xs ws zs := by
  funext i
  by_cases hb : i=b
  · subst i; simp [tripleRegisters,pairRegisters,hbd]
  · by_cases hd : i=d
    · subst i; simp [tripleRegisters,pairRegisters,hb]
    · simp [tripleRegisters,pairRegisters,hb,hd]
lemma tripleRegisters_update_d (R : Fin (k+8) → List Bool) (a b d : Fin (k+8))
    (xs ys zs ws : List Bool) :
    Function.update (tripleRegisters R a b d xs ys zs) d ws=tripleRegisters R a b d xs ys ws := by
  simp [tripleRegisters]
lemma copy_scan (a b d : Fin (k+8)) (hab : a≠b) (had : a≠d) (hbd : b≠d)
    (O : IndependenceOracle n) (R : Fin (k+8) → List Bool) (xs ys zs : List Bool)
    (q c : ℕ) (bits : ℕ → Bool) :
    execution (copyProgram a b d) O (copyConfig (tripleRegisters R a b d xs ys zs) 0 q c) bits
      (2*xs.length+1)=copyConfig (tripleRegisters R a b d [] (xs.reverse++ys) zs) 3 q (c+2*xs.length+1) := by
  induction xs generalizing ys c bits with
  | nil => simp [execution,machineStep,copyProgram,copyConfig,tripleRegisters_a _ _ _ _ hab had]
  | cons x xs ih =>
    have ht : execution (copyProgram a b d) O (copyConfig (tripleRegisters R a b d (x::xs) ys zs) 0 q c) bits 2=
        copyConfig (tripleRegisters R a b d xs (x::ys) zs) 0 q (c+2) := by
      cases x <;> simp [execution,machineStep,copyProgram,copyConfig,tripleRegisters_a _ _ _ _ hab had,
        tripleRegisters_b _ _ _ _ hbd,tripleRegisters_update_a _ _ _ _ hab had,tripleRegisters_update_b _ _ _ _ hbd]
    rw [List.length_cons,show 2*(xs.length+1)+1=2+(2*xs.length+1) by omega,execution_add,ht,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
    congr 1 ; omega
lemma copy_restore (a b d : Fin (k+8)) (hab : a≠b) (had : a≠d) (hbd : b≠d)
    (O : IndependenceOracle n) (R : Fin (k+8) → List Bool) (xs ys zs : List Bool)
    (q c : ℕ) (bits : ℕ → Bool) :
    execution (copyProgram a b d) O (copyConfig (tripleRegisters R a b d xs ys zs) 3 q c) bits
      (3*ys.length+1)=copyConfig (tripleRegisters R a b d (ys.reverse++xs) [] (ys.reverse++zs)) 8 q (c+3*ys.length+1) := by
  induction ys generalizing xs zs c bits with
  | nil => simp [execution,machineStep,copyProgram,copyConfig,tripleRegisters_b _ _ _ _ hbd]
  | cons y ys ih =>
    have ht : execution (copyProgram a b d) O (copyConfig (tripleRegisters R a b d xs (y::ys) zs) 3 q c) bits 3=
        copyConfig (tripleRegisters R a b d (y::xs) ys (y::zs)) 3 q (c+3) := by
      cases y <;> simp [execution,machineStep,copyProgram,copyConfig,tripleRegisters_a _ _ _ _ hab had,
        tripleRegisters_b _ _ _ _ hbd,tripleRegisters_d,tripleRegisters_update_a _ _ _ _ hab had,
        tripleRegisters_update_b _ _ _ _ hbd,tripleRegisters_update_d]
    rw [List.length_cons,show 3*(ys.length+1)+1=3+(3*ys.length+1) by omega,execution_add,ht,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
    congr 1 ; omega

theorem copy_block (a b d : Fin (k+8)) (hab : a≠b) (had : a≠d) (hbd : b≠d)
    (O : IndependenceOracle n) (R : Fin (k+8) → List Bool) (xs zs : List Bool)
    (q c : ℕ) (bits : ℕ → Bool) :
    execution (copyProgram a b d) O (copyConfig (tripleRegisters R a b d xs [] zs) 0 q c) bits
      (5*xs.length+2)=copyConfig (tripleRegisters R a b d xs [] (xs++zs)) 8 q (c+5*xs.length+2) := by
  rw [show 5*xs.length+2=(2*xs.length+1)+(3*xs.length+1) by omega,execution_add,
    copy_scan a b d hab had hbd]
  simp only [List.append_nil]
  rw [←List.length_reverse (as:=xs),copy_restore a b d hab had hbd]
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil]
  congr 1 ; omega

lemma addDigits_value (c : Bool) (xs ys : List Bool) :
    binaryValue (addDigits c xs ys)=binaryValue xs+binaryValue ys+(if c then 1 else 0) := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [addDigits,binaryValue]
    | cons y ys ih =>
      simp only [addDigits,binaryValue,ih]
      cases y <;> cases c <;> simp [sumDigit,sumCarry] <;> omega
  | cons x xs ih =>
    cases ys with
    | nil =>
      simp only [addDigits,binaryValue,ih]
      cases x <;> cases c <;> simp [sumDigit,sumCarry] <;> omega
    | cons y ys =>
      simp only [addDigits,binaryValue,ih]
      cases x <;> cases y <;> cases c <;> simp [sumDigit,sumCarry] <;> omega
lemma addDigits_length_cost (c : Bool) (xs ys : List Bool) :
    (addDigits c xs ys).length≤xs.length+ys.length+1 ∧
      addCost c xs ys≤3*(xs.length+ys.length)+3 := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [addDigits,addCost]
    | cons y ys ih =>
      have hi := ih (sumCarry false y c)
      simp only [addDigits,addCost,List.length_cons,List.length_nil] at *
      constructor <;> omega
  | cons x xs ih =>
    cases ys with
    | nil =>
      have hi := ih (sumCarry x false c) []
      simp only [addDigits,addCost,List.length_cons,List.length_nil] at *
      constructor <;> omega
    | cons y ys =>
      have hi := ih (sumCarry x y c) ys
      simp only [addDigits,addCost,List.length_cons] at *
      constructor <;> omega

lemma add_build (a b d : Fin (k+8)) (hab : a≠b) (had : a≠d) (hbd : b≠d)
    (O : IndependenceOracle n) (R : Fin (k+8) → List Bool) (xs ys zs : List Bool)
    (carry : Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution (addProgram a b d) O
      (addConfig (tripleRegisters R a b d xs ys zs) (if carry then 1 else 0) q c) bits
      (addCost carry xs ys)=addConfig
        (tripleRegisters R a b d [] [] ((addDigits carry xs ys).reverse++zs)) 12 q (c+addCost carry xs ys) := by
  induction xs generalizing ys zs carry c bits with
  | nil =>
    induction ys generalizing zs carry c bits with
    | nil =>
      cases carry <;> simp [addCost,addDigits,execution,machineStep,addProgram,addConfig,
        tripleRegisters_a _ _ _ _ hab had,tripleRegisters_b _ _ _ _ hbd,tripleRegisters_d,
        tripleRegisters_update_d]
    | cons y ys ih =>
      have ht : execution (addProgram a b d) O
          (addConfig (tripleRegisters R a b d [] (y::ys) zs) (if carry then 1 else 0) q c) bits 3=
          addConfig (tripleRegisters R a b d [] ys (sumDigit false y carry::zs))
            (if sumCarry false y carry then 1 else 0) q (c+3) := by
        cases y <;> cases carry <;> simp [execution,machineStep,addProgram,addConfig,sumDigit,sumCarry,
          tripleRegisters_a _ _ _ _ hab had,tripleRegisters_b _ _ _ _ hbd,tripleRegisters_d,
          tripleRegisters_update_b _ _ _ _ hbd,tripleRegisters_update_d]
      rw [addCost,execution_add,ht,ih]
      simp only [addDigits,List.reverse_cons,List.append_assoc,List.singleton_append]
      congr 1 ; omega
  | cons x xs ih =>
    cases ys with
    | nil =>
      have ht : execution (addProgram a b d) O
          (addConfig (tripleRegisters R a b d (x::xs) [] zs) (if carry then 1 else 0) q c) bits 3=
          addConfig (tripleRegisters R a b d xs [] (sumDigit x false carry::zs))
            (if sumCarry x false carry then 1 else 0) q (c+3) := by
        cases x <;> cases carry <;> simp [execution,machineStep,addProgram,addConfig,sumDigit,sumCarry,
          tripleRegisters_a _ _ _ _ hab had,tripleRegisters_b _ _ _ _ hbd,tripleRegisters_d,
          tripleRegisters_update_a _ _ _ _ hab had,tripleRegisters_update_d]
      rw [addCost,execution_add,ht,ih]
      simp only [addDigits,List.reverse_cons,List.append_assoc,List.singleton_append]
      congr 1 ; omega
    | cons y ys =>
      have ht : execution (addProgram a b d) O
          (addConfig (tripleRegisters R a b d (x::xs) (y::ys) zs) (if carry then 1 else 0) q c) bits 3=
          addConfig (tripleRegisters R a b d xs ys (sumDigit x y carry::zs))
            (if sumCarry x y carry then 1 else 0) q (c+3) := by
        cases x <;> cases y <;> cases carry <;> simp [execution,machineStep,addProgram,addConfig,sumDigit,sumCarry,
          tripleRegisters_a _ _ _ _ hab had,tripleRegisters_b _ _ _ _ hbd,tripleRegisters_d,
          tripleRegisters_update_a _ _ _ _ hab had,tripleRegisters_update_b _ _ _ _ hbd,
          tripleRegisters_update_d]
      rw [addCost,execution_add,ht,ih]
      simp only [addDigits,List.reverse_cons,List.append_assoc,List.singleton_append]
      congr 1 ; omega
lemma add_restore (a b d : Fin (k+8)) (hab : a≠b) (had : a≠d) (_ : b≠d)
    (O : IndependenceOracle n) (R : Fin (k+8) → List Bool) (xs ys zs : List Bool)
    (q c : ℕ) (bits : ℕ → Bool) :
    execution (addProgram a b d) O (addConfig (tripleRegisters R a b d xs ys zs) 12 q c) bits
      (2*zs.length+1)=addConfig (tripleRegisters R a b d (zs.reverse++xs) ys []) 16 q (c+2*zs.length+1) := by
  induction zs generalizing xs c bits with
  | nil => simp [execution,machineStep,addProgram,addConfig,tripleRegisters_d]
  | cons z zs ih =>
    have ht : execution (addProgram a b d) O (addConfig (tripleRegisters R a b d xs ys (z::zs)) 12 q c) bits 2=
        addConfig (tripleRegisters R a b d (z::xs) ys zs) 12 q (c+2) := by
      cases z <;> simp [execution,machineStep,addProgram,addConfig,tripleRegisters_a _ _ _ _ hab had,
        tripleRegisters_d,tripleRegisters_update_a _ _ _ _ hab had,tripleRegisters_update_d]
    rw [List.length_cons,show 2*(zs.length+1)+1=2+(2*zs.length+1) by omega,execution_add,ht,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
    congr 1 ; omega

theorem addition_block (a b d : Fin (k+8)) (hab : a≠b) (had : a≠d) (hbd : b≠d)
    (O : IndependenceOracle n) (R : Fin (k+8) → List Bool) (xs ys : List Bool)
    (q c : ℕ) (bits : ℕ → Bool) :
    let z := addDigits false xs ys
    let t := addCost false xs ys+2*z.length+1
    binaryValue z=binaryValue xs+binaryValue ys ∧ t≤5*(xs.length+ys.length)+6 ∧
      execution (addProgram a b d) O (addConfig (tripleRegisters R a b d xs ys []) 0 q c) bits t=
        addConfig (tripleRegisters R a b d z [] []) 16 q (c+t) := by
  dsimp only
  refine ⟨by simpa using addDigits_value false xs ys,?_,?_⟩
  · have h := addDigits_length_cost false xs ys
    omega
  · rw [show addCost false xs ys+2*(addDigits false xs ys).length+1=
        addCost false xs ys+(2*(addDigits false xs ys).length+1) by omega,execution_add]
    rw [show (0 : Fin 17)=(if false then 1 else 0) by rfl,add_build a b d hab had hbd]
    simp only [List.append_nil]
    rw [←List.length_reverse (as:=addDigits false xs ys),add_restore a b d hab had hbd]
    simp only [List.reverse_reverse,List.length_reverse,List.append_nil]
    congr 1 ; omega

lemma addDigits_length_max (c : Bool) (xs ys : List Bool) :
    (addDigits c xs ys).length≤ max xs.length ys.length+1 := by
  induction xs generalizing c ys with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [addDigits]
    | cons y ys ih =>
      have h := ih (sumCarry false y c)
      simp only [addDigits,List.length_cons,List.length_nil,Nat.zero_max] at *
      omega
  | cons x xs ih =>
    cases ys with
    | nil =>
      have h := ih (sumCarry x false c) []
      simp only [addDigits,List.length_cons,List.length_nil,Nat.max_zero] at *
      omega
    | cons y ys =>
      have h := ih (sumCarry x y c) ys
      simp only [addDigits,List.length_cons] at *
      omega

lemma workReg_ne {a b : ℕ} (ha : a<k+8) (hb : b<k+8) (hne : a≠b) :
    Fin.ofNat (k+8) a≠Fin.ofNat (k+8) b := by
  intro h
  have hh := congrArg Fin.val h
  change a%(k+8)=b%(k+8) at hh
  rw [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at hh
  exact hne hh
@[simp] lemma workReg_ne01 : (0 : Fin (k+8))≠1 := workReg_ne (a:=0) (b:=1) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne02 : (0 : Fin (k+8))≠2 := workReg_ne (a:=0) (b:=2) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne03 : (0 : Fin (k+8))≠3 := workReg_ne (a:=0) (b:=3) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne04 : (0 : Fin (k+8))≠4 := workReg_ne (a:=0) (b:=4) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne10 : (1 : Fin (k+8))≠0 := workReg_ne (a:=1) (b:=0) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne12 : (1 : Fin (k+8))≠2 := workReg_ne (a:=1) (b:=2) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne13 : (1 : Fin (k+8))≠3 := workReg_ne (a:=1) (b:=3) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne14 : (1 : Fin (k+8))≠4 := workReg_ne (a:=1) (b:=4) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne20 : (2 : Fin (k+8))≠0 := workReg_ne (a:=2) (b:=0) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne21 : (2 : Fin (k+8))≠1 := workReg_ne (a:=2) (b:=1) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne23 : (2 : Fin (k+8))≠3 := workReg_ne (a:=2) (b:=3) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne24 : (2 : Fin (k+8))≠4 := workReg_ne (a:=2) (b:=4) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne30 : (3 : Fin (k+8))≠0 := workReg_ne (a:=3) (b:=0) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne31 : (3 : Fin (k+8))≠1 := workReg_ne (a:=3) (b:=1) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne32 : (3 : Fin (k+8))≠2 := workReg_ne (a:=3) (b:=2) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne34 : (3 : Fin (k+8))≠4 := workReg_ne (a:=3) (b:=4) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne40 : (4 : Fin (k+8))≠0 := workReg_ne (a:=4) (b:=0) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne41 : (4 : Fin (k+8))≠1 := workReg_ne (a:=4) (b:=1) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne42 : (4 : Fin (k+8))≠2 := workReg_ne (a:=4) (b:=2) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne43 : (4 : Fin (k+8))≠3 := workReg_ne (a:=4) (b:=3) (by omega) (by omega) (by omega)

lemma mulRegisters_copy_in (R : Fin (k+8) → List Bool) (xs ys zs : List Bool) :
    tripleRegisters (mulRegisters R xs ys zs []) 0 3 4 xs [] []=mulRegisters R xs ys zs [] := by
  funext i
  by_cases h0 : i=0 <;> by_cases h3 : i=3 <;> by_cases h4 : i=4 <;>
    simp_all [tripleRegisters,pairRegisters,mulRegisters]
lemma mulRegisters_copy_out (R : Fin (k+8) → List Bool) (xs ys zs : List Bool) :
    tripleRegisters (mulRegisters R xs ys zs []) 0 3 4 xs [] xs=mulRegisters R xs ys zs xs := by
  funext i
  by_cases h0 : i=0 <;> by_cases h3 : i=3 <;> by_cases h4 : i=4 <;>
    simp_all [tripleRegisters,pairRegisters,mulRegisters]
lemma mulRegisters_add_in (R : Fin (k+8) → List Bool) (xs ys zs : List Bool) :
    tripleRegisters (mulRegisters R xs ys zs xs) 2 4 3 zs xs []=mulRegisters R xs ys zs xs := by
  funext i
  by_cases h2 : i=2 <;> by_cases h3 : i=3 <;> by_cases h4 : i=4 <;>
    simp_all [tripleRegisters,pairRegisters,mulRegisters]
lemma mulRegisters_add_out (R : Fin (k+8) → List Bool) (xs ys zs us : List Bool) :
    tripleRegisters (mulRegisters R xs ys zs xs) 2 4 3 us [] []=mulRegisters R xs ys us [] := by
  funext i
  by_cases h2 : i=2 <;> by_cases h3 : i=3 <;> by_cases h4 : i=4 <;>
    simp_all [tripleRegisters,pairRegisters,mulRegisters]
lemma mulRegisters_update0 (R : Fin (k+8) → List Bool) (xs ys zs ws us : List Bool) :
    Function.update (mulRegisters R xs ys zs ws) 0 us=mulRegisters R us ys zs ws := by
  funext i
  by_cases h0 : i=0 <;> simp [mulRegisters,h0]
lemma mulRegisters_update1 (R : Fin (k+8) → List Bool) (xs ys zs ws us : List Bool) :
    Function.update (mulRegisters R xs ys zs ws) 1 us=mulRegisters R xs us zs ws := by
  funext i
  by_cases h0 : i=0 <;> by_cases h1 : i=1 <;> simp_all [mulRegisters]

lemma mulBody_exit : (mulBody : Program k 24) (lastLabel 24)=.halt := by
  simp [mulBody,concatProgram,lastLabel,addProgram,Instruction.relabel]
lemma mulBody_run (O : IndependenceOracle n) (R : Fin (k+8) → List Bool)
    (xs ys zs : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution mulBody O (mulBodyConfig (mulRegisters R xs ys zs []) 0 q c) bits (mulBodyCost xs zs)=
      mulBodyConfig (mulRegisters R xs ys (addDigits false zs xs) []) 24 q (c+mulBodyCost xs zs) := by
  have hc := copy_block (k:=k) (0 : Fin (k+8)) 3 4 (by simp) (by simp) (by simp)
    O (mulRegisters R xs ys zs []) xs [] q c bits
  simp only [List.append_nil,mulRegisters_copy_in,mulRegisters_copy_out] at hc
  have ha := (addition_block (k:=k) (2 : Fin (k+8)) 4 3 (by simp) (by simp) (by simp)
    O (mulRegisters R xs ys zs xs) zs xs q (c+(5*xs.length+2))
      (fun i => bits (5*xs.length+2+i))).2.2
  simp only [mulRegisters_add_in,mulRegisters_add_out] at ha
  have hh := concat_run (copyProgram (k:=k) 0 3 4) (addProgram 2 4 3)
    (by rfl) O (copyConfig (mulRegisters R xs ys zs []) 0 q c) bits (5*xs.length+2)
      (addCost false zs xs+2*(addDigits false zs xs).length+1)
      (by rw [hc]; rfl) (by rw [hc]; rfl)
  rw [hc] at hh
  have hre : restartControl (copyConfig (mulRegisters R xs ys zs xs) 8 q (c+5*xs.length+2))
      (0 : Fin 17)=addConfig (mulRegisters R xs ys zs xs) 0 q (c+(5*xs.length+2)) := by
    simp [restartControl,copyConfig,addConfig,Nat.add_assoc]
  rw [hre,ha] at hh
  simpa [mulBody,mulBodyCost,mulBodyConfig,copyConfig,addConfig,relabelConfig,firstLabel,secondLabel,
    Nat.add_assoc] using hh
lemma mulBodyCost_bound (xs zs : List Bool) :
    mulBodyCost xs zs≤15*max xs.length zs.length+8 := by
  have h := addDigits_length_cost false zs xs
  unfold mulBodyCost
  have hx : xs.length≤ max xs.length zs.length := Nat.le_max_left _ _
  have hz : zs.length≤ max xs.length zs.length := Nat.le_max_right _ _
  omega

lemma mulProgram_body (i : Fin 25) (hi : i≠lastLabel 24) :
    (mulProgram : Program k 26) (mulBodyLabel i)=((mulBody : Program k 24) i).relabel mulBodyLabel := by
  have h : i.val<24 := by
    have hh : i.val≠24 := by intro hh; apply hi; exact Fin.ext hh
    omega
  simp [mulProgram,mulBodyLabel,show i.val+1<25 by omega]
lemma mulProgram_body_run (O : IndependenceOracle n) (R : Fin (k+8) → List Bool)
    (xs ys zs : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution mulProgram O (mulConfig (mulRegisters R xs ys zs []) 1 q c) bits (mulBodyCost xs zs)=
      mulConfig (mulRegisters R xs ys (addDigits false zs xs) []) 25 q (c+mulBodyCost xs zs) := by
  have h := execution_relabel_before_halt (mulBody : Program k 24) mulProgram mulBodyLabel
    (lastLabel 24) mulBody_exit mulProgram_body O
    (mulBodyConfig (mulRegisters R xs ys zs []) 0 q c) bits (mulBodyCost xs zs)
    (by rw [mulBody_run]; rfl)
  rw [mulBody_run] at h
  simpa [relabelConfig,mulBodyConfig,mulConfig,mulBodyLabel] using h

lemma mulDigits_value (xs ys zs : List Bool) :
    binaryValue (mulDigits xs ys zs)=binaryValue zs+binaryValue xs*binaryValue ys := by
  induction ys generalizing xs zs with
  | nil => simp [mulDigits,binaryValue]
  | cons bit ys ih =>
    simp only [mulDigits,ih]
    cases bit <;> simp [binaryValue,addDigits_value] <;> ring
lemma mulDigits_length (xs ys zs : List Bool) :
    (mulDigits xs ys zs).length≤ max xs.length zs.length+ys.length := by
  induction ys generalizing xs zs with
  | nil => simp [mulDigits]
  | cons bit ys ih =>
    have h1 := ih (false::xs) (if bit then addDigits false zs xs else zs)
    have h2 := addDigits_length_max false zs xs
    cases bit <;> simp only [mulDigits,Bool.false_eq_true,ite_false,ite_true,List.length_cons] at * <;> omega
lemma mulCost_bound (xs ys zs : List Bool) :
    mulCost xs ys zs≤(15*(max xs.length zs.length+ys.length)+10)*ys.length+1 := by
  induction ys generalizing xs zs with
  | nil => simp [mulCost]
  | cons bit ys ih =>
    have h1 := ih (false::xs) (if bit then addDigits false zs xs else zs)
    have h2 := addDigits_length_max false zs xs
    have h3 := mulBodyCost_bound xs zs
    have hz : (if bit then addDigits false zs xs else zs).length≤ max xs.length zs.length+1 := by
      cases bit <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
    have hh : max (false::xs).length (if bit then addDigits false zs xs else zs).length≤
        max xs.length zs.length+1 := by simp only [List.length_cons]; omega
    have hm : (15*(max (false::xs).length (if bit then addDigits false zs xs else zs).length+ys.length)+10)*ys.length≤
        (15*(max xs.length zs.length+1+ys.length)+10)*ys.length :=
      Nat.mul_le_mul_right _ (by omega)
    cases bit <;> simp only [mulCost,Bool.false_eq_true,ite_false,ite_true,List.length_cons] at * <;> nlinarith
lemma mul_run (O : IndependenceOracle n) (R : Fin (k+8) → List Bool)
    (xs ys zs : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution mulProgram O (mulConfig (mulRegisters R xs ys zs []) 0 q c) bits (mulCost xs ys zs)=
      mulConfig (mulRegisters R (List.replicate ys.length false++xs) [] (mulDigits xs ys zs) [])
        26 q (c+mulCost xs ys zs) := by
  induction ys generalizing xs zs c bits with
  | nil => simp [mulCost,mulDigits,execution,machineStep,mulProgram,mulConfig,mulRegisters]
  | cons bit ys ih =>
    have hpop : execution mulProgram O (mulConfig (mulRegisters R xs (bit::ys) zs []) 0 q c) bits 1=
        mulConfig (mulRegisters R xs ys zs []) (if bit then 1 else 25) q (c+1) := by
      cases bit <;> simp [execution,machineStep,mulProgram,mulConfig,mulRegisters_update1,mulRegisters]
    have hshift (us : List Bool) (c' : ℕ) (bits' : ℕ → Bool) :
        execution mulProgram O (mulConfig (mulRegisters R xs ys us []) 25 q c') bits' 1=
          mulConfig (mulRegisters R (false::xs) ys us []) 0 q (c'+1) := by
      simp [execution,machineStep,mulProgram,mulConfig,mulRegisters_update0,mulRegisters]
    have hbody : execution mulProgram O (mulConfig (mulRegisters R xs (bit::ys) zs []) 0 q c) bits
        (2+(if bit then mulBodyCost xs zs else 0))=
        mulConfig (mulRegisters R (false::xs) ys (if bit then addDigits false zs xs else zs) []) 0 q
          (c+(2+(if bit then mulBodyCost xs zs else 0))) := by
      cases bit with
      | false =>
        simp only [Bool.false_eq_true,ite_false,Nat.add_zero]
        rw [show 2=1+1 by rfl,execution_add,hpop]
        simp only [Bool.false_eq_true,ite_false]
        rw [hshift]
      | true =>
        simp only [ite_true]
        rw [show 2+mulBodyCost xs zs=1+(mulBodyCost xs zs+1) by omega,
          execution_add,hpop]
        simp only [ite_true]
        rw [execution_add,mulProgram_body_run,hshift]
        try (congr 1 ; omega)
    rw [mulCost,execution_add,hbody,ih]
    simp only [mulDigits,List.length_cons,List.replicate_add,List.replicate_one,List.append_assoc,List.singleton_append]
    congr 1 ; omega

theorem multiplication_block (O : IndependenceOracle n) (R : Fin (k+8) → List Bool)
    (xs ys : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    let z := mulDigits xs ys []
    let t := mulCost xs ys []
    binaryValue z=binaryValue xs*binaryValue ys ∧
      t≤(15*(xs.length+ys.length)+10)*ys.length+1 ∧
      execution mulProgram O (mulConfig (mulRegisters R xs ys [] []) 0 q c) bits t=
        mulConfig (mulRegisters R (List.replicate ys.length false++xs) [] z []) 26 q (c+t) := by
  refine ⟨by simp [mulDigits_value,binaryValue],?_,mul_run O R xs ys [] q c bits⟩
  simpa using mulCost_bound xs ys []

end

open scoped Classical

section

variable {k n : ℕ}
lemma greedyTime_bound (n : ℕ) (xs : List Bool) : greedyTime n xs≤(6*n+5)*xs.length+1 := by
  induction xs with
  | nil => simp [greedyTime]
  | cons b xs ih => cases b <;> simp only [greedyTime,List.length_cons,Bool.false_eq_true,ite_false,ite_true] <;> nlinarith
lemma greedyWork_bound (n : ℕ) (xs : List Bool) : greedyWork n xs≤(8*n+5)*xs.length+1 := by
  induction xs with
  | nil => simp [greedyWork]
  | cons b xs ih => cases b <;> simp only [greedyWork,List.length_cons,Bool.false_eq_true,ite_false,ite_true] <;> nlinarith
lemma greedyCalls_bound (xs : List Bool) : greedyCalls xs≤xs.length := by
  induction xs with
  | nil => simp [greedyCalls]
  | cons b xs ih => cases b <;> simp_all [greedyCalls] <;> omega
lemma wordGreedy_length (W : List Bool → Bool) (xs ps : List Bool) :
    (wordGreedy W xs ps).length=xs.length+ps.length := by
  induction xs generalizing ps with
  | nil => simp [wordGreedy]
  | cons b xs ih => simp [wordGreedy,ih,Nat.add_comm,Nat.add_left_comm]

lemma greedyRegisters_update0 (R : Fin (k+8) → List Bool) (xs zs ps qs us : List Bool) :
    Function.update (greedyRegisters R xs zs ps qs) 0 us=greedyRegisters R us zs ps qs := by
  funext i; by_cases h : i=0 <;> simp_all [greedyRegisters]
lemma greedyRegisters_update1 (R : Fin (k+8) → List Bool) (xs zs ps qs us : List Bool) :
    Function.update (greedyRegisters R xs zs ps qs) 1 us=greedyRegisters R xs us ps qs := by
  funext i; by_cases h : i=1 <;> simp_all [greedyRegisters]
lemma greedyRegisters_update2 (R : Fin (k+8) → List Bool) (xs zs ps qs us : List Bool) :
    Function.update (greedyRegisters R xs zs ps qs) 2 us=greedyRegisters R xs zs us qs := by
  funext i; by_cases h : i=2 <;> simp_all [greedyRegisters]
lemma greedyRegisters_update4 (R : Fin (k+8) → List Bool) (xs zs ps qs us : List Bool) :
    Function.update (greedyRegisters R xs zs ps qs) 4 us=greedyRegisters R xs zs ps us := by
  funext i; by_cases h : i=4 <;> simp_all [greedyRegisters]
lemma greedy_copy₁ (which : Bool) (i : Fin 9) (hi : i≠8) :
    greedyProgram (k:=k) which (greedyCopy₁ i)=(copyProgram 2 3 4 i).relabel greedyCopy₁ := by
  have hh : i.val<8 := by
    have hb := i.isLt
    have hn : i.val≠8 := by intro h; exact hi (Fin.ext h)
    omega
  simp [greedyProgram,greedyCopy₁,hh,show 4≤ i.val+4 by omega]
lemma greedy_copy₂ (which : Bool) (i : Fin 9) (hi : i≠8) :
    greedyProgram (k:=k) which (greedyCopy₂ i)=(copyProgram 1 3 4 i).relabel greedyCopy₂ := by
  have hh : i.val<8 := by
    have hb := i.isLt
    have hn : i.val≠8 := by intro h; exact hi (Fin.ext h)
    omega
  simp [greedyProgram,greedyCopy₂,hh,show 13≤ i.val+13 by omega,show ¬i.val+13<12 by omega]
lemma greedyRegisters_copy₁ (R : Fin (k+8) → List Bool) (xs zs ps qs : List Bool) :
    tripleRegisters (greedyRegisters R xs zs ps qs) 2 3 4 ps [] qs=greedyRegisters R xs zs ps qs := by
  funext i
  by_cases h2 : i=2 <;> by_cases h3 : i=3 <;> by_cases h4 : i=4 <;>
    simp_all [tripleRegisters,pairRegisters,greedyRegisters]
lemma greedyRegisters_copy₁_out (R : Fin (k+8) → List Bool) (xs zs ps qs : List Bool) :
    tripleRegisters (greedyRegisters R xs zs ps qs) 2 3 4 ps [] (ps++qs)=greedyRegisters R xs zs ps (ps++qs) := by
  funext i
  by_cases h2 : i=2 <;> by_cases h3 : i=3 <;> by_cases h4 : i=4 <;>
    simp_all [tripleRegisters,pairRegisters,greedyRegisters]
lemma greedyRegisters_copy₂ (R : Fin (k+8) → List Bool) (xs zs ps qs : List Bool) :
    tripleRegisters (greedyRegisters R xs zs ps qs) 1 3 4 zs [] qs=greedyRegisters R xs zs ps qs := by
  funext i
  by_cases h1 : i=1 <;> by_cases h3 : i=3 <;> by_cases h4 : i=4 <;>
    simp_all [tripleRegisters,pairRegisters,greedyRegisters]
lemma greedyRegisters_copy₂_out (R : Fin (k+8) → List Bool) (xs zs ps qs : List Bool) :
    tripleRegisters (greedyRegisters R xs zs ps qs) 1 3 4 zs [] (zs++qs)=greedyRegisters R xs zs ps (zs++qs) := by
  funext i
  by_cases h1 : i=1 <;> by_cases h3 : i=3 <;> by_cases h4 : i=4 <;>
    simp_all [tripleRegisters,pairRegisters,greedyRegisters]
lemma greedy_copy₁_run (which : Bool) (O : IndependenceOracle n) (R : Fin (k+8) → List Bool)
    (xs zs ps qs : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution (greedyProgram which) O (greedyConfig (greedyRegisters R xs zs ps qs) 4 q c) bits (5*ps.length+2)=
      greedyConfig (greedyRegisters R xs zs ps (ps++qs)) 12 q (c+5*ps.length+2) := by
  have hc := copy_block (k:=k) (2 : Fin (k+8)) 3 4 (by simp) (by simp) (by simp)
    O (greedyRegisters R xs zs ps qs) ps qs q c bits
  simp only [greedyRegisters_copy₁,greedyRegisters_copy₁_out] at hc
  have h := execution_relabel_before_halt (copyProgram (k:=k) 2 3 4) (greedyProgram which) greedyCopy₁
    8 (by rfl) (greedy_copy₁ which) O (copyConfig (greedyRegisters R xs zs ps qs) 0 q c) bits (5*ps.length+2)
    (by rw [hc]; rfl)
  rw [hc] at h
  simpa [relabelConfig,copyConfig,greedyConfig,greedyCopy₁] using h
lemma greedy_copy₂_run (which : Bool) (O : IndependenceOracle n) (R : Fin (k+8) → List Bool)
    (xs zs ps qs : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution (greedyProgram which) O (greedyConfig (greedyRegisters R xs zs ps qs) 13 q c) bits (5*zs.length+2)=
      greedyConfig (greedyRegisters R xs zs ps (zs++qs)) 21 q (c+5*zs.length+2) := by
  have hc := copy_block (k:=k) (1 : Fin (k+8)) 3 4 (by simp) (by simp) (by simp)
    O (greedyRegisters R xs zs ps qs) zs qs q c bits
  simp only [greedyRegisters_copy₂,greedyRegisters_copy₂_out] at hc
  have h := execution_relabel_before_halt (copyProgram (k:=k) 1 3 4) (greedyProgram which) greedyCopy₂
    8 (by rfl) (greedy_copy₂ which) O (copyConfig (greedyRegisters R xs zs ps qs) 0 q c) bits (5*zs.length+2)
    (by rw [hc]; rfl)
  rw [hc] at h
  simpa [relabelConfig,copyConfig,greedyConfig,greedyCopy₂] using h
lemma greedy_clear (which b : Bool) (O : IndependenceOracle n) (R : Fin (k+8) → List Bool)
    (xs zs ps qs : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution (greedyProgram which) O (greedyConfig (greedyRegisters R xs zs ps qs) (if b then 23 else 22) q c)
      bits (qs.length+1)=greedyConfig (greedyRegisters R xs zs ps []) (if b then 25 else 24) q (c+qs.length+1) := by
  induction qs generalizing c bits with
  | nil => cases b <;> simp [execution,machineStep,greedyProgram,greedyConfig,greedyRegisters]
  | cons a qs ih =>
    have ht : execution (greedyProgram which) O (greedyConfig (greedyRegisters R xs zs ps (a::qs))
        (if b then 23 else 22) q c) bits 1=
        greedyConfig (greedyRegisters R xs zs ps qs) (if b then 23 else 22) q (c+1) := by
      cases b <;> cases a <;> simp [execution,machineStep,greedyProgram,greedyConfig,greedyRegisters,greedyRegisters_update4]
    rw [List.length_cons,show qs.length+1+1=1+(qs.length+1) by omega,execution_add,ht,ih]
    congr 1 ; omega
lemma greedy_query_run (which : Bool) (O : IndependenceOracle n) (R : Fin (k+8) → List Bool)
    (xs zs ps qs : List Bool) (hn : qs.length=n) (q c : ℕ) (bits : ℕ → Bool) :
    execution (greedyProgram which) O (greedyConfig (greedyRegisters R xs zs ps qs) 21 q c) bits (n+3)=
      greedyConfig (greedyRegisters R xs zs (wordOracle which O qs::ps) []) 0 (q+1) (c+3*n+3) := by
  have ht : execution (greedyProgram which) O (greedyConfig (greedyRegisters R xs zs ps qs) 21 q c) bits 1=
      greedyConfig (greedyRegisters R xs zs ps qs) (if wordOracle which O qs then 23 else 22) (q+1) (c+2*n+1) := by
    simp [execution,machineStep,greedyProgram,greedyConfig,greedyRegisters,wordOracle,hn,two_mul,Nat.add_assoc]
  have hp (b : Bool) (c' : ℕ) (bits' : ℕ → Bool) :
      execution (greedyProgram which) O (greedyConfig (greedyRegisters R xs zs ps []) (if b then 25 else 24) (q+1) c') bits' 1=
        greedyConfig (greedyRegisters R xs zs (b::ps) []) 0 (q+1) (c'+1) := by
    cases b <;> simp [execution,machineStep,greedyProgram,greedyConfig,greedyRegisters_update2,greedyRegisters]
  rw [show n+3=1+((qs.length+1)+1) by omega,execution_add,ht,execution_add,greedy_clear,hp]
  congr 1 ; omega
lemma greedy_true_body (which : Bool) (O : IndependenceOracle n) (R : Fin (k+8) → List Bool)
    (xs ps : List Bool) (hn : xs.length+ps.length+1=n) (q c : ℕ) (bits : ℕ → Bool) :
    execution (greedyProgram which) O
      (greedyConfig (greedyRegisters R (true::xs) (List.replicate (xs.length+1) false) ps []) 0 q c) bits (6*n+5)=
      greedyConfig (greedyRegisters R xs (List.replicate xs.length false)
        (wordOracle which O (List.replicate xs.length false++true::ps)::ps) []) 0 (q+1) (c+8*n+5) := by
  let zs := List.replicate xs.length false
  have hpop : execution (greedyProgram which) O
      (greedyConfig (greedyRegisters R (true::xs) (List.replicate (xs.length+1) false) ps []) 0 q c) bits 2=
        greedyConfig (greedyRegisters R xs zs ps []) 4 q (c+2) := by
    simp [execution,machineStep,greedyProgram,greedyConfig,greedyRegisters_update0,greedyRegisters_update1,
      greedyRegisters,List.replicate_succ,zs]
  have hpush (c' : ℕ) (bits' : ℕ → Bool) :
      execution (greedyProgram which) O (greedyConfig (greedyRegisters R xs zs ps ps) 12 q c') bits' 1=
        greedyConfig (greedyRegisters R xs zs ps (true::ps)) 13 q (c'+1) := by
    simp [execution,machineStep,greedyProgram,greedyConfig,greedyRegisters_update4,greedyRegisters]
  have hlen : (zs++true::ps).length=n := by simp only [List.length_append,List.length_cons,List.length_replicate,zs]; omega
  rw [show 6*n+5=2+((5*ps.length+2)+(1+((5*zs.length+2)+(n+3)))) by simp only [zs,List.length_replicate]; omega,
    execution_add,hpop,execution_add,greedy_copy₁_run]
  simp only [List.append_nil]
  rw [execution_add,hpush,execution_add,greedy_copy₂_run,greedy_query_run _ _ _ _ _ _ _ hlen]
  congr 1 ; simp only [zs,List.length_replicate] ; omega
lemma greedy_false_body (which : Bool) (O : IndependenceOracle n) (R : Fin (k+8) → List Bool)
    (xs ps : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution (greedyProgram which) O
      (greedyConfig (greedyRegisters R (false::xs) (List.replicate (xs.length+1) false) ps []) 0 q c) bits 3=
      greedyConfig (greedyRegisters R xs (List.replicate xs.length false) (false::ps) []) 0 q (c+3) := by
  simp [execution,machineStep,greedyProgram,greedyConfig,greedyRegisters_update0,greedyRegisters_update1,
    greedyRegisters_update2,greedyRegisters,List.replicate_succ]

theorem greedy_machine_run (which : Bool) (O : IndependenceOracle n) (R : Fin (k+8) → List Bool)
    (xs ps : List Bool) (hn : xs.length+ps.length=n) (q c : ℕ) (bits : ℕ → Bool) :
    execution (greedyProgram which) O
      (greedyConfig (greedyRegisters R xs (List.replicate xs.length false) ps []) 0 q c) bits (greedyTime n xs)=
      greedyConfig (greedyRegisters R [] [] (wordGreedy (wordOracle which O) xs ps) []) 26
        (q+greedyCalls xs) (c+greedyWork n xs) := by
  induction xs generalizing ps q c bits with
  | nil => simp [greedyTime,greedyWork,greedyCalls,wordGreedy,execution,machineStep,greedyProgram,greedyConfig,greedyRegisters]
  | cons b xs ih =>
    have hn' : xs.length+ps.length+1=n := by simp only [List.length_cons] at hn; omega
    cases b with
    | false =>
      simp only [greedyTime,greedyWork,greedyCalls,wordGreedy,Bool.false_and,Bool.false_eq_true,ite_false,Nat.zero_add]
      rw [List.length_cons,execution_add,greedy_false_body,ih]
      · congr 1 ; omega
      · simp only [List.length_cons]; omega
    | true =>
      simp only [greedyTime,greedyWork,greedyCalls,wordGreedy,Bool.true_and,ite_true]
      rw [List.length_cons,execution_add,greedy_true_body _ _ _ _ _ hn',ih]
      · congr 1 <;> omega
      · simp only [List.length_cons]; omega

end

section

variable {k n : ℕ}
lemma incrementBits_length (ys : List Bool) : (incrementBits ys).length≤ys.length+1 := by
  induction ys with
  | nil => simp [incrementBits,leadingOnes,carryTail]
  | cons b ys ih =>
    cases b <;> simp only [incrementBits,leadingOnes,carryTail,List.length_append,List.length_replicate,
      List.length_cons] at * <;> omega

lemma popcountTime_bound (xs ys : List Bool) :
    popcountTime xs ys≤(4*(xs.length+ys.length)+4)*xs.length+1 := by
  induction xs generalizing ys with
  | nil => simp [popcountTime]
  | cons b xs ih =>
    have hi := ih (if b then incrementBits ys else ys)
    have hl : (if b then incrementBits ys else ys).length≤ys.length+1 := by
      cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true]; exacts [by omega,incrementBits_length ys]
    have hh := Nat.mul_le_mul_right xs.length (show 4*(xs.length+(if b then incrementBits ys else ys).length)+4≤
        4*(xs.length+ys.length+1)+4 by omega)
    have ho := leadingOnes_le ys
    cases b <;> simp only [popcountTime,List.length_cons,Bool.false_eq_true,ite_false,ite_true] at * <;> nlinarith

lemma popcount_increment (i : Fin 6) (hi : i≠5) :
    (popcountProgram : Program k 6) (popcountLabel i)=(incrementProgram 0 3 i).relabel popcountLabel := by
  have hh : i.val<5 := by
    have hb := i.isLt
    have hn : i.val≠5 := by intro h; exact hi (Fin.ext h)
    omega
  simp [popcountProgram,popcountLabel,hh,show i.val+1<6 by omega]
lemma greedyRegisters_increment_in (R : Fin (k+8) → List Bool) (xs ys : List Bool) :
    pairRegisters (greedyRegisters R ys [] xs []) 0 3 ys []=greedyRegisters R ys [] xs [] := by
  funext i
  by_cases h0 : i=0 <;> by_cases h3 : i=3 <;> simp_all [pairRegisters,greedyRegisters]
lemma greedyRegisters_increment_out (R : Fin (k+8) → List Bool) (xs ys : List Bool) :
    pairRegisters (greedyRegisters R ys [] xs []) 0 3 (incrementBits ys) []=
      greedyRegisters R (incrementBits ys) [] xs [] := by
  funext i
  by_cases h0 : i=0 <;> by_cases h3 : i=3 <;> simp_all [pairRegisters,greedyRegisters]
lemma popcount_increment_run (O : IndependenceOracle n) (R : Fin (k+8) → List Bool)
    (xs ys : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution popcountProgram O (popcountConfig (greedyRegisters R ys [] xs []) 1 q c) bits (4*leadingOnes ys+3)=
      popcountConfig (greedyRegisters R (incrementBits ys) [] xs []) 0 q (c+4*leadingOnes ys+3) := by
  have hi := (increment_block (k:=k) (0 : Fin (k+8)) 3 (by simp) O (greedyRegisters R ys [] xs []) ys q c bits).1
  simp only [greedyRegisters_increment_in,greedyRegisters_increment_out] at hi
  have h := execution_relabel_before_halt (incrementProgram (k:=k) 0 3) popcountProgram popcountLabel
    5 (by rfl) popcount_increment O (workConfig (greedyRegisters R ys [] xs []) 0 q c) bits (4*leadingOnes ys+3)
    (by rw [hi]; rfl)
  rw [hi] at h
  simpa [relabelConfig,workConfig,popcountConfig,popcountLabel] using h

theorem popcount_run (O : IndependenceOracle n) (R : Fin (k+8) → List Bool)
    (xs ys : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution popcountProgram O (popcountConfig (greedyRegisters R ys [] xs []) 0 q c) bits (popcountTime xs ys)=
      popcountConfig (greedyRegisters R (popcountBits xs ys) [] [] []) 6 q (c+popcountTime xs ys) := by
  induction xs generalizing ys c bits with
  | nil => simp [popcountTime,popcountBits,execution,machineStep,popcountProgram,popcountConfig,greedyRegisters]
  | cons b xs ih =>
    have hp : execution popcountProgram O (popcountConfig (greedyRegisters R ys [] (b::xs) []) 0 q c) bits 1=
        popcountConfig (greedyRegisters R ys [] xs []) (if b then 1 else 0) q (c+1) := by
      cases b <;> simp [execution,machineStep,popcountProgram,popcountConfig,greedyRegisters,greedyRegisters_update2]
    cases b with
    | false =>
      simp only [popcountTime,popcountBits,Bool.false_eq_true,ite_false,Nat.add_zero]
      rw [execution_add,hp]
      simp only [Bool.false_eq_true,ite_false]
      rw [ih]
      congr 1 ; omega
    | true =>
      simp only [popcountTime,popcountBits,ite_true]
      rw [show 1+(4*leadingOnes ys+3)+popcountTime xs (incrementBits ys)=
          1+((4*leadingOnes ys+3)+popcountTime xs (incrementBits ys)) by omega,execution_add,hp]
      simp only [ite_true]
      rw [execution_add,popcount_increment_run,ih]
      congr 1 ; omega

end

section
open scoped BigOperators Classical
variable {k n : ℕ}
lemma rankTime_bound (which : Bool) (O : IndependenceOracle n) (xs : List Bool) (hn : xs.length=n) :
    rankTime which O xs≤(10*n+9)*n+2 := by
  have hg := greedyTime_bound n xs
  have hp := popcountTime_bound (wordGreedy (wordOracle which O) xs []) []
  simp only [wordGreedy_length,List.length_nil,Nat.add_zero,hn] at *
  unfold rankTime
  nlinarith
lemma rankWork_bound (which : Bool) (O : IndependenceOracle n) (xs : List Bool) (hn : xs.length=n) :
    rankWork which O xs≤(12*n+9)*n+2 := by
  have hg := greedyWork_bound n xs
  have hp := popcountTime_bound (wordGreedy (wordOracle which O) xs []) []
  simp only [wordGreedy_length,List.length_nil,Nat.add_zero,hn] at *
  unfold rankWork
  nlinarith
lemma rank_run (which : Bool) (O : IndependenceOracle n) (R : Fin (k+8) → List Bool)
    (xs : List Bool) (hn : xs.length=n) (q c : ℕ) (bits : ℕ → Bool) :
    execution (rankProgram which) O
      (rankConfig (greedyRegisters R xs (List.replicate n false) [] []) 0 q c) bits (rankTime which O xs)=
      rankConfig (greedyRegisters R (rankBits which O xs) [] [] []) 32
        (q+greedyCalls xs) (c+rankWork which O xs) := by
  have hg := greedy_machine_run which O R xs [] (by simpa using hn) q c bits
  have hp := popcount_run O R (wordGreedy (wordOracle which O) xs []) [] (q+greedyCalls xs)
    (c+greedyWork n xs) (fun i => bits (greedyTime n xs+i))
  have h := concat_run (greedyProgram (k:=k) which) popcountProgram (by rfl) O
    (greedyConfig (greedyRegisters R xs (List.replicate xs.length false) [] []) 0 q c) bits
    (greedyTime n xs) (popcountTime (wordGreedy (wordOracle which O) xs []) [])
    (by rw [hg]; rfl) (by rw [hg]; rfl)
  rw [hg] at h
  have hre : restartControl (greedyConfig (greedyRegisters R [] [] (wordGreedy (wordOracle which O) xs []) [])
      26 (q+greedyCalls xs) (c+greedyWork n xs)) (0 : Fin 7)=
      popcountConfig (greedyRegisters R [] [] (wordGreedy (wordOracle which O) xs []) []) 0 (q+greedyCalls xs) (c+greedyWork n xs) := rfl
  rw [hre,hp] at h
  simpa [rankProgram,rankConfig,rankTime,rankWork,rankBits,relabelConfig,greedyConfig,popcountConfig,
    firstLabel,secondLabel,hn,Nat.add_assoc] using h

end

section

variable {k n : ℕ}
lemma compareBits_correct (b : Bool) (xs ys : List Bool) :
    compareBits b xs ys=true ↔ binaryValue xs<binaryValue ys ∨ (binaryValue xs=binaryValue ys ∧ b=true) := by
  induction xs generalizing b ys with
  | nil =>
    induction ys generalizing b with
    | nil => simp [compareBits,binaryValue]
    | cons y ys ih =>
      rw [compareBits,ih]
      cases b <;> cases y <;> simp [binaryValue] <;> omega
  | cons x xs ih =>
    cases ys with
    | nil =>
      rw [compareBits,ih]
      cases b <;> cases x <;> simp [binaryValue]
    | cons y ys =>
      rw [compareBits,ih]
      cases b <;> cases x <;> cases y <;> simp [binaryValue] <;> omega
lemma compareBits_lt (xs ys : List Bool) : compareBits false xs ys=true ↔ binaryValue xs<binaryValue ys := by
  simp [compareBits_correct]

theorem comparison_run (a b : Fin (k+8)) (hab : a≠b) (O : IndependenceOracle n)
    (R : Fin (k+8) → List Bool) (xs ys : List Bool) (lt : Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution (compareProgram a b) O (compareConfig (pairRegisters R a b xs ys) (if lt then 4 else 0) q c) bits
      (2*max xs.length ys.length+2)=
      compareConfig (pairRegisters R a b [] []) (if compareBits lt xs ys then 9 else 8) q
        (c+(2*max xs.length ys.length+2)) := by
  induction xs generalizing lt ys c bits with
  | nil =>
    induction ys generalizing lt c bits with
    | nil => cases lt <;> simp [execution,machineStep,compareProgram,compareConfig,pairRegisters_a _ _ _ hab,pairRegisters_b,compareBits]
    | cons y ys ih =>
      have hstep : execution (compareProgram a b) O (compareConfig (pairRegisters R a b [] (y::ys))
          (if lt then 4 else 0) q c) bits 2=
          compareConfig (pairRegisters R a b [] ys) (if (if y then true else lt) then 4 else 0) q (c+2) := by
        cases lt <;> cases y <;> simp [execution,machineStep,compareProgram,compareConfig,
          pairRegisters_a _ _ _ hab,pairRegisters_b,pairRegisters_update_b]
      simp only [List.length_nil,List.length_cons,Nat.zero_max]
      rw [show 2*(ys.length+1)+2=2+(2*ys.length+2) by omega,execution_add,hstep]
      simpa [compareBits,Nat.add_assoc] using ih (if y then true else lt) (c+2) (fun i => bits (2+i))
  | cons x xs ih =>
    cases ys with
    | nil =>
      have hstep : execution (compareProgram a b) O (compareConfig (pairRegisters R a b (x::xs) [])
          (if lt then 4 else 0) q c) bits 2=
          compareConfig (pairRegisters R a b xs []) (if (if x then false else lt) then 4 else 0) q (c+2) := by
        cases lt <;> cases x <;> simp [execution,machineStep,compareProgram,compareConfig,
          pairRegisters_a _ _ _ hab,pairRegisters_b,pairRegisters_update_a _ _ _ hab]
      simp only [List.length_nil,List.length_cons,Nat.max_zero]
      rw [show 2*(xs.length+1)+2=2+(2*xs.length+2) by omega,execution_add,hstep]
      simpa [compareBits,Nat.add_assoc] using ih [] (if x then false else lt) (c+2) (fun i => bits (2+i))
    | cons y ys =>
      have hstep : execution (compareProgram a b) O (compareConfig (pairRegisters R a b (x::xs) (y::ys))
          (if lt then 4 else 0) q c) bits 2=
          compareConfig (pairRegisters R a b xs ys) (if (if x=y then lt else y) then 4 else 0) q (c+2) := by
        cases lt <;> cases x <;> cases y <;> simp [execution,machineStep,compareProgram,compareConfig,
          pairRegisters_a _ _ _ hab,pairRegisters_b,pairRegisters_update_a _ _ _ hab,pairRegisters_update_b]
      simp only [List.length_cons,max_add_add_right]
      rw [show 2*(max xs.length ys.length+1)+2=2+(2*max xs.length ys.length+2) by omega,execution_add,hstep]
      simpa [compareBits,Nat.add_assoc] using ih ys (if x=y then lt else y) (c+2) (fun i => bits (2+i))

theorem comparison_block (a b : Fin (k+8)) (hab : a≠b) (O : IndependenceOracle n)
    (R : Fin (k+8) → List Bool) (xs ys : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    let t := 2*max xs.length ys.length+2
    execution (compareProgram a b) O (compareConfig (pairRegisters R a b xs ys) 0 q c) bits t=
      compareConfig (pairRegisters R a b [] []) (if binaryValue xs<binaryValue ys then 9 else 8) q (c+t) := by
  simpa only [Bool.false_eq_true,ite_false,compareBits_lt] using comparison_run a b hab O R xs ys false q c bits

lemma subDigits_value (c : Bool) (xs ys : List Bool)
    (h : binaryValue ys+(if c then 1 else 0)≤binaryValue xs) :
    binaryValue (subDigits c xs ys)+binaryValue ys+(if c then 1 else 0)=binaryValue xs := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp_all [subDigits,binaryValue]
    | cons y ys ih =>
      cases y <;> cases c <;> simp_all [binaryValue,subDigits,subBorrow,sumDigit]
  | cons x xs ih =>
    cases ys with
    | nil =>
      have ht : binaryValue []+(if subBorrow x false c then 1 else 0)≤binaryValue xs := by
        cases x <;> cases c <;> simp_all [binaryValue,subBorrow] ; omega
      have hi := ih (subBorrow x false c) [] ht
      simp only [subDigits,binaryValue]
      cases x <;> cases c <;> simp [subBorrow,sumDigit,binaryValue] at hi h ⊢ <;> omega
    | cons y ys =>
      have ht : binaryValue ys+(if subBorrow x y c then 1 else 0)≤binaryValue xs := by
        cases x <;> cases y <;> cases c <;> simp_all [binaryValue,subBorrow] <;> omega
      have hi := ih (subBorrow x y c) ys ht
      simp only [subDigits,binaryValue]
      cases x <;> cases y <;> cases c <;> simp [subBorrow,sumDigit,binaryValue] at hi h ⊢ <;> omega
lemma subDigits_length_cost (c : Bool) (xs ys : List Bool) :
    (subDigits c xs ys).length≤xs.length+ys.length+1 ∧
      subCost c xs ys≤3*(xs.length+ys.length)+3 := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [subDigits,subCost]
    | cons y ys ih =>
      have hi := ih (subBorrow false y c)
      simp only [subDigits,subCost,List.length_cons,List.length_nil] at *
      constructor <;> omega
  | cons x xs ih =>
    cases ys with
    | nil =>
      have hi := ih (subBorrow x false c) []
      simp only [subDigits,subCost,List.length_cons,List.length_nil] at *
      constructor <;> omega
    | cons y ys =>
      have hi := ih (subBorrow x y c) ys
      simp only [subDigits,subCost,List.length_cons] at *
      constructor <;> omega

lemma sub_build (a b d : Fin (k+8)) (hab : a≠b) (had : a≠d) (hbd : b≠d)
    (O : IndependenceOracle n) (R : Fin (k+8) → List Bool) (xs ys zs : List Bool)
    (carry : Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution (subProgram a b d) O
      (subConfig (tripleRegisters R a b d xs ys zs) (if carry then 1 else 0) q c) bits
      (subCost carry xs ys)=subConfig
        (tripleRegisters R a b d [] [] ((subDigits carry xs ys).reverse++zs)) 12 q (c+subCost carry xs ys) := by
  induction xs generalizing ys zs carry c bits with
  | nil =>
    induction ys generalizing zs carry c bits with
    | nil =>
      cases carry <;> simp [subCost,subDigits,execution,machineStep,subProgram,subConfig,
        tripleRegisters_a _ _ _ _ hab had,tripleRegisters_b _ _ _ _ hbd,]
    | cons y ys ih =>
      have ht : execution (subProgram a b d) O
          (subConfig (tripleRegisters R a b d [] (y::ys) zs) (if carry then 1 else 0) q c) bits 3=
          subConfig (tripleRegisters R a b d [] ys (sumDigit false y carry::zs))
            (if subBorrow false y carry then 1 else 0) q (c+3) := by
        cases y <;> cases carry <;> simp [execution,machineStep,subProgram,subConfig,sumDigit,subBorrow,
          tripleRegisters_a _ _ _ _ hab had,tripleRegisters_b _ _ _ _ hbd,tripleRegisters_d,
          tripleRegisters_update_b _ _ _ _ hbd,tripleRegisters_update_d]
      rw [subCost,execution_add,ht,ih]
      simp only [subDigits,List.reverse_cons,List.append_assoc,List.singleton_append]
      congr 1 ; omega
  | cons x xs ih =>
    cases ys with
    | nil =>
      have ht : execution (subProgram a b d) O
          (subConfig (tripleRegisters R a b d (x::xs) [] zs) (if carry then 1 else 0) q c) bits 3=
          subConfig (tripleRegisters R a b d xs [] (sumDigit x false carry::zs))
            (if subBorrow x false carry then 1 else 0) q (c+3) := by
        cases x <;> cases carry <;> simp [execution,machineStep,subProgram,subConfig,sumDigit,subBorrow,
          tripleRegisters_a _ _ _ _ hab had,tripleRegisters_b _ _ _ _ hbd,tripleRegisters_d,
          tripleRegisters_update_a _ _ _ _ hab had,tripleRegisters_update_d]
      rw [subCost,execution_add,ht,ih]
      simp only [subDigits,List.reverse_cons,List.append_assoc,List.singleton_append]
      congr 1 ; omega
    | cons y ys =>
      have ht : execution (subProgram a b d) O
          (subConfig (tripleRegisters R a b d (x::xs) (y::ys) zs) (if carry then 1 else 0) q c) bits 3=
          subConfig (tripleRegisters R a b d xs ys (sumDigit x y carry::zs))
            (if subBorrow x y carry then 1 else 0) q (c+3) := by
        cases x <;> cases y <;> cases carry <;> simp [execution,machineStep,subProgram,subConfig,sumDigit,subBorrow,
          tripleRegisters_a _ _ _ _ hab had,tripleRegisters_b _ _ _ _ hbd,tripleRegisters_d,
          tripleRegisters_update_a _ _ _ _ hab had,tripleRegisters_update_b _ _ _ _ hbd,
          tripleRegisters_update_d]
      rw [subCost,execution_add,ht,ih]
      simp only [subDigits,List.reverse_cons,List.append_assoc,List.singleton_append]
      congr 1 ; omega
lemma sub_restore (a b d : Fin (k+8)) (hab : a≠b) (had : a≠d) (_ : b≠d)
    (O : IndependenceOracle n) (R : Fin (k+8) → List Bool) (xs ys zs : List Bool)
    (q c : ℕ) (bits : ℕ → Bool) :
    execution (subProgram a b d) O (subConfig (tripleRegisters R a b d xs ys zs) 12 q c) bits
      (2*zs.length+1)=subConfig (tripleRegisters R a b d (zs.reverse++xs) ys []) 16 q (c+2*zs.length+1) := by
  induction zs generalizing xs c bits with
  | nil => simp [execution,machineStep,subProgram,subConfig,tripleRegisters_d]
  | cons z zs ih =>
    have ht : execution (subProgram a b d) O (subConfig (tripleRegisters R a b d xs ys (z::zs)) 12 q c) bits 2=
        subConfig (tripleRegisters R a b d (z::xs) ys zs) 12 q (c+2) := by
      cases z <;> simp [execution,machineStep,subProgram,subConfig,tripleRegisters_a _ _ _ _ hab had,
        tripleRegisters_d,tripleRegisters_update_a _ _ _ _ hab had,tripleRegisters_update_d]
    rw [List.length_cons,show 2*(zs.length+1)+1=2+(2*zs.length+1) by omega,execution_add,ht,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
    congr 1 ; omega

theorem subtraction_block (a b d : Fin (k+8)) (hab : a≠b) (had : a≠d) (hbd : b≠d)
    (O : IndependenceOracle n) (R : Fin (k+8) → List Bool) (xs ys : List Bool)
    (hxy : binaryValue ys≤binaryValue xs) (q c : ℕ) (bits : ℕ → Bool) :
    let z := subDigits false xs ys
    let t := subCost false xs ys+2*z.length+1
    binaryValue z=binaryValue xs-binaryValue ys ∧ t≤5*(xs.length+ys.length)+6 ∧
      execution (subProgram a b d) O (subConfig (tripleRegisters R a b d xs ys []) 0 q c) bits t=
        subConfig (tripleRegisters R a b d z [] []) 16 q (c+t) := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · have h := subDigits_value false xs ys (by simpa using hxy)
    simp only [Bool.false_eq_true,ite_false,Nat.add_zero] at h
    omega
  · have h := subDigits_length_cost false xs ys
    omega
  · rw [show subCost false xs ys+2*(subDigits false xs ys).length+1=
        subCost false xs ys+(2*(subDigits false xs ys).length+1) by omega,execution_add]
    rw [show (0 : Fin 17)=(if false then 1 else 0) by rfl,sub_build a b d hab had hbd]
    simp only [List.append_nil]
    rw [←List.length_reverse (as:=subDigits false xs ys),sub_restore a b d hab had hbd]
    simp only [List.reverse_reverse,List.length_reverse,List.append_nil]
    congr 1 ; omega

end

section

variable {k s t n : ℕ}
lemma execution_relabel_before_any_halt (P : Program k s) (Q : Program k t)
    (e : Fin (s+1) → Fin (t+1))
    (h : ∀ i,P i≠.halt → Q (e i)=(P i).relabel e) (O : IndependenceOracle n)
    (c : MachineConfig k s) (bits : ℕ → Bool) (u : ℕ)
    (hu : (execution P O c bits u).output=none) :
    execution Q O (relabelConfig e c) bits u=relabelConfig e (execution P O c bits u) := by
  induction u with
  | zero => rfl
  | succ u ih =>
    have hn := machineStep_none_pre P O (bits u) (execution P O c bits u) hu
    have hh := machineStep_none_not_halt P O (bits u) (execution P O c bits u) hu
    simp only [execution,ih hn]
    exact machineStep_relabel P Q e O _ _ (h _ hh)

lemma execution_of_output (P : Program k s) (O : IndependenceOracle n)
    (c : MachineConfig k s) (bits : ℕ → Bool) (u : ℕ) (h : c.output.isSome) :
    execution P O c bits u=c := by
  induction u with
  | zero => rfl
  | succ u ih => simp [execution,ih,machineStep,h]
lemma execution_extend_output (P : Program k s) (O : IndependenceOracle n)
    (c : MachineConfig k s) (bits : ℕ → Bool) (u B : ℕ) (hu : u≤B)
    (h : (execution P O c bits u).output.isSome) :
    execution P O c bits B=execution P O c bits u := by
  rw [show B=u+(B-u) by omega,execution_add]
  exact execution_of_output P O _ _ _ h

end

section

variable {k n : ℕ}
@[simp] lemma workReg_ne05 : (0 : Fin (k+8))≠5 := workReg_ne (a:=0) (b:=5) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne06 : (0 : Fin (k+8))≠6 := workReg_ne (a:=0) (b:=6) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne15 : (1 : Fin (k+8))≠5 := workReg_ne (a:=1) (b:=5) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne16 : (1 : Fin (k+8))≠6 := workReg_ne (a:=1) (b:=6) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne25 : (2 : Fin (k+8))≠5 := workReg_ne (a:=2) (b:=5) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne26 : (2 : Fin (k+8))≠6 := workReg_ne (a:=2) (b:=6) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne35 : (3 : Fin (k+8))≠5 := workReg_ne (a:=3) (b:=5) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne36 : (3 : Fin (k+8))≠6 := workReg_ne (a:=3) (b:=6) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne45 : (4 : Fin (k+8))≠5 := workReg_ne (a:=4) (b:=5) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne46 : (4 : Fin (k+8))≠6 := workReg_ne (a:=4) (b:=6) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne50 : (5 : Fin (k+8))≠0 := workReg_ne (a:=5) (b:=0) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne51 : (5 : Fin (k+8))≠1 := workReg_ne (a:=5) (b:=1) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne52 : (5 : Fin (k+8))≠2 := workReg_ne (a:=5) (b:=2) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne53 : (5 : Fin (k+8))≠3 := workReg_ne (a:=5) (b:=3) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne54 : (5 : Fin (k+8))≠4 := workReg_ne (a:=5) (b:=4) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne56 : (5 : Fin (k+8))≠6 := workReg_ne (a:=5) (b:=6) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne60 : (6 : Fin (k+8))≠0 := workReg_ne (a:=6) (b:=0) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne61 : (6 : Fin (k+8))≠1 := workReg_ne (a:=6) (b:=1) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne62 : (6 : Fin (k+8))≠2 := workReg_ne (a:=6) (b:=2) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne63 : (6 : Fin (k+8))≠3 := workReg_ne (a:=6) (b:=3) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne64 : (6 : Fin (k+8))≠4 := workReg_ne (a:=6) (b:=4) (by omega) (by omega) (by omega)
@[simp] lemma workReg_ne65 : (6 : Fin (k+8))≠5 := workReg_ne (a:=6) (b:=5) (by omega) (by omega) (by omega)
lemma divRegisters_copyR_in (R : Fin (k+8) → List Bool) (xs ys zs ws as bs : List Bool)  :
    tripleRegisters (divRegisters R xs ys zs ws as bs) 2 4 5 zs [] as=divRegisters R xs ys zs ws as bs := by
  funext i
  by_cases h0 : i=0 <;> by_cases h1 : i=1 <;> by_cases h2 : i=2 <;> by_cases h3 : i=3 <;> by_cases h4 : i=4 <;> by_cases h5 : i=5 <;> by_cases h6 : i=6 <;>
    simp_all [divRegisters,tripleRegisters,pairRegisters]
lemma divRegisters_copyR_out (R : Fin (k+8) → List Bool) (xs ys zs ws bs : List Bool)  :
    tripleRegisters (divRegisters R xs ys zs ws [] bs) 2 4 5 zs [] zs=divRegisters R xs ys zs ws zs bs := by
  funext i
  by_cases h0 : i=0 <;> by_cases h1 : i=1 <;> by_cases h2 : i=2 <;> by_cases h3 : i=3 <;> by_cases h4 : i=4 <;> by_cases h5 : i=5 <;> by_cases h6 : i=6 <;>
    simp_all [divRegisters,tripleRegisters,pairRegisters]
lemma divRegisters_copyD_in (R : Fin (k+8) → List Bool) (xs ys zs ws as bs : List Bool)  :
    tripleRegisters (divRegisters R xs ys zs ws as bs) 1 4 6 ys [] bs=divRegisters R xs ys zs ws as bs := by
  funext i
  by_cases h0 : i=0 <;> by_cases h1 : i=1 <;> by_cases h2 : i=2 <;> by_cases h3 : i=3 <;> by_cases h4 : i=4 <;> by_cases h5 : i=5 <;> by_cases h6 : i=6 <;>
    simp_all [divRegisters,tripleRegisters,pairRegisters]
lemma divRegisters_copyD_out (R : Fin (k+8) → List Bool) (xs ys zs ws as : List Bool)  :
    tripleRegisters (divRegisters R xs ys zs ws as []) 1 4 6 ys [] ys=divRegisters R xs ys zs ws as ys := by
  funext i
  by_cases h0 : i=0 <;> by_cases h1 : i=1 <;> by_cases h2 : i=2 <;> by_cases h3 : i=3 <;> by_cases h4 : i=4 <;> by_cases h5 : i=5 <;> by_cases h6 : i=6 <;>
    simp_all [divRegisters,tripleRegisters,pairRegisters]
lemma divRegisters_compare_in (R : Fin (k+8) → List Bool) (xs ys zs ws as bs : List Bool)  :
    pairRegisters (divRegisters R xs ys zs ws as bs) 5 6 as bs=divRegisters R xs ys zs ws as bs := by
  funext i
  by_cases h0 : i=0 <;> by_cases h1 : i=1 <;> by_cases h2 : i=2 <;> by_cases h3 : i=3 <;> by_cases h4 : i=4 <;> by_cases h5 : i=5 <;> by_cases h6 : i=6 <;>
    simp_all [divRegisters,pairRegisters]
lemma divRegisters_compare_out (R : Fin (k+8) → List Bool) (xs ys zs ws as bs : List Bool)  :
    pairRegisters (divRegisters R xs ys zs ws as bs) 5 6 [] []=divRegisters R xs ys zs ws [] [] := by
  funext i
  by_cases h0 : i=0 <;> by_cases h1 : i=1 <;> by_cases h2 : i=2 <;> by_cases h3 : i=3 <;> by_cases h4 : i=4 <;> by_cases h5 : i=5 <;> by_cases h6 : i=6 <;>
    simp_all [divRegisters,pairRegisters]
lemma divRegisters_copyS_in (R : Fin (k+8) → List Bool) (xs ys zs ws as bs : List Bool)  :
    tripleRegisters (divRegisters R xs ys zs ws as bs) 1 4 5 ys [] as=divRegisters R xs ys zs ws as bs := by
  funext i
  by_cases h0 : i=0 <;> by_cases h1 : i=1 <;> by_cases h2 : i=2 <;> by_cases h3 : i=3 <;> by_cases h4 : i=4 <;> by_cases h5 : i=5 <;> by_cases h6 : i=6 <;>
    simp_all [divRegisters,tripleRegisters,pairRegisters]
lemma divRegisters_copyS_out (R : Fin (k+8) → List Bool) (xs ys zs ws bs : List Bool)  :
    tripleRegisters (divRegisters R xs ys zs ws [] bs) 1 4 5 ys [] ys=divRegisters R xs ys zs ws ys bs := by
  funext i
  by_cases h0 : i=0 <;> by_cases h1 : i=1 <;> by_cases h2 : i=2 <;> by_cases h3 : i=3 <;> by_cases h4 : i=4 <;> by_cases h5 : i=5 <;> by_cases h6 : i=6 <;>
    simp_all [divRegisters,tripleRegisters,pairRegisters]
lemma divRegisters_sub_in (R : Fin (k+8) → List Bool) (xs ys zs ws as bs : List Bool)  :
    tripleRegisters (divRegisters R xs ys zs ws as bs) 2 5 4 zs as []=divRegisters R xs ys zs ws as bs := by
  funext i
  by_cases h0 : i=0 <;> by_cases h1 : i=1 <;> by_cases h2 : i=2 <;> by_cases h3 : i=3 <;> by_cases h4 : i=4 <;> by_cases h5 : i=5 <;> by_cases h6 : i=6 <;>
    simp_all [divRegisters,tripleRegisters,pairRegisters]
lemma divRegisters_sub_out (R : Fin (k+8) → List Bool) (xs ys zs ws as bs : List Bool) (us : List Bool) :
    tripleRegisters (divRegisters R xs ys zs ws as bs) 2 5 4 us [] []=divRegisters R xs ys us ws [] bs := by
  funext i
  by_cases h0 : i=0 <;> by_cases h1 : i=1 <;> by_cases h2 : i=2 <;> by_cases h3 : i=3 <;> by_cases h4 : i=4 <;> by_cases h5 : i=5 <;> by_cases h6 : i=6 <;>
    simp_all [divRegisters,tripleRegisters,pairRegisters]
lemma divRegisters_update0 (R : Fin (k+8) → List Bool) (xs ys zs ws as bs : List Bool) (us : List Bool) :
    Function.update (divRegisters R xs ys zs ws as bs) 0 us=divRegisters R us ys zs ws as bs := by
  funext i
  by_cases h0 : i=0 <;> by_cases h1 : i=1 <;> by_cases h2 : i=2 <;> by_cases h3 : i=3 <;> by_cases h4 : i=4 <;> by_cases h5 : i=5 <;> by_cases h6 : i=6 <;>
    simp_all [divRegisters,]
lemma divRegisters_update2 (R : Fin (k+8) → List Bool) (xs ys zs ws as bs : List Bool) (us : List Bool) :
    Function.update (divRegisters R xs ys zs ws as bs) 2 us=divRegisters R xs ys us ws as bs := by
  funext i
  by_cases h0 : i=0 <;> by_cases h1 : i=1 <;> by_cases h2 : i=2 <;> by_cases h3 : i=3 <;> by_cases h4 : i=4 <;> by_cases h5 : i=5 <;> by_cases h6 : i=6 <;>
    simp_all [divRegisters,]
lemma divRegisters_update3 (R : Fin (k+8) → List Bool) (xs ys zs ws as bs : List Bool) (us : List Bool) :
    Function.update (divRegisters R xs ys zs ws as bs) 3 us=divRegisters R xs ys zs us as bs := by
  funext i
  by_cases h0 : i=0 <;> by_cases h1 : i=1 <;> by_cases h2 : i=2 <;> by_cases h3 : i=3 <;> by_cases h4 : i=4 <;> by_cases h5 : i=5 <;> by_cases h6 : i=6 <;>
    simp_all [divRegisters,]
lemma divCopies_exit : (divCopies : Program k 16) (lastLabel 16)=.halt := by
  simp [divCopies,concatProgram,lastLabel,copyProgram,Instruction.relabel]
lemma divSubtract_exit : (divSubtract : Program k 24) (lastLabel 24)=.halt := by
  simp [divSubtract,concatProgram,lastLabel,subProgram,Instruction.relabel]
lemma divCopies_run (O : IndependenceOracle n) (R : Fin (k+8) → List Bool)
    (xs ys zs ws : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution divCopies O (divCopiesConfig (divRegisters R xs ys zs ws [] []) 0 q c) bits
      ((5*zs.length+2)+(5*ys.length+2))=
      divCopiesConfig (divRegisters R xs ys zs ws zs ys) 16 q (c+((5*zs.length+2)+(5*ys.length+2))) := by
  have hc := copy_block (k:=k) (2 : Fin (k+8)) 4 5 (by simp) (by simp) (by simp)
    O (divRegisters R xs ys zs ws [] []) zs [] q c bits
  simp only [List.append_nil,divRegisters_copyR_in,divRegisters_copyR_out] at hc
  have hd := copy_block (k:=k) (1 : Fin (k+8)) 4 6 (by simp) (by simp) (by simp)
    O (divRegisters R xs ys zs ws zs []) ys [] q (c+(5*zs.length+2)) (fun i => bits (5*zs.length+2+i))
  simp only [List.append_nil,divRegisters_copyD_in,divRegisters_copyD_out] at hd
  have hh := concat_run (copyProgram (k:=k) 2 4 5) (copyProgram 1 4 6) (by rfl) O
    (copyConfig (divRegisters R xs ys zs ws [] []) 0 q c) bits (5*zs.length+2) (5*ys.length+2)
    (by rw [hc]; rfl) (by rw [hc]; rfl)
  rw [hc] at hh
  have hre : restartControl (copyConfig (divRegisters R xs ys zs ws zs []) 8 q (c+5*zs.length+2))
      (0 : Fin 9)=copyConfig (divRegisters R xs ys zs ws zs []) 0 q (c+(5*zs.length+2)) := by
    simp [restartControl,copyConfig,Nat.add_assoc]
  rw [hre,hd] at hh
  simpa [divCopies,divCopiesConfig,copyConfig,relabelConfig,firstLabel,secondLabel,Nat.add_assoc] using hh

lemma divCheck_run (O : IndependenceOracle n) (R : Fin (k+8) → List Bool)
    (xs ys zs ws : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution divCheck O (divCheckConfig (divRegisters R xs ys zs ws [] []) 0 q c) bits
      (divCheckCost ys zs)=
      divCheckConfig (divRegisters R xs ys zs ws [] []) (if binaryValue zs<binaryValue ys then 25 else 24) q (c+divCheckCost ys zs) := by
  have hc := divCopies_run O R xs ys zs ws q c bits
  have hd := comparison_block (k:=k) (5 : Fin (k+8)) 6 (by simp) O
    (divRegisters R xs ys zs ws zs ys) zs ys q (c+((5*zs.length+2)+(5*ys.length+2)))
      (fun i => bits ((5*zs.length+2)+(5*ys.length+2)+i))
  dsimp only at hd
  simp only [divRegisters_compare_in,divRegisters_compare_out] at hd
  have hh := concat_run (divCopies : Program k 16) (compareProgram 5 6) divCopies_exit O
    (divCopiesConfig (divRegisters R xs ys zs ws [] []) 0 q c) bits
      ((5*zs.length+2)+(5*ys.length+2)) (2*max zs.length ys.length+2)
      (by rw [hc]; rfl) (by rw [hc]; rfl)
  rw [hc] at hh
  have hre : restartControl (divCopiesConfig (divRegisters R xs ys zs ws zs ys) 16 q (c+((5*zs.length+2)+(5*ys.length+2))))
      (0 : Fin 10)=compareConfig (divRegisters R xs ys zs ws zs ys) 0 q (c+((5*zs.length+2)+(5*ys.length+2))) := rfl
  rw [hre,hd] at hh
  split_ifs at hh ⊢ <;> simpa [divCheck,divCheckCost,divCopiesConfig,divCheckConfig,compareConfig,relabelConfig,firstLabel,secondLabel,Nat.add_assoc] using hh

lemma divSubtract_run (O : IndependenceOracle n) (R : Fin (k+8) → List Bool)
    (xs ys zs ws : List Bool) (hzy : binaryValue ys≤binaryValue zs) (q c : ℕ) (bits : ℕ → Bool) :
    execution divSubtract O (divSubtractConfig (divRegisters R xs ys zs ws [] []) 0 q c) bits
      (divSubtractCost ys zs)=
      divSubtractConfig (divRegisters R xs ys (subDigits false zs ys) ws [] []) 24 q (c+divSubtractCost ys zs) := by
  have hc := copy_block (k:=k) (1 : Fin (k+8)) 4 5 (by simp) (by simp) (by simp)
    O (divRegisters R xs ys zs ws [] []) ys [] q c bits
  simp only [List.append_nil,divRegisters_copyS_in,divRegisters_copyS_out] at hc
  have hd := (subtraction_block (k:=k) (2 : Fin (k+8)) 5 4 (by simp) (by simp) (by simp)
    O (divRegisters R xs ys zs ws ys []) zs ys hzy q (c+(5*ys.length+2))
      (fun i => bits (5*ys.length+2+i))).2.2
  simp only [divRegisters_sub_in,divRegisters_sub_out] at hd
  have hh := concat_run (copyProgram (k:=k) 1 4 5) (subProgram 2 5 4) (by rfl) O
    (copyConfig (divRegisters R xs ys zs ws [] []) 0 q c) bits (5*ys.length+2)
      (subCost false zs ys+2*(subDigits false zs ys).length+1)
      (by rw [hc]; rfl) (by rw [hc]; rfl)
  rw [hc] at hh
  have hre : restartControl (copyConfig (divRegisters R xs ys zs ws ys []) 8 q (c+5*ys.length+2))
      (0 : Fin 17)=subConfig (divRegisters R xs ys zs ws ys []) 0 q (c+(5*ys.length+2)) := by
    simp [restartControl,copyConfig,subConfig,Nat.add_assoc]
  rw [hre,hd] at hh
  simpa [divSubtract,divSubtractCost,divSubtractConfig,copyConfig,subConfig,relabelConfig,firstLabel,secondLabel,Nat.add_assoc] using hh

lemma division_check_table (i : Fin 26) (hi : (divCheck : Program k 25) i≠.halt) :
    (divisionProgram : Program k 53) (divisionCheckLabel i)=
      ((divCheck : Program k 25) i).relabel divisionCheckLabel := by
  have hil : i.val<24 := by
    by_contra hh
    have he : i=24 ∨ i=25 := by
      have hl := i.isLt
      rcases (show i.val=24 ∨ i.val=25 by omega) with h|h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases he with rfl|rfl <;> exact hi rfl
  simp [divisionCheckLabel,hil,divisionProgram,
    show ¬3+i.val=1 by omega,show ¬3+i.val=2 by omega,show 3+i.val<27 by omega]
lemma division_sub_table (i : Fin 25) (hi : i≠lastLabel 24) :
    (divisionProgram : Program k 53) (divisionSubLabel i)=
      ((divSubtract : Program k 24) i).relabel divisionSubLabel := by
  have hil : i.val<24 := by
    have hn : i.val≠24 := by intro h; exact hi (Fin.ext h)
    omega
  simp [divisionSubLabel,divisionProgram,
    show ¬27+i.val=1 by omega,show ¬27+i.val=2 by omega,
    show ¬27+i.val<27 by omega,show 27+i.val<51 by omega]
lemma division_check_run (O : IndependenceOracle n) (R : Fin (k+8) → List Bool)
    (xs ys zs ws : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution divisionProgram O (divisionConfig (divRegisters R xs ys zs ws [] []) 3 q c) bits
      (divCheckCost ys zs)=divisionConfig (divRegisters R xs ys zs ws [] [])
        (if binaryValue zs<binaryValue ys then 52 else 27) q (c+divCheckCost ys zs) := by
  have h := execution_relabel_before_any_halt (divCheck : Program k 25) divisionProgram divisionCheckLabel
    division_check_table O (divCheckConfig (divRegisters R xs ys zs ws [] []) 0 q c) bits
      (divCheckCost ys zs) (by rw [divCheck_run]; rfl)
  rw [divCheck_run] at h
  split_ifs at h ⊢ <;> simpa [relabelConfig,divCheckConfig,divisionConfig,divisionCheckLabel] using h
lemma division_sub_run (O : IndependenceOracle n) (R : Fin (k+8) → List Bool)
    (xs ys zs ws : List Bool) (hzy : binaryValue ys≤binaryValue zs) (q c : ℕ) (bits : ℕ → Bool) :
    execution divisionProgram O (divisionConfig (divRegisters R xs ys zs ws [] []) 27 q c) bits
      (divSubtractCost ys zs)=divisionConfig (divRegisters R xs ys (subDigits false zs ys) ws [] [])
        51 q (c+divSubtractCost ys zs) := by
  have h := execution_relabel_before_halt (divSubtract : Program k 24) divisionProgram divisionSubLabel
    (lastLabel 24) divSubtract_exit division_sub_table O
    (divSubtractConfig (divRegisters R xs ys zs ws [] []) 0 q c) bits (divSubtractCost ys zs)
    (by rw [divSubtract_run O R xs ys zs ws hzy]; rfl)
  rw [divSubtract_run O R xs ys zs ws hzy] at h
  simpa [relabelConfig,divSubtractConfig,divisionConfig,divisionSubLabel] using h

lemma division_digit_run (O : IndependenceOracle n) (R : Fin (k+8) → List Bool)
    (x : Bool) (xs ys zs ws : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution divisionProgram O (divisionConfig (divRegisters R (x::xs) ys zs ws [] []) 0 q c) bits
      (divisionDigitCost ys (x::zs))=
      divisionConfig (divRegisters R xs ys (divisionRemainder ys (x::zs))
        (divisionDigit ys (x::zs)::ws) [] []) 0 q (c+divisionDigitCost ys (x::zs)) := by
  have hp : execution divisionProgram O
      (divisionConfig (divRegisters R (x::xs) ys zs ws [] []) 0 q c) bits 2=
      divisionConfig (divRegisters R xs ys (x::zs) ws [] []) 3 q (c+2) := by
    cases x <;> simp [execution,machineStep,divisionProgram,divisionConfig,
      divRegisters_update0,divRegisters_update2,divRegisters]
  unfold divisionDigitCost
  rw [show 2+divCheckCost ys (x::zs)+(if binaryValue (x::zs)<binaryValue ys then 0 else divSubtractCost ys (x::zs))+1=
    2+(divCheckCost ys (x::zs)+((if binaryValue (x::zs)<binaryValue ys then 0 else divSubtractCost ys (x::zs))+1)) by omega]
  rw [execution_add,hp,execution_add,division_check_run]
  by_cases hl : binaryValue (x::zs)<binaryValue ys
  · have hn : ¬binaryValue ys≤binaryValue (x::zs) := by omega
    simp [hl,divisionRemainder,divisionDigit,hn,execution,machineStep,divisionProgram,divisionConfig,
      divRegisters_update3,divRegisters,Nat.add_assoc]
  · have hn : binaryValue ys≤binaryValue (x::zs) := by omega
    simp only [hl,ite_false]
    rw [execution_add,division_sub_run O R xs ys (x::zs) ws hn]
    simp [divisionRemainder,divisionDigit,hl,hn,execution,machineStep,divisionProgram,divisionConfig,
      divRegisters_update3,divRegisters,Nat.add_assoc]

theorem division_machine_run (O : IndependenceOracle n) (R : Fin (k+8) → List Bool)
    (xs ys zs ws : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution divisionProgram O (divisionConfig (divRegisters R xs ys zs ws [] []) 0 q c) bits
      (divisionCost xs ys zs)=divisionConfig
        (divRegisters R [] ys (divisionWords xs ys zs ws).1 (divisionWords xs ys zs ws).2 [] [])
        53 q (c+divisionCost xs ys zs) := by
  induction xs generalizing zs ws c bits with
  | nil => simp [divisionCost,divisionWords,execution,machineStep,divisionProgram,divisionConfig,divRegisters]
  | cons x xs ih =>
    rw [divisionCost,execution_add,division_digit_run,ih]
    simp only [divisionWords,Nat.add_assoc]

lemma binaryValue_append (xs ys : List Bool) :
    binaryValue (xs++ys)=binaryValue xs+2^xs.length*binaryValue ys := by
  induction xs with
  | nil => simp [binaryValue]
  | cons x xs ih =>
    simp only [List.cons_append,binaryValue,ih,List.length_cons,pow_succ]
    ring

lemma streamValue_eq (xs : List Bool) (a : ℕ) :
    streamValue xs a=binaryValue xs.reverse+2^xs.length*a := by
  induction xs generalizing a with
  | nil => simp [streamValue,binaryValue]
  | cons x xs ih =>
    simp only [streamValue,ih,List.reverse_cons,binaryValue_append,List.length_reverse,
      List.length_cons,pow_succ,binaryValue]
    ring
lemma division_step_math (x : Bool) (ys zs : List Bool) (hr : binaryValue zs<binaryValue ys) :
    binaryValue (divisionRemainder ys (x::zs))<binaryValue ys ∧
      binaryValue (divisionRemainder ys (x::zs))+
        binaryValue ys*(if divisionDigit ys (x::zs) then 1 else 0)=binaryValue (x::zs) := by
  by_cases hl : binaryValue (x::zs)<binaryValue ys
  · have hn : ¬binaryValue ys≤binaryValue (x::zs) := by omega
    simp [divisionRemainder,divisionDigit,hl,hn]
  · have hn : binaryValue ys≤binaryValue (x::zs) := by omega
    have hv := subDigits_value false (x::zs) ys (by simpa using hn)
    simp only [Bool.false_eq_true,ite_false,Nat.add_zero] at hv
    simp only [divisionRemainder,divisionDigit,hl,ite_false,hn,decide_true,ite_true,Nat.mul_one]
    refine ⟨?_,hv⟩
    cases x <;> simp [binaryValue] at hv <;> omega
lemma divisionWords_invariant (xs ys zs ws : List Bool) (hr : binaryValue zs<binaryValue ys) :
    binaryValue (divisionWords xs ys zs ws).1+binaryValue ys*binaryValue (divisionWords xs ys zs ws).2=
      streamValue xs (binaryValue zs+binaryValue ys*binaryValue ws) ∧
      binaryValue (divisionWords xs ys zs ws).1<binaryValue ys := by
  induction xs generalizing zs ws with
  | nil => exact ⟨rfl,hr⟩
  | cons x xs ih =>
    have hd := division_step_math x ys zs hr
    have hi := ih (divisionRemainder ys (x::zs)) (divisionDigit ys (x::zs)::ws) hd.1
    simp only [divisionWords]
    refine ⟨?_,hi.2⟩
    rw [hi.1,streamValue]
    congr 1
    simp only [binaryValue]
    have hv := hd.2
    simp only [binaryValue] at hv
    nlinarith

theorem divisionWords_correct (xs ys : List Bool) (hy : 0<binaryValue ys) :
    binaryValue (divisionWords xs ys [] []).1=binaryValue xs.reverse%binaryValue ys ∧
      binaryValue (divisionWords xs ys [] []).2=binaryValue xs.reverse/binaryValue ys := by
  have h := divisionWords_invariant xs ys [] [] (by simpa [binaryValue] using hy)
  simp only [binaryValue,Nat.mul_zero,Nat.add_zero,streamValue_eq] at h
  constructor
  · rw [←h.1,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt h.2]
  · rw [←h.1,Nat.add_mul_div_left _ _ hy,Nat.div_eq_of_lt h.2,Nat.zero_add]

lemma subDigits_length (c : Bool) (xs ys : List Bool) :
    (subDigits c xs ys).length=max xs.length ys.length := by
  induction xs generalizing c ys with
  | nil =>
    induction ys generalizing c with
    | nil => simp [subDigits]
    | cons y ys ih => simp [subDigits,ih]
  | cons x xs ih =>
    cases ys with
    | nil => simp [subDigits,ih]
    | cons y ys => simp [subDigits,ih,max_add_add_right]
lemma divisionRemainder_length (ys zs : List Bool) :
    (divisionRemainder ys zs).length ≤ max zs.length ys.length := by
  unfold divisionRemainder
  split_ifs
  · exact Nat.le_max_left _ _
  · exact (subDigits_length false zs ys).le
lemma divCheckCost_bound (ys zs : List Bool) :
    divCheckCost ys zs≤12*max ys.length zs.length+6 := by
  have hy := Nat.le_max_left ys.length zs.length
  have hz := Nat.le_max_right ys.length zs.length
  unfold divCheckCost
  rw [Nat.max_comm zs.length ys.length]
  omega
lemma divSubtractCost_bound (ys zs : List Bool) :
    divSubtractCost ys zs≤13*max ys.length zs.length+6 := by
  have hy := Nat.le_max_left ys.length zs.length
  have hz := Nat.le_max_right ys.length zs.length
  have h := (subDigits_length_cost false zs ys).2
  unfold divSubtractCost
  rw [subDigits_length,Nat.max_comm zs.length ys.length]
  omega
lemma divisionDigitCost_bound (ys zs : List Bool) :
    divisionDigitCost ys zs≤25*max ys.length zs.length+15 := by
  have hc := divCheckCost_bound ys zs
  have hs := divSubtractCost_bound ys zs
  unfold divisionDigitCost
  split_ifs <;> omega
lemma divisionCost_bound (xs ys zs : List Bool) (K : ℕ) (hy : ys.length≤K) (hz : zs.length≤K) :
    divisionCost xs ys zs≤40*xs.length*(K+xs.length+1)+1 := by
  induction xs generalizing zs K with
  | nil => simp [divisionCost]
  | cons x xs ih =>
    have hl : max ys.length (x::zs).length≤K+1 := by simp only [List.length_cons]; omega
    have hr : (divisionRemainder ys (x::zs)).length≤K+1 := by
      have hh := divisionRemainder_length ys (x::zs)
      rw [Nat.max_comm] at hh
      exact hh.trans hl
    have hc := (divisionDigitCost_bound ys (x::zs)).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 25 hl) 15)
    have ht := ih (divisionRemainder ys (x::zs)) (K+1) (by omega) hr
    simp only [divisionCost,List.length_cons]
    nlinarith

end

variable {k n : ℕ}
lemma bitFrame_length (bs : List Bool) : (bitFrame bs).length=2*bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [bitFrame,ih]; omega
lemma bitFrame_append (xs ys : List Bool) :
    bitFrame (xs++ys)=(xs.flatMap (fun b => [false,b]))++bitFrame ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [bitFrame,ih]
lemma frame_pack_scan (a d : Fin (k+8)) (had : a≠d) (O : IndependenceOracle n)
    (R : Fin (k+8) → List Bool) (xs ts : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution (framePackProgram a d) O (frameConfig (pairRegisters R a d xs ts) 1 q c) bits
      (3*xs.length+1)=frameConfig (pairRegisters R a d []
        ((xs.reverse.flatMap (fun b => [false,b]))++ts)) 5 q (c+3*xs.length+1) := by
  induction xs generalizing ts c bits with
  | nil => simp [execution,machineStep,framePackProgram,frameConfig,pairRegisters_a _ _ _ had]
  | cons x xs ih =>
    have ht : execution (framePackProgram a d) O (frameConfig (pairRegisters R a d (x::xs) ts) 1 q c) bits 3=
        frameConfig (pairRegisters R a d xs (false::x::ts)) 1 q (c+3) := by
      cases x <;> simp [execution,machineStep,framePackProgram,frameConfig,
        pairRegisters_a _ _ _ had,pairRegisters_b,pairRegisters_update_a _ _ _ had,pairRegisters_update_b]
    rw [List.length_cons,show 3*(xs.length+1)+1=3+(3*xs.length+1) by omega,execution_add,ht,ih]
    simp only [List.reverse_cons,List.flatMap_append,List.flatMap_singleton,List.append_assoc,List.cons_append,List.nil_append]
    congr 1 ; omega

theorem frame_pack_block (a d : Fin (k+8)) (had : a≠d) (O : IndependenceOracle n)
    (R : Fin (k+8) → List Bool) (xs ts : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution (framePackProgram a d) O (frameConfig (pairRegisters R a d xs ts) 0 q c) bits
      (3*xs.length+2)=frameConfig (pairRegisters R a d [] (bitFrame xs.reverse++ts)) 5 q (c+3*xs.length+2) := by
  have ht : execution (framePackProgram a d) O (frameConfig (pairRegisters R a d xs ts) 0 q c) bits 1=
      frameConfig (pairRegisters R a d xs (true::ts)) 1 q (c+1) := by
    simp [execution,machineStep,framePackProgram,frameConfig,pairRegisters_b,pairRegisters_update_b]
  rw [show 3*xs.length+2=1+(3*xs.length+1) by omega,execution_add,ht,frame_pack_scan a d had]
  have hf : bitFrame xs.reverse=(xs.reverse.flatMap (fun b => [false,b]))++[true] := by
    simpa [bitFrame] using bitFrame_append xs.reverse []
  simp only [hf,List.append_assoc,List.singleton_append]
  congr 1 ; omega

theorem frame_unpack_block (a d : Fin (k+8)) (had : a≠d) (O : IndependenceOracle n)
    (R : Fin (k+8) → List Bool) (xs ts zs : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution (frameUnpackProgram a d) O
      (frameConfig (pairRegisters R a d (bitFrame xs++ts) zs) 0 q c) bits (3*xs.length+1)=
      frameConfig (pairRegisters R a d ts (xs.reverse++zs)) 4 q (c+3*xs.length+1) := by
  induction xs generalizing zs c bits with
  | nil => simp [bitFrame,execution,machineStep,frameUnpackProgram,frameConfig,
      pairRegisters_a _ _ _ had,pairRegisters_update_a _ _ _ had]
  | cons x xs ih =>
    have ht : execution (frameUnpackProgram a d) O
        (frameConfig (pairRegisters R a d (bitFrame (x::xs)++ts) zs) 0 q c) bits 3=
        frameConfig (pairRegisters R a d (bitFrame xs++ts) (x::zs)) 0 q (c+3) := by
      cases x <;> simp [bitFrame,execution,machineStep,frameUnpackProgram,frameConfig,
        pairRegisters_a _ _ _ had,pairRegisters_b,pairRegisters_update_a _ _ _ had,pairRegisters_update_b]
    rw [List.length_cons,show 3*(xs.length+1)+1=3+(3*xs.length+1) by omega,execution_add,ht,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
    congr 1 ; omega

end

namespace MachineCode
lemma runs_skip {k n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool) (R : Registers k) :
    Runs (skip k) O bits R R 0 0 0 := by
  intro q w
  rfl

lemma runs_seq {k n : ℕ} {p q : Block k} (O : IndependenceOracle n) (bits : ℕ → Bool)
    {R S T : Registers k} {u v a b c d : ℕ}
    (hp : Runs p O bits R S u a b)
    (hq : Runs q O (fun i => bits (u+i)) S T v c d) :
    Runs (seq p q) O bits R T (u+v) (a+c) (b+d) := by
  intro q₀ w₀
  have ep := hp q₀ w₀
  have en : (execution p.code O (state R 0 q₀ w₀) bits u).output=none := by rw [ep]; rfl
  have ec : (execution p.code O (state R 0 q₀ w₀) bits u).control=lastLabel p.size := by rw [ep]; rfl
  have h := concat_run p.code q.code p.exit_halt O (state R 0 q₀ w₀) bits u v en ec
  rw [ep] at h
  have eh := hq (q₀+a) (w₀+b)
  change execution q.code O (restartControl (state S (lastLabel p.size) (q₀+a) (w₀+b)) 0)
    (fun i => bits (u+i)) v = _ at eh
  rw [eh] at h
  change execution (concatProgram p.code q.code) O (state R 0 q₀ w₀) bits (u+v) =
    state T (lastLabel (p.size+q.size)) (q₀+(a+c)) (w₀+(b+d))
  simpa [state,relabelConfig,firstLabel,secondLabel,lastLabel,Nat.add_assoc] using h

lemma runs_push {k n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool)
    (R : Registers k) (a : Fin (k+8)) (b : Bool) :
    Runs (push a b) O bits R (Function.update R a (b::R a)) 1 0 1 := by
  intro q w
  rfl

lemma test_step {k s n : ℕ} (test : Test k) (O : IndependenceOracle n) (bit : Bool)
    (P : Program k s) (pc no yes : Fin (s+1)) (hP : P pc=test.instruction no yes)
    (R R' : Registers k) (b : Bool) (h : test.result O bit R=some (b,R')) (q w : ℕ) :
    machineStep P O bit (state R pc q w)=
      state R' (if b then yes else no) (q+test.queries) (w+test.work n R) := by
  cases test with
  | pop a e z o =>
    cases ha : R a with
    | nil =>
      simp only [Test.result,ha,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      simp [machineStep,state,hP,Test.instruction,ha,Test.queries,Test.work]
    | cons x xs =>
      simp only [Test.result,ha,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      cases x <;> simp [machineStep,state,hP,Test.instruction,ha,Test.queries,Test.work]
  | query which a =>
    simp only [Test.result] at h
    split_ifs at h with hn
    · simp only [Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      simp [machineStep,state,hP,Test.instruction,hn,Test.queries,Test.work,Nat.add_assoc]
  | coin =>
    simp only [Test.result,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    simp [machineStep,state,hP,Test.instruction,Test.queries,Test.work]

lemma noLabel_exit (s t : ℕ) : noLabel s t (lastLabel s)=lastLabel (s+t+1) := by
  simp [noLabel,lastLabel]
lemma yesLabel_exit (s t : ℕ) : yesLabel s t (lastLabel t)=lastLabel (s+t+1) := by
  simp [yesLabel,lastLabel]

lemma fork_head {k : ℕ} (test : Test k) (p q : Block k) :
    (fork test p q).code 0=test.instruction (noLabel p.size q.size 0) (yesLabel p.size q.size 0) := by
  simp [fork]
lemma fork_no {k : ℕ} (test : Test k) (p q : Block k) (i : Fin (p.size+1)) (hi : i≠lastLabel p.size) :
    (fork test p q).code (noLabel p.size q.size i)=(p.code i).relabel (noLabel p.size q.size) := by
  have hv : i.val≠p.size := by intro h; exact hi (Fin.ext h)
  have hv' : i.val+1≤p.size := by omega
  simp [fork,noLabel,hv,hv']
lemma fork_yes {k : ℕ} (test : Test k) (p q : Block k) (i : Fin (q.size+1)) (hi : i≠lastLabel q.size) :
    (fork test p q).code (yesLabel p.size q.size i)=(q.code i).relabel (yesLabel p.size q.size) := by
  have hv : i.val≠q.size := by intro h; exact hi (Fin.ext h)
  have hv' : p.size+i.val+1≤p.size+q.size := by omega
  simp [fork,yesLabel,hv,show ¬p.size+i.val+1≤p.size by omega,hv',show p.size+i.val+1-p.size-1=i.val by omega]

lemma fork_run_no {k n : ℕ} (test : Test k) (p q : Block k) (O : IndependenceOracle n)
    (bits : ℕ → Bool) {R S T : Registers k} {t a b : ℕ}
    (ht : test.result O (bits 0) R=some (false,S))
    (hp : Runs p O (fun i => bits (1+i)) S T t a b) :
    Runs (fork test p q) O bits R T (1+t) (test.queries+a) (test.work n R+b) := by
  intro q₀ w₀
  have first := test_step test O (bits 0) (fork test p q).code 0 _ _ (fork_head test p q) R S false ht q₀ w₀
  have er := hp (q₀+test.queries) (w₀+test.work n R)
  have en : (execution p.code O (state S 0 (q₀+test.queries) (w₀+test.work n R))
      (fun i => bits (1+i)) t).output=none := by rw [er]; rfl
  have rel := execution_relabel_before_halt p.code (fork test p q).code (noLabel p.size q.size)
    (lastLabel p.size) p.exit_halt (fork_no test p q) O _ (fun i => bits (1+i)) t en
  rw [er] at rel
  rw [execution_add]
  change execution (fork test p q).code O
    (machineStep (fork test p q).code O (bits 0) (state R 0 q₀ w₀)) (fun i => bits (1+i)) t = _
  rw [first]
  change execution (fork test p q).code O
    (relabelConfig (noLabel p.size q.size) (state S 0 (q₀+test.queries) (w₀+test.work n R)))
    (fun i => bits (1+i)) t = _
  rw [rel]
  simp only [state,relabelConfig,noLabel_exit,Nat.add_assoc]
  rfl
lemma fork_run_yes {k n : ℕ} (test : Test k) (p q : Block k) (O : IndependenceOracle n)
    (bits : ℕ → Bool) {R S T : Registers k} {t a b : ℕ}
    (ht : test.result O (bits 0) R=some (true,S))
    (hq : Runs q O (fun i => bits (1+i)) S T t a b) :
    Runs (fork test p q) O bits R T (1+t) (test.queries+a) (test.work n R+b) := by
  intro q₀ w₀
  have first := test_step test O (bits 0) (fork test p q).code 0 _ _ (fork_head test p q) R S true ht q₀ w₀
  have er := hq (q₀+test.queries) (w₀+test.work n R)
  have en : (execution q.code O (state S 0 (q₀+test.queries) (w₀+test.work n R))
      (fun i => bits (1+i)) t).output=none := by rw [er]; rfl
  have rel := execution_relabel_before_halt q.code (fork test p q).code (yesLabel p.size q.size)
    (lastLabel q.size) q.exit_halt (fork_yes test p q) O _ (fun i => bits (1+i)) t en
  rw [er] at rel
  rw [execution_add]
  change execution (fork test p q).code O
    (machineStep (fork test p q).code O (bits 0) (state R 0 q₀ w₀)) (fun i => bits (1+i)) t = _
  rw [first]
  change execution (fork test p q).code O
    (relabelConfig (yesLabel p.size q.size) (state S 0 (q₀+test.queries) (w₀+test.work n R)))
    (fun i => bits (1+i)) t = _
  rw [rel]
  simp only [state,relabelConfig,yesLabel_exit,Nat.add_assoc]
  rfl

end MachineCode

section MachineLoops
variable {k s n : ℕ}
lemma repeatProgram_body (P : Program k s) (a : Fin (k+8)) (i : Fin (s+1))
    (hi : i≠lastLabel s) : repeatProgram P a (loopLabel s i)=(P i).relabel (loopLabel s) := by
  have hiv : i.val≠s := by intro h; apply hi; exact Fin.ext h
  simp [repeatProgram,loopLabel,hiv,show i.val+1≤ s by omega]
lemma loopLabel_last (s : ℕ) : loopLabel s (lastLabel s)=0 := by simp [loopLabel,lastLabel]
lemma repeatProgram_pop (P : Program k s) (a : Fin (k+8)) (O : IndependenceOracle n)
    (R : Fin (k+8) → List Bool) (x : Bool) (xs : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution (repeatProgram P a) O (loopConfig (Function.update R a (x::xs)) 0 q c) bits 1=
      relabelConfig (loopLabel s) (loopConfig (Function.update R a xs) 0 q (c+1)) := by
  cases x <;> simp [execution,machineStep,repeatProgram,loopConfig,relabelConfig]
lemma repeatProgram_empty (P : Program k s) (a : Fin (k+8)) (O : IndependenceOracle n)
    (R : Fin (k+8) → List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution (repeatProgram P a) O (loopConfig (Function.update R a []) 0 q c) bits 1=
      loopConfig (Function.update R a []) (lastLabel (s+1)) q (c+1) := by
  simp [execution,machineStep,repeatProgram,loopConfig]
end MachineLoops

section MachineMove
variable {k n : ℕ}
theorem reverse_block (a d : Fin (k+8)) (had : a≠d) (O : IndependenceOracle n)
    (R : Fin (k+8) → List Bool) (xs ys : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution (reverseProgram a d) O (reverseConfig (pairRegisters R a d xs ys) 0 q c) bits (2*xs.length+1)=
      reverseConfig (pairRegisters R a d [] (xs.reverse++ys)) 3 q (c+2*xs.length+1) := by
  induction xs generalizing ys c bits with
  | nil => simp [execution,machineStep,reverseProgram,reverseConfig,pairRegisters_a _ _ _ had]
  | cons x xs ih =>
    have ht : execution (reverseProgram a d) O (reverseConfig (pairRegisters R a d (x::xs) ys) 0 q c) bits 2=
        reverseConfig (pairRegisters R a d xs (x::ys)) 0 q (c+2) := by
      cases x <;> simp [execution,machineStep,reverseProgram,reverseConfig,pairRegisters_a _ _ _ had,pairRegisters_b,
        pairRegisters_update_a _ _ _ had,pairRegisters_update_b]
    rw [List.length_cons,show 2*(xs.length+1)+1=2+(2*xs.length+1) by omega,execution_add,ht,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
    congr 1; omega
theorem clear_block (a : Fin (k+8)) (O : IndependenceOracle n)
    (R : Fin (k+8) → List Bool) (xs : List Bool) (q c : ℕ) (bits : ℕ → Bool) :
    execution (clearProgram a) O (clearConfig (Function.update R a xs) 0 q c) bits (xs.length+1)=
      clearConfig (Function.update R a []) 1 q (c+xs.length+1) := by
  induction xs generalizing c bits with
  | nil => simp [execution,machineStep,clearProgram,clearConfig]
  | cons x xs ih =>
    have ht : execution (clearProgram a) O (clearConfig (Function.update R a (x::xs)) 0 q c) bits 1=
        clearConfig (Function.update R a xs) 0 q (c+1) := by
      cases x <;> simp [execution,machineStep,clearProgram,clearConfig]
    rw [List.length_cons,show xs.length+1+1=1+(xs.length+1) by omega,execution_add,ht,ih]
    congr 1; omega
lemma triple_pair_ab (R : Fin (k+8) → List Bool) (a b d : Fin (k+8))
    (hab : a≠b) (had : a≠d) (hbd : b≠d) (xs ys zs us vs : List Bool) :
    pairRegisters (tripleRegisters R a b d xs ys zs) a b us vs=tripleRegisters R a b d us vs zs := by
  simp only [pairRegisters,tripleRegisters_update_a _ _ _ _ hab had,tripleRegisters_update_b _ _ _ _ hbd]
lemma triple_pair_bd (R : Fin (k+8) → List Bool) (a b d : Fin (k+8))
    (hbd : b≠d) (xs ys zs us vs : List Bool) :
    pairRegisters (tripleRegisters R a b d xs ys zs) b d us vs=tripleRegisters R a b d xs us vs := by
  simp only [pairRegisters,tripleRegisters_update_b _ _ _ _ hbd,tripleRegisters_update_d]
theorem move_block (a b d : Fin (k+8)) (hab : a≠b) (had : a≠d) (hbd : b≠d)
    (O : IndependenceOracle n) (R : Fin (k+8) → List Bool) (xs ys : List Bool)
    (q c : ℕ) (bits : ℕ → Bool) :
    execution (moveProgram a b d) O (moveConfig (tripleRegisters R a b d xs [] ys) 0 q c) bits (4*xs.length+2)=
      moveConfig (tripleRegisters R a b d [] [] (xs++ys)) 6 q (c+4*xs.length+2) := by
  have h1 := reverse_block a b hab O (tripleRegisters R a b d xs [] ys) xs [] q c bits
  simp only [triple_pair_ab _ _ _ _ hab had hbd,List.append_nil] at h1
  have h2 := reverse_block b d hbd O (tripleRegisters R a b d [] xs.reverse ys) xs.reverse ys q
    (c+2*xs.length+1) (fun i => bits (2*xs.length+1+i))
  simp only [triple_pair_bd _ _ _ _ hbd,List.reverse_reverse,List.length_reverse] at h2
  have h := concat_run (reverseProgram a b) (reverseProgram b d) (by rfl) O
    (reverseConfig (tripleRegisters R a b d xs [] ys) 0 q c) bits (2*xs.length+1) (2*xs.length+1)
    (by rw [h1]; rfl) (by rw [h1]; rfl)
  rw [h1] at h
  change execution (moveProgram a b d) O (moveConfig (tripleRegisters R a b d xs [] ys) 0 q c) bits
    ((2*xs.length+1)+(2*xs.length+1))=relabelConfig (secondLabel 3 3)
      (execution (reverseProgram b d) O (reverseConfig (tripleRegisters R a b d [] xs.reverse ys) 0 q (c+2*xs.length+1))
        (fun i => bits (2*xs.length+1+i)) (2*xs.length+1)) at h
  rw [h2] at h
  convert h using 1 <;> simp only [relabelConfig,reverseConfig,moveConfig,secondLabel,
    show 2*xs.length+1+(2*xs.length+1)=4*xs.length+2 by omega,
    show c+2*xs.length+1+2*xs.length+1=c+4*xs.length+2 by omega]
  rfl
end MachineMove

namespace MachineCode

lemma runs_reverse {k n : ℕ} (a d : Fin (k+8)) (had : a≠d) (O : IndependenceOracle n)
    (R : Registers k) (xs ys : List Bool) (bits : ℕ → Bool) :
    Runs (reverse a d) O bits (pairRegisters R a d xs ys)
      (pairRegisters R a d [] (xs.reverse++ys)) (2*xs.length+1) 0 (2*xs.length+1) := by
  intro q w
  convert reverse_block a d had O R xs ys q w bits using 1 <;> simp [reverse,state,reverseConfig,lastLabel,Nat.add_assoc]
  rfl
lemma runs_clear {k n : ℕ} (a : Fin (k+8)) (O : IndependenceOracle n)
    (R : Registers k) (xs : List Bool) (bits : ℕ → Bool) :
    Runs (clear a) O bits (Function.update R a xs)
      (Function.update R a []) (xs.length+1) 0 (xs.length+1) := by
  intro q w
  convert clear_block a O R xs q w bits using 1 <;> simp [clear,state,clearConfig,lastLabel,Nat.add_assoc]
  rfl
lemma runs_move {k n : ℕ} (a b d : Fin (k+8)) (hab : a≠b) (had : a≠d) (hbd : b≠d)
    (O : IndependenceOracle n) (R : Registers k) (xs ys : List Bool) (bits : ℕ → Bool) :
    Runs (move a b d) O bits (tripleRegisters R a b d xs [] ys)
      (tripleRegisters R a b d [] [] (xs++ys)) (4*xs.length+2) 0 (4*xs.length+2) := by
  intro q w
  convert move_block a b d hab had hbd O R xs ys q w bits using 1 <;> simp [move,state,moveConfig,lastLabel,Nat.add_assoc]
  rfl
lemma runs_pack {k n : ℕ} (a d : Fin (k+8)) (had : a≠d) (O : IndependenceOracle n)
    (R : Registers k) (xs ts : List Bool) (bits : ℕ → Bool) :
    Runs (pack a d) O bits (pairRegisters R a d xs ts)
      (pairRegisters R a d [] (bitFrame xs.reverse++ts)) (3*xs.length+2) 0 (3*xs.length+2) := by
  intro q w
  convert frame_pack_block a d had O R xs ts q w bits using 1 <;> simp [pack,state,frameConfig,lastLabel,Nat.add_assoc]
  rfl
lemma runs_unpack {k n : ℕ} (a d : Fin (k+8)) (had : a≠d) (O : IndependenceOracle n)
    (R : Registers k) (xs ts zs : List Bool) (bits : ℕ → Bool) :
    Runs (unpack a d) O bits (pairRegisters R a d (bitFrame xs++ts) zs)
      (pairRegisters R a d ts (xs.reverse++zs)) (3*xs.length+1) 0 (3*xs.length+1) := by
  intro q w
  let f : Fin 6 → Fin 5 := fun i => ⟨min i.val 4,by omega⟩
  have h := frame_unpack_block a d had O R xs ts zs q w bits
  have hn : (execution (frameUnpackProgram a d) O
      (frameConfig (pairRegisters R a d (bitFrame xs++ts) zs) 0 q w) bits (3*xs.length+1)).output=none := by
    rw [h]; rfl
  have rel := execution_relabel_before_halt (frameUnpackProgram a d) (unpack a d).code f 4 rfl
    (by intro i hi; fin_cases i <;> rfl) O _ bits (3*xs.length+1) hn
  rw [h] at rel
  convert rel using 1 <;> simp [state,relabelConfig,frameConfig,f,unpack,lastLabel,Nat.add_assoc]
  rfl
lemma runs_unpack_packed {k n : ℕ} (a d : Fin (k+8)) (had : a≠d) (O : IndependenceOracle n)
    (R : Registers k) (xs ts : List Bool) (bits : ℕ → Bool) :
    Runs (unpack a d) O bits (pairRegisters R a d (bitFrame xs.reverse++ts) [])
      (pairRegisters R a d ts xs) (3*xs.length+1) 0 (3*xs.length+1) := by
  simpa only [List.length_reverse,List.reverse_reverse,List.append_nil] using
    runs_unpack a d had O R xs.reverse ts [] bits

@[simp] lemma regs_two (x y z s : Word) : regs x y z s 2=z := by simp [regs]
@[simp] lemma update_regs_zero (x y z s u : Word) : Function.update (regs x y z s) 0 u=regs u y z s := by
  funext i; fin_cases i <;> simp [regs]
@[simp] lemma update_regs_one (x y z s u : Word) : Function.update (regs x y z s) 1 u=regs x u z s := by
  funext i; fin_cases i <;> simp [regs]
@[simp] lemma update_regs_two (x y z s u : Word) : Function.update (regs x y z s) 2 u=regs x y u s := by
  funext i; fin_cases i <;> simp [regs]
@[simp] lemma update_regs_eight (x y z s u : Word) : Function.update (regs x y z s) 8 u=regs x y z u := by
  funext i; fin_cases i <;> simp [regs]

@[simp] lemma pair_length (x y : Word) : (pair x y).length=2*x.length+1+y.length := by
  simp [pair,bitFrame_length]

lemma computes_skip {n : ℕ} (O : IndependenceOracle n) (x : Word) :
    Computes (skip 1) O x x 0 0 0 := fun s bits => runs_skip O bits (regs x [] [] s)
lemma computes_seq {n : ℕ} {p q : Block 1} {O : IndependenceOracle n} {x y z : Word}
    {t₁ q₁ w₁ t₂ q₂ w₂ : ℕ} (hp : Computes p O x y t₁ q₁ w₁) (hq : Computes q O y z t₂ q₂ w₂) :
    Computes (seq p q) O x z (t₁+t₂) (q₁+q₂) (w₁+w₂) := by
  intro s bits
  exact runs_seq O bits (hp s bits) (hq s (fun i => bits (t₁+i)))
lemma bounded_seq {n : ℕ} {p q : Block 1} {O : IndependenceOracle n} {x y z : Word}
    {B C : ℕ} (hp : Bounded p O x y B) (hq : Bounded q O y z C) :
    Bounded (seq p q) O x z (B+C) := by
  obtain ⟨t₁,q₁,w₁,ht₁,hq₁,hw₁,hp⟩ := hp
  obtain ⟨t₂,q₂,w₂,ht₂,hq₂,hw₂,hq⟩ := hq
  exact ⟨_,_,_,Nat.add_le_add ht₁ ht₂,Nat.add_le_add hq₁ hq₂,Nat.add_le_add hw₁ hw₂,computes_seq hp hq⟩
lemma bounded_mono {n : ℕ} {p : Block 1} {O : IndependenceOracle n} {x y : Word}
    {B C : ℕ} (h : Bounded p O x y B) (hBC : B≤C) : Bounded p O x y C := by
  obtain ⟨t,q,w,ht,hq,hw,hp⟩ := h
  exact ⟨t,q,w,ht.trans hBC,hq.trans hBC,hw.trans hBC,hp⟩

lemma runs_copy {k n : ℕ} (a b d : Fin (k+8)) (hab : a≠b) (had : a≠d) (hbd : b≠d)
    (O : IndependenceOracle n) (R : Registers k) (xs ys : Word) (bits : ℕ → Bool) :
    Runs (copy a b d) O bits (tripleRegisters R a b d xs [] ys)
      (tripleRegisters R a b d xs [] (xs++ys)) (5*xs.length+2) 0 (5*xs.length+2) := by
  intro q w
  convert copy_block a b d hab had hbd O R xs ys q w bits using 1 <;>
    simp [copy,state,copyConfig,lastLabel,Nat.add_assoc]
  rfl

lemma computes_duplicate {n : ℕ} (O : IndependenceOracle n) (x : Word) :
    Computes duplicate O x (pair x x) (8*x.length+4) 0 (8*x.length+4) := by
  intro s bits
  have hc := runs_copy (k:=1) 0 2 1 (by decide) (by decide) (by decide) O (regs x [] [] s) x [] bits
  simp only [tripleRegisters,pairRegisters,update_regs_zero,update_regs_two,update_regs_one,List.append_nil] at hc
  have hp := runs_pack (k:=1) 1 0 (by decide) O (regs x x [] s) x x (fun i => bits (5*x.length+2+i))
  simp only [pairRegisters,update_regs_one,update_regs_zero] at hp
  simpa only [duplicate,pair,show 5*x.length+2+(3*x.length+2)=8*x.length+4 by omega,Nat.zero_add] using
    runs_seq O bits hc hp

lemma split_pair {n : ℕ} (O : IndependenceOracle n) (x y z s : Word) (bits : ℕ → Bool) :
    Runs (unpack 0 1) O bits (regs (pair x y) z [] s) (regs y (x++z) [] s)
      (3*x.length+1) 0 (3*x.length+1) := by
  have h := runs_unpack (k:=1) 0 1 (by decide) O (regs [] [] [] s) x.reverse y z bits
  simpa only [pair,pairRegisters,update_regs_zero,update_regs_one,List.length_reverse,List.reverse_reverse] using h
lemma move_one_zero {n : ℕ} (O : IndependenceOracle n) (x y s : Word) (bits : ℕ → Bool) :
    Runs (move 1 2 0) O bits (regs y x [] s) (regs (x++y) [] [] s)
      (4*x.length+2) 0 (4*x.length+2) := by
  simpa only [tripleRegisters,pairRegisters,update_regs_zero,update_regs_one,update_regs_two] using
    runs_move (k:=1) 1 2 0 (by decide) (by decide) (by decide) O (regs [] [] [] s) x y bits

lemma computes_first {n : ℕ} (O : IndependenceOracle n) (x y : Word) :
    Computes first O (pair x y) x (7*x.length+y.length+4) 0 (7*x.length+y.length+4) := by
  intro s bits
  have hu := split_pair O x y [] s bits
  have hc := runs_clear (k:=1) 0 O (regs y x [] s) y (fun i => bits (3*x.length+1+i))
  simp only [update_regs_zero] at hc
  have hm := move_one_zero O x [] s (fun i => bits (3*x.length+1+(y.length+1+i)))
  simp only [List.append_nil] at hu hm
  have ht := runs_seq O bits hu (runs_seq O (fun i => bits (3*x.length+1+i)) hc hm)
  simpa only [first,show 3*x.length+1+(y.length+1+(4*x.length+2))=7*x.length+y.length+4 by omega,Nat.zero_add] using ht
lemma computes_second {n : ℕ} (O : IndependenceOracle n) (x y : Word) :
    Computes second O (pair x y) y (4*x.length+2) 0 (4*x.length+2) := by
  intro s bits
  have hu := split_pair O x y [] s bits
  simp only [List.append_nil] at hu
  have hc := runs_clear (k:=1) 1 O (regs y x [] s) x (fun i => bits (3*x.length+1+i))
  simp only [update_regs_one] at hc
  simpa only [second,show 3*x.length+1+(x.length+1)=4*x.length+2 by omega,Nat.zero_add] using runs_seq O bits hu hc

lemma save_zero {n : ℕ} (O : IndependenceOracle n) (x y s : Word) (bits : ℕ → Bool) :
    Runs (pack 0 8) O bits (regs x y [] s) (regs [] y [] (pair x s))
      (3*x.length+2) 0 (3*x.length+2) := by
  simpa only [pair,pairRegisters,update_regs_zero,update_regs_eight] using
    runs_pack (k:=1) 0 8 (by decide) O (regs [] y [] []) x s bits
lemma restore_one {n : ℕ} (O : IndependenceOracle n) (x y s : Word) (bits : ℕ → Bool) :
    Runs (unpack 8 1) O bits (regs x [] [] (pair y s)) (regs x y [] s)
      (3*y.length+1) 0 (3*y.length+1) := by
  simpa only [pair,pairRegisters,update_regs_one,update_regs_eight] using
    runs_unpack_packed (k:=1) 8 1 (by decide) O (regs x [] [] []) y s bits
lemma pack_zero_one {n : ℕ} (O : IndependenceOracle n) (x y s : Word) (bits : ℕ → Bool) :
    Runs (pack 0 1) O bits (regs x y [] s) (regs [] (pair x y) [] s)
      (3*x.length+2) 0 (3*x.length+2) := by
  simpa only [pair,pairRegisters,update_regs_zero,update_regs_one] using
    runs_pack (k:=1) 0 1 (by decide) O (regs [] [] [] s) x y bits

lemma computes_swap {n : ℕ} (O : IndependenceOracle n) (x y : Word) :
    Computes swap O (pair x y) (pair y x) (7*x.length+11*y.length+9) 0 (7*x.length+11*y.length+9) := by
  intro s bits
  have hu := split_pair O x y [] s bits
  simp only [List.append_nil] at hu
  have hp := pack_zero_one O y x s (fun i => bits (3*x.length+1+i))
  have hm := move_one_zero O (pair y x) [] s (fun i => bits (3*x.length+1+(3*y.length+2+i)))
  simp only [List.append_nil] at hm
  have ht := runs_seq O bits hu (runs_seq O (fun i => bits (3*x.length+1+i)) hp hm)
  have he : 3*x.length+1+(3*y.length+2+(4*(pair y x).length+2))=7*x.length+11*y.length+9 := by
    rw [pair_length]; omega
  simpa only [swap,he,Nat.zero_add] using ht

lemma computes_left {n : ℕ} {O : IndependenceOracle n} {p : Block 1} {x u : Word}
    {t q w : ℕ} (h : Computes p O x u t q w) (y : Word) :
    Computes (left p) O (pair x y) (pair u y)
      (7*x.length+10*y.length+11*u.length+14+t) q (7*x.length+10*y.length+11*u.length+14+w) := by
  intro s bits
  have hu := split_pair O x y [] s bits
  simp only [List.append_nil] at hu
  have hs := save_zero O y x s (fun i => bits (3*x.length+1+i))
  have hm := move_one_zero O x [] (pair y s) (fun i => bits (3*x.length+1+(3*y.length+2+i)))
  simp only [List.append_nil] at hm
  have hp := h (pair y s) (fun i => bits (3*x.length+1+(3*y.length+2+(4*x.length+2+i))))
  have hr := restore_one O u y s (fun i => bits (3*x.length+1+(3*y.length+2+(4*x.length+2+(t+i)))))
  have hf := pack_zero_one O u y s (fun i => bits (3*x.length+1+(3*y.length+2+(4*x.length+2+(t+(3*y.length+1+i))))))
  have he := move_one_zero O (pair u y) [] s
    (fun i => bits (3*x.length+1+(3*y.length+2+(4*x.length+2+(t+(3*y.length+1+(3*u.length+2+i)))))))
  simp only [List.append_nil] at he
  have ht := runs_seq O bits hu (runs_seq O _ hs (runs_seq O _ hm
    (runs_seq O _ hp (runs_seq O _ hr (runs_seq O _ hf he)))))
  have cost (v : ℕ) : 3*x.length+1+(3*y.length+2+(4*x.length+2+(v+(3*y.length+1+(3*u.length+2+(4*(pair u y).length+2))))))=
      7*x.length+10*y.length+11*u.length+14+v := by rw [pair_length]; omega
  simpa only [left,cost,Nat.zero_add,Nat.add_zero] using ht

lemma computes_right {n : ℕ} {O : IndependenceOracle n} {p : Block 1} {x u : Word}
    {t q w : ℕ} (h : Computes p O x u t q w) (y : Word) :
    Computes (right p) O (pair y x) (pair y u)
      (28*y.length+18*x.length+18*u.length+32+t) q (28*y.length+18*x.length+18*u.length+32+w) := by
  have ht := computes_seq (computes_swap O y x) (computes_seq (computes_left h y) (computes_swap O u y))
  convert ht using 1 <;> first | rfl | omega

lemma strip_length (x : Word) : (stripZeros x).length≤x.length := by
  induction x with
  | nil => rfl
  | cons b xs ih => cases b <;> simp only [stripZeros,List.length_cons] <;> omega
lemma strip_cost_le (x : Word) : stripCost x≤x.length+2 := by
  induction x with
  | nil => decide
  | cons b xs ih => cases b <;> simp only [stripCost,List.length_cons] <;> omega
lemma strip_append (x y : Word) : stripZeros (x++y)=if stripZeros x=[] then stripZeros y else stripZeros x++y := by
  induction x with
  | nil => simp [stripZeros]
  | cons b xs ih =>
    cases b <;> simp [stripZeros,ih]
    rfl

lemma normal_length (x : Word) : (normalWord x).length≤x.length := by
  simpa only [normalWord,List.length_reverse] using strip_length x.reverse
lemma normalWord_cons (b : Bool) (xs : Word) :
    normalWord (b::xs)=if normalWord xs=[] then (if b then [true] else []) else b::normalWord xs := by
  simp only [normalWord,List.reverse_cons,strip_append]
  by_cases h : stripZeros xs.reverse=[]
  · simp [h]; cases b <;> rfl
  · simp [h,List.reverse_eq_nil_iff]

lemma binaryValue_bits (n : ℕ) : binaryValue n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b <;> simp [binaryValue,ih,Nat.bit]
    omega
lemma normalWord_eq_bits (xs : Word) : normalWord xs=(binaryValue xs).bits := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    rw [normalWord_cons,ih]
    by_cases hz : binaryValue xs=0
    · cases b <;> simp [binaryValue,hz]
    · have hb : (binaryValue xs).bits≠[] := by
        intro h
        have he := binaryValue_bits (binaryValue xs)
        rw [h] at he
        exact hz he.symm
      cases b with
      | false => simp [binaryValue,hb,Nat.bit0_bits _ hz]
      | true =>
        simp only [ite_true,ite_eq_right hb,binaryValue]
        rw [Nat.add_comm 1, Nat.bit1_bits]
@[simp] lemma normalWord_bits (n : ℕ) : normalWord n.bits=n.bits := by
  rw [normalWord_eq_bits,binaryValue_bits]

lemma runs_strip {k n : ℕ} (a : Fin (k+8)) (O : IndependenceOracle n) (R : Registers k)
    (x : Word) (bits : ℕ → Bool) :
    Runs (stripCode a) O bits (Function.update R a x) (Function.update R a (stripZeros x))
      (stripCost x) 0 (stripCost x) := by
  intro q w
  induction x generalizing w bits with
  | nil => simp [stripCode,stripCost,stripZeros,execution,machineStep,state,lastLabel]
  | cons b xs ih =>
    cases b with
    | false =>
      have hf : execution (stripCode a).code O (state (Function.update R a (false::xs)) 0 q w) bits 1=
          state (Function.update R a xs) 0 q (w+1) := by
        simp [stripCode,state,execution,machineStep]
        rfl
      rw [stripCost,execution_add,hf,ih]
      simp [stripZeros,Nat.add_assoc]
    | true => simp [stripCode,stripCost,stripZeros,execution,machineStep,state,lastLabel,Nat.add_assoc]

lemma normalCost_le (x : Word) : normalCost x≤5*x.length+4 := by
  have h₁:=strip_cost_le x.reverse
  have h₂:=strip_length x.reverse
  simp only [List.length_reverse] at h₁ h₂
  unfold normalCost
  omega
lemma computes_normalCode {n : ℕ} (O : IndependenceOracle n) (x : Word) :
    Computes normalCode O x (normalWord x) (normalCost x) 0 (normalCost x) := by
  intro s bits
  have h₁ := runs_reverse (k:=1) 0 1 (by decide) O (regs [] [] [] s) x [] bits
  simp only [pairRegisters,update_regs_zero,update_regs_one,List.append_nil] at h₁
  have h₂ := runs_strip (k:=1) 1 O (regs [] [] [] s) x.reverse (fun i => bits (2*x.length+1+i))
  simp only [update_regs_one] at h₂
  have h₃ := runs_reverse (k:=1) 1 0 (by decide) O (regs [] [] [] s) (stripZeros x.reverse) []
    (fun i => bits (2*x.length+1+(stripCost x.reverse+i)))
  simp only [pairRegisters,update_regs_zero,update_regs_one,List.append_nil] at h₃
  simpa only [normalCode,normalCost,normalWord,Nat.zero_add] using runs_seq O bits h₁ (runs_seq O _ h₂ h₃)
lemma runs_add {n : ℕ} (O : IndependenceOracle n) (x y s : Word) (bits : ℕ → Bool) :
    Runs addBlock O bits (regs x y [] s) (regs (addDigits false x y) [] [] s)
      (addTime x y) 0 (addTime x y) := by
  dsimp only [Runs,addBlock]
  intro q w
  have h := (addition_block (k:=1) 0 1 2 (by decide) (by decide) (by decide) O (regs [] [] [] s) x y q w bits).2.2
  convert h using 1 <;> simp only [addTime,addConfig,state,tripleRegisters,pairRegisters,update_regs_zero,
    update_regs_one,update_regs_two,lastLabel,Nat.add_zero]
  rfl
lemma addTime_le (x y : Word) : addTime x y ≤ 5*(x.length+y.length)+6 := by
  have h := addDigits_length_cost false x y
  unfold addTime
  omega

lemma computes_add {n : ℕ} (O : IndependenceOracle n) (x y : Word) :
    Computes addCode O (pair x y) (binaryValue x+binaryValue y).bits
      (3*x.length+1+addTime y x+normalCost (addDigits false y x)) 0
      (3*x.length+1+addTime y x+normalCost (addDigits false y x)) := by
  have hv : binaryValue (addDigits false y x)=binaryValue x+binaryValue y := by
    simpa [Nat.add_comm] using addDigits_value false y x
  intro s bits
  have hs := split_pair O x y [] s bits
  simp only [List.append_nil] at hs
  have ha := runs_add O y x s (fun i => bits (3*x.length+1+i))
  have hn := computes_normalCode O (addDigits false y x) s (fun i => bits (3*x.length+1+(addTime y x+i)))
  rw [normalWord_eq_bits,hv] at hn
  have ht := runs_seq O bits hs (runs_seq O _ ha hn)
  simpa only [addCode,Nat.zero_add,Nat.add_assoc] using ht
lemma bounded_add {n : ℕ} (O : IndependenceOracle n) (x y : Word) :
    Bounded addCode O (pair x y) (binaryValue x+binaryValue y).bits (20*(x.length+y.length+1)) := by
  have h₁ := addTime_le y x
  have h₂ := normalCost_le (addDigits false y x)
  have h₃ := (addDigits_length_cost false y x).1
  refine ⟨_,0,_,?_,Nat.zero_le _,?_,computes_add O x y⟩ <;> omega

lemma mulRegisters_regs (x y z s : Word) : mulRegisters (regs [] [] [] s) x y z []=regs x y z s := by
  funext i; fin_cases i <;> simp [mulRegisters,regs]
lemma runs_mul {n : ℕ} (O : IndependenceOracle n) (x y s : Word) (bits : ℕ → Bool) :
    Runs mulBlock O bits (regs x y [] s)
      (regs (List.replicate y.length false++x) [] (mulDigits x y []) s)
      (mulCost x y []) 0 (mulCost x y []) := by
  dsimp only [Runs,mulBlock]
  intro q w
  have h := (multiplication_block (k:=1) O (regs [] [] [] s) x y q w bits).2.2
  convert h using 1 <;> simp only [mulConfig,state,mulRegisters_regs,lastLabel,Nat.add_zero]
  rfl
lemma clear_zero {n : ℕ} (O : IndependenceOracle n) (x y z s : Word) (bits : ℕ → Bool) :
    Runs (clear 0) O bits (regs x y z s) (regs [] y z s) (x.length+1) 0 (x.length+1) := by
  simpa only [update_regs_zero] using runs_clear (k:=1) 0 O (regs [] y z s) x bits
lemma move_two_zero {n : ℕ} (O : IndependenceOracle n) (x s : Word) (bits : ℕ → Bool) :
    Runs (move 2 1 0) O bits (regs [] [] x s) (regs x [] [] s) (4*x.length+2) 0 (4*x.length+2) := by
  simpa only [tripleRegisters,pairRegisters,update_regs_zero,update_regs_one,update_regs_two,List.append_nil] using
    runs_move (k:=1) 2 1 0 (by decide) (by decide) (by decide) O (regs [] [] [] s) x [] bits

lemma computes_mul {n : ℕ} (O : IndependenceOracle n) (x y : Word) :
    Computes mulCode O (pair x y) (binaryValue x*binaryValue y).bits (mulTime x y) 0 (mulTime x y) := by
  have hv : binaryValue (mulDigits y x [])=binaryValue x*binaryValue y := by
    simp [mulDigits_value,binaryValue,Nat.mul_comm]
  intro s bits
  have h₁ := split_pair O x y [] s bits
  simp only [List.append_nil] at h₁
  have h₂ := runs_mul O y x s (fun i => bits (3*x.length+1+i))
  have h₃ := clear_zero O (List.replicate x.length false++y) [] (mulDigits y x []) s
    (fun i => bits (3*x.length+1+(mulCost y x []+i)))
  simp only [List.length_append,List.length_replicate] at h₃
  have h₄ := move_two_zero O (mulDigits y x []) s
    (fun i => bits (3*x.length+1+(mulCost y x []+(x.length+y.length+1+i))))
  have h₅ := computes_normalCode O (mulDigits y x []) s
    (fun i => bits (3*x.length+1+(mulCost y x []+(x.length+y.length+1+(4*(mulDigits y x []).length+2+i)))))
  rw [normalWord_eq_bits,hv] at h₅
  have ht := runs_seq O bits h₁ (runs_seq O _ h₂ (runs_seq O _ h₃ (runs_seq O _ h₄ h₅)))
  simpa only [mulCode,mulTime,Nat.zero_add,Nat.add_assoc] using ht
lemma mulTime_le (x y : Word) : mulTime x y ≤ 60*(x.length+y.length+1)^2 := by
  have h₁ := mulCost_bound y x []
  have h₂ := mulDigits_length y x []
  have h₃ := normalCost_le (mulDigits y x [])
  simp only [List.length_nil,Nat.max_zero] at h₁ h₂
  unfold mulTime
  nlinarith [sq_nonneg (x.length:ℤ),sq_nonneg (y.length:ℤ)]
lemma bounded_mul {n : ℕ} (O : IndependenceOracle n) (x y : Word) :
    Bounded mulCode O (pair x y) (binaryValue x*binaryValue y).bits (60*(x.length+y.length+1)^2) :=
  ⟨_,0,_,mulTime_le x y,Nat.zero_le _,mulTime_le x y,computes_mul O x y⟩

lemma computes_parallel {n : ℕ} {O : IndependenceOracle n} {p q : Block 1} {x y u v : Word}
    {t₁ q₁ w₁ t₂ q₂ w₂ : ℕ} (hp : Computes p O x u t₁ q₁ w₁) (hq : Computes q O y v t₂ q₂ w₂) :
    Computes (parallel p q) O (pair x y) (pair u v)
      (7*x.length+28*y.length+39*u.length+18*v.length+46+t₁+t₂) (q₁+q₂)
      (7*x.length+28*y.length+39*u.length+18*v.length+46+w₁+w₂) := by
  have ht := computes_seq (computes_left hp y) (computes_right hq u)
  convert ht using 1 <;> first | rfl | omega
lemma computes_fanout {n : ℕ} {O : IndependenceOracle n} {p q : Block 1} {x u v : Word}
    {t₁ q₁ w₁ t₂ q₂ w₂ : ℕ} (hp : Computes p O x u t₁ q₁ w₁) (hq : Computes q O x v t₂ q₂ w₂) :
    Computes (fanout p q) O x (pair u v)
      (43*x.length+39*u.length+18*v.length+50+t₁+t₂) (q₁+q₂)
      (43*x.length+39*u.length+18*v.length+50+w₁+w₂) := by
  have ht := computes_seq (computes_duplicate O x) (computes_parallel hp hq)
  convert ht using 1 <;> first | rfl | omega

lemma computes_prepend {n : ℕ} (O : IndependenceOracle n) (x y : Word) :
    Computes (prependCode x) O y (x++y) x.length 0 x.length := by
  induction x with
  | nil => exact computes_skip O y
  | cons b xs ih =>
    have hp : Computes (push 0 b) O (xs++y) (b::(xs++y)) 1 0 1 := by
      intro s bits
      simpa only [regs_zero,update_regs_zero] using runs_push O bits (regs (xs++y) [] [] s) 0 b
    have ht := computes_seq ih hp
    simpa only [prependCode,List.cons_append,List.length_cons,Nat.zero_add] using ht

lemma computes_const {n : ℕ} (O : IndependenceOracle n) (x y : Word) :
    Computes (constCode y) O x y (x.length+y.length+1) 0 (x.length+y.length+1) := by
  have hc : Computes (clear 0) O x [] (x.length+1) 0 (x.length+1) :=
    fun s bits => clear_zero O x [] [] s bits
  have ht := computes_seq hc (computes_prepend O y [])
  simpa only [constCode,List.append_nil,Nat.zero_add,show x.length+1+y.length=x.length+y.length+1 by omega] using ht

lemma computes_select {n : ℕ} {O : IndependenceOracle n} (p q : Block 1) (b : Bool) {x y : Word}
    {t a w : ℕ} (h : Computes (if b then q else p) O x y t a w) :
    Computes (selectCode p q) O (pair [b] x) y (5+t) a (5+w) := by
  intro s bits
  have hu := split_pair O [b] x [] s bits
  simp only [List.append_nil,List.length_singleton,show 3*1+1=4 by omega] at hu
  have hf : Runs (fork (.pop 1 false false true) p q) O (fun i => bits (4+i))
      (regs x [b] [] s) (regs y [] [] s) (1+t) a (1+w) := by
    cases b with
    | false =>
      have hp := h s (fun i => bits (4+(1+i)))
      have hh := fork_run_no (.pop 1 false false true) p q O (fun i => bits (4+i))
        (R:=regs x [false] [] s) (by simp [Test.result]) hp
      simpa only [Test.queries,Test.work,Nat.zero_add] using hh
    | true =>
      have hp := h s (fun i => bits (4+(1+i)))
      have hh := fork_run_yes (.pop 1 false false true) p q O (fun i => bits (4+i))
        (R:=regs x [true] [] s) (by simp [Test.result]) hp
      simpa only [Test.queries,Test.work,Nat.zero_add] using hh
  have ht := runs_seq O bits hu hf
  simpa only [selectCode,Nat.zero_add,show 4+(1+t)=5+t by omega,show 4+(1+w)=5+w by omega] using ht

lemma computes_query {n : ℕ} (O : IndependenceOracle n) (which : Bool) (x : Word) (hx : x.length=n) :
    Computes (queryCode which) O x [O which (fun i => x[i.val]?.getD false)] (n+3) 1 (3*n+3) := by
  intro s bits
  have hp (b : Bool) := computes_const O x [b] s (fun i => bits (1+i))
  have hres : (Test.query which 0).result O (bits 0) (regs x [] [] s)=
      some (O which (fun i => x[i.val]?.getD false),regs x [] [] s) := by simp [Test.result,hx]
  cases hb : O which (fun i => x[i.val]?.getD false) with
  | false =>
    rw [hb] at hres
    have ht := fork_run_no (.query which 0) (constCode [false]) (constCode [true]) O bits hres (hp false)
    simp only [Test.queries,Test.work,regs_zero,hx,List.length_singleton] at ht
    convert ht using 1 <;> first | rfl | omega
  | true =>
    rw [hb] at hres
    have ht := fork_run_yes (.query which 0) (constCode [false]) (constCode [true]) O bits hres (hp true)
    simp only [Test.queries,Test.work,regs_zero,hx,List.length_singleton] at ht
    convert ht using 1 <;> first | rfl | omega

@[simp] lemma quadRegs_zero (x y z u s : Word) : quadRegs x y z u s 0=x := by simp [quadRegs]
@[simp] lemma quadRegs_one (x y z u s : Word) : quadRegs x y z u s 1=y := by simp [quadRegs]
@[simp] lemma quadRegs_two (x y z u s : Word) : quadRegs x y z u s 2=z := by simp [quadRegs]
@[simp] lemma quadRegs_nil (x y z s : Word) : quadRegs x y z [] s=regs x y z s := by
  funext i; fin_cases i <;> simp [quadRegs,regs]
@[simp] lemma update_quad_zero (x y z u s v : Word) : Function.update (quadRegs x y z u s) 0 v=quadRegs v y z u s := by
  funext i; fin_cases i <;> simp [quadRegs,regs]
@[simp] lemma update_quad_one (x y z u s v : Word) : Function.update (quadRegs x y z u s) 1 v=quadRegs x v z u s := by
  funext i; fin_cases i <;> simp [quadRegs,regs]
@[simp] lemma update_quad_two (x y z u s v : Word) : Function.update (quadRegs x y z u s) 2 v=quadRegs x y v u s := by
  funext i; fin_cases i <;> simp [quadRegs,regs]
lemma divRegisters_quad (x y z u s : Word) : divRegisters (regs [] [] [] s) x y z u [] []=quadRegs x y z u s := by
  funext i; fin_cases i <;> simp [divRegisters,quadRegs,regs]

lemma runs_div {n : ℕ} (O : IndependenceOracle n) (x y s : Word) (bits : ℕ → Bool) :
    Runs divBlock O bits (regs x y [] s)
      (quadRegs [] y (divisionWords x y [] []).1 (divisionWords x y [] []).2 s)
      (divisionCost x y []) 0 (divisionCost x y []) := by
  dsimp only [Runs,divBlock]
  intro q w
  have h := division_machine_run (k:=1) O (regs [] [] [] s) x y [] [] q w bits
  convert h using 1 <;> simp only [divisionConfig,state,divRegisters_quad,quadRegs_nil,lastLabel,Nat.add_zero]
  rfl

lemma div_prepare {n : ℕ} (O : IndependenceOracle n) (x y s : Word) (bits : ℕ → Bool) :
    Runs (seq (reverse 0 2) (move 2 3 0)) O bits (regs x y [] s) (regs x.reverse y [] s)
      (6*x.length+3) 0 (6*x.length+3) := by
  have hr := runs_reverse (k:=1) 0 2 (by decide) O (regs [] y [] s) x [] bits
  simp only [pairRegisters,update_regs_zero,update_regs_two,List.append_nil] at hr
  have hm := runs_move (k:=1) 2 3 0 (by decide) (by decide) (by decide) O
    (quadRegs [] y [] [] s) x.reverse [] (fun i => bits (2*x.length+1+i))
  simp only [tripleRegisters,pairRegisters,update_quad_zero,update_quad_two,update_quad_three,
    List.append_nil,List.length_reverse] at hm
  simp only [quadRegs_nil] at hm
  have ht := runs_seq O bits hr hm
  convert ht using 1 <;> first | rfl | omega

lemma div_finish {n : ℕ} (O : IndependenceOracle n) (x r q s : Word) (bits : ℕ → Bool) :
    Runs (seq (clear 1) (seq (pack 2 3) (move 3 1 0))) O bits (quadRegs [] x r q s)
      (regs (pair r q) [] [] s) (x.length+11*r.length+4*q.length+9) 0
      (x.length+11*r.length+4*q.length+9) := by
  have h₁ := runs_clear (k:=1) 1 O (quadRegs [] [] r q s) x bits
  simp only [update_quad_one] at h₁
  have h₂ := runs_pack (k:=1) 2 3 (by decide) O (quadRegs [] [] [] [] s) r q
    (fun i => bits (x.length+1+i))
  simp only [pairRegisters,update_quad_two,update_quad_three] at h₂
  change Runs (pack 2 3) O _ (quadRegs [] [] r q s) (quadRegs [] [] [] (pair r q) s) _ _ _ at h₂
  have h₃ := runs_move (k:=1) 3 1 0 (by decide) (by decide) (by decide) O (quadRegs [] [] [] [] s)
    (pair r q) [] (fun i => bits (x.length+1+(3*r.length+2+i)))
  simp only [tripleRegisters,pairRegisters,update_quad_zero,update_quad_one,update_quad_three,
    List.append_nil] at h₃
  simp only [quadRegs_nil] at h₃
  have ht := runs_seq O bits h₁ (runs_seq O _ h₂ h₃)
  convert ht using 1 <;> first | rfl | simp only [pair_length]; omega

lemma computes_rawDiv {n : ℕ} (O : IndependenceOracle n) (x y : Word) :
    Computes rawDivCode O (pair x y) (pair (divResult x y).1 (divResult x y).2)
      (rawDivTime x y) 0 (rawDivTime x y) := by
  intro s bits
  have h₁ := split_pair O x y [] s bits
  simp only [List.append_nil] at h₁
  have h₂ := div_prepare O y x s (fun i => bits (3*x.length+1+i))
  have h₃ := runs_div O y.reverse x s (fun i => bits (3*x.length+1+(6*y.length+3+i)))
  have h₄ := div_finish O x (divResult x y).1 (divResult x y).2 s
    (fun i => bits (3*x.length+1+(6*y.length+3+(divisionCost y.reverse x []+i))))
  have ht := runs_seq O bits h₁ (runs_seq O _ h₂ (runs_seq O _ h₃ h₄))
  convert ht using 1 <;> first | rfl | unfold rawDivTime; omega

lemma divisionWords_length (xs ys zs ws : Word) :
    (divisionWords xs ys zs ws).1.length ≤ max ys.length zs.length+xs.length ∧
    (divisionWords xs ys zs ws).2.length = xs.length+ws.length := by
  induction xs generalizing zs ws with
  | nil => simp only [divisionWords,List.length_nil,Nat.add_zero,Nat.zero_add]; exact ⟨Nat.le_max_right _ _,True.intro⟩
  | cons x xs ih =>
    have hh := ih (divisionRemainder ys (x::zs)) (divisionDigit ys (x::zs)::ws)
    have hr := divisionRemainder_length ys (x::zs)
    simp only [divisionWords,List.length_cons] at *
    constructor <;> omega
lemma divResult_length (x y : Word) : (divResult x y).1.length ≤ x.length+y.length ∧
    (divResult x y).2.length=y.length := by
  simpa only [divResult,List.length_reverse,List.length_nil,Nat.max_zero,Nat.add_zero] using divisionWords_length y.reverse x [] []
lemma rawDivTime_le (x y : Word) : rawDivTime x y ≤ 100*(x.length+y.length+1)^2 := by
  have hd := divisionCost_bound y.reverse x [] x.length le_rfl (by simp)
  have hl := divResult_length x y
  simp only [List.length_reverse] at hd
  unfold rawDivTime
  nlinarith

lemma bounded_div {n : ℕ} (O : IndependenceOracle n) (x y : Word) :
    Bounded divCode O (pair x y) (normalizedResult x y) (300*(x.length+y.length+1)^2) := by
  have h₁ := computes_rawDiv O x y
  have h₂ := computes_parallel (computes_normalCode O (divResult x y).1) (computes_normalCode O (divResult x y).2)
  have ht := computes_seq h₁ h₂
  simp only [normalWord_eq_bits] at ht
  have hl := divResult_length x y
  have hr := rawDivTime_le x y
  have hn₁ := normal_length (divResult x y).1
  have hn₂ := normal_length (divResult x y).2
  have hc₁ := normalCost_le (divResult x y).1
  have hc₂ := normalCost_le (divResult x y).2
  rw [normalWord_eq_bits] at hn₁ hn₂
  refine ⟨_,0,_,?_,Nat.zero_le _,?_,ht⟩ <;> nlinarith
lemma normalizedResult_pos (x y : Word) (hx : 0 < binaryValue x) :
    normalizedResult x y=pair (binaryValue y%binaryValue x).bits (binaryValue y/binaryValue x).bits := by
  have hh := divisionWords_correct y.reverse x hx
  simpa only [normalizedResult,divResult,List.reverse_reverse] using congrArg₂ (fun a b : ℕ => pair a.bits b.bits) hh.1 hh.2

lemma cmpBlock_body (i : Fin 10) (h : compareProgram (1 : Fin 9) 0 i ≠ .halt) :
    cmpBlock.code (cmpLabel i)=(compareProgram (1 : Fin 9) 0 i).relabel cmpLabel := by
  have hi : i.val<8 := by
    by_contra hn
    have hiv := i.isLt
    have : i.val=8 ∨ i.val=9 := by omega
    rcases this with hi|hi <;> simp [compareProgram,hi] at h
  simp [cmpBlock,cmpLabel,hi]
lemma runs_cmp {n : ℕ} (O : IndependenceOracle n) (x y s : Word) (bits : ℕ → Bool) :
    Runs cmpBlock O bits (regs y x [] s) (regs [decide (binaryValue x<binaryValue y)] [] [] s)
      (2*max x.length y.length+3) 0 (2*max x.length y.length+3) := by
  intro q w
  have hh := comparison_block (1 : Fin 9) 0 (by decide) O (regs [] [] [] s) x y q w bits
  simp only [pairRegisters,update_regs_zero,update_regs_one] at hh
  have hp := execution_relabel_before_any_halt (compareProgram (1 : Fin 9) 0) cmpBlock.code
    cmpLabel cmpBlock_body O (state (regs y x [] s) 0 q w) bits (2*max x.length y.length+2)
    (by rw [show state (regs y x [] s) 0 q w=compareConfig (regs y x [] s) 0 q w by rfl,hh]; rfl)
  rw [show state (regs y x [] s) 0 q w=compareConfig (regs y x [] s) 0 q w by rfl,hh] at hp
  change execution cmpBlock.code O (state (regs y x [] s) 0 q w) bits (2*max x.length y.length+2)=_ at hp
  rw [show 2*max x.length y.length+3=(2*max x.length y.length+2)+1 by omega,execution_add,hp]
  by_cases h : binaryValue x<binaryValue y <;>
    simp [h,relabelConfig,cmpLabel,compareConfig,state,execution,machineStep,cmpBlock,lastLabel,Nat.add_assoc]

lemma computes_cmp {n : ℕ} (O : IndependenceOracle n) (x y : Word) :
    Computes cmpCode O (pair x y) [decide (binaryValue x<binaryValue y)]
      (3*x.length+2*max x.length y.length+4) 0 (3*x.length+2*max x.length y.length+4) := by
  intro s bits
  have hu := split_pair O x y [] s bits
  simp only [List.append_nil] at hu
  have hr := runs_cmp O x y s (fun i => bits (3*x.length+1+i))
  have hh := runs_seq O bits hu hr
  convert hh using 1 <;> first | rfl | omega
lemma bounded_cmp {n : ℕ} (O : IndependenceOracle n) (x y : Word) :
    Bounded cmpCode O (pair x y) [decide (binaryValue x<binaryValue y)] (5*(x.length+y.length+1)) := by
  refine ⟨_,0,_,?_,Nat.zero_le _,?_,computes_cmp O x y⟩ <;> omega

lemma runs_repeat_cons {k n : ℕ} {p : Block k} {a : Fin (k+8)} {O : IndependenceOracle n}
    {bits : ℕ → Bool} {R R' R'' : Registers k} {b : Bool} {xs : Word}
    {t q w u v z : ℕ}
    (hp : Runs p O (fun i => bits (1+i)) (Function.update R a xs) R' t q w)
    (hi : Runs (repeatBlock p a) O (fun i => bits (1+t+i)) R' R'' u v z) :
    Runs (repeatBlock p a) O bits (Function.update R a (b::xs)) R''
      (1+t+u) (q+v) (1+w+z) := by
  dsimp only [Runs, repeatBlock] at *
  intro q₀ w₀
  have hb := hp q₀ (w₀+1)
  have hnone : (execution p.code O (state (Function.update R a xs) 0 q₀ (w₀+1))
      (fun i => bits (1+i)) t).output=none := by rw [hb]; rfl
  have hl := execution_relabel_before_halt p.code (repeatProgram p.code a) (loopLabel p.size)
      (lastLabel p.size) p.exit_halt (repeatProgram_body p.code a) O _ (fun i => bits (1+i)) t hnone
  rw [execution_add,execution_add]
  change execution _ O (execution _ O (execution (repeatProgram p.code a) O
    (loopConfig (Function.update R a (b::xs)) 0 q₀ w₀) bits 1) _ _) _ _ = _
  rw [repeatProgram_pop]
  change execution _ O (execution _ O (relabelConfig _ (state (Function.update R a xs) 0 q₀ (w₀+1))) _ _) _ _ = _
  rw [hl,hb]
  simp only [relabelConfig,state,loopLabel_last]
  have hh := hi (q₀+q) (w₀+1+w)
  simpa [state,Nat.add_assoc] using hh

lemma unpack_one_two {n : ℕ} (O : IndependenceOracle n) (a x tail s : Word) (bits : ℕ → Bool) :
    Runs (unpack 1 2) O bits (regs a (pair x tail) [] s) (regs a tail x s)
      (3*x.length+1) 0 (3*x.length+1) := by
  simpa only [pair,pairRegisters,update_regs_one,update_regs_two] using
    runs_unpack_packed (k:=1) 1 2 (by decide) O (regs a [] [] s) x tail bits
lemma pack_two_zero {n : ℕ} (O : IndependenceOracle n) (a x s : Word) (bits : ℕ → Bool) :
    Runs (pack 2 0) O bits (regs a [] x s) (regs (pair x a) [] [] s)
      (3*x.length+2) 0 (3*x.length+2) := by
  simpa only [pair,pairRegisters,update_regs_zero,update_regs_two] using
    runs_pack (k:=1) 2 0 (by decide) O (regs [] [] [] s) x a bits
lemma save_one_with_two {n : ℕ} (O : IndependenceOracle n) (a y x s : Word) (bits : ℕ → Bool) :
    Runs (pack 1 8) O bits (regs a y x s) (regs a [] x (pair y s))
      (3*y.length+2) 0 (3*y.length+2) := by
  simpa only [pair,pairRegisters,update_regs_one,update_regs_eight] using
    runs_pack (k:=1) 1 8 (by decide) O (regs a [] x []) y s bits

lemma list_body {n : ℕ} {O : IndependenceOracle n} {p : Block 1} {x a b : Word}
    {t q w : ℕ} (h : Computes p O (pair x a) b t q w) (tail saved : Word) (bits : ℕ → Bool) :
    Runs (listBody p) O bits (regs a (pair x tail) [] saved) (regs b tail [] saved)
      (6*x.length+6*tail.length+6+t) q (6*x.length+6*tail.length+6+w) := by
  have h₁ := unpack_one_two O a x tail saved bits
  have h₂ := save_one_with_two O a tail x saved (fun i => bits (3*x.length+1+i))
  have h₃ := pack_two_zero O a x (pair tail saved) (fun i => bits (3*x.length+1+(3*tail.length+2+i)))
  have h₄ := h (pair tail saved) (fun i => bits (3*x.length+1+(3*tail.length+2+(3*x.length+2+i))))
  have h₅ := restore_one O b tail saved (fun i => bits (3*x.length+1+(3*tail.length+2+(3*x.length+2+(t+i)))))
  have ht := runs_seq O bits h₁ (runs_seq O _ h₂ (runs_seq O _ h₃ (runs_seq O _ h₄ h₅)))
  convert ht using 1 <;> first | rfl | omega

lemma computes_reverse {n : ℕ} (O : IndependenceOracle n) (x : Word) :
    Computes reverseCode O x x.reverse (6*x.length+3) 0 (6*x.length+3) := by
  intro s bits
  have hr := runs_reverse (k:=1) 0 1 (by decide) O (regs [] [] [] s) x [] bits
  simp only [pairRegisters,update_regs_zero,update_regs_one,List.append_nil] at hr
  have hm := move_one_zero O x.reverse [] s (fun i => bits (2*x.length+1+i))
  have ht := runs_seq O bits hr hm
  simpa only [reverseCode,List.append_nil,List.length_reverse,Nat.zero_add,
    show 2*x.length+1+(4*x.length+2)=6*x.length+3 by omega] using ht

lemma runs_boolList {n : ℕ} (O : IndependenceOracle n) (x y s : Word) (bits : ℕ → Bool) :
    Runs boolListBlock O bits (regs (words (y.map (fun b => [b]))) x [] s)
      (regs (words ((x.reverse++y).map (fun b => [b]))) [] [] s) (5*x.length+1) 0 (5*x.length+1) := by
  intro q w
  induction x generalizing y w bits with
  | nil => simp [execution,machineStep,boolListBlock,state,lastLabel]
  | cons b xs ih =>
    have hh : execution boolListBlock.code O
        (state (regs (words (y.map (fun b => [b]))) (b::xs) [] s) 0 q w) bits 5=
        state (regs (words ((b::y).map (fun b => [b]))) xs [] s) 0 q (w+5) := by
      cases b <;> simp [execution,machineStep,boolListBlock,state,words,pair,bitFrame,Nat.add_assoc] <;> rfl
    rw [List.length_cons,show 5*(xs.length+1)+1=5+(5*xs.length+1) by omega,execution_add,hh,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
    congr 1; omega

lemma computes_boolList {n : ℕ} (O : IndependenceOracle n) (x : Word) :
    Computes boolListCode O x (words (x.map (fun b => [b]))) (7*x.length+2) 0 (7*x.length+2) := by
  intro s bits
  have hr := runs_reverse (k:=1) 0 1 (by decide) O (regs [] [] [] s) x [] bits
  simp only [pairRegisters,update_regs_zero,update_regs_one,List.append_nil] at hr
  have hb := runs_boolList O x.reverse [] s (fun i => bits (2*x.length+1+i))
  simp only [List.map_nil,words,List.reverse_reverse,List.append_nil,List.length_reverse] at hb
  have ht := runs_seq O bits hr hb
  convert ht using 1 <;> first | rfl | omega

lemma computes_consWord {n : ℕ} (O : IndependenceOracle n) (b : Bool) (x : Word) :
    Computes consWordCode O (pair [b] x) (b::x) 6 0 6 := by
  have h (b : Bool) : Computes (push 0 b) O x (b::x) 1 0 1 := by
    intro s bits
    simpa only [regs_zero,update_regs_zero] using runs_push O bits (regs x [] [] s) 0 b
  have ht := computes_select (push 0 false) (push 0 true) b (x:=x) (y:=b::x) (by cases b <;> exact h _)
  exact ht

lemma computes_consList {n : ℕ} (O : IndependenceOracle n) (x : Word) (xs : List Word) :
    Computes consListCode O (pair x (words xs)) (words (x::xs)) 1 0 1 := by
  intro s bits
  simpa only [regs_zero,update_regs_zero,consListCode,words] using runs_push O bits (regs (pair x (words xs)) [] [] s) 0 true

lemma computes_append {n : ℕ} (O : IndependenceOracle n) (x y : Word) :
    Computes appendCode O (pair x y) (x++y) (7*x.length+3) 0 (7*x.length+3) := by
  intro s bits
  have hs := split_pair O x y [] s bits
  simp only [List.append_nil] at hs
  have hm := move_one_zero O x y s (fun i => bits (3*x.length+1+i))
  simpa only [appendCode,Nat.zero_add,show 3*x.length+1+(4*x.length+2)=7*x.length+3 by omega] using
    runs_seq O bits hs hm

lemma runs_sub {n : ℕ} (O : IndependenceOracle n) (x y s : Word)
    (hxy : binaryValue y≤binaryValue x) (bits : ℕ → Bool) :
    Runs subBlock O bits (regs y x [] s) (regs [] (subDigits false x y) [] s)
      (subTime x y) 0 (subTime x y) := by
  dsimp only [Runs,subBlock]
  intro q w
  have h := (subtraction_block (k:=1) 1 0 2 (by decide) (by decide) (by decide) O
    (regs [] [] [] s) x y hxy q w bits).2.2
  convert h using 1 <;> simp only [subTime,subConfig,state,tripleRegisters,pairRegisters,update_regs_zero,
    update_regs_one,update_regs_two,lastLabel,Nat.add_zero]
  rfl

lemma computes_sub {n : ℕ} (O : IndependenceOracle n) (x y : Word)
    (hxy : binaryValue y≤binaryValue x) :
    Computes subCode O (pair x y) (binaryValue x-binaryValue y).bits
      (3*x.length+1+subTime x y+4*(subDigits false x y).length+2+normalCost (subDigits false x y)) 0
      (3*x.length+1+subTime x y+4*(subDigits false x y).length+2+normalCost (subDigits false x y)) := by
  have hv := (subtraction_block (k:=1) 1 0 2 (by decide) (by decide) (by decide) O
    (regs [] [] [] []) x y hxy 0 0 (fun _ => false)).1
  intro s bits
  have hs := split_pair O x y [] s bits
  simp only [List.append_nil] at hs
  have hd := runs_sub O x y s hxy (fun i => bits (3*x.length+1+i))
  have hm := move_one_zero O (subDigits false x y) [] s (fun i => bits (3*x.length+1+(subTime x y+i)))
  simp only [List.append_nil] at hm
  have hn := computes_normalCode O (subDigits false x y) s
    (fun i => bits (3*x.length+1+(subTime x y+(4*(subDigits false x y).length+2+i))))
  rw [normalWord_eq_bits,hv] at hn
  have hh := runs_seq O bits hs (runs_seq O _ hd (runs_seq O _ hm hn))
  convert hh using 1 <;> first | rfl | omega
lemma bounded_sub {n : ℕ} (O : IndependenceOracle n) (x y : Word)
    (hxy : binaryValue y≤binaryValue x) :
    Bounded subCode O (pair x y) (binaryValue x-binaryValue y).bits (30*(x.length+y.length+1)) := by
  have h₁ := subDigits_length_cost false x y
  have h₂ := normalCost_le (subDigits false x y)
  refine ⟨_,0,_,?_,Nat.zero_le _,?_,computes_sub O x y hxy⟩ <;> dsimp only [subTime] <;> omega

lemma runs_rankPrep {n : ℕ} (O : IndependenceOracle n) (x y z s : Word) (bits : ℕ → Bool) :
    Runs rankPrep O bits (regs x y z s)
      (regs [] (List.replicate x.length false++y) (x.reverse++z) s) (3*x.length+1) 0 (3*x.length+1) := by
  dsimp only [Runs]
  intro q w
  induction x generalizing y z w bits with
  | nil => simp [execution,machineStep,rankPrep,state,lastLabel]
  | cons b xs ih =>
    have h : execution rankPrep.code O (state (regs (b::xs) y z s) 0 q w) bits 3=
        state (regs xs (false::y) (b::z) s) 0 q (w+3) := by
      cases b <;> simp [execution,machineStep,rankPrep,state,Nat.add_assoc] <;> rfl
    rw [List.length_cons,show 3*(xs.length+1)+1=3+(3*xs.length+1) by omega,execution_add,h,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_zero]
    congr 1
    · simp [List.replicate_add,List.append_assoc]
    · omega

lemma update_regs_three_empty (x y z s : Word) : Function.update (regs x y z s) 3 []=regs x y z s := by
  funext i; fin_cases i <;> simp [regs]
lemma greedyRegisters_regs (x y z s : Word) : greedyRegisters (regs [] [] [] s) x y z []=regs x y z s := by
  funext i; fin_cases i <;> simp [greedyRegisters,regs]

lemma popcountBits_length (xs ys : Word) : (popcountBits xs ys).length≤xs.length+ys.length := by
  induction xs generalizing ys with
  | nil => simp [popcountBits]
  | cons b xs ih =>
    cases b with
    | false => simpa only [popcountBits,Bool.false_eq_true,ite_false,List.length_cons] using
        (ih ys).trans (by omega)
    | true =>
      have h := ih (incrementBits ys)
      have hi := incrementBits_length ys
      simp only [popcountBits,ite_true,List.length_cons]
      omega
lemma rankBits_length {n : ℕ} (O : IndependenceOracle n) (which : Bool) (x : Word) :
    (rankBits which O x).length≤x.length := by
  simpa only [rankBits,wordGreedy_length,List.length_nil,Nat.add_zero] using
    popcountBits_length (wordGreedy (wordOracle which O) x []) []
lemma computes_rank {n : ℕ} (O : IndependenceOracle n) (which : Bool) (x : Word) (hx : x.length=n) :
    Computes (rankCode which) O x (rankWord O which x).bits
      (7*n+3+rankTime which O x.reverse+normalCost (rankBits which O x.reverse))
      (greedyCalls x.reverse)
      (7*n+3+rankWork which O x.reverse+normalCost (rankBits which O x.reverse)) := by
  intro s bits
  have hp := runs_rankPrep O x [] [] s bits
  simp only [hx,List.append_nil] at hp
  have hm := runs_move (k:=1) 2 3 0 (by decide) (by decide) (by decide) O
    (regs [] (List.replicate n false) [] s) x.reverse [] (fun i => bits (3*n+1+i))
  simp only [tripleRegisters,pairRegisters,update_regs_zero,update_regs_two,update_regs_three_empty,
    List.append_nil,List.length_reverse,hx] at hm
  have hr : Runs (readyRank which) O (fun i => bits (3*n+1+(4*n+2+i)))
      (regs x.reverse (List.replicate n false) [] s) (regs (rankBits which O x.reverse) [] [] s)
      (rankTime which O x.reverse) (greedyCalls x.reverse) (rankWork which O x.reverse) := by
    intro q w
    convert rank_run which O (regs [] [] [] s) x.reverse (by simpa only [List.length_reverse] using hx) q w (fun i => bits (3*n+1+(4*n+2+i))) using 1 <;>
      (try simp only [readyRank,state,rankConfig,greedyRegisters_regs,lastLabel]) <;> rfl
  have hn := computes_normalCode O (rankBits which O x.reverse) s
    (fun i => bits (3*n+1+(4*n+2+(rankTime which O x.reverse+i))))
  rw [normalWord_eq_bits] at hn
  have hh := runs_seq O bits hp (runs_seq O _ hm (runs_seq O _ hr hn))
  convert hh using 1 <;> first | rfl | omega
lemma bounded_rank {n : ℕ} (O : IndependenceOracle n) (which : Bool) (x : Word) (hx : x.length=n) :
    Bounded (rankCode which) O x (rankWord O which x).bits (100*(n+1)^2) := by
  have hr : x.reverse.length=n := by simpa only [List.length_reverse] using hx
  have ht := rankTime_bound which O x.reverse hr
  have hw := rankWork_bound which O x.reverse hr
  have hl := rankBits_length O which x.reverse
  have hn := normalCost_le (rankBits which O x.reverse)
  have hq := greedyCalls_bound x.reverse
  simp only [List.length_reverse,hx] at hl hq
  refine ⟨_,_,_,?_,?_,?_,computes_rank O which x hx⟩ <;> nlinarith

lemma bounded_fanout {n : ℕ} {O : IndependenceOracle n} {p q : Block 1} {x y z : Word} {B C : ℕ}
    (h : Bounded p O x y B) (g : Bounded q O x z C) :
    Bounded (fanout p q) O x (pair y z) (43*x.length+39*y.length+18*z.length+50+B+C) := by
  obtain ⟨t,a,w,ht,ha,hw,hp⟩ := h
  obtain ⟨u,b,v,hu,hb,hv,hq⟩ := g
  refine ⟨_,_,_,?_,?_,?_,computes_fanout hp hq⟩ <;> omega
lemma bounded_select {n : ℕ} {O : IndependenceOracle n} (p q : Block 1) (b : Bool) {x y : Word} {B : ℕ}
    (h : Bounded (if b then q else p) O x y B) :
    Bounded (selectCode p q) O (pair [b] x) y (5+B) := by
  obtain ⟨t,a,w,ht,ha,hw,hp⟩ := h
  refine ⟨_,_,_,?_,?_,?_,computes_select p q b hp⟩ <;> omega

lemma computes_bounded {n : ℕ} {O : IndependenceOracle n} {p : Block 1} {x y : Word} {c : ℕ}
    (h : Computes p O x y c 0 c) : Bounded p O x y c :=
  ⟨c,0,c,le_rfl,Nat.zero_le _,le_rfl,h⟩

lemma evalFold_loop {n : ℕ} {O : IndependenceOracle n} {a b : DataType}
    (p : Block 1) (f : Value (.prod a b) → Option (Value b × ℕ))
    (hf : ∀ x y c, f x=some (y,c) → Bounded p O (encode x) (encode y) c)
    (xs : List (Value a)) (z y : Value b) (c : ℕ) (h : evalFold f xs z=some (y,c)) :
    ∃ t q w, t≤1+c ∧ q≤c ∧ w≤1+c ∧ ∀ s bits,
      Runs (repeatBlock (listBody p) 1) O bits (regs (encode z) (encode (a:=.list a) xs) [] s)
        (regs (encode y) [] [] s) t q w := by
  induction xs generalizing z y c with
  | nil =>
    simp only [evalFold,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    refine ⟨1,0,1,by omega,by omega,by omega,?_⟩
    intro s bits
    dsimp only [Runs, repeatBlock]
    intro q w
    simpa only [repeatBlock,state,loopConfig,encode,List.map_nil,words,Nat.add_zero,update_regs_one] using
      repeatProgram_empty (listBody p).code 1 O (regs (encode z) [] [] s) q w bits
  | cons x xs ih =>
    cases h₁ : f (x,z) with
    | none => simp [evalFold,h₁] at h
    | some r =>
      rcases r with ⟨z',c₁⟩
      cases h₂ : evalFold f xs z' with
      | none => simp [evalFold,h₁,h₂] at h
      | some r =>
        rcases r with ⟨y',c₂⟩
        simp [evalFold,h₁,h₂] at h
        rcases h with ⟨rfl,rfl⟩
        obtain ⟨t₁,q₁,w₁,ht₁,hq₁,hw₁,hp⟩ := hf _ _ _ h₁
        obtain ⟨t₂,q₂,w₂,ht₂,hq₂,hw₂,hr⟩ := ih z' y' c₂ h₂
        refine ⟨7+6*width x+6*width (a:=.list a) xs+t₁+t₂,q₁+q₂,
          7+6*width x+6*width (a:=.list a) xs+w₁+w₂,by omega,by omega,by omega,?_⟩
        intro s bits
        have hb := list_body hp (encode (a:=.list a) xs) s (fun i => bits (1+i))
        have hh := runs_repeat_cons (R:=regs (encode z) [] [] s) (b:=true)
          (by simpa only [update_regs_one] using hb)
          (hr s (fun i => bits (1+(6*(encode x).length+6*(encode (a:=.list a) xs).length+6+t₁)+i)))
        simp only [update_regs_one] at hh
        convert hh using 1 <;> first | rfl | (dsimp only [width]; omega)

lemma evalFold_bounded {n : ℕ} {O : IndependenceOracle n} {a b : DataType}
    (p : Block 1) (f : Value (.prod a b) → Option (Value b × ℕ))
    (hf : ∀ x y c, f x=some (y,c) → Bounded p O (encode x) (encode y) c)
    (xs : List (Value a)) (z y : Value b) (c : ℕ) (h : evalFold f xs z=some (y,c)) :
    Bounded (foldCode p) O (encode (a:=.prod (.list a) b) (xs,z)) (encode y) (3*width (a:=.list a) xs+2+c) := by
  obtain ⟨t,q,w,ht,hq,hw,hl⟩ := evalFold_loop p f hf xs z y c h
  refine ⟨3*width (a:=.list a) xs+1+t,q,3*width (a:=.list a) xs+1+w,by omega,by omega,by omega,?_⟩
  intro s bits
  have hs := split_pair O (encode (a:=.list a) xs) (encode z) [] s bits
  simp only [List.append_nil] at hs
  simpa only [Nat.zero_add, foldCode, encode, width] using runs_seq O bits hs (hl s (fun i => bits (3*width (a:=.list a) xs+1+i)))

theorem compile_correct {n : ℕ} (O : IndependenceOracle n) {a b : DataType}
    (e : Expression a b) : ∀ x y c, evaluate O e x=some (y,c) →
      Bounded (compile e) O (encode x) (encode y) c := by
  induction e with
  | ident =>
    intro x y c h
    simp only [evaluate,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    exact computes_bounded (computes_skip O _)
  | constant v =>
    intro x y c h
    simp only [evaluate,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    exact computes_bounded (computes_const O _ _)
  | compose p q ihp ihq =>
    intro x y c h
    cases hp : evaluate O p x with
    | none => simp [evaluate,hp] at h
    | some r =>
      rcases r with ⟨z,d⟩
      cases hq : evaluate O q z with
      | none => simp [evaluate,hp,hq] at h
      | some r =>
        rcases r with ⟨v,f⟩
        simp [evaluate,hp,hq] at h
        rcases h with ⟨rfl,rfl⟩
        exact bounded_seq (ihp _ _ _ hp) (ihq _ _ _ hq)
  | both p q ihp ihq =>
    intro x y c h
    cases hp : evaluate O p x with
    | none => simp [evaluate,hp] at h
    | some r =>
      rcases r with ⟨z,d⟩
      cases hq : evaluate O q x with
      | none => simp [evaluate,hp,hq] at h
      | some r =>
        rcases r with ⟨v,f⟩
        simp [evaluate,hp,hq] at h
        rcases h with ⟨rfl,rfl⟩
        exact bounded_fanout (ihp _ _ _ hp) (ihq _ _ _ hq)
  | fst =>
    intro ⟨x,z⟩ y c h
    simp only [evaluate,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    exact computes_bounded (computes_first O _ _)
  | snd =>
    intro ⟨x,z⟩ y c h
    simp only [evaluate,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    exact computes_bounded (computes_second O _ _)
  | branch p q ihp ihq =>
    intro ⟨b,x⟩ y c h
    have he : (if b then evaluate O q x else evaluate O p x)=evaluate O (if b then q else p) x := by cases b <;> rfl
    cases hp : evaluate O (if b then q else p) x with
    | none => simp [evaluate,he,hp] at h
    | some r =>
      rcases r with ⟨z,d⟩
      simp [evaluate,he,hp] at h
      rcases h with ⟨rfl,rfl⟩
      apply bounded_select
      cases b with
      | false => exact ihp _ _ _ hp
      | true => exact ihq _ _ _ hp
  | fold p ih =>
    intro ⟨xs,z⟩ y c h
    cases hp : evalFold (evaluate O p) xs z with
    | none => simp [evaluate,hp] at h
    | some r =>
      rcases r with ⟨v,d⟩
      simp [evaluate,hp] at h
      rcases h with ⟨rfl,rfl⟩
      exact evalFold_bounded (compile p) (evaluate O p) ih xs z v d hp
  | cons =>
    intro ⟨x,xs⟩ y c h
    simp only [evaluate,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    exact computes_bounded (computes_consList O _ _)
  | consBit =>
    intro ⟨b,x⟩ y c h
    simp only [evaluate,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    exact computes_bounded (computes_consWord O _ _)
  | append =>
    intro ⟨x,z⟩ y c h
    simp only [evaluate,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    exact computes_bounded (computes_append O _ _)
  | reverse =>
    intro x y c h
    simp only [evaluate,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    exact computes_bounded (computes_reverse O _)
  | toList =>
    intro x y c h
    simp only [evaluate,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    exact computes_bounded (computes_boolList O _)
  | toBits =>
    intro x y c h
    simp only [evaluate,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    exact computes_bounded (computes_skip O _)
  | toNat =>
    intro x y c h
    simp only [evaluate,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    have hh := computes_bounded (computes_normalCode O x)
    rw [normalWord_eq_bits] at hh
    exact bounded_mono hh (normalCost_le x)
  | add =>
    intro ⟨x,z⟩ y c h
    simp only [evaluate,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    simpa only [compile, encode, binaryValue_bits] using bounded_add O x.bits z.bits
  | sub =>
    intro ⟨x,z⟩ y c h
    simp only [evaluate] at h
    by_cases hx : z≤x
    · simp only [ite_eq_left hx,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      simpa only [compile,encode,binaryValue_bits] using bounded_sub O x.bits z.bits
        (by simpa only [binaryValue_bits] using hx)
    · simp [hx] at h
  | rank b =>
    intro x y c h
    simp only [evaluate] at h
    by_cases hx : x.length=n
    · simp only [ite_eq_left hx,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      exact bounded_rank O b x hx
    · simp [hx] at h
  | mul =>
    intro ⟨x,z⟩ y c h
    simp only [evaluate,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    simpa only [compile, encode, binaryValue_bits] using bounded_mul O x.bits z.bits
  | less =>
    intro ⟨x,z⟩ y c h
    simp only [evaluate,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    simpa only [compile, encode, binaryValue_bits] using bounded_cmp O x.bits z.bits
  | divRem =>
    intro ⟨x,z⟩ y c h
    simp only [evaluate] at h
    by_cases hx : x=0
    · simp [hx] at h
    · simp only [ite_eq_right hx] at h
      simp only [Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      have hh := bounded_div O x.bits z.bits
      rw [normalizedResult_pos _ _ (by simpa only [binaryValue_bits] using Nat.pos_of_ne_zero hx)] at hh
      simpa only [compile, encode, binaryValue_bits] using hh
  | query b =>
    intro x y c h
    simp only [evaluate] at h
    by_cases hx : x.length=n
    · simp only [ite_eq_left hx] at h
      simp only [Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      exact ⟨n+3,1,3*n+3,by omega,by omega,le_rfl,computes_query O b x hx⟩
    · simp [hx] at h

lemma evalFold_forget {a b : DataType} (f : Value (.prod a b) → Option (Value b × ℕ))
    (g : Value (.prod a b) → Option (Value b)) (hfg : ∀ x,(f x).map Prod.fst=g x)
    (xs : List (Value a)) (z : Value b) : (evalFold f xs z).map Prod.fst=foldValue g xs z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
    rw [evalFold,foldValue,←hfg]
    cases hf : f (x,z) with
    | none => rfl
    | some r =>
      rcases r with ⟨z',c⟩
      simp only [Option.map_some,Option.bind_some]
      rw [←ih]
      cases hh : evalFold f xs z' <;> simp [hh]
lemma evaluate_forget {n : ℕ} (O : IndependenceOracle n) {a b : DataType} (e : Expression a b)
    (x : Value a) : (evaluate O e x).map Prod.fst=run O e x := by
  induction e with
  | compose p q ihp ihq =>
    simp only [evaluate,run,←ihp]
    cases hp : evaluate O p x with
    | none => rfl
    | some r =>
      rcases r with ⟨y,c⟩
      simp only [Option.map_some,Option.bind_some]
      rw [←ihq]
      cases hh : evaluate O q y <;> simp [hh]
  | both p q ihp ihq =>
    simp only [evaluate,run,←ihp,←ihq]
    cases evaluate O p x <;> cases evaluate O q x <;> rfl
  | branch p q ihp ihq =>
    rcases x with ⟨b,x⟩
    cases b <;> simp only [evaluate,run,Bool.false_eq_true,ite_false,ite_true,←ihp,←ihq] <;>
      first | (cases evaluate O p x <;> rfl) | (cases evaluate O q x <;> rfl)
  | fold p ih =>
    rcases x with ⟨xs,z⟩
    simp only [evaluate,run,←evalFold_forget (evaluate O p) (run O p) ih xs z]
    cases evalFold (evaluate O p) xs z <;> rfl
  | divRem => rcases x with ⟨x,y⟩; simp only [evaluate,run]; split_ifs <;> rfl
  | sub => rcases x with ⟨x,y⟩; simp only [evaluate,run]; split_ifs <;> rfl
  | query b => simp only [evaluate,run]; split_ifs <;> rfl
  | rank b => simp only [evaluate,run]; split_ifs <;> rfl
  | _ => rfl


namespace Expression
variable {n : ℕ} (O : IndependenceOracle n)
lemma run_listLength {a : DataType} (xs : List (Value a)) :
    run O listLength xs=some xs.length := by
  have hf : ∀ (ys : List (Value a)) (z : ℕ),
      foldValue (fun p : Value (.prod a .nat) => some (p.2+1)) ys z=some (z+ys.length) := by
    intro ys
    induction ys with
    | nil => intro z; simp [foldValue]
    | cons x ys ih => intro z; simpa [foldValue,ih] using congrArg some (by omega : z+1+ys.length=z+(ys.length+1))
  simp [listLength,run,hf]
lemma run_wordRepeatStep (b : Bool) (w : Word) :
    run O wordRepeatStep (b,w)=some (if b then false::(w++w) else w++w) := by
  cases b <;> rfl
lemma unary_value (xs : List Bool) (w : Word) :
    ∃ out, foldValue (run O wordRepeatStep) xs.reverse w=some out ∧
      out.length=2^xs.length*w.length+binaryValue xs := by
  induction xs generalizing w with
  | nil => exact ⟨w,rfl,by simp [binaryValue]⟩
  | cons b xs ih =>
    obtain ⟨u,hu,hl⟩ := ih w
    have happ : ∀ (ys zs : List Bool) v,
        foldValue (run O wordRepeatStep) (ys++zs) v=
          (foldValue (run O wordRepeatStep) ys v).bind (foldValue (run O wordRepeatStep) zs) := by
      intro ys
      induction ys with
      | nil => intros; rfl
      | cons y ys ih => intros; simp [foldValue,ih,Option.bind_assoc]
    refine ⟨(if b then false::(u++u) else u++u),?_,?_⟩
    · rw [List.reverse_cons,happ,hu]
      simp only [Option.bind_some,foldValue]
      rw [run_wordRepeatStep]; rfl
    · cases b <;> simp [List.length_append,hl,binaryValue,Nat.pow_succ] <;> ring
lemma run_unary (m : ℕ) : ∃ w,run O unary m=some w ∧ w.length=m := by
  obtain ⟨w,hw,hlen⟩ := unary_value O m.bits []
  refine ⟨w,?_,?_⟩
  · simpa [unary,run] using hw
  · simpa [binaryValue_bits] using hlen
end Expression

@[simp] lemma width_pair {a b : DataType} (x : Value a) (y : Value b) :
    width (a:=.prod a b) (x,y)=2*width x+1+width y := by simp [width,encode]
@[simp] lemma width_cons {a : DataType} (x : Value a) (xs : List (Value a)) :
    width (a:=.list a) (x::xs)=2*width x+2+width (a:=.list a) xs := by
  simp [width,encode,words]; omega
lemma list_length_le_width {a : DataType} (xs : List (Value a)) :
    xs.length≤width (a:=.list a) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.length_cons,width_cons]; omega

lemma safe_input {n S : ℕ} {O : IndependenceOracle n} {a b : DataType}
    {p : Expression a b} {x : Value a} (h : Safe O S p x) : width x≤S := by
  cases p <;> exact h.1
lemma safe_output {n S : ℕ} {O : IndependenceOracle n} {a b : DataType}
    {p : Expression a b} {x : Value a} (h : Safe O S p x) {y : Value b}
    (hr : run O p x=some y) : width y≤S := by
  cases p <;> exact h.2.1 y hr

lemma evalFold_charge {n : ℕ} (O : IndependenceOracle n) {a b : DataType}
    (p : Expression (.prod a b) b) (S E : ℕ)
    (hp : ∀ x y c,Safe O S p x → evaluate O p x=some (y,c) → c≤E)
    (xs : List (Value a)) (z y : Value b) (c : ℕ)
    (hs : FoldSafe (Safe O S p) (run O p) xs z) (hw : width (a:=.list a) xs≤S)
    (he : evalFold (evaluate O p) xs z=some (y,c)) :
    c≤xs.length*(7+12*S+E) := by
  induction xs generalizing z y c with
  | nil => simp [evalFold] at he; rcases he with ⟨rfl,rfl⟩; simp
  | cons x xs ih =>
    rw [evalFold] at he
    cases hh : evaluate O p (x,z) with
    | none => simp [hh] at he
    | some u =>
      rcases u with ⟨z',d⟩
      have hrun : run O p (x,z)=some z' := by rw [←evaluate_forget,hh]; rfl
      have hd := hp (x,z) z' d hs.1 hh
      have hw' : width (a:=.list a) xs≤S := by rw [width_cons] at hw; omega
      have hx : width x≤S := by rw [width_cons] at hw; omega
      cases ht : evalFold (evaluate O p) xs z' with
      | none => simp [hh,ht] at he
      | some u =>
        rcases u with ⟨y',e⟩
        simp [hh,ht] at he
        rcases he with ⟨rfl,rfl⟩
        have hh := ih z' y' e (hs.2 z' hrun) hw' ht
        simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
        omega

lemma charge_primitive (T : ℕ) : 300*(2*T+1)^2+100*T+100≤10000*(T+1)^2 := by nlinarith

lemma evaluate_charge {n : ℕ} (O : IndependenceOracle n) {a b : DataType} (p : Expression a b)
    (S : ℕ) (x : Value a) (y : Value b) (c : ℕ) (hs : Safe O S p x)
    (he : evaluate O p x=some (y,c)) : c≤chargeBound p (S+n) := by
  induction p generalizing S c with
  | compose p q ihp ihq =>
    rcases hs with ⟨hx,hy,hp,hq⟩
    simp only [evaluate] at he
    cases hpv : evaluate O p x with
    | none => simp [hpv] at he
    | some u =>
      rcases u with ⟨z,d⟩
      have hr : run O p x=some z := by rw [←evaluate_forget,hpv]; rfl
      have hd := ihp S x z d hp hpv
      cases hqv : evaluate O q z with
      | none => simp [hpv,hqv] at he
      | some u =>
        rcases u with ⟨y',e⟩
        simp [hpv,hqv] at he
        rcases he with ⟨rfl,rfl⟩
        have hh := ihq S z y' e (hq z hr) hqv
        simp only [chargeBound]; omega
  | both p q ihp ihq =>
    rcases hs with ⟨hx,hy,hp,hq⟩
    simp only [evaluate] at he
    cases hpv : evaluate O p x with
    | none => simp [hpv] at he
    | some u =>
      rcases u with ⟨z,d⟩
      have hr : run O p x=some z := by rw [←evaluate_forget,hpv]; rfl
      have hz := safe_output hp hr
      have hd := ihp S x z d hp hpv
      cases hqv : evaluate O q x with
      | none => simp [hpv,hqv] at he
      | some u =>
        rcases u with ⟨z',e⟩
        have hr' : run O q x=some z' := by rw [←evaluate_forget,hqv]; rfl
        have hz' := safe_output hq hr'
        simp [hpv,hqv] at he
        rcases he with ⟨rfl,rfl⟩
        have hh := ihq S x z' e hq hqv
        have hb := charge_primitive (S+n)
        simp only [chargeBound]; nlinarith
  | branch p q ihp ihq =>
    rcases x with ⟨b,x⟩
    rcases hs with ⟨hx,hy,hh⟩
    cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hh <;>
      simp only [evaluate,Bool.false_eq_true,ite_false,ite_true] at he
    · cases hv : evaluate O p x with
      | none => simp [hv] at he
      | some u =>
        rcases u with ⟨y',d⟩
        simp [hv] at he
        rcases he with ⟨rfl,rfl⟩
        have hd := ihp S x y' d hh hv
        have hb := charge_primitive (S+n)
        simp only [chargeBound]; omega
    · cases hv : evaluate O q x with
      | none => simp [hv] at he
      | some u =>
        rcases u with ⟨y',d⟩
        simp [hv] at he
        rcases he with ⟨rfl,rfl⟩
        have hd := ihq S x y' d hh hv
        have hb := charge_primitive (S+n)
        simp only [chargeBound]; omega
  | fold p ih =>
    rcases x with ⟨xs,z⟩
    rcases hs with ⟨hx,hy,hh⟩
    have hw : width (a:=.list _) xs≤S := by rw [width_pair] at hx; omega
    have hlen := list_length_le_width xs
    simp only [evaluate] at he
    cases hv : evalFold (evaluate O p) xs z with
    | none => simp [hv] at he
    | some u =>
      rcases u with ⟨y',d⟩
      simp [hv] at he
      rcases he with ⟨rfl,rfl⟩
      have hd := evalFold_charge O p S (chargeBound p (S+n)) (fun x y c => ih S x y c) xs z y' d hh hw hv
      have hb := charge_primitive (S+n)
      have hmul : xs.length*(7+12*S+chargeBound p (S+n))≤(S+n+1)*(10000*(S+n+1)^2+chargeBound p (S+n)) :=
        Nat.mul_le_mul (by omega) (by omega)
      simp only [chargeBound]; omega
  | ident => simp only [evaluate,Option.some.injEq,Prod.mk.injEq] at he; rcases he with ⟨rfl,rfl⟩; exact Nat.zero_le _
  | constant z =>
    have hx := safe_input hs
    have hz := safe_output hs (y:=z) rfl
    simp only [evaluate,Option.some.injEq,Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩
    have hb := charge_primitive (S+n)
    simp only [chargeBound]; omega
  | fst =>
    rcases x with ⟨u,v⟩
    have hx := safe_input hs
    rw [width_pair] at hx
    simp only [evaluate,Option.some.injEq,Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩
    have hb := charge_primitive (S+n)
    simp only [chargeBound]; omega
  | snd =>
    rcases x with ⟨u,v⟩
    have hx := safe_input hs
    rw [width_pair] at hx
    simp only [evaluate,Option.some.injEq,Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩
    have hb := charge_primitive (S+n)
    simp only [chargeBound]; omega
  | cons | consBit | append | add | sub | mul | less | divRem =>
    rcases x with ⟨x,y⟩
    have hx := safe_input hs
    have hb := charge_primitive (S+n)
    try simp only [width_pair] at hx
    simp only [evaluate] at he
    try split_ifs at he
    all_goals
      simp only [Option.some.injEq,Prod.mk.injEq] at he
      try contradiction
      rcases he with ⟨rfl,rfl⟩
      simp only [chargeBound,width,encode,pair_length] at hx ⊢
      nlinarith
  | reverse | toList | toBits | toNat | rank | query =>
    have hx := safe_input hs
    have hb := charge_primitive (S+n)
    simp only [evaluate] at he
    try split_ifs at he
    all_goals
      simp only [Option.some.injEq,Prod.mk.injEq] at he
      try contradiction
      rcases he with ⟨rfl,rfl⟩
      simp only [chargeBound,width,encode] at hx ⊢
      nlinarith

lemma monomial_add_bound (T C D e f x y : ℕ) (hx : x≤C*(T+1)^e) (hy : y≤D*(T+1)^f) :
    10000*(T+1)^2+x+y≤(10000+C+D)*(T+1)^(e+f+3) := by
  have hbase : 1≤T+1 := by omega
  have hp : (T+1)^2≤(T+1)^(e+f+3) := Nat.pow_le_pow_right hbase (by omega)
  have he : (T+1)^e≤(T+1)^(e+f+3) := Nat.pow_le_pow_right hbase (by omega)
  have hf : (T+1)^f≤(T+1)^(e+f+3) := Nat.pow_le_pow_right hbase (by omega)
  have hx' := hx.trans (Nat.mul_le_mul_left C he)
  have hy' := hy.trans (Nat.mul_le_mul_left D hf)
  calc
    _ ≤ 10000*(T+1)^(e+f+3)+C*(T+1)^(e+f+3)+D*(T+1)^(e+f+3) := by omega
    _ = _ := by ring
lemma monomial_fold_bound (T C e x : ℕ) (hx : x≤C*(T+1)^e) :
    10000*(T+1)^2+(T+1)*(10000*(T+1)^2+x)≤(20000+C)*(T+1)^(e+3) := by
  have hbase : 1≤T+1 := by omega
  have hp : (T+1)^2≤(T+1)^(e+3) := Nat.pow_le_pow_right hbase (by omega)
  have hq : (T+1)^3≤(T+1)^(e+3) := Nat.pow_le_pow_right hbase (by omega)
  have he : (T+1)^(e+1)≤(T+1)^(e+3) := Nat.pow_le_pow_right hbase (by omega)
  calc
    _ ≤ 10000*(T+1)^2+(T+1)*(10000*(T+1)^2+C*(T+1)^e) := by gcongr
    _ = 10000*(T+1)^2+10000*(T+1)^3+C*(T+1)^(e+1) := by ring
    _ ≤ 10000*(T+1)^(e+3)+10000*(T+1)^(e+3)+C*(T+1)^(e+3) := by gcongr
    _ = _ := by ring

lemma chargeBound_polynomial {a b : DataType} (p : Expression a b) (T : ℕ) :
    chargeBound p T≤chargeCoefficient p*(T+1)^chargeDegree p := by
  induction p with
  | compose p q ihp ihq | both p q ihp ihq | branch p q ihp ihq =>
      exact monomial_add_bound T _ _ _ _ _ _ ihp ihq
  | fold p ih => exact monomial_fold_bound T _ _ _ ih
  | ident | constant | fst | snd | cons | consBit | append | reverse | toList | toBits | toNat |
    add | sub | mul | less | divRem | query | rank => exact Nat.le_refl _

lemma evaluate_polynomial {n : ℕ} (O : IndependenceOracle n) {a b : DataType} (p : Expression a b)
    (S : ℕ) (x : Value a) (y : Value b) (c : ℕ) (hs : Safe O S p x)
    (he : evaluate O p x=some (y,c)) :
    c≤chargeCoefficient p*(S+n+1)^chargeDegree p :=
  (evaluate_charge O p S x y c hs he).trans (chargeBound_polynomial p (S+n))

open Expression

open Expression

lemma rationalPair_value {q : ℚ} (hq : 0≤q) :
    ((rationalPair q).1:ℚ)/((rationalPair q).2:ℚ)=q := by
  dsimp [rationalPair]
  have hnum : 0≤q.num := Rat.num_nonneg.mpr hq
  have he : (q.num.natAbs:ℚ)=(q.num:ℚ) := by
    have hnat : (q.num.natAbs:ℤ)=q.num := Int.natAbs_of_nonneg hnum
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℚ)) hnat
  rw [he]
  exact Rat.num_div_den q

namespace Expression

lemma run_compose {n : ℕ} (O : IndependenceOracle n) {a b c : DataType}
    (p : Expression a b) (q : Expression b c) (x : Value a) :
    run O (p >>> q) x=(run O p x).bind (run O q) := rfl
lemma run_both {n : ℕ} (O : IndependenceOracle n) {a b c : DataType}
    (p : Expression a b) (q : Expression a c) (x : Value a) :
    run O (both p q) x=(run O p x).bind (fun y => (run O q x).map (fun z => (y,z))) := by
  simp only [run]
  congr 1
  funext y
  cases run O q x <;> rfl

end Expression

open Expression

open Expression

open Expression

open Expression
end MachineCode

namespace MachineCode

open Expression
open scoped Classical

open Expression

open Expression
open scoped Classical

open Expression
open scoped Classical

open Expression

open Expression
open scoped Classical

open Expression
open scoped Classical

open Expression

open Expression Effect

open Expression
open scoped Classical

open Expression

open Expression Effect

open Expression
namespace Expression

lemma run_natPow {n : ℕ} (O : IndependenceOracle n) (k x : ℕ) :
    run O (natPow k) x=some (x^k) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [natPow,run_compose,ih,run,pow_succ,Nat.mul_comm]
lemma run_ceilDivCode {n : ℕ} (O : IndependenceOracle n) (a b : ℕ) (ha : 0<a) :
    run O ceilDivCode (a,b)=some ((b+a-1)/a) := by
  simp only [ceilDivCode,sumE,run_compose,run_both,run_fst,run_snd,run_constant,
    Option.bind_some,Option.map_some]
  simp only [show run O add (b,a)=some (b+a) by rfl,Option.bind_some,]
  rw [run_natSub]
  simp [run,ha.ne']
lemma run_lengthNatCode {n : ℕ} (O : IndependenceOracle n) (x : ℕ) :
    run O lengthNatCode x=some x.bits.length := by
  change run O (listLength (a:=.bool)) x.bits=_
  exact run_listLength O _
lemma run_annealLengthCode {n : ℕ} (O : IndependenceOracle n) (x e : ℕ) :
    run O annealLengthCode (x,e)=some (2*x*(x+(e+5))) := by
  simp [annealLengthCode,prodE,sumE,run_compose,run]
lemma run_sampleCountCode {n : ℕ} (O : IndependenceOracle n) (x L E : ℕ) :
    run O sampleCountCode (x,(L,E))=some (10^14*(L+1)^3*x^14*E^2+1) := by
  simp only [sampleCountCode,prodE,sumE,run_compose,run_both,run_constant,run_fst,run_snd,
    Option.bind_some,Option.map_some,run_natPow]
  rfl
lemma run_tauCode {n : ℕ} (O : IndependenceOracle n) (x L : ℕ) :
    run O tauCode (x,L)=some (20*x^4*(x*(L+1)+2)) := by
  simp only [tauCode,prodE,sumE,run_compose,run_both,run_constant,run_fst,run_snd,
    Option.bind_some,Option.map_some,run_natPow]
  rfl
lemma run_capCode {n : ℕ} (O : IndependenceOracle n) (x L : ℕ) :
    run O capCode (x,L)=some (restartCap x L) := by
  simp only [capCode,prodE,sumE,run_compose,run_both,run_constant,run_fst,run_snd,
    Option.bind_some,Option.map_some,run_natPow]
  simp only [run,Option.bind_some,Option.map_some]
  rw [run_tauCode]
  rfl
end Expression

lemma ceil_nat_ratio (a b : ℕ) (ha : 0<a) : ⌈(b:ℚ)/a⌉₊=(b+a-1)/a := by
  apply le_antisymm
  · apply Nat.ceil_le.mpr
    apply (div_le_iff₀ (by exact_mod_cast ha)).mpr
    have h : b≤a*((b+a-1)/a) := (ceilDiv_le_iff_le_mul ha).mp (le_rfl : b⌈/⌉a≤b⌈/⌉a)
    exact_mod_cast (by simpa [Nat.mul_comm] using h)
  · change b⌈/⌉a≤⌈(b:ℚ)/a⌉₊
    apply (ceilDiv_le_iff_le_mul ha).mpr
    have h := Nat.le_ceil ((b:ℚ)/a)
    have h' := (div_le_iff₀ (by exact_mod_cast ha : (0:ℚ)<a)).mp h
    have h'' : (b:ℚ)≤(a:ℚ)*(⌈(b:ℚ)/a⌉₊:ℚ) := by simpa [mul_comm] using h'
    exact_mod_cast h''
lemma inverse_ceiling_input (ε : ℚ) (hε : 0<ε) :
    ⌈ε⁻¹⌉₊=(ε.den+ε.num.natAbs-1)/ε.num.natAbs := by
  have hp : 0<ε.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hε))
  have hn : ((ε.num.natAbs:ℕ):ℚ)=ε.num := by
    rw [←Int.cast_natCast,Int.natCast_natAbs,abs_of_pos (Rat.num_pos.mpr hε)]
  rw [←ceil_nat_ratio _ _ hp]
  congr 1
  rw [hn]
  conv_lhs => rw [←Rat.num_div_den ε,inv_div]
open Expression Effect
namespace Expression
lemma run_frozenN {n : ℕ} (O : IndependenceOracle n) (r : ℕ) (ε δ : ℚ) :
    run O frozenN (frozenValue n r ε δ)=some n := rfl
lemma run_frozenL {n : ℕ} (O : IndependenceOracle n) (r : ℕ) (ε δ : ℚ) :
    run O frozenL (frozenValue n r ε δ)=some (annealLength n (accuracyExponent ε)) := by
  simp only [frozenL,frozenN,run_compose,run_both,run_fst,run_snd,Option.bind_some,frozenValue]
  rw [run_lengthNatCode,Option.map_some,Option.bind_some,run_annealLengthCode]
  rfl
lemma run_frozenE {n : ℕ} (O : IndependenceOracle n) (r : ℕ) (ε δ : ℚ) (hε : 0<ε) :
    run O frozenE (frozenValue n r ε δ)=some ⌈ε⁻¹⌉₊ := by
  change run O ceilDivCode (ε.num.natAbs,ε.den)=_
  rw [run_ceilDivCode O _ _ (Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hε))),inverse_ceiling_input ε hε]
lemma run_frozenSamples {n : ℕ} (O : IndependenceOracle n) (r : ℕ) (ε δ : ℚ) (hε : 0<ε) :
    run O frozenSamples (frozenValue n r ε δ)=some (sampleCount n (annealLength n (accuracyExponent ε)) ε) := by
  simp only [frozenSamples,run_compose,run_both,run_frozenN,run_frozenL,run_frozenE O r ε δ hε,Option.bind_some,Option.map_some]
  rw [run_sampleCountCode]; rfl
lemma run_frozenParams {n : ℕ} (O : IndependenceOracle n) (r : ℕ) (ε δ : ℚ) (hε : 0<ε) :
    run O frozenParams (frozenValue n r ε δ)=some (params n r (sampleCount n (annealLength n (accuracyExponent ε)) ε) (annealLength n (accuracyExponent ε))) := by
  simp only [frozenParams,run_both,run_compose,run_fst,run_frozenN,run_frozenL,run_frozenSamples O r ε δ hε,Option.bind_some,Option.map_some]
  rw [run_capCode,run_tauCode]; rfl
lemma run_frozenReps {n : ℕ} (O : IndependenceOracle n) (r : ℕ) (ε δ : ℚ) :
    run O frozenReps (frozenValue n r ε δ)=some (repetitionCount δ) := by
  simp only [frozenReps,prodE,sumE,run_compose,run_both,run_constant,run_snd,Option.bind_some,Option.map_some,frozenValue]
  rw [run_lengthNatCode]; rfl
lemma run_drawsCode {n : ℕ} (O : IndependenceOracle n) (x N L : ℕ) :
    run O drawsCode (x,(N,L))=some (algorithmDrawBound x N L) := by
  simp only [drawsCode,prodE,sumE,run_compose,run_both,run_constant,run_fst,run_snd,Option.bind_some,Option.map_some]
  rw [run_capCode O,run_tauCode O]
  rfl
lemma run_wordBoundCode {n : ℕ} (O : IndependenceOracle n) (x N L : ℕ) :
    run O wordBoundCode (x,(N,L))=some (drawWordBound x N L) := by
  simp only [wordBoundCode,prodE,sumE,run_compose,run_both,run_constant,run_fst,run_snd,Option.bind_some,Option.map_some,run_natPow]
  rfl
lemma run_frozenRecipe3 {n : ℕ} (O : IndependenceOracle n) (r : ℕ) (ε δ : ℚ) (hε : 0<ε) :
    run O frozenRecipe3 (frozenValue n r ε δ)=some (n,(sampleCount n (annealLength n (accuracyExponent ε)) ε,annealLength n (accuracyExponent ε))) := by
  simp only [frozenRecipe3,run_both,run_frozenN,run_frozenL,run_frozenSamples O r ε δ hε,Option.bind_some,Option.map_some]
lemma run_frozenPrepared {n : ℕ} (O : IndependenceOracle n) (r : ℕ) (ε δ : ℚ) (hε : 0<ε) :
    let L := annealLength n (accuracyExponent ε)
    let N := sampleCount n L ε
    run O frozenPrepared (frozenValue n r ε δ)=some (params n r N L,(repetitionCount δ,(algorithmDrawBound n N L,drawWordBound n N L))) := by
  simp only [frozenPrepared,frozenDraws,frozenWordBound,run_both,run_compose,run_frozenParams O r ε δ hε,run_frozenReps,run_frozenRecipe3 O r ε δ hε,Option.bind_some]
  rw [run_drawsCode O,run_wordBoundCode O]
  rfl
lemma run_frozenBitCount {n : ℕ} (O : IndependenceOracle n) (r : ℕ) (ε δ : ℚ) (hε : 0<ε) :
    run O frozenBitCount (frozenValue n r ε δ)=some (fairBitCount n ε δ) := by
  simp only [frozenBitCount,run_compose,run_frozenPrepared O r ε δ hε,run_snd,Option.bind_some]
  rfl
end Expression
lemma runs_coinPush {k n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool)
    (R : Registers k) (a : Fin (k+8)) :
    Runs (coinPush a) O bits R (Function.update R a (bits 0::R a)) 2 0 2 := by
  cases h : bits 0
  · exact fork_run_no .coin _ _ O bits (by simp [Test.result,h])
      (runs_push O (fun i => bits (1+i)) R a false)
  · exact fork_run_yes .coin _ _ O bits (by simp [Test.result,h])
      (runs_push O (fun i => bits (1+i)) R a true)

lemma sampledWord_get (m : ℕ) (bits : ℕ → Bool) (i : ℕ) (hi : i < m) :
    (sampledWord m bits)[i]'(by rw [sampledWord_length]; exact hi)=
      bits (3*(m-1-i)+1) := by
  induction m generalizing bits i with
  | zero => omega
  | succ m ih =>
    by_cases him : i < m
    · simp only [sampledWord]
      rw [List.getElem_append_left (by rw [sampledWord_length]; exact him),ih _ _ him]
      congr 1
      omega
    · have he : i=m := by omega
      subst i
      simp [sampledWord,List.getElem_append_right,sampledWord_length]
lemma sampledWord_ofFn (m : ℕ) (bits : ℕ → Bool) :
    sampledWord m bits=List.ofFn (fun i : Fin m => bits (3*(m-1-i.val)+1)) := by
  apply List.ext_getElem
  · simp [sampledWord_length]
  · intro i hi hj
    simp only [List.getElem_ofFn]
    exact sampledWord_get m bits i (by simpa [sampledWord_length] using hi)
lemma runs_coinLoop {k n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool)
    (R : Registers k) (a b : Fin (k+8)) (hab : a≠b) (xs : Word) :
    Runs (repeatBlock (coinPush b) a) O bits (Function.update R a xs)
      (Function.update (Function.update R b (sampledWord xs.length bits ++ R b)) a [])
      (3*xs.length+1) 0 (3*xs.length+1) := by
  induction xs generalizing R bits with
  | nil =>
    intro q w
    have h := repeatProgram_empty (coinPush b).code a O R q w bits
    convert h using 1 <;> simp [repeatBlock,sampledWord,state,loopConfig] ; rfl
  | cons x xs ih =>
    have hp := runs_coinPush O (fun i => bits (1+i)) (Function.update R a xs) b
    have hi := ih (fun i => bits (3+i)) (Function.update R b (bits 1::R b))
    have hc : Function.update (Function.update R a xs) b (bits 1::(Function.update R a xs) b)=
        Function.update (Function.update R b (bits 1::R b)) a xs := by
      rw [Function.update_of_ne hab.symm]
      exact Function.update_comm hab ..
    rw [hc] at hp
    have h := runs_repeat_cons (b:=x) hp hi
    convert h using 1 <;> simp only [sampledWord,List.length_cons]
    · simp only [Function.update_self,List.append_assoc,List.singleton_append]
      rw [Function.update_idem]
    · omega
    · omega

lemma runs_pack_any {k n : ℕ} (a d : Fin (k+8)) (had : a≠d)
    (O : IndependenceOracle n) (R : Registers k) (bits : ℕ → Bool) :
    Runs (pack a d) O bits R
      (Function.update (Function.update R a []) d (pair (R a) (R d)))
      (3*(R a).length+2) 0 (3*(R a).length+2) := by
  have h := runs_pack a d had O R (R a) (R d) bits
  have he : pairRegisters R a d (R a) (R d)=R := by
    simp [pairRegisters]
  rw [he] at h
  exact h
lemma runs_move_any {k n : ℕ} (a b d : Fin (k+8)) (hab : a≠b) (had : a≠d) (hbd : b≠d)
    (O : IndependenceOracle n) (R : Registers k) (hb : R b=[]) (hd : R d=[])
    (bits : ℕ → Bool) :
    Runs (move a b d) O bits R (Function.update (Function.update R a []) d (R a))
      (4*(R a).length+2) 0 (4*(R a).length+2) := by
  have h := runs_move a b d hab had hbd O R (R a) [] bits
  have he : tripleRegisters R a b d (R a) [] []=R := by
    unfold tripleRegisters pairRegisters
    rw [Function.update_eq_self]
    have h1 : Function.update R b []=R := by rw [←hb, Function.update_eq_self]
    rw [h1]
    rw [←hd,Function.update_eq_self]
  rw [he] at h
  simp only [List.append_nil] at h
  convert h using 1
  simp only [tripleRegisters, pairRegisters]
  rw [Function.update_comm hab,show Function.update R b []=R by rw [←hb,Function.update_eq_self]]
lemma runs_inputPack {n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool)
    (a b c d e f : Word) :
    Runs inputPack O bits (sixRegs a b c d e f)
      (regs (pair (pair a b) (pair (pair c d) (pair e f))) [] [] [])
      (inputTime a b c d e f) 0 (inputTime a b c d e f) := by
  have h1 (bits) : Runs (pack 4 5) O bits (sixRegs a b c d e f)
      (sixRegs a b c d [] (pair e f)) (3*e.length+2) 0 (3*e.length+2) := by
    convert runs_pack_any (k:=1) 4 5 (by decide) O (sixRegs a b c d e f) bits using 1
    all_goals first | rfl | (funext i; fin_cases i <;> simp [sixRegs])
  have h2 (bits) : Runs (pack 2 3) O bits (sixRegs a b c d [] (pair e f))
      (sixRegs a b [] (pair c d) [] (pair e f)) (3*c.length+2) 0 (3*c.length+2) := by
    convert runs_pack_any (k:=1) 2 3 (by decide) O (sixRegs a b c d [] (pair e f)) bits using 1
    all_goals first | rfl | (funext i; fin_cases i <;> simp [sixRegs])
  have h3 (bits) : Runs (pack 3 5) O bits (sixRegs a b [] (pair c d) [] (pair e f))
      (sixRegs a b [] [] [] (pair (pair c d) (pair e f)))
      (3*(pair c d).length+2) 0 (3*(pair c d).length+2) := by
    convert runs_pack_any (k:=1) 3 5 (by decide) O (sixRegs a b [] (pair c d) [] (pair e f)) bits using 1
    all_goals first | rfl | (funext i; fin_cases i <;> simp [sixRegs])
  have h4 (bits) : Runs (pack 0 1) O bits (sixRegs a b [] [] [] (pair (pair c d) (pair e f)))
      (sixRegs [] (pair a b) [] [] [] (pair (pair c d) (pair e f)))
      (3*a.length+2) 0 (3*a.length+2) := by
    convert runs_pack_any (k:=1) 0 1 (by decide) O (sixRegs a b [] [] [] (pair (pair c d) (pair e f))) bits using 1
    all_goals first | rfl | (funext i; fin_cases i <;> simp [sixRegs])
  have h5 (bits) : Runs (pack 1 5) O bits (sixRegs [] (pair a b) [] [] [] (pair (pair c d) (pair e f)))
      (sixRegs [] [] [] [] [] (pair (pair a b) (pair (pair c d) (pair e f))))
      (3*(pair a b).length+2) 0 (3*(pair a b).length+2) := by
    convert runs_pack_any (k:=1) 1 5 (by decide) O (sixRegs [] (pair a b) [] [] [] (pair (pair c d) (pair e f))) bits using 1
    all_goals first | rfl | (funext i; fin_cases i <;> simp [sixRegs])
  have h6 (bits) : Runs (move 5 2 0) O bits
      (sixRegs [] [] [] [] [] (pair (pair a b) (pair (pair c d) (pair e f))))
      (regs (pair (pair a b) (pair (pair c d) (pair e f))) [] [] [])
      (4*(pair (pair a b) (pair (pair c d) (pair e f))).length+2) 0
      (4*(pair (pair a b) (pair (pair c d) (pair e f))).length+2) := by
    convert runs_move_any (k:=1) 5 2 0 (by decide) (by decide) (by decide) O
      (sixRegs [] [] [] [] [] (pair (pair a b) (pair (pair c d) (pair e f)))) rfl rfl bits using 1
    all_goals first | rfl | (funext i; fin_cases i <;> simp [sixRegs,regs])
  exact runs_seq O bits (h1 _) (runs_seq O _ (h2 _) (runs_seq O _ (h3 _)
    (runs_seq O _ (h4 _) (runs_seq O _ (h5 _) (h6 _)))))
lemma inputTime_bound (a b c d e f : Word) :
    inputTime a b c d e f≤100*(6+a.length+b.length+c.length+d.length+e.length+f.length) := by
  simp only [inputTime,pair_length]
  omega

open Expression

open Expression
namespace SizePolynomial
lemma eval_pow (p : SizePolynomial) (k x : ℕ) : (p.pow k).eval x=(p.eval x)^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [pow,eval,ih,pow_succ]
end SizePolynomial

lemma master_pos (n r : ℕ) (ε δ : ℚ) : 0 < masterParameter n r ε δ := by
  unfold masterParameter; omega
lemma rank_le_ground {n r : ℕ} (M : Matroid (Fin n)) (hr : M.eRank=(r:ℕ∞)) : r ≤ n := by
  have h := M.eRank_le_encard_ground
  rw [hr] at h
  have hg : M.E.encard ≤ n := (Set.encard_mono (Set.subset_univ _)).trans_eq (by simp)
  exact_mod_cast h.trans hg
lemma master_fields (n r : ℕ) (ε δ : ℚ) :
    n ≤ masterParameter n r ε δ ∧ inputLength n r ε δ ≤ masterParameter n r ε δ ∧
    ε.den.bits.length ≤ masterParameter n r ε δ ∧ δ.den.bits.length ≤ masterParameter n r ε δ ∧
    ⌈ε⁻¹⌉₊ ≤ masterParameter n r ε δ ∧ bitResourceParameter n ε δ ≤ masterParameter n r ε δ := by
  unfold masterParameter bitResourceParameter inputLength
  omega
lemma atom_ge (T : ℕ) : T ≤ atomPoly.eval T ∧ 1 ≤ atomPoly.eval T := by
  simp only [atomPoly,SizePolynomial.eval,SizePolynomial.eval_pow]
  have h : T+1 ≤ (T+1)^24 := Nat.le_self_pow (by decide) _
  constructor <;> omega
lemma recipe_atom_bounds (n r : ℕ) (ε δ : ℚ) :
    let T := masterParameter n r ε δ
    let L := annealLength n (accuracyExponent ε)
    let N := sampleCount n L ε
    n ≤ atomPoly.eval T ∧ L ≤ atomPoly.eval T ∧ N ≤ atomPoly.eval T ∧
      drawWordBound n N L ≤ atomPoly.eval T ∧ algorithmDrawBound n N L ≤ atomPoly.eval T ∧
      repetitionCount δ ≤ atomPoly.eval T := by
  let T := masterParameter n r ε δ
  have hf := master_fields n r ε δ
  have hh := polynomial_recipe_bounds n ε.den.bits.length δ.den.bits.length ⌈ε⁻¹⌉₊ T
    (master_pos n r ε δ) hf.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1
  have hp (k : ℕ) (hk : k ≤ 24) : T^k ≤ (T+1)^24 :=
    (Nat.pow_le_pow_left (by omega : T ≤ T+1) k).trans
      (Nat.pow_le_pow_right (by omega : 1 ≤ T+1) hk)
  have h1 := hp 1 (by omega)
  simp only [pow_one] at h1
  refine ⟨hf.1.trans (atom_ge T).1,?_,?_,?_,?_,?_⟩
  all_goals simp only [atomPoly,SizePolynomial.eval_pow,SizePolynomial.eval]
  all_goals dsimp only [T] at h1 hp hh
  · exact hh.1.trans (by have h := hp 2 (by omega); omega)
  · exact hh.2.1.trans (by have h := hp 22 (by omega); omega)
  · exact hh.2.2.1.trans (by have h := hp 24 (by omega); omega)
  · exact hh.2.2.2.1.trans (by have h := hp 24 (by omega); omega)
  · exact hh.2.2.2.2.trans (by omega)
lemma envelope_parameters (n r : ℕ) (ε δ : ℚ) (hr : r ≤ n) :
    let T := masterParameter n r ε δ
    let S := sourceEnvelope.eval T
    let L := annealLength n (accuracyExponent ε)
    let N := sampleCount n L ε
    n ≤ S ∧ r ≤ S ∧ N ≤ S ∧ L ≤ S ∧ restartCap n L ≤ S ∧ 20*n^4*(n*(L+1)+2) ≤ S ∧
      repetitionCount δ ≤ S ∧ algorithmDrawBound n N L+6 ≤ S ∧ drawWordBound n N L ≤ S ∧
      fairBitCount n ε δ ≤ S ∧ inputLength n r ε δ ≤ S := by
  let T := masterParameter n r ε δ
  let A := atomPoly.eval T
  let L := annealLength n (accuracyExponent ε)
  have hh := recipe_atom_bounds n r ε δ
  have ht : 20*n^4*(n*(L+1)+2) ≤ tauPoly.eval T := by
    simp only [tauPoly,SizePolynomial.eval,SizePolynomial.eval_pow]
    gcongr
    · exact hh.1
    · exact hh.1
    · exact hh.2.1
  have hc : restartCap n L ≤ capPoly.eval T := by
    unfold restartCap
    simp only [capPoly,SizePolynomial.eval,SizePolynomial.eval_pow]
    gcongr <;> first | exact hh.2.1 | exact hh.1
  have hb : fairBitCount n ε δ ≤ fairPoly.eval T := by
    apply (fairBitCount_polynomial n ε δ).trans
    simp only [fairPoly,SizePolynomial.eval,SizePolynomial.eval_pow]
    gcongr
    have hf := (master_fields n r ε δ).2.2.2.2.2
    omega
  have hi : inputLength n r ε δ ≤ atomPoly.eval T :=
    (master_fields n r ε δ).2.1.trans (atom_ge T).1
  dsimp only [sourceEnvelope,SizePolynomial.eval]
  dsimp only at hh
  dsimp only [T,L] at ht hc hb hi
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega,
    by omega,by omega,by omega,by omega,by omega⟩

open Expression Effect

open Expression
lemma compile_safe_bound {n : ℕ} (O : IndependenceOracle n) {a b : DataType}
    (p : Expression a b) (S : ℕ) (x : Value a) (y : Value b)
    (hs : Safe O S p x) (hr : run O p x=some y) :
    Bounded (compile p) O (encode x) (encode y)
      (chargeCoefficient p*(S+n+1)^chargeDegree p) := by
  rw [←evaluate_forget] at hr
  cases he : evaluate O p x with
  | none => simp [he] at hr
  | some v =>
    rcases v with ⟨y',c⟩
    simp only [he,Option.map_some,Option.some.injEq] at hr
    subst y'
    exact bounded_mono (compile_correct O p x y c he) (evaluate_polynomial O p S x y c hs he)

lemma compile_majorant {n : ℕ} (O : IndependenceOracle n) {a b : DataType}
    (p : Expression a b) (f : SizePolynomial) (T : ℕ) (hn : n≤T)
    (x : Value a) (y : Value b) (hs : Safe O (f.eval T) p x) (hr : run O p x=some y) :
    Bounded (compile p) O (encode x) (encode y) ((compiledMajorant p f).eval T) := by
  apply bounded_mono (compile_safe_bound O p (f.eval T) x y hs hr)
  simp only [compiledMajorant,SizePolynomial.eval,SizePolynomial.eval_pow]
  gcongr

lemma runs_outputPack {n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool) (a b : Word) :
    Runs outputPack O bits (regs (pair a b) [] [] []) (outRegs a b)
      (outputTime a b) 0 (outputTime a b) := by
  let mid : Registers 1 := fun i => if i=0 then b else if i=6 then a else []
  have h1 (bits) : Runs (unpack 0 6) O bits (regs (pair a b) [] [] []) mid
      (3*a.length+1) 0 (3*a.length+1) := by
    convert runs_unpack_packed (k:=1) 0 6 (by decide) O (fun _ => []) a b bits using 1 <;>
      funext i <;> fin_cases i <;> simp [pairRegisters,regs,mid,pair]
  have h2 (bits) : Runs (move 0 1 7) O bits mid (outRegs a b)
      (4*b.length+2) 0 (4*b.length+2) := by
    convert runs_move_any (k:=1) 0 1 7 (by decide) (by decide) (by decide) O mid
      (by simp [mid]) (by simp [mid]) bits using 1
    all_goals first | rfl | (funext i; fin_cases i <;> simp [mid,outRegs])
  exact runs_seq O bits (h1 _) (h2 _)
lemma runs_coinLoop_regs {n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool)
    (x counter : Word) :
    Runs (repeatBlock (coinPush 2) 1) O bits (regs x counter [] [])
      (regs x [] (sampledWord counter.length bits) [])
      (3*counter.length+1) 0 (3*counter.length+1) := by
  have h := runs_coinLoop O bits (regs x [] [] []) 1 2 (by decide) counter
  simpa only [update_regs_one,update_regs_two,regs_two,List.append_nil] using h
lemma runs_randomPack {n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool) (p w : Word) :
    Runs (pack 2 0) O bits (regs p [] w []) (regs (pair w p) [] [] [])
      (3*w.length+2) 0 (3*w.length+2) := by
  simpa only [update_regs_zero,update_regs_two,regs_two,regs_zero] using
    runs_pack_any (k:=1) 2 0 (by decide) O (regs p [] w []) bits

lemma runs_pipeline {n : ℕ} (O : IndependenceOracle n) (bits : ℕ → Bool)
    (a b c d e f : Word) (pre post : Block 1) (counter params x y : Word)
    (tp qp wp tq qq wq : ℕ)
    (hp : Computes pre O (pair (pair a b) (pair (pair c d) (pair e f)))
      (pair counter params) tp qp wp)
    (hq : Computes post O
      (pair (sampledWord counter.length (fun j => bits (inputTime a b c d e f+tp+(3*counter.length+1)+j))) params)
        (pair x y) tq qq wq) :
    Runs (pipeline pre post) O bits (sixRegs a b c d e f) (outRegs x y)
      (pipelineTime (inputTime a b c d e f) tp counter.length tq x.length y.length)
      (qp+qq)
      (pipelineTime (inputTime a b c d e f) wp counter.length wq x.length y.length) := by
  have h0 := runs_inputPack O bits a b c d e f
  have h1 := hp [] (fun j => bits (inputTime a b c d e f+j))
  have h2 := split_pair O counter params [] [] (fun j => bits (inputTime a b c d e f+(tp+j)))
  simp only [List.append_nil] at h2
  let bs := fun j => bits (inputTime a b c d e f+(tp+((3*counter.length+1)+j)))
  have h3 := runs_coinLoop_regs O bs params counter
  have h4 := runs_randomPack O (fun j => bs (3*counter.length+1+j)) params (sampledWord counter.length bs)
  have h5 := hq [] (fun j => bs (3*counter.length+1+(3*(sampledWord counter.length bs).length+2+j)))
  have he : (fun j => bits (inputTime a b c d e f+tp+(3*counter.length+1)+j))=bs := by
    funext j; dsimp [bs]; congr 1; omega
  rw [he] at h5
  have h6 := runs_outputPack O
    (fun j => bs (3*counter.length+1+(3*(sampledWord counter.length bs).length+2+(tq+j)))) x y
  have h := runs_seq O bits h0 (runs_seq O _ h1 (runs_seq O _ h2
    (runs_seq O _ h3 (runs_seq O _ h4 (runs_seq O _ h5 h6)))))
  simpa only [pipeline,pipelineTime,outputTime,sampledWord_length,Nat.zero_add,Nat.add_zero] using h

lemma sampledWord_physical (start m : ℕ) (bits : ℕ → Bool) :
    sampledWord m (fun j => bits (start+j))=List.ofFn (physicalWord start m bits) := by
  rw [sampledWord_ofFn]
  apply congrArg List.ofFn
  funext i
  unfold physicalWord
  congr 1
lemma runs_terminal {n : ℕ} (p : Block 1) (O : IndependenceOracle n) (bits : ℕ → Bool)
    (R : Registers 1) (x y : Word) (t q w : ℕ) (h : Runs p O bits R (outRegs x y) t q w) :
    execution p.code O (state R 0 0 0) bits (t+1)=terminalState p x y q w := by
  rw [execution,h 0 0]
  simp only [Nat.zero_add]
  unfold machineStep state
  simp only [Option.isSome_none,Bool.false_eq_true,ite_false,p.exit_halt]
  simp only [outRegs,]
  rfl
lemma terminal_rational (p : Block 1) (z : ℚ) (hz : 0≤z) (q w : ℕ) :
    (terminalState p (rationalPair z).1.bits (rationalPair z).2.bits q w).output=some z := by
  change some ((binaryValue (rationalPair z).1.bits:ℚ)/(binaryValue (rationalPair z).2.bits:ℚ))=some z
  rw [binaryValue_bits,binaryValue_bits,rationalPair_value hz]

lemma pipeline_budget (i F cp cq W tp qp wp tq qq wq a b : ℕ)
    (htp : tp≤cp) (hqp : qp≤cp) (hwp : wp≤cp)
    (htq : tq≤cq) (hqq : qq≤cq) (hwq : wq≤cq) (ho : 2*a+1+b≤W) :
    pipelineTime i tp F tq a b+1≤pipelineBudget i F cp cq W ∧
    qp+qq≤pipelineBudget i F cp cq W ∧
    pipelineTime i wp F wq a b+a+b+1≤pipelineBudget i F cp cq W ∧
    i+tp+(3*F+1)+3*F+1≤pipelineBudget i F cp cq W := by
  unfold pipelineTime pipelineBudget
  omega

lemma pipeline_budgeted {n : ℕ} (O : IndependenceOracle n)
    (a b c d e f : Word) (pre post : Block 1) (counter params : Word)
    (cp cq W B : ℕ)
    (hp : Bounded pre O (pair (pair a b) (pair (pair c d) (pair e f)))
      (pair counter params) cp)
    (v : BitWord counter.length → ℚ) (hv : ∀ w,0≤v w)
    (hq : ∀ w,Bounded post O (pair (List.ofFn w) params)
      (pair (rationalPair (v w)).1.bits (rationalPair (v w)).2.bits) cq ∧
      2*(rationalPair (v w)).1.bits.length+1+(rationalPair (v w)).2.bits.length≤W)
    (hB : pipelineBudget (inputTime a b c d e f) counter.length cp cq W≤B) :
    ∃ start,start+3*counter.length+1≤B ∧ ∀ bits : ℕ → Bool,
      let out := execution (pipeline pre post).code O (state (sixRegs a b c d e f) 0 0 0) bits B
      out.output=some (v (physicalWord start counter.length bits)) ∧
        out.oracleCalls≤B ∧ out.bitOperations≤B := by
  obtain ⟨tp,qp,wp,htp,hqp,hwp,hp⟩ := hp
  let start := inputTime a b c d e f+tp+(3*counter.length+1)
  have hs : start+3*counter.length+1≤B := by
    apply le_trans _ hB
    unfold start pipelineBudget
    omega
  refine ⟨start,hs,?_⟩
  intro bits
  let w := physicalWord start counter.length bits
  obtain ⟨⟨tq,qq,wq,htq,hqq,hwq,hq⟩,ho⟩ := hq w
  have hr := runs_pipeline O bits a b c d e f pre post counter params
    (rationalPair (v w)).1.bits (rationalPair (v w)).2.bits tp qp wp tq qq wq hp
    (by rw [sampledWord_physical]; exact hq)
  have hb := pipeline_budget (inputTime a b c d e f) counter.length cp cq W
    tp qp wp tq qq wq (rationalPair (v w)).1.bits.length (rationalPair (v w)).2.bits.length
    htp hqp hwp htq hqq hwq ho
  have ht := runs_terminal (pipeline pre post) O bits _ _ _ _ _ _ hr
  have hout := terminal_rational (pipeline pre post) (v w) (hv w) (qp+qq)
    (pipelineTime (inputTime a b c d e f) wp counter.length wq
      (rationalPair (v w)).1.bits.length (rationalPair (v w)).2.bits.length)
  have hsome : (execution (pipeline pre post).code O (state (sixRegs a b c d e f) 0 0 0) bits
      (pipelineTime (inputTime a b c d e f) tp counter.length tq
        (rationalPair (v w)).1.bits.length (rationalPair (v w)).2.bits.length+1)).output.isSome := by
    rw [ht,hout]; rfl
  have he := execution_extend_output (pipeline pre post).code O (state (sixRegs a b c d e f) 0 0 0)
    bits _ B (hb.1.trans hB) hsome
  dsimp only
  rw [he,ht]
  exact ⟨hout,hb.2.1.trans hB,hb.2.2.1.trans hB⟩

lemma pipeline_budgeted_length {n : ℕ} (O : IndependenceOracle n)
    (a b c d e f : Word) (pre post : Block 1) (counter params : Word)
    (F cp cq W B : ℕ) (hF : counter.length=F)
    (hp : Bounded pre O (pair (pair a b) (pair (pair c d) (pair e f)))
      (pair counter params) cp)
    (v : BitWord F → ℚ) (hv : ∀ w,0≤v w)
    (hq : ∀ w,Bounded post O (pair (List.ofFn w) params)
      (pair (rationalPair (v w)).1.bits (rationalPair (v w)).2.bits) cq ∧
      2*(rationalPair (v w)).1.bits.length+1+(rationalPair (v w)).2.bits.length≤W)
    (hB : pipelineBudget (inputTime a b c d e f) F cp cq W≤B) :
    ∃ start,start+3*F+1≤B ∧ ∀ bits : ℕ → Bool,
      let out := execution (pipeline pre post).code O (state (sixRegs a b c d e f) 0 0 0) bits B
      out.output=some (v (physicalWord start F bits)) ∧
        out.oracleCalls≤B ∧ out.bitOperations≤B := by
  subst F
  exact pipeline_budgeted O a b c d e f pre post counter params cp cq W B hp v hv hq hB

open Expression

lemma totalResourcePoly_budget (fp fq : SizePolynomial) (n r : ℕ) (ε δ : ℚ) (hr : r≤n) :
    pipelineBudget
      (inputTime n.bits r.bits ε.num.natAbs.bits ε.den.bits δ.num.natAbs.bits δ.den.bits)
      (fairBitCount n ε δ) ((compiledMajorant preambleCode fp).eval (masterParameter n r ε δ))
      ((compiledMajorant postambleCode fq).eval (masterParameter n r ε δ))
      (fq.eval (masterParameter n r ε δ)) ≤
      (totalResourcePoly fp fq).eval (masterParameter n r ε δ) := by
  have hi := inputTime_bound n.bits r.bits ε.num.natAbs.bits ε.den.bits δ.num.natAbs.bits δ.den.bits
  change _ ≤ 100*inputLength n r ε δ at hi
  have ha := envelope_parameters n r ε δ hr
  have hF := ha.2.2.2.2.2.2.2.2.2.1
  have hI := ha.2.2.2.2.2.2.2.2.2.2
  simp only [pipelineBudget,totalResourcePoly,SizePolynomial.eval]
  omega

open Expression Effect
open scoped Classical

open Expression

open Expression
open scoped Classical

lemma run_preamble_generic {n : ℕ} (O : IndependenceOracle n) (x : Value FrozenData)
    (F : ℕ) (p : Value PreparedData)
    (hF : run O frozenBitCount x=some F) (hp : run O frozenPrepared x=some p) :
    ∃ counter : Word,counter.length=F ∧ run O preambleCode x=some (counter,p) := by
  obtain ⟨counter,hc,hl⟩ := run_unary O F
  refine ⟨counter,hl,?_⟩
  simp only [preambleCode,run_both,run_compose,hF,hc,hp,Option.bind_some,Option.map_some]
lemma run_preambleCode {n : ℕ} (O : IndependenceOracle n) (r : ℕ) (ε δ : ℚ) (hε : 0<ε) :
    ∃ counter : Word,counter.length=fairBitCount n ε δ ∧
      run O preambleCode (frozenValue n r ε δ)=some (counter,preparedValue n r ε δ) := by
  exact run_preamble_generic O _ _ _ (run_frozenBitCount O r ε δ hε) (run_frozenPrepared O r ε δ hε)

open Expression
lemma encode_natPair (z : Value NN) : encode z=pair z.1.bits z.2.bits := rfl
lemma encode_rawValue (n r : ℕ) (ε δ : ℚ) (w : BitWord (fairBitCount n ε δ)) :
    encode (rawValue n r ε δ w)=pair (List.ofFn w) (encode (preparedValue n r ε δ)) := rfl
lemma width_natPair (z : Value NN) : width z=2*z.1.bits.length+1+z.2.bits.length := by
  rw [width,encode_natPair,pair_length]

lemma frozen_machine_oai (fp fq : SizePolynomial) (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n) (ε δ : ℚ)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (hr₁ : M₁.eRank=(r:ℕ∞)) (hr₂ : M₂.eRank=(r:ℕ∞)) (hε : 0<ε)
    (hp : Safe O (fp.eval (masterParameter n r ε δ)) preambleCode (frozenValue n r ε δ))
    (hq : ∀ w : BitWord (fairBitCount n ε δ),
      Safe O (fq.eval (masterParameter n r ε δ)) postambleCode (rawValue n r ε δ w))
    (B : ℕ) (hB : (totalResourcePoly fp fq).eval (masterParameter n r ε δ)≤B) :
    ∃ (v : BitWord (fairBitCount n ε δ) → ℚ) (start : ℕ),
      OutputCertificate r M₁ M₂ O ε δ v ∧ start+3*fairBitCount n ε δ+1≤B ∧
      ∀ bits : ℕ → Bool,
        let out := execution fprasBlock.code O (initialConfig 1 fprasBlock.size n r ε δ) bits B
        out.output=some (v (physicalWord start (fairBitCount n ε δ) bits)) ∧
          out.oracleCalls≤B ∧ out.bitOperations≤B := by
  obtain ⟨v,hv⟩ := output_certificate r M₁ M₂ O hO hE₁ hE₂ hr₁ hr₂ ε δ
  obtain ⟨counter,hc,hpc⟩ := run_preambleCode O r ε δ hε
  have hn := (master_fields n r ε δ).1
  have hpre := compile_majorant O preambleCode fp (masterParameter n r ε δ) hn _ _ hp hpc
  have hpost (w : BitWord (fairBitCount n ε δ)) :
      Bounded (compile postambleCode) O (pair (List.ofFn w) (encode (preparedValue n r ε δ)))
        (pair (rationalPair (v w)).1.bits (rationalPair (v w)).2.bits)
        ((compiledMajorant postambleCode fq).eval (masterParameter n r ε δ)) ∧
      2*(rationalPair (v w)).1.bits.length+1+(rationalPair (v w)).2.bits.length≤
        fq.eval (masterParameter n r ε δ) := by
    constructor
    · have hm := compile_majorant O postambleCode fq (masterParameter n r ε δ) hn
        (rawValue n r ε δ w) (rationalPair (v w)) (hq w) (hv.1 w)
      rw [encode_rawValue,encode_natPair] at hm
      exact hm
    · have hw := safe_output (hq w) (hv.1 w)
      rw [width_natPair] at hw
      exact hw
  have hb := (totalResourcePoly_budget fp fq n r ε δ (rank_le_ground M₁ hr₁)).trans hB
  obtain ⟨start,hs,he⟩ := pipeline_budgeted_length O n.bits r.bits ε.num.natAbs.bits ε.den.bits
    δ.num.natAbs.bits δ.den.bits (compile preambleCode) (compile postambleCode)
    counter (encode (preparedValue n r ε δ)) (fairBitCount n ε δ)
    ((compiledMajorant preambleCode fp).eval (masterParameter n r ε δ))
    ((compiledMajorant postambleCode fq).eval (masterParameter n r ε δ))
    (fq.eval (masterParameter n r ε δ)) B hc hpre v (fun w => (hv.2.1 w).1) hpost hb
  exact ⟨v,start,hv,hs,he⟩

open scoped Classical

end MachineCode
end CommonBasesFPRAS

open CommonBasesFPRAS CommonBasesFPRAS.MachineCode

end OAI
end

theorem solution : type_of% @OAI.CommonBasesFPRAS.MachineCode.frozen_machine_oai := @OAI.CommonBasesFPRAS.MachineCode.frozen_machine_oai
