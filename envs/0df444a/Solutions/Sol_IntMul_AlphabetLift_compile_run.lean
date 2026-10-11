-- Prove2me | solution 1 for IntMul.AlphabetLift.compile_run
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T16:59:07.503578+00:00
-- url     : https://prove2.me/submissions/62f64f59-04c9-4e0b-a748-7332d0023b61

import Definitions.Def_IntMul_TaggedAlphabetLift
import Mathlib.Tactic
namespace IntMul.AlphabetLift
private theorem cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c;cases d;cases hs;cases hc;cases hh;rfl
private theorem decode_encode (M : MultitapeTM) (s : M.Sym) :
    BankedSimulation.decode M (encode M s)=s := by
  classical
  by_cases h : s=M.startSym <;> simp [encode,h,BankedSimulation.decode]
private theorem encode_action (M : MultitapeTM) (q : M.K) (a : Fin M.k → M.Sym) (i : Fin M.k) :
    BankedSimulation.protect M (encode M (a i)) ((M.δ q a).2 i).1 ((M.δ q a).2 i).2=
      (encode M ((M.δ q a).2 i).1,((M.δ q a).2 i).2) := by
  classical
  by_cases h : a i=M.startSym
  · obtain ⟨hw,hd⟩ := M.start_preserved q a i h
    simp only [encode,if_pos h,hw,if_pos rfl,BankedSimulation.protect]
    cases hm : ((M.δ q a).2 i).2 <;> simp_all
  · have hw := M.start_only_at_start q a i h
    simp [encode,h,hw,BankedSimulation.protect]
private theorem transition_embed (M : MultitapeTM) (q : M.K) (a : Fin M.k → M.Sym) :
    transition M q (fun i => encode M (a i))=
      ((M.δ q a).1,fun i => (encode M ((M.δ q a).2 i).1,((M.δ q a).2 i).2)) := by
  simp only [transition,decode_encode]
  congr 1;funext i;exact encode_action M q a i
private theorem step_embed (M : MultitapeTM) (c : M.Cfg) :
    (machine M).step (embed M c)=embed M (M.step c) := by
  have ht := transition_embed M c.state (fun i => c.cells i (c.head i))
  change transition M (embed M c).state
    (fun i => (embed M c).cells i ((embed M c).head i))=_ at ht
  apply cfg_ext (machine M)
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];funext i p
    change Function.update (fun j => encode M (c.cells i j)) (c.head i)
      (encode M ((M.δ c.state (fun j => c.cells j (c.head j))).2 i).1) p=
        encode M (Function.update (c.cells i) (c.head i)
          ((M.δ c.state (fun j => c.cells j (c.head j))).2 i).1 p)
    by_cases h : p=c.head i <;> simp [h]
  · simp only [MultitapeTM.step,ht];rfl
private theorem iterate_embed (M : MultitapeTM) (c : M.Cfg) (t : ℕ) :
    (machine M).step^[t] (embed M c)=embed M (M.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,step_embed,Function.iterate_succ_apply']
private theorem symbol_encodings (M : MultitapeTM) :
    encode M M.blank=some M.blank ∧ encode M M.startSym=none ∧
    encode M M.zero=some M.zero ∧ encode M M.one=some M.one ∧ encode M M.sep=some M.sep := by
  classical
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,not_or] at hd
  simp [encode];aesop
private theorem bit_encoding (M : MultitapeTM) (b : Bool) :
    encode M (M.bitSym b)=(machine M).bitSym b := by
  have hs := symbol_encodings M
  cases b <;> simp_all [MultitapeTM.bitSym]
private theorem tape_encoding (M : MultitapeTM) (w : List M.Sym) (p : ℕ) :
    encode M (M.tapeOf w p)=(machine M).tapeOf (w.map (encode M)) p := by
  have hs := symbol_encodings M
  cases p with
  | zero => exact hs.2.1
  | succ p =>
      change encode M (w.getD p M.blank)=(w.map (encode M)).getD p (some M.blank)
      rw [←hs.1,List.getD_map]
private theorem bitword_encoding (M : MultitapeTM) (w : List Bool) :
    (w.map M.bitSym).map (encode M)=w.map (machine M).bitSym := by
  simp only [List.map_map];congr 1;funext b;exact bit_encoding M b
private theorem initial_embedding (M : MultitapeTM) (x y : List Bool) :
    embed M (M.initCfg x y)=(machine M).initCfg x y := by
  have hs := symbol_encodings M
  apply cfg_ext (machine M)
  · rfl
  · funext i p
    change encode M ((if i=M.inTape then M.tapeOf (x.map M.bitSym++M.sep::y.map M.bitSym)
      else M.tapeOf []) p)=(if i=M.inTape then
        (machine M).tapeOf (x.map (machine M).bitSym++some M.sep::y.map (machine M).bitSym)
      else (machine M).tapeOf []) p
    by_cases h : i=M.inTape
    · rw [if_pos h,if_pos h,tape_encoding]
      simp only [List.map_append,List.map_cons,bitword_encoding,hs.2.2.2.2]
    · rw [if_neg h,if_neg h,tape_encoding];rfl
  · rfl
private theorem output_encoding (M : MultitapeTM) (c : M.Cfg) (w : List Bool) :
    (embed M c).cells (machine M).outTape=(machine M).tapeOf (w.map (machine M).bitSym) ↔
      c.cells M.outTape=M.tapeOf (w.map M.bitSym) := by
  have he : (machine M).tapeOf (w.map (machine M).bitSym)=
      fun p => encode M (M.tapeOf (w.map M.bitSym) p) := by
    funext p;rw [tape_encoding,bitword_encoding]
  rw [he]
  change (fun p => encode M (c.cells M.outTape p))=(fun p => encode M (M.tapeOf (w.map M.bitSym) p)) ↔ _
  constructor
  · intro h;funext p
    have hp := congrArg (BankedSimulation.decode M) (congrFun h p)
    simpa only [decode_encode] using hp
  · intro h;rw [h]

private theorem compile_run (M : MultitapeTM) :
    (∀ c : M.Cfg, ∀ t : ℕ, (machine M).step^[t] (embed M c)=embed M (M.step^[t] c)) ∧
    (∀ x y : List Bool, ∀ t : ℕ,
      (machine M).step^[t] ((machine M).initCfg x y)=embed M (M.step^[t] (M.initCfg x y))) ∧
    (∀ x y w : List Bool, ∀ t : ℕ,
      (machine M).HaltsWithOutput x y t w ↔ M.HaltsWithOutput x y t w) := by
  refine ⟨iterate_embed M,?_,?_⟩
  · intro x y t;rw [←initial_embedding,iterate_embed]
  · intro x y w t
    unfold MultitapeTM.HaltsWithOutput
    rw [←initial_embedding,iterate_embed,output_encoding]
    rfl
end IntMul.AlphabetLift

open IntMul IntMul.AlphabetLift

theorem solution (M : MultitapeTM) :
    (∀ c : M.Cfg, ∀ t : ℕ, (machine M).step^[t] (embed M c)=embed M (M.step^[t] c)) ∧
    (∀ x y : List Bool, ∀ t : ℕ,
      (machine M).step^[t] ((machine M).initCfg x y)=embed M (M.step^[t] (M.initCfg x y))) ∧
    (∀ x y w : List Bool, ∀ t : ℕ,
      (machine M).HaltsWithOutput x y t w ↔ M.HaltsWithOutput x y t w) :=
  IntMul.AlphabetLift.compile_run M

#print axioms solution
