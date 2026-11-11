-- Prove2me | solution 1 for OAI.UniformKServer.ConstructorSearch.exists_certificate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:58:13.50624+00:00
-- url     : https://prove2.me/submissions/ec4f46c9-cb90-4c19-bd51-81eca0f94e5f

import Mathlib
import Definitions.Def_UniformKServer
import Definitions.Def_Q220Uk011

section
-- module Solutions.Q220_UK.UniformKServer_FiniteRepresentation
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Finite arrays represented by ordinary lists, including sparse integer keys.
This is an existence lemma used to show that exhaustive certificate search halts;
it is not nonuniform advice to the online machine. -/
namespace UniformKServer.FiniteRepresentation
open scoped Classical

theorem represents {α β : Type*} [Fintype α] (key : α→ℕ) (hk : Function.Injective key)
    (f : α→β) (default : β) : ∃xs : List β,∀a,(xs.getD (key a) default)=f a := by
  let B := Finset.univ.sup key+1
  let g (i : Fin B) : β := if h : ∃a,key a=i.val then f (Classical.choose h) else default
  refine ⟨List.ofFn g,?_⟩
  intro a
  have hbound : key a<B := by
    exact Nat.lt_succ_of_le (Finset.le_sup (f:=key) (Finset.mem_univ a))
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hbound)]
  simp only [List.getElem_ofFn,g]
  have h : ∃b,key b=(⟨key a,hbound⟩:Fin B).val := ⟨a,rfl⟩
  rw [dite_eq_left h]
  congr 1
  exact hk (Classical.choose_spec h)

end UniformKServer.FiniteRepresentation

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawArithmetic
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! A primitive-recursive nonnegative rational presentation for the uniform
finite certificate search. Denominators are stored minus one, so every bit
string denotes a valid nonnegative rational; there is no division oracle. -/
namespace UniformKServer.RawArithmetic

theorem eq_present (a : ℚ) (ha : 0≤a) : value (a.num.natAbs,a.den-1)=a := by
  have hd : a.den-1+1=a.den := by have:=a.pos; omega
  unfold value
  rw [←Nat.cast_one (R:=ℚ),←Nat.cast_add,hd]
  have hn : (a.num.natAbs:ℚ)=a.num := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℚ))
      (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr ha))
  rw [hn,Rat.num_div_den]

open Primrec

end UniformKServer.RawArithmetic

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawPath
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawProgram.unpack_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                              
section

namespace UniformKServer.RawPath
open RawArithmetic RawTable RawWords

theorem history_cons (r j : ℕ) (w g : List ℕ) :
    history (r::w) (j::g)=(r,j)::history w g := by
  simp [history,List.range_succ_eq_map,List.map_map,Function.comp_def]

theorem fold_weight (n : ℕ) (d : List Q) (T p c : List ℕ) (m : ℕ) (q : Q) (h : List (ℕ×ℕ)) :
    (h.foldl (pathStep n d T) ((p,c),(m,q))).2.1=m*weight T p c h := by
  induction h generalizing p c m q with
  | nil=>simp [weight]
  | cons rj h ih=>
    obtain ⟨r,j⟩:=rj
    simp only [List.foldl_cons,pathStep,ih,weight]
    exact Nat.mul_assoc _ _ _

theorem fold_movement (n : ℕ) (d : List Q) (T p c : List ℕ) (m : ℕ) (q : Q) (h : List (ℕ×ℕ)) :
    value (h.foldl (pathStep n d T) ((p,c),(m,q))).2.2=value q+movement n d c h := by
  induction h generalizing p c m q with
  | nil=>simp [movement]
  | cons rj h ih=>
    obtain ⟨r,j⟩:=rj
    simp only [List.foldl_cons,pathStep,ih,movement,value_add]
    exact add_assoc _ _ _

theorem term_value (n : ℕ) (d : List Q) (T p c w g : List ℕ) :
    value (term n d T p c w g) =
      (weight T p c (history w g):ℚ)*movement n d c (history w g) := by
  simp [term,path,value_mul,value_natural,fold_weight,fold_movement]

theorem cost_value (n : ℕ) (d : List Q) (c w g : List ℕ) :
    value (cost n d c w g)=movement n d c (history w g) := by
  simp [cost,path,fold_movement]

theorem value_sum (xs : List Q) : value (xs.foldr add (natural 0))=(xs.map value).sum := by
  induction xs <;> simp [*]

theorem total_value (n k : ℕ) (d : List Q) (T p c w : List ℕ) :
    value (total n k d T p c w) =
      ((words k w.length).map fun g=>
        (weight T p c (history w g):ℚ)*movement n d c (history w g)).sum := by
  simp only [total,value_sum,List.map_map,Function.comp_def,term_value]

theorem expected_value (n k b : ℕ) (d : List Q) (T p c w : List ℕ) :
    value (expected n k b d T p c w)=value (total n k d T p c w)/(2:ℚ)^(b*w.length) := by
  have h : 2^(b*w.length)-1+1=2^(b*w.length) := by have:=Nat.two_pow_pos (b*w.length);omega
  simp only [expected,value_divide,←Nat.cast_one (R:=ℚ),←Nat.cast_add,h,Nat.cast_pow,Nat.cast_ofNat]

end UniformKServer.RawPath

end


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawTyped
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.Fallback.mem_coverers _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawMarks.covers_bits _root_.OAI.UniformKServer.lazyPath_nil_iff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                               
section

namespace UniformKServer.RawTyped
open RawArithmetic RawWords RawTable RawPath

theorem config_get {n k : ℕ} (c : Configuration n k) (j : Fin k) :
    (config c).getD j.val 0=(c j).val := by
  rw [List.getD_eq_getElem _ _ (by simp [config])]
  simp [config]

theorem config_set {n k : ℕ} (c : Configuration n k) (r : Fin n) (j : Fin k) :
    (config c).set j.val r.val=config (serve c r j) := by
  apply List.ext_getElem
  · simp [config]
  · intro i hi hj
    simp only [List.length_set,List.length_ofFn,config] at hi hj ⊢
    rw [List.getElem_set]
    simp only [List.getElem_ofFn,serve,Function.update_apply]
    by_cases h : j.val=i
    · have he : (⟨i,hj⟩:Fin k)=j := Fin.ext h.symm
      simp [h,he]
    · have he : (⟨i,hj⟩:Fin k)≠j := by intro he;exact h (congrArg Fin.val he).symm
      simp [h,he]

theorem history_zip {n k : ℕ} (w : List (Fin n)) (g : List (Fin k)) (h : w.length=g.length) :
    history (requests w) (requests g)=events (w.zip g) := by
  induction w generalizing g with
  | nil=>simp [requests,history,events]
  | cons r w ih=>
    cases g with
    | nil=>simp at h
    | cons j g=>
      have h' : w.length=g.length := by simpa using h
      simpa only [requests,List.map_cons,history_cons,List.zip_cons_cons,events] using
        congrArg ((r.val,j.val)::·) (ih g h')

end UniformKServer.RawTyped

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawMetric
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
attribute [-simp] _root_.OAI.UniformKServer.RawBinary.distances_length _root_.OAI.UniformKServer.RawProgram.unpack_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                
section

namespace UniformKServer.RawMetric
open RawArithmetic RawWords RawTable RawTyped RawCertificate

@[simp] theorem present_eq (a : ℚ) (ha : 0≤a) : value (present a)=a := eq_present a ha

theorem present_pos (a : ℚ) (ha : 0<a) : 0<(present a).1 := by
  change 0<a.num.natAbs
  exact Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr ha))

theorem bounds_ok {n : ℕ} (d : RationalMetric n) (draw : List Q)
    (hd : ∀x y : Fin n,value (dist n draw x.val y.val)=d.distance x y)
    (D δ : Q) (hdiam : ∀x y,d.distance x y≤value D)
    (hsep : ∀x y,x≠y→value δ≤d.distance x y) : boundsOK n draw D δ=true := by
  apply List.all_eq_true.mpr
  intro x hx
  apply List.all_eq_true.mpr
  intro y hy
  let x' : Fin n := ⟨x,List.mem_range.mp hx⟩
  let y' : Fin n := ⟨y,List.mem_range.mp hy⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true ((le_iff _ _).mpr (by
    change value (dist n draw x'.val y'.val)≤value D
    rw [hd];exact hdiam x' y')),?_⟩
  by_cases h : x=y
  · simp [h]
  · have h' : x'≠y' := fun he=>h (congrArg Fin.val he)
    have hs:=hsep x' y' h'
    have hl : le δ (dist n draw x y) := (le_iff _ _).mpr (by
      change value δ≤value (dist n draw x'.val y'.val)
      rw [hd];exact hs)
    simp [hl]

end UniformKServer.RawMetric

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawBinary
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawProgram.unpack_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                
section

namespace UniformKServer.RawBinary
open Primrec RawCertificate
attribute [fun_prop] Primrec.list_tail

theorem value_bits (a : ℕ) : value a.bits=a := by
  induction a using Nat.binaryRec' with
  | zero=>rfl
  | bit b n h ih=>rw [Nat.bits_append_bit n b h,value_cons,ih]

@[simp] theorem read_natCode (a : ℕ) (w : List Bool) : readNat (natCode a++w)=(a,w) := by
  have ht : ((natCode a++w).takeWhile id).length=a.bits.length := by
    simp [natCode,List.append_assoc]
  dsimp only [readNat]
  rw [ht]
  have hd : (natCode a++w).drop (a.bits.length+1)=a.bits++w := by
    simp [natCode,List.append_assoc,List.drop_append]
  rw [hd]
  simp [value_bits]

@[simp] theorem read_rationalCode (a : ℚ) (w : List Bool) :
    readQ (rationalCode a++w)=(RawMetric.present a,w) := by
  simp only [readQ,rationalCode,List.cons_append,List.tail_cons,List.append_assoc,read_natCode,
    RawMetric.present]

end UniformKServer.RawBinary

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawBits
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                              
section

namespace UniformKServer.RawBits
open Primrec

 theorem bits_value (w : List Bool) : (RawBinary.value (w++[true])).bits=w++[true] := by
  induction w with
  | nil=>simp
  | cons b w ih=>
    simp only [List.cons_append,RawBinary.value_cons]
    rw [Nat.bits_append_bit _ _ (fun h=>by
      have hh:=congrArg Nat.bits h
      rw [ih] at hh
      simp at hh),ih]

open Turing.PartrecToTM2

end UniformKServer.RawBits

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_BitSampling
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.BitSampling

theorem exact_row_proof {k b : ℕ} (N : Fin k → ℕ) (hN : ∑ j, N j = 2^b) :
    (∀ coins, 0 < N (row N hN coins)) ∧
    (∀ coins, cumulative N (row N hN coins) ≤ (bitsEquiv b coins).val ∧
      (bitsEquiv b coins).val < cumulative N (row N hN coins) + N (row N hN coins)) ∧
    (∀ f : Fin k → ℝ,
      (∑ coins : Fin b → Bool, f (row N hN coins)) / (2^b : ℕ) =
        ∑ j, (N j : ℝ) / (2^b : ℕ) * f j) := by
  let e : (Fin b → Bool) ≃ ((j : Fin k) × Fin (N j)) :=
    (bitsEquiv b).trans ((finCongr hN).symm.trans finSigmaFinEquiv.symm)
  refine ⟨?_, ?_, ?_⟩
  · intro coins
    exact Nat.zero_lt_of_lt (e coins).2.isLt
  · intro coins
    have he := congrArg Fin.val (finSigmaFinEquiv.apply_symm_apply
      ((finCongr hN).symm (bitsEquiv b coins)))
    rw [finSigmaFinEquiv_apply] at he
    change cumulative N (row N hN coins) + (e coins).2.val = (bitsEquiv b coins).val at he
    have ht := (e coins).2.isLt
    change (e coins).2.val < N (row N hN coins) at ht
    omega
  · intro f
    have hs : (∑ coins : Fin b → Bool, f (row N hN coins)) =
        ∑ j, (N j : ℝ) * f j := by
      calc
        _ = ∑ v : (j : Fin k) × Fin (N j), f v.1 :=
          e.sum_comp (fun v => f v.1)
        _ = _ := by simp [Fintype.sum_sigma]
    rw [hs, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring

                                                                            
theorem exact_row {k b : ℕ} (N : Fin k → ℕ) (hN : ∑ j, N j = 2^b) :
    (∀ coins, 0 < N (row N hN coins)) ∧
    (∀ coins, cumulative N (row N hN coins) ≤ (bitsEquiv b coins).val ∧
      (bitsEquiv b coins).val < cumulative N (row N hN coins) + N (row N hN coins)) ∧
    (∀ f : Fin k → ℝ,
      (∑ coins : Fin b → Bool, f (row N hN coins)) / (2^b : ℕ) =
        ∑ j, (N j : ℝ) / (2^b : ℕ) * f j) := by
  exact exact_row_proof N hN

end UniformKServer.BitSampling



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_BitPaths
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.BitSampling

theorem mean_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (v : B → ℝ) : mean (fun a => v (e a)) = mean v := by
  unfold mean
  rw [e.sum_comp, Fintype.card_congr e]

theorem mean_add {A : Type*} [Fintype A] (f g : A → ℝ) :
    mean (fun a => f a + g a) = mean f + mean g := by
  simp only [mean, Finset.sum_add_distrib, add_div]

theorem mean_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) :
    mean (fun _ : A => c) = c := by
  have hc : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero (α:=A))
  simp [mean, hc]

theorem mean_prod {A B : Type*} [Fintype A] [Fintype B] (f : A × B → ℝ) :
    mean f = mean (fun a => mean (fun b => f (a,b))) := by
  simp only [mean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  rw [mul_comm (Fintype.card A : ℝ), div_mul_eq_div_div, Finset.sum_div]

theorem mean_row {k b : ℕ} (N : Fin k → ℕ) (hN : ∑ j, N j = 2^b)
    (f : Fin k → ℝ) : mean (fun coins => f (row N hN coins)) =
      ∑ j, (N j : ℝ) / (2^b : ℕ) * f j := by
  simpa only [mean, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using
    (exact_row N hN).2.2 f

theorem bit_path_mean_proof {S R : Type*} {k b : ℕ} (N : S → R → Fin k → ℕ)
    (hN : ∀ s r, ∑ j, N s r j = 2^b) (next : S → R → Fin k → S)
    (charge : S → R → Fin k → ℝ) (s : S) (w : List R) :
    mean (runCost N hN next charge s w) = rowCost (b:=b) N next charge s w := by
  induction w generalizing s with
  | nil => simp [mean, runCost, rowCost]
  | cons r w ih =>
    let e := Fin.consEquiv (fun _ : Fin (w.length+1) => Fin b → Bool)
    calc
      mean (runCost N hN next charge s (r::w)) =
          mean (fun p : (Fin b → Bool) × (Fin w.length → Fin b → Bool) =>
            charge s r (row (N s r) (hN s r) p.1) +
              runCost N hN next charge (next s r (row (N s r) (hN s r) p.1)) w p.2) := by
        have he := mean_equiv e (runCost N hN next charge s (r::w))
        simpa only [e, runCost, Fin.consEquiv, Equiv.coe_fn_mk,
          Fin.cons_zero, Fin.tail_cons] using he.symm
      _ = mean (fun coin : Fin b → Bool =>
          mean (fun rest : Fin w.length → Fin b → Bool =>
            charge s r (row (N s r) (hN s r) coin) +
              runCost N hN next charge (next s r (row (N s r) (hN s r) coin)) w rest)) := mean_prod _
      _ = mean (fun coin : Fin b → Bool =>
          charge s r (row (N s r) (hN s r) coin) +
            rowCost (b:=b) N next charge (next s r (row (N s r) (hN s r) coin)) w) := by
        congr 1
        funext coin
        rw [mean_add, mean_const, ih]
      _ = rowCost (b:=b) N next charge s (r::w) := by
        exact mean_row (N s r) (hN s r)
          (fun j => charge s r j + rowCost (b:=b) N next charge (next s r j) w)

-- The full finite tape has exactly b fresh unbiased bits per request.
theorem bit_path_mean {S R : Type*} {k b : ℕ} (N : S → R → Fin k → ℕ)
    (hN : ∀ s r, ∑ j, N s r j = 2^b) (next : S → R → Fin k → S)
    (charge : S → R → Fin k → ℝ) (s : S) (w : List R) :
    mean (runCost N hN next charge s w) = rowCost (b:=b) N next charge s w := by
  exact bit_path_mean_proof N hN next charge s w

end UniformKServer.BitSampling



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_Fallback
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer
namespace Fallback


theorem pick_mem {k : ℕ} (hk : 0 < k) (A : Finset (Fin k)) (hA : A.Nonempty) :
    pick hk A ∈ A := by
  simp only [pick, hA, ↓reduceDIte]
  exact A.min'_mem hA

end Fallback

end UniformKServer


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_EpochFinite
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawFilter.allCover_state _root_.OAI.UniformKServer.RawFilter.births_entry _root_.OAI.UniformKServer.RawFilter.cover_entry _root_.OAI.UniformKServer.RawGlobal.chosen_state _root_.OAI.UniformKServer.RawMarks.covers_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                  
section

namespace UniformKServer.EpochControl
open EpochShadow

theorem unpack_pack {n k M : ℕ} (s : {s : State n k // Bounded M s}) :
    unpack (pack s)=s.val := by
  have hl : ((s.val.filter.live.attach.map (fun e =>
      (e.val.position, (⟨e.val.moves,Nat.lt_succ_of_le (s.property.1.1 e.val e.property)⟩ : Fin (M+1))))).map
      (fun e => (⟨e.1,e.2.val⟩ : Entry n k))) = s.val.filter.live := by
    simp only [List.map_map]
    change s.val.filter.live.attach.map (fun e => e.val) = _
    simp
  simp only [pack,unpack,hl]

instance instFiniteSubtypeStateBounded {n k M : ℕ} : Finite {s : State n k // Bounded M s} := by
  apply Finite.of_injective (@pack n k M)
  intro s t h
  apply Subtype.ext
  rw [←unpack_pack s,←unpack_pack t,h]

end UniformKServer.EpochControl

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawMarks
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawFallback.endpoint_bits _root_.OAI.UniformKServer.RawFallback.nextSeen_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                               
section

namespace UniformKServer.RawMarks
open RawTyped

theorem length_bits {a : ℕ} (A : Finset (Fin a)) : (bits A).length=a := by simp [bits]

@[simp] theorem pick_bits {a : ℕ} (ha : 0<a) (A : Finset (Fin a)) :
    pick (bits A)=(Fallback.pick ha A).val := by
  by_cases h : A.Nonempty
  · let j:=A.min' h
    have hj : j.val<(bits A).length := by simp [length_bits]
    have hf : (bits A).findIdx id=j.val := by
      apply (List.findIdx_eq hj).mpr
      constructor
      · simpa [bits] using Finset.min'_mem A h
      · intro i hi
        simp only [bits,List.getElem_ofFn,id_eq,decide_eq_false_iff_not]
        intro hm
        have hh:=Finset.min'_le A (⟨i,lt_trans hi j.isLt⟩ : Fin a) hm
        exact (Nat.not_le_of_lt hi) hh
    simp only [pick,hf,ite_eq_left hj,Fallback.pick,dite_eq_left h,j]
  · have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst A
    have hf : (bits (∅ : Finset (Fin a))).findIdx id=a := by
      calc
        _ = (bits (∅ : Finset (Fin a))).length := List.findIdx_eq_length_of_false (by
          intro b hb
          simp [bits] at hb
          simp [hb])
        _ = a := length_bits _
    simp [pick,hf,length_bits,Fallback.pick]

end UniformKServer.RawMarks

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawFallback
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawControl.initial_state
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                  
section

namespace UniformKServer.RawFallback
open RawTyped RawMarks

@[simp] theorem choose_bits {n k : ℕ} (hk : 0<k) (c : Configuration n k)
    (A : Finset (Fin k)) (r : Fin n) :
    choose (config c) (bits A) r.val=(Fallback.choose hk ⟨c,A⟩ r).val := by
  simp only [choose,covers_bits,card_bits,Finset.card_pos,Bool.cond_decide,
    complement_bits,pick_bits hk,Fallback.choose]
  split_ifs <;> simp_all

@[simp] theorem label_bits {n k : ℕ} (hk : 0<k) (s : Fallback.RawState n k) (r : Fin n) :
    label k (config s.marking.position) (bits s.marking.marked) (bits s.seen) r.val=
      (Fallback.rawChoice hk s r).val := by
  by_cases he : Fallback.isEndpoint s r
  · have he' : k<(Insert.insert r s.seen).card := he
    simp only [label,endpoint_bits,Bool.cond_decide,ite_eq_left he',covers_bits,pick_bits hk,
      Fallback.rawChoice,ite_eq_left he]
  · have he' : ¬k<(Insert.insert r s.seen).card := he
    simp only [label,endpoint_bits,Bool.cond_decide,ite_eq_right he',choose_bits hk,
      Fallback.rawChoice,ite_eq_right he]

theorem step_bits {n k : ℕ} (hk : 0<k) (s : Fallback.RawState n k) (r : Fin n) :
    let j:=label k (config s.marking.position) (bits s.marking.marked) (bits s.seen) r.val
    ((config s.marking.position).set j r.val,
      nextMarked k (bits s.marking.marked) (bits s.seen) r.val j,
      nextSeen n k (bits s.seen) r.val)=
    (config (Fallback.rawStep hk s r).marking.position,
      bits (Fallback.rawStep hk s r).marking.marked,bits (Fallback.rawStep hk s r).seen) := by
  dsimp only
  rw [label_bits hk,config_set]
  by_cases he : Fallback.isEndpoint s r
  · have he' : k<(Insert.insert r s.seen).card := he
    simp only [nextMarked,nextSeen,endpoint_bits,Bool.cond_decide,ite_eq_left he',
      Fallback.rawStep,ite_eq_left he,empty_bits]
  · have he' : ¬k<(Insert.insert r s.seen).card := he
    simp only [nextMarked,nextSeen,endpoint_bits,Bool.cond_decide,ite_eq_right he',
      Fallback.rawStep,ite_eq_right he,Fallback.rawChoice,Fallback.step,insert_bits]

end UniformKServer.RawFallback

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PathExpansion
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

namespace UniformKServer.PathExpansion
variable {S R : Type*} {k b : ℕ}

theorem sum_cons {A : Type*} [AddCommMonoid A] (r : R) (w : List R)
    (f : List (R×Fin k)→A) :
    ((traces k (r::w)).map f).sum=
      ∑ j : Fin k,((traces k w).map fun h=>f ((r,j)::h)).sum := by
  simp [traces,List.map_flatten,List.map_ofFn,List.map_map,List.sum_flatten,List.sum_ofFn,Function.comp_def]

theorem sum_weight (N : S→R→Fin k→ℕ) (hN : ∀s r,∑j,N s r j=2^b)
    (next : S→R→Fin k→S) (s : S) (w : List R) :
    ((traces k w).map fun h=>weight N next s h).sum=(2^b)^w.length := by
  induction w generalizing s with
  | nil=>simp [traces,weight]
  | cons r w ih=>
    rw [sum_cons]
    simp only [weight,List.sum_map_mul_left,ih]
    rw [←Finset.sum_mul,hN]
    simp [pow_succ,mul_comm]

theorem sum_weight_cost (N : S→R→Fin k→ℕ) (hN : ∀s r,∑j,N s r j=2^b)
    (next : S→R→Fin k→S) (charge : S→R→Fin k→ℝ) (s : S) (w : List R) :
    ((traces k w).map fun h=>(weight N next s h:ℝ)*movement next charge s h).sum=
      ((2:ℝ)^b)^w.length*BitSampling.rowCost (b:=b) N next charge s w := by
  induction w generalizing s with
  | nil=>simp [traces,weight,movement,BitSampling.rowCost]
  | cons r w ih=>
    rw [sum_cons]
    have hcast (s : S) : ((traces k w).map fun h=>(weight N next s h:ℝ)).sum=((2:ℝ)^b)^w.length := by
      have h := congrArg (fun a : ℕ => (a:ℝ)) (sum_weight N hN next s w)
      simpa only [Nat.cast_list_sum,List.map_map,Function.comp_def,Nat.cast_pow,Nat.cast_ofNat] using h
    have hs (j : Fin k) :
        ((traces k w).map fun h=>(weight N next s ((r,j)::h):ℝ)*movement next charge s ((r,j)::h)).sum=
        (N s r j:ℝ)*(((2:ℝ)^b)^w.length*charge s r j+
          ((2:ℝ)^b)^w.length*BitSampling.rowCost (b:=b) N next charge (next s r j) w) := by
      simp only [weight,movement,Nat.cast_mul]
      have he (h : List (R×Fin k)) :
          (N s r j:ℝ)*(weight N next (next s r j) h:ℝ)*
            (charge s r j+movement next charge (next s r j) h)=
          ((N s r j:ℝ)*charge s r j)*(weight N next (next s r j) h:ℝ)+
            (N s r j:ℝ)*((weight N next (next s r j) h:ℝ)*movement next charge (next s r j) h) := by ring
      simp_rw [he]
      rw [List.sum_map_add,List.sum_map_mul_left,List.sum_map_mul_left,hcast,ih]
      ring
    simp_rw [hs]
    simp only [List.length_cons,pow_succ,BitSampling.rowCost,Nat.cast_pow,Nat.cast_ofNat]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hb : (2:ℝ)^b≠0 := by positivity
    field_simp

end UniformKServer.PathExpansion

end


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawExpansion
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
attribute [-simp] _root_.OAI.UniformKServer.Fallback.mem_coverers _root_.OAI.UniformKServer.RawBinary.distances_length _root_.OAI.UniformKServer.RawBinary.read_rationalCode _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawFallback.choose_bits _root_.OAI.UniformKServer.RawFallback.label_bits _root_.OAI.UniformKServer.RawMarks.covers_bits _root_.OAI.UniformKServer.RawMetric.present_eq _root_.OAI.UniformKServer.RawProgram.unpack_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

namespace UniformKServer.RawExpansion
open RawArithmetic RawWords RawTable RawPath RawTyped

theorem weight_eq {n k : ℕ} (T : List ℕ) (p : List (Fin n)) (c : Configuration n k) (h : History n k) :
    RawPath.weight T (requests p) (config c) (events h)=
      PathExpansion.weight (kernel T) next (p,c) h := by
  induction h generalizing p c with
  | nil=>rfl
  | cons rj h ih=>
    obtain ⟨r,j⟩:=rj
    simp only [events,List.map_cons,RawPath.weight,PathExpansion.weight,kernel,next,config_set]
    rw [←ih]
    simp [requests,events]

theorem movement_eq {n k : ℕ} (d : RationalMetric n) (draw : List Q)
    (hd : ∀x y : Fin n,value (dist n draw x.val y.val)=d.distance x y)
    (c : Configuration n k) (h : History n k) :
    (RawPath.movement n draw (config c) (events h):ℝ)=costAlong d c h := by
  induction h generalizing c with
  | nil=>simp [RawPath.movement,events,costAlong]
  | cons rj h ih=>
    obtain ⟨r,j⟩:=rj
    change ((value (dist n draw ((config c).getD j.val 0) r.val)+
      RawPath.movement n draw ((config c).set j.val r.val) (events h):ℚ):ℝ)=_
    push_cast
    rw [config_get,config_set,hd,ih]
    rfl

theorem path_movement_eq {n k : ℕ} (d : RationalMetric n) (p : List (Fin n))
    (c : Configuration n k) (h : History n k) :
    PathExpansion.movement next (charge d) (p,c) h=costAlong d c h := by
  induction h generalizing p c with
  | nil=>rfl
  | cons rj h ih=>
    obtain ⟨r,j⟩:=rj
    simp only [PathExpansion.movement,next,charge,costAlong,ih]

theorem histories_eq {n : ℕ} (k : ℕ) (w : List (Fin n)) :
    ((words k w.length).map fun g=>history (requests w) g)=
      (PathExpansion.traces k w).map events := by
  induction w with
  | nil=>simp [words,PathExpansion.traces,requests,history,events]
  | cons r w ih=>
    simp only [List.length_cons,words,requests,List.map_cons,PathExpansion.traces,
      List.map_flatMap,List.map_map,Function.comp_def,history_cons,List.map_flatten,List.map_ofFn]
    rw [range_eq_ofFn]
    rw [List.flatMap_def]
    simp only [List.map_ofFn]
    congr 1
    apply congrArg List.ofFn
    funext j
    have he:=congrArg (List.map ((r.val,j.val)::·)) ih
    simpa only [List.map_map,Function.comp_def,events,List.map_cons,requests] using he

theorem total_eq {n k : ℕ} (d : RationalMetric n) (draw : List Q)
    (hd : ∀x y : Fin n,value (dist n draw x.val y.val)=d.distance x y)
    (T : List ℕ) (p : List (Fin n)) (c : Configuration n k) (w : List (Fin n)) :
    (value (total n k draw T (requests p) (config c) (requests w)):ℝ)=
      ((PathExpansion.traces k w).map fun h=>
        (PathExpansion.weight (kernel T) next (p,c) h:ℝ)*
          PathExpansion.movement next (charge d) (p,c) h).sum := by
  rw [total_value]
  have he:=congrArg (List.map (fun h=>(RawPath.weight T (requests p) (config c) h:ℚ)*
    RawPath.movement n draw (config c) h)) (histories_eq k w)
  simp only [List.map_map,Function.comp_def] at he
  have hl : (requests w).length=w.length := by simp [requests]
  rw [hl,he]
  have hsum (xs : List ℚ) : (xs.sum:ℝ)=(xs.map fun q : ℚ =>(q:ℝ)).sum :=
    map_list_sum (Rat.castHom ℝ) xs
  rw [hsum]
  congr 1
  simp only [List.map_map,Function.comp_def,Rat.cast_mul,Rat.cast_natCast,
    weight_eq,movement_eq d draw hd,←path_movement_eq d p c]

end UniformKServer.RawExpansion

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawFilter
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawFallback.choose_bits _root_.OAI.UniformKServer.RawFallback.label_bits _root_.OAI.UniformKServer.RawMarks.covers_bits _root_.OAI.UniformKServer.RawProgram.unpack_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                
section

namespace UniformKServer.RawFilter
open RawTyped

@[simp] theorem expand_entry {n k : ℕ} (M : ℕ) (r : Fin n) (e : UniformKServer.Entry n k) :
    expand k M r.val (entry e)=(UniformKServer.expand M r e).map entry := by
  rw [expand,cover_entry]
  simp only [Bool.cond_decide,UniformKServer.expand]
  change (if Covers e r then [entry e] else
    if e.moves<M then (List.range k).map (fun j=>(config e.position |>.set j r.val,e.moves+1)) else []) = _
  split_ifs with hcov hm
  · rfl
  · simp only [List.map_map]
    rw [RawExpansion.range_eq_ofFn, List.map_ofFn, ←List.ofFn_eq_map]
    apply congrArg List.ofFn
    funext j
    simp only [Function.comp_apply,entry,config_set]
    rfl
  · rfl

@[simp] theorem step_state {n k : ℕ} (M : ℕ) (s : UniformKServer.FilterState n k) (r : Fin n) :
    step k M (state s) r.val=state (UniformKServer.step M s r) := by
  simp only [step,allCover_state,Bool.cond_decide,UniformKServer.step]
  split_ifs with h
  · rfl
  · simp only [state,List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def,
      expand_entry,births_entry,requests,List.map_append,List.map_cons,List.map_nil]

end UniformKServer.RawFilter

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawRowSelect
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawFallback.choose_bits _root_.OAI.UniformKServer.RawFallback.label_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                   
section

namespace UniformKServer.RawRowSelect
open RawTyped RawTable

theorem partialMass_succ (T p c : List ℕ) (r j : ℕ) :
    partialMass T p c r (j+1)=partialMass T p c r j+entry T p c r j := by
  simp [partialMass,List.range_succ,List.map_append,List.sum_append]

theorem partialMass_mono (T p c : List ℕ) (r : ℕ) : Monotone (partialMass T p c r) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [partialMass_succ]
  omega

theorem partialMass_cumulative {n k : ℕ} (T : List ℕ) (p : List (Fin n))
    (c : Configuration n k) (r : Fin n) (N : Fin k→ℕ)
    (hrep : ∀j,entry T (requests p) (config c) r.val j.val=N j) (j : Fin k) :
    partialMass T (requests p) (config c) r.val j.val=BitSampling.cumulative N j := by
  rw [partialMass,RawExpansion.range_eq_ofFn,List.map_ofFn,List.sum_ofFn]
  unfold BitSampling.cumulative
  apply Finset.sum_congr rfl
  intro i hi
  exact hrep (Fin.castLE j.isLt.le i)

theorem choose_eq {n k b : ℕ} (T : List ℕ) (p : List (Fin n))
    (c : Configuration n k) (r : Fin n) (N : Fin k→ℕ)
    (hrep : ∀j,entry T (requests p) (config c) r.val j.val=N j)
    (hN : ∑j,N j=2^b) (coins : Fin b→Bool) :
    choose k T (requests p) (config c) r.val (BitSampling.bitsEquiv b coins).val=
      (BitSampling.row N hN coins).val := by
  let j:=BitSampling.row N hN coins
  let a:=(BitSampling.bitsEquiv b coins).val
  let A:=(List.range k).map (fun i=>decide (a<partialMass T (requests p) (config c) r.val (i+1)))
  have hj : j.val<A.length := by simp [A]
  have hp:= (BitSampling.exact_row_proof N hN).2.1 coins
  have he:=partialMass_cumulative T p c r N hrep j
  have hf : A.findIdx id=j.val := by
    apply (List.findIdx_eq hj).mpr
    constructor
    · have hu : a<partialMass T (requests p) (config c) r.val (j.val+1) := by
        rw [partialMass_succ,he,hrep]
        exact hp.2
      simpa [A] using hu
    · intro i hi
      have hu : partialMass T (requests p) (config c) r.val (i+1)≤a :=
        (partialMass_mono T (requests p) (config c) r.val (by omega : i+1≤j.val)).trans (he ▸ hp.1)
      simpa [A] using Nat.not_lt_of_ge hu
  change RawMarks.pick A=j.val
  simp only [RawMarks.pick,hf,ite_eq_left hj]

end UniformKServer.RawRowSelect

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawControl
attribute [-instance] _root_.OAI.UniformKServer.EpochControl.instFiniteSubtypeStateBounded _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawProgram.unpack_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                 
section

namespace UniformKServer.RawControl
open RawTyped RawMarks

@[simp] theorem nextEntry_state {n k : ℕ} (e : Entry n k) (r : Fin n) (j : Fin k) :
    nextEntry (RawFilter.entry e) r.val j.val=RawFilter.entry (EpochShadow.nextEntry e r j) := by
  simp only [nextEntry,RawFilter.entry,config_set,config_get,Bool.cond_decide,
    EpochShadow.nextEntry,Fin.ext_iff]

/-- Local representation lemma: only the current causal selector value is needed. -/
theorem label_state {n k : ℕ} (hk : 0<k) (T coins : List ℕ) (U : EpochShadow.Selector n k)
    (s : EpochControl.State n k) (r : Fin n)
    (hselect : trackingLabel k T coins (state s) r.val=(U s.filter.kept s.virtual.position r).val) :
    label k T coins (state s) r.val=(EpochControl.label hk U s r).val := by
  have hf:=RawFallback.label_bits hk (EpochControl.asRaw s) r
  simp only [EpochControl.asRaw] at hf
  simp only [label,state,RawFilter.entry,RawFilter.allCover_state,hf,
    RawMarks.covers_bits,RawMarks.pick_bits hk,Bool.cond_eq_ite,decide_eq_true_eq,
    EpochControl.label]
  change (if s.fallback=true then _ else if ∀z∈s.filter.live,Covers z r then _ else
    trackingLabel k T coins (state s) r.val)=_
  rw [hselect]
  split_ifs <;> rfl

theorem step_state {n k : ℕ} (hk : 0<k) (M : ℕ) (T coins : List ℕ) (U : EpochShadow.Selector n k)
    (s : EpochControl.State n k) (r : Fin n)
    (hselect : trackingLabel k T coins (state s) r.val=(U s.filter.kept s.virtual.position r).val) :
    step n k M T coins (state s) r.val=state (EpochControl.step hk M U s r) := by
  have hf:=RawFallback.step_bits hk (EpochControl.asRaw s) r
  simp only [EpochControl.asRaw] at hf
  by_cases hb : s.fallback=true
  · simp only [step,state,RawFilter.entry,hb,Bool.cond_true,EpochControl.step,
      RawFilter.step_state,ite_true, if_true]
    have hp:=congrArg Prod.fst hf
    have hm:=congrArg (fun x=>x.2.1) hf
    have hs:=congrArg (fun x=>x.2.2) hf
    dsimp only at hp hm hs
    rw [hp,hm,hs]
    rfl
  · have hb' : s.fallback=false := Bool.eq_false_iff.mpr hb
    by_cases hc : ∀z∈s.filter.live,Covers z r
    · simp only [step,state,RawFilter.allCover_state,RawFilter.entry,hb',Bool.cond_false,
        Bool.cond_decide,ite_eq_left hc,EpochControl.step,RawFallback.nextSeen_bits,Bool.false_eq_true,ite_false, if_false]
    · simp only [step,EpochControl.step,state,RawFilter.entry,RawFilter.allCover_state,hb',
        Bool.cond_false,Bool.cond_decide,ite_eq_right hc,Bool.false_eq_true,ite_false, if_false]
      change (RawFilter.step k M (RawFilter.state s.filter) r.val,
        nextEntry (RawFilter.entry s.virtual) r.val (trackingLabel k T coins (state s) r.val),
        empty k,RawFallback.nextSeen n k (bits s.seen) r.val,
        decide (M<(nextEntry (RawFilter.entry s.virtual) r.val
          (trackingLabel k T coins (state s) r.val)).2)) = _
      rw [hselect,RawFilter.step_state,nextEntry_state,empty_bits,RawFallback.nextSeen_bits]
      rfl

end UniformKServer.RawControl

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawTape
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawGlobal.chosen_state
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                              
section

namespace UniformKServer.RawTape
open RawTyped

theorem zeros (b : ℕ) : (BitSampling.bitsEquiv b (fun _=>false)).val=0 := by
  simp [BitSampling.bitsEquiv,Equiv.trans_apply,finPiFinEquiv_apply,finTwoEquiv]

theorem get_tape {H b : ℕ} (coins : Fin H→Fin b→Bool) (t : ℕ) :
    (tape coins).getD t 0=(BitSampling.bitsEquiv b (EpochExpectation.extend coins t)).val := by
  by_cases h : t<H
  · simp [tape,EpochExpectation.extend,h]
  · rw [List.getD_eq_default _ _ (by simpa [tape] using Nat.le_of_not_gt h)]
    simp [EpochExpectation.extend,h,zeros]

theorem tracking {n k M b : ℕ} (hk : 0<k) (T : List ℕ)
    (hT : RawCertificate.rowsOK n k (horizon k M) b T=true)
    (s : EpochControl.State n k) (hs : EpochControl.Bounded M s) (r : Fin n)
    (coins : Fin (horizon k M)→Fin b→Bool) :
    RawControl.trackingLabel k T (tape coins) (RawControl.state s) r.val=
      (EpochExpectation.selector (RawRows.complete hk (horizon k M) b T)
        (RawRows.total hk hT) (EpochExpectation.extend coins) s.filter.kept s.virtual.position r).val := by
  have hp : s.filter.kept.length≤horizon k M := by
    have h₁:=hs.1.2.1
    have h₂:=hs.1.2.2
    omega
  unfold RawControl.trackingLabel
  simp only [RawControl.state,RawFilter.state,RawFilter.entry,requests,List.length_map,get_tape]
  exact RawRowSelect.choose_eq T s.filter.kept s.virtual.position r
    (RawRows.complete hk (horizon k M) b T (s.filter.kept,s.virtual.position) r)
    (by intro j;simp only [RawRows.complete,ite_eq_left hp,RawExpansion.kernel])
    (RawRows.total hk hT _ _) _

end UniformKServer.RawTape

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TapeController
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawGlobal.boundary_state _root_.OAI.UniformKServer.RawGlobal.chosen_state
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                     
section

namespace UniformKServer.TapeController
open EpochShadow EpochExpectation

instance instFiniteState {n k M R b : ℕ} : Finite (State n k M R b) := by
  let f : State n k M R b → {s : EpochControl.State n k // EpochControl.Bounded M s} ×
      Fin R × Option (Tape k M b) := fun s => (s.localState,s.completed,s.tape)
  apply Finite.of_injective f
  intro a b h
  cases a;cases b
  simp_all [f]

end UniformKServer.TapeController

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawGlobal
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawProgram.unpack_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                
section

namespace UniformKServer.RawGlobal
open RawTyped

@[simp] theorem label_state {n k M R b : ℕ} (hk : 0<k) (T : List ℕ)
    (hT : RawCertificate.rowsOK n k (horizon k M) b T=true)
    (s : TapeController.State n k M R b) (r : Fin n) (fresh : TapeController.Tape k M b) :
    label k T (state s) r.val (RawTape.tape fresh)=
      (TapeController.choose hk (RawRows.complete hk (horizon k M) b T) (RawRows.total hk hT) s r fresh).val := by
  simp only [label,chosen_state]
  apply RawControl.label_state
  exact RawTape.tracking hk T hT s.localState.val s.localState.property r _

@[simp] theorem step_state {n k M R b : ℕ} (hk : 0<k) (hkn : k≤n) (hR : 0<R) (T : List ℕ)
    (hT : RawCertificate.rowsOK n k (horizon k M) b T=true)
    (s : TapeController.State n k M R b) (r : Fin n) (fresh : TapeController.Tape k M b) :
    step n k M R T (state s) r.val (RawTape.tape fresh)=
      state (TapeController.step hk hR (fun j : Fin k=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩)
        (RawRows.complete hk (horizon k M) b T) (RawRows.total hk hT) s r fresh) := by
  simp only [step,boundary_state,Bool.cond_decide,TapeController.step]
  by_cases h : TapeController.boundary s r
  · simp only [ite_eq_left h,dite_eq_left h]
    exact initial_state hkn hR
  · simp only [ite_eq_right h,dite_eq_right h]
    rw [chosen_state]
    have hh:=RawControl.step_state hk M T (RawTape.tape (TapeController.chosen s fresh))
      (EpochExpectation.selector (RawRows.complete hk (horizon k M) b T) (RawRows.total hk hT)
        (EpochExpectation.extend (TapeController.chosen s fresh))) s.localState.val r
      (RawTape.tracking hk T hT s.localState.val s.localState.property r _)
    change (RawControl.step n k M T _ (RawControl.state s.localState.val) r.val,_,_)=_
    rw [hh]
    simp only [state,RawControl.state,RawFallback.endpoint_bits,Bool.cond_decide,Option.map_some,
      EpochControl.boundedStep]

end UniformKServer.RawGlobal

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawProgram
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                 
section

namespace UniformKServer.RawProgram
open Primrec RawCertificate
attribute [fun_prop] RawBits.primitive_bits

@[simp] theorem request_code (r : ℕ) :
    request (RawBinary.value (natCode (r+1)++[true]))=r := by
  simp only [request,RawBits.bits_value,RawBinary.read_natCode,Nat.add_sub_cancel]

end UniformKServer.RawProgram

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_BinaryTape
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                 
section

namespace UniformKServer.BinaryTape
open RawBinary

 theorem value_sum {b : ℕ} (v : Fin b→Bool) :
    value (List.ofFn v)=∑i : Fin b,(if v i then 1 else 0)*2^i.val := by
  induction b with
  | zero=>simp [value]
  | succ b ih=>
    rw [List.ofFn_succ,RawBinary.value_cons,Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,mul_one,Fin.val_succ,pow_succ]
    rw [ih]
    simp_rw [←Nat.mul_assoc,←Finset.sum_mul]
    cases v 0 <;> simp only [Nat.bit_val,Bool.toNat_false,Bool.toNat_true,
      Bool.false_eq_true,ite_false, if_false,ite_true, if_true] <;> omega

 theorem bits_value {b : ℕ} (v : Fin b→Bool) :
    (BitSampling.bitsEquiv b v).val=value (List.ofFn v) := by
  rw [value_sum]
  simp only [BitSampling.bitsEquiv,Equiv.trans_apply,finPiFinEquiv_apply,
    finCongr_apply,Fin.val_cast,Equiv.piCongrRight_apply,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  cases h:v i <;> simp [finTwoEquiv,h]

 theorem value_pad (b : ℕ) (w : List Bool) :
    value (List.ofFn (fun i : Fin b=>w.getD i.val false))=value (w.take b) := by
  induction b generalizing w with
  | zero=>rfl
  | succ b ih=>
    cases w with
    | nil=>
      simp only [List.getD_nil,List.take_nil,List.ofFn_succ,RawBinary.value_cons]
      have hh:=ih []
      simp only [List.getD_nil,List.take_nil] at hh
      rw [hh]
      rfl
    | cons a w=>
      simp only [List.ofFn_succ,Fin.val_zero,List.getD_cons_zero,Fin.val_succ,List.getD_cons_succ,
        List.take_succ_cons,RawBinary.value_cons]
      rw [ih]

 theorem fresh_eq (k M b a : ℕ) :
    RawProgram.fresh k M b a=RawTape.tape (coins k M b a) := by
  unfold RawProgram.fresh
  rw [RawMetric.horizon_eq,RawExpansion.range_eq_ofFn]
  simp only [List.map_ofFn,RawTape.tape]
  apply List.ofFn_inj.mpr
  funext i
  rw [bits_value]
  change value ((a.bits.drop (b*i.val)).take b)=
    value (List.ofFn (fun j : Fin b=>(a.bits.drop (b*i.val)).getD j.val false))
  exact (value_pad b _).symm

end UniformKServer.BinaryTape

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_DyadicRows
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer

theorem rowLoss_bounds {k : ℕ} (q : Fin k → ℝ)
    (hq : ∀ j, 0 ≤ q j) (j₀ : Fin k) (B : ℕ) (hB : 0 < B) :
    0 ≤ rowLoss q j₀ B ∧ rowLoss q j₀ B ≤ k / (B : ℝ) := by
  classical
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  refine ⟨Finset.sum_nonneg (fun j _ => sub_nonneg.mpr
    (floor_fraction_bounds q hq B hB j).2.1), ?_⟩
  calc
    rowLoss q j₀ B ≤ ∑ _i ∈ Finset.univ.erase j₀, (1 : ℝ) / B :=
      Finset.sum_le_sum (fun i _ => (floor_fraction_bounds q hq B hB i).2.2)
    _ ≤ ∑ _i : Fin k, (1 : ℝ) / B :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun _ _ _ => div_nonneg (by norm_num) (le_of_lt hb))
    _ = k / (B : ℝ) := by simp [div_eq_mul_inv]

theorem round_reserve {k : ℕ} (q : Fin k → ℝ)
    (hs : ∑ j, q j = 1) (j₀ : Fin k) (B : ℕ) :
    roundedRow q j₀ B j₀ = q j₀ + rowLoss q j₀ B := by
  classical
  have ht := Finset.sum_erase_add Finset.univ q (Finset.mem_univ j₀)
  rw [hs] at ht
  simp only [roundedRow, ↓reduceIte, rowLoss, Finset.sum_sub_distrib]
  linarith

theorem round_row_expectation {k : ℕ} (q : Fin k → ℝ)
    (hq : ∀ j, 0 ≤ q j) (hs : ∑ j, q j = 1) (j₀ : Fin k)
    (B : ℕ) (hB : 0 < B) (v : Fin k → ℝ) (T : ℝ)
    (hv : ∀ j, 0 ≤ v j ∧ v j ≤ T) :
    (∑ j, roundedRow q j₀ B j * v j) ≤
      (∑ j, q j * v j) + k / (B : ℝ) * T := by
  classical
  have hothers : (∑ i ∈ Finset.univ.erase j₀, roundedRow q j₀ B i * v i) ≤
      ∑ i ∈ Finset.univ.erase j₀, q i * v i := by
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_right _ (hv i).1
    simpa [roundedRow, Finset.ne_of_mem_erase hi] using
      (floor_fraction_bounds q hq B hB i).2.1
  have hsum := Finset.sum_erase_add Finset.univ (fun i => q i * v i)
    (Finset.mem_univ j₀)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j₀), round_reserve q hs]
  have hl := rowLoss_bounds q hq j₀ B hB
  have hlt := mul_le_mul_of_nonneg_left (hv j₀).2 hl.1
  have hT : 0 ≤ T := le_trans (hv j₀).1 (hv j₀).2
  have hlt' := mul_le_mul_of_nonneg_right hl.2 hT
  nlinarith


end UniformKServer




end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ExecutableDyadic
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.ExecutableDyadic

theorem rationalCost_cast {S R : Type*} {k : ℕ} (q : S → R → Fin k → ℚ)
    (next : S → R → Fin k → S) (charge : S → R → Fin k → ℚ)
    (s : S) (r : R) (w : List R) :
    (rationalCost q next charge s (r::w) : ℝ) =
      ∑ j, (q s r j : ℝ) * ((charge s r j : ℝ) +
        (rationalCost q next charge (next s r j) w : ℝ)) := by
  simp only [rationalCost, Rat.cast_sum, Rat.cast_mul, Rat.cast_add]

theorem rationalCost_bounds {S R : Type*} {k : ℕ} (q : S → R → Fin k → ℚ)
    (hq : ∀ s r j, 0 ≤ q s r j) (hs : ∀ s r, ∑ j, q s r j = 1)
    (next : S → R → Fin k → S) (charge : S → R → Fin k → ℚ)
    (hn : ∀ s r j, 0 ≤ charge s r j) (D : ℝ)
    (hd : ∀ s r j, (charge s r j : ℝ) ≤ D) (s : S) (w : List R) :
    0 ≤ (rationalCost q next charge s w : ℝ) ∧
      (rationalCost q next charge s w : ℝ) ≤ w.length * D := by
  induction w generalizing s with
  | nil => simp [rationalCost]
  | cons r w ih =>
    rw [rationalCost_cast]
    have hqr (j : Fin k) : (0 : ℝ) ≤ q s r j := by exact_mod_cast hq s r j
    have hnr (j : Fin k) : (0 : ℝ) ≤ charge s r j := by exact_mod_cast hn s r j
    have hsr : ∑ j, (q s r j : ℝ) = 1 := by exact_mod_cast hs s r
    constructor
    · exact Finset.sum_nonneg (fun j _ => mul_nonneg (hqr j)
        (add_nonneg (hnr j) (ih (next s r j)).1))
    · calc
        _ ≤ ∑ j, (q s r j : ℝ) * (((w.length : ℝ) + 1) * D) := by
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul_of_nonneg_left _ (hqr j)
          have := hd s r j
          have := (ih (next s r j)).2
          nlinarith
        _ = _ := by rw [← Finset.sum_mul, hsr]; simp

theorem rowCost_bound {S R : Type*} {k : ℕ}
    (q : S → R → Fin k → ℚ) (hq : ∀ s r j, 0 ≤ q s r j)
    (hs : ∀ s r, ∑ j, q s r j = 1) (reserve : S → R → Fin k)
    (b : ℕ) (next : S → R → Fin k → S) (charge : S → R → Fin k → ℚ)
    (hn : ∀ s r j, 0 ≤ charge s r j) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ s r j, (charge s r j : ℝ) ≤ D) (s : S) (w : List R) :
    BitSampling.rowCost (b:=b) (fun s r => numerators (q s r) (reserve s r) (2^b))
      next (fun s r j => (charge s r j : ℝ)) s w ≤
        (rationalCost q next charge s w : ℝ) +
          (k : ℝ) * (w.length : ℝ)^2 / ((2^b : ℕ) : ℝ) * D := by
  let N := fun s r => numerators (q s r) (reserve s r) (2^b)
  have hB : 0 < 2^b := by positivity
  have hb : (0 : ℝ) < (2^b : ℕ) := by exact_mod_cast hB
  have hqr (s : S) (r : R) (j : Fin k) : (0 : ℝ) ≤ q s r j := by
    exact_mod_cast hq s r j
  have hsr (s : S) (r : R) : ∑ j, (q s r j : ℝ) = 1 := by
    exact_mod_cast hs s r
  have hrepr (s : S) (r : R) (j : Fin k) : (N s r j : ℝ) / (2^b : ℕ) =
      roundedRow (fun j => (q s r j : ℝ)) (reserve s r) (2^b) j :=
    numerators_repr (q s r) (hq s r) (hs s r) (reserve s r) (2^b) hB j
  have hnt (s : S) (r : R) : ∑ j, (N s r j : ℝ) / (2^b : ℕ) = 1 := by
    simp only [hrepr, round_row_sum]
  have hnn (s : S) (r : R) (j : Fin k) : (0 : ℝ) ≤ (N s r j : ℝ) / (2^b : ℕ) :=
    div_nonneg (Nat.cast_nonneg _) hb.le
  change BitSampling.rowCost (b:=b) N next _ s w ≤ _
  induction w generalizing s with
  | nil => simp [BitSampling.rowCost, rationalCost]
  | cons r w ih =>
    let v : Fin k → ℝ := fun j => (charge s r j : ℝ) +
      (rationalCost q next charge (next s r j) w : ℝ)
    let err : ℝ := (k : ℝ) * (w.length : ℝ)^2 / (2^b : ℕ) * D
    have hv (j : Fin k) : 0 ≤ v j ∧ v j ≤ ((w.length : ℝ) + 1) * D := by
      have hl := rationalCost_bounds q hq hs next charge hn D hd (next s r j) w
      have hn' : (0 : ℝ) ≤ charge s r j := by exact_mod_cast hn s r j
      have hu := hd s r j
      dsimp [v]
      constructor <;> nlinarith [hl.1, hl.2]
    have next_le : BitSampling.rowCost (b:=b) N next (fun s r j => (charge s r j : ℝ))
        s (r::w) ≤ (∑ j, (N s r j : ℝ) / (2^b : ℕ) * v j) + err := by
      rw [BitSampling.rowCost]
      calc
        _ ≤ ∑ j, (N s r j : ℝ) / (2^b : ℕ) * (v j + err) := by
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul_of_nonneg_left _ (hnn s r j)
          have ht := ih (next s r j)
          dsimp [v, err]
          linarith
        _ = _ := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hnt, one_mul]
    have local_le := round_row_expectation (fun j => (q s r j : ℝ)) (hqr s r)
      (hsr s r) (reserve s r) (2^b) hB v (((w.length : ℝ) + 1) * D) hv
    simp only [← hrepr s r] at local_le
    have combo : BitSampling.rowCost (b:=b) N next (fun s r j => (charge s r j : ℝ))
        s (r::w) ≤ (rationalCost q next charge s (r::w) : ℝ) +
          k / ((2^b : ℕ) : ℝ) * (((w.length : ℝ) + 1) * D) + err := by
      rw [rationalCost_cast]
      change BitSampling.rowCost (b:=b) N next _ s (r::w) ≤
        (∑ j, (q s r j : ℝ) * v j) + _ + err
      linarith
    have heps : 0 ≤ (k : ℝ) / (2^b : ℕ) * D :=
      mul_nonneg (div_nonneg (Nat.cast_nonneg _) hb.le) hD
    have hm : 0 ≤ (w.length : ℝ) := Nat.cast_nonneg _
    have inc : k / ((2^b : ℕ) : ℝ) * (((w.length : ℝ) + 1) * D) + err ≤
        (k : ℝ) * ((r :: w).length : ℝ)^2 / (2^b : ℕ) * D := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one, err]
      have hp := mul_nonneg heps hm
      calc
        _ ≤ k / ((2^b : ℕ) : ℝ) * (((w.length : ℝ) + 1) * D) +
            (k : ℝ) * (w.length : ℝ)^2 / (2^b : ℕ) * D +
            k / ((2^b : ℕ) : ℝ) * D * (w.length : ℝ) := le_add_of_nonneg_right hp
        _ = _ := by ring
    exact combo.trans (by linarith)

/-- Exact executable downward rounding and finite-bit realization, with the
source's full-horizon error bound; every history/state is included. -/
theorem finite_bit_perturbation {S R : Type*} {k : ℕ}
    (q : S → R → Fin k → ℚ) (hq : ∀ s r j, 0 ≤ q s r j)
    (hs : ∀ s r, ∑ j, q s r j = 1) (reserve : S → R → Fin k)
    (b : ℕ) (next : S → R → Fin k → S) (charge : S → R → Fin k → ℚ)
    (hn : ∀ s r j, 0 ≤ charge s r j) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ s r j, (charge s r j : ℝ) ≤ D) :
    ∃ hN : ∀ s r, ∑ j, numerators (q s r) (reserve s r) (2^b) j = 2^b,
      (∀ s r j, j ≠ reserve s r → q s r j = 0 →
        numerators (q s r) (reserve s r) (2^b) j = 0) ∧
      (∀ s w, BitSampling.mean
        (BitSampling.runCost (fun s r => numerators (q s r) (reserve s r) (2^b))
          hN next (fun s r j => (charge s r j : ℝ)) s w) ≤
        (rationalCost q next charge s w : ℝ) +
          (k : ℝ) * (w.length : ℝ)^2 / ((2^b : ℕ) : ℝ) * D) := by
  have hN (s : S) (r : R) := numerators_sum (q s r) (hq s r) (hs s r)
    (reserve s r) (2^b) (by positivity)
  refine ⟨hN, ?_, ?_⟩
  · intro s r j hj hz
    simp [numerators, hj, hz]
  · intro s w
    rw [BitSampling.bit_path_mean]
    exact rowCost_bound q hq hs reserve b next charge hn D hD hd s w
end UniformKServer.ExecutableDyadic



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OffsetTable
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                  
section

namespace UniformKServer.OffsetTable
open EffectiveLP
open OffsetLP

theorem error_bound {k H h : ℕ} (hh : h ≤ H) (D : ℝ) (hD : 0 ≤ D) :
    (k : ℝ) * (h : ℝ)^2 / ((2^(bitWidth k H) : ℕ) : ℝ) * D ≤ D := by
  have hb : (0 : ℝ) < (2^(bitWidth k H) : ℕ) := by positivity
  have hle : k * h^2 ≤ 2^(bitWidth k H) :=
    (Nat.mul_le_mul_left k (Nat.pow_le_pow_left hh 2)).trans (Nat.le_pow_clog (by omega) _)
  have hle' : (k : ℝ) * (h : ℝ)^2 ≤ (2^(bitWidth k H) : ℕ) := by exact_mod_cast hle
  have := mul_le_mul_of_nonneg_right ((div_le_one hb).mpr hle') hD
  simpa using this

/-- Total deterministic construction, exact-bit legal realization, and the
finite-word inequality of source Proposition finite-table. The sharp coefficient
is deliberately exposed as optimization against real feasible flows, not assumed
from an unproved companion theorem. -/
theorem construct {n k : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) (A : ℚ)
    (H : ℕ) (hv : OffsetLP.Valid d u A (flow (H:=H) d u A) (offset d u A H)) (D : ℝ) (hD : 0 ≤ D) (hd : ∀ x y, (d.distance x y : ℝ) ≤ D) :
    (k * H^2 ≤ 2^(bitWidth k H)) ∧
    (∀ b, k * H^2 ≤ 2^b → bitWidth k H ≤ b) ∧
    ∃ hN : ∀ s r, ∑ j, counts d u A H s r j = 2^(bitWidth k H),
      (∀ s r coins, BitSampling.row (counts d u A H s r) (hN s r) coins ∈ labels s.2 r) ∧
      (∀ w : List (Fin n), w.length ≤ H →
        BitSampling.mean (BitSampling.runCost (counts d u A H) hN next
          (fun s r j => (charge d s r j : ℝ)) ([],u) w) ≤
          (A : ℝ) * offlineCost d u.val w + (offset d u A H : ℝ) + D) := by
  obtain ⟨hn,hs,hp,hc⟩ := row_facts d u A H hv
  obtain ⟨hN,hz,he⟩ := ExecutableDyadic.finite_bit_perturbation (qrow d u A H) hn hs
    (fun s r => FiniteTable.fallback s.2 r) (bitWidth k H) next (charge d)
    (fun s r j => d.nonneg (s.2.val j) r) D hD (fun s r j => hd (s.2.val j) r)
  refine ⟨Nat.le_pow_clog (by omega) _, fun b hb => (Nat.clog_le_iff_le_pow (by omega)).mpr hb,
    hN, ?_, ?_⟩
  · intro s r coins
    by_contra hbad
    have hj : BitSampling.row (counts d u A H s r) (hN s r) coins ≠ FiniteTable.fallback s.2 r := by
      intro heq
      exact hbad (heq ▸ FiniteTable.fallback_mem s.2 r)
    have hzero := hz s r _ hj (hp s r _ hbad)
    have hpositive := (BitSampling.exact_row (counts d u A H s r) (hN s r)).1 coins
    change 0 < ExecutableDyadic.numerators _ _ _ _ at hpositive
    rw [hzero] at hpositive
    omega
  · intro w hw
    have hce : (ExecutableDyadic.rationalCost (qrow d u A H) next (charge d) ([],u) w : ℝ) ≤
        (A : ℝ) * (OfflineDynamic.optRat d u.val w : ℝ)+(offset d u A H : ℝ) := by
      exact_mod_cast hc w hw
    rw [OfflineDynamic.offline_eq_optRat]
    exact (he ([],u) w).trans (add_le_add hce (error_bound hw D hD))

end UniformKServer.OffsetTable

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OffsetParameters
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                       
section

/-! Terminating rational search for the restart length. The uniform finite-law
endpoint is used only to prove termination, never supplied to the constructor. -/
namespace UniformKServer.OffsetParameters
open EffectiveLP ComputedInstance
variable {n k : ℕ} [NeZero k]

theorem restart_spec (hn : 2 ≤ n) (hk : 2 ≤ k) (d : RationalMetric n)
    (u : Config n k) (A : ℚ)
    (hA : PartitionTree.absoluteRate*(Real.log (k+1))^2 ≤ (A : ℝ)) :
    acceptable hn d u A (restart hn hk d u A hA) := Nat.find_spec _

theorem cap_bound (hn : 2 ≤ n) (d : RationalMetric n) (R : ℕ) :
    (R:ℝ)*(k+1)*(diameter hn d : ℝ) ≤
      ((cap (k:=k) hn d R : ℝ)+1)*(separation hn d : ℝ) := by
  have hs : 0 < separation hn d := by
    exact_mod_cast (ComputedInstance.parameters hn (NeZero.pos k) d).2.1
  have hb : (R:ℚ)*(k+1)*diameter hn d ≤
      (cap (k:=k) hn d R : ℚ)*separation hn d := (div_le_iff₀ hs).mp (Nat.le_ceil _)
  have hb' : (R:ℚ)*(k+1)*diameter hn d ≤
      ((cap (k:=k) hn d R : ℚ)+1)*separation hn d := by nlinarith
  exact_mod_cast hb'

end UniformKServer.OffsetParameters

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OffsetEpoch
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
attribute [-simp] _root_.OAI.UniformKServer.RawBinary.distances_length _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawFallback.choose_bits _root_.OAI.UniformKServer.RawMarks.covers_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                  
section

namespace UniformKServer.OffsetEpoch
open EffectiveLP

theorem base_covers {n k : ℕ} [NeZero k] (c : Configuration n k) (r : Fin n)
    (h : ∃ j, c j = r) : c (baseLabel c r) = r := by
  apply (Fallback.mem_coverers _ _ _).mp
  apply Fallback.pick_mem
  obtain ⟨j,hj⟩ := h
  exact ⟨j,(Fallback.mem_coverers _ _ _).mpr hj⟩

theorem forbidden {n k : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) (A : ℚ) (H : ℕ) (hv : OffsetLP.Valid d u A (OffsetTable.flow (H:=H) d u A) (OffsetTable.offset d u A H)) :
    ∀ s r j, (∃ i, s.2 i = r) → s.2 j ≠ r → counts d u A H s r j = 0 := by
  intro s r j hhit hbad
  by_cases hc : Function.Injective s.2
  · have hj : j ∉ labels ⟨s.2,hc⟩ r := by simp [labels, hhit, hbad]
    have hres : j ≠ FiniteTable.fallback ⟨s.2,hc⟩ r := by
      intro he
      exact hj (he ▸ FiniteTable.fallback_mem ⟨s.2,hc⟩ r)
    have hq := (OffsetTable.row_facts d u A H hv).2.2.1 (s.1,⟨s.2,hc⟩) r j hj
    simp only [counts, dite_eq_left hc, OffsetTable.counts, ExecutableDyadic.numerators,
      ite_eq_right hres, hq, mul_zero, Nat.floor_zero]
  · have hj : j ≠ baseLabel s.2 r := by
      intro he; exact hbad (he ▸ base_covers s.2 r hhit)
    simp [counts, hc, hj]

theorem runCost_eq {n k : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) (A : ℚ) (H : ℕ)
    (hv : OffsetLP.Valid d u A (OffsetTable.flow (H:=H) d u A) (OffsetTable.offset d u A H))
    (hA : ∀ s r, ∑ j, OffsetTable.counts d u A H s r j = 2^(OffsetTable.bitWidth k H))
    (hlegal : ∀ s r coins,
      BitSampling.row (OffsetTable.counts d u A H s r) (hA s r) coins ∈ labels s.2 r)
    (p : List (Fin n)) (c : Config n k) (w : List (Fin n))
    (coins : Fin w.length → Fin (OffsetTable.bitWidth k H) → Bool) :
    BitSampling.runCost (counts d u A H) (total d u A H hv) EpochExpectation.next
      (EpochExpectation.charge d) (p,c.val) w coins =
    BitSampling.runCost (OffsetTable.counts d u A H) hA OffsetTable.next
      (fun s r j => (OffsetTable.charge d s r j : ℝ)) (p,c) w coins := by
  induction w generalizing p c with
  | nil => rfl
  | cons r w ih =>
    have he : counts d u A H (p,c.val) r = OffsetTable.counts d u A H (p,c) r := by
      funext j
      simp only [counts, dite_eq_left c.property]
      rfl
    have hr : BitSampling.row (counts d u A H (p,c.val) r) (total d u A H hv (p,c.val) r)
        (coins 0) = BitSampling.row (OffsetTable.counts d u A H (p,c) r)
          (hA (p,c) r) (coins 0) := by
      congr 1
    let j := BitSampling.row (OffsetTable.counts d u A H (p,c) r) (hA (p,c) r) (coins 0)
    have hj : j ∈ labels c r := hlegal (p,c) r (coins 0)
    have heq : (FiniteTable.next c r j).val = serve c.val r j := by
      unfold FiniteTable.next
      split
      · rfl
      · contradiction
    simp only [BitSampling.runCost, hr, EpochExpectation.next, OffsetTable.next,
      EpochExpectation.charge, OffsetTable.charge]
    change (d.distance (c.val j) r : ℝ) +
      BitSampling.runCost (counts d u A H) (total d u A H hv) EpochExpectation.next
        (EpochExpectation.charge d) (p++[r],serve c.val r j) w (Fin.tail coins) = _
    rw [← heq, ih]
    rfl

end UniformKServer.OffsetEpoch

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OffsetInstance
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                     
section

/-! Uniform absolute squared-log cost for the exact rational-search/dyadic
suffix, with arbitrary repeated starts and arbitrary finite activation delay.
The literal bit-machine implementation is deliberately not asserted here. -/
namespace UniformKServer.OffsetInstance

open EffectiveLP ComputedInstance
variable (mult : ℕ) (hm : PartitionTree.absoluteRate ≤ (mult : ℝ))
variable {n k : ℕ} [NeZero k]

include hm in
theorem valid (hk : 2 ≤ k) (hkn : k ≤ n) (d : RationalMetric n) (H : ℕ) :
    OffsetLP.Valid d (canonical hkn) (slope mult k)
      (OffsetTable.flow (H:=H) d (canonical hkn) (slope mult k))
      (OffsetTable.offset d (canonical hkn) (slope mult k) H) := by
  obtain ⟨_,_,h⟩ := OffsetTable.computed_uniform d (canonical hkn) hk (slope mult k)
    (rate_bound mult hm hk)
  exact (h H).1

end UniformKServer.OffsetInstance

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawRepresentation
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.Fallback.mem_coverers _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawFallback.choose_bits _root_.OAI.UniformKServer.RawFallback.label_bits _root_.OAI.UniformKServer.RawMarks.covers_bits _root_.OAI.UniformKServer.lazyPath_nil_iff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                        
section

namespace UniformKServer.RawRepresentation
open RawArithmetic RawWords RawTable RawTyped

theorem requests_injective {n : ℕ} : Function.Injective (@requests n) :=
  List.map_injective_iff.mpr Fin.val_injective

theorem config_injective {n k : ℕ} : Function.Injective (@config n k) := by
  intro c c' hh
  funext j
  apply Fin.ext
  have he:=congrArg (fun xs : List ℕ=>xs.getD j.val 0) hh
  simpa only [config_get] using he

theorem lift_list {n : ℕ} (w : List ℕ) (hw : ∀x∈w,x<n) :
    ∃v : List (Fin n),requests v=w := by
  refine ⟨w.attach.map (fun x=>⟨x.val,hw x.val x.property⟩),?_⟩
  simp [requests,List.map_map]

theorem lift_config {n k : ℕ} (c : List ℕ) (hc : c∈words n k) :
    ∃v : Configuration n k,config v=c := by
  obtain ⟨hlen,hmem⟩:= (mem_words n k c).mp hc
  let v : Configuration n k := fun j=>
    ⟨c.get ⟨j.val,by omega⟩,hmem _ (List.getElem_mem (by omega))⟩
  refine ⟨v,?_⟩
  apply List.ext_getElem
  · simp [config,hlen]
  · intro i hi hi'
    simp only [config,List.getElem_ofFn,v,List.get_eq_getElem]

theorem index_inj {n k H : ℕ} : Function.Injective (@indexKey n k H) := by
  intro a b hab
  have he:=Encodable.encode_injective (α:=List ℕ×List ℕ×ℕ×ℕ) hab
  have hp : a.1=b.1 := Subtype.ext (requests_injective (congrArg Prod.fst he))
  have hc : a.2.1=b.2.1 := config_injective (congrArg (fun z=>z.2.1) he)
  have hr : a.2.2.1=b.2.2.1 := Fin.ext (congrArg (fun z=>z.2.2.1) he)
  have hj : a.2.2.2=b.2.2.2 := Fin.ext (congrArg (fun z=>z.2.2.2) he)
  exact Prod.ext hp (Prod.ext hc (Prod.ext hr hj))

theorem represents {n k : ℕ} (H : ℕ)
    (N : (List (Fin n)×Configuration n k)→Fin n→Fin k→ℕ) :
    ∃ T : List ℕ,∀p c r j,p.length≤H→
      entry T (requests p) (config c) r.val j.val=N (p,c) r j := by
  obtain ⟨T,hT⟩:=FiniteRepresentation.represents (@indexKey n k H) index_inj
    (fun i : Index n k H=>N (i.1.val,i.2.1) i.2.2.1 i.2.2.2) 0
  refine ⟨T,?_⟩
  intro p c r j hp
  exact hT (⟨p,(EffectiveLP.mem_words p).mpr hp⟩,c,r,j)

end UniformKServer.RawRepresentation

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawCompleteness
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
attribute [-simp] _root_.OAI.UniformKServer.Fallback.mem_coverers _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawFallback.choose_bits _root_.OAI.UniformKServer.RawFallback.label_bits _root_.OAI.UniformKServer.RawGlobal.label_state _root_.OAI.UniformKServer.RawGlobal.step_state _root_.OAI.UniformKServer.RawMarks.covers_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                      
section

namespace UniformKServer.RawCompleteness
open RawArithmetic RawWords RawTable RawTyped RawExpansion RawCertificate RawRows RawRepresentation

theorem config_any {n k : ℕ} (c : Configuration n k) (r : Fin n) :
    (config c).any (fun x=>decide (x=r.val))=true ↔ ∃j,c j=r := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x,hx,he⟩
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hx
    exact ⟨j,Fin.ext (of_decide_eq_true he)⟩
  · rintro ⟨j,hj⟩
    exact ⟨(c j).val,List.mem_ofFn.mpr ⟨j,rfl⟩,by simp [hj]⟩

theorem row_ok {n k b : ℕ} (T : List ℕ) (p : List (Fin n)) (c : Configuration n k)
    (r : Fin n) (N : Fin k→ℕ) (hrep : ∀j,entry T (requests p) (config c) r.val j.val=N j)
    (hN : ∑j,N j=2^b) (hl : ∀j,(∃i,c i=r)→c j≠r→N j=0) :
    rowOK k b T (requests p) (config c) r.val=true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [range_eq_ofFn]
    simpa only [List.map_ofFn,Function.comp_def,hrep,List.sum_ofFn] using hN
  · apply List.all_eq_true.mpr
    intro j hj
    let j' : Fin k := ⟨j,List.mem_range.mp hj⟩
    change (!(config c).any (fun x=>decide (x=r.val)) ||
      decide ((config c).getD j'.val 0=r.val) ||
        decide (entry T (requests p) (config c) r.val j'.val=0))=true
    rw [config_get,hrep]
    by_cases hh : ∃i,c i=r
    · have ha := (config_any c r).mpr hh
      by_cases hjr : c j'=r
      · simp [hjr]
      · have hn : (c j').val≠r.val := fun h=>hjr (Fin.ext h)
        simp [ha,hn,hl j' hh hjr]
    · have ha : (config c).any (fun x=>decide (x=r.val))=false :=
        Bool.eq_false_of_not_eq_true (fun h=>hh ((config_any c r).mp h))
      simp [ha]

theorem rows_ok {n k H b : ℕ} (T : List ℕ)
    (N : State n k→Fin n→Fin k→ℕ)
    (hrep : ∀p c r j,p.length≤H→entry T (requests p) (config c) r.val j.val=N (p,c) r j)
    (hN : ∀s r,∑j,N s r j=2^b)
    (hl : ∀s r j,(∃i,s.2 i=r)→s.2 j≠r→N s r j=0) : rowsOK n k H b T=true := by
  apply List.all_eq_true.mpr
  intro p hp
  obtain ⟨hlen,hp'⟩ := (mem_upto n H p).mp hp
  obtain ⟨p',rfl⟩:=lift_list p hp'
  apply List.all_eq_true.mpr
  intro c hc
  obtain ⟨c',rfl⟩:=lift_config c hc
  apply List.all_eq_true.mpr
  intro r hr
  let r' : Fin n := ⟨r,List.mem_range.mp hr⟩
  exact row_ok T p' c' r' (N (p',c') r')
    (fun j=>hrep p' c' r' j (by simpa [requests] using hlen)) (hN _ _) (hl (p',c') r')

theorem rowCost_eq {n k H b : ℕ} (hk : 0<k) (T : List ℕ)
    (N : State n k→Fin n→Fin k→ℕ)
    (hrep : ∀p c r j,p.length≤H→entry T (requests p) (config c) r.val j.val=N (p,c) r j)
    (d : RationalMetric n) (p : List (Fin n)) (c : Configuration n k) (w : List (Fin n))
    (hw : p.length+w.length≤H) :
    BitSampling.rowCost (b:=b) (complete hk H b T) next (charge d) (p,c) w=
      BitSampling.rowCost (b:=b) N next (charge d) (p,c) w := by
  induction w generalizing p c with
  | nil=>rfl
  | cons r w ih=>
    have hp : p.length≤H := by simp only [List.length_cons] at hw;omega
    simp only [BitSampling.rowCost,complete,ite_eq_left hp,kernel,hrep p c r _ hp,next]
    congr 1
    funext j
    rw [ih]
    simp only [List.length_append,List.length_cons,List.length_nil] at *
    omega

end UniformKServer.RawCompleteness

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawBounded
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                 
section

namespace UniformKServer.RawBounded
open RawArithmetic RawWords RawTable RawPath RawTyped RawExpansion RawCertificate RawRows

theorem traces_length {R : Type*} {k : ℕ} (w : List R) (h : List (R×Fin k))
    (hh : h∈PathExpansion.traces k w) : h.length=w.length := by
  induction w generalizing h with
  | nil=>simpa [PathExpansion.traces] using hh
  | cons r w ih=>
    obtain ⟨l,hl,hh⟩:=List.mem_flatten.mp hh
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hl
    obtain ⟨h',hh',rfl⟩:=List.mem_map.mp hh
    simp [ih h' hh']

theorem weight_complete {n k H b : ℕ} (hk : 0<k) (T : List ℕ)
    (p : List (Fin n)) (c : Configuration n k) (h : History n k)
    (hp : p.length+h.length≤H) :
    PathExpansion.weight (kernel T) next (p,c) h=
      PathExpansion.weight (complete hk H b T) next (p,c) h := by
  induction h generalizing p c with
  | nil=>rfl
  | cons rj h ih=>
    obtain ⟨r,j⟩:=rj
    have hp' : p.length≤H := by simp only [List.length_cons] at hp;omega
    simp only [PathExpansion.weight,complete,ite_eq_left hp',next]
    rw [ih]
    simp only [List.length_append,List.length_cons,List.length_nil] at *
    omega

theorem expected_eq {n k H b : ℕ} (hk : 0<k) (d : RationalMetric n) (draw : List Q)
    (hd : ∀x y : Fin n,value (dist n draw x.val y.val)=d.distance x y)
    (T : List ℕ) (hrows : rowsOK n k H b T=true)
    (p : List (Fin n)) (c : Configuration n k) (w : List (Fin n))
    (hw : p.length+w.length≤H) :
    (value (expected n k b draw T (requests p) (config c) (requests w)):ℝ)=
      BitSampling.rowCost (b:=b) (complete hk H b T) next (charge d) (p,c) w := by
  rw [expected_value]
  push_cast
  rw [total_eq d draw hd]
  have he : ((PathExpansion.traces k w).map fun h=>
      (PathExpansion.weight (kernel T) next (p,c) h:ℝ)*
        PathExpansion.movement next (charge d) (p,c) h)=
      (PathExpansion.traces k w).map (fun h=>
        (PathExpansion.weight (complete hk H b T) next (p,c) h:ℝ)*
          PathExpansion.movement next (charge d) (p,c) h) := by
    apply List.map_congr_left
    intro h hh
    rw [weight_complete hk T p c h (by simpa only [traces_length w h hh] using hw)]
  rw [he,PathExpansion.sum_weight_cost _ (RawRows.total hk hrows)]
  simp only [requests,List.length_map,pow_mul]
  exact mul_div_cancel_left₀ _ (by positivity)

end UniformKServer.RawBounded

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawSound
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                               
section

namespace UniformKServer.RawSound
open RawArithmetic RawWords RawTable RawPath RawTyped RawExpansion RawCertificate RawRows

theorem config_canonical {n k : ℕ} (hkn : k≤n) :
    config (fun j : Fin k=>(⟨j.val,lt_of_lt_of_le j.isLt hkn⟩:Fin n))=List.range k := by
  exact (range_eq_ofFn k).symm

end UniformKServer.RawSound

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawTableWitness
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
attribute [-simp] _root_.OAI.UniformKServer.Fallback.mem_coverers _root_.OAI.UniformKServer.RawBinary.distances_length _root_.OAI.UniformKServer.RawBinary.read_rationalCode _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawFallback.choose_bits _root_.OAI.UniformKServer.RawFallback.label_bits _root_.OAI.UniformKServer.RawGlobal.label_state _root_.OAI.UniformKServer.RawGlobal.step_state _root_.OAI.UniformKServer.RawMarks.covers_bits _root_.OAI.UniformKServer.RawMetric.present_eq _root_.OAI.UniformKServer.RawProgram.unpack_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                      
section

namespace UniformKServer.RawTableWitness
open RawArithmetic RawWords RawTable RawPath RawTyped RawExpansion RawCertificate RawRows RawRepresentation

theorem table_ok {n k H b A R : ℕ} [NeZero k] (hkn : k≤n)
    (d : RationalMetric n) (draw : List Q)
    (hd : ∀x y : Fin n,value (dist n draw x.val y.val)=d.distance x y)
    (D δ : Q) (T : List ℕ) (N : State n k→Fin n→Fin k→ℕ)
    (hrep : ∀p c r j,p.length≤H→entry T (requests p) (config c) r.val j.val=N (p,c) r j)
    (hN : ∀s r,∑j,N s r j=2^b)
    (hlazy : ∀s r j,(∃i,s.2 i=r)→s.2 j≠r→N s r j=0)
    (hbound : ∀w : List (Fin n),w.length≤H→
      BitSampling.rowCost (b:=b) N next (charge d)
        ([],fun j : Fin k=>(⟨j.val,lt_of_lt_of_le j.isLt hkn⟩:Fin n)) w ≤
        (A:ℝ)*offlineCost d (fun j : Fin k=>(⟨j.val,lt_of_lt_of_le j.isLt hkn⟩:Fin n)) w+
          R*(value δ:ℝ)+(value D:ℝ)) :
    tableOK n k H b A R draw D δ T=true := by
  have hr:=RawCompleteness.rows_ok T N hrep hN hlazy
  let u : Configuration n k := fun j=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩
  have hu : config u=List.range k := RawSound.config_canonical hkn
  apply List.all_eq_true.mpr
  intro w hw
  obtain ⟨hlen,hmem⟩:=(mem_upto n H w).mp hw
  obtain ⟨w',rfl⟩:=lift_list w hmem
  have hw' : w'.length≤H := by simpa [requests] using hlen
  apply List.all_eq_true.mpr
  intro g hg
  obtain ⟨hglen,hgmem⟩:= (mem_words k (requests w').length g).mp hg
  obtain ⟨g',rfl⟩:=lift_list g hgmem
  have hlen' : w'.length=g'.length := by simpa [requests] using hglen.symm
  apply decide_eq_true
  apply (le_iff _ _).mpr
  have he:=RawBounded.expected_eq (NeZero.pos k) d draw hd T hr [] u w' (by simpa using hw')
  rw [RawCompleteness.rowCost_eq (NeZero.pos k) T N hrep d [] u w' (by simpa using hw')] at he
  have hl := OfflineDynamic.optRat_lower d u (w'.zip g')
  have hzip : (w'.zip g').map Prod.fst=w' := List.map_fst_zip (by omega)
  rw [hzip,←OfflineDynamic.offline_eq_optRat] at hl
  have hb:=hbound w' hw'
  have hc : (value (cost n draw (config u) (requests w') (requests g')):ℝ)=
      costAlong d u (w'.zip g') := by
    rw [cost_value,history_zip w' g' hlen']
    exact movement_eq d draw hd u (w'.zip g')
  have ha : (0:ℝ)≤A := by positivity
  have hm:=mul_le_mul_of_nonneg_left hl ha
  have hfinal : (value (expected n k b draw T [] (List.range k) (requests w')):ℝ) ≤
      A*(value (cost n draw (List.range k) (requests w') (requests g')):ℝ)+
        R*(value δ:ℝ)+(value D:ℝ) := by
    change (value (expected n k b draw T [] (config u) (requests w')):ℝ)=_ at he
    rw [hu] at he
    rw [hu] at hc
    rw [he,hc]
    exact hb.trans (by dsimp [u] at *;linarith only [hm])
  simp only [value_add,value_mul,value_natural]
  have hfinal' : (value (expected n k b draw T [] (List.range k) (requests w')):ℝ) ≤
      (A:ℝ)*(value (cost n draw (List.range k) (requests w') (requests g')):ℝ)+
        ((R:ℝ)*(value δ:ℝ)+(value D:ℝ)) := by simpa only [add_assoc] using hfinal
  exact_mod_cast hfinal'

end UniformKServer.RawTableWitness

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawExistence
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawBinary.distances_length _root_.OAI.UniformKServer.RawBinary.read_rationalCode _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawFallback.choose_bits _root_.OAI.UniformKServer.RawFallback.label_bits _root_.OAI.UniformKServer.RawGlobal.chosen_state _root_.OAI.UniformKServer.RawGlobal.label_state _root_.OAI.UniformKServer.RawGlobal.step_state _root_.OAI.UniformKServer.RawMarks.covers_bits _root_.OAI.UniformKServer.RawProgram.unpack_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                   
section

namespace UniformKServer.RawExistence
open RawArithmetic RawWords RawTable RawTyped RawCertificate ComputedInstance EffectiveLP

theorem row_bound {n k : ℕ} [NeZero k] (hn : 2≤n) (hk : 2≤k) (hkn : k≤n)
    (mult : ℕ) (hm : PartitionTree.absoluteRate≤(mult:ℝ)) (d : RationalMetric n)
    (w : List (Fin n)) (hw : w.length≤horizon k (OffsetInstance.cap mult hm hn hk hkn d)) :
    BitSampling.rowCost (b:=OffsetTable.bitWidth k (horizon k (OffsetInstance.cap mult hm hn hk hkn d)))
      (OffsetEpoch.counts d (canonical hkn) (OffsetInstance.slope mult k)
        (horizon k (OffsetInstance.cap mult hm hn hk hkn d)))
      RawExpansion.next (RawExpansion.charge d) ([],(canonical hkn).val) w ≤
      (OffsetInstance.slope mult k:ℝ)*offlineCost d (canonical hkn).val w+
        (OffsetInstance.restart mult hm hn hk hkn d:ℝ)*(separation hn d:ℝ)+(diameter hn d:ℝ) := by
  let H:=horizon k (OffsetInstance.cap mult hm hn hk hkn d)
  have hv:=OffsetInstance.valid mult hm hk hkn d H
  obtain ⟨_,_,hN,hlegal,hcost⟩:=OffsetTable.construct d (canonical hkn) (OffsetInstance.slope mult k)
    H hv (diameter hn d:ℝ) (parameters hn (NeZero.pos k) d).1 (parameters hn (NeZero.pos k) d).2.2.1
  have htotal:=OffsetEpoch.total d (canonical hkn) (OffsetInstance.slope mult k) H hv
  have he : BitSampling.rowCost (b:=OffsetTable.bitWidth k H) (OffsetEpoch.counts d (canonical hkn) (OffsetInstance.slope mult k) H)
      RawExpansion.next (RawExpansion.charge d) ([],(canonical hkn).val) w=
      BitSampling.mean (BitSampling.runCost (OffsetTable.counts d (canonical hkn) (OffsetInstance.slope mult k) H)
        hN OffsetTable.next (fun s r j=>(OffsetTable.charge d s r j:ℝ)) ([],canonical hkn) w) := by
    rw [←BitSampling.bit_path_mean _ htotal]
    congr 1
    funext coins
    exact OffsetEpoch.runCost_eq d (canonical hkn) (OffsetInstance.slope mult k) H hv hN hlegal [] (canonical hkn) w coins
  rw [he]
  have hc:=hcost w hw
  have hr:= (OffsetParameters.restart_spec hn hk d (canonical hkn) (OffsetInstance.slope mult k)
    (OffsetInstance.rate_bound mult hm hk)).2.2
  have hr' : (OffsetTable.offset d (canonical hkn) (OffsetInstance.slope mult k) H : ℝ) ≤
    (OffsetInstance.restart mult hm hn hk hkn d:ℝ)*(separation hn d:ℝ) := by exact_mod_cast hr
  exact hc.trans (by linarith)

theorem exists_certificate {n k : ℕ} [NeZero k] (hn : 2≤n) (hk : 2≤k) (hkn : k≤n)
    (mult : ℕ) (hm : PartitionTree.absoluteRate≤(mult:ℝ)) (d : RationalMetric n)
    (draw : List Q) (hd : ∀x y : Fin n,value (dist n draw x.val y.val)=d.distance x y) :
    ∃v : Certificate,verify mult (n,k,draw) v=true := by
  let ell:=Nat.clog 2 (k+1)
  let M:=OffsetInstance.cap mult hm hn hk hkn d
  let H:=UniformKServer.horizon k M
  let R:=OffsetInstance.restart mult hm hn hk hkn d
  let b:=OffsetTable.bitWidth k H
  let A:=OffsetInstance.slope mult k
  let N:=OffsetEpoch.counts d (canonical hkn) A H
  let D:=RawMetric.present (diameter hn d)
  let δ:=RawMetric.present (separation hn d)
  have hp:=parameters hn (NeZero.pos k) d
  have hD : 0≤diameter hn d := by exact_mod_cast hp.1
  have hδ : 0 < separation hn d := by exact_mod_cast hp.2.1
  have hDe : value D=diameter hn d := RawMetric.present_eq _ hD
  have hδe : value δ=separation hn d := RawMetric.present_eq _ hδ.le
  have hv:=OffsetInstance.valid mult hm hk hkn d H
  have htotal:=OffsetEpoch.total d (canonical hkn) A H hv
  have hforbid:=OffsetEpoch.forbidden d (canonical hkn) A H hv
  obtain ⟨T,hT⟩:=RawRepresentation.represents H N
  let v : Certificate:=((ell,b,M,R),(D,δ),T)
  refine ⟨v,?_⟩
  have hnums : numbersOK k v=true := by
    have hr:=OffsetParameters.restart_spec hn hk d (canonical hkn) A (OffsetInstance.rate_bound mult hm hk)
    have hc:=OffsetParameters.cap_bound (k:=k) hn d R
    have hend : (R*(k+1):ℚ)*value D≤(M+1:ℚ)*value δ := by
      rw [hDe,hδe]
      exact_mod_cast hc
    simp only [numbersOK,RawCertificate.ell,RawCertificate.cap,RawCertificate.restart,diam,sep,v,
      Bool.and_eq_true_iff]
    refine ⟨⟨⟨⟨⟨⟨decide_eq_true (Nat.clog_pos (by decide : 1<2) (by omega : 1<k+1)),
      decide_eq_true (Nat.pow_pred_clog_lt_self (by decide : 1<2) (by omega : 1<k+1))⟩,
      decide_eq_true (Nat.le_pow_clog (by decide : 1<2) (k+1))⟩,decide_eq_true hr.1⟩,decide_eq_true (RawMetric.present_pos _ hδ)⟩,?_⟩,?_⟩
    · apply decide_eq_true
      apply (le_iff _ _).mpr
      simpa only [value_mul,value_natural,hDe,hδe,R,A,OffsetInstance.restart] using hr.2.1
    · apply decide_eq_true
      apply (le_iff _ _).mpr
      simpa only [value_mul,value_natural,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using hend
  have hbounds : boundsOK n draw D δ=true := by
    apply RawMetric.bounds_ok d draw hd D δ
    · intro x y;rw [hDe];exact_mod_cast hp.2.2.1 x y
    · intro x y h;rw [hδe];exact_mod_cast hp.2.2.2.1 x y h
  have hrows:=RawCompleteness.rows_ok T N hT htotal hforbid
  have htable : tableOK n k H b (mult*ell^2) R draw D δ T=true := by
    apply RawTableWitness.table_ok hkn d draw hd D δ T N hT htotal hforbid
    intro w hw
    have hcanon : (canonical hkn).val=(fun j : Fin k=>(⟨j.val,lt_of_lt_of_le j.isLt hkn⟩:Fin n)) := by
      funext j;exact Fin.ext rfl
    rw [←hcanon]
    have hb:=row_bound hn hk hkn mult hm d w hw
    dsimp [N,A,H,M,R,ell]
    simpa only [hDe,hδe,OffsetInstance.slope,OffsetLP.slope,Rat.cast_mul,Rat.cast_natCast,
      Rat.cast_pow,Nat.cast_mul,Nat.cast_pow,canonical] using hb
  change (numbersOK k v && boundsOK n draw D δ &&
    rowsOK n k (RawCertificate.horizon k M) b T &&
    tableOK n k (RawCertificate.horizon k M) b (mult*ell^2) R draw D δ T)=true
  rw [RawMetric.horizon_eq]
  change (numbersOK k v && boundsOK n draw D δ && rowsOK n k H b T &&
    tableOK n k H b (mult*ell^2) R draw D δ T)=true
  rw [hnums,hbounds,hrows,htable]
  rfl

end UniformKServer.RawExistence

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StackRun
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.UniformWrapper.ofWord_tape _root_.OAI.UniformKServer.UniformWrapper.tape_shift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.StackCompiler

theorem run_halted {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    (hy : s.yielded=true) (bs : List Bool) : run P s bs=s := by
  induction bs with
  | nil=>rfl
  | cons b bs ih=>simpa [run_cons,step,hy] using ih

theorem capped_after {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    {t B : ℕ} (h : (run P s (List.replicate t false)).yielded=true) (htB : t≤B) :
    run P s (List.replicate B false)=run P s (List.replicate t false) := by
  obtain ⟨a,rfl⟩:=Nat.exists_eq_add_of_le htB
  rw [List.replicate_add,run_append]
  exact run_halted P _ h _

end UniformKServer.StackCompiler

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LiteralBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.LiteralBound
open Turing StackCompiler StackPrimitive
open scoped Classical

 theorem monotone_time {t T u r a : ℕ} (h : finishes t u r a=true) (ht : t≤T) :
    finishes T u r a=true := by
  rw [finishes_run] at h ⊢
  rw [capped_after program _ h ht]
  exact h

end UniformKServer.LiteralBound

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawFinite
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.RawFinite
open RawProgram RawCertificate
open scoped Classical

 theorem choose_repr {n k : ℕ} (hk : 0<k) (v : Certificate)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true)
    (s : TapeController.State n k (cap v) (restart v) (bits v)) (r : Fin n) (a : ℕ) :
    RawProgram.chosen (repr v s) (requestToken r.val) a=
      (TapeController.choose hk (RawRows.complete hk (UniformKServer.horizon k (cap v)) (bits v) (table v))
        (RawRows.total hk hT) s r (BinaryTape.coins k (cap v) (bits v) a)).val := by
  simp only [RawProgram.chosen,repr,payload,requestToken,request_code,BinaryTape.fresh_eq]
  exact RawGlobal.label_state hk (table v) hT s r _

 theorem next_repr {n k : ℕ} (hk : 0<k) (hkn : k≤n) (v : Certificate) (hR : 0 < restart v)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true)
    (s : TapeController.State n k (cap v) (restart v) (bits v)) (r : Fin n) (a : ℕ) :
    RawProgram.next (repr v s) (requestToken r.val) a=
      repr v (TapeController.step hk hR (fun j : Fin k=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩)
        (RawRows.complete hk (UniformKServer.horizon k (cap v)) (bits v) (table v))
        (RawRows.total hk hT) s r (BinaryTape.coins k (cap v) (bits v) a)) := by
  simp only [RawProgram.next,repr,payload,requestToken,request_code,BinaryTape.fresh_eq]
  rw [RawGlobal.step_state hk hkn hR (table v) hT]

 theorem finite_closed {n k : ℕ} (hk : 0<k) (hkn : k≤n) (v : Certificate) (hR : 0 < restart v)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true) :
    ∃S : List ℕ, Encodable.encode (RawProgram.initial n k v)∈S ∧
      ∀u∈S,∀r<n,∀a : ℕ,
        RawProgram.chosen (unpack u) (requestToken r) a<k ∧
        Encodable.encode (RawProgram.next (unpack u) (requestToken r) a)∈S := by
  let State:=TapeController.State n k (cap v) (restart v) (bits v)
  let : Fintype State:=Fintype.ofFinite _
  let S : Finset ℕ:=Finset.univ.image (fun s : State=>Encodable.encode (repr v s))
  have hm (s : State) : Encodable.encode (repr v s)∈S := Finset.mem_image.mpr ⟨s,Finset.mem_univ _,rfl⟩
  refine ⟨S.toList,?_,?_⟩
  · rw [Finset.mem_toList]
    convert hm (TapeController.initial hR (fun j : Fin k=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩)) using 1
    all_goals try with_reducible_and_instances rfl
    exact congrArg (fun x=>Encodable.encode (payload n k v x))
      (RawGlobal.initial_state (M:=cap v) (b:=bits v) hkn hR)
  · intro u hu r hr a
    rw [Finset.mem_toList] at hu
    obtain ⟨s,hs,rfl⟩:=Finset.mem_image.mp hu
    simp only [unpack_encode]
    rw [choose_repr hk v hT s (⟨r,hr⟩ : Fin n) a,
      next_repr hk hkn v hR hT s (⟨r,hr⟩ : Fin n) a]
    exact ⟨Fin.isLt _,Finset.mem_toList.mpr (hm _)⟩

end UniformKServer.RawFinite

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RuntimeExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.RuntimeCertificate
open RawProgram RawCertificate RawFinite
open scoped Classical

theorem time_good (u r a : ℕ) : LiteralBound.finishes (time u r a) u r a=true :=
  Classical.choose_spec (LiteralBound.exists_time u r a)

theorem exists_cert {n k : ℕ} (hk : 0<k) (hkn : k≤n) (v : Certificate) (hR : 0 < restart v)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true) :
    ∃c,verify n k v c=true := by
  obtain ⟨S,h₀,hS⟩:=finite_closed hk hkn v hR hT
  let b:=B k v
  let T:=bound n b S
  refine ⟨(S,T),(verify_iff _ _ _ _).mpr ⟨h₀,le_max_left _ _,?_⟩⟩
  intro u hu
  have hU : needU n b u≤T :=
    (Finset.le_sup (f:=needU n b) (List.mem_toFinset.mpr hu)).trans (le_max_right _ _)
  refine ⟨(le_max_left _ _).trans hU,?_⟩
  intro r hr
  have hR' : needR b u r≤T :=
    (Finset.le_sup (f:=needR b u) (Finset.mem_range.mpr hr)).trans
      ((le_max_right _ _).trans hU)
  refine ⟨(le_max_left _ _).trans hR',?_⟩
  intro a ha
  have hA : needA u r a≤T :=
    (Finset.le_sup (f:=needA u r) (Finset.mem_range.mpr ha)).trans
      ((le_max_right _ _).trans hR')
  exact ⟨(hS u hu r hr a).1,(hS u hu r hr a).2,(le_max_left _ _).trans hA,
    LiteralBound.monotone_time (time_good _ _ _) ((le_max_right _ _).trans hA)⟩

end UniformKServer.RuntimeCertificate

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ConstructorSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.ConstructorSearch
open RawCertificate
open scoped Classical

theorem exists_certificate_oai {n k : ℕ} [NeZero k] (hn : 2≤n) (hk : 2≤k) (hkn : k≤n)
    (mult : ℕ) (hm : PartitionTree.absoluteRate≤(mult:ℝ)) (d : RationalMetric n)
    (draw : List RawArithmetic.Q)
    (hd : ∀x y : Fin n,RawArithmetic.value (RawTable.dist n draw x.val y.val)=d.distance x y) :
    ∃v : Cert,verify mult (n,k,draw) v=true := by
  obtain ⟨v,hv⟩:=RawExistence.exists_certificate hn hk hkn mult hm d draw hd
  have hp:=RawAccepted.spec d draw hd hv
  obtain ⟨c,hc⟩:=RuntimeCertificate.exists_cert (by omega) hkn v hp.numbers.restart_pos hp.rows
  exact ⟨(v,c),by simp only [verify,hv,hc,Bool.and_self]⟩

end UniformKServer.ConstructorSearch

end

end OAI
end

theorem solution : type_of% @OAI.UniformKServer.ConstructorSearch.exists_certificate_oai := @OAI.UniformKServer.ConstructorSearch.exists_certificate_oai
