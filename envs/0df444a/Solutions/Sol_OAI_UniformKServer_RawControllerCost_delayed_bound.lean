-- Prove2me | solution 1 for OAI.UniformKServer.RawControllerCost.delayed_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:00:27.599907+00:00
-- url     : https://prove2.me/submissions/124eae3b-3a0c-4428-97cd-efcbfaf3d2e6

import Mathlib
import Definitions.Def_UniformKServer
import Definitions.Def_Q220Uk008
import Theorems.Thm_OAI_UniformKServer_ControllerBound_suffix

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
-- module Solutions.Q220_UK.UniformKServer_OffsetInstance
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawBinary.distances_length _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawMarks.covers_bits
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

theorem history_diameter {n k : ℕ} (d : RationalMetric n) (s : Configuration n k)
    (h : History n k) (D : ℝ) (hd : ∀x y,(d.distance x y : ℝ) ≤ D) :
    costAlong d s h ≤ h.length*D := by
  induction h generalizing s with
  | nil => simp [costAlong]
  | cons x h ih =>
    simp only [costAlong,List.length_cons,Nat.cast_add,Nat.cast_one]
    have hh := ih (serve s x.1 x.2)
    have hx := hd (s x.2) x.1
    linarith

open EffectiveLP ComputedInstance
variable (mult : ℕ) (hm : PartitionTree.absoluteRate ≤ (mult : ℝ))
variable {n k : ℕ} [NeZero k]

include hm in
omit [NeZero k] in
theorem coefficient_bound (hk : 2 ≤ k) :
    4*(slope mult k : ℝ)+4 ≤ coefficient mult*(Real.log (k+1))^2 := by
  obtain ⟨_,hs⟩ := OffsetLP.slope_bounds mult k (by omega) hm
  have hlog : Real.log 2 ≤ Real.log (k+1) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ k+1 by omega))
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsq : (Real.log 2)^2 ≤ (Real.log (k+1))^2 := by nlinarith
  have hb := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4/(Real.log 2)^2 by positivity)
  have he : 4/(Real.log 2)^2*(Real.log 2)^2=4 := by field_simp [ne_of_gt hl]
  rw [he] at hb
  unfold coefficient slope
  nlinarith only [hs,hb]

end UniformKServer.OffsetInstance

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
theorem value_nonneg (a : Q) : 0≤value a := by unfold value;positivity

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
-- module Solutions.Q220_UK.UniformKServer_RawExpansion
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
attribute [-simp] _root_.OAI.UniformKServer.Fallback.mem_coverers _root_.OAI.UniformKServer.RawBinary.distances_length _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawMarks.covers_bits _root_.OAI.UniformKServer.RawProgram.unpack_encode
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
-- module Solutions.Q220_UK.UniformKServer_RawRows
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.Fallback.mem_coverers _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawMarks.covers_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                              
section

namespace UniformKServer.RawRows
open RawArithmetic RawWords RawTable RawTyped RawExpansion RawCertificate

theorem forbidden_row {n k H b : ℕ} {T : List ℕ} (h : rowsOK n k H b T=true)
    (p : List (Fin n)) (c : Configuration n k) (r : Fin n) (j : Fin k) (hp : p.length≤H)
    (hhit : ∃ i,c i=r) (hbad : c j≠r) : kernel T (p,c) r j=0 := by
  have hh := selected_row h (requests p) (config c) r.val (requests_mem p H hp) (config_mem c) r.isLt
  have hf := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hh).2 j.val (List.mem_range.mpr j.isLt)
  have hx : (config c).any (fun x=>decide (x=r.val))=true := by
    apply List.any_eq_true.mpr
    obtain ⟨i,hi⟩:=hhit
    refine ⟨(c i).val,List.mem_ofFn.mpr ⟨i,rfl⟩,?_⟩
    simp [hi]
  have he : (c j).val≠r.val := by intro he;exact hbad (Fin.ext he)
  simpa only [hx,Bool.not_true,Bool.false_or,config_get,decide_eq_false he,Bool.false_or,
    decide_eq_true_eq,kernel] using hf

theorem fallback_hit {n k : ℕ} (hk : 0<k) (c : Configuration n k) (r : Fin n)
    (h : ∃j,c j=r) : c (fallback hk c r)=r := by
  simp only [fallback,dite_eq_left h]
  exact Classical.choose_spec h

theorem forbidden {n k H b : ℕ} {T : List ℕ} (hk : 0<k) (h : rowsOK n k H b T=true) :
    ∀(s : State n k) r j,(∃i,s.2 i=r)→s.2 j≠r→complete hk H b T s r j=0 := by
  intro s r j hhit hbad
  by_cases hp : s.1.length≤H
  · simp only [complete,ite_eq_left hp]
    exact forbidden_row h s.1 s.2 r j hp hhit hbad
  · have hj : j≠fallback hk s.2 r := by intro he;exact hbad (he ▸ fallback_hit hk s.2 r hhit)
    simp [complete,hp,hj]

end UniformKServer.RawRows

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
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
attribute [-simp] _root_.OAI.UniformKServer.Fallback.mem_coverers _root_.OAI.UniformKServer.RawBinary.distances_length _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawMarks.covers_bits _root_.OAI.UniformKServer.RawProgram.unpack_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                               
section

namespace UniformKServer.RawSound
open RawArithmetic RawWords RawTable RawPath RawTyped RawExpansion RawCertificate RawRows

theorem extracted_cost {n k : ℕ} (d : RationalMetric n) (draw : List Q)
    (hd : ∀x y : Fin n,value (dist n draw x.val y.val)=d.distance x y)
    (c : Configuration n k) (h : History n k) :
    (value (cost n draw (config c) (requests (h.map Prod.fst))
      (requests (h.map Prod.snd))):ℝ)=costAlong d c h := by
  rw [cost_value,history_zip (h.map Prod.fst) (h.map Prod.snd) (by simp)]
  have hz : (h.map Prod.fst).zip (h.map Prod.snd)=h := by
    induction h <;> simp_all
  simpa only [hz] using movement_eq d draw hd c h

theorem config_canonical {n k : ℕ} (hkn : k≤n) :
    config (fun j : Fin k=>(⟨j.val,lt_of_lt_of_le j.isLt hkn⟩:Fin n))=List.range k := by
  exact (range_eq_ofFn k).symm

theorem table_bound {n k H b A R : ℕ} [NeZero k] (hkn : k≤n)
    (d : RationalMetric n) (draw : List Q)
    (hd : ∀x y : Fin n,value (dist n draw x.val y.val)=d.distance x y)
    (D δ : Q) (T : List ℕ) (hrows : rowsOK n k H b T=true)
    (htable : tableOK n k H b A R draw D δ T=true)
    (w : List (Fin n)) (hw : w.length≤H) :
    BitSampling.rowCost (b:=b) (complete (NeZero.pos k) H b T) next (charge d)
      ([],fun j : Fin k=>(⟨j.val,lt_of_lt_of_le j.isLt hkn⟩:Fin n)) w ≤
      (A:ℝ)*offlineCost d (fun j : Fin k=>(⟨j.val,lt_of_lt_of_le j.isLt hkn⟩:Fin n)) w+
        R*(value δ:ℝ)+(value D:ℝ) := by
  let u : Configuration n k := fun j=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩
  obtain ⟨h,hh,hcost⟩:=OfflineDynamic.optRat_attained d u w
  have hg : requests (h.map Prod.snd)∈words k (requests w).length := by
    apply (mem_words _ _ _).mpr
    refine ⟨?_,?_⟩
    · simp only [requests,List.length_map]
      simpa only [List.length_map] using congrArg List.length hh
    · intro j hj
      obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hj
      exact x.isLt
  have ht:=of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp htable (requests w) (requests_mem w H hw))
      (requests (h.map Prod.snd)) hg)
  have ht':=(le_iff _ _).mp ht
  have htR : (value (expected n k b draw T [] (List.range k) (requests w)):ℝ) ≤
      A*(value (cost n draw (List.range k) (requests w) (requests (h.map Prod.snd))):ℝ)+
        (R*(value δ:ℝ)+(value D:ℝ)) := by
    exact_mod_cast (by simpa only [value_add,value_mul,value_natural] using ht')
  have he:=RawBounded.expected_eq (NeZero.pos k) d draw hd T hrows [] u w (by simpa using hw)
  have hu : config u=List.range k := config_canonical hkn
  simp only [requests,List.map_nil,hu] at he
  rw [←he]
  have hc:=extracted_cost d draw hd u h
  rw [hh,hu,hcost,←OfflineDynamic.offline_eq_optRat] at hc
  rw [hc] at htR
  simpa only [add_assoc,requests,u] using htR

end UniformKServer.RawSound

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawControllerCost
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.RawBinary.distances_length _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawGlobal.chosen_state _root_.OAI.UniformKServer.RawGlobal.initial_state _root_.OAI.UniformKServer.RawMarks.covers_bits _root_.OAI.UniformKServer.RawProgram.unpack_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                        
section

namespace UniformKServer.RawControllerCost
open RawArithmetic RawCertificate EpochExpectation
variable {n k mult : ℕ} [NeZero k] (hk : 2≤k) (hkn : k≤n)
  (hm : PartitionTree.absoluteRate≤(mult:ℝ)) (d : RationalMetric n) (draw : List Q)
  (hd : ∀x y : Fin n,value (RawTable.dist n draw x.val y.val)=d.distance x y)
  (v : Certificate) (hv : verify mult (n,k,draw) v=true)

omit [NeZero k] in
theorem u_injective : Function.Injective (u hkn) := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin n=>x.val) h)

include hd hv in
theorem lazy : ∀s r j,(∃i,s.2 i=r)→s.2 j≠r→N (n:=n) (k:=k) v s r j=0 :=
  RawRows.forbidden (NeZero.pos k) (RawAccepted.spec d draw hd hv).rows

omit [NeZero k] in
theorem endpoint_nonneg : 0≤endpoint (k:=k) (mult:=mult) v := by
  have hD : (0:ℝ)≤(value (diam v):ℝ) := by exact_mod_cast value_nonneg (diam v)
  have hδ : (0:ℝ)≤(value (sep v):ℝ) := by exact_mod_cast value_nonneg (sep v)
  unfold endpoint slope
  positivity

include hk hd hv in
theorem suffix (pre w : List (Fin n)) (original actual : Configuration n k) :
    expected hkn d draw hd v hv actual w≤
      (4*slope (mult:=mult) v+4)*offlineCost d original (pre++w)+endpoint (k:=k) (mult:=mult) v := by
  have hp:=RawAccepted.spec d draw hd hv
  let D : ℝ := value (diam v)
  let δ : ℝ := value (sep v)
  let A : ℝ := slope (mult:=mult) v
  let E : ℝ := (restart v)*δ
  have hD : 0≤D := by dsimp [D];exact_mod_cast value_nonneg (diam v)
  have hδ : 0≤δ := by dsimp [δ];exact_mod_cast hp.numbers.sep_pos.le
  have hA : 0≤A := by dsimp [A,slope] <;> positivity
  have hE : 0≤E := by dsimp [E] <;> positivity
  have hdiam : ∀x y,(d.distance x y:ℝ)≤D := by intro x y;dsimp [D];exact_mod_cast hp.diam_bound x y
  have hsep : ∀x y,x≠y→δ≤(d.distance x y:ℝ) := by intro x y h;dsimp [δ];exact_mod_cast hp.sep_bound x y h
  have hcap : (restart v:ℝ)*(k+1)*D≤(cap v+1:ℝ)*δ := by dsimp [D,δ];exact_mod_cast hp.numbers.cap_bound
  have hrestart : (k:ℝ)*D≤(restart v:ℝ)*δ := by dsimp [D,δ];exact_mod_cast hp.numbers.restart_bound
  have hpay : (2*A+1)*k*D+2*E+2*D≤(2*A+4)*(restart v)*δ := by
    have hk' : (2:ℝ)≤k := by exact_mod_cast hk
    have hb:=mul_le_mul_of_nonneg_left hrestart (by positivity : 0≤2*A+1)
    dsimp [E]
    nlinarith [mul_le_mul_of_nonneg_right hk' hD]
  have ht : ∀w : List (Fin n),w.length≤horizon k (cap v)→
      BitSampling.mean (BitSampling.runCost (N v) (total d draw hd v hv)
        EpochExpectation.next (EpochExpectation.charge d) ([],u hkn) w)≤
        A*offlineCost d (u hkn) w+E+D := by
    intro w hw
    rw [BitSampling.bit_path_mean]
    have hh:=RawSound.table_bound hkn d draw hd (diam v) (sep v) (table v) hp.rows hp.budget w hw
    have hn : @RawExpansion.next n k = @EpochExpectation.next n k := rfl
    have hc : @RawExpansion.charge n k d = @EpochExpectation.charge n k d := rfl
    rw [hn,hc] at hh
    simpa only [A,slope,E,D,δ,N,u,Nat.cast_mul,Nat.cast_pow,add_assoc] using hh
  have hh:=ControllerBound.suffix hk d (u hkn) (u_injective hkn) (N v)
    (total d draw hd v hv) (lazy d draw hd v hv) D δ A E hD hδ hA hdiam hsep hcap ht
    hp.numbers.restart_pos hE hpay pre w original actual
  simpa only [expected,endpoint,A,D,δ,E,mul_assoc] using hh

include hm hk hd hv in
omit [NeZero k] in
theorem coefficient_bound : 4*slope (mult:=mult) v+4≤
    OffsetInstance.coefficient mult*(Real.log (k+1))^2 := by
  have he:=(RawAccepted.spec d draw hd hv).numbers.ell_eq
  have hh:=OffsetInstance.coefficient_bound mult hm hk
  simpa only [OffsetInstance.slope,OffsetLP.slope,slope,he,Rat.cast_mul,Rat.cast_natCast,Rat.cast_pow] using hh

include hk hm hd hv in
theorem delayed_bound_oai (s : Configuration n k) (delay : ℕ) :
    ∃B : ℝ,0≤B ∧ ∀w : List (Fin n),delayed hkn d draw hd v hv s delay w≤
      OffsetInstance.coefficient mult*(Real.log (k+1))^2*offlineCost d s w+B := by
  let B : ℝ := (delay:ℝ)*(value (diam v):ℝ)+endpoint (k:=k) (mult:=mult) v
  have hp:=RawAccepted.spec d draw hd hv
  have hD : (0:ℝ)≤(value (diam v):ℝ) := by exact_mod_cast value_nonneg (diam v)
  refine ⟨B,add_nonneg (mul_nonneg (Nat.cast_nonneg _) hD) (endpoint_nonneg v),?_⟩
  intro w
  have he:=suffix hk hkn d draw hd v hv (w.take delay) (w.drop delay) s
    (UniformKServer.finish s (ComputedInstance.prefixTrace (w.take delay)))
  rw [List.take_append_drop] at he
  have ht:=OffsetInstance.history_diameter d s (ComputedInstance.prefixTrace (w.take delay))
    (value (diam v):ℝ) (fun x y=>by exact_mod_cast hp.diam_bound x y)
  have hl : (ComputedInstance.prefixTrace (k:=k) (w.take delay)).length≤delay := by
    simp [ComputedInstance.prefixTrace,List.length_take]
  have hb:=mul_le_mul_of_nonneg_right (show ((ComputedInstance.prefixTrace (k:=k) (w.take delay)).length:ℝ)≤delay by exact_mod_cast hl) hD
  have ho : 0≤offlineCost d s w := by
    rw [OfflineDynamic.offline_eq_optRat]
    exact_mod_cast EffectiveLP.opt_nonneg d s w
  have hc:=mul_le_mul_of_nonneg_right (coefficient_bound hk hm d draw hd v hv) ho
  unfold delayed
  dsimp [B]
  linarith

end UniformKServer.RawControllerCost

end


end

end OAI
end

theorem solution : type_of% @OAI.UniformKServer.RawControllerCost.delayed_bound_oai := @OAI.UniformKServer.RawControllerCost.delayed_bound_oai
