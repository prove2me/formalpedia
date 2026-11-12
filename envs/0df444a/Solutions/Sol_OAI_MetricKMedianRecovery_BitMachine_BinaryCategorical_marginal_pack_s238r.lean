-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.marginal_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:38:14.881366+00:00
-- url     : https://prove2.me/submissions/0829320a-82b9-4449-b16d-303715eee10a

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L024
import Definitions.Def_Q238L026
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCategorical_draw_pack_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MulComputes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryRational

lemma decode_encode (x : ℚ) : decode (encode x)=x := by
  simp only [decode,numerator,denominator,encode,pairBits,extractPrefix_pair,discardPrefix_pair,
    Signed.encode_decode,value_bits,Rat.mkRat_self]

end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Table
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace Categorical

open FiniteSampling
variable {E Ω : Type*} [Fintype E] [DecidableEq E] [Fintype Ω] [Nonempty Ω]

omit [Fintype E] [Fintype Ω] [Nonempty Ω] in
lemma mem_draw {a : ℕ} (r : Fin a → Table Ω E) (seed : Fin a → Ω)
    (S : Finset E) (e : E) :
    e ∈ draw a r seed S ↔ e ∈ S ∨ ∃ j, r j (seed j) = some e := by
  induction a with
  | zero => simp [draw]
  | succ a ih =>
    simp only [draw]
    have he : (∃ j : Fin (a+1), r j (seed j) = some e) ↔
      r 0 (seed 0) = some e ∨ ∃ j : Fin a, r j.succ (seed j.succ) = some e := Fin.exists_fin_succ
    rw [he]
    cases h : r 0 (seed 0) with
    | none => simpa [put, h, Fin.tail_def] using ih (Fin.tail r) (Fin.tail seed)
    | some f =>
      simp only [put, Finset.mem_insert, ih, Fin.tail_def, Option.some.injEq]
      tauto

end Categorical
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RowEncode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

attribute [local irreducible] WordList.mapWith WordList.Indices.run WordList.Lookup.run
  WordList.Fold.run IntegerArray.sumWords 
open WordOperations BinaryArithmetic
namespace WordList
lemma lookup_ofFn {n : ℕ} (i : Fin n) (f : Fin n → List Bool) :
    Lookup.run (pairBits (i.val.bits,encode (List.ofFn f)))=f i := by
  rw [Lookup.run_encode]
  simp only [List.getElem?_ofFn,i.isLt,dite_eq_left,Option.getD_some]
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalTable
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
variable {E : Type*} {a T : ℕ}
lemma drawn_toFinset [DecidableEq E] (r : Fin a→Fin T→Option E) (s : Fin a→Fin T) :
    (drawn r s).toFinset=Categorical.draw a r s ∅ := by
  ext e
  simp only [drawn,List.mem_toFinset,List.mem_flatten,List.mem_ofFn,
    Categorical.mem_draw,Finset.notMem_empty,false_or]
  aesop
lemma omitted_update (r : Fin a→Fin T→Option E) (j : Fin a) :
    omitted r j.val=Function.update r j (fun _=>none) := by
  funext i t
  by_cases hi : i=j
  · subst i; simp [omitted]
  · have hv : i.val≠j.val:=fun h=>hi (Fin.ext h)
    simp only [omitted,ite_eq_right hv,Function.update_of_ne hi]
attribute [local irreducible] Set.run mapWith
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalScore
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
variable {q a T L : ℕ}
attribute [local irreducible] mapWith
lemma elementPart_pack (ctx : List Bool) (part : Fin q→Fin a) (r : Fin a→Fin T→Option (Fin q))
    (seed : Categorical.OracleSeed (Fin q) a T L) (e : Fin q) :
    elementPart (pairBits (scorePack ctx part r seed,elemBits e))=(part e).val.bits := by
  simp only [elementPart,scorePack,elemBits,partBits,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,extractPrefix_pairBits,discardPrefix_pairBits,lookup_ofFn]
lemma marginalDraw_pack (ctx : List Bool) (part : Fin q→Fin a) (r : Fin a→Fin T→Option (Fin q))
    (seed : Categorical.OracleSeed (Fin q) a T L) (e : Fin q) (s : Fin a→Fin T) :
    marginalDraw (pairBits (pairBits (scorePack ctx part r seed,elemBits e),seedBits s))=
      encode ((drawn (Function.update r (part e) (fun _=>none)) s).map elemBits) := by
  unfold marginalDraw
  rw [extractPrefix_pairBits,elementPart_pack]
  simp only [extractPrefix_pairBits,discardPrefix_pairBits,scorePack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some]
  change draw (drawPack elemBits r s (part e).val)=_
  rw [draw_pack_s238r,omitted_update]
lemma marginal_pack_s238r_oai (g : List Bool→List Bool) (ctx : List Bool) (G : Finset (Fin q)→ℚ)
    (hg : ∀ xs : List (Fin q),g (pairBits (ctx,encode (xs.map elemBits)))=BinaryRational.encode (G xs.toFinset))
    (part : Fin q→Fin a) (r : Fin a→Fin T→Option (Fin q)) (seed : Categorical.OracleSeed (Fin q) a T L)
    (e : Fin q) (s : Fin a→Fin T) :
    marginal g (pairBits (pairBits (scorePack ctx part r seed,elemBits e),seedBits s))=
      BinaryRational.encode (rationalMarginal G part r e s) := by
  unfold marginal
  rw [marginalDraw_pack ctx part r seed e s]
  simp only [extractPrefix_pairBits,discardPrefix_pairBits,scorePack,field_encode,
    List.getElem?_cons_zero,Option.getD_some]
  change BinaryRational.encode (BinaryRational.decode (g (pairBits (ctx,encode ((e::drawn (Function.update r (part e) (fun _=>none)) s).map elemBits))))-
    BinaryRational.decode (g (pairBits (ctx,encode ((drawn (Function.update r (part e) (fun _=>none)) s).map elemBits)))))=_
  rw [hg,hg,BinaryRational.decode_encode,BinaryRational.decode_encode]
  simp only [List.toFinset_cons,drawn_toFinset,rationalMarginal]
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.marginal_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.marginal_pack_s238r_oai
