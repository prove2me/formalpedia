-- Prove2me | solution 1 for InfoSharing.Economy.sequential_vs_concurrent
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:01:47.749771+00:00
-- url     : https://prove2.me/submissions/ef04d915-c5a1-4297-b123-67c416a0cdde

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic
import Definitions.Def_InfoSharing_Shared_IsSequentialSPE
import Definitions.Def_InfoSharing_Economy_IsConcurrentOutcome
import Definitions.Def_InfoSharing_Shared_ClosedForms
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Theorems.Thm_InfoSharing_Economy_lemma_1_pricing_equilibrium
import Theorems.Thm_InfoSharing_Economy_ex_ante_profits_manufacturers
import Theorems.Thm_InfoSharing_Economy_ex_ante_profits_retailer

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
open MeasureTheory Filter
open InfoSharing.Shared
namespace InfoBase
theorem profile_cases (X : Fin 2→Status) :
    X=(fun _=> Status.uninformed) ∨ X=onlyInformed 0 ∨ X=onlyInformed 1 ∨
      X=(fun _=> Status.informed) := by
  have hv : X=![X 0,X 1] := by funext i;fin_cases i <;> rfl
  rw [hv]
  cases h₀ : X 0 <;> cases h₁ : X 1 <;>
    simp [funext_iff,Fin.forall_fin_two,onlyInformed]

theorem forall_status (p : Status→Prop) : (∀ s,p s) ↔ p Status.informed ∧ p Status.uninformed := by
  constructor
  · intro h;exact ⟨h _,h _⟩
  · rintro ⟨hi,hu⟩ s;cases s;exact hi;exact hu
theorem num_u : numInformed (fun _=> Status.uninformed)=0 := by decide
theorem num_i : numInformed (fun _=> Status.informed)=2 := by decide
theorem num_only (i : Fin 2) : numInformed (onlyInformed i)=1 := by
  fin_cases i <;> decide

end InfoBase
namespace InfoSeq
noncomputable section
abbrev I := Status.informed
abbrev U := Status.uninformed
@[simp] theorem U_ne_I : Status.uninformed ≠ Status.informed := by decide
@[simp] theorem I_ne_U : Status.informed ≠ Status.uninformed := by decide
def val (vi vu:ℝ) (d:Status) : ℝ := if d=I then vi else vu
def pay (t:ℝ) (d:Status) : ℝ := if d=I then t else 0
def buyer (mi mu t:ℝ) (d:Status) : ℝ := val mi mu d-pay t d
def seller (ri ru t:ℝ) (d:Status) : ℝ := val ri ru d+pay t d

 theorem buyer_threshold (mi mu:ℝ) (acc:ℝ → Status)
    (hacc:∀ t d,0 ≤ t → buyer mi mu t d ≤ buyer mi mu t (acc t))
    (t:ℝ) (ht:0 ≤ t) :
    (acc t=I → t ≤ mi-mu) ∧ (acc t=U → mi-mu ≤ t) := by
  have hi := hacc t I ht
  have hu := hacc t U ht
  constructor <;> intro heq <;> rw [heq] at hi hu <;>
    simp [buyer,val,pay,I,U] at hi hu <;> linarith

 theorem seller_opt_value (mi mu ri ru:ℝ) (hg:0 < mi-mu) (acc:ℝ → Status)
    (hacc:∀ t d,0 ≤ t → buyer mi mu t d ≤ buyer mi mu t (acc t))
    (t:ℝ) (ht:0 ≤ t)
    (hopt:∀ t',0 ≤ t' → seller ri ru t' (acc t') ≤ seller ri ru t (acc t)) :
    seller ri ru t (acc t)=max ru (ri+(mi-mu)) := by
  apply le_antisymm
  · cases h:acc t with
    | informed =>
      have hh := (buyer_threshold mi mu acc hacc t ht).1 h
      change ri+t ≤ max ru (ri+(mi-mu))
      exact (by linarith : ri+t ≤ ri+(mi-mu)).trans (le_max_right _ _)
    | uninformed => simpa [seller,val,pay,I,U,h] using le_max_left ru (ri+(mi-mu))
  · apply max_le
    · have hp:0 ≤ mi-mu+1 := by linarith
      have hu : acc (mi-mu+1)=U := by
        cases heq:acc (mi-mu+1) with
        | uninformed => rfl
        | informed =>
          have hh := (buyer_threshold mi mu acc hacc _ hp).1 heq
          linarith
      have hh := hopt (mi-mu+1) hp
      simpa [seller,val,pay,I,U,hu] using hh
    · apply le_of_forall_pos_le_add
      intro eps heps
      let eta := min ((mi-mu)/2) (eps/2)
      have heta : 0 < eta := by dsimp [eta]; positivity
      have hetag : eta ≤ (mi-mu)/2 := min_le_left _ _
      have hetae : eta ≤ eps/2 := min_le_right _ _
      have hp : 0 ≤ mi-mu-eta := by linarith
      have hi : acc (mi-mu-eta)=I := by
        cases heq:acc (mi-mu-eta) with
        | informed => rfl
        | uninformed =>
          have hh := (buyer_threshold mi mu acc hacc _ hp).2 heq
          linarith
      have hh := hopt (mi-mu-eta) hp
      rw [hi] at hh
      change ri+(mi-mu-eta) ≤ seller ri ru t (acc t) at hh
      linarith

 theorem seller_opt_status (mi mu ri ru:ℝ) (hg:0 < mi-mu) (acc:ℝ → Status)
    (hacc:∀ t d,0 ≤ t → buyer mi mu t d ≤ buyer mi mu t (acc t))
    (t:ℝ) (ht:0 ≤ t)
    (hopt:∀ t',0 ≤ t' → seller ri ru t' (acc t') ≤ seller ri ru t (acc t)) :
    (ri+(mi-mu) < ru → acc t=U) ∧ (ru < ri+(mi-mu) → acc t=I) ∧
      (acc t=I → t=mi-mu) := by
  have hv := seller_opt_value mi mu ri ru hg acc hacc t ht hopt
  have hb := buyer_threshold mi mu acc hacc t ht
  refine ⟨?_,?_,?_⟩
  · intro hlt
    cases heq:acc t with
    | uninformed => rfl
    | informed =>
      have hle := hb.1 heq
      rw [heq] at hv
      simp [seller,val,pay,I,U,max_eq_left hlt.le] at hv
      linarith
  · intro hlt
    cases heq:acc t with
    | informed => rfl
    | uninformed =>
      rw [heq] at hv
      simp [seller,val,pay,I,U,max_eq_right hlt.le] at hv
      linarith
  · intro hi
    have hle := hb.1 hi
    rw [hi] at hv
    change ri+t=max ru (ri+(mi-mu)) at hv
    have hge := le_max_right ru (ri+(mi-mu))
    linarith

 def accept (g t:ℝ) : Status := if t ≤ g then I else U
 theorem accept_opt (mi mu:ℝ) :
    ∀ t d,0 ≤ t → buyer mi mu t d ≤ buyer mi mu t (accept (mi-mu) t) := by
  intro t d ht
  unfold accept
  split_ifs with h
  · cases d <;> simp [buyer,val,pay,I,U] <;> linarith
  · cases d <;> simp [buyer,val,pay,I,U] <;> linarith


def table (m0 mu mi m2 r0 r1 r2 : ℝ) : PayoffTable where
  M X i := if X i=I then (if X (other i)=I then m2 else mi)
    else (if X (other i)=I then mu else m0)
  R X := if numInformed X=0 then r0 else if numInformed X=1 then r1 else r2

 theorem second_pay (m0 mu mi m2 r0 r1 r2 Tf Ts:ℝ) (k:Fin 2) (dk ds:Status) :
    seqMfrPayoff (table m0 mu mi m2 r0 r1 r2) k Tf dk Ts ds (other k)=
      buyer (val m2 mi dk) (val mu m0 dk) Ts ds := by
  fin_cases k <;> cases dk <;> cases ds <;>
    norm_num [seqMfrPayoff,seqProfile,table,buyer,val,pay,I,U,other]

 theorem first_pay (m0 mu mi m2 r0 r1 r2 Tf Ts:ℝ) (k:Fin 2) (dk ds:Status) :
    seqMfrPayoff (table m0 mu mi m2 r0 r1 r2) k Tf dk Ts ds k=
      buyer (val m2 mi ds) (val mu m0 ds) Tf dk := by
  fin_cases k <;> cases dk <;> cases ds <;>
    norm_num [seqMfrPayoff,seqProfile,table,buyer,val,pay,I,U,other]

 theorem ret_pay (m0 mu mi m2 r0 r1 r2 Tf Ts:ℝ) (k:Fin 2) (dk ds:Status) :
    seqRetPayoff (table m0 mu mi m2 r0 r1 r2) k Tf dk Ts ds=
      seller (val r2 r1 dk) (val r1 r0 dk) Ts ds+pay Tf dk := by
  fin_cases k <;> cases dk <;> cases ds <;>
    norm_num [seqRetPayoff,seqProfile,table,seller,val,pay,I,U,other,numInformed,
      Finset.univ_fin2,Finset.filter_insert,Finset.filter_singleton] <;> ring

 theorem second_optimal (m0 mu mi m2 r0 r1 r2:ℝ) (k:Fin 2) (s:SeqStrategy)
    (hs:IsSequentialSPE (table m0 mu mi m2 r0 r1 r2) k s)
    (Tf:ℝ) (hTf:0 ≤ Tf) (dk:Status) :
    (∀ t d,0 ≤ t → buyer (val m2 mi dk) (val mu m0 dk) t d ≤
      buyer (val m2 mi dk) (val mu m0 dk) t (s.accS Tf dk t)) ∧
    0 ≤ s.Ts Tf dk ∧
    (∀ t,0 ≤ t → seller (val r2 r1 dk) (val r1 r0 dk) t (s.accS Tf dk t) ≤
      seller (val r2 r1 dk) (val r1 r0 dk) (s.Ts Tf dk) (s.accS Tf dk (s.Ts Tf dk))) := by
  refine ⟨?_,(hs.2.1 Tf dk hTf).1,?_⟩
  · intro t d ht
    simpa only [second_pay] using hs.1 Tf dk t d hTf ht
  · intro t ht
    have hh := (hs.2.1 Tf dk hTf).2 t ht
    simpa only [ret_pay,add_le_add_iff_right] using hh

 theorem second_characterization (m0 mu mi m2 r0 r1 r2:ℝ)
    (hg0:0 < mi-m0) (hg1:0 < m2-mu) (k:Fin 2) (s:SeqStrategy)
    (hs:IsSequentialSPE (table m0 mu mi m2 r0 r1 r2) k s)
    (Tf:ℝ) (hTf:0 ≤ Tf) (dk:Status) :
    let g:=val m2 mi dk-val mu m0 dk
    let ri:=val r2 r1 dk
    let ru:=val r1 r0 dk
    seller ri ru (s.Ts Tf dk) (s.accS Tf dk (s.Ts Tf dk))=max ru (ri+g) ∧
    (ri+g < ru → s.accS Tf dk (s.Ts Tf dk)=U) ∧
    (ru < ri+g → s.accS Tf dk (s.Ts Tf dk)=I) ∧
    (s.accS Tf dk (s.Ts Tf dk)=I → s.Ts Tf dk=g) := by
  dsimp only
  have hg : 0 < val m2 mi dk-val mu m0 dk := by
    cases dk
    · simpa [val,I,U] using hg1
    · simpa [val,I,U] using hg0
  obtain ⟨ha,ht,ho⟩ := second_optimal m0 mu mi m2 r0 r1 r2 k s hs Tf hTf dk
  exact ⟨seller_opt_value _ _ _ _ hg _ ha _ ht ho,
    seller_opt_status _ _ _ _ hg _ ha _ ht ho⟩

 theorem first_optimal (m0 mu mi m2 r0 r1 r2:ℝ) (k:Fin 2) (s:SeqStrategy)
    (hs:IsSequentialSPE (table m0 mu mi m2 r0 r1 r2) k s)
    (q:Status → Status) (V:Status → ℝ)
    (hq:∀ Tf,0 ≤ Tf → ∀ dk,s.accS Tf dk (s.Ts Tf dk)=q dk)
    (hV:∀ Tf,0 ≤ Tf → ∀ dk,
      seller (val r2 r1 dk) (val r1 r0 dk) (s.Ts Tf dk) (s.accS Tf dk (s.Ts Tf dk))=V dk) :
    (∀ t d,0 ≤ t → buyer (val m2 mi (q I)) (val mu m0 (q U)) t d ≤
      buyer (val m2 mi (q I)) (val mu m0 (q U)) t (s.accF t)) ∧
    0 ≤ s.Tf ∧
    (∀ t,0 ≤ t → seller (V I) (V U) t (s.accF t) ≤
      seller (V I) (V U) s.Tf (s.accF s.Tf)) := by
  have hmfr (t:ℝ) (ht:0 ≤ t) (d:Status) :
      seqMfrPayoff (table m0 mu mi m2 r0 r1 r2) k t d (s.Ts t d)
        (s.accS t d (s.Ts t d)) k=buyer (val m2 mi (q I)) (val mu m0 (q U)) t d := by
    rw [first_pay,hq t ht d]
    cases d <;> simp [buyer,val,pay,I,U]
  have hret (t:ℝ) (ht:0 ≤ t) (d:Status) :
      seqRetPayoff (table m0 mu mi m2 r0 r1 r2) k t d (s.Ts t d)
        (s.accS t d (s.Ts t d))=seller (V I) (V U) t d := by
    rw [ret_pay,hV t ht d]
    cases d <;> simp [seller,val,pay,I,U]
  refine ⟨?_,hs.2.2.2.1,?_⟩
  · intro t d ht
    simpa only [hmfr t ht] using hs.2.2.1 t d ht
  · intro t ht
    simpa only [hret t ht,hret s.Tf hs.2.2.2.1] using hs.2.2.2.2 t ht

end
end InfoSeq
open InfoSharing.Shared InfoSharing.Economy InfoSeq
namespace InfoEconGame
noncomputable section
 theorem ne_u (m0 mu mi m2 r0 r1 r2 T:ℝ) :
    IsPureNE (table m0 mu mi m2 r0 r1 r2) T (fun _=> U) ↔ mi-m0 ≤ T := by
  simp [IsPureNE,Fin.forall_fin_two,InfoBase.forall_status,concManufacturerPayoff,table,other,I,U]
  constructor <;> intro h <;> linarith
 theorem ne_i (m0 mu mi m2 r0 r1 r2 T:ℝ) :
    IsPureNE (table m0 mu mi m2 r0 r1 r2) T (fun _=> I) ↔ T ≤ m2-mu := by
  simp [IsPureNE,Fin.forall_fin_two,InfoBase.forall_status,concManufacturerPayoff,table,other,I,U]
  constructor <;> intro h <;> linarith
 theorem ne_only (m0 mu mi m2 r0 r1 r2 T:ℝ) (i:Fin 2) :
    IsPureNE (table m0 mu mi m2 r0 r1 r2) T (onlyInformed i) ↔ m2-mu ≤ T ∧ T ≤ mi-m0 := by
  fin_cases i <;>
    simp [IsPureNE,Fin.forall_fin_two,InfoBase.forall_status,concManufacturerPayoff,table,other,onlyInformed,I,U]
  all_goals constructor <;> intro h <;> constructor <;> linarith
 theorem ret_u (m0 mu mi m2 r0 r1 r2 T:ℝ) :
    concRetailer (table m0 mu mi m2 r0 r1 r2) T (fun _=> U)=r0 := by simp [concRetailer,table,I,U,InfoBase.num_u]
 theorem ret_i (m0 mu mi m2 r0 r1 r2 T:ℝ) :
    concRetailer (table m0 mu mi m2 r0 r1 r2) T (fun _=> I)=r2+2*T := by simp [concRetailer,table,I,U,InfoBase.num_i];ring
 theorem ret_only (m0 mu mi m2 r0 r1 r2 T:ℝ) (i:Fin 2) :
    concRetailer (table m0 mu mi m2 r0 r1 r2) T (onlyInformed i)=r1+T := by simp [concRetailer,table,InfoBase.num_only]
 theorem pareto_only (m0 mu mi m2 r0 r1 r2 T:ℝ) (i:Fin 2)
    (hlo:m2-mu < T) (hhi:T < mi-m0) :
    IsParetoOptimalNE (table m0 mu mi m2 r0 r1 r2) T (onlyInformed i) := by
  refine ⟨(ne_only _ _ _ _ _ _ _ _ _).mpr ⟨hlo.le,hhi.le⟩,?_⟩
  rintro ⟨X,hX,hw,j,hj⟩
  rcases InfoBase.profile_cases X with rfl|rfl|rfl|rfl
  · have hh:=(ne_u _ _ _ _ _ _ _ _).mp hX;linarith
  · fin_cases i <;> fin_cases j <;>
      simp [concManufacturerPayoff,table,onlyInformed,other,I,U] at hw hj <;>
      first | exact (lt_irrefl _ hj) | (linarith [hw.1,hw.2])
  · fin_cases i <;> fin_cases j <;>
      simp [concManufacturerPayoff,table,onlyInformed,other,I,U] at hw hj <;>
      first | exact (lt_irrefl _ hj) | (linarith [hw.1,hw.2])
  · have hh:=(ne_i _ _ _ _ _ _ _ _).mp hX;linarith
end
end InfoEconGame

namespace InfoSeq
noncomputable section

def chosenOfferAny (g : ℝ) (d : Status) : ℝ := if d = I then g else max g 0 + 1

theorem chosen_opt_any (g ri ru : ℝ) (d : Status)
    (hdI : d = I → 0 ≤ g ∧ ru ≤ ri + g)
    (hdU : d = U → g < 0 ∨ ri + g ≤ ru) :
    0 ≤ chosenOfferAny g d ∧ accept g (chosenOfferAny g d) = d ∧
    ∀ t, 0 ≤ t → seller ri ru t (accept g t) ≤ seller ri ru (chosenOfferAny g d) d := by
  cases d with
  | informed =>
    obtain ⟨hg, hr⟩ := hdI rfl
    refine ⟨by simpa [chosenOfferAny] using hg, by simp [chosenOfferAny, accept], ?_⟩
    intro t ht
    by_cases htg : t ≤ g
    · simp [chosenOfferAny, accept, seller, val, pay, I, U, htg] <;> linarith
    · simpa [chosenOfferAny, accept, seller, val, pay, I, U, htg] using hr
  | uninformed =>
    have hgg : ¬ max g 0 + 1 ≤ g := by linarith [le_max_left g 0]
    refine ⟨by simp [chosenOfferAny, I, U]; positivity,
      by simp [chosenOfferAny, accept, I, U, hgg], ?_⟩
    intro t ht
    by_cases htg : t ≤ g
    · obtain hneg | hr := hdU rfl
      · linarith
      · simp [chosenOfferAny, accept, seller, val, pay, I, U, htg] <;> linarith
    · simp [chosenOfferAny, accept, seller, val, pay, I, U, htg]

theorem exists_seq_any (m0 mu mi m2 r0 r1 r2 : ℝ) (k : Fin 2) :
    ∃ s : SeqStrategy, IsSequentialSPE (table m0 mu mi m2 r0 r1 r2) k s := by
  let g := fun z ↦ val m2 mi z - val mu m0 z
  let q := fun z ↦ if 0 ≤ g z ∧ val r1 r0 z ≤ val r2 r1 z + g z then I else U
  have hqI (z : Status) : q z = I → 0 ≤ g z ∧ val r1 r0 z ≤ val r2 r1 z + g z := by
    simp only [q, ite_eq_left_iff, U_ne_I, imp_false, not_not]; exact id
  have hqU (z : Status) : q z = U → g z < 0 ∨ val r2 r1 z + g z ≤ val r1 r0 z := by
    intro hh
    by_cases hg : 0 ≤ g z
    · right
      have hn : ¬ val r1 r0 z ≤ val r2 r1 z + g z := by
        intro hr
        simp [q, hg, hr, I_ne_U] at hh
      exact (lt_of_not_ge hn).le
    · exact Or.inl (lt_of_not_ge hg)
  let V := fun z ↦ val (val r2 r1 z + g z) (val r1 r0 z) (q z)
  let gf := val m2 mi (q I) - val mu m0 (q U)
  let d := if 0 ≤ gf ∧ V U ≤ V I + gf then I else U
  have hdI : d = I → 0 ≤ gf ∧ V U ≤ V I + gf := by
    simp only [d, ite_eq_left_iff, U_ne_I, imp_false, not_not]; exact id
  have hdU : d = U → gf < 0 ∨ V I + gf ≤ V U := by
    intro hh
    by_cases hg : 0 ≤ gf
    · right
      have hn : ¬ V U ≤ V I + gf := by
        intro hr
        simp [d, hg, hr, I_ne_U] at hh
      exact (lt_of_not_ge hn).le
    · exact Or.inl (lt_of_not_ge hg)
  let s : SeqStrategy := ⟨chosenOfferAny gf d, accept gf,
    (fun _ z ↦ chosenOfferAny (g z) (q z)), (fun _ z ↦ accept (g z))⟩
  have hsec (t : ℝ) (z : Status) : s.accS t z (s.Ts t z) = q z :=
    (chosen_opt_any (g z) (val r2 r1 z) (val r1 r0 z) (q z) (hqI z) (hqU z)).2.1
  have hsecV (t : ℝ) (z : Status) :
      seller (val r2 r1 z) (val r1 r0 z) (s.Ts t z) (s.accS t z (s.Ts t z)) = V z := by
    rw [hsec]
    dsimp [s, V, chosenOfferAny, seller, val, pay]
    split_ifs <;> ring
  have hfirst := chosen_opt_any gf (V I) (V U) d hdI hdU
  have hmfr (t : ℝ) (z : Status) :
      seqMfrPayoff (table m0 mu mi m2 r0 r1 r2) k t z (s.Ts t z)
        (s.accS t z (s.Ts t z)) k = buyer (val m2 mi (q I)) (val mu m0 (q U)) t z := by
    rw [first_pay, hsec]
    cases z <;> simp [buyer, val, pay, I, U]
  have hret (t : ℝ) (z : Status) :
      seqRetPayoff (table m0 mu mi m2 r0 r1 r2) k t z (s.Ts t z)
        (s.accS t z (s.Ts t z)) = seller (V I) (V U) t z := by
    rw [ret_pay, hsecV]
    cases z <;> simp [seller, val, pay, I, U]
  refine ⟨s, ⟨?_, ?_, ?_, hfirst.1, ?_⟩⟩
  · intro Tf z Ts d' hTf hTs
    rw [second_pay, second_pay]
    exact accept_opt _ _ Ts d' hTs
  · intro Tf z hTf
    have hh := chosen_opt_any (g z) (val r2 r1 z) (val r1 r0 z) (q z) (hqI z) (hqU z)
    refine ⟨hh.1, ?_⟩
    intro Ts hTs
    rw [ret_pay, ret_pay, hsec]
    exact add_le_add (hh.2.2 Ts hTs) (le_refl (pay Tf z))
  · intro Tf z hTf
    rw [hmfr, hmfr]
    exact accept_opt _ _ Tf z hTf
  · intro Tf hTf
    rw [hret, hret]
    change seller (V I) (V U) Tf (accept gf Tf) ≤
      seller (V I) (V U) (chosenOfferAny gf d) (accept gf (chosenOfferAny gf d))
    rw [hfirst.2.1]
    exact hfirst.2.2 Tf hTf

end
end InfoSeq

open InfoSharing.Shared InfoSharing.Economy InfoSeq
namespace InfoEconGame
noncomputable section

theorem pareto_i_low (m0 mu mi m2 r0 r1 r2 T : ℝ)
    (h0 : T < mi - m0) (h1 : T < m2 - mu) :
    IsParetoOptimalNE (table m0 mu mi m2 r0 r1 r2) T (fun _ ↦ I) := by
  refine ⟨(ne_i ..).mpr h1.le, ?_⟩
  rintro ⟨X, hX, hweak, i, hstrict⟩
  rcases InfoBase.profile_cases X with rfl | rfl | rfl | rfl
  · have hh := (ne_u ..).mp hX; linarith
  · have hh := (ne_only ..).mp hX; linarith [hh.1]
  · have hh := (ne_only ..).mp hX; linarith [hh.1]
  · exact (lt_irrefl _ hstrict)

theorem pareto_u_high (m0 mu mi m2 r0 r1 r2 T : ℝ)
    (h0 : mi - m0 < T) (h1 : m2 - mu < T) :
    IsParetoOptimalNE (table m0 mu mi m2 r0 r1 r2) T (fun _ ↦ U) := by
  refine ⟨(ne_u ..).mpr h0.le, ?_⟩
  rintro ⟨X, hX, hweak, i, hstrict⟩
  rcases InfoBase.profile_cases X with rfl | rfl | rfl | rfl
  · exact (lt_irrefl _ hstrict)
  · have hh := (ne_only ..).mp hX; linarith [hh.2]
  · have hh := (ne_only ..).mp hX; linarith [hh.2]
  · have hh := (ne_i ..).mp hX; linarith

theorem approx_zero (m0 mu mi m2 r0 r1 r2 : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ T X, 0 ≤ T ∧ IsParetoOptimalNE (table m0 mu mi m2 r0 r1 r2) T X ∧
      r0 < concRetailer (table m0 mu mi m2 r0 r1 r2) T X + ε := by
  let T := max 0 (max (mi - m0) (m2 - mu)) + 1
  have h0 : mi - m0 < T := by dsimp [T]; linarith [le_max_right 0 (max (mi-m0) (m2-mu)), le_max_left (mi-m0) (m2-mu)]
  have h1 : m2 - mu < T := by dsimp [T]; linarith [le_max_right 0 (max (mi-m0) (m2-mu)), le_max_right (mi-m0) (m2-mu)]
  refine ⟨T, fun _ ↦ U, by dsimp [T]; linarith [le_max_left 0 (max (mi-m0) (m2-mu))],
    pareto_u_high _ _ _ _ _ _ _ _ h0 h1, ?_⟩
  rw [ret_u]; linarith

theorem approx_one (m0 mu mi m2 r0 r1 r2 : ℝ) (hg0 : 0 < mi - m0)
    (hg : m2 - mu < mi - m0) (ε : ℝ) (hε : 0 < ε) :
    ∃ T X, 0 ≤ T ∧ IsParetoOptimalNE (table m0 mu mi m2 r0 r1 r2) T X ∧
      r1 + (mi - m0) < concRetailer (table m0 mu mi m2 r0 r1 r2) T X + ε := by
  let η := min ((mi-m0)/2) (min ((mi-m0-(m2-mu))/2) (ε/2))
  have hη : 0 < η := by dsimp [η]; positivity
  have hη0 : η ≤ (mi-m0)/2 := min_le_left _ _
  have hη1 : η ≤ (mi-m0-(m2-mu))/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηε : η ≤ ε/2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨mi-m0-η, onlyInformed 0, by linarith,
    pareto_only _ _ _ _ _ _ _ _ 0 (by linarith) (by linarith), ?_⟩
  rw [ret_only]; linarith

theorem approx_two (m0 mu mi m2 r0 r1 r2 : ℝ) (hg0 : 0 < mi - m0)
    (hg1 : 0 < m2 - mu) (ε : ℝ) (hε : 0 < ε) :
    ∃ T X, 0 ≤ T ∧ IsParetoOptimalNE (table m0 mu mi m2 r0 r1 r2) T X ∧
      r2 + 2 * min (mi - m0) (m2 - mu) <
        concRetailer (table m0 mu mi m2 r0 r1 r2) T X + ε := by
  let g := min (mi-m0) (m2-mu)
  have hg : 0 < g := lt_min hg0 hg1
  let η := min (g/2) (ε/4)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηg : η ≤ g/2 := min_le_left _ _
  have hηε : η ≤ ε/4 := min_le_right _ _
  refine ⟨g-η, fun _ ↦ I, by linarith,
    pareto_i_low _ _ _ _ _ _ _ _ (by linarith [min_le_left (mi-m0) (m2-mu)])
      (by linarith [min_le_right (mi-m0) (m2-mu)]), ?_⟩
  rw [ret_i]; change r2+2*g < r2+2*(g-η)+ε; linarith

theorem ne_ret_bound (m0 mu mi m2 r0 r1 r2 T : ℝ) (X : Fin 2 → Status)
    (hX : IsPureNE (table m0 mu mi m2 r0 r1 r2) T X) :
    concRetailer (table m0 mu mi m2 r0 r1 r2) T X ≤
      max r0 (max (r1+(mi-m0)) (r2+2*(m2-mu))) := by
  rcases InfoBase.profile_cases X with rfl | rfl | rfl | rfl
  · rw [ret_u]; exact le_max_left _ _
  · have hh := (ne_only ..).mp hX
    rw [ret_only]
    exact (by linarith [hh.2] : r1+T ≤ r1+(mi-m0)).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · have hh := (ne_only ..).mp hX
    rw [ret_only]
    exact (by linarith [hh.2] : r1+T ≤ r1+(mi-m0)).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · have hh := (ne_i ..).mp hX
    rw [ret_i]
    exact (by linarith : r2+2*T ≤ r2+2*(m2-mu)).trans
      ((le_max_right _ _).trans (le_max_right _ _))

theorem pareto_upper_high (m0 mu mi m2 r0 r1 r2 : ℝ)
    (hmi : m2 < mi) (hg : mi-m0 ≤ m2-mu) (T : ℝ) (X : Fin 2 → Status)
    (hX : IsParetoOptimalNE (table m0 mu mi m2 r0 r1 r2) T X) :
    concRetailer (table m0 mu mi m2 r0 r1 r2) T X ≤ max r0 (r2+2*(mi-m0)) := by
  have hmu : mu < m0 := by linarith
  have hnot (i : Fin 2) (hXi : X = onlyInformed i) : False := by
    subst X
    obtain ⟨hlo,hhi⟩ := (ne_only ..).mp hX.1
    have ht : T = mi-m0 := by linarith
    apply hX.2
    refine ⟨fun _ ↦ U, (ne_u ..).mpr (by linarith), ?_, ?_⟩
    · intro j
      fin_cases i <;> fin_cases j <;>
        simp [concManufacturerPayoff, table, onlyInformed, other, I, U, ht] <;> linarith
    · refine ⟨other i, ?_⟩
      fin_cases i <;> simp [concManufacturerPayoff, table, onlyInformed, other, I, U, ht] <;> linarith
  rcases InfoBase.profile_cases X with hh | hh | hh | hh
  · subst X; rw [ret_u]; exact le_max_left _ _
  · exact (hnot 0 hh).elim
  · exact (hnot 1 hh).elim
  · subst X
    have ht : T < mi-m0 := by
      by_contra hn
      have hT : mi-m0 ≤ T := le_of_not_gt hn
      apply hX.2
      refine ⟨fun _ ↦ U, (ne_u ..).mpr hT, ?_, 0, ?_⟩
      · intro i; simp [concManufacturerPayoff, table, I, U]; linarith
      · simp [concManufacturerPayoff, table, I, U]; linarith
    rw [ret_i]
    exact (by linarith : r2+2*T ≤ r2+2*(mi-m0)).trans (le_max_right _ _)

theorem conc_upper_high (m0 mu mi m2 r0 r1 r2 : ℝ)
    (hmi : m2 < mi) (hg : mi-m0 ≤ m2-mu) (T : ℝ) (X : Fin 2 → Status)
    (hX : IsConcurrentOutcome (table m0 mu mi m2 r0 r1 r2) T X) :
    concRetailer (table m0 mu mi m2 r0 r1 r2) T X ≤ max r0 (r2+2*(mi-m0)) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨T',X',hT',hX',hh⟩ := hX.2.2.2 ε hε
  have hb := pareto_upper_high _ _ _ _ _ _ _ hmi hg T' X' hX'
  linarith

theorem conc_lower_one (m0 mu mi m2 r0 r1 r2 : ℝ) (hg0 : 0 < mi-m0)
    (hg : m2-mu < mi-m0) (T : ℝ) (X : Fin 2 → Status)
    (hX : IsConcurrentOutcome (table m0 mu mi m2 r0 r1 r2) T X) :
    r1+(mi-m0) ≤ concRetailer (table m0 mu mi m2 r0 r1 r2) T X := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨T',X',hT',hX',hh⟩ := approx_one _ _ _ _ _ _ _ hg0 hg ε hε
  have hb := hX.2.2.1 T' X' hT' hX'
  linarith

end
end InfoEconGame

namespace InfoSeq
noncomputable section

theorem seller_inactive (mi mu ri ru : ℝ) (acc : ℝ → Status)
    (hacc : ∀ t d, 0 ≤ t → buyer mi mu t d ≤ buyer mi mu t (acc t))
    (t : ℝ) (ht : 0 ≤ t)
    (hopt : ∀ t', 0 ≤ t' → seller ri ru t' (acc t') ≤ seller ri ru t (acc t))
    (hgap : ri+(mi-mu) < ru) : acc t = U := by
  let t' := max (mi-mu) 0 + 1
  have ht' : 0 ≤ t' := by dsimp [t']; positivity
  have hlarge : mi-mu < t' := by dsimp [t']; linarith [le_max_left (mi-mu) 0]
  have hrefuse : acc t' = U := by
    cases h : acc t' with
    | uninformed => rfl
    | informed => have hh := (buyer_threshold mi mu acc hacc t' ht').1 h; linarith
  cases h : acc t with
  | uninformed => rfl
  | informed =>
    have hb := (buyer_threshold mi mu acc hacc t ht).1 h
    have ho := hopt t' ht'
    simp [hrefuse, h, seller, val, pay, I, U] at ho
    linarith

theorem second_inactive (m0 mu mi m2 r0 r1 r2 : ℝ) (k : Fin 2) (s : SeqStrategy)
    (hs : IsSequentialSPE (table m0 mu mi m2 r0 r1 r2) k s)
    (t : ℝ) (ht : 0 ≤ t) (d : Status)
    (hgap : val r2 r1 d + (val m2 mi d - val mu m0 d) < val r1 r0 d) :
    s.accS t d (s.Ts t d) = U := by
  obtain ⟨ha, hT, ho⟩ := second_optimal _ _ _ _ _ _ _ k s hs t ht d
  exact seller_inactive _ _ _ _ _ ha _ hT ho hgap

theorem secondU_active (m0 mu mi m2 r0 r1 r2 : ℝ) (k : Fin 2) (s : SeqStrategy)
    (hs : IsSequentialSPE (table m0 mu mi m2 r0 r1 r2) k s)
    (hg0 : 0 < mi-m0) (hA : r0 < r1+(mi-m0)) (t : ℝ) (ht : 0 ≤ t) :
    s.accS t U (s.Ts t U) = I ∧ s.Ts t U = mi-m0 := by
  obtain ⟨ha, hT, ho⟩ := second_optimal _ _ _ _ _ _ _ k s hs t ht U
  simp only [val, U, I, U_ne_I, if_false] at ha ho
  have hc := seller_opt_status mi m0 r1 r0 hg0 _ ha _ hT ho
  have he := hc.2.1 hA
  exact ⟨he, hc.2.2 he⟩

theorem secondI_active (m0 mu mi m2 r0 r1 r2 : ℝ) (k : Fin 2) (s : SeqStrategy)
    (hs : IsSequentialSPE (table m0 mu mi m2 r0 r1 r2) k s)
    (hg1 : 0 < m2-mu) (hB : r1 < r2+(m2-mu)) (t : ℝ) (ht : 0 ≤ t) :
    s.accS t I (s.Ts t I) = I ∧ s.Ts t I = m2-mu := by
  obtain ⟨ha, hT, ho⟩ := second_optimal _ _ _ _ _ _ _ k s hs t ht I
  simp only [val, ite_true] at ha ho
  have hc := seller_opt_status m2 mu r2 r1 hg1 _ ha _ hT ho
  have he := hc.2.1 hB
  exact ⟨he, hc.2.2 he⟩

theorem total_pay (m0 mu mi m2 r0 r1 r2 Tf Ts : ℝ) (k : Fin 2) (d e : Status) :
    (∑ i : Fin 2, seqMfrPayoff (table m0 mu mi m2 r0 r1 r2) k Tf d Ts e i) =
    if d = I then (if e = I then 2*m2-Tf-Ts else mi+mu-Tf)
    else (if e = I then mi+mu-Ts else 2*m0) := by
  fin_cases k <;> cases d <;> cases e <;>
    norm_num [Fin.sum_univ_two, seqMfrPayoff, seqProfile, table, I, U, other] <;> ring

theorem seq_low (m0 mu mi m2 r0 r1 r2 : ℝ) (k : Fin 2) (s : SeqStrategy)
    (hs : IsSequentialSPE (table m0 mu mi m2 r0 r1 r2) k s)
    (hA : r1+(mi-m0) < r0) (hB : r2+(m2-mu) < r1) :
    seqRetailer (table m0 mu mi m2 r0 r1 r2) k s = r0 ∧
    seqManufacturersTotal (table m0 mu mi m2 r0 r1 r2) k s = 2*m0 := by
  have hq (t : ℝ) (ht : 0 ≤ t) (d : Status) : s.accS t d (s.Ts t d) = U := by
    apply second_inactive _ _ _ _ _ _ _ k s hs t ht d
    cases d with
    | informed => simpa [val, I, U] using hB
    | uninformed => simpa [val, I, U] using hA
  have hV (t : ℝ) (ht : 0 ≤ t) (d : Status) :
      seller (val r2 r1 d) (val r1 r0 d) (s.Ts t d) (s.accS t d (s.Ts t d)) = val r1 r0 d := by
    rw [hq t ht d]; simp [seller, val, pay, I, U]
  obtain ⟨ha, ht, ho⟩ := first_optimal _ _ _ _ _ _ _ k s hs (fun _ ↦ U) (val r1 r0) hq hV
  simp only [val, U, I, U_ne_I, if_false] at ha ho
  have hf := seller_inactive mi m0 r1 r0 s.accF ha s.Tf ht ho hA
  have he := hq s.Tf ht U
  constructor
  · simp [seqRetailer, hf, he, ret_pay, seller, val, pay, I, U]
  · simp only [seqManufacturersTotal, hf, he, total_pay, I, U_ne_I, if_false]

end
end InfoSeq

open InfoSharing.Shared InfoSharing.Economy InfoSeq
namespace InfoEconGame
noncomputable section

theorem mfr_u (m0 mu mi m2 r0 r1 r2 T : ℝ) :
    concManufacturersTotal (table m0 mu mi m2 r0 r1 r2) T (fun _ ↦ U) = 2*m0 := by
  simp [concManufacturersTotal, concManufacturerPayoff, table, I, U, Fin.sum_univ_two] <;> ring

theorem mfr_i (m0 mu mi m2 r0 r1 r2 T : ℝ) :
    concManufacturersTotal (table m0 mu mi m2 r0 r1 r2) T (fun _ ↦ I) = 2*m2-2*T := by
  simp [concManufacturersTotal, concManufacturerPayoff, table, I, U, Fin.sum_univ_two] <;> ring

theorem mfr_only (m0 mu mi m2 r0 r1 r2 T : ℝ) (i : Fin 2) :
    concManufacturersTotal (table m0 mu mi m2 r0 r1 r2) T (onlyInformed i) = mi+mu-T := by
  fin_cases i <;>
    norm_num [concManufacturersTotal, concManufacturerPayoff, table, I, U, Fin.sum_univ_two,
      onlyInformed, other] <;> ring

def largeFee (m0 mu mi m2 : ℝ) : ℝ := max 0 (max (mi-m0) (m2-mu)) + 1

theorem largeFee_valid (m0 mu mi m2 r0 r1 r2 : ℝ) :
    0 ≤ largeFee m0 mu mi m2 ∧
      IsParetoOptimalNE (table m0 mu mi m2 r0 r1 r2) (largeFee m0 mu mi m2) (fun _ ↦ U) := by
  have h0 : mi-m0 < largeFee m0 mu mi m2 := by
    dsimp [largeFee]; linarith [le_max_right 0 (max (mi-m0) (m2-mu)), le_max_left (mi-m0) (m2-mu)]
  have h1 : m2-mu < largeFee m0 mu mi m2 := by
    dsimp [largeFee]; linarith [le_max_right 0 (max (mi-m0) (m2-mu)), le_max_right (mi-m0) (m2-mu)]
  exact ⟨by dsimp [largeFee]; positivity, pareto_u_high _ _ _ _ _ _ _ _ h0 h1⟩

theorem conc_lower_zero (m0 mu mi m2 r0 r1 r2 T : ℝ) (X : Fin 2 → Status)
    (hX : IsConcurrentOutcome (table m0 mu mi m2 r0 r1 r2) T X) :
    r0 ≤ concRetailer (table m0 mu mi m2 r0 r1 r2) T X := by
  obtain ⟨hT, hP⟩ := largeFee_valid m0 mu mi m2 r0 r1 r2
  simpa only [ret_u] using hX.2.2.1 _ _ hT hP

theorem exists_conc_low (m0 mu mi m2 r0 r1 r2 : ℝ)
    (hA : r1+(mi-m0) ≤ r0) (hC : r2+2*(m2-mu) ≤ r0) :
    ∃ T X, IsConcurrentOutcome (table m0 mu mi m2 r0 r1 r2) T X := by
  obtain ⟨hT, hP⟩ := largeFee_valid m0 mu mi m2 r0 r1 r2
  refine ⟨largeFee m0 mu mi m2, fun _ ↦ U, hT, hP.1, ?_, ?_⟩
  · intro T X hT hX
    rw [ret_u]
    exact (ne_ret_bound _ _ _ _ _ _ _ T X hX.1).trans (max_le le_rfl (max_le hA hC))
  · intro ε hε
    refine ⟨largeFee m0 mu mi m2, fun _ ↦ U, hT, hP, ?_⟩
    rw [ret_u]; linarith

theorem conc_low (m0 mu mi m2 r0 r1 r2 T : ℝ) (X : Fin 2 → Status)
    (hX : IsConcurrentOutcome (table m0 mu mi m2 r0 r1 r2) T X)
    (hA : r1+(mi-m0) < r0) (hC : r2+2*(m2-mu) < r0) :
    concRetailer (table m0 mu mi m2 r0 r1 r2) T X = r0 ∧
      concManufacturersTotal (table m0 mu mi m2 r0 r1 r2) T X = 2*m0 := by
  have hl := conc_lower_zero _ _ _ _ _ _ _ T X hX
  rcases InfoBase.profile_cases X with rfl | rfl | rfl | rfl
  · exact ⟨ret_u .., mfr_u ..⟩
  · have hh := (ne_only ..).mp hX.2.1; rw [ret_only] at hl; linarith [hh.2]
  · have hh := (ne_only ..).mp hX.2.1; rw [ret_only] at hl; linarith [hh.2]
  · have hh := (ne_i ..).mp hX.2.1; rw [ret_i] at hl; linarith

theorem exists_conc_high (m0 mu mi m2 r0 r1 r2 : ℝ)
    (hg0 : 0 < mi-m0) (hmi : m2 < mi) (hA : r0 < r1+(mi-m0))
    (hneg : m2-mu ≤ 0 → r2 < r1) :
    ∃ T X, IsConcurrentOutcome (table m0 mu mi m2 r0 r1 r2) T X := by
  by_cases hg : mi-m0 ≤ m2-mu
  · by_cases hr : r0 ≤ r2+2*(mi-m0)
    · refine ⟨mi-m0, fun _ ↦ I, hg0.le, (ne_i ..).mpr hg, ?_, ?_⟩
      · intro T X hT hX
        rw [ret_i]
        exact (pareto_upper_high _ _ _ _ _ _ _ hmi hg T X hX).trans (max_le hr le_rfl)
      · intro ε hε
        simpa only [ret_i, min_eq_left hg] using
          approx_two m0 mu mi m2 r0 r1 r2 hg0 (hg0.trans_le hg) ε hε
    · obtain ⟨hT,hP⟩ := largeFee_valid m0 mu mi m2 r0 r1 r2
      refine ⟨largeFee m0 mu mi m2, fun _ ↦ U, hT, hP.1, ?_, ?_⟩
      · intro T X hT hX
        rw [ret_u]
        exact (pareto_upper_high _ _ _ _ _ _ _ hmi hg T X hX).trans
          (max_le le_rfl (le_of_not_ge hr))
      · intro ε hε
        simpa only [ret_u] using approx_zero m0 mu mi m2 r0 r1 r2 ε hε
  · have hg' : m2-mu < mi-m0 := lt_of_not_ge hg
    by_cases hr : r2+2*(m2-mu) ≤ r1+(mi-m0)
    · refine ⟨mi-m0, onlyInformed 0, hg0.le,
        (ne_only ..).mpr ⟨hg'.le, le_rfl⟩, ?_, ?_⟩
      · intro T X hT hX
        rw [ret_only]
        exact (ne_ret_bound _ _ _ _ _ _ _ T X hX.1).trans
          (max_le hA.le (max_le le_rfl hr))
      · intro ε hε
        simpa only [ret_only] using approx_one m0 mu mi m2 r0 r1 r2 hg0 hg' ε hε
    · have hpos : 0 < m2-mu := by
        by_contra hn
        have hh := hneg (le_of_not_gt hn)
        linarith
      refine ⟨m2-mu, fun _ ↦ I, hpos.le, (ne_i ..).mpr le_rfl, ?_, ?_⟩
      · intro T X hT hX
        rw [ret_i]
        exact (ne_ret_bound _ _ _ _ _ _ _ T X hX.1).trans
          (max_le (hA.le.trans (le_of_not_ge hr)) (max_le (le_of_not_ge hr) le_rfl))
      · intro ε hε
        simpa only [ret_i, min_eq_right hg'.le] using
          approx_two m0 mu mi m2 r0 r1 r2 hg0 hpos ε hε

end
end InfoEconGame

namespace InfoSeq
noncomputable section

theorem seller_lower_reject (mi mu ri ru : ℝ) (acc : ℝ → Status)
    (hacc : ∀ t d, 0 ≤ t → buyer mi mu t d ≤ buyer mi mu t (acc t))
    (t : ℝ) (ht : 0 ≤ t)
    (hopt : ∀ t', 0 ≤ t' → seller ri ru t' (acc t') ≤ seller ri ru t (acc t)) :
    ru ≤ seller ri ru t (acc t) := by
  let t' := max (mi-mu) 0 + 1
  have ht' : 0 ≤ t' := by dsimp [t']; positivity
  have hlarge : mi-mu < t' := by dsimp [t']; linarith [le_max_left (mi-mu) 0]
  have hrefuse : acc t' = U := by
    cases h : acc t' with
    | uninformed => rfl
    | informed => have hh := (buyer_threshold mi mu acc hacc t' ht').1 h; linarith
  simpa [hrefuse, seller, val, pay, I, U] using hopt t' ht'

theorem seq_Bneg (m0 mu mi m2 r0 r1 r2 : ℝ) (k : Fin 2) (s : SeqStrategy)
    (hs : IsSequentialSPE (table m0 mu mi m2 r0 r1 r2) k s)
    (hg0 : 0 < mi-m0) (hA : r0 < r1+(mi-m0)) (hB : r2+(m2-mu) < r1) :
    r1+(mi-m0) ≤ seqRetailer (table m0 mu mi m2 r0 r1 r2) k s ∧
    seqManufacturersTotal (table m0 mu mi m2 r0 r1 r2) k s ≤ m0+mu ∧
    (mu < m0 → seqManufacturersTotal (table m0 mu mi m2 r0 r1 r2) k s ≤ 2*mu) := by
  let q := fun d ↦ if d = I then U else I
  let V := fun d ↦ if d = I then r1 else r1+(mi-m0)
  have hq (t : ℝ) (ht : 0 ≤ t) (d : Status) : s.accS t d (s.Ts t d) = q d := by
    cases d with
    | informed => exact second_inactive _ _ _ _ _ _ _ k s hs t ht I (by simpa [val] using hB)
    | uninformed => exact (secondU_active _ _ _ _ _ _ _ k s hs hg0 hA t ht).1
  have hV (t : ℝ) (ht : 0 ≤ t) (d : Status) :
      seller (val r2 r1 d) (val r1 r0 d) (s.Ts t d) (s.accS t d (s.Ts t d)) = V d := by
    rw [hq t ht d]
    cases d with
    | informed => simp [q, V, seller, val, pay, I, U]
    | uninformed =>
      rw [(secondU_active _ _ _ _ _ _ _ k s hs hg0 hA t ht).2]
      simp [q, V, seller, val, pay, I, U]
  obtain ⟨ha, ht, ho⟩ := first_optimal _ _ _ _ _ _ _ k s hs q V hq hV
  simp only [q, V, val, ite_true, U_ne_I, if_false] at ha ho
  have hr : seqRetailer (table m0 mu mi m2 r0 r1 r2) k s =
      seller r1 (r1+(mi-m0)) s.Tf (s.accF s.Tf) := by
    unfold seqRetailer
    rw [ret_pay, hV s.Tf ht]
    cases s.accF s.Tf <;> simp [V, seller, val, pay, I, U]
  have hl := seller_lower_reject mi mu r1 (r1+(mi-m0)) s.accF ha s.Tf ht ho
  refine ⟨by rwa [hr], ?_, ?_⟩
  · cases hf : s.accF s.Tf with
    | informed =>
      have he : s.accS s.Tf I (s.Ts s.Tf I) = U := hq s.Tf ht I
      simp only [hf, seller, val, pay, ite_true] at hl
      simp only [seqManufacturersTotal, hf, he, total_pay, ite_true, U_ne_I, if_false]
      linarith
    | uninformed =>
      have he := secondU_active _ _ _ _ _ _ _ k s hs hg0 hA s.Tf ht
      simp only [seqManufacturersTotal, hf, he.1, total_pay, U_ne_I, if_false, ite_true]
      rw [he.2]; linarith
  · intro hmu
    have hgf : 0 < mi-mu := by linarith
    have hc := seller_opt_status mi mu r1 (r1+(mi-m0)) hgf s.accF ha s.Tf ht ho
    have hf : s.accF s.Tf = I := hc.2.1 (by linarith)
    have hfee : s.Tf = mi-mu := hc.2.2 hf
    have he : s.accS s.Tf I (s.Ts s.Tf I) = U := hq s.Tf ht I
    simp only [seqManufacturersTotal, hf, he, total_pay, ite_true, U_ne_I, if_false]
    rw [hfee]; linarith

theorem seq_Bpos (m0 mu mi m2 r0 r1 r2 : ℝ) (k : Fin 2) (s : SeqStrategy)
    (hs : IsSequentialSPE (table m0 mu mi m2 r0 r1 r2) k s)
    (hg0 : 0 < mi-m0) (hg1 : 0 < m2-mu)
    (hA : r0 < r1+(mi-m0)) (hB : r1 < r2+(m2-mu)) :
    seqRetailer (table m0 mu mi m2 r0 r1 r2) k s =
      max (r1+(mi-m0)) (r2+2*(m2-mu)) ∧
    (seqManufacturersTotal (table m0 mu mi m2 r0 r1 r2) k s = 2*mu ∨
      (seqManufacturersTotal (table m0 mu mi m2 r0 r1 r2) k s = m0+mu ∧
        r2+2*(m2-mu) ≤ r1+(mi-m0))) := by
  let V := fun d ↦ if d = I then r2+(m2-mu) else r1+(mi-m0)
  have hq (t : ℝ) (ht : 0 ≤ t) (d : Status) : s.accS t d (s.Ts t d) = I := by
    cases d with
    | informed => exact (secondI_active _ _ _ _ _ _ _ k s hs hg1 hB t ht).1
    | uninformed => exact (secondU_active _ _ _ _ _ _ _ k s hs hg0 hA t ht).1
  have hV (t : ℝ) (ht : 0 ≤ t) (d : Status) :
      seller (val r2 r1 d) (val r1 r0 d) (s.Ts t d) (s.accS t d (s.Ts t d)) = V d := by
    rw [hq t ht d]
    cases d with
    | informed =>
      rw [(secondI_active _ _ _ _ _ _ _ k s hs hg1 hB t ht).2]
      simp [V, seller, val, pay, I, U]
    | uninformed =>
      rw [(secondU_active _ _ _ _ _ _ _ k s hs hg0 hA t ht).2]
      simp [V, seller, val, pay, I, U]
  obtain ⟨ha, ht, ho⟩ := first_optimal _ _ _ _ _ _ _ k s hs (fun _ ↦ I) V hq hV
  simp only [V, val, ite_true, U_ne_I, if_false] at ha ho
  have hr : seqRetailer (table m0 mu mi m2 r0 r1 r2) k s =
      seller (r2+(m2-mu)) (r1+(mi-m0)) s.Tf (s.accF s.Tf) := by
    unfold seqRetailer
    rw [ret_pay, hV s.Tf ht]
    cases s.accF s.Tf <;> simp [V, seller, val, pay, I, U]
  have hv := seller_opt_value m2 mu (r2+(m2-mu)) (r1+(mi-m0)) hg1 s.accF ha s.Tf ht ho
  have hc := seller_opt_status m2 mu (r2+(m2-mu)) (r1+(mi-m0)) hg1 s.accF ha s.Tf ht ho
  have hval : seqRetailer (table m0 mu mi m2 r0 r1 r2) k s =
      max (r1+(mi-m0)) (r2+2*(m2-mu)) := by rw [hr, hv]; congr 1 <;> ring
  refine ⟨hval, ?_⟩
  cases hf : s.accF s.Tf with
  | informed =>
    left
    have he := secondI_active _ _ _ _ _ _ _ k s hs hg1 hB s.Tf ht
    have hfee := hc.2.2 hf
    simp only [seqManufacturersTotal, hf, he.1, total_pay, ite_true]
    rw [he.2, hfee]; ring
  | uninformed =>
    right
    have he := secondU_active _ _ _ _ _ _ _ k s hs hg0 hA s.Tf ht
    refine ⟨?_, ?_⟩
    · simp only [seqManufacturersTotal, hf, he.1, total_pay, U_ne_I, if_false, ite_true]
      rw [he.2]; ring
    · rw [hr] at hval
      simp [hf, seller, val, pay, I, U] at hval
      exact hval

end
end InfoSeq


namespace InfoSeq
noncomputable section

theorem seq_Bzero (m0 mu mi m2 r0 r1 r2 : ℝ) (k : Fin 2) (s : SeqStrategy)
    (hs : IsSequentialSPE (table m0 mu mi m2 r0 r1 r2) k s)
    (hg0 : 0 < mi-m0) (hg1 : 0 < m2-mu) (hmi : m2 < mi)
    (hA : r0 < r1+(mi-m0)) (hB : r2+(m2-mu) = r1) :
    max (r1+(mi-m0)) (r2+2*(m2-mu)) ≤
      seqRetailer (table m0 mu mi m2 r0 r1 r2) k s := by
  have hU (t : ℝ) (ht : 0 ≤ t) : s.accS t U (s.Ts t U) = I :=
    (secondU_active _ _ _ _ _ _ _ k s hs hg0 hA t ht).1
  have hV (t : ℝ) (ht : 0 ≤ t) (d : Status) :
      seqRetPayoff (table m0 mu mi m2 r0 r1 r2) k t d (s.Ts t d)
        (s.accS t d (s.Ts t d)) =
        (if d = I then r1 else r1+(mi-m0)) + pay t d := by
    rw [ret_pay]
    have hv := (second_characterization _ _ _ _ _ _ _ hg0 hg1 k s hs t ht d).1
    rw [hv]
    cases d <;> simp [val, I, U, hB, max_eq_right hA.le]
  apply max_le
  · let t := mi-mu+1
    have ht : 0 ≤ t := by dsimp [t]; linarith
    have hf : s.accF t = U := by
      cases he : s.accF t with
      | uninformed => rfl
      | informed =>
        have hh := hs.2.2.1 t U ht
        rw [he, hU t ht, first_pay, first_pay] at hh
        cases hsec : s.accS t I (s.Ts t I) <;>
          simp [hsec, buyer, val, pay, I, U, t] at hh <;> linarith
    have hh := hs.2.2.2.2 t ht
    rw [hf, hV t ht U] at hh
    simpa [seqRetailer, pay, I, U] using hh
  · apply le_of_forall_pos_le_add
    intro ε hε
    let η := min ((m2-mu)/2) (ε/2)
    have hη : 0 < η := by dsimp [η]; positivity
    have hηg : η ≤ (m2-mu)/2 := min_le_left _ _
    have hηε : η ≤ ε/2 := min_le_right _ _
    let t := m2-mu-η
    have ht : 0 ≤ t := by dsimp [t]; linarith
    have hf : s.accF t = I := by
      cases he : s.accF t with
      | informed => rfl
      | uninformed =>
        have hh := hs.2.2.1 t I ht
        rw [he, hU t ht, first_pay, first_pay] at hh
        cases hsec : s.accS t I (s.Ts t I) <;>
          simp [hsec, buyer, val, pay, I, U, t] at hh <;> linarith
    have hh := hs.2.2.2.2 t ht
    rw [hf, hV t ht I] at hh
    change r1+t ≤ seqRetailer (table m0 mu mi m2 r0 r1 r2) k s at hh
    dsimp [t] at hh
    linarith

theorem seq_neutral (m r : ℝ) (k : Fin 2) (s : SeqStrategy)
    (hs : IsSequentialSPE (table m m m m r r r) k s) :
    seqRetailer (table m m m m r r r) k s = r ∧
      seqManufacturersTotal (table m m m m r r r) k s = 2*m := by
  have ht := hs.2.2.2.1
  have hf : s.accF s.Tf = I → s.Tf = 0 := by
    intro hh
    have hb := hs.2.2.1 s.Tf U ht
    rw [hh, first_pay, first_pay] at hb
    simp [buyer, val, pay, I, U] at hb
    linarith
  have he (d : Status) : s.accS s.Tf d (s.Ts s.Tf d) = I → s.Ts s.Tf d = 0 := by
    intro hh
    obtain ⟨ha,hT,ho⟩ := second_optimal m m m m r r r k s hs s.Tf ht d
    have hb := (buyer_threshold _ _ _ ha _ hT).1 hh
    simp [val] at hb
    linarith
  cases hF : s.accF s.Tf <;> cases hE : s.accS s.Tf (s.accF s.Tf) (s.Ts s.Tf (s.accF s.Tf))
  all_goals simp only [hF] at hE
  all_goals constructor
  all_goals simp only [seqRetailer, seqManufacturersTotal, hF, hE, ret_pay, total_pay,
    seller, val, pay, I_ne_U, U_ne_I, ite_true, if_false]
  all_goals first | (rw [he _ hE, hf hF]; ring) | (rw [hf hF]; ring) | (rw [he _ hE]; ring) | ring

end
end InfoSeq

open InfoSharing.Shared InfoSharing.Economy InfoSeq
namespace InfoEconGame
noncomputable section

theorem conc_neutral (m r T : ℝ) (X : Fin 2 → Status)
    (hX : IsConcurrentOutcome (table m m m m r r r) T X) :
    concRetailer (table m m m m r r r) T X = r ∧
      concManufacturersTotal (table m m m m r r r) T X = 2*m := by
  rcases InfoBase.profile_cases X with rfl | rfl | rfl | rfl
  · exact ⟨ret_u .., mfr_u ..⟩
  · have hh := (ne_only ..).mp hX.2.1
    have ht : T = 0 := by linarith [hX.1, hh.2]
    rw [ret_only, mfr_only, ht]; constructor <;> ring
  · have hh := (ne_only ..).mp hX.2.1
    have ht : T = 0 := by linarith [hX.1, hh.2]
    rw [ret_only, mfr_only, ht]; constructor <;> ring
  · have hh := (ne_i ..).mp hX.2.1
    have ht : T = 0 := by linarith [hX.1]
    rw [ret_i, mfr_i, ht]; constructor <;> ring

theorem comparison_high (m0 mu mi m2 r0 r1 r2 : ℝ)
    (hg0 : 0 < mi-m0) (hmi : m2 < mi) (hA : r0 < r1+(mi-m0))
    (hneg : m2-mu ≤ 0 → r2 < r1)
    (hmu : r1 < r2+(m2-mu) → mu < m0)
    (T : ℝ) (X : Fin 2 → Status) (k : Fin 2) (s : SeqStrategy)
    (hX : IsConcurrentOutcome (table m0 mu mi m2 r0 r1 r2) T X)
    (hs : IsSequentialSPE (table m0 mu mi m2 r0 r1 r2) k s) :
    concRetailer (table m0 mu mi m2 r0 r1 r2) T X ≤
      seqRetailer (table m0 mu mi m2 r0 r1 r2) k s ∧
    (r2+(m2-mu) ≠ r1 → r2+2*(m2-mu) ≠ r1+(mi-m0) →
      seqManufacturersTotal (table m0 mu mi m2 r0 r1 r2) k s ≤
        concManufacturersTotal (table m0 mu mi m2 r0 r1 r2) T X) := by
  rcases lt_trichotomy (r2+(m2-mu)) r1 with hB | hB | hB
  · obtain ⟨hl, hm, hm'⟩ := seq_Bneg _ _ _ _ _ _ _ k s hs hg0 hA hB
    have hr : concRetailer (table m0 mu mi m2 r0 r1 r2) T X ≤ r1+(mi-m0) := by
      by_cases hg : mi-m0 ≤ m2-mu
      · have hu := conc_upper_high _ _ _ _ _ _ _ hmi hg T X hX
        exact hu.trans (max_le hA.le (by linarith))
      · have hg' : m2-mu < mi-m0 := lt_of_not_ge hg
        exact (ne_ret_bound _ _ _ _ _ _ _ T X hX.2.1).trans
          (max_le hA.le (max_le le_rfl (by linarith)))
    refine ⟨hr.trans hl, ?_⟩
    intro hBn hDn
    rcases InfoBase.profile_cases X with rfl | rfl | rfl | rfl
    · rw [mfr_u]
      by_cases hg : m2-mu < mi-m0
      · have hh := conc_lower_one _ _ _ _ _ _ _ hg0 hg T (fun _ ↦ U) hX
        rw [ret_u] at hh; linarith
      · have hμ : mu < m0 := by linarith [le_of_not_gt hg]
        have hh := hm' hμ
        linarith
    · rw [mfr_only]
      have hh := (ne_only ..).mp hX.2.1
      linarith [hh.2]
    · rw [mfr_only]
      have hh := (ne_only ..).mp hX.2.1
      linarith [hh.2]
    · rw [mfr_i]
      have ht := (ne_i ..).mp hX.2.1
      by_cases hg : m2-mu < mi-m0
      · have hh := conc_lower_one _ _ _ _ _ _ _ hg0 hg T (fun _ ↦ I) hX
        rw [ret_i] at hh; linarith
      · have hμ : mu < m0 := by linarith [le_of_not_gt hg]
        have hh := hm' hμ
        linarith
  · have hg1 : 0 < m2-mu := by
      by_contra hh
      have h := hneg (le_of_not_gt hh)
      linarith
    have hl := seq_Bzero _ _ _ _ _ _ _ k s hs hg0 hg1 hmi hA hB
    have hu := ne_ret_bound _ _ _ _ _ _ _ T X hX.2.1
    refine ⟨(hu.trans (max_le (hA.le.trans (le_max_left _ _)) le_rfl)).trans hl, ?_⟩
    intro hn
    exact (hn hB).elim
  · have hg1 : 0 < m2-mu := by
      by_contra hh
      have h := hneg (le_of_not_gt hh)
      linarith
    obtain ⟨hv, hm⟩ := seq_Bpos _ _ _ _ _ _ _ k s hs hg0 hg1 hA hB
    have hμ := hmu hB
    have hu := ne_ret_bound _ _ _ _ _ _ _ T X hX.2.1
    refine ⟨?_, ?_⟩
    · rw [hv]
      exact hu.trans (max_le (hA.le.trans (le_max_left _ _)) le_rfl)
    intro hBn hDn
    have htotal : seqManufacturersTotal (table m0 mu mi m2 r0 r1 r2) k s ≤ m0+mu := by
      rcases hm with hh | ⟨hh,_⟩ <;> rw [hh] <;> linarith
    rcases InfoBase.profile_cases X with rfl | rfl | rfl | rfl
    · rw [mfr_u]; linarith
    · rw [mfr_only]
      have hh := (ne_only ..).mp hX.2.1
      linarith [hh.2]
    · rw [mfr_only]
      have hh := (ne_only ..).mp hX.2.1
      linarith [hh.2]
    · rw [mfr_i]
      have ht := (ne_i ..).mp hX.2.1
      rcases hm with hh | ⟨hh,hC⟩
      · rw [hh]; linarith
      · have hClt : r2+2*(m2-mu) < r1+(mi-m0) := lt_of_le_of_ne hC hDn
        by_cases hg : m2-mu < mi-m0
        · have hl := conc_lower_one _ _ _ _ _ _ _ hg0 hg T (fun _ ↦ I) hX
          rw [ret_i] at hl; linarith
        · have hh := le_of_not_gt hg; linarith

end
end InfoEconGame


open InfoSharing.Shared
namespace InfoEconAlgebra
noncomputable section
set_option maxHeartbeats 3000000

def bPoly (p z : ℝ) : ℝ :=
  (4*p^2+4*p+1)*z^4+(6*p^3-5*p^2-8*p-2)*z^3+
  (p^4-20*p^3-17*p^2-6*p-1)*z^2+(-6*p^4+4*p^3+5*p^2+2*p)*z+
  3*p^4+2*p^3+p^2

def dPoly (p z : ℝ) : ℝ :=
  (7*p^2+6*p+1)*z^4+(12*p^3-8*p^2-12*p-2)*z^3+
  (5*p^4-28*p^3-18*p^2-4*p-1)*z^2+(-12*p^4+6*p^3+6*p^2+2*p)*z+
  5*p^4+2*p^3+p^2

private theorem quartic_unique (a0 a1 a2 a3 a4 x y : ℝ)
    (h0 : 0 < a0) (h1 : 0 < a1) (h3 : 0 < a3) (h4 : 0 < a4)
    (hx : 0 < x) (hy : 0 < y)
    (hex : -a4*x^4-a3*x^3+a2*x^2+a1*x+a0=0)
    (hey : -a4*y^4-a3*y^3+a2*y^2+a1*y+a0=0) : x=y := by
  let K := a4*x^2*y^2*(x+y)+a3*x^2*y^2+a1*x*y+a0*(x+y)
  have hk : 0 < K := by dsimp [K]; positivity
  have hid : (x-y)*K =
      (-a4*y^4-a3*y^3+a2*y^2+a1*y+a0)*x^2-
      (-a4*x^4-a3*x^3+a2*x^2+a1*x+a0)*y^2 := by dsimp [K]; ring
  rw [hex,hey] at hid
  have : (x-y)*K=0 := by simpa using hid
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hk.ne')

private theorem b_transform (p z : ℝ) (hz : z ≠ 1) :
    bPoly p z / (1-z)^4 =
      -(2*(p+1)^4)*(z/(1-z))^4-
      (4*p^4+14*p^3+20*p^2+14*p+4)*(z/(1-z))^3+
      (p^4+4*p^3+4*p^2-1)*(z/(1-z))^2+
      (6*p^4+12*p^3+9*p^2+2*p)*(z/(1-z))+(3*p^4+2*p^3+p^2) := by
  have h : 1-z≠0 := sub_ne_zero.mpr (Ne.symm hz)
  unfold bPoly
  field_simp
  <;> ring

private theorem d_transform (p z : ℝ) (hz : z ≠ 1) :
    dPoly p z / (1-z)^4 =
      -(2*(p+1)^4)*(z/(1-z))^4-
      (6*p^4+18*p^3+22*p^2+14*p+4)*(z/(1-z))^3+
      (-p^4+2*p^3+6*p^2+2*p-1)*(z/(1-z))^2+
      (8*p^4+14*p^3+10*p^2+2*p)*(z/(1-z))+(5*p^4+2*p^3+p^2) := by
  have h : 1-z≠0 := sub_ne_zero.mpr (Ne.symm hz)
  unfold dPoly
  field_simp
  <;> ring

private theorem unit_ratio_inj (x y : ℝ) (hx : x < 1) (hy : y < 1)
    (h : x/(1-x)=y/(1-y)) : x=y := by
  have he := (div_eq_div_iff (sub_pos.mpr hx).ne' (sub_pos.mpr hy).ne').mp h
  nlinarith only [he]

theorem b_root (p : ℝ) (hp : 0 < p) :
    ∃ Z ∈ Set.Ioo (0:ℝ) 1, bPoly p Z=0 ∧
      ∀ z ∈ Set.Ioo (0:ℝ) 1, bPoly p z=0 → z=Z := by
  have h0 : 0 < bPoly p 0 := by simp only [bPoly, zero_pow (by decide : 4≠0),
    zero_pow (by decide : 3≠0), zero_pow (by decide : 2≠0), mul_zero, add_zero]; positivity
  have h1 : bPoly p 1 < 0 := by
    have he : bPoly p 1 = -2*(p+1)^4 := by unfold bPoly; ring
    rw [he]; have : 0 < (p+1)^4 := by positivity
    linarith
  have hc : Continuous (bPoly p) := by unfold bPoly; fun_prop
  obtain ⟨Z,hZ,hroot⟩ := intermediate_value_Icc' (a:=0) (b:=1) (by norm_num)
    hc.continuousOn ⟨h1.le,h0.le⟩
  have hZ0 : 0 < Z := lt_of_le_of_ne hZ.1 (by intro h; rw [←h] at hroot; linarith)
  have hZ1 : Z < 1 := lt_of_le_of_ne hZ.2 (by intro h; rw [h] at hroot; linarith)
  refine ⟨Z,⟨hZ0,hZ1⟩,hroot,?_⟩
  intro z hz he
  apply unit_ratio_inj z Z hz.2 hZ1
  apply quartic_unique (3*p^4+2*p^3+p^2) (6*p^4+12*p^3+9*p^2+2*p)
    (p^4+4*p^3+4*p^2-1) (4*p^4+14*p^3+20*p^2+14*p+4) (2*(p+1)^4)
    <;> try positivity
  · exact div_pos hz.1 (sub_pos.mpr hz.2)
  · rw [← b_transform p z (ne_of_lt hz.2),he,zero_div]
  · rw [← b_transform p Z (ne_of_lt hZ1),hroot,zero_div]

theorem d_root (p : ℝ) (hp : 0 < p) :
    ∃ Z ∈ Set.Ioo (0:ℝ) 1, dPoly p Z=0 ∧
      ∀ z ∈ Set.Ioo (0:ℝ) 1, dPoly p z=0 → z=Z := by
  have h0 : 0 < dPoly p 0 := by simp only [dPoly, zero_pow (by decide : 4≠0),
    zero_pow (by decide : 3≠0), zero_pow (by decide : 2≠0), mul_zero, add_zero]; positivity
  have h1 : dPoly p 1 < 0 := by
    have he : dPoly p 1 = -2*(p+1)^4 := by unfold dPoly; ring
    rw [he]; have : 0 < (p+1)^4 := by positivity
    linarith
  have hc : Continuous (dPoly p) := by unfold dPoly; fun_prop
  obtain ⟨Z,hZ,hroot⟩ := intermediate_value_Icc' (a:=0) (b:=1) (by norm_num)
    hc.continuousOn ⟨h1.le,h0.le⟩
  have hZ0 : 0 < Z := lt_of_le_of_ne hZ.1 (by intro h; rw [←h] at hroot; linarith)
  have hZ1 : Z < 1 := lt_of_le_of_ne hZ.2 (by intro h; rw [h] at hroot; linarith)
  refine ⟨Z,⟨hZ0,hZ1⟩,hroot,?_⟩
  intro z hz he
  apply unit_ratio_inj z Z hz.2 hZ1
  apply quartic_unique (5*p^4+2*p^3+p^2) (8*p^4+14*p^3+10*p^2+2*p)
    (-p^4+2*p^3+6*p^2+2*p-1) (6*p^4+18*p^3+22*p^2+14*p+4) (2*(p+1)^4)
    <;> try positivity
  · exact div_pos hz.1 (sub_pos.mpr hz.2)
  · rw [← d_transform p z (ne_of_lt hz.2),he,zero_div]
  · rw [← d_transform p Z (ne_of_lt hZ1),hroot,zero_div]


def mPoly (p z : ℝ) : ℝ :=
  5*p^4*z-2*p^4+4*p^2*(2*p+1)*z^2+(2*p+1)^2*z^3

def rPoly (p z : ℝ) : ℝ :=
  p^2+(p^2+2*p)*z-(2*p+1)^2*z^2-(2*p+1)*z^3

def cPoly (p z : ℝ) : ℝ :=
  (8*p^2+8*p+2)*z^4+(14*p^3-6*p^2-14*p-4)*z^3+
  (6*p^4-30*p^3-26*p^2-10*p-2)*z^2-14*p^4*z+4*p^4

theorem profit_gaps (a b c p σ β : ℝ) (hp : 0 < p) (hc : 0 < 2+(1+p)*c) :
    let z:=2+(1+p)*c
    piMI1 a b c p σ β-piM0 a b c p σ β=(z-1)^2*β*σ^2/(4*z*(1+p)) ∧
    piM0 a b c p σ β-piMU1 a b c p σ β=
      p*(z-2)*(z-1)*((3*p+2)*z-p)*β*σ^2/(4*z^2*(1+p)^3) ∧
    piM2 a b c p σ β-piMI1 a b c p σ β=
      p*(z-1)*(p*z+p+2*z)*β*σ^2/(4*z*(1+p)*(p+z)^2) ∧
    piR1 a b c p σ β+(piMI1 a b c p σ β-piM0 a b c p σ β)-piR0 a b c p σ β=
      (z-1)*(z^2-2*z-1)*β*σ^2/(4*(1+p)*z^2) ∧
    piR2 a b c p σ β+(piM2 a b c p σ β-piMU1 a b c p σ β)-piR1 a b c p σ β=
      (z-1)*bPoly p z*β*σ^2/(4*z^2*(1+p)^3*(p+z)^2) ∧
    piR2 a b c p σ β+2*(piM2 a b c p σ β-piMU1 a b c p σ β)-piR1 a b c p σ β-
        (piMI1 a b c p σ β-piM0 a b c p σ β)=
      (z-1)*dPoly p z*β*σ^2/(4*z^2*(1+p)^3*(p+z)^2) ∧
    piR2 a b c p σ β+2*(piM2 a b c p σ β-piMU1 a b c p σ β)-piR0 a b c p σ β=
      (z-1)*cPoly p z*β*σ^2/(4*z^2*(1+p)^3*(p+z)^2) ∧
    piM2 a b c p σ β-piMU1 a b c p σ β=
      (z-1)^2*mPoly p z*β*σ^2/(4*z^2*(1+p)^3*(p+z)^2) ∧
    piR2 a b c p σ β-piR1 a b c p σ β=
      (z-1)*rPoly p z*β*σ^2/(4*z^2*(1+p)*(p+z)^2) := by
  have hA : 0 < 1+p := by positivity
  have hH : 0 < p+(2+(1+p)*c) := by positivity
  have hH' : 0 < 2+p+(1+p)*c := by linarith
  have hn : 4+p*c*4+p*c^2*2+p^2*c^2+c*4+c^2≠0 := by
    have he : 4+p*c*4+p*c^2*2+p^2*c^2+c*4+c^2=(2+(1+p)*c)^2 := by ring
    rw [he]; positivity
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    simp only [piM0,piMI1,piMU1,piM2,piR0,piR1,piR2,bPoly,dPoly,cPoly,mPoly,rPoly] <;>
    field_simp (disch := (first | positivity | nlinarith [sq_pos_of_pos hc])) <;> ring

theorem m_nonpos_r_pos (p z : ℝ) (hp : 0 < p) (hz : 0 < z) (hz1 : z < 1)
    (hm : mPoly p z ≤ 0) : 0 < rPoly p z := by
  let k := (2*p+1)*z
  have hk0 : 0 < k := by dsimp [k]; positivity
  have hk : k < p := by
    by_contra hh
    have hkp : 0 ≤ k-p := sub_nonneg.mpr (le_of_not_gt hh)
    have hK : 0 < k^2+(4*p^2+p)*k+(5*p^4+4*p^3+p^2) := by positivity
    have hprod := mul_nonneg hkp hK.le
    have he : (2*p+1)*mPoly p z =
        (k-p)*(k^2+(4*p^2+p)*k+(5*p^4+4*p^3+p^2))+p^3*(p+1)^2 := by
      dsimp [mPoly,k]; ring
    have hneg := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2*p+1) hm
    have hpos : 0 < p^3*(p+1)^2 := by positivity
    linarith only [he,hneg,hprod,hpos]
  have hs : k^2 < p^2 := (sq_lt_sq₀ hk0.le hp.le).mpr hk
  have hzk1 : z*k < k := by simpa using mul_lt_mul_of_pos_right hz1 hk0
  have hzk : z*k < p := hzk1.trans hk
  have hterm : 0 < z*(p^2+2*p-z*k) := mul_pos hz (by nlinarith only [hzk,hp,sq_nonneg p])
  have he : rPoly p z = p^2-k^2+z*(p^2+2*p-z*k) := by dsimp [rPoly,k]; ring
  rw [he]
  linarith only [hs,hterm]

private theorem positive_before (f : ℝ → ℝ) (hf : Continuous f)
    (h0 : 0 < f 0) (h1 : f 1 < 0)
    (hu : ∀ x ∈ Set.Ioo (0:ℝ) 1, ∀ y ∈ Set.Ioo (0:ℝ) 1,
      f x=0 → f y=0 → x=y)
    (b z : ℝ) (hb : b ∈ Set.Ioo (0:ℝ) 1) (hfb : 0 < f b)
    (hz : 0 < z) (hzb : z ≤ b) : 0 < f z := by
  by_contra hn
  have hfn : f z ≤ 0 := le_of_not_gt hn
  obtain ⟨X,hX,hfX⟩ := intermediate_value_Icc' (a:=0) (b:=z) hz.le
    hf.continuousOn ⟨hfn,h0.le⟩
  obtain ⟨Y,hY,hfY⟩ := intermediate_value_Icc' (a:=b) (b:=1) hb.2.le
    hf.continuousOn ⟨h1.le,hfb.le⟩
  have hX0 : 0 < X := lt_of_le_of_ne hX.1 (by intro h; rw [←h] at hfX; linarith)
  have hX1 : X < 1 := hX.2.trans_lt (hzb.trans_lt hb.2)
  have hYb : b < Y := lt_of_le_of_ne hY.1 (by intro h; rw [←h] at hfY; linarith)
  have hY1 : Y < 1 := lt_of_le_of_ne hY.2 (by intro h; rw [h] at hfY; linarith)
  have he := hu X ⟨hX0,hX1⟩ Y ⟨hb.1.trans hYb,hY1⟩ hfX hfY
  linarith only [hX.2,hzb,hYb,he]

theorem b_positive_small (p z : ℝ) (hp : 0 < p) (hz : 0 < z)
    (hle : (3*p+2)*z ≤ p) : 0 < bPoly p z := by
  have hd : 0 < 3*p+2 := by positivity
  have hb0 : 0 < p/(3*p+2) := div_pos hp hd
  have hb1 : p/(3*p+2) < 1 := (div_lt_one hd).mpr (by linarith)
  have hfb : 0 < bPoly p (p/(3*p+2)) := by
    have he : bPoly p (p/(3*p+2)) * (3*p+2)^4 =
        90*p^8+444*p^7+908*p^6+988*p^5+606*p^4+200*p^3+28*p^2 := by
      unfold bPoly
      field_simp
      <;> ring
    have hpos : 0 < 90*p^8+444*p^7+908*p^6+988*p^5+606*p^4+200*p^3+28*p^2 := by positivity
    have : 0 < bPoly p (p/(3*p+2)) * (3*p+2)^4 := he ▸ hpos
    exact (mul_pos_iff_of_pos_right (by positivity)).mp this
  obtain ⟨Z,hZ,_,hu⟩ := b_root p hp
  have h0 : 0 < bPoly p 0 := by unfold bPoly; norm_num; positivity
  have h1 : bPoly p 1 < 0 := by
    have he : bPoly p 1 = -2*(p+1)^4 := by unfold bPoly; ring
    rw [he]; have hh : 0 < (p+1)^4 := by positivity
    linarith
  have hu' : ∀ x ∈ Set.Ioo (0:ℝ) 1, ∀ y ∈ Set.Ioo (0:ℝ) 1,
      bPoly p x=0 → bPoly p y=0 → x=y := by
    intro x hx y hy hfx hfy
    exact (hu x hx hfx).trans (hu y hy hfy).symm
  exact positive_before (bPoly p) (by unfold bPoly; fun_prop) h0 h1 hu'
    (p/(3*p+2)) z ⟨hb0,hb1⟩ hfb hz
    ((le_div_iff₀ hd).mpr (by nlinarith only [hle]))


theorem bPoly_neg (p z : ℝ) (hp : 0 < p) (hz1 : 1 < z) (hz2 : z < 2) :
    bPoly p z < 0 := by
  have hleft : 0 < z-1 := sub_pos.mpr hz1
  have hright : 0 < 2-z := sub_pos.mpr hz2
  have he : -bPoly p z = (2*p^4+8*p^3+12*p^2+8*p^1+2)*(z-1)^0*(2-z)^4 +
      (12*p^4+50*p^3+76*p^2+50*p^1+12)*(z-1)^1*(2-z)^3 +
      (23*p^4+104*p^3+164*p^2+108*p^1+25)*(z-1)^2*(2-z)^2 +
      (18*p^4+84*p^3+137*p^2+90*p^1+20)*(z-1)^3*(2-z)^1 +
      (5*p^4+22*p^3+33*p^2+20*p^1+4)*(z-1)^4*(2-z)^0 := by unfold bPoly; ring
  have hh : 0 < -bPoly p z := by rw [he]; positivity
  linarith only [hh]

theorem cPoly_neg (p z : ℝ) (hp : 0 < p) (hz1 : 1 < z) (hz2 : z < 2) :
    cPoly p z < 0 := by
  have hleft : 0 < z-1 := sub_pos.mpr hz1
  have hright : 0 < 2-z := sub_pos.mpr hz2
  have he : -cPoly p z = (4*p^4+16*p^3+24*p^2+16*p^1+4)*(z-1)^0*(2-z)^4 +
      (18*p^4+82*p^3+134*p^2+94*p^1+24)*(z-1)^1*(2-z)^3 +
      (24*p^4+138*p^3+254*p^2+190*p^1+50)*(z-1)^2*(2-z)^2 +
      (10*p^4+80*p^3+176*p^2+144*p^1+40)*(z-1)^3*(2-z)^1 +
      (8*p^3+24*p^2+24*p^1+8)*(z-1)^4*(2-z)^0 := by unfold cPoly; ring
  have hh : 0 < -cPoly p z := by rw [he]; positivity
  linarith only [hh]


theorem low_gaps (a b c p σ β : ℝ) (hp : 0 < p) (hσ : 0 < σ) (hβ : 0 < β)
    (hz1 : 1 < 2+(1+p)*c) (hz2 : 2+(1+p)*c < 2) :
    piR1 a b c p σ β+(piMI1 a b c p σ β-piM0 a b c p σ β)<piR0 a b c p σ β ∧
    piR2 a b c p σ β+(piM2 a b c p σ β-piMU1 a b c p σ β)<piR1 a b c p σ β ∧
    piR2 a b c p σ β+2*(piM2 a b c p σ β-piMU1 a b c p σ β)<piR0 a b c p σ β := by
  let z := 2+(1+p)*c
  have hz0 : 0 < z := by dsimp [z]; linarith
  have hz1' : 1 < z := hz1
  have hz2' : z < 2 := hz2
  obtain ⟨_,_,_,hA,hB,_,hC,_,_⟩ := profit_gaps a b c p σ β hp hz0
  have hpA : z^2-2*z-1 < 0 := by nlinarith [mul_pos hz0 (sub_pos.mpr hz2')]
  have hpB := bPoly_neg p z hp hz1' hz2'
  have hpC := cPoly_neg p z hp hz1' hz2'
  have hneg (q d : ℝ) (hq : q < 0) (hd : 0 < d) : (z-1)*q*β*σ^2/d < 0 := by
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (sub_pos.mpr hz1') hq) hβ)
      (sq_pos_of_pos hσ)) hd
  have hnA := hneg _ _ hpA (by positivity : 0 < 4*(1+p)*z^2)
  have hnB := hneg _ _ hpB (by positivity : 0 < 4*z^2*(1+p)^3*(p+z)^2)
  have hnC := hneg _ _ hpC (by positivity : 0 < 4*z^2*(1+p)^3*(p+z)^2)
  exact ⟨by linarith only [hA,hnA],by linarith only [hB,hnB],by linarith only [hC,hnC]⟩

theorem high_gaps (a b c p σ β : ℝ) (hp : 0 < p) (hσ : 0 < σ) (hβ : 0 < β)
    (hz0 : 0 < 2+(1+p)*c) (hz1 : 2+(1+p)*c < 1) :
    piM0 a b c p σ β < piMI1 a b c p σ β ∧
    piM2 a b c p σ β < piMI1 a b c p σ β ∧
    piR0 a b c p σ β < piR1 a b c p σ β+(piMI1 a b c p σ β-piM0 a b c p σ β) ∧
    (piM2 a b c p σ β-piMU1 a b c p σ β ≤ 0 → piR2 a b c p σ β < piR1 a b c p σ β) ∧
    (piR1 a b c p σ β < piR2 a b c p σ β+(piM2 a b c p σ β-piMU1 a b c p σ β) →
      piMU1 a b c p σ β < piM0 a b c p σ β) := by
  let z := 2+(1+p)*c
  have hz0' : 0 < z := hz0
  have hz1' : z < 1 := hz1
  have hz2 : z < 2 := by linarith
  have hzm : z-1 < 0 := sub_neg.mpr hz1'
  have hsq : 0 < (z-1)^2 := sq_pos_of_ne_zero hzm.ne
  have hden : 0 < 4*z^2*(1+p)^3*(p+z)^2 := by positivity
  have hdenR : 0 < 4*z^2*(1+p)*(p+z)^2 := by positivity
  obtain ⟨hg0,hgmu,hg2,hA,hB,_,_,hg1,hR⟩ := profit_gaps a b c p σ β hp hz0
  have hg0pos : 0 < (z-1)^2*β*σ^2/(4*z*(1+p)) := by positivity
  have hg2neg : p*(z-1)*(p*z+p+2*z)*β*σ^2/(4*z*(1+p)*(p+z)^2) < 0 := by
    apply div_neg_of_neg_of_pos _ (by positivity)
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hp hzm) (by positivity)) hβ)
      (sq_pos_of_pos hσ)
  have hpA : z^2-2*z-1 < 0 := by nlinarith [mul_pos hz0' (sub_pos.mpr hz2)]
  have hApos : 0 < (z-1)*(z^2-2*z-1)*β*σ^2/(4*(1+p)*z^2) := by
    apply div_pos _ (by positivity)
    exact mul_pos (mul_pos (mul_pos_of_neg_of_neg hzm hpA) hβ) (sq_pos_of_pos hσ)
  refine ⟨by linarith only [hg0,hg0pos],by linarith only [hg2,hg2neg],
    by linarith only [hA,hApos],?_,?_⟩
  · intro hle
    have hm : mPoly p z ≤ 0 := by
      by_contra hh
      have hh : 0 < mPoly p z := lt_of_not_ge hh
      have hx : 0 < (z-1)^2*mPoly p z*β*σ^2/(4*z^2*(1+p)^3*(p+z)^2) := by positivity
      linarith only [hg1,hle,hx]
    have hr := m_nonpos_r_pos p z hp hz0' hz1' hm
    have hx : (z-1)*rPoly p z*β*σ^2/(4*z^2*(1+p)*(p+z)^2) < 0 := by
      apply div_neg_of_neg_of_pos _ hdenR
      exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos hzm hr) hβ) (sq_pos_of_pos hσ)
    linarith only [hR,hx]
  · intro hBpos
    by_contra hh
    have hmu : piM0 a b c p σ β ≤ piMU1 a b c p σ β := le_of_not_gt hh
    have hle : (3*p+2)*z ≤ p := by
      by_contra hh
      have hgt : 0 < (3*p+2)*z-p := sub_pos.mpr (lt_of_not_ge hh)
      have hfirst : 0 < p*(z-2)*(z-1) :=
        mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hp (sub_neg.mpr hz2)) hzm
      have hx : 0 < p*(z-2)*(z-1)*((3*p+2)*z-p)*β*σ^2/(4*z^2*(1+p)^3) := by positivity
      linarith only [hgmu,hmu,hx]
    have hb := b_positive_small p z hp hz0' hle
    have hx : (z-1)*bPoly p z*β*σ^2/(4*z^2*(1+p)^3*(p+z)^2) < 0 := by
      apply div_neg_of_neg_of_pos _ hden
      exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos hzm hb) hβ) (sq_pos_of_pos hσ)
    linarith only [hB,hBpos,hx]

theorem neutral_gaps (a b c p σ β : ℝ) (hp : 0 < p) (hz : 2+(1+p)*c=1) :
    piMI1 a b c p σ β=piM0 a b c p σ β ∧
    piMU1 a b c p σ β=piM0 a b c p σ β ∧
    piM2 a b c p σ β=piM0 a b c p σ β ∧
    piR1 a b c p σ β=piR0 a b c p σ β ∧
    piR2 a b c p σ β=piR0 a b c p σ β := by
  obtain ⟨hg0,hgmu,hg2,hA,hB,_,_,_,_⟩ := profit_gaps a b c p σ β hp (by linarith)
  simp only [hz,sub_self,zero_pow (by decide : 2≠0),zero_mul,mul_zero,zero_div] at hg0 hgmu hg2 hA hB
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

end
end InfoEconAlgebra

open MeasureTheory Filter InfoSharing.Shared InfoSharing.Economy
namespace InfoEconBridge
noncomputable section
theorem cond_mul_integral {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z W : Ω→ℝ) (hZ : Measurable Z) (hW : MemLp W 2 μ)
    (f : ℝ→ℝ) (hmf : Measurable f) (hif : MemLp (fun ω=> f (Z ω)) 2 μ)
    (β : ℝ) (hc : μ[W | MeasurableSpace.comap Z inferInstance] =ᵐ[μ] fun ω=> β*Z ω) :
    (∫ ω,f (Z ω)*W ω ∂μ)=β*(∫ ω,f (Z ω)*Z ω ∂μ) := by
  let m := MeasurableSpace.comap Z inferInstance
  have hm : m ≤ mΩ := hZ.comap_le
  have hfm : StronglyMeasurable[m] (fun ω=> f (Z ω)) :=
    (hmf.comp (comap_measurable Z)).stronglyMeasurable
  have hp := condExp_mul_of_stronglyMeasurable_left hfm (hif.integrable_mul hW)
    (hW.integrable (by norm_num))
  calc
    _ = ∫ ω,(μ[(fun ω=> f (Z ω))*W | m]) ω ∂μ := by
      convert! (integral_condExp (μ:=μ) (f:=(fun ω=> f (Z ω))*W) hm).symm using 1
    _ = ∫ ω,f (Z ω)*(β*Z ω) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hp,hc] with ω hp hc
      change (μ[W | m]) ω=β*Z ω at hc
      simpa only [Pi.mul_apply,hc] using hp
    _ = β*(∫ ω,f (Z ω)*Z ω ∂μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ω
      ring

theorem signal_moments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω→ℝ) (σ β : ℝ) (h : IsSignalModel μ θ Y σ β) :
    (∫ ω,Y ω ∂μ)=0 ∧ (∫ ω,θ ω*Y ω ∂μ)=σ^2 ∧
    β*(∫ ω,Y ω^2 ∂μ)=σ^2 ∧ 0< β := by
  obtain ⟨hprob,hmθ,hmY,hiθ,hiY,hmean,hvar,hσ,hcY,hcθ⟩ := h
  haveI := hprob
  have hY : (∫ ω,Y ω ∂μ)=0 := by
    calc
      _ = ∫ ω,(μ[Y | MeasurableSpace.comap θ inferInstance]) ω ∂μ := (integral_condExp hmθ.comap_le).symm
      _ = ∫ ω,θ ω ∂μ := integral_congr_ae hcY
      _ = 0 := hmean
  have hcross : (∫ ω,θ ω*Y ω ∂μ)=σ^2 := by
    have hh := cond_mul_integral μ θ Y hmθ hiY id measurable_id hiθ 1 (by simpa using hcY)
    simpa only [id_eq,one_mul,← sq,hvar] using hh
  have hbeta : β*(∫ ω,Y ω^2 ∂μ)=σ^2 := by
    have hh := cond_mul_integral μ Y θ hmY hiθ id measurable_id hiY β hcθ
    have hcomm : (∫ ω,Y ω*θ ω ∂μ)=(∫ ω,θ ω*Y ω ∂μ) := by congr 1;funext ω;ring
    simpa only [id_eq,← sq,hcomm,hcross] using hh.symm
  have hβ : 0< β := by
    have hnn : 0≤∫ ω,Y ω^2 ∂μ := integral_nonneg (fun ω=> sq_nonneg _)
    have hσ2 : 0< σ^2 := sq_pos_of_pos hσ
    nlinarith
  exact ⟨hY,hcross,hbeta,hβ⟩


theorem pricing_family (φ ce c a b σ β : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (θ Y : Ω → ℝ) (hφ : 0 < φ) (hc : c = -ce)
    (hce : 0 < ce) (hA : ce < 2/(1+φ)) (hM : IsSignalModel μ θ Y σ β) :
    ∃ E : (Fin 2 → Status) → PricingProfile, IsPricingEqFamily μ θ Y a b c φ β E := by
  have h (X : Fin 2 → Status) :=
    (lemma_1_pricing_equilibrium φ ce c a b σ β μ θ Y hφ hc hce hA hM X).1
  choose ρ f hf using h
  exact ⟨fun X ↦ ⟨ρ X, f X⟩, hf⟩

theorem payoff_eq_table (φ ce c a b σ β : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (θ Y : Ω → ℝ) (E : (Fin 2 → Status) → PricingProfile)
    (hφ : 0 < φ) (hc : c = -ce) (hce : 0 < ce) (hA : ce < 2/(1+φ))
    (hU : ce ≠ (2+3*φ)/((1+2*φ)*(1+φ))) (hM : IsSignalModel μ θ Y σ β)
    (hE : IsPricingEqFamily μ θ Y a b c φ β E) :
    payoffTable μ θ Y a b c φ E = InfoSeq.table
      (piM0 a b c φ σ β) (piMU1 a b c φ σ β) (piMI1 a b c φ σ β)
      (piM2 a b c φ σ β) (piR0 a b c φ σ β) (piR1 a b c φ σ β)
      (piR2 a b c φ σ β) := by
  have hm (X : Fin 2 → Status) (i : Fin 2) :=
    ex_ante_profits_manufacturers φ ce c a b σ β μ θ Y E hφ hc hce hA hU hM hE X i
  have hr (X : Fin 2 → Status) :=
    ex_ante_profits_retailer φ ce c a b σ β μ θ Y E hφ hc hce hA hU hM hE X
  have hM' : (payoffTable μ θ Y a b c φ E).M = (InfoSeq.table
      (piM0 a b c φ σ β) (piMU1 a b c φ σ β) (piMI1 a b c φ σ β)
      (piM2 a b c φ σ β) (piR0 a b c φ σ β) (piR1 a b c φ σ β)
      (piR2 a b c φ σ β)).M := by
    funext X i
    rcases InfoBase.profile_cases X with rfl | rfl | rfl | rfl
    · simpa [InfoSeq.table, InfoSeq.I, InfoSeq.U] using
        (hm (fun _ ↦ Status.uninformed) i).1 InfoBase.num_u
    · fin_cases i
      · simpa [InfoSeq.table, onlyInformed, other, InfoSeq.I, InfoSeq.U] using
          (hm (onlyInformed 0) 0).2.2.1 (InfoBase.num_only 0) (by decide)
      · simpa [InfoSeq.table, onlyInformed, other, InfoSeq.I, InfoSeq.U] using
          (hm (onlyInformed 0) 1).2.1 (InfoBase.num_only 0) (by decide)
    · fin_cases i
      · simpa [InfoSeq.table, onlyInformed, other, InfoSeq.I, InfoSeq.U] using
          (hm (onlyInformed 1) 0).2.1 (InfoBase.num_only 1) (by decide)
      · simpa [InfoSeq.table, onlyInformed, other, InfoSeq.I, InfoSeq.U] using
          (hm (onlyInformed 1) 1).2.2.1 (InfoBase.num_only 1) (by decide)
    · simpa [InfoSeq.table, InfoSeq.I, InfoSeq.U] using
        (hm (fun _ ↦ Status.informed) i).2.2.2 InfoBase.num_i
  have hR' : (payoffTable μ θ Y a b c φ E).R = (InfoSeq.table
      (piM0 a b c φ σ β) (piMU1 a b c φ σ β) (piMI1 a b c φ σ β)
      (piM2 a b c φ σ β) (piR0 a b c φ σ β) (piR1 a b c φ σ β)
      (piR2 a b c φ σ β)).R := by
    funext X
    rcases InfoBase.profile_cases X with rfl | rfl | rfl | rfl
    · simpa [InfoSeq.table, InfoBase.num_u] using
        (hr (fun _ ↦ Status.uninformed)).1 InfoBase.num_u
    · simpa [InfoSeq.table, InfoBase.num_only] using
        (hr (onlyInformed 0)).2.1 (InfoBase.num_only 0)
    · simpa [InfoSeq.table, InfoBase.num_only] using
        (hr (onlyInformed 1)).2.1 (InfoBase.num_only 1)
    · simpa [InfoSeq.table, InfoBase.num_i] using
        (hr (fun _ ↦ Status.informed)).2.2 InfoBase.num_i
  exact congr_arg₂ PayoffTable.mk hM' hR'

end
end InfoEconBridge

open MeasureTheory Filter InfoSharing.Shared InfoSharing.Economy
set_option maxHeartbeats 3000000

theorem solution :
    ∀ φ : ℝ, 0 < φ → ∃ c₁ c₂ : ℝ,
    ∀ (ce c a b σ β : ℝ) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (θ Y : Ω → ℝ),
      c = -ce → 0 < ce → ce < 2 / (1 + φ) → IsSignalModel μ θ Y σ β →
      (∃ E : (Fin 2 → Status) → PricingProfile, IsPricingEqFamily μ θ Y a b c φ β E) ∧
      (ce ≠ (2 + 3 * φ) / ((1 + 2 * φ) * (1 + φ)) →
      ∀ E : (Fin 2 → Status) → PricingProfile, IsPricingEqFamily μ θ Y a b c φ β E →
        let P := payoffTable μ θ Y a b c φ E
        (∃ (T : ℝ) (X : Fin 2 → Status), IsConcurrentOutcome P T X) ∧
        (∀ k : Fin 2, ∃ s : SeqStrategy, IsSequentialSPE P k s) ∧
        (∀ (T : ℝ) (X : Fin 2 → Status) (k : Fin 2) (s : SeqStrategy),
          IsConcurrentOutcome P T X → IsSequentialSPE P k s →
            concRetailer P T X ≤ seqRetailer P k s) ∧
        (ce ≠ c₁ → ce ≠ c₂ →
          ∀ (T : ℝ) (X : Fin 2 → Status) (k : Fin 2) (s : SeqStrategy),
            IsConcurrentOutcome P T X → IsSequentialSPE P k s →
              seqManufacturersTotal P k s ≤ concManufacturersTotal P T X)) := by
  intro φ hφ
  obtain ⟨ZB,hZB,hbRoot,hbUnique⟩ := InfoEconAlgebra.b_root φ hφ
  obtain ⟨ZD,hZD,hdRoot,hdUnique⟩ := InfoEconAlgebra.d_root φ hφ
  refine ⟨(2-ZB)/(1+φ), (2-ZD)/(1+φ), ?_⟩
  intro ce c a b σ β Ω _ μ θ Y hc hce hcap hM
  refine ⟨InfoEconBridge.pricing_family φ ce c a b σ β μ θ Y hφ hc hce hcap hM, ?_⟩
  intro hU E hE
  dsimp only
  rw [InfoEconBridge.payoff_eq_table φ ce c a b σ β μ θ Y E hφ hc hce hcap hU hM hE]
  let m0 := piM0 a b c φ σ β
  let mu := piMU1 a b c φ σ β
  let mi := piMI1 a b c φ σ β
  let m2 := piM2 a b c φ σ β
  let r0 := piR0 a b c φ σ β
  let r1 := piR1 a b c φ σ β
  let r2 := piR2 a b c φ σ β
  have hσ : 0 < σ := hM.2.2.2.2.2.2.2.1
  have hβ : 0 < β := (InfoEconBridge.signal_moments μ θ Y σ β hM).2.2.2
  have hp1 : 0 < 1+φ := by positivity
  let z := 2+(1+φ)*c
  have hz : 0 < z := by
    have hh := (lt_div_iff₀ hp1).mp hcap
    dsimp [z]; rw [hc]; nlinarith
  have hz2 : z < 2 := by dsimp [z]; rw [hc]; nlinarith [mul_pos hp1 hce]
  have hseq (k : Fin 2) := InfoSeq.exists_seq_any m0 mu mi m2 r0 r1 r2 k
  rcases lt_trichotomy z 1 with hz1 | hzeq | hz1
  · obtain ⟨hg0,hmi,hA,hneg,hmu⟩ := InfoEconAlgebra.high_gaps a b c φ σ β hφ hσ hβ hz hz1
    have hg0' : 0 < mi-m0 := sub_pos.mpr hg0
    have hBne (hne : ce ≠ (2-ZB)/(1+φ)) : r2+(m2-mu) ≠ r1 := by
      have hzB : z ≠ ZB := by
        intro hh
        apply hne
        apply (eq_div_iff hp1.ne').mpr
        dsimp [z] at hh
        rw [hc] at hh
        nlinarith
      have hb : InfoEconAlgebra.bPoly φ z ≠ 0 := fun hh ↦ hzB (hbUnique z ⟨hz,hz1⟩ hh)
      have hg := (InfoEconAlgebra.profit_gaps a b c φ σ β hφ hz).2.2.2.2.1
      have hn : (z-1)*InfoEconAlgebra.bPoly φ z*β*σ^2 /
          (4*z^2*(1+φ)^3*(φ+z)^2) ≠ 0 := by
        apply div_ne_zero _ (by positivity)
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (ne_of_lt hz1)) hb)
          hβ.ne') (pow_ne_zero 2 hσ.ne')
      intro hh
      apply hn
      rw [← hg]
      exact sub_eq_zero.mpr hh
    have hDne (hne : ce ≠ (2-ZD)/(1+φ)) : r2+2*(m2-mu) ≠ r1+(mi-m0) := by
      have hzD : z ≠ ZD := by
        intro hh
        apply hne
        apply (eq_div_iff hp1.ne').mpr
        dsimp [z] at hh
        rw [hc] at hh
        nlinarith
      have hd : InfoEconAlgebra.dPoly φ z ≠ 0 := fun hh ↦ hzD (hdUnique z ⟨hz,hz1⟩ hh)
      have hg := (InfoEconAlgebra.profit_gaps a b c φ σ β hφ hz).2.2.2.2.2.1
      have hn : (z-1)*InfoEconAlgebra.dPoly φ z*β*σ^2 /
          (4*z^2*(1+φ)^3*(φ+z)^2) ≠ 0 := by
        apply div_ne_zero _ (by positivity)
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (ne_of_lt hz1)) hd)
          hβ.ne') (pow_ne_zero 2 hσ.ne')
      intro hh
      apply hn
      rw [← hg]
      change r2+2*(m2-mu)-r1-(mi-m0)=0
      linarith
    refine ⟨InfoEconGame.exists_conc_high m0 mu mi m2 r0 r1 r2 hg0' hmi hA hneg, hseq, ?_, ?_⟩
    · intro T X k s hX hs
      exact (InfoEconGame.comparison_high m0 mu mi m2 r0 r1 r2 hg0' hmi hA hneg hmu
        T X k s hX hs).1
    · intro hneB hneD T X k s hX hs
      exact (InfoEconGame.comparison_high m0 mu mi m2 r0 r1 r2 hg0' hmi hA hneg hmu
        T X k s hX hs).2 (hBne hneB) (hDne hneD)
  · obtain ⟨hmi,hmu,hm2,hr1,hr2⟩ := InfoEconAlgebra.neutral_gaps a b c φ σ β hφ hzeq
    rw [hmi,hmu,hm2,hr1,hr2]
    refine ⟨InfoEconGame.exists_conc_low m0 m0 m0 m0 r0 r0 r0 (by linarith) (by linarith),
      fun k ↦ InfoSeq.exists_seq_any m0 m0 m0 m0 r0 r0 r0 k, ?_, ?_⟩
    · intro T X k s hX hs
      exact le_of_eq ((InfoEconGame.conc_neutral m0 r0 T X hX).1.trans
        (InfoSeq.seq_neutral m0 r0 k s hs).1.symm)
    · intro _ _ T X k s hX hs
      exact le_of_eq ((InfoSeq.seq_neutral m0 r0 k s hs).2.trans
        (InfoEconGame.conc_neutral m0 r0 T X hX).2.symm)
  · obtain ⟨hA,hB,hC⟩ := InfoEconAlgebra.low_gaps a b c φ σ β hφ hσ hβ hz1 hz2
    refine ⟨InfoEconGame.exists_conc_low m0 mu mi m2 r0 r1 r2 hA.le hC.le, hseq, ?_, ?_⟩
    · intro T X k s hX hs
      exact le_of_eq ((InfoEconGame.conc_low m0 mu mi m2 r0 r1 r2 T X hX hA hC).1.trans
        (InfoSeq.seq_low m0 mu mi m2 r0 r1 r2 k s hs hA hB).1.symm)
    · intro _ _ T X k s hX hs
      exact le_of_eq ((InfoSeq.seq_low m0 mu mi m2 r0 r1 r2 k s hs hA hB).2.trans
        (InfoEconGame.conc_low m0 mu mi m2 r0 r1 r2 T X hX hA hC).2.symm)
