-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.CanonicalCoupledMerge.transition_valid_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:53:32.627348+00:00
-- url     : https://prove2.me/submissions/3be3724e-3244-4dbd-a544-12f724672dfc

import Mathlib
import Definitions.Def_Q238K031
import Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalCoupledMerge_step_correct_s238

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

lemma zero (b : ℕ) : Height 0 b := by
  constructor
  · simp
  · simpa using (one_le_pow₀ (by norm_num : (1:ℕ)≤2) : 1≤2^b)

lemma of_fraction (p : ℤ) (d b : ℕ) (hd : 0<d) (hp : p.natAbs≤2^b) (hdb : d≤2^b) :
    Height ((p:ℚ)/(d:ℚ)) b := by
  constructor
  · by_cases hz : p=0
    · simp [hz]
    · have hh := Rat.num_dvd p (by exact_mod_cast hd.ne' : (d:ℤ)≠0)
      rw [←Rat.intCast_div_eq_divInt] at hh
      simp only [Int.cast_natCast] at hh
      exact (Nat.le_of_dvd (by omega : 0<p.natAbs) (Int.natAbs_dvd_natAbs.mpr hh)).trans hp
  · have hh := Rat.den_dvd p (d:ℤ)
    rw [←Rat.intCast_div_eq_divInt] at hh
    simp only [Int.cast_natCast] at hh
    exact (Nat.le_of_dvd hd (Int.natCast_dvd_natCast.mp hh)).trans hdb

lemma natCast (n b : ℕ) (hn : n≤2^b) : Height (n:ℚ) b := by
  constructor
  · simpa using hn
  · simpa using (one_le_pow₀ (by norm_num : (1:ℕ)≤2) : 1≤2^b)

lemma Height.neg {q : ℚ} {b : ℕ} (hq : Height q b) : Height (-q) b := by
  simpa only [Height,Rat.num_neg_eq_neg_num,Int.natAbs_neg,Rat.den_neg_eq_den] using hq

lemma Height.add {q r : ℚ} {b c : ℕ} (hq : Height q b) (hr : Height r c) :
    Height (q+r) (b+c+1) := by
  have hn : (q.num*(r.den:ℤ)+r.num*(q.den:ℤ)).natAbs≤2^(b+c+1) := by
    calc
      _ ≤ q.num.natAbs*r.den+r.num.natAbs*q.den := by
        simpa only [Int.natAbs_mul,Int.natAbs_natCast] using
          Int.natAbs_add_le (q.num*(r.den:ℤ)) (r.num*(q.den:ℤ))
      _ ≤ 2^b*2^c+2^c*2^b := Nat.add_le_add (Nat.mul_le_mul hq.1 hr.2) (Nat.mul_le_mul hr.1 hq.2)
      _ = _ := by rw [pow_succ,pow_add]; ring
  have hd : q.den*r.den≤2^(b+c+1) := by
    have hh := Nat.mul_le_mul hq.2 hr.2
    rw [←pow_add] at hh
    exact hh.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have he : q+r=((q.num*(r.den:ℤ)+r.num*(q.den:ℤ):ℤ):ℚ)/(q.den*r.den:ℕ) := by
    nth_rw 1 [←Rat.num_div_den q]
    nth_rw 1 [←Rat.num_div_den r]
    push_cast
    convert div_add_div (q.num:ℚ) (r.num:ℚ) (by exact_mod_cast q.den_nz : (q.den:ℚ)≠0) (by exact_mod_cast r.den_nz : (r.den:ℚ)≠0) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  rw [he]
  exact of_fraction _ _ _ (Nat.mul_pos q.den_pos r.den_pos) hn hd

lemma Height.sub {q r : ℚ} {b c : ℕ} (hq : Height q b) (hr : Height r c) :
    Height (q-r) (b+c+1) := by
  rw [sub_eq_add_neg]
  exact hq.add hr.neg

lemma Height.mul {q r : ℚ} {b c : ℕ} (hq : Height q b) (hr : Height r c) :
    Height (q*r) (b+c) := by
  have hn : (q.num*r.num).natAbs≤2^(b+c) := by
    rw [Int.natAbs_mul,pow_add]
    exact Nat.mul_le_mul hq.1 hr.1
  have hd : q.den*r.den≤2^(b+c) := by rw [pow_add]; exact Nat.mul_le_mul hq.2 hr.2
  have he : q*r=((q.num*r.num:ℤ):ℚ)/(q.den*r.den:ℕ) := by
    nth_rw 1 [←Rat.num_div_den q]
    nth_rw 1 [←Rat.num_div_den r]
    push_cast
    exact div_mul_div_comm _ _ _ _
  rw [he]
  exact of_fraction _ _ _ (Nat.mul_pos q.den_pos r.den_pos) hn hd

lemma Height.inv {q : ℚ} {b : ℕ} (hq : Height q b) : Height q⁻¹ b := by
  by_cases hz : q=0
  · subst q
    simpa only [inv_zero] using zero b
  · have hn : q.num≠0 := Rat.num_ne_zero.mpr hz
    constructor
    · simpa only [Rat.num_inv,Int.natAbs_mul,Int.natAbs_sign_of_ne_zero hn,
        Int.natAbs_natCast,one_mul] using hq.2
    · simpa only [Rat.den_inv_of_ne_zero hz] using hq.1

lemma Height.div {q r : ℚ} {b c : ℕ} (hq : Height q b) (hr : Height r c) :
    Height (q/r) (b+c) := by
  rw [div_eq_mul_inv]
  exact hq.mul hr.inv

end MetricKMedianRecovery.RationalHeight

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FiniteCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalLengthView
open PhaseSequence PhaseMergeRefinement CanonicalMergeRefinement PhaseCountCrossing
variable {X : Type*} [DecidableEq X] {d : ℕ}

lemma view_sound (distance : X → Fin d → ℚ) (F : Finset X) (R H G : List X) (J : Plan X)
    (h : view distance F R H G=some J) : accepts distance F H G J :=
  of_decide_eq_true (List.find?_some (p := fun J=>decide (accepts distance F H G J)) h)

end MetricKMedianRecovery.CanonicalLengthView

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalLeaves
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [PseudoMetricSpace V]

attribute [local instance] metric

variable [DecidableEq V]

omit [PseudoMetricSpace V] [DecidableEq V] in
lemma Before.mono {B : Finset (Label V)} {a b : ℕ} (h : Before a B) (hab : a≤b) : Before b B :=
  fun c hc=>(h c hc).trans_le hab

omit [PseudoMetricSpace V] in
lemma pool_before (F : Finset V) (B : Finset (Label V)) (key : ℕ) (hB : Before key B) :
    Before (key+1) (PhaseMergePath.pool (F.image original) B (copy key)) := by
  intro c hc
  rcases Finset.mem_union.mp hc with hc|hc
  · exact (hB c hc).trans (by omega)
  · obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hc
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    have hh : c=(key,j,0) := by simpa only [copy,original,leaf,Function.Embedding.coeFn_mk,Sum.elim_inl,Sum.inr.injEq] using he.symm
    subst c
    omega

omit [PseudoMetricSpace V] in
lemma singleton_before (key : ℕ) (i : V) (s : ℚ) (B : Finset (Label V)) (hB : Before key B) :
    Before (key+1) (insert (leaf key i s) B) := by
  intro c hc
  rcases Finset.mem_insert.mp hc with he|hc
  · have hh : c=(key,i,s) := Sum.inr.inj he
    subst c
    omega
  · exact (hB c hc).trans (by omega)

end MetricKMedianRecovery.RationalLeaves

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MergeResources
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
open RationalHeight
variable {V : Type*} [DecidableEq V]

lemma parent_shorten (key : ℕ) (i : V) (l u : ℚ) (x : Label V) :
    parent (shorten key i l u x)=parent x := by
  simp only [shorten,Equiv.swap_apply_def]
  split_ifs with hu hl
  · subst x; rfl
  · subst x; rfl
  · rfl

lemma height_shorten (key : ℕ) (i : V) (l u : ℚ) (h : ℕ)
    (hl : Height l h) (hu : Height u h) (x : Label V) (hx : HeightBound h x) :
    HeightBound h (shorten key i l u x) := by
  simp only [shorten,Equiv.swap_apply_def]
  split_ifs
  · exact hl
  · exact hu
  · exact hx

omit [DecidableEq V] in
lemma BankBound.mono {F : Finset V} {h key size key' size' : ℕ} {B : Finset (Label V)}
    (hb : BankBound F h key size B) (hk : key ≤ key') (hs : size ≤ size') :
    BankBound F h key' size' B :=
  ⟨hb.rooted,hb.height,hb.before.mono hk,hb.card.trans hs⟩

lemma BankBound.pool {F : Finset V} {h key size : ℕ} {B : Finset (Label V)}
    (hb : BankBound F h key size B) :
    BankBound F h (key+1) (size+F.card) (PhaseMergePath.pool (F.image original) B (copy key)) := by
  refine ⟨?_,?_,pool_before F B key hb.before,?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx|hx
    · exact hb.rooted x hx
    · obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
      obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hy
      exact hi
  · intro x hx
    rcases Finset.mem_union.mp hx with hx|hx
    · exact hb.height x hx
    · obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hy
      exact RationalHeight.zero h
  · have h₁ := Finset.card_union_le B ((F.image original).image (copy key))
    have h₂ := Finset.card_image_le (f:=copy key) (s:=F.image original)
    have h₃ := Finset.card_image_le (f:=original) (s:=F)
    have hc := hb.card
    dsimp only [PhaseMergePath.pool]
    omega

lemma BankBound.insert {F : Finset V} {h key size : ℕ} {B : Finset (Label V)}
    (hb : BankBound F h key size B) (i : V) (hi : i∈F) (s : ℚ) (hs : Height s h) :
    BankBound F h (key+1) (size+1) (insert (leaf key i s) B) := by
  refine ⟨?_,?_,singleton_before key i s B hb.before,?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hi
    · exact hb.rooted x hx
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hs
    · exact hb.height x hx
  · exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hb.card 1)

end MetricKMedianRecovery.RationalLeaves

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves RationalHeight
variable {V : Type*} [DecidableEq V]

lemma Correction.parent (r : Correction V) (x : Label V) : parent (r.apply x)=parent x := by
  cases r with
  | identity=>rfl
  | shorten key i l u=>exact parent_shorten key i l u x

lemma Correction.height {h : ℕ} (r : Correction V) (hr : r.Bounded h)
    (x : Label V) (hx : HeightBound h x) : HeightBound h (r.apply x) := by
  cases r with
  | identity=>exact hx
  | shorten key i l u=>exact height_shorten key i l u h hr.1 hr.2 x hx

lemma State.Resources.map_bank {F : Finset V} {q h p : ℕ} {s : State V}
    (hs : s.Resources F q h p) (hb : Before (3*q) s.mapFree) :
    BankBound F h (3*q) (q*(2*F.card+1)) s.mapFree := by
  refine ⟨?_,?_,hb,?_⟩
  · intro x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    rw [Correction.parent]
    exact hs.bank.rooted y hy
  · intro x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    exact s.correction.height hs.correction y (hs.bank.height y hy)
  · exact (Finset.card_image_le).trans hs.bank.card

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyAge
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
lemma Before.level {key : ℕ} {B : Finset (Label V)} (hb : Before key B)
    (x : Label V) (hx : x∈B) : level x ≤ key := by
  cases x with
  | inl i=>exact Nat.zero_le _
  | inr c=>exact hb c hx

lemma level_shorten (key : ℕ) (i : V) (l u : ℚ) (x : Label V) :
    level (shorten key i l u x)=level x := by
  simp only [shorten,Equiv.swap_apply_def]
  split_ifs with hu hl
  · subst x; rfl
  · subst x; rfl
  · rfl

end MetricKMedianRecovery.RationalLeaves

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves RationalHeight
variable {V : Type*} [DecidableEq V]

lemma Correction.level (r : Correction V) (x : Label V) : level (r.apply x)=level x := by
  cases r with
  | identity=>rfl
  | shorten key i l u=>exact level_shorten key i l u x

lemma Correction.before (r : Correction V) {key : ℕ} {B : Finset (Label V)}
    (hb : Before key B) : Before key (B.image r.apply) := by
  intro c hc
  obtain ⟨x,hx,he⟩:=Finset.mem_image.mp hc
  have h:=hb.level x hx
  rw [←r.level x,he] at h
  exact h

lemma State.Resources.map_bound {F : Finset V} {q h p : ℕ} {s : State V}
    (hs : s.Resources F q h p) : BankBound F h (3*q) (q*(2*F.card+1)) s.mapFree :=
  hs.map_bank (s.correction.before hs.bank.before)

omit [DecidableEq V] in
lemma State.Resources.advance {F : Finset V} {q h p : ℕ} {s : State V}
    (hs : s.Resources F q h p) (G : List (Label V)) (T U : List (List (Label V))) :
    (advanceState s G T U).Resources F (q+1) h p :=
  ⟨hs.bank.mono (by omega) (Nat.mul_le_mul_right _ (by omega)),hs.correction,hs.oldPrice,hs.newPrice⟩

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DecisionOps
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PriceBisection

section
open RationalHeight

lemma search_eq_iterate (count : ℚ → ℕ) (h n : ℕ) (I : ℚ × ℚ) :
    search count h n I = (refine count h)^[n] I := by
  induction n generalizing I with
  | zero => rfl
  | succ n ih => rw [search, ih, Function.iterate_succ_apply]

lemma iterate_dyadic (count : ℚ → ℕ) (h n : ℕ) (a b : ℚ) :
    ∃ j : ℕ, j < 2^n ∧
      ((refine count h)^[n] (a,b)).1 = a+(b-a)*(j:ℚ)/2^n ∧
      ((refine count h)^[n] (a,b)).2 = a+(b-a)*(j+1:ℕ)/2^n := by
  induction n with
  | zero => exact ⟨0,by norm_num,by simp,by simp⟩
  | succ n ih =>
    obtain ⟨j,hj,hl,hu⟩ := ih
    have hn : (2:ℚ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
    have hm : (((refine count h)^[n] (a,b)).1+
        ((refine count h)^[n] (a,b)).2)/2 =
        a+(b-a)*(2*j+1:ℕ)/(2:ℚ)^(n+1) := by
      rw [hl,hu,pow_succ]
      push_cast
      field_simp
      ring
    rw [Function.iterate_succ_apply']
    simp only [refine]
    split_ifs with hc
    · refine ⟨2*j+1,by rw [pow_succ]; omega,hm,?_⟩
      rw [hu,pow_succ]
      push_cast
      field_simp
      ring
    · refine ⟨2*j,by rw [pow_succ]; omega,?_,hm⟩
      rw [hl,pow_succ]
      push_cast
      field_simp

lemma dyadic_height {a b : ℚ} {N n j : ℕ}
    (ha : Height a N) (hb : Height b N) (hj : j ≤ 2^n) :
    Height (a+(b-a)*(j:ℚ)/(2:ℚ)^n) (3*N+2*n+2) := by
  have hjh := natCast j n hj
  have h2 : Height ((2:ℚ)^n) n := by
    have hh := natCast (2^n) n le_rfl
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
  have hh := ha.add (((hb.sub ha).mul hjh).div h2)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  omega

lemma iterate_height {a b : ℚ} {N : ℕ} (ha : Height a N) (hb : Height b N)
    (count : ℚ → ℕ) (h n : ℕ) :
    Height ((refine count h)^[n] (a,b)).1 (3*N+2*n+2) ∧
    Height ((refine count h)^[n] (a,b)).2 (3*N+2*n+2) := by
  obtain ⟨j,hj,hl,hu⟩ := iterate_dyadic count h n a b
  rw [hl,hu]
  exact ⟨dyadic_height ha hb hj.le,dyadic_height ha hb (by omega)⟩

end

end MetricKMedianRecovery.PriceBisection

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CorrectionSize
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves
variable {V : Type*} [LinearOrder V] {d : ℕ}
omit [LinearOrder V] in
lemma Correction.Keys.mono {r : Correction V} {q t : ℕ} (h : r.Keys q) (hqt : q≤t) : r.Keys t := by
  cases r with
  | identity=>trivial
  | shorten key i l u=>exact h.trans_le (Nat.mul_le_mul_left 3 hqt)
lemma resolve_keys (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v M : ℚ) (N precision q n k : ℕ) (B : Finset (Label V)) (lam : ℚ)
    (P : List (List (Label V))) (R : CanonicalMergeCrossing.Result (Label V)) :
    (resolve loc distance F v M N precision q n k (3*q+2) B lam P R).Keys q := by
  cases R with
  | success H T=>trivial
  | common H T U=>trivial
  | sensitive H G T U=>
    dsimp only [resolve]
    split
    · trivial
    · split
      · trivial
      · change 3*q+2<3*(q+1)
        omega
lemma step_keys (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v M : ℚ) (N precision q n k : ℕ) (s : State V) (hk : s.correction.Keys q) :
    (step loc distance F v M N precision q n k s).Keys q := by
  dsimp only [step]
  split
  · split_ifs
    · trivial
    · exact resolve_keys ..
    · change s.correction.Keys (q+1)
      exact hk.mono (by omega)
  · trivial
end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthHeight
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalLengthSearch
open RationalHeight
variable {X : Type*} [DecidableEq X]

lemma range_height (f : ℚ → ℕ) (k precision : ℕ) (b : ℚ) (h : ℕ) (hb : Height b h) :
    Height (range f k precision b).1 (heightBudget b precision h) ∧
    Height (range f k precision b).2 (heightBudget b precision h) := by
  unfold range
  split
  · have hh := PriceBisection.iterate_height (zero h) hb (fun s=>f (b-s)) k
      (PriceBisection.iterations 0 b precision)
    rw [←PriceBisection.search_eq_iterate] at hh
    exact ⟨by convert hb.sub hh.2 using 1 <;> first | (with_reducible_and_instances rfl) | (simp [heightBudget]; omega),
      by convert hb.sub hh.1 using 1; simp [heightBudget]; omega⟩
  · have hh := PriceBisection.iterate_height (zero h) hb f k
      (PriceBisection.iterations 0 b precision)
    rw [←PriceBisection.search_eq_iterate] at hh
    exact ⟨hh.1.mono (by unfold heightBudget; omega),hh.2.mono (by unfold heightBudget; omega)⟩

lemma run_height (F Q : Finset X) (leaf : ℚ → X) (complete : ℚ → List (List X))
    (T U : List (List X)) (b : ℚ) (k precision h : ℕ) (hb : Height b h) :
    (run F Q leaf complete T U b k precision).Bounded (heightBudget b precision h) := by
  have hh := range_height (count F Q leaf complete T U b) k precision b h hb
  dsimp only [run]
  split_ifs
  · exact hh.1
  · exact hh.2
  · exact hh

end MetricKMedianRecovery.CanonicalLengthSearch

namespace MetricKMedianRecovery.CanonicalSensitiveEndpoint
open PhaseSequence RationalLeaves RationalHeight CanonicalLengthView
variable {V : Type*} [LinearOrder V] {d : ℕ}
lemma run_height (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (Q : Finset (Label V)) (v lam b : ℚ) (q n k key precision h : ℕ)
    (H : List (Label V)) (T U : List (List (Label V))) (J : Plan (Label V)) (hb : Height b h) :
    (run loc distance F Q v lam b q n k key precision H T U J).Bounded
      (CanonicalLengthSearch.heightBudget b precision h) := by
  dsimp only [run]
  split
  · exact zero _
  · exact CanonicalLengthSearch.run_height _ _ _ _ _ _ _ _ _ _ hb
end MetricKMedianRecovery.CanonicalSensitiveEndpoint

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ResolveResources
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer RationalLeaves RationalHeight CanonicalLengthView
variable {V : Type*} [LinearOrder V] {d : ℕ}

lemma banks_bound {F : Finset V} {q h p : ℕ} {s : State V}
    (hs : s.Resources F q h p) :
    BankBound F h (3*q+2) (q*(2*F.card+1)+2*F.card) (banks F s.mapFree q) := by
  have hh := hs.map_bound.pool.pool
  dsimp only [banks]
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (omega)

lemma resolve_resources (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (v M : ℚ) (N precision q n k H p : ℕ) (B : Finset (Label V)) (lam : ℚ)
    (P : List (List (Label V))) (R : CanonicalMergeCrossing.Result (Label V))
    (hb : BankBound F (CanonicalLengthSearch.heightBudget (20*N*M) precision H)
      (3*q+2) (q*(2*F.card+1)+2*F.card) B)
    (hlam : Height lam p) (hfar : Height (20*N*M) H) :
    (resolve loc distance F v M N precision q n k (3*q+2) B lam P R).Resources F q
      (CanonicalLengthSearch.heightBudget (20*N*M) precision H) p := by
  let h := CanonicalLengthSearch.heightBudget (20*N*M) precision H
  have hsize : q*(2*F.card+1)+2*F.card+1=(q+1)*(2*F.card+1) := by ring
  have hmono : BankBound F h (3*(q+1)) ((q+1)*(2*F.card+1)) B :=
    hb.mono (by omega) (by omega)
  cases R with
  | success G T=>exact ⟨hmono,hlam⟩
  | common G T U=>exact ⟨hmono,True.intro,hlam,hlam⟩
  | sensitive G J T U=>
    dsimp only [resolve]
    cases hv : view (rows distance) (F.image original) ((F.sort (·≤·)).map original) G J with
    | none=>exact ⟨hmono,hlam⟩
    | some plan=>
      dsimp only
      have ha:=view_sound (rows distance) (F.image original) ((F.sort (·≤·)).map original) G J plan hv
      have hroot : plan.root∈F.image original := by
        cases plan <;> exact ha.1
      have hparent : parent plan.root∈F := by
        obtain ⟨i,hi,he⟩:=Finset.mem_image.mp hroot
        rw [←he]
        exact hi
      have hh := CanonicalSensitiveEndpoint.run_height loc distance F (after ∅ P) v lam (20*N*M)
        q n k (3*q+2) precision H G T U plan hfar
      cases he : CanonicalSensitiveEndpoint.run loc distance F (after ∅ P) v lam (20*N*M)
          q n k (3*q+2) precision G T U plan with
      | success s W=>
        rw [he] at hh
        refine ⟨?_,hlam⟩
        have ht := hb.insert (parent plan.root) hparent s hh
        rw [hsize] at ht
        convert ht using 1 <;> rfl
      | bracket l u A Z=>
        rw [he] at hh
        refine ⟨?_,hh,hlam,hlam⟩
        have ht := hb.insert (parent plan.root) hparent u hh.2
        rw [hsize] at ht
        convert ht using 1 <;> rfl

lemma step_resources (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (v M : ℚ) (N precision q n k H p : ℕ) (s : State V)
    (hs : s.Resources F q (CanonicalLengthSearch.heightBudget (20*N*M) precision H) p)
    (hfar : Height (20*N*M) H) :
    (step loc distance F v M N precision q n k s).Resources F q
      (CanonicalLengthSearch.heightBudget (20*N*M) precision H) p := by
  dsimp only [step]
  split
  · split_ifs
    · exact ⟨hs.map_bound.mono (by omega) (Nat.mul_le_mul_right _ (by omega)),hs.newPrice⟩
    · exact resolve_resources loc distance F v M N precision q n k H p _ _ _ _ (banks_bound hs) hs.newPrice hfar
    · exact hs.advance _ _ _
  · exact ⟨hs.bank.mono (by omega) (Nat.mul_le_mul_right _ (by omega)),hs.oldPrice⟩

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

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

lemma transition_valid_s238_oai (loc : Fin d→V) (distance : V→Fin d→ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset V)
    (v M : ℚ) (eta lo hi : ℝ) (N precision total k H p : ℕ)
    (hF : F.Nonempty) (hM : 0<M) (hN : 3≤N)
    (hv : (0:ℝ)<v) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0≤eta)
    (hhi : hi≤8*N*(M:ℝ)) (hprecision : (1/(2:ℚ)^precision:ℚ)≤eta)
    (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ)) (hfar : Height (20*N*M) H)
    (f : Frame V) (hf : f.Valid loc F v eta lo hi total k (CanonicalLengthSearch.heightBudget (20*N*M) precision H) p) :
    (transition loc distance F v M N precision k f).Valid loc F v eta lo hi total k
      (CanonicalLengthSearch.heightBudget (20*N*M) precision H) p := by
  rcases f with ⟨q,n,o⟩
  cases o with
  | inl o=>exact hf
  | inr s=>
    cases n with
    | zero=>exact hf
    | succ n=>
      obtain ⟨hn,hc,hr,hkey⟩:=hf
      change q+(n+1)=total at hn
      have hs:=step_correct_s238 loc distance hmetric F v M eta lo hi N precision q n k s hc
        hF hM hN hv hv1 hlo heta hhi hprecision hdiam
      have hb:=step_resources loc distance F v M N precision q n k H p s hr hfar
      have hk:=step_keys loc distance F v M N precision q n k s hkey
      refine ⟨by dsimp only [transition]; omega,?_⟩
      dsimp only [transition]
      cases he : step loc distance F v M N precision q n k s with
      | inl o=>
        rw [he] at hs hb
        exact ⟨by simpa only [Outcome.Correct,hn] using hs,hb⟩
      | inr s=>
        rw [he] at hs hb hk
        exact ⟨hs,hb,hk⟩
end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.CanonicalCoupledMerge.transition_valid_s238_oai.{u_1} := @OAI.MetricKMedianRecovery.CanonicalCoupledMerge.transition_valid_s238_oai.{u_1}
