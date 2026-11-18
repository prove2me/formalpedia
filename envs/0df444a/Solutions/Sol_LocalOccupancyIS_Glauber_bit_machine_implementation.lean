-- Prove2me | solution 1 for LocalOccupancyIS.Glauber.bit_machine_implementation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T02:18:52.000203+00:00
-- url     : https://prove2.me/submissions/a29fc80c-769c-41b9-a239-52d7d027a0f1

import Definitions.Def_LocalOccupancyIS_Glauber_BitExecution
import Mathlib.Data.Rat.Lemmas
import Definitions.Def_LocalOccupancyIS_Glauber_Dynamics
import Theorems.Thm_SinkhornHall_lemma_1_1
import Definitions.Def_LocalOccupancyIS_Glauber_Parameters
import Definitions.Def_LocalOccupancyIS_Glauber_Execution

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma nat_lt_pow_bits (n : ℕ) : n < 2^(bits n) := by
  simpa only [bits,Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n

lemma normalize_exp_le_bits (y : ℚ) : (y.num.natAbs/y.den).log2 ≤ ratBits y := by
  have hd := Nat.div_le_self y.num.natAbs y.den
  have hm : (y.num.natAbs/y.den).log2 ≤ y.num.natAbs.log2 := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right (b := 2) hd
  unfold ratBits bits
  omega

lemma bits_le (a : ℕ) : bits a ≤ a+1 := by
  unfold bits
  exact Nat.add_le_add_right (Nat.log2_le_self a) 1

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

 def QBound (q : ℚ) (L : ℕ) : Prop := q.num.natAbs ≤ 2^L ∧ q.den ≤ 2^L

lemma bits_le_of_pow {a L : ℕ} (ha : a ≤ 2^L) : bits a ≤ L+1 := by
  have hh := Nat.log_mono_right (b := 2) ha
  rw [Nat.log_pow (by norm_num)] at hh
  simpa only [bits,Nat.log2_eq_log_two] using Nat.add_le_add_right hh 1

lemma QBound.bits {q : ℚ} {L : ℕ} (h : QBound q L) : ratBits q ≤ 2*L+3 := by
  have hn := bits_le_of_pow h.1
  have hd := bits_le_of_pow h.2
  unfold ratBits
  omega

lemma QBound.self (q : ℚ) : QBound q (ratBits q) := by
  have hn := (nat_lt_pow_bits q.num.natAbs).le
  have hd := (nat_lt_pow_bits q.den).le
  constructor
  · exact hn.trans (Nat.pow_le_pow_right (by norm_num) (by unfold ratBits; omega))
  · exact hd.trans (Nat.pow_le_pow_right (by norm_num) (by unfold ratBits; omega))

lemma QBound.mono {q : ℚ} {L M : ℕ} (h : QBound q L) (hLM : L ≤ M) : QBound q M :=
  ⟨h.1.trans (Nat.pow_le_pow_right (by norm_num) hLM),h.2.trans (Nat.pow_le_pow_right (by norm_num) hLM)⟩

lemma QBound.divInt {a d : ℤ} (hd : d ≠ 0) {L : ℕ} (ha : a.natAbs ≤ 2^L)
    (hden : d.natAbs ≤ 2^L) : QBound (Rat.divInt a d) L := by
  constructor
  · by_cases hz : a=0
    · simp [hz]
    · exact (Nat.le_of_dvd (Int.natAbs_pos.mpr hz) (Int.natAbs_dvd_natAbs.mpr (Rat.num_dvd a hd))).trans ha
  · have hh := Int.natAbs_dvd_natAbs.mpr (Rat.den_dvd a d)
    simp only [Int.natAbs_natCast] at hh
    exact (Nat.le_of_dvd (Int.natAbs_pos.mpr hd) hh).trans hden

lemma QBound.fraction {a : ℤ} {d L : ℕ} (hd : d ≠ 0) (ha : a.natAbs ≤ 2^L)
    (hden : d ≤ 2^L) : QBound ((a:ℚ)/d) L := by
  simpa only [Rat.divInt_eq_div,Int.cast_natCast] using
    QBound.divInt (Int.natCast_ne_zero.mpr hd) ha (by simpa using hden)

lemma QBound.zero : QBound 0 0 := by norm_num [QBound]
lemma QBound.one : QBound 1 0 := by norm_num [QBound]

lemma QBound.nat (a : ℕ) : QBound (a:ℚ) (LocalOccupancyIS.Glauber.bits a) := by
  constructor
  · simpa using (nat_lt_pow_bits a).le
  · change 1 ≤ 2^(LocalOccupancyIS.Glauber.bits a)
    have hh : 0 < 2^(LocalOccupancyIS.Glauber.bits a) := by positivity
    omega

lemma QBound.neg {a : ℚ} {L : ℕ} (h : QBound a L) : QBound (-a) L := by
  simpa [QBound,Rat.neg_num] using h

lemma QBound.add {a b : ℚ} {L M : ℕ} (ha : QBound a L) (hb : QBound b M) :
    QBound (a+b) (L+M+1) := by
  have he : a+b = ((a.num*(b.den:ℤ)+b.num*(a.den:ℤ):ℤ):ℚ)/(a.den*b.den:ℕ) := by
    conv_lhs => rw [← Rat.num_divInt_den a,← Rat.num_divInt_den b,Rat.divInt_eq_div,Rat.divInt_eq_div]
    push_cast
    field_simp
    <;> ring
  rw [he]
  apply QBound.fraction (Nat.mul_ne_zero a.den_nz b.den_nz)
  · calc
      _ ≤ (a.num*(b.den:ℤ)).natAbs+(b.num*(a.den:ℤ)).natAbs := Int.natAbs_add_le _ _
      _ = a.num.natAbs*b.den+b.num.natAbs*a.den := by simp only [Int.natAbs_mul,Int.natAbs_natCast]
      _ ≤ 2^L*2^M+2^M*2^L := Nat.add_le_add (Nat.mul_le_mul ha.1 hb.2) (Nat.mul_le_mul hb.1 ha.2)
      _ = 2^(L+M+1) := by rw [pow_succ,pow_add]; ring
  · calc
      _ ≤ 2^L*2^M := Nat.mul_le_mul ha.2 hb.2
      _ ≤ 2^(L+M+1) := by rw [pow_succ,pow_add]; omega

lemma QBound.sub {a b : ℚ} {L M : ℕ} (ha : QBound a L) (hb : QBound b M) :
    QBound (a-b) (L+M+1) := by simpa only [sub_eq_add_neg] using ha.add hb.neg

lemma QBound.mul {a b : ℚ} {L M : ℕ} (ha : QBound a L) (hb : QBound b M) :
    QBound (a*b) (L+M) := by
  have he : a*b = ((a.num*b.num:ℤ):ℚ)/(a.den*b.den:ℕ) := by
    conv_lhs => rw [← Rat.num_divInt_den a,← Rat.num_divInt_den b,Rat.divInt_eq_div,Rat.divInt_eq_div]
    push_cast
    ring
  rw [he]
  apply QBound.fraction (Nat.mul_ne_zero a.den_nz b.den_nz)
  · simpa only [Int.natAbs_mul,pow_add] using Nat.mul_le_mul ha.1 hb.1
  · simpa only [pow_add] using Nat.mul_le_mul ha.2 hb.2

lemma QBound.inv {a : ℚ} {L : ℕ} (ha : QBound a L) : QBound a⁻¹ L := by
  by_cases hz : a=0
  · subst a; simpa using QBound.zero.mono (Nat.zero_le L)
  · rw [Rat.inv_def]
    apply QBound.divInt (Rat.num_ne_zero.mpr hz)
    · simpa using ha.2
    · exact ha.1

lemma QBound.div {a b : ℚ} {L M : ℕ} (ha : QBound a L) (hb : QBound b M) :
    QBound (a/b) (L+M) := by simpa only [div_eq_mul_inv] using ha.mul hb.inv

lemma QBound.pow {a : ℚ} {L : ℕ} (ha : QBound a L) (r : ℕ) : QBound (a^r) (L*r) := by
  induction r with
  | zero => simpa using QBound.one
  | succ r ih => simpa [pow_succ,Nat.mul_succ] using ih.mul ha

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber

@[simp] lemma charge_run (c z : ℕ) : (charge c).run z = ((),z+c) := rfl
@[simp] lemma rationalOp_run (op : ℚ → ℚ → ℚ) (a b : ℚ) (z : ℕ) :
    (rationalOp op a b).run z = (op a b,z+(ratBits a+ratBits b+1)^3) := rfl
@[simp] lemma addQ_run (a b : ℚ) (z : ℕ) : (addQ a b).run z = (a+b,z+(ratBits a+ratBits b+1)^3) := rfl
@[simp] lemma subQ_run (a b : ℚ) (z : ℕ) : (subQ a b).run z = (a-b,z+(ratBits a+ratBits b+1)^3) := rfl
@[simp] lemma mulQ_run (a b : ℚ) (z : ℕ) : (mulQ a b).run z = (a*b,z+(ratBits a+ratBits b+1)^3) := rfl
@[simp] lemma divQ_run (a b : ℚ) (z : ℕ) : (divQ a b).run z = (a/b,z+(ratBits a+ratBits b+1)^3) := rfl
@[simp] lemma lessQ_run (a b : ℚ) (z : ℕ) : (lessQ a b).run z = (decide (a<b),z+(ratBits a+ratBits b+1)^3) := rfl

lemma counted_forIn_run {ι α : Type} (l : List ι) (a : α)
    (f : ι → α → Counted (ForInStep α)) (g : ι → α → α) (c : ι → α → ℕ)
    (h : ∀ i a z, (f i a).run z = (.yield (g i a),z+c i a)) (z : ℕ) :
    (forIn l a f).run z = l.foldl (fun az i => (g i az.1,az.2+c i az.1)) (a,z) := by
  induction l generalizing a z with
  | nil => rfl
  | cons i l ih =>
    simp only [List.forIn_cons,StateT.run_bind,h,List.foldl_cons]
    exact ih _ _

lemma counted_forIn_value {ι α : Type} (l : List ι) (a : α)
    (f : ι → α → Counted (ForInStep α)) (g : ι → α → α)
    (h : ∀ i a z, ((f i a).run z).1 = .yield (g i a)) (z : ℕ) :
    ((forIn l a f).run z).1 = l.foldl (fun a i => g i a) a := by
  induction l generalizing a z with
  | nil => rfl
  | cons i l ih =>
    simp only [List.forIn_cons,StateT.run_bind,List.foldl_cons]
    change ((match ((f i a).run z).1 with
      | .done b => pure b
      | .yield b => forIn l b f).run ((f i a).run z).2).1 = _
    rw [h]
    exact ih _ _

lemma powQ_value (a : ℚ) (r z : ℕ) : ((powQ a r).run z).1 = a^r := by
  unfold powQ
  simp only [StateT.run_bind,StateT.run_pure]
  have hh := counted_forIn_value (List.range r) (1:ℚ)
    (fun _ y => do let y ← mulQ y a; pure (.yield y)) (fun _ y => y*a)
    (by intro i y z; rfl) z
  change ((forIn (List.range r) (1:ℚ) (fun _ y => do let y ← mulQ y a; pure (.yield y))).run z).1 = _
  rw [hh]
  have hfold (r : ℕ) (y : ℚ) : (List.range r).foldl (fun y _ => y*a) y = y*a^r := by
    induction r generalizing y with
    | zero => simp
    | succ r ih => rw [List.range_succ,List.foldl_append]; simp [ih,pow_succ,mul_assoc]
  simpa using hfold r 1

lemma logSeries_value (z : ℚ) (L c : ℕ) : ((logSeries z L).run c).1 =
    2*∑ i ∈ Finset.range L, z^(2*i+1)/(2*(i:ℚ)+1) := by
  unfold logSeries
  simp only [StateT.run_bind,mulQ_run]
  change 2*((forIn (List.range L) ((0:ℚ),z) (fun (i : ℕ) (ap : ℚ × ℚ) => do
    let y ← divQ ap.2 (2*(i:ℚ)+1)
    let a ← addQ ap.1 y
    let power ← mulQ ap.2 (z*z)
    pure (.yield (a,power)))).run (c+(ratBits z+ratBits z+1)^3)).1.1 = _
  have hh := counted_forIn_value (List.range L) ((0:ℚ),z)
    (fun (i : ℕ) (ap : ℚ × ℚ) => do
      let y ← divQ ap.2 (2*(i:ℚ)+1)
      let a ← addQ ap.1 y
      let power ← mulQ ap.2 (z*z)
      pure (.yield (a,power)))
    (fun i ap => (ap.1+ap.2/(2*(i:ℚ)+1),ap.2*(z*z))) (by intros; rfl)
    (c+(ratBits z+ratBits z+1)^3)
  rw [hh]
  have hfold (L : ℕ) : (List.range L).foldl
      (fun (ap : ℚ × ℚ) (i : ℕ) => (ap.1+ap.2/(2*(i:ℚ)+1),ap.2*(z*z))) ((0:ℚ),z) =
      (∑ i ∈ Finset.range L,z^(2*i+1)/(2*(i:ℚ)+1),z^(2*L+1)) := by
    induction L with
    | zero => simp
    | succ L ih =>
      rw [List.range_succ,List.foldl_append,ih]
      simp only [List.foldl_cons,List.foldl_nil,Finset.sum_range_succ]
      congr 1
      have he : 2*(L+1)+1 = (2*L+1)+2 := by omega
      simp only [he,pow_add,pow_two,pow_one] <;> ring
  rw [hfold]

@[simp] lemma counted_bind_value {α β : Type} (x : Counted α) (f : α → Counted β) (z : ℕ) :
    ((x >>= f).run z).1 = ((f ((x.run z).1)).run ((x.run z).2)).1 := rfl
@[simp] lemma counted_pure_value {α : Type} (a : α) (z : ℕ) : ((pure a : Counted α).run z).1 = a := rfl

def seriesQ (z : ℚ) (L : ℕ) : ℚ := 2*∑ i ∈ Finset.range L,z^(2*i+1)/(2*(i:ℚ)+1)

lemma logBracket_value (y : ℚ) (h c : ℕ) :
    let k := (y.num.natAbs/y.den).log2
    let z := y/2^k
    let L := h+ratBits y+10
    let lo := (k:ℚ)*seriesQ (1/3) L+seriesQ ((z-1)/(z+1)) L
    ((logBracket y h).run c).1 = (lo,lo+3*((k:ℚ)+1)/9^L) := by
  unfold logBracket
  simp only [counted_bind_value,charge_run,powQ_value,mulQ_run,subQ_run,addQ_run,divQ_run,
    logSeries_value,counted_pure_value]
  rfl

end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section

@[simp] lemma counted_bind_run {α β : Type} (x : Counted α) (f : α → Counted β) (z : ℕ) :
    (x >>= f).run z = (f (x.run z).1).run (x.run z).2 := rfl
@[simp] lemma counted_pure_run {α : Type} (a : α) (z : ℕ) :
    (pure a : Counted α).run z = (a,z) := rfl

lemma powQ_run (a : ℚ) (r z : ℕ) : (powQ a r).run z =
    (a^r,z+∑ i ∈ Finset.range r,(ratBits (a^i)+ratBits a+1)^3) := by
  unfold powQ
  simp only [StateT.run_bind,StateT.run_pure]
  have hh := counted_forIn_run (List.range r) (1:ℚ)
    (fun _ y => do let y ← mulQ y a; pure (.yield y)) (fun _ y => y*a)
    (fun _ y => (ratBits y+ratBits a+1)^3) (by intros; rfl) z
  change (forIn (List.range r) (1:ℚ) (fun _ y => do let y ← mulQ y a; pure (.yield y))).run z = _
  rw [hh]
  have hfold (r : ℕ) (y : ℚ) (z : ℕ) : (List.range r).foldl
      (fun yz _ => (yz.1*a,yz.2+(ratBits yz.1+ratBits a+1)^3)) (y,z) =
      (y*a^r,z+∑ i ∈ Finset.range r,(ratBits (y*a^i)+ratBits a+1)^3) := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [List.range_succ,List.foldl_append,ih]
      simp only [List.foldl_cons,List.foldl_nil,Finset.sum_range_succ,pow_succ]
      congr 1
      · ring
      · omega
  simpa using hfold r 1 z

lemma powQ_cost {a : ℚ} {L : ℕ} (ha : QBound a L) (r z : ℕ) :
    ((powQ a r).run z).2 ≤ z+r*(2*L*(r+1)+7)^3 := by
  rw [powQ_run]
  simp only [Prod.snd]
  apply Nat.add_le_add_left
  have hh (i : ℕ) (hi : i∈Finset.range r) : (ratBits (a^i)+ratBits a+1)^3 ≤ (2*L*(r+1)+7)^3 := by
    have hp := (ha.pow i).bits
    have hbits := ha.bits
    have hil : L*i ≤ L*r := Nat.mul_le_mul_left L (Finset.mem_range.mp hi).le
    apply Nat.pow_le_pow_left
    nlinarith
  have hb := Finset.sum_le_sum hh
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id] using hb

lemma fold_pair_cost {α : Type} (g : ℕ → α → α) (c : ℕ → α → ℕ) (P : ℕ → α → Prop)
    (N C : ℕ) (a : α) (z : ℕ) (h0 : P 0 a)
    (hstep : ∀ i,Nat.lt i N → ∀ a,P i a → P (i+1) (g i a) ∧ c i a ≤ C) :
    let y := (List.range N).foldl (fun az i => (g i az.1,az.2+c i az.1)) (a,z)
    P N y.1 ∧ y.2 ≤ z+N*C := by
  have hi (M : ℕ) (hM : M ≤ N) :
      let y := (List.range M).foldl (fun az i => (g i az.1,az.2+c i az.1)) (a,z)
      P M y.1 ∧ y.2 ≤ z+M*C := by
    induction M with
    | zero => simpa using And.intro h0 (Nat.le_refl z)
    | succ M ih =>
      rw [List.range_succ,List.foldl_append]
      simp only [List.foldl_cons,List.foldl_nil]
      have hprev := ih (by omega)
      have hlt : M < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self M) hM
      have hnext := hstep M hlt _ hprev.1
      exact ⟨hnext.1,by nlinarith [hprev.2,hnext.2]⟩
  exact hi N le_rfl

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section

 def seriesTermSize (Z L : ℕ) : ℕ := Z*(2*L+1)+2*L+2
 def seriesSize (Z L : ℕ) : ℕ := (L+1)*(seriesTermSize Z L+1)+2*Z+2*L+10
 def seriesCharge (z : ℚ) (i : ℕ) (ap : ℚ × ℚ) : ℕ :=
  (ratBits ap.2+ratBits (2*(i:ℚ)+1)+1)^3+
  (ratBits ap.1+ratBits (ap.2/(2*(i:ℚ)+1))+1)^3+
  (ratBits ap.2+ratBits (z*z)+1)^3

lemma series_body_bound {z : ℚ} {Z L i : ℕ} (hz : QBound z Z) (hi : i < L) (ap : ℚ × ℚ)
    (ha : QBound ap.1 (i*(seriesTermSize Z L+1))) (hp : QBound ap.2 (Z*(2*i+1))) :
    QBound (ap.1+ap.2/(2*(i:ℚ)+1)) ((i+1)*(seriesTermSize Z L+1)) ∧
    QBound (ap.2*(z*z)) (Z*(2*(i+1)+1)) ∧
    seriesCharge z i ap ≤ 3*(4*seriesSize Z L+7)^3 := by
  let E := seriesTermSize Z L
  let F := seriesSize Z L
  have hi' : 2*i+1 ≤ 2*L+1 := by omega
  have hden : QBound (2*(i:ℚ)+1) (2*L+2) := by
    have hh := (QBound.nat (2*i+1)).mono ((bits_le (2*i+1)).trans (by omega : 2*i+1+1 ≤ 2*L+2))
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hh
  have hterm : QBound (ap.2/(2*(i:ℚ)+1)) E := by
    exact (hp.div hden).mono (by dsimp [E,seriesTermSize]; nlinarith)
  have hsum : QBound (ap.1+ap.2/(2*(i:ℚ)+1)) ((i+1)*(E+1)) := by
    convert ha.add hterm using 1 <;> dsimp only [E] <;> ring
  have hpower : QBound (ap.2*(z*z)) (Z*(2*(i+1)+1)) := by
    simpa only [show Z*(2*i+1)+(Z+Z)=Z*(2*(i+1)+1) by ring] using hp.mul (hz.mul hz)
  have hF1 : i*(E+1) ≤ F := by dsimp [F,seriesSize]; nlinarith
  have hF2 : Z*(2*i+1) ≤ F := by
    have ht : Z*(2*i+1) ≤ E := by dsimp [E,seriesTermSize]; nlinarith
    have he : E ≤ F := by dsimp [F,seriesSize]; nlinarith
    exact ht.trans he
  have hF3 : E ≤ F := by dsimp [F,seriesSize]; nlinarith
  have hF4 : 2*L+2 ≤ F := by dsimp [F,seriesSize]; nlinarith
  have hF5 : Z+Z ≤ F := by dsimp [F,seriesSize]; nlinarith
  have hba := (ha.mono hF1).bits
  have hbp := (hp.mono hF2).bits
  have hbd := (hden.mono hF4).bits
  have hbt := (hterm.mono hF3).bits
  have hbz := ((hz.mul hz).mono hF5).bits
  have hc1 : ratBits ap.2+ratBits (2*(i:ℚ)+1)+1 ≤ 4*F+7 := by omega
  have hc2 : ratBits ap.1+ratBits (ap.2/(2*(i:ℚ)+1))+1 ≤ 4*F+7 := by omega
  have hc3 : ratBits ap.2+ratBits (z*z)+1 ≤ 4*F+7 := by omega
  refine ⟨hsum,hpower,?_⟩
  unfold seriesCharge
  have h1 := Nat.pow_le_pow_left hc1 3
  have h2 := Nat.pow_le_pow_left hc2 3
  have h3 := Nat.pow_le_pow_left hc3 3
  change _ ≤ 3*(4*F+7)^3
  omega

lemma logSeries_cost_size {z : ℚ} {Z : ℕ} (hz : QBound z Z) (L c : ℕ) :
    QBound ((logSeries z L).run c).1 (seriesSize Z L+2) ∧
    ((logSeries z L).run c).2 ≤ c+(3*L+2)*(4*seriesSize Z L+11)^3 := by
  let E := seriesTermSize Z L
  let F := seriesSize Z L
  let g := fun (i : ℕ) (ap : ℚ × ℚ) => (ap.1+ap.2/(2*(i:ℚ)+1),ap.2*(z*z))
  let P := fun i (ap : ℚ × ℚ) => QBound ap.1 (i*(E+1)) ∧ QBound ap.2 (Z*(2*i+1))
  let c0 := c+(ratBits z+ratBits z+1)^3
  have hloop := counted_forIn_run (List.range L) ((0:ℚ),z)
    (fun (i : ℕ) (ap : ℚ × ℚ) => do
      let y ← divQ ap.2 (2*(i:ℚ)+1)
      let a ← addQ ap.1 y
      let power ← mulQ ap.2 (z*z)
      pure (.yield (a,power))) g (seriesCharge z) (by
        intro i ap c
        simp only [counted_bind_run,divQ_run,addQ_run,mulQ_run,counted_pure_run,g,seriesCharge]
        congr 1 <;> omega) c0
  let y := (List.range L).foldl (fun az i => (g i az.1,az.2+seriesCharge z i az.1)) (((0:ℚ),z),c0)
  have hb : P L y.1 ∧ y.2 ≤ c0+L*(3*(4*F+7)^3) :=
    fold_pair_cost g (seriesCharge z) P L (3*(4*F+7)^3) (0,z) c0
      ⟨by simpa using QBound.zero,by simpa using hz⟩ (by
        intro i hi ap hap
        have hh := series_body_bound hz hi ap hap.1 hap.2
        exact ⟨⟨hh.1,hh.2.1⟩,hh.2.2⟩)
  have hsum : QBound y.1.1 F := hb.1.1.mono (by dsimp [F,seriesSize]; nlinarith)
  have htwo : QBound (2:ℚ) 2 := by norm_num [QBound]
  have hreturn : QBound (2*y.1.1) (F+2) := by simpa only [Nat.add_comm] using htwo.mul hsum
  have hzF : Z ≤ F := by dsimp [F,seriesSize]; nlinarith
  have hinit : (ratBits z+ratBits z+1)^3 ≤ (4*F+11)^3 := by
    apply Nat.pow_le_pow_left
    have hh := (hz.mono hzF).bits
    omega
  have hlast : (ratBits (2:ℚ)+ratBits y.1.1+1)^3 ≤ (4*F+11)^3 := by
    apply Nat.pow_le_pow_left
    have hh := hsum.bits
    have htwoBits : ratBits (2:ℚ)=4 := by decide
    omega
  have hbody : (4*F+7)^3 ≤ (4*F+11)^3 := Nat.pow_le_pow_left (by omega) 3
  unfold logSeries
  simp only [counted_bind_run,mulQ_run,counted_pure_run]
  rw [hloop]
  change QBound (2*y.1.1) (F+2) ∧ y.2+(ratBits (2:ℚ)+ratBits y.1.1+1)^3 ≤ c+(3*L+2)*(4*F+11)^3
  refine ⟨hreturn,?_⟩
  have hh := hb.2
  dsimp only [c0] at hh
  nlinarith only [hh,hinit,hlast,Nat.mul_le_mul_left (3*L) hbody]

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

def bisectQ (B : ℚ) (r : ℕ) (x : ℚ × ℚ) : ℚ × ℚ :=
  let mid := (x.1+x.2)/2
  if mid^r < B then (mid,x.2) else (x.1,mid)

lemma rootBracket_value (B : ℚ) (r h c : ℕ) : ((rootBracket B r h).run c).1 =
    (List.range (h+ratBits B+2)).foldl (fun x _ => bisectQ B r x) (1,max 1 B) := by
  unfold rootBracket
  simp only [counted_bind_value,counted_pure_value]
  apply counted_forIn_value
  intro i x z
  simp only [counted_bind_value,addQ_run,divQ_run,powQ_value,lessQ_run,counted_pure_value]
  dsimp only [bisectQ]
  simp only [decide_eq_true_eq]
  split_ifs <;> simp_all only [counted_pure_value]

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

 def DyadicBound (D L k : ℕ) (q : ℚ) : Prop :=
  ∃ a : ℤ,q=(a:ℚ)/(D*2^k:ℕ) ∧ a.natAbs ≤ 2^(L+k)

lemma DyadicBound.bound {D L k : ℕ} {q : ℚ} (hD : D ≠ 0) (hDL : D ≤ 2^L)
    (h : DyadicBound D L k q) : QBound q (L+k) := by
  rcases h with ⟨a,rfl,ha⟩
  exact QBound.fraction (Nat.mul_ne_zero hD (by positivity)) ha
    (by simpa only [pow_add] using Nat.mul_le_mul_right (2^k) hDL)

lemma DyadicBound.next {D L k : ℕ} {q : ℚ} (h : DyadicBound D L k q) :
    DyadicBound D L (k+1) q := by
  rcases h with ⟨a,ha,hab⟩
  refine ⟨2*a,?_,?_⟩
  · rw [ha]
    push_cast
    rw [pow_succ]
    ring
  · rw [Int.natAbs_mul]
    norm_num
    calc
      _ ≤ 2*2^(L+k) := Nat.mul_le_mul_left 2 hab
      _ = _ := by rw [show L+(k+1)=(L+k)+1 by omega,pow_succ]; ring

lemma DyadicBound.mid {D L k : ℕ} {a b : ℚ} (ha : DyadicBound D L k a)
    (hb : DyadicBound D L k b) : DyadicBound D L (k+1) ((a+b)/2) := by
  rcases ha with ⟨u,hu,hub⟩
  rcases hb with ⟨v,hv,hvb⟩
  refine ⟨u+v,?_,?_⟩
  · rw [hu,hv]
    push_cast
    rw [pow_succ]
    ring
  · calc
      _ ≤ u.natAbs+v.natAbs := Int.natAbs_add_le _ _
      _ ≤ 2^(L+k)+2^(L+k) := Nat.add_le_add hub hvb
      _ = _ := by rw [show L+(k+1)=(L+k)+1 by omega,pow_succ]; ring

lemma bisectQ_dyadic (B : ℚ) (r D L k : ℕ) (x : ℚ × ℚ)
    (hx : DyadicBound D L k x.1 ∧ DyadicBound D L k x.2) :
    DyadicBound D L (k+1) (bisectQ B r x).1 ∧ DyadicBound D L (k+1) (bisectQ B r x).2 := by
  have hm := hx.1.mid hx.2
  simp only [bisectQ]
  split_ifs
  · exact ⟨hm,hx.2.next⟩
  · exact ⟨hx.1.next,hm⟩

lemma root_initial_dyadic (B : ℚ) :
    DyadicBound B.den (ratBits B) 0 1 ∧ DyadicBound B.den (ratBits B) 0 (max 1 B) := by
  have hself := QBound.self B
  have hone : DyadicBound B.den (ratBits B) 0 1 := by
    refine ⟨B.den,by simp [B.den_ne_zero],?_⟩
    simpa using hself.2
  have hB : DyadicBound B.den (ratBits B) 0 B := by
    refine ⟨B.num,?_,?_⟩
    · simp only [pow_zero,Nat.mul_one]
      simpa only [Rat.divInt_eq_div,Int.cast_natCast] using (Rat.num_divInt_den B).symm
    · simpa using hself.1
  refine ⟨hone,?_⟩
  by_cases hb : 1 ≤ B
  · rw [max_eq_right hb]; exact hB
  · rw [max_eq_left (le_of_not_ge hb)]; exact hone

lemma bisectQ_fold_dyadic (B : ℚ) (r N : ℕ) :
    let y := (List.range N).foldl (fun x _ => bisectQ B r x) (1,max 1 B)
    DyadicBound B.den (ratBits B) N y.1 ∧ DyadicBound B.den (ratBits B) N y.2 := by
  induction N with
  | zero => simpa using root_initial_dyadic B
  | succ N ih =>
    rw [List.range_succ,List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil]
    exact bisectQ_dyadic B r B.den (ratBits B) N _ ih

lemma rootBracket_size (B : ℚ) (r h c : ℕ) :
    let y := ((rootBracket B r h).run c).1
    QBound y.1 (h+2*ratBits B+2) ∧ QBound y.2 (h+2*ratBits B+2) := by
  rw [rootBracket_value]
  have hh := bisectQ_fold_dyadic B r (h+ratBits B+2)
  have hn := (QBound.self B).2
  exact ⟨by simpa only [show ratBits B+(h+ratBits B+2)=h+2*ratBits B+2 by omega] using
    hh.1.bound B.den_ne_zero hn,
    by simpa only [show ratBits B+(h+ratBits B+2)=h+2*ratBits B+2 by omega] using hh.2.bound B.den_ne_zero hn⟩

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section

 def rootCharge (B : ℚ) (r : ℕ) (x : ℚ × ℚ) : ℕ :=
  let mid := (x.1+x.2)/2
  (ratBits x.1+ratBits x.2+1)^3+(ratBits (x.1+x.2)+ratBits 2+1)^3+
  (∑ i ∈ Finset.range r,(ratBits (mid^i)+ratBits mid+1)^3)+
  (ratBits (mid^r)+ratBits B+1)^3

lemma rootCharge_bound {B : ℚ} {r L : ℕ} {x : ℚ × ℚ}
    (hB : QBound B L) (hx : QBound x.1 L ∧ QBound x.2 L) :
    rootCharge B r x ≤ (r+3)*(20*(L+1)*(r+1))^3 := by
  let mid := (x.1+x.2)/2
  have htwo : QBound (2:ℚ) 2 := by norm_num [QBound]
  have hm : QBound mid (2*L+3) := by simpa only [mid,show L+L+1+2=2*L+3 by omega] using (hx.1.add hx.2).div htwo
  have hA : ratBits x.1+ratBits x.2+1 ≤ 20*(L+1)*(r+1) := by
    have h1 := hx.1.bits; have h2 := hx.2.bits
    nlinarith
  have hB' : ratBits (x.1+x.2)+ratBits (2:ℚ)+1 ≤ 20*(L+1)*(r+1) := by
    have h1 := (hx.1.add hx.2).bits
    have htwoBits : ratBits (2:ℚ)=4 := by decide
    rw [htwoBits]
    nlinarith
  have hP := powQ_cost hm r 0
  rw [powQ_run] at hP
  simp only [Prod.snd,Nat.zero_add] at hP
  have hP' : 2*(2*L+3)*(r+1)+7 ≤ 20*(L+1)*(r+1) := by nlinarith
  have hPower : (∑ i ∈ Finset.range r,(ratBits (mid^i)+ratBits mid+1)^3) ≤ r*(20*(L+1)*(r+1))^3 :=
    hP.trans (Nat.mul_le_mul_left r (Nat.pow_le_pow_left hP' 3))
  have hC : ratBits (mid^r)+ratBits B+1 ≤ 20*(L+1)*(r+1) := by
    have h1 := (hm.pow r).bits
    have h2 := hB.bits
    nlinarith
  unfold rootCharge
  have hAp := Nat.pow_le_pow_left hA 3
  have hBp := Nat.pow_le_pow_left hB' 3
  have hCp := Nat.pow_le_pow_left hC 3
  change _+_+(∑ i ∈ Finset.range r,(ratBits (mid^i)+ratBits mid+1)^3)+_ ≤ _
  nlinarith only [hAp,hBp,hCp,hPower]

lemma rootBracket_run (B : ℚ) (r h z : ℕ) : (rootBracket B r h).run z =
    (List.range (h+ratBits B+2)).foldl (fun xz _ =>
      (bisectQ B r xz.1,xz.2+rootCharge B r xz.1)) ((1,max 1 B),z) := by
  unfold rootBracket
  simp only [counted_bind_run,counted_pure_run]
  apply counted_forIn_run
  intro i x z
  simp only [counted_bind_run,addQ_run,divQ_run,powQ_run,lessQ_run,counted_pure_run]
  simp only [decide_eq_true_eq]
  unfold bisectQ rootCharge
  split_ifs <;> simp_all only [counted_pure_run,if_pos,if_neg,ite_true,ite_false,Nat.add_assoc]

lemma rootBracket_cost (B : ℚ) (r h z : ℕ) :
    ((rootBracket B r h).run z).2 ≤ z+
      (h+ratBits B+2)*(r+3)*(20*(h+2*ratBits B+3)*(r+1))^3 := by
  let N := h+ratBits B+2
  let L := h+2*ratBits B+2
  let P := fun i (x : ℚ × ℚ) => DyadicBound B.den (ratBits B) i x.1 ∧ DyadicBound B.den (ratBits B) i x.2
  have hp := fold_pair_cost (fun _ x => bisectQ B r x) (fun _ x => rootCharge B r x) P
    N ((r+3)*(20*(L+1)*(r+1))^3) (1,max 1 B) z (root_initial_dyadic B) (by
      intro i hi x hx
      refine ⟨bisectQ_dyadic B r B.den (ratBits B) i x hx,?_⟩
      have hL : ratBits B+i ≤ L := by dsimp [N,L] at *; omega
      have hd := (QBound.self B).2
      apply rootCharge_bound ((QBound.self B).mono (by dsimp [L]; omega))
      exact ⟨(hx.1.bound B.den_ne_zero hd).mono hL,(hx.2.bound B.den_ne_zero hd).mono hL⟩)
  rw [rootBracket_run]
  convert hp.2 using 1 <;> dsimp [N,L] <;> ring

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

 def Budget {α : Type} (x : Counted α) (P : α → Prop) (C : ℕ) : Prop :=
  ∀ z,P (x.run z).1 ∧ (x.run z).2 ≤ z+C

lemma Budget.pure {α : Type} (a : α) {P : α → Prop} (ha : P a) : Budget (pure a) P 0 := by
  intro z; exact ⟨ha,le_rfl⟩

lemma Budget.bind {α β : Type} {x : Counted α} {f : α → Counted β} {P : α → Prop} {Q : β → Prop}
    {C D : ℕ} (hx : Budget x P C) (hf : ∀ a,P a → Budget (f a) Q D) : Budget (x >>= f) Q (C+D) := by
  intro z
  rw [counted_bind_run]
  have h1 := hx z
  have h2 := hf _ h1.1 (x.run z).2
  exact ⟨h2.1,by omega⟩

lemma Budget.weaken {α : Type} {x : Counted α} {P Q : α → Prop} {C D : ℕ}
    (hx : Budget x P C) (hP : ∀ a,P a → Q a) (hC : C ≤ D) : Budget x Q D := by
  intro z
  exact ⟨hP _ (hx z).1,(hx z).2.trans (Nat.add_le_add_left hC z)⟩

lemma Budget.charge (c : ℕ) : Budget (charge c) (fun _ => True) c := by
  intro z; exact ⟨True.intro,le_rfl⟩

lemma Budget.op {a b : ℚ} {L M N : ℕ} (op : ℚ → ℚ → ℚ) (ha : QBound a L) (hb : QBound b M)
    (hres : QBound (op a b) N) :
    Budget (rationalOp op a b) (fun q => QBound q N) ((2*L+2*M+7)^3) := by
  intro z
  rw [rationalOp_run]
  refine ⟨hres,Nat.add_le_add_left (Nat.pow_le_pow_left ?_ 3) z⟩
  have h1 := ha.bits; have h2 := hb.bits
  omega

lemma Budget.add {a b : ℚ} {L M : ℕ} (ha : QBound a L) (hb : QBound b M) :
    Budget (addQ a b) (fun q => QBound q (L+M+1)) ((2*L+2*M+7)^3) := Budget.op _ ha hb (ha.add hb)
lemma Budget.sub {a b : ℚ} {L M : ℕ} (ha : QBound a L) (hb : QBound b M) :
    Budget (subQ a b) (fun q => QBound q (L+M+1)) ((2*L+2*M+7)^3) := Budget.op _ ha hb (ha.sub hb)
lemma Budget.mul {a b : ℚ} {L M : ℕ} (ha : QBound a L) (hb : QBound b M) :
    Budget (mulQ a b) (fun q => QBound q (L+M)) ((2*L+2*M+7)^3) := Budget.op _ ha hb (ha.mul hb)
lemma Budget.div {a b : ℚ} {L M : ℕ} (ha : QBound a L) (hb : QBound b M) :
    Budget (divQ a b) (fun q => QBound q (L+M)) ((2*L+2*M+7)^3) := Budget.op _ ha hb (ha.div hb)

lemma Budget.pow {a : ℚ} {L : ℕ} (ha : QBound a L) (r : ℕ) :
    Budget (powQ a r) (fun q => QBound q (L*r)) (r*(2*L*(r+1)+7)^3) := by
  intro z
  exact ⟨by rw [powQ_value]; exact ha.pow r,powQ_cost ha r z⟩

lemma Budget.series {a : ℚ} {L : ℕ} (ha : QBound a L) (r : ℕ) :
    Budget (logSeries a r) (fun q => QBound q (seriesSize L r+2))
      ((3*r+2)*(4*seriesSize L r+11)^3) := fun z => logSeries_cost_size ha r z

lemma Budget.root (B : ℚ) (r h : ℕ) :
    Budget (rootBracket B r h) (fun q => QBound q.1 (h+2*ratBits B+2) ∧ QBound q.2 (h+2*ratBits B+2))
      ((h+ratBits B+2)*(r+3)*(20*(h+2*ratBits B+3)*(r+1))^3) := by
  intro z
  exact ⟨rootBracket_size B r h z,rootBracket_cost B r h z⟩

lemma QBound.max_zero {a : ℚ} {L : ℕ} (ha : QBound a L) : QBound (max 0 a) L := by
  by_cases h : 0≤a
  · rw [max_eq_right h]; exact ha
  · rw [max_eq_left (le_of_not_ge h)]; exact QBound.zero.mono (Nat.zero_le _)

lemma Budget.less {a b : ℚ} {L M : ℕ} (ha : QBound a L) (hb : QBound b M) :
    Budget (lessQ a b) (fun _ => True) ((2*L+2*M+7)^3) := by
  intro z
  rw [lessQ_run]
  refine ⟨True.intro,Nat.add_le_add_left (Nat.pow_le_pow_left ?_ 3) z⟩
  have h1 := ha.bits; have h2 := hb.bits
  omega

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section
set_option maxHeartbeats 300000

 def logSize (Y h : ℕ) : ℕ :=
  let L := h+Y+10
  let F1 := seriesSize 2 L+2
  let F2 := seriesSize (6*Y+2) L+2
  2*Y+F1+F2+4*L+7

 def logCost (Y h : ℕ) : ℕ :=
  let L := h+Y+10
  let F1 := seriesSize 2 L+2
  let F2 := seriesSize (6*Y+2) L+2
  let U := Y+F1+F2+2
  let V := Y+4+4*L
  (Y+1)^3+(Y*(4*(Y+1)+7)^3+((6*Y+7)^3+
    ((3*L+2)*(4*seriesSize 2 L+11)^3+((6*Y+7)^3+((6*Y+7)^3+((12*Y+11)^3+
    ((3*L+2)*(4*seriesSize (6*Y+2) L+11)^3+((2*(Y+1)+2*F1+7)^3+
    ((2*(Y+1+F1)+2*F2+7)^3+(L*(8*(L+1)+7)^3+((2*(Y+4)+8*L+7)^3+
    ((2*U+2*V+7)^3+0))))))))))))

lemma logBracket_budget (y : ℚ) (h : ℕ) :
    Budget (logBracket y h) (fun v => QBound v.1 (logSize (ratBits y) h) ∧ QBound v.2 (logSize (ratBits y) h))
      (logCost (ratBits y) h) := by
  let Y := ratBits y
  let k := (y.num.natAbs/y.den).log2
  let L := h+Y+10
  let F1 := seriesSize 2 L+2
  let F2 := seriesSize (6*Y+2) L+2
  let U := Y+F1+F2+2
  let V := Y+4+4*L
  have hy : QBound y Y := QBound.self y
  have hk : k ≤ Y := normalize_exp_le_bits y
  have htwo : QBound (2:ℚ) 2 := by norm_num [QBound]
  have hone : QBound (1:ℚ) 0 := QBound.one
  have hthird : QBound (1/3:ℚ) 2 := by norm_num [QBound]
  have hnine : QBound (9:ℚ) 4 := by norm_num [QBound]
  have hthree : QBound (3:ℚ) 2 := by norm_num [QBound]
  have hknat : QBound (k:ℚ) (Y+1) := (QBound.nat k).mono ((bits_le k).trans (by omega))
  have hkplus : QBound ((k:ℚ)+1) (Y+2) := by
    exact (hknat.add hone).mono (by omega)
  have hnum : QBound (3*((k:ℚ)+1)) (Y+4) := by simpa only [Nat.add_comm 2] using hthree.mul hkplus
  have hpow2 : Budget (powQ 2 k) (fun q => QBound q (2*Y)) (Y*(4*(Y+1)+7)^3) :=
    (Budget.pow htwo k).weaken (fun _ hh => hh.mono (by omega)) (by gcongr <;> omega)
  unfold logBracket logCost
  change Budget (do
    charge ((Y+1)^3)
    let z ← divQ y (← powQ 2 k)
    let ln₂ ← logSeries (1/3) L
    let a ← logSeries (← divQ (← subQ z 1) (← addQ z 1)) L
    let lo ← addQ (← mulQ k ln₂) a
    let err ← divQ (3*((k:ℚ)+1)) (← powQ 9 L)
    pure (lo,← addQ lo err)) _ _
  refine (Budget.charge ((Y+1)^3)).bind (fun _ _ => ?_)
  refine hpow2.bind (fun p hp => ?_)
  have hzdiv : Budget (divQ y p) (fun z => QBound z (3*Y)) ((6*Y+7)^3) := by
    exact (Budget.div hy hp).weaken (fun _ hh => hh.mono (by omega)) (Nat.pow_le_pow_left (by omega) 3)
  refine hzdiv.bind (fun z hz => ?_)
  refine (Budget.series hthird L).bind (fun ln2 hln2 => ?_)
  have hzsub : Budget (subQ z 1) (fun a => QBound a (3*Y+1)) ((6*Y+7)^3) := by
    exact (Budget.sub hz hone).weaken (fun _ hh => hh.mono (by omega)) (Nat.pow_le_pow_left (by omega) 3)
  refine hzsub.bind (fun a ha => ?_)
  have hzadd : Budget (addQ z 1) (fun a => QBound a (3*Y+1)) ((6*Y+7)^3) := by
    exact (Budget.add hz hone).weaken (fun _ hh => hh.mono (by omega)) (Nat.pow_le_pow_left (by omega) 3)
  refine hzadd.bind (fun aa haa => ?_)
  have hzquot : Budget (divQ a aa) (fun q => QBound q (6*Y+2)) ((12*Y+11)^3) := by
    exact (Budget.div ha haa).weaken (fun _ hh => hh.mono (by omega)) (Nat.pow_le_pow_left (by omega) 3)
  refine hzquot.bind (fun zz hzz => ?_)
  refine (Budget.series hzz L).bind (fun logz hlogz => ?_)
  refine (Budget.mul hknat hln2).bind (fun kl hkln => ?_)
  refine (Budget.add hkln hlogz).bind (fun lo hlo => ?_)
  refine (Budget.pow hnine L).bind (fun power hpower => ?_)
  have herr : Budget (divQ (3*((k:ℚ)+1)) power) (fun q => QBound q V) ((2*(Y+4)+8*L+7)^3) := by
    exact (Budget.div hnum hpower).weaken (fun _ hh => hh.mono (by dsimp [V]; omega)) (Nat.pow_le_pow_left (by omega) 3)
  refine herr.bind (fun err he => ?_)
  have hlo' : QBound lo U := hlo.mono (by dsimp only [U,F1,F2]; omega)
  have hlast : Budget (addQ lo err) (fun q => QBound q (U+V+1)) ((2*U+2*V+7)^3) := Budget.add hlo' he
  refine hlast.bind (fun upper hupper => ?_)
  apply Budget.pure
  have heq : U+V+1=logSize Y h := by dsimp [U,V,F1,F2,L,logSize]; ring
  rw [← heq]
  exact ⟨hlo'.mono (by omega),hupper⟩

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

inductive CostExpr where
  | constant : ℕ → CostExpr
  | input : ℕ → CostExpr
  | add : CostExpr → CostExpr → CostExpr
  | mul : CostExpr → CostExpr → CostExpr
  | pow : CostExpr → ℕ → CostExpr

def CostExpr.eval (xs : ℕ → ℕ) : CostExpr → ℕ
  | .constant c => c
  | .input i => xs i
  | .add a b => a.eval xs+b.eval xs
  | .mul a b => a.eval xs*b.eval xs
  | .pow a r => a.eval xs^r

def CostExpr.degree : CostExpr → ℕ
  | .constant _ => 0
  | .input _ => 1
  | .add a b => max a.degree b.degree
  | .mul a b => a.degree+b.degree
  | .pow a r => a.degree*r

def CostExpr.mass (a : CostExpr) : ℕ := a.eval (fun _ => 1)

lemma CostExpr.eval_mono (a : CostExpr) {xs ys : ℕ → ℕ} (h : ∀ i,xs i ≤ ys i) : a.eval xs ≤ a.eval ys := by
  induction a with
  | constant c => rfl
  | input i => exact h i
  | add a b ha hb => exact Nat.add_le_add ha hb
  | mul a b ha hb => exact Nat.mul_le_mul ha hb
  | pow a r ha => exact Nat.pow_le_pow_left ha r

lemma CostExpr.bound (a : CostExpr) {xs : ℕ → ℕ} {E : ℕ} (hE : 1 ≤ E) (h : ∀ i,xs i ≤ E) :
    a.eval xs ≤ a.mass*E^a.degree := by
  induction a with
  | constant c => simp [eval,mass,degree]
  | input i => simpa [eval,mass,degree] using h i
  | add a b ha hb =>
    have h1 := ha.trans (Nat.mul_le_mul_left a.mass (Nat.pow_le_pow_right hE (le_max_left a.degree b.degree)))
    have h2 := hb.trans (Nat.mul_le_mul_left b.mass (Nat.pow_le_pow_right hE (le_max_right a.degree b.degree)))
    change a.eval xs+b.eval xs ≤ (a.mass+b.mass)*E^(max a.degree b.degree)
    nlinarith only [h1,h2]
  | mul a b ha hb =>
    have hh := Nat.mul_le_mul ha hb
    change a.eval xs*b.eval xs ≤ (a.mass*b.mass)*E^(a.degree+b.degree)
    convert hh using 1 <;> rw [pow_add] <;> ring
  | pow a r ha =>
    have hh := Nat.pow_le_pow_left ha r
    change a.eval xs^r ≤ a.mass^r*E^(a.degree*r)
    simpa only [mul_pow,pow_mul] using hh

lemma CostExpr.bound_larger (a : CostExpr) {xs : ℕ → ℕ} {E k : ℕ} (hE : 1 ≤ E)
    (h : ∀ i,xs i ≤ E) (hk : a.degree ≤ k) : a.eval xs ≤ a.mass*E^k :=
  (a.bound hE h).trans (Nat.mul_le_mul_left a.mass (Nat.pow_le_pow_right hE hk))

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

instance (n : ℕ) : OfNat CostExpr n := ⟨CostExpr.constant n⟩
instance : Add CostExpr := ⟨CostExpr.add⟩
instance : Mul CostExpr := ⟨CostExpr.mul⟩
instance : HPow CostExpr ℕ CostExpr := ⟨CostExpr.pow⟩

 def seriesTermSizeExpr (Z L : CostExpr) : CostExpr := Z*(2*L+1)+2*L+2
 def seriesSizeExpr (Z L : CostExpr) : CostExpr := (L+1)*(seriesTermSizeExpr Z L+1)+2*Z+2*L+10
 def logSizeExpr (Y h : CostExpr) : CostExpr :=
  let L := h+Y+10
  let F1 := seriesSizeExpr 2 L+2
  let F2 := seriesSizeExpr (6*Y+2) L+2
  2*Y+F1+F2+4*L+7

 def logCostExpr (Y h : CostExpr) : CostExpr :=
  let L := h+Y+10
  let F1 := seriesSizeExpr 2 L+2
  let F2 := seriesSizeExpr (6*Y+2) L+2
  let U := Y+F1+F2+2
  let V := Y+4+4*L
  (Y+1)^3+(Y*(4*(Y+1)+7)^3+((6*Y+7)^3+
    ((3*L+2)*(4*seriesSizeExpr 2 L+11)^3+((6*Y+7)^3+((6*Y+7)^3+((12*Y+11)^3+
    ((3*L+2)*(4*seriesSizeExpr (6*Y+2) L+11)^3+((2*(Y+1)+2*F1+7)^3+
    ((2*(Y+1+F1)+2*F2+7)^3+(L*(8*(L+1)+7)^3+((2*(Y+4)+8*L+7)^3+
    ((2*U+2*V+7)^3+0))))))))))))

lemma seriesTermSizeExpr_eval (Z L : CostExpr) (xs : ℕ → ℕ) :
    (seriesTermSizeExpr Z L).eval xs=seriesTermSize (Z.eval xs) (L.eval xs) := rfl
lemma seriesSizeExpr_eval (Z L : CostExpr) (xs : ℕ → ℕ) :
    (seriesSizeExpr Z L).eval xs=seriesSize (Z.eval xs) (L.eval xs) := rfl
lemma logSizeExpr_eval (Y h : CostExpr) (xs : ℕ → ℕ) :
    (logSizeExpr Y h).eval xs=logSize (Y.eval xs) (h.eval xs) := rfl
lemma logCostExpr_eval (Y h : CostExpr) (xs : ℕ → ℕ) :
    (logCostExpr Y h).eval xs=logCost (Y.eval xs) (h.eval xs) := rfl

lemma logSize_mono {Y h Z k : ℕ} (hY : Y ≤ Z) (hh : h ≤ k) : logSize Y h ≤ logSize Z k := by
  let xs := fun i : ℕ => if i=0 then Y else h
  let ys := fun i : ℕ => if i=0 then Z else k
  have hx : ∀ i,xs i ≤ ys i := by intro i; dsimp [xs,ys]; split_ifs <;> assumption
  have hm := (logSizeExpr (.input 0) (.input 1)).eval_mono hx
  rw [logSizeExpr_eval,logSizeExpr_eval] at hm
  simpa only [CostExpr.eval,xs,ys,ite_true,if_neg (by decide : ¬(1:ℕ)=0)] using hm

lemma logCost_mono {Y h Z k : ℕ} (hY : Y ≤ Z) (hh : h ≤ k) : logCost Y h ≤ logCost Z k := by
  let xs := fun i : ℕ => if i=0 then Y else h
  let ys := fun i : ℕ => if i=0 then Z else k
  have hx : ∀ i,xs i ≤ ys i := by intro i; dsimp [xs,ys]; split_ifs <;> assumption
  have hm := (logCostExpr (.input 0) (.input 1)).eval_mono hx
  rw [logCostExpr_eval,logCostExpr_eval] at hm
  simpa only [CostExpr.eval,xs,ys,ite_true,if_neg (by decide : ¬(1:ℕ)=0)] using hm

lemma logBracket_budget_bound {y : ℚ} {Y : ℕ} (hy : ratBits y ≤ Y) (h : ℕ) :
    Budget (logBracket y h) (fun v => QBound v.1 (logSize Y h) ∧ QBound v.2 (logSize Y h)) (logCost Y h) :=
  (logBracket_budget y h).weaken (fun _ hh => ⟨hh.1.mono (logSize_mono hy le_rfl),hh.2.mono (logSize_mono hy le_rfl)⟩)
    (logCost_mono hy le_rfl)

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

 def stageCost (n t Y h : ℕ) : ℕ :=
  let R := 2*t
  let Z := h+4*Y+12
  let S := logSize (2*n+2*Z+10) h
  let L := logCost (2*n+2*Z+10) h
  let U := (20*(Z+S+1)*(R+1))^3
  let Croot := (h+2*Y+7)*(R+3)*(20*(h+4*Y+13)*(R+1))^3
  (2*Y+7)^3+(Croot+(L+(L+(L+(U+(U+(R*U+(U+(R*U+(U+(U+(U+(U+0)))))))))))))

lemma parameterStage_budget (Δ t n : ℕ) (b : ℚ) (h : ℕ) (hΔn : Δ ≤ n) :
    Budget (parameterStage Δ t b h) (fun _ => True) (stageCost n t (ratBits b) h) := by
  let Y := ratBits b
  let R := 2*t
  let r := 2*t-1
  let Z := h+4*Y+12
  let Q := 2*n+2*Z+10
  let S := logSize Q h
  let L := logCost Q h
  let F := 2*S+1
  let M := Z+F*R
  let U := (20*(Z+S+1)*(R+1))^3
  let Croot := (h+2*Y+7)*(R+3)*(20*(h+4*Y+13)*(R+1))^3
  have hr : r ≤ R := Nat.sub_le _ _
  have hb : QBound b Y := QBound.self b
  have hone : QBound (1:ℚ) 0 := QBound.one
  have hhalf : QBound (1/2:ℚ) 1 := by norm_num [QBound]
  have hΔbits : ratBits (Δ:ℚ)  ≤  Q := by
    have hh := (QBound.nat Δ).bits
    have hd := bits_le Δ
    dsimp only [Q]
    omega
  have hlogΔ : Budget (logBracket (Δ:ℚ) h) (fun v => QBound v.1 S ∧ QBound v.2 S) L :=
    logBracket_budget_bound hΔbits h
  have hop (a b : ℚ) (ha : QBound a S) (hb : QBound b S) :
      Budget (subQ a b) (fun q => QBound q F) U := by
    exact (Budget.sub ha hb).weaken (fun _ hh => hh.mono (by dsimp only [F]; omega))
      (Nat.pow_le_pow_left (by nlinarith : 2*S+2*S+7  ≤  20*(Z+S+1)*(R+1)) 3)
  have hpow (a : ℚ) (ha : QBound a F) : Budget (powQ a r) (fun q => QBound q (F*R)) (R*U) := by
    apply (Budget.pow ha r).weaken (fun _ hh => hh.mono (Nat.mul_le_mul_left F hr))
    apply Nat.mul_le_mul hr
    apply Nat.pow_le_pow_left
    dsimp only [F,U]
    nlinarith
  have hmul (a b : ℚ) (ha : QBound a Z) (hb : QBound b (F*R)) :
      Budget (mulQ a b) (fun q => QBound q M) U := by
    exact (Budget.mul ha hb).weaken (fun _ hh => hh) (Nat.pow_le_pow_left (by dsimp only [F]; nlinarith) 3)
  have hwidth (a b : ℚ) (ha : QBound a M) (hb : QBound b M) :
      Budget (subQ a b) (fun q => QBound q (2*M+1)) U := by
    apply (Budget.sub ha hb).weaken (fun _ hh => hh.mono (by omega))
    apply Nat.pow_le_pow_left
    dsimp only [M,F]
    nlinarith
  have htest (a : ℚ) (ha : QBound a (2*M+1)) : Budget (lessQ (1/2) a) (fun _ => True) U := by
    apply (Budget.less hhalf ha).weaken (fun _ _ => True.intro)
    apply Nat.pow_le_pow_left
    dsimp only [M,F]
    nlinarith
  have hceil (a : ℚ) (ha : QBound a M) : (ratBits a+1)^3  ≤  U := by
    apply Nat.pow_le_pow_left
    have hh := ha.bits
    dsimp only [M,F] at hh
    nlinarith
  unfold parameterStage stageCost
  change Budget (do
    let B ← addQ b 1
    let (sl,sh) ← rootBracket B r h
    let (dl,dh) ← logBracket Δ h
    let (ll,_) ← logBracket sl h
    let (_,hh) ← logBracket sh h
    let lowD ← subQ dl hh
    let highD ← subQ dh ll
    let xl ← mulQ sl (← powQ (max 0 lowD) r)
    let xh ← mulQ sh (← powQ (max 0 highD) r)
    let width ← subQ xh xl
    if ← lessQ (1/2) width then pure none else
      charge ((ratBits xh+1)^3)
      pure (some (max 1 (Int.toNat ⌈xh⌉),xl,xh))) _ _
  have hadd : Budget (addQ b 1) (fun B => QBound B (Y+1)) ((2*Y+7)^3) := by
    exact (Budget.add hb hone).weaken (fun _ hh => hh) (Nat.pow_le_pow_left (by omega) 3)
  refine hadd.bind (fun B hB => ?_)
  have hBB : ratBits B ≤ 2*Y+5 := by have hh := hB.bits; omega
  have hroot : Budget (rootBracket B r h) (fun v => QBound v.1 Z ∧ QBound v.2 Z) Croot := by
    apply (Budget.root B r h).weaken
    · intro v hv
      exact ⟨hv.1.mono (by dsimp only [Z]; omega),hv.2.mono (by dsimp only [Z]; omega)⟩
    · have h1 : h+ratBits B+2  ≤  h+2*Y+7 := by omega
      have h2 : r+3 ≤ R+3 := by omega
      have h3 : 20*(h+2*ratBits B+3)*(r+1)  ≤  20*(h+4*Y+13)*(R+1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 20 (by omega)) (by omega)
      exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) (Nat.pow_le_pow_left h3 3)
  refine hroot.bind (fun v hv => ?_)
  rcases v with ⟨sl,sh⟩
  have hslBits : ratBits sl ≤ Q := by
    have hh : ratBits sl ≤ 2*Z+3 := hv.1.bits
    dsimp only [Q]; omega
  have hshBits : ratBits sh ≤ Q := by
    have hh : ratBits sh ≤ 2*Z+3 := hv.2.bits
    dsimp only [Q]; omega
  refine hlogΔ.bind (fun a ha => ?_)
  rcases a with ⟨dl,dh⟩
  refine (logBracket_budget_bound hslBits h).bind (fun l hl => ?_)
  rcases l with ⟨ll,lh⟩
  refine (logBracket_budget_bound hshBits h).bind (fun u hu => ?_)
  rcases u with ⟨ul,uh⟩
  refine (hop dl uh ha.1 hu.2).bind (fun lowD hlow => ?_)
  refine (hop dh ll ha.2 hl.1).bind (fun highD hhigh => ?_)
  refine (hpow (max 0 lowD) hlow.max_zero).bind (fun lowpow hlp => ?_)
  refine (hmul sl lowpow hv.1 hlp).bind (fun xl hxl => ?_)
  refine (hpow (max 0 highD) hhigh.max_zero).bind (fun highpow hhp => ?_)
  refine (hmul sh highpow hv.2 hhp).bind (fun xh hxh => ?_)
  refine (hwidth xh xl hxh hxl).bind (fun width hw => ?_)
  refine (htest width hw).bind (fun flag _ => ?_)
  cases flag
  · simp only [Bool.false_eq_true,ite_false]
    have hc : Budget (charge ((ratBits xh+1)^3)) (fun _ => True) U :=
      (Budget.charge _).weaken (fun _ _ => True.intro) (hceil xh hxh)
    exact hc.bind (fun _ _ => Budget.pure _ True.intro)
  · simp only [ite_true]
    exact (Budget.pure none (P := fun _ => True) True.intro).weaken (fun _ _ => True.intro) (Nat.zero_le (U+0))

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma empty_hardcore (G : SimpleGraph V) : MarkovMixing.IsHardcore G (fun _ => false) := by
  intro v w h
  simp

instance stateNonempty (G : SimpleGraph V) : Nonempty (State G) :=
  ⟨⟨_, empty_hardcore G⟩⟩

lemma hcWeight_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (σ : V → Bool) : 0 ≤ MarkovMixing.hardcoreWeight G lam σ := by
  unfold MarkovMixing.hardcoreWeight
  split_ifs
  · exact le_of_lt (pow_pos hlam _)
  · rfl

lemma hcPartition_pos (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) : 0 < ∑ σ : V → Bool, MarkovMixing.hardcoreWeight G lam σ := by
  apply Finset.sum_pos'
  · intro σ hσ
    exact hcWeight_nonneg G hlam σ
  · refine ⟨fun _ => false, Finset.mem_univ _, ?_⟩
    simp [MarkovMixing.hardcoreWeight, empty_hardcore]

lemma hcLaw_pos (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (σ : State G) : 0 < HardCoreBochner.hcLaw G lam σ := by
  apply div_pos _ (hcPartition_pos G hlam)
  simp only [MarkovMixing.hardcoreWeight, if_pos σ.property]
  exact pow_pos hlam _

lemma hcLaw_dist (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) : MarkovMixing.IsDist (HardCoreBochner.hcLaw G lam) := by
  constructor
  · intro σ; exact (hcLaw_pos G hlam σ).le
  · unfold HardCoreBochner.hcLaw MarkovMixing.hardcoreDist
    rw [← Finset.sum_div]
    have heq : (∑ σ : State G, MarkovMixing.hardcoreWeight G lam σ.val) =
        ∑ σ : V → Bool, MarkovMixing.hardcoreWeight G lam σ := by
      calc
        _ = ∑ σ ∈ Finset.univ.filter (MarkovMixing.IsHardcore G),
            MarkovMixing.hardcoreWeight G lam σ :=
          (Finset.sum_subtype _ (by simp) _).symm
        _ = _ := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro σ _
          by_cases hs : MarkovMixing.IsHardcore G σ <;>
            simp [hs, MarkovMixing.hardcoreWeight]
    rw [heq, div_self (ne_of_gt (hcPartition_pos G hlam))]

lemma heatBath_stochastic (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (A : Finset V) : MarkovMixing.IsStochastic (heatBath G lam A) := by
  classical
  have hp := hcLaw_pos G hlam
  have hden (σ : State G) : 0 < ∑ ζ : State G,
      if ∀ v ∉ A, ζ.val v = σ.val v then HardCoreBochner.hcLaw G lam ζ else 0 := by
    apply Finset.sum_pos'
    · intro ζ _
      split_ifs
      · exact (hp ζ).le
      · rfl
    · exact ⟨σ, Finset.mem_univ _, by simpa using hp σ⟩
  constructor
  · intro σ τ
    unfold heatBath
    split_ifs
    · exact (div_pos (hp τ) (hden σ)).le
    · rfl
  · intro σ
    unfold heatBath
    simp_rw [show ∀ (c : Prop) [Decidable c] (a b : ℝ), (if c then a / b else 0) = (if c then a else 0) / b from fun c _ a b => by split_ifs <;> simp]
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (hden σ))

lemma push_dist {Ω : Type} [Fintype Ω] {ν : Ω → ℝ} {K : Matrix Ω Ω ℝ}
    (hν : MarkovMixing.IsDist ν) (hK : MarkovMixing.IsStochastic K) :
    MarkovMixing.IsDist (push ν K) := by
  constructor
  · intro y
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (hν.1 x) (hK.1 x y))
  · change (∑ y, ∑ x, ν x * K x y) = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hK.2, mul_one]
    exact hν.2

lemma finite_pinsker {Ω : Type} [Fintype Ω] [Nonempty Ω] {ν μ : Ω → ℝ}
    (hν : MarkovMixing.IsDist ν) (hμ : MarkovMixing.IsDist μ) (hd : Dominated ν μ) :
    2 * tv ν μ ^ 2 ≤ kl ν μ := by
  classical
  have h := SinkhornHall.lemma_1_1 ν μ hν.1 hμ.1 (hν.2.trans hμ.2.symm)
  have hn : ¬ ∃ x, μ x = 0 ∧ 0 < ν x := by
    rintro ⟨x, hx, hv⟩
    have := hd x hv.ne'
    linarith
  rw [SinkhornHall.klDiv, if_neg hn, hν.2] at h
  have he : kl ν μ = ∑ x, ν x * Real.log (ν x / μ x) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : ν x = 0 <;> simp [hx]
  rw [he]
  have hr : (∑ x, |ν x - μ x|) ^ 2 / 2 ≤ ∑ x, ν x * Real.log (ν x / μ x) := by
    exact_mod_cast h
  unfold tv
  nlinarith

lemma heatBath_dominated (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (A : Finset V) {ν : State G → ℝ}
    (hν : MarkovMixing.IsDist ν) : Dominated ν (push ν (heatBath G lam A)) := by
  classical
  intro σ hσ
  have hd : 0 < ∑ ζ : State G,
      if ∀ v ∉ A, ζ.val v = σ.val v then HardCoreBochner.hcLaw G lam ζ else 0 := by
    apply Finset.sum_pos'
    · intro ζ _
      split_ifs
      · exact (hcLaw_pos G hlam ζ).le
      · rfl
    · exact ⟨σ, Finset.mem_univ _, by simpa using hcLaw_pos G hlam σ⟩
  have hdiag : 0 < heatBath G lam A σ σ := by
    simpa [heatBath] using div_pos (hcLaw_pos G hlam σ) hd
  have hσpos : 0 < ν σ := lt_of_le_of_ne (hν.1 σ) (Ne.symm hσ)
  have hstoch := heatBath_stochastic G hlam A
  exact (mul_pos hσpos hdiag).trans_le
    (Finset.single_le_sum (fun x _ => mul_nonneg (hν.1 x) (hstoch.1 x σ)) (Finset.mem_univ σ))

lemma kl_eq_sum {Ω : Type} [Fintype Ω] (ν μ : Ω → ℝ) :
    kl ν μ = ∑ x, ν x * Real.log (ν x / μ x) := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ν x = 0 <;> simp [hx]


end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma full_fiber_sum (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (σ : State G) (u : V) :
    (∑ ζ : State G, if ∀ v, v ≠ u → ζ.val v = σ.val v then HardCoreBochner.hcLaw G lam ζ else 0) =
    ∑ ζ ∈ Finset.univ.filter (fun ζ : V → Bool => ∀ v, v ≠ u → ζ v = σ.val v),
      MarkovMixing.hardcoreDist G lam ζ := by
  classical
  calc
    _ = ∑ ζ ∈ Finset.univ.filter (MarkovMixing.IsHardcore G),
        if ∀ v, v ≠ u → ζ v = σ.val v then MarkovMixing.hardcoreDist G lam ζ else 0 := by
      exact (Finset.sum_subtype (p := MarkovMixing.IsHardcore G)
        (Finset.univ.filter (MarkovMixing.IsHardcore G)) (by intro ζ; simp)
        (fun ζ => if ∀ v, v ≠ u → ζ v = σ.val v then MarkovMixing.hardcoreDist G lam ζ else 0)).symm
    _ = _ := by
      simp_rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ζ _
      by_cases hz : MarkovMixing.IsHardcore G ζ
      · simp [hz]
      · simp [hz, MarkovMixing.hardcoreDist, MarkovMixing.hardcoreWeight]

lemma scan_eq (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) :
    K G lam = (Fintype.card V : ℝ)⁻¹ • ∑ u, P G lam u := by
  classical
  ext σ τ
  simp only [K, HardCoreBochner.hcChain, MarkovMixing.subChain, MarkovMixing.glauber,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  simp only [P, heatBath, Finset.mem_singleton]
  rw [full_fiber_sum]
  rfl

lemma scan_stochastic [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam) : MarkovMixing.IsStochastic (K G lam) := by
  classical
  rw [scan_eq]
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  constructor
  · intro σ τ
    simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    change 0 ≤ (Fintype.card V : ℝ)⁻¹ * ∑ u, P G lam u σ τ
    exact mul_nonneg (inv_nonneg.mpr hn.le)
      (Finset.sum_nonneg (fun u _ => (heatBath_stochastic G hlam {u}).1 σ τ))
  · intro σ
    simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    change (∑ τ, (Fintype.card V : ℝ)⁻¹ * ∑ u, P G lam u σ τ) = 1
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hrow (u : V) : ∑ τ, P G lam u σ τ = 1 := (heatBath_stochastic G hlam {u}).2 σ
    simp_rw [hrow]
    simp [hn.ne']

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma update_false_hardcore (G : SimpleGraph V) {σ : V → Bool}
    (hσ : MarkovMixing.IsHardcore G σ) (u : V) :
    MarkovMixing.IsHardcore G (Function.update σ u false) := by
  intro v w hvw
  by_cases hv : v = u
  · subst v; simp
  by_cases hw : w = u
  · subst w; simp
  simpa [Function.update_of_ne hv, Function.update_of_ne hw] using hσ v w hvw

lemma update_true_hardcore (G : SimpleGraph V) [DecidableRel G.Adj] {σ : V → Bool}
    (hσ : MarkovMixing.IsHardcore G σ) (u : V)
    (hu : ∀ v ∈ G.neighborFinset u, σ v = false) :
    MarkovMixing.IsHardcore G (Function.update σ u true) := by
  intro v w hvw
  by_cases hv : v = u
  · subst v
    have hw : w ≠ u := G.ne_of_adj hvw.symm
    simp [Function.update_of_ne hw, hu w (by simpa using hvw)]
  by_cases hw : w = u
  · subst w
    simp [Function.update_of_ne hv, hu v (by simpa using hvw.symm)]
  simpa [Function.update_of_ne hv, Function.update_of_ne hw] using hσ v w hvw

lemma spin_hardcore (G : SimpleGraph V) [DecidableRel G.Adj] (σ : State G)
    (u : V) (coin : Bool) : MarkovMixing.IsHardcore G (updateSpin G σ.val u coin) := by
  unfold updateSpin
  split_ifs with h
  · cases coin
    · exact update_false_hardcore G σ.property u
    · exact update_true_hardcore G σ.property u h
  · exact update_false_hardcore G σ.property u

lemma size_update_true (σ : V → Bool) (u : V) :
    size (Function.update σ u true) = size (Function.update σ u false) + 1 := by
  classical
  have hset : (Finset.univ.filter (fun v => Function.update σ u true v = true)) =
      insert u (Finset.univ.filter (fun v => Function.update σ u false v = true)) := by
    ext v
    by_cases hv : v = u <;> simp [hv, Function.update_of_ne]
  have hu : u ∉ Finset.univ.filter (fun v => Function.update σ u false v = true) := by simp
  unfold size
  rw [hset, Finset.card_insert_of_notMem hu]

lemma exterior_two (σ τ : V → Bool) (u : V)
    (he : ∀ v, v ≠ u → τ v = σ v) :
    τ = Function.update σ u false ∨ τ = Function.update σ u true := by
  have hu : τ = Function.update σ u (τ u) := by
    ext v
    by_cases hv : v = u
    · simp [hv]
    · simp [Function.update_of_ne hv, he v hv]
  cases h : τ u
  · exact Or.inl (hu.trans (by rw [h]))
  · exact Or.inr (hu.trans (by rw [h]))

lemma full_fiber_two (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (σ : State G) (u : V) :
    (∑ ζ ∈ Finset.univ.filter (fun ζ : V → Bool => ∀ v, v ≠ u → ζ v = σ.val v),
      MarkovMixing.hardcoreDist G lam ζ) =
      MarkovMixing.hardcoreDist G lam (Function.update σ.val u false) +
      MarkovMixing.hardcoreDist G lam (Function.update σ.val u true) := by
  classical
  have he : Finset.univ.filter (fun ζ : V → Bool => ∀ v, v ≠ u → ζ v = σ.val v) =
      {Function.update σ.val u false, Function.update σ.val u true} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact exterior_two σ.val τ u
    · rintro (rfl | rfl) v hv <;> exact Function.update_of_ne hv _ _
  have hne : Function.update σ.val u false ≠ Function.update σ.val u true := by
    intro h
    have := congrFun h u
    simp at this
  rw [he, Finset.sum_pair hne]

lemma raw_true_iff (G : SimpleGraph V) [DecidableRel G.Adj] (σ : State G) (u : V) :
    MarkovMixing.IsHardcore G (Function.update σ.val u true) ↔
      ∀ v ∈ G.neighborFinset u, σ.val v = false := by
  constructor
  · intro h v hv
    have huv : G.Adj u v := by simpa using hv
    have hne : v ≠ u := G.ne_of_adj huv.symm
    have hh := h u v huv
    simp only [Function.update_self, Function.update_of_ne hne] at hh
    cases he : σ.val v <;> simp_all
  · exact update_true_hardcore G σ.property u

lemma raw_true_law (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (σ : State G) (u : V) :
    MarkovMixing.hardcoreDist G lam (Function.update σ.val u true) =
      if ∀ v ∈ G.neighborFinset u, σ.val v = false then
        lam * MarkovMixing.hardcoreDist G lam (Function.update σ.val u false) else 0 := by
  classical
  have h0 := update_false_hardcore G σ.property u
  by_cases h : ∀ v ∈ G.neighborFinset u, σ.val v = false
  · rw [if_pos h]
    have h1 := (raw_true_iff G σ u).mpr h
    simp only [MarkovMixing.hardcoreDist, MarkovMixing.hardcoreWeight, if_pos h0, if_pos h1]
    change lam ^ size (Function.update σ.val u true) / _ = lam * (lam ^ size (Function.update σ.val u false) / _)
    rw [size_update_true, pow_succ]
    ring
  · rw [if_neg h]
    have h1 : ¬ MarkovMixing.IsHardcore G (Function.update σ.val u true) :=
      mt (raw_true_iff G σ u).mp h
    simp [MarkovMixing.hardcoreDist, MarkovMixing.hardcoreWeight, h1]

lemma single_site_formula (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (σ τ : State G) (u : V) :
    P G lam u σ τ =
      (if τ.val = updateSpin G σ.val u true then p lam else 0) +
      (if τ.val = updateSpin G σ.val u false then 1-p lam else 0) := by
  classical
  have h0 := update_false_hardcore G σ.property u
  have hpos : 0 < MarkovMixing.hardcoreDist G lam (Function.update σ.val u false) :=
    hcLaw_pos G hlam ⟨_,h0⟩
  have hne : Function.update σ.val u false ≠ Function.update σ.val u true := by
    intro he
    have := congrFun he u
    simp at this
  have h0ext : ∀ v, v ≠ u → Function.update σ.val u false v = σ.val v := by
    intro v hv; exact Function.update_of_ne hv _ _
  have h1ext : ∀ v, v ≠ u → Function.update σ.val u true v = σ.val v := by
    intro v hv; exact Function.update_of_ne hv _ _
  unfold P heatBath
  simp only [Finset.mem_singleton]
  rw [full_fiber_sum, full_fiber_two, raw_true_law]
  simp only [updateSpin, HardCoreBochner.hcLaw]
  by_cases hu : ∀ v ∈ G.neighborFinset u, σ.val v = false
  · simp only [if_pos hu]
    by_cases he0 : τ.val = Function.update σ.val u false
    · have he1 : τ.val ≠ Function.update σ.val u true := he0 ▸ hne
      simp only [he0, if_pos h0ext, if_neg hne, ite_true, p, zero_add]
      field_simp [hpos.ne', show (1+lam) ≠ 0 by positivity]
      <;> ring
    · by_cases he1 : τ.val = Function.update σ.val u true
      · simp only [he1, if_pos h1ext, if_neg (Ne.symm hne), ite_true, p, add_zero]
        rw [raw_true_law, if_pos hu]
        field_simp [hpos.ne', show (1+lam) ≠ 0 by positivity]
        <;> ring
      · have he : ¬ ∀ v, v ≠ u → τ.val v = σ.val v :=
          fun h => (exterior_two σ.val τ.val u h).elim he0 he1
        simp only [if_neg he, if_neg he0, if_neg he1, add_zero]
  · simp only [if_neg hu]
    by_cases he0 : τ.val = Function.update σ.val u false
    · simp only [he0, if_pos h0ext, ite_true, add_zero]
      rw [div_self hpos.ne']
      ring
    · have he1 : τ.val ≠ Function.update σ.val u true := by
        intro he
        have h := (raw_true_iff G σ u).mp (he ▸ τ.property)
        exact hu h
      have he : ¬ ∀ v, v ≠ u → τ.val v = σ.val v :=
        fun h => (exterior_two σ.val τ.val u h).elim he0 he1
      simp only [if_neg he, if_neg he0, add_zero]

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {Ω : Type} [Fintype Ω]

lemma tv_nonneg (ν μ : Ω → ℝ) : 0 ≤ tv ν μ := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)

lemma tv_symm (ν μ : Ω → ℝ) : tv ν μ = tv μ ν := by
  unfold tv
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact abs_sub_comm _ _

lemma tv_triangle (ν μ ρ : Ω → ℝ) : tv ν ρ ≤ tv ν μ + tv μ ρ := by
  unfold tv
  have h := Finset.sum_le_sum (s := Finset.univ) (fun (x : Ω) _ => abs_sub_le (ν x) (μ x) (ρ x))
  rw [Finset.sum_add_distrib] at h
  linarith

lemma tv_contraction (ν μ : Ω → ℝ) {K : Matrix Ω Ω ℝ}
    (hK : MarkovMixing.IsStochastic K) : tv (push ν K) (push μ K) ≤ tv ν μ := by
  unfold tv
  suffices (∑ y, |push ν K y - push μ K y|) ≤ ∑ x, |ν x - μ x| by linarith
  calc
    _ ≤ ∑ y, ∑ x, |ν x - μ x| * K x y := by
      apply Finset.sum_le_sum
      intro y _
      change |(∑ x, ν x * K x y) - ∑ x, μ x * K x y| ≤ _
      rw [← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ x, |ν x * K x y - μ x * K x y| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro x _
          rw [← sub_mul, abs_mul, abs_of_nonneg (hK.1 x y)]
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hK.2, mul_one]

lemma expectation_tv {ν μ : Ω → ℝ} (hν : MarkovMixing.IsDist ν)
    (hμ : MarkovMixing.IsDist μ) (f : Ω → ℝ) {L : ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ L) :
    |expectation ν f - expectation μ f| ≤ L * tv ν μ := by
  have heq : expectation ν f - expectation μ f = ∑ x, (ν x - μ x) * (f x - L/2) := by
    unfold expectation
    simp_rw [sub_mul, mul_sub]
    simp_rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hν.2, hμ.2]
    ring
  rw [heq]
  calc
    _ ≤ ∑ x, |(ν x - μ x) * (f x - L/2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |ν x - μ x| * (L/2) := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply abs_le.mpr
      constructor <;> linarith [(hf x).1, (hf x).2]
    _ = _ := by rw [← Finset.sum_mul]; unfold tv; ring

lemma push_push (ν : Ω → ℝ) (K L : Matrix Ω Ω ℝ) : push (push ν K) L = push ν (K*L) := by
  exact Matrix.vecMul_vecMul ν K L

lemma word_append {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) (w w' : List V) :
    word G lam (w ++ w') = word G lam w * word G lam w' := by
  simp [word]

lemma word_stochastic {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ} (hlam : 0 < lam) (w : List V) :
    MarkovMixing.IsStochastic (word G lam w) := by
  classical
  induction w with
  | nil =>
    constructor
    · intro σ τ
      simp only [word, List.map_nil, List.prod_nil, Matrix.one_apply]
      split_ifs <;> norm_num
    · intro σ
      simp [word, Matrix.one_apply]
  | cons u w ih =>
    have hP := heatBath_stochastic G hlam {u}
    change MarkovMixing.IsStochastic (P G lam u * word G lam w)
    constructor
    · intro σ τ
      exact Finset.sum_nonneg fun ζ _ => mul_nonneg (hP.1 σ ζ) (ih.1 ζ τ)
    · intro σ
      change (∑ τ, ∑ ζ, P G lam u σ ζ * word G lam w ζ τ) = 1
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, ih.2, mul_one]
      exact hP.2 σ

lemma tv_word_bound {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ} (hlam : 0 < lam)
    (ν : State G → ℝ) (w : List V) :
    tv ν (push ν (word G lam w)) ≤ (w.map (fun u => tv ν (push ν (P G lam u)))).sum := by
  classical
  induction w with
  | nil => simp [word, push, tv, Matrix.vecMul_one]
  | cons u w ih =>
    change tv ν (push ν (P G lam u * word G lam w)) ≤ _
    rw [← push_push]
    calc
      _ ≤ tv ν (push ν (word G lam w)) +
          tv (push ν (word G lam w)) (push (push ν (P G lam u)) (word G lam w)) := tv_triangle _ _ _
      _ ≤ (w.map (fun u => tv ν (push ν (P G lam u)))).sum + tv ν (push ν (P G lam u)) :=
        add_le_add ih (tv_contraction _ _ (word_stochastic G hlam w))
      _ = _ := by simp; ring

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma size_sum (σ : V → Bool) : (size σ : ℝ) = ∑ v, if σ v = true then 1 else 0 := by
  rw [← Finset.sum_filter]
  simp [size]

lemma nbrSize_sum (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (σ : V → Bool) :
    (nbrSize G u σ : ℝ) = ∑ v, if G.Adj u v then (if σ v = true then 1 else 0) else 0 := by
  classical
  conv_rhs => rw [← Finset.sum_filter]
  have he : Finset.univ.filter (G.Adj u) = G.neighborFinset u := by ext v; simp
  rw [he, ← Finset.sum_filter]
  simp [nbrSize]

lemma nbrSize_zero (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (σ : V → Bool) :
    nbrSize G u σ = 0 ↔ ∀ v ∈ G.neighborFinset u, σ v = false := by
  simp only [nbrSize, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h v hv
    cases hs : σ v <;> simp_all
  · intro h v hv
    simp [h v hv]

lemma degree_sum_bound (G : SimpleGraph V) [DecidableRel G.Adj] {Δ : ℕ}
    (hΔ : DegreeBound G Δ) (σ : V → Bool) :
    (∑ u, (nbrSize G u σ : ℝ)) ≤ Δ * size σ := by
  classical
  simp_rw [nbrSize_sum]
  rw [Finset.sum_comm, size_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : σ v = true
  · simp only [hv, ite_true, mul_one]
    have heq : (∑ u : V, if G.Adj u v then (1 : ℝ) else 0) = G.degree v := by
      simp_rw [G.adj_comm (v := v)]
      rw [← Finset.sum_filter]
      simp [← SimpleGraph.mem_neighborFinset]
    rw [heq]
    exact_mod_cast hΔ v
  · simp [hv]

lemma site_occupancy (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (σ : State G) (u : V) :
    (∑ τ : State G, P G lam u σ τ * (if τ.val u = true then (1 : ℝ) else 0)) =
      p lam * (if nbrSize G u σ.val = 0 then 1 else 0) := by
  classical
  let s0 : State G := ⟨updateSpin G σ.val u false, spin_hardcore G σ u false⟩
  let s1 : State G := ⟨updateSpin G σ.val u true, spin_hardcore G σ u true⟩
  have he0 (τ : State G) : (τ.val = updateSpin G σ.val u false) ↔ τ = s0 := by
    constructor
    · intro ht; apply Subtype.ext; exact ht
    · exact congrArg Subtype.val
  have he1 (τ : State G) : (τ.val = updateSpin G σ.val u true) ↔ τ = s1 := by
    constructor
    · intro ht; apply Subtype.ext; exact ht
    · exact congrArg Subtype.val
  simp_rw [single_site_formula G hlam, he0, he1, add_mul, ite_mul, zero_mul]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [s0, s1, updateSpin, Function.update_self]
  by_cases h : ∀ v ∈ G.neighborFinset u, σ.val v = false
  · simp only [if_pos h, (nbrSize_zero G u σ.val).mpr h, ite_true, Bool.false_eq_true, ite_false, mul_one, mul_zero, add_zero]
  · have hz : nbrSize G u σ.val ≠ 0 := mt (nbrSize_zero G u σ.val).mp h
    simp only [if_neg h, if_neg hz, Bool.false_eq_true, ite_false, mul_zero, add_zero]

lemma expected_site_occupancy (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) (u : V) :
    expectation (push ν (P G lam u)) (fun σ => if σ.val u = true then 1 else 0) =
      p lam * expectation ν (fun σ => if nbrSize G u σ.val = 0 then 1 else 0) := by
  unfold expectation
  change (∑ τ, (∑ σ, ν σ * P G lam u σ τ) * _) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, site_occupancy G hlam]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The two feasible outputs of a heat-bath proposal. -/
def spinState (G : SimpleGraph V) [DecidableRel G.Adj] (σ : State G) (u : V) (coin : Bool) : State G :=
  ⟨updateSpin G σ.val u coin, spin_hardcore G σ u coin⟩

lemma single_site_average (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (σ : State G) (u : V) (f : State G → ℝ) :
    (∑ τ : State G, P G lam u σ τ * f τ) =
      p lam * f (spinState G σ u true) + (1-p lam) * f (spinState G σ u false) := by
  classical
  have he (coin : Bool) (τ : State G) : (τ.val = updateSpin G σ.val u coin) ↔ τ = spinState G σ u coin := by
    constructor
    · intro ht; apply Subtype.ext; exact ht
    · exact congrArg Subtype.val
  simp_rw [single_site_formula G hlam, he, add_mul, ite_mul, zero_mul]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma expectation_push {Ω : Type} [Fintype Ω] (ν : Ω → ℝ) (K : Matrix Ω Ω ℝ) (f : Ω → ℝ) :
    expectation (push ν K) f = ∑ σ, ν σ * ∑ τ, K σ τ * f τ := by
  unfold expectation
  change (∑ τ, (∑ σ, ν σ * K σ τ) * f τ) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum]

lemma p_pos {lam : ℝ} (hlam : 0 < lam) : 0 < p lam := by
  exact div_pos hlam (by positivity)

lemma one_sub_p_pos {lam : ℝ} (hlam : 0 < lam) : 0 < 1-p lam := by
  unfold p
  have h : 0 < 1+lam := by positivity
  apply sub_pos.mpr
  exact (div_lt_one h).mpr (by linarith)

/-- Indicator that every vertex in A is unoccupied. -/
def emptyOn (G : SimpleGraph V) (A : Finset V) (σ : State G) : ℝ :=
  if ∀ v ∈ A, σ.val v = false then 1 else 0

lemma emptyOn_nonneg (G : SimpleGraph V) (A : Finset V) (σ : State G) : 0 ≤ emptyOn G A σ := by
  unfold emptyOn; split_ifs <;> norm_num

lemma emptyOn_false_update (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : State G) (u : V) (A : Finset V) :
    emptyOn G A (spinState G σ u false) = emptyOn G (A.erase u) σ := by
  have he : (∀ v ∈ A, (spinState G σ u false).val v = false) ↔ ∀ v ∈ A.erase u, σ.val v = false := by
    constructor
    · intro h v hv
      obtain ⟨hvu,hvA⟩ := Finset.mem_erase.mp hv
      simpa [spinState, updateSpin, Function.update_of_ne hvu] using h v hvA
    · intro h v hv
      by_cases hvu : v = u
      · subst v; simp [spinState, updateSpin]
      · simpa [spinState, updateSpin, Function.update_of_ne hvu] using h v (Finset.mem_erase.mpr ⟨hvu,hv⟩)
  simp only [emptyOn, he]

lemma emptyOn_outside_update (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : State G) (u : V) (A : Finset V) (hu : u ∉ A) (coin : Bool) :
    emptyOn G A (spinState G σ u coin) = emptyOn G A σ := by
  have he : (∀ v ∈ A, (spinState G σ u coin).val v = false) ↔ ∀ v ∈ A, σ.val v = false := by
    have hvu (v : V) (hv : v ∈ A) : v ≠ u := by intro h; exact hu (h ▸ hv)
    simp only [spinState, updateSpin]
    constructor <;> intro h v hv <;> simpa [Function.update_of_ne (hvu v hv)] using h v hv
  simp only [emptyOn, he]

lemma emptyOn_step_lower (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) (hν : MarkovMixing.IsDist ν) (u : V) (A : Finset V) :
    (1-p lam) * expectation ν (emptyOn G (A.erase u)) ≤
      expectation (push ν (P G lam u)) (emptyOn G A) := by
  rw [expectation_push]
  simp_rw [single_site_average G hlam, emptyOn_false_update]
  unfold expectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro σ _
  have hh : 0 ≤ p lam * emptyOn G A (spinState G σ u true) :=
    mul_nonneg (p_pos hlam).le (emptyOn_nonneg G A _)
  nlinarith [hν.1 σ]

lemma emptyOn_step_outside (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) (u : V) (A : Finset V) (hu : u ∉ A) :
    expectation (push ν (P G lam u)) (emptyOn G A) = expectation ν (emptyOn G A) := by
  rw [expectation_push]
  simp_rw [single_site_average G hlam, emptyOn_outside_update G _ u A hu]
  apply Finset.sum_congr rfl
  intro σ _
  ring

lemma emptyOn_word_lower (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) (hν : MarkovMixing.IsDist ν)
    (w : List V) (A : Finset V) (hcover : A ⊆ w.toFinset) :
    (1-p lam)^A.card ≤ expectation (push ν (word G lam w)) (emptyOn G A) := by
  classical
  induction w using List.reverseRecOn generalizing A with
  | nil =>
    have hA : A = ∅ := by simpa using hcover
    subst A
    simp [word, push, emptyOn, expectation, hν.2]
  | append_singleton w u ih =>
    rw [word_append]
    simp only [word, List.map_singleton, List.prod_singleton]
    rw [← push_push]
    by_cases hu : u ∈ A
    · have hc : A.erase u ⊆ w.toFinset := by
        intro v hv
        have hvA := (Finset.mem_erase.mp hv).2
        have hmem := hcover hvA
        simpa [List.toFinset_append, Finset.mem_union, List.toFinset_cons, List.toFinset_nil,
          Finset.mem_singleton, (Finset.mem_erase.mp hv).1] using hmem
      have hh := mul_le_mul_of_nonneg_left (ih (A.erase u) hc) (one_sub_p_pos hlam).le
      have hcA : A.card = (A.erase u).card+1 := by simpa using (Finset.card_erase_add_one hu).symm
      rw [hcA, pow_succ]
      refine le_trans ?_ (emptyOn_step_lower G hlam _ (push_dist hν (word_stochastic G hlam w)) u A)
      simpa [mul_comm] using hh
    · have hc : A ⊆ w.toFinset := by
        intro v hv
        have hmem := hcover hv
        have hvu : v ≠ u := by intro h; exact hu (h ▸ hv)
        simpa [List.toFinset_append, Finset.mem_union, List.toFinset_cons, List.toFinset_nil,
          Finset.mem_singleton, hvu] using hmem
      rw [emptyOn_step_outside G hlam _ u A hu]
      exact ih A hc

lemma point_dist {Ω : Type} [Fintype Ω] [DecidableEq Ω] (x : Ω) : MarkovMixing.IsDist (point x) := by
  constructor
  · intro y; unfold point; split_ifs <;> norm_num
  · simp [point]

lemma site_step_outside (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) {u v : V} (hvu : v ≠ u) :
    expectation (push ν (P G lam u)) (fun σ => if σ.val v = true then (1 : ℝ) else 0) =
      expectation ν (fun σ => if σ.val v = true then 1 else 0) := by
  rw [expectation_push]
  simp_rw [single_site_average G hlam]
  simp only [spinState, updateSpin, Function.update_of_ne hvu]
  apply Finset.sum_congr rfl
  intro σ _
  ring

lemma site_word_outside (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) (w : List V) {v : V} (hv : v ∉ w) :
    expectation (push ν (word G lam w)) (fun σ => if σ.val v = true then (1 : ℝ) else 0) =
      expectation ν (fun σ => if σ.val v = true then 1 else 0) := by
  induction w generalizing ν with
  | nil => simp [word, push]
  | cons u w ih =>
    have hparts : v ≠ u ∧ v ∉ w := by simpa using hv
    have hvu := hparts.1
    have hvw := hparts.2
    change expectation (push ν (P G lam u * word G lam w)) _ = _
    rw [← push_push, ih _ hvw, site_step_outside G hlam _ hvu]

lemma q_power (lam : ℝ) (hlam : 0 < lam) (k : ℕ) :
    (1-p lam)^k = (1+lam)^(-(k:ℝ)) := by
  have hq : 1-p lam = 1/(1+lam) := by unfold p; field_simp <;> ring
  rw [hq, Real.rpow_neg (by positivity), Real.rpow_natCast, one_div_pow]
  simp only [one_div]

lemma second_sweep_marginal (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) (hν : MarkovMixing.IsDist ν)
    (w₁ w₂ : List V) (h₁ : IsSweep Finset.univ w₁) (h₂ : IsSweep Finset.univ w₂) (v : V) :
    p lam * (1+lam)^(-(G.degree v:ℝ)) ≤
      expectation (push ν (word G lam (w₁++w₂))) (fun σ => if σ.val v = true then 1 else 0) := by
  classical
  have hmem : v ∈ w₂ := by
    rw [← List.mem_toFinset, h₂.2]
    exact Finset.mem_univ _
  obtain ⟨pre,post,hw⟩ := List.mem_iff_append.mp hmem
  have hpost : v ∉ post := by
    have hh := h₂.1
    rw [hw] at hh
    exact (List.nodup_cons.mp (List.nodup_append.mp hh).2.1).1
  have he : w₁++w₂ = ((w₁++pre)++[v])++post := by rw [hw]; simp [List.append_assoc]
  rw [he, word_append, ← push_push, site_word_outside G hlam _ post hpost,
    word_append, ← push_push]
  simp only [word, List.map_singleton, List.prod_singleton]
  rw [expected_site_occupancy G hlam]
  have hcover : G.neighborFinset v ⊆ (w₁++pre).toFinset := by
    intro u hu
    simp [List.toFinset_append, h₁.2]
  have hh := emptyOn_word_lower G hlam ν hν (w₁++pre) (G.neighborFinset v) hcover
  have hevent : emptyOn G (G.neighborFinset v) =
      (fun σ : State G => if nbrSize G v σ.val = 0 then (1:ℝ) else 0) := by
    ext σ
    simp only [emptyOn, nbrSize_zero]
  rw [hevent, q_power lam hlam] at hh
  exact mul_le_mul_of_nonneg_left hh (p_pos hlam).le

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section

 def tapeSplit (n : ℕ) : (Fin (n+1) → Bool) ≃ Bool × (Fin n → Bool) where
  toFun f := (f 0,fun i => f i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv f := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv x := by rcases x with ⟨b,f⟩; simp

def tapeSum {S R : Type} [AddCommMonoid R] (step : S → Bool → S) (s : S) (f : S → R) (j : ℕ) : R :=
  ∑ tape : Fin j → Bool,f ((List.ofFn tape).foldl step s)

lemma tapeSum_succ {S R : Type} [AddCommMonoid R] (step : S → Bool → S) (s : S) (f : S → R) (j : ℕ) :
    tapeSum step s f (j+1) = tapeSum step (step s true) f j+tapeSum step (step s false) f j := by
  unfold tapeSum
  rw [Fintype.sum_equiv (tapeSplit j) _ (fun x => f ((List.ofFn x.2).foldl step (step s x.1)))
    (by intro tape; rw [List.ofFn_succ]; rfl)]
  rw [Fintype.sum_prod_type,Fintype.sum_bool]

lemma tapeSum_zero {S R : Type} [AddCommMonoid R] (step : S → Bool → S) (s : S) (f : S → R) :
    tapeSum step s f 0 = f s := by simp [tapeSum]

def tapeMean {S : Type} (step : S → Bool → S) (s : S) (f : S → ℝ) (j : ℕ) : ℝ :=
  (1/2:ℝ)^j*tapeSum step s f j

lemma tapeMean_zero {S : Type} (step : S → Bool → S) (s : S) (f : S → ℝ) :
    tapeMean step s f 0 = f s := by simp [tapeMean,tapeSum_zero]

lemma tapeMean_succ {S : Type} (step : S → Bool → S) (s : S) (f : S → ℝ) (j : ℕ) :
    tapeMean step s f (j+1) = (tapeMean step (step s true) f j+tapeMean step (step s false) f j)/2 := by
  simp only [tapeMean,tapeSum_succ,pow_succ]
  ring

lemma tapeMean_const {S : Type} (step : S → Bool → S) (s : S) (a : ℝ) (j : ℕ) :
    tapeMean step s (fun _ => a) j = a := by
  induction j generalizing s with
  | zero => exact tapeMean_zero _ _ _
  | succ j ih => rw [tapeMean_succ,ih,ih]; ring

lemma tapeMean_nonneg {S : Type} (step : S → Bool → S) (s : S) {f : S → ℝ}
    (hf : ∀ s, 0 ≤ f s) (j : ℕ) : 0 ≤ tapeMean step s f j := by
  unfold tapeMean tapeSum
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun t _ => hf _))

lemma tapeMean_add {S : Type} (step : S → Bool → S) (s : S) (f g : S → ℝ) (j : ℕ) :
    tapeMean step s (fun s => f s+g s) j = tapeMean step s f j+tapeMean step s g j := by
  simp only [tapeMean,tapeSum,Finset.sum_add_distrib,mul_add]

lemma tapeMean_mono {S : Type} (step : S → Bool → S) (s : S) {f g : S → ℝ}
    (h : ∀ s, f s ≤ g s) (j : ℕ) : tapeMean step s f j ≤ tapeMean step s g j := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun t _ => h _)

lemma tapeMean_harmonic {S : Type} (step : S → Bool → S) (f : S → ℝ)
    (h : ∀ s, (f (step s true)+f (step s false))/2 = f s) (s : S) (j : ℕ) :
    tapeMean step s f j = f s := by
  induction j generalizing s with
  | zero => exact tapeMean_zero _ _ _
  | succ j ih => rw [tapeMean_succ,ih,ih,h]

lemma tapeMean_future {S : Type} (step : S → Bool → S) (s : S) (f : S → ℝ) (j : ℕ) :
    tapeMean step s (fun s => (f (step s true)+f (step s false))/2) j = tapeMean step s f (j+1) := by
  induction j generalizing s with
  | zero => rw [tapeMean_zero,tapeMean_succ,tapeMean_zero,tapeMean_zero]
  | succ j ih => rw [tapeMean_succ,tapeMean_succ,ih,ih]

lemma tape_cost_partial_bound {S : Type} (step : S → Bool → S) (cost V : S → ℝ)
    (hV : ∀ s, 0 ≤ V s) (hstep : ∀ s, cost s+(V (step s true)+V (step s false))/2 ≤ V s)
    (s : S) (N : ℕ) : (∑ j ∈ Finset.range N,tapeMean step s cost j)+tapeMean step s V N ≤ V s := by
  have hj (j : ℕ) : tapeMean step s cost j+tapeMean step s V (j+1) ≤ tapeMean step s V j := by
    have hh := tapeMean_mono step s hstep j
    rw [tapeMean_add,tapeMean_future] at hh
    exact hh
  induction N with
  | zero => simp only [Finset.sum_range_zero,zero_add,tapeMean_zero,le_refl]
  | succ N ih => rw [Finset.sum_range_succ]; linarith [hj N]

lemma tape_cost_summable {S : Type} (step : S → Bool → S) (cost V : S → ℝ)
    (hc : ∀ s, 0 ≤ cost s) (hV : ∀ s, 0 ≤ V s)
    (hstep : ∀ s, cost s+(V (step s true)+V (step s false))/2 ≤ V s) (s : S) :
    Summable (fun j => tapeMean step s cost j) ∧ (∑' j,tapeMean step s cost j) ≤ V s := by
  have hb (N : ℕ) : (∑ j ∈ Finset.range N,tapeMean step s cost j) ≤ V s := by
    have hh := tape_cost_partial_bound step cost V hV hstep s N
    have hn := tapeMean_nonneg step s hV N
    linarith
  have hs := summable_of_sum_range_le (fun j => tapeMean_nonneg step s hc j) hb
  exact ⟨hs,hs.tsum_le_of_sum_range_le hb⟩

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section

lemma tapeMean_sub {S : Type} (step : S → Bool → S) (s : S) (f g : S → ℝ) (j : ℕ) :
    tapeMean step s (fun s => f s-g s) j = tapeMean step s f j-tapeMean step s g j := by
  simp only [tapeMean,tapeSum,Finset.sum_sub_distrib,mul_sub]

lemma tapeMean_abs_bound {S : Type} (step : S → Bool → S) (s : S) (f g : S → ℝ)
    (h : ∀ s, |f s| ≤ g s) (j : ℕ) : |tapeMean step s f j| ≤ tapeMean step s g j := by
  unfold tapeMean tapeSum
  rw [abs_mul,abs_of_nonneg (by positivity : (0:ℝ) ≤ (1/2:ℝ)^j)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun tape _ => h _))

def haltRate {S : Type} (step : S → Bool → S) (live : S → Bool) (f : S → ℝ) (s : S) : ℝ :=
  if live s then (f (step s true)+f (step s false))/2 else 0

lemma haltRate_increment {S : Type} (step : S → Bool → S) (live : S → Bool) (f : S → ℝ)
    (hf0 : ∀ s, live s = true → f s = 0)
    (hfend : ∀ s, live s = false → ∀ b, f (step s b) = f s) (s : S) :
    haltRate step live f s = (f (step s true)+f (step s false))/2-f s := by
  cases hs : live s
  · simp [haltRate,hs,hfend s hs]
  · simp [haltRate,hs,hf0 s hs]

lemma haltRate_partial {S : Type} (step : S → Bool → S) (live : S → Bool) (f : S → ℝ)
    (hf0 : ∀ s, live s = true → f s = 0)
    (hfend : ∀ s, live s = false → ∀ b, f (step s b) = f s) (s : S) (N : ℕ) :
    (∑ j ∈ Finset.range N,tapeMean step s (haltRate step live f) j) = tapeMean step s f N-f s := by
  have he : haltRate step live f = fun s => (f (step s true)+f (step s false))/2-f s :=
    funext (haltRate_increment step live f hf0 hfend)
  rw [he]
  simp_rw [tapeMean_sub,tapeMean_future]
  induction N with
  | zero => simp [tapeMean_zero]
  | succ N ih => rw [Finset.sum_range_succ,ih]; ring

lemma haltRate_summable {S : Type} (step : S → Bool → S) (live : S → Bool) (f : S → ℝ)
    (hf : ∀ s, 0 ≤ f s ∧ f s ≤ 1) (hf0 : ∀ s, live s = true → f s = 0)
    (hfend : ∀ s, live s = false → ∀ b, f (step s b) = f s) (s : S) :
    Summable (fun j => tapeMean step s (haltRate step live f) j) := by
  have hrate : ∀ s, 0 ≤ haltRate step live f s := by
    intro s
    unfold haltRate
    split_ifs
    · exact div_nonneg (add_nonneg (hf _).1 (hf _).1) (by norm_num)
    · rfl
  apply summable_of_sum_range_le (fun j => tapeMean_nonneg step s hrate j) (c := 1)
  intro N
  rw [haltRate_partial step live f hf0 hfend]
  have hm := tapeMean_mono step s (fun s => (hf s).2) N
  rw [tapeMean_const] at hm
  linarith [(hf s).1]

lemma harmonic_halt_law {S : Type} (step : S → Bool → S) (live : S → Bool) (f H : S → ℝ)
    (hf : ∀ s, 0 ≤ f s ∧ f s ≤ 1) (hH : ∀ s, 0 ≤ H s ∧ H s ≤ 1)
    (hf0 : ∀ s, live s = true → f s = 0)
    (hfend : ∀ s, live s = false → ∀ b, f (step s b) = f s)
    (hHend : ∀ s, live s = false → H s = f s)
    (hHarm : ∀ s, (H (step s true)+H (step s false))/2 = H s)
    (s : S) (hs : live s = true)
    (htail : Filter.Tendsto (fun j => tapeMean step s (fun s => if live s then (1:ℝ) else 0) j)
      Filter.atTop (nhds 0)) :
    (∑' j,tapeMean step s (haltRate step live f) j) = H s := by
  have hbound (x : S) : |f x-H x| ≤ if live x then (1:ℝ) else 0 := by
    cases hx : live x
    · simp [hx,hHend x hx]
    · change |f x-H x| ≤ 1
      exact abs_le.mpr ⟨by linarith [(hf x).1,(hH x).2],by linarith [(hf x).2,(hH x).1]⟩
  have hlim0 : Filter.Tendsto (fun j => tapeMean step s f j-H s) Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm (fun j => ?_) htail
    have hh := tapeMean_abs_bound step s (fun x => f x-H x) _ hbound j
    rw [tapeMean_sub,tapeMean_harmonic step H hHarm] at hh
    simpa only [Real.norm_eq_abs] using hh
  have hlim : Filter.Tendsto (fun j => tapeMean step s f j) Filter.atTop (nhds (H s)) := by
    have hh := hlim0.add_const (H s)
    simpa only [sub_add_cancel,zero_add] using hh
  have hpartial := (haltRate_summable step live f hf hf0 hfend s).hasSum.tendsto_sum_nat
  have heq (N : ℕ) : (∑ j ∈ Finset.range N,tapeMean step s (haltRate step live f) j) = tapeMean step s f N := by
    rw [haltRate_partial step live f hf0 hfend,hf0 s hs,sub_zero]
  simp_rw [heq] at hpartial
  exact tendsto_nhds_unique hpartial hlim

lemma survival_tendsto_of_potential {S : Type} (step : S → Bool → S) (live : S → Bool)
    (cost V : S → ℝ) (hc : ∀ s, 0 ≤ cost s) (hV : ∀ s, 0 ≤ V s)
    (hstep : ∀ s, cost s+(V (step s true)+V (step s false))/2 ≤ V s)
    (hcost : ∀ s, (if live s then (1:ℝ) else 0) ≤ cost s) (s : S) :
    Filter.Tendsto (fun j => tapeMean step s (fun s => if live s then (1:ℝ) else 0) j)
      Filter.atTop (nhds 0) := by
  have hnonneg : ∀ x : S, (0:ℝ) ≤ if live x then 1 else 0 := by intro x; split_ifs <;> norm_num
  have hs := tape_cost_summable step cost V hc hV hstep s
  have hb (N : ℕ) : (∑ j ∈ Finset.range N,tapeMean step s (fun s => if live s then (1:ℝ) else 0) j) ≤ V s := by
    have hh := tape_cost_partial_bound step cost V hV hstep s N
    have hn := tapeMean_nonneg step s hV N
    have hle := Finset.sum_le_sum (s := Finset.range N) (fun j _ => tapeMean_mono step s hcost j)
    linarith
  exact (summable_of_sum_range_le (fun j => tapeMean_nonneg step s hnonneg j) hb).tendsto_atTop_zero

 def tapeSnoc (n : ℕ) : (Fin (n+1) → Bool) ≃ (Fin n → Bool) × Bool where
  toFun f := (Fin.init f,f (Fin.last n))
  invFun x := Fin.snoc x.1 x.2
  left_inv f := Fin.snoc_init_self f
  right_inv x := by rcases x with ⟨f,b⟩; simp

def firstMass {S : Type} (step : S → Bool → S) (live : S → Bool) (f : S → ℝ) (s : S) (j : ℕ) : ℝ :=
  ∑ tape : Fin (j+1) → Bool,
    if live (((List.ofFn tape).take j).foldl step s) then
      f ((List.ofFn tape).foldl step s)*(1/2:ℝ)^(j+1) else 0

lemma firstMass_eq_rate {S : Type} (step : S → Bool → S) (live : S → Bool) (f : S → ℝ) (s : S) (j : ℕ) :
    firstMass step live f s j = tapeMean step s (haltRate step live f) j := by
  unfold firstMass tapeMean tapeSum haltRate
  rw [Fintype.sum_equiv (tapeSnoc j) _ (fun x =>
    if live ((List.ofFn x.1).foldl step s) then
      f (step ((List.ofFn x.1).foldl step s) x.2)*(1/2:ℝ)^(j+1) else 0) ?_]
  · rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_bool]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro tape _
    split_ifs <;> (try rw [pow_succ]) <;> ring
  · intro tape
    rw [List.ofFn_succ_last]
    have htake : ((List.ofFn fun i : Fin j => tape i.castSucc)++[tape (Fin.last j)]).take j =
        List.ofFn (fun i : Fin j => tape i.castSucc) := by
      convert (List.take_left (l₁ := List.ofFn fun i : Fin j => tape i.castSucc) (l₂ := [tape (Fin.last j)])) using 1 <;> simp
    rw [htake,List.foldl_append]
    rfl

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section

def blockMean (w j acc : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ a ∈ Finset.range (2^(w-j)),f (2^(w-j)*acc+a))/(2:ℝ)^(w-j)

lemma blockMean_end (w acc : ℕ) (f : ℕ → ℝ) : blockMean w w acc f = f acc := by
  simp [blockMean]

lemma blockMean_step (w j acc : ℕ) (hj : j < w) (f : ℕ → ℝ) :
    blockMean w j acc f = (blockMean w (j+1) (2*acc) f+blockMean w (j+1) (2*acc+1) f)/2 := by
  let N := 2^(w-(j+1))
  have he : w-j = (w-(j+1))+1 := by omega
  have hpow : 2^(w-j) = N+N := by rw [he,pow_succ]; dsimp [N]; omega
  unfold blockMean
  rw [hpow,Finset.sum_range_add]
  have h₁ : (∑ a ∈ Finset.range N,f ((N+N)*acc+a)) = (∑ a ∈ Finset.range N,f (N*(2*acc)+a)) := by
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    ring
  have h₂ : (∑ a ∈ Finset.range N,f ((N+N)*acc+(N+a))) = (∑ a ∈ Finset.range N,f (N*(2*acc+1)+a)) := by
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    ring
  rw [h₁,h₂]
  rw [he,pow_succ]
  change (_+_)/((2:ℝ)^(w-(j+1))*2) = _
  ring

lemma sum_rejection_dispatch (N m : ℕ) (hm : m ≤ N) (f : ℕ → ℝ) (v : ℝ) :
    (∑ a ∈ Finset.range N,if a < m then f a else v) = (∑ a ∈ Finset.range m,f a)+((N-m:ℕ):ℝ)*v := by
  conv_lhs => rw [show N = m+(N-m) by omega,Finset.sum_range_add]
  have h₁ : (∑ a ∈ Finset.range m,if a < m then f a else v) = ∑ a ∈ Finset.range m,f a := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [if_pos (Finset.mem_range.mp ha)]
  have h₂ : (∑ a ∈ Finset.range (N-m),if m+a < m then f (m+a) else v) = ((N-m:ℕ):ℝ)*v := by
    simp
  rw [h₁,h₂]

 def uniformMean (m : ℕ) (f : ℕ → ℝ) : ℝ := (∑ a ∈ Finset.range m,f a)/m

lemma drawWidth_bounds {m : ℕ} (hm : 1 ≤ m) : m ≤ 2^(drawWidth m) ∧ 2^(drawWidth m) ≤ 2*m := by
  have hupper := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (m-1)
  simp only [drawWidth,bits,Nat.log2_eq_log_two] at *
  constructor
  · omega
  · by_cases h1 : m = 1
    · simp [h1]
    · have hp := Nat.log2_self_le (by omega : m-1 ≠ 0)
      rw [Nat.log2_eq_log_two] at hp
      rw [pow_succ]
      omega

lemma blockMean_dispatch_start {m : ℕ} (hm : 1 ≤ m) (f : ℕ → ℝ) (v : ℝ) :
    blockMean (drawWidth m) 0 0 (fun a => if a < m then f a else v) =
      ((m:ℝ)*uniformMean m f+(2^(drawWidth m)-m)*v)/(2:ℝ)^(drawWidth m) := by
  simp only [blockMean,Nat.sub_zero,Nat.mul_zero,zero_add]
  rw [sum_rejection_dispatch _ _ (drawWidth_bounds hm).1]
  unfold uniformMean
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  rw [mul_div_cancel₀ _ hm0]
  simp only [Nat.cast_sub (drawWidth_bounds hm).1,Nat.cast_pow,Nat.cast_ofNat]

lemma blockMean_rejection_start {m : ℕ} (hm : 1 ≤ m) (f : ℕ → ℝ) :
    blockMean (drawWidth m) 0 0 (fun a => if a < m then f a else uniformMean m f) = uniformMean m f := by
  rw [blockMean_dispatch_start hm]
  field_simp
  <;> ring

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section

lemma blockMean_nonneg (w j acc : ℕ) {f : ℕ → ℝ} (hf : ∀ a, 0 ≤ f a) : 0 ≤ blockMean w j acc f := by
  unfold blockMean
  exact div_nonneg (Finset.sum_nonneg (fun a _ => hf _)) (by positivity)

lemma blockMean_le (w j acc : ℕ) {f : ℕ → ℝ} {K : ℝ} (hf : ∀ a, f a ≤ K) :
    blockMean w j acc f ≤ K := by
  unfold blockMean
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^(w-j))).mpr
  have hh := Finset.sum_le_sum (s := Finset.range (2^(w-j))) (fun a _ => hf (2^(w-j)*acc+a))
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat,mul_comm] using hh

lemma uniformMean_const {m : ℕ} (hm : 1 ≤ m) (a : ℝ) : uniformMean m (fun _ => a) = a := by
  unfold uniformMean
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  field_simp

 def drawCost (m : ℕ) (C : ℝ) : ℝ := C*(drawWidth m+1)*(2:ℝ)^(drawWidth m)/m
 def drawPotential (m : ℕ) (C next : ℝ) (j acc : ℕ) : ℝ :=
  C*((drawWidth m-j+1:ℕ):ℝ)+blockMean (drawWidth m) j acc
    (fun a => if a < m then next else drawCost m C+next)

lemma drawCost_nonneg (m : ℕ) {C : ℝ} (hC : 0 ≤ C) : 0 ≤ drawCost m C := by unfold drawCost; positivity

lemma drawCost_le {m : ℕ} (hm : 1 ≤ m) {C : ℝ} (hC : 0 ≤ C) :
    drawCost m C ≤ 2*C*(drawWidth m+1) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  unfold drawCost
  apply (div_le_iff₀ hm0).mpr
  have hh : (2:ℝ)^(drawWidth m) ≤ 2*m := by exact_mod_cast (drawWidth_bounds hm).2
  have hmul := mul_le_mul_of_nonneg_left hh (show 0 ≤ C*(drawWidth m+1) by positivity)
  nlinarith

lemma drawPotential_start {m : ℕ} (hm : 1 ≤ m) (C next : ℝ) :
    drawPotential m C next 0 0 = drawCost m C+next := by
  unfold drawPotential
  rw [blockMean_dispatch_start hm,uniformMean_const hm]
  simp only [Nat.sub_zero,Nat.cast_add,Nat.cast_one]
  unfold drawCost
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  field_simp
  <;> ring

lemma drawPotential_end (m : ℕ) (C next : ℝ) (acc : ℕ) :
    drawPotential m C next (drawWidth m) acc = C+(if acc < m then next else drawCost m C+next) := by
  simp [drawPotential,blockMean_end]

lemma drawPotential_step (m : ℕ) (C next : ℝ) (j acc : ℕ) (hj : j < drawWidth m) :
    C+(drawPotential m C next (j+1) (2*acc)+drawPotential m C next (j+1) (2*acc+1))/2 = drawPotential m C next j acc := by
  unfold drawPotential
  rw [blockMean_step _ _ _ hj]
  have he : drawWidth m-j+1 = (drawWidth m-(j+1)+1)+1 := by omega
  rw [he]
  push_cast
  ring

lemma drawPotential_nonneg (m : ℕ) {C next : ℝ} (hC : 0 ≤ C) (hn : 0 ≤ next) (j acc : ℕ) :
    0 ≤ drawPotential m C next j acc := by
  unfold drawPotential
  apply add_nonneg (by positivity)
  apply blockMean_nonneg
  intro a
  split_ifs
  · exact hn
  · exact add_nonneg (drawCost_nonneg m hC) hn

lemma drawPotential_le {m : ℕ} (hm : 1 ≤ m) {C next : ℝ} (hC : 0 ≤ C) (hn : 0 ≤ next)
    (j acc : ℕ) : drawPotential m C next j acc ≤ next+3*C*(drawWidth m+1) := by
  have hwidth : drawWidth m-j+1 ≤ drawWidth m+1 := by omega
  have hblock := blockMean_le (drawWidth m) j acc
    (f := fun a => if a < m then next else drawCost m C+next)
    (K := drawCost m C+next) (fun a => by split_ifs <;> linarith [drawCost_nonneg m hC])
  have hh := mul_le_mul_of_nonneg_left (show (((drawWidth m-j+1:ℕ):ℝ)) ≤ drawWidth m+1 by exact_mod_cast hwidth) hC
  have hd := drawCost_le hm hC
  unfold drawPotential
  nlinarith

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma bitSize_eq_size {n : ℕ} (σ : Fin n → Bool) : bitSize σ = size σ := by
  unfold bitSize size
  rw [List.countP_eq_length_filter,← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter σ)]
  congr 1
  ext v
  simp

lemma bitSpin_eq_update {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Fin n → Bool) (u : Fin n) (coin : Bool) : bitSpin G σ u coin = updateSpin G σ u coin := by
  have he : ((List.finRange n).all (fun v => !(decide (G.Adj u v) && σ v)) = true) ↔
      ∀ v ∈ G.neighborFinset u, σ v = false := by
    rw [List.all_eq_true]
    constructor
    · intro h v hv
      have hh := h v (List.mem_finRange v)
      have hv' : G.Adj u v := by simpa using hv
      simpa [hv'] using hh
    · intro h v _
      by_cases hv : G.Adj u v
      · simp [hv,h v (by simpa using hv)]
      · simp [hv]
  unfold bitSpin updateSpin
  by_cases hEvt : ∀ v ∈ G.neighborFinset u, σ v = false
  · rw [if_pos (he.mpr hEvt),if_pos hEvt]
  · rw [if_neg (fun hh => hEvt (he.mp hh)),if_neg hEvt]

lemma bitSpin_hardcore {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Fin n → Bool) (hσ : MarkovMixing.IsHardcore G σ) (u : Fin n) (coin : Bool) :
    MarkovMixing.IsHardcore G (bitSpin G σ u coin) := by
  rw [bitSpin_eq_update]
  exact spin_hardcore G ⟨σ,hσ⟩ u coin

 def drawValid {n : ℕ} (G : SimpleGraph (Fin n)) (initial : Fin n → Bool) (q T R : ℕ) : BitState n → Prop
  | .prepare _ => False
  | .done best => MarkovMixing.IsHardcore G best ∧ size initial ≤ size best
  | .draw q' runs remaining current best proposal site j acc =>
    q'=q ∧ 1 ≤ runs ∧ runs ≤ R ∧ 1 ≤ remaining ∧ remaining ≤ T ∧
    MarkovMixing.IsHardcore G current ∧ MarkovMixing.IsHardcore G best ∧
    size initial ≤ size best ∧ size current ≤ size best ∧ j ≤ drawWidth (if proposal then q+1 else n) ∧ acc < 2^j ∧ (proposal=true → site < n)

lemma drawValid_start {n : ℕ} (G : SimpleGraph (Fin n)) (I : State G) (q T R : ℕ)
    (hT : 1 ≤ T) (hR : 1 ≤ R) :
    drawValid G I.val q T R (.draw q R T I.val I.val false 0 0 0) := by
  exact ⟨rfl,hR,le_rfl,hT,le_rfl,I.property,I.property,le_rfl,le_rfl,Nat.zero_le _,by norm_num,by simp⟩

lemma drawValid_step {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b : ℚ) (I : State G) (m q R : ℕ) {s : BitState n}
    (hR : 1 ≤ R) (hs : drawValid G I.val q (bitHorizon n) R s) (coin : Bool) :
    drawValid G I.val q (bitHorizon n) R (bitStep G Δ t b I.val m s coin) := by
  cases s with
  | prepare h => exact False.elim hs
  | done best => exact hs
  | draw q' runs remaining current best proposal site j acc =>
    rcases hs with ⟨heq,hr1,hrR,ht1,htT,hcur,hbest,hinit,hrecordcur,hj,hacc,hsite⟩
    subst q'
    let target := if proposal then q+1 else n
    by_cases hbits : j < drawWidth target
    · dsimp only [target] at hbits
      simp only [bitStep,if_pos hbits]
      refine ⟨rfl,hr1,hrR,ht1,htT,hcur,hbest,hinit,hrecordcur,by omega,?_,hsite⟩
      rw [pow_succ]
      cases coin <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
    · dsimp only [target] at hbits
      have hjeq : j = drawWidth target := by dsimp only [target]; omega
      by_cases hrej : target ≤ acc
      · dsimp only [target] at hrej
        simp only [bitStep,if_neg hbits,if_pos hrej]
        exact ⟨rfl,hr1,hrR,ht1,htT,hcur,hbest,hinit,hrecordcur,Nat.zero_le _,by norm_num,hsite⟩
      · dsimp only [target] at hrej
        cases hp : proposal with
        | false =>
          simp only [hp,ite_true,ite_false] at hbits hrej hj hsite
          simp only [bitStep,hp,Bool.not_false,ite_false,if_neg hbits,if_neg hrej,ite_true]
          refine ⟨rfl,hr1,hrR,ht1,htT,hcur,hbest,hinit,hrecordcur,Nat.zero_le _,by norm_num,?_⟩
          intro _
          dsimp [target] at hrej
          simpa [hp] using Nat.lt_of_not_ge hrej
        | true =>
          simp only [hp,ite_true,ite_false] at hbits hrej hj hsite
          have hsite' : site < n := hsite True.intro
          let next := bitSpin G current ⟨site,hsite'⟩ (decide (acc=0))
          let record := if bitSize best < bitSize next then next else best
          have hn : MarkovMixing.IsHardcore G next := bitSpin_hardcore G current hcur _ _
          have hbrec : MarkovMixing.IsHardcore G record := by dsimp [record]; split_ifs <;> assumption
          have hbestrec : size best ≤ size record := by
            dsimp only [record]
            split_ifs with hh
            · simpa only [bitSize_eq_size] using hh.le
            · rfl
          have hnextrec : size next ≤ size record := by
            dsimp only [record]
            split_ifs with hh
            · rfl
            · simpa only [bitSize_eq_size] using le_of_not_gt hh
          have hinitrec : size I.val ≤ size record := hinit.trans hbestrec
          by_cases ht : 1 < remaining
          · simp only [bitStep,hp,Bool.not_true,ite_true,if_neg hbits,if_neg hrej,ite_false,dif_pos hsite',if_pos ht]
            exact ⟨rfl,hr1,hrR,by omega,by omega,hn,hbrec,hinitrec,hnextrec,Nat.zero_le _,by norm_num,by simp⟩
          · by_cases hr : 1 < runs
            · simp only [bitStep,hp,Bool.not_true,ite_true,if_neg hbits,if_neg hrej,ite_false,dif_pos hsite',if_neg ht,if_pos hr]
              exact ⟨rfl,by omega,by omega,le_max_left _ _,le_rfl,I.property,hbrec,hinitrec,hinitrec,Nat.zero_le _,by norm_num,by simp⟩
            · simp only [bitStep,hp,Bool.not_true,ite_true,if_neg hbits,if_neg hrej,ite_false,dif_pos hsite',if_neg ht,if_neg hr]
              exact ⟨hbrec,hinitrec⟩

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section

lemma stochastic_mul {Ω : Type} [Fintype Ω] {K L : Matrix Ω Ω ℝ}
    (hK : MarkovMixing.IsStochastic K) (hL : MarkovMixing.IsStochastic L) :
    MarkovMixing.IsStochastic (K*L) := by
  constructor
  · intro x y
    exact Finset.sum_nonneg (fun z _ => mul_nonneg (hK.1 x z) (hL.1 z y))
  · intro x
    change (∑ y, ∑ z, K x z*L z y) = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hL.2, mul_one]
    exact hK.2 x

lemma stochastic_pow {Ω : Type} [Fintype Ω] [DecidableEq Ω] {K : Matrix Ω Ω ℝ}
    (hK : MarkovMixing.IsStochastic K) (T : ℕ) : MarkovMixing.IsStochastic (K^T) := by
  induction T with
  | zero =>
    constructor
    · intro x y
      simp only [pow_zero, Matrix.one_apply]
      split_ifs <;> norm_num
    · intro x; simp [Matrix.one_apply]
  | succ T ih => rw [pow_succ]; exact stochastic_mul ih hK

lemma point_push {Ω : Type} [Fintype Ω] [DecidableEq Ω] (x : Ω) (K : Matrix Ω Ω ℝ) :
    push (point x) K = fun y => K x y := by
  ext y
  simp [push, point, Matrix.vecMul, dotProduct]

variable {V : Type} [Fintype V] [DecidableEq V]

lemma size_larger (G : SimpleGraph V) (I J : State G) :
    size (larger G I J).val = max (size I.val) (size J.val) := by
  unfold larger
  split_ifs with h
  · exact (max_eq_right h.le).symm
  · exact (max_eq_left (le_of_not_gt h)).symm

lemma record_stochastic [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam) : MarkovMixing.IsStochastic (recordKernel G lam) := by
  have hK := scan_stochastic G hlam
  constructor
  · intro x y
    unfold recordKernel
    split_ifs
    · exact hK.1 _ _
    · rfl
  · intro x
    rw [Fintype.sum_prod_type]
    simp only [recordKernel]
    simp_rw [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact hK.2 x.1

lemma runLargest_dist [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam) (I : State G) (T : ℕ) :
    MarkovMixing.IsDist (runLargest G lam I T) := by
  have hK := stochastic_pow (record_stochastic G hlam) T
  constructor
  · intro B
    exact Finset.sum_nonneg (fun J _ => hK.1 (I,I) (J,B))
  · change (∑ B, ∑ J, (recordKernel G lam^T) (I,I) (J,B)) = 1
    rw [Finset.sum_comm, ← Fintype.sum_prod_type]
    exact hK.2 (I,I)

lemma repetition_stochastic [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam) (I : State G) (T : ℕ) :
    MarkovMixing.IsStochastic (repetitionKernel G lam I T) := by
  have hrun := runLargest_dist G hlam I T
  constructor
  · intro B C
    unfold repetitionKernel
    apply Finset.sum_nonneg
    intro A _
    split_ifs
    · exact hrun.1 A
    · rfl
  · intro B
    unfold repetitionKernel
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact hrun.2

lemma amplified_dist [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam) (I : State G) (T R : ℕ) :
    MarkovMixing.IsDist (amplifiedLaw G lam I T R) := by
  exact push_dist (by
    constructor
    · intro J; unfold point; split_ifs <;> norm_num
    · simp [point]) (stochastic_pow (repetition_stochastic G hlam I T) R)

lemma record_row_average (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (x : State G × State G) (f : State G × State G → ℝ) :
    (∑ y, recordKernel G lam x y*f y) = ∑ J, K G lam x.1 J*f (J,larger G x.2 J) := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [recordKernel, ite_mul, zero_mul]
  simp_rw [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma record_first_step (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (ν : State G × State G → ℝ) (f : State G → ℝ) :
    expectation (push ν (recordKernel G lam)) (fun x => f x.1) =
      expectation ν (fun x => ∑ J, K G lam x.1 J*f J) := by
  rw [expectation_push]
  simp_rw [record_row_average]
  rfl

lemma record_first_expectation (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (x : State G × State G) (T : ℕ) (f : State G → ℝ) :
    expectation (push (point x) (recordKernel G lam^T)) (fun y => f y.1) =
      expectation (push (point x.1) (K G lam^T)) f := by
  induction T generalizing f with
  | zero => simp [push, point, expectation]
  | succ T ih =>
    rw [pow_succ, ← push_push, record_first_step]
    rw [ih (fun I => ∑ J, K G lam I J*f J)]
    conv_rhs => rw [pow_succ, ← push_push, expectation_push]
    rfl

lemma record_step_increases [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam) (ν : State G × State G → ℝ) (hν : MarkovMixing.IsDist ν) :
    expectation ν (fun x => (size x.2.val:ℝ)) ≤
      expectation (push ν (recordKernel G lam)) (fun x => (size x.2.val:ℝ)) := by
  have hK := scan_stochastic G hlam
  rw [expectation_push]
  simp_rw [record_row_average]
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (hν.1 x)
  calc
    _ = ∑ J, K G lam x.1 J*(size x.2.val:ℝ) := by rw [← Finset.sum_mul, hK.2, one_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro J _
      apply mul_le_mul_of_nonneg_left _ (hK.1 x.1 J)
      exact_mod_cast (show size x.2.val ≤ size (larger G x.2 J).val by rw [size_larger]; exact le_max_left _ _)

lemma record_step_dominates [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam) (ν : State G × State G → ℝ) (hν : MarkovMixing.IsDist ν) :
    expectation (push ν (recordKernel G lam)) (fun x => (size x.1.val:ℝ)) ≤
      expectation (push ν (recordKernel G lam)) (fun x => (size x.2.val:ℝ)) := by
  have hK := scan_stochastic G hlam
  rw [expectation_push, expectation_push]
  simp_rw [record_row_average]
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (hν.1 x)
  apply Finset.sum_le_sum
  intro J _
  apply mul_le_mul_of_nonneg_left _ (hK.1 x.1 J)
  exact_mod_cast (show size J.val ≤ size (larger G x.2 J).val by rw [size_larger]; exact le_max_right _ _)

lemma runLargest_expectation (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (I : State G) (T : ℕ) :
    expectation (runLargest G lam I T) (fun J => size J.val) =
      expectation (push (point (I,I)) (recordKernel G lam^T)) (fun x => size x.2.val) := by
  rw [point_push]
  unfold expectation runLargest
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Fintype.sum_prod_type]

lemma record_time_domination [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam) (I : State G) (T : ℕ) (hT : 1 ≤ T) :
    timeMean G lam (point I) T ≤ expectation (runLargest G lam I T) (fun J => size J.val) := by
  let μ (j : ℕ) := push (point (I,I)) (recordKernel G lam^j)
  have hμ (j : ℕ) : MarkovMixing.IsDist (μ j) :=
    push_dist (point_dist (I,I)) (stochastic_pow (record_stochastic G hlam) j)
  have hsucc (j : ℕ) : μ (j+1) = push (μ j) (recordKernel G lam) := by
    dsimp [μ]
    rw [pow_succ, push_push]
  have hmono : Monotone (fun j => expectation (μ j) (fun x => (size x.2.val:ℝ))) := by
    apply monotone_nat_of_le_succ
    intro j
    rw [hsucc]
    exact record_step_increases G hlam (μ j) (hμ j)
  have hdom (j : ℕ) : expectation (push (point I) (K G lam^j)) (fun J => size J.val) ≤
      expectation (μ j) (fun x => size x.2.val) := by
    rw [← record_first_expectation G lam (I,I)]
    cases j with
    | zero => simp [μ, push, expectation, point]
    | succ j =>
      change expectation (μ (j+1)) _ ≤ expectation (μ (j+1)) _
      rw [hsucc]
      exact record_step_dominates G hlam _ (hμ j)
  have hrow (j : ℕ) (hj : j ∈ Finset.range T) :
      expectation (push (point I) (K G lam^j)) (fun J => size J.val) ≤
        expectation (runLargest G lam I T) (fun J => size J.val) := by
    rw [runLargest_expectation]
    exact (hdom j).trans (hmono (Finset.mem_range.mp hj).le)
  unfold timeMean
  have hTpos : (0:ℝ) < T := by exact_mod_cast hT
  apply (div_le_iff₀ hTpos).mpr
  have hh := Finset.sum_le_sum (s := Finset.range T) hrow
  simpa [mul_comm] using hh

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

def failure (G : SimpleGraph V) [DecidableRel G.Adj] (ν : State G → ℝ) (a : ℝ) : ℝ :=
  expectation ν (fun I => if (size I.val:ℝ) < a then 1 else 0)

lemma success_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] {ν : State G → ℝ}
    (hν : MarkovMixing.IsDist ν) (a : ℝ) : 0 ≤ success G ν a := by
  unfold success
  apply Finset.sum_nonneg
  intro I _
  split_ifs
  · exact hν.1 I
  · rfl

lemma success_le_one (G : SimpleGraph V) [DecidableRel G.Adj] {ν : State G → ℝ}
    (hν : MarkovMixing.IsDist ν) (a : ℝ) : success G ν a ≤ 1 := by
  calc
    _ ≤ ∑ I, ν I := by
      apply Finset.sum_le_sum
      intro I _
      split_ifs
      · rfl
      · exact hν.1 I
    _ = _ := hν.2

lemma success_add_failure (G : SimpleGraph V) [DecidableRel G.Adj] {ν : State G → ℝ}
    (hν : MarkovMixing.IsDist ν) (a : ℝ) : success G ν a+failure G ν a = 1 := by
  unfold success failure expectation
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ I, ν I := by
      apply Finset.sum_congr rfl
      intro I _
      by_cases h : a ≤ (size I.val:ℝ)
      · simp [h, not_lt.mpr h]
      · simp [h, lt_of_not_ge h]
    _ = _ := hν.2

lemma size_le_card (G : SimpleGraph V) (I : State G) : size I.val ≤ Fintype.card V :=
  Finset.card_filter_le _ _

lemma expectation_size_upper (G : SimpleGraph V) [DecidableRel G.Adj]
    {ν : State G → ℝ} (hν : MarkovMixing.IsDist ν) {a : ℝ} (ha : 0 ≤ a) :
    expectation ν (fun I => size I.val) ≤ a+Fintype.card V*success G ν a := by
  have hh (I : State G) : (size I.val:ℝ) ≤ a+(if a ≤ (size I.val:ℝ) then (Fintype.card V:ℝ) else 0) := by
    split_ifs with h
    · have hsize : (size I.val:ℝ) ≤ Fintype.card V := by exact_mod_cast size_le_card G I
      linarith
    · have hh := lt_of_not_ge h
      linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun I _ => mul_le_mul_of_nonneg_left (hh I) (hν.1 I))
  simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul] at hs
  rw [hν.2, one_mul] at hs
  have he : (∑ I, ν I*(if a ≤ (size I.val:ℝ) then (Fintype.card V:ℝ) else 0)) =
      Fintype.card V*success G ν a := by
    unfold success
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I _
    split_ifs <;> ring
  rw [he] at hs
  exact hs

lemma run_success_from_mean [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam Γ ε : ℝ} (hlam : 0 < lam) (hΓ : 0 < Γ) (hε : 0 < ε) (hε1 : ε < 1)
    (I : State G) (T : ℕ) (hT : 1 ≤ T)
    (hmean : (1-ε/2)*Fintype.card V/Γ ≤ timeMean G lam (point I) T) :
    ε/(2*Γ) ≤ success G (runLargest G lam I T) ((1-ε)*Fintype.card V/Γ) := by
  have hN : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have ha : 0 ≤ (1-ε)*Fintype.card V/Γ := by positivity
  have hup := expectation_size_upper G (runLargest_dist G hlam I T) ha
  have hlo := hmean.trans (record_time_domination G hlam I T hT)
  have heq : (1-ε)*Fintype.card V/Γ + (ε/(2*Γ))*Fintype.card V =
      (1-ε/2)*Fintype.card V/Γ := by ring
  have hh : (ε/(2*Γ))*Fintype.card V ≤
      success G (runLargest G lam I T) ((1-ε)*Fintype.card V/Γ)*Fintype.card V := by nlinarith
  exact (mul_le_mul_iff_left₀ hN).mp hh

lemma repetition_row_average (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (I : State G) (T : ℕ) (B : State G) (f : State G → ℝ) :
    (∑ C, repetitionKernel G lam I T B C*f C) = ∑ A, runLargest G lam I T A*f (larger G B A) := by
  classical
  unfold repetitionKernel
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma failure_step (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (I : State G) (T : ℕ) (ν : State G → ℝ) (a : ℝ) :
    failure G (push ν (repetitionKernel G lam I T)) a = failure G ν a*failure G (runLargest G lam I T) a := by
  classical
  unfold failure
  rw [expectation_push]
  simp_rw [repetition_row_average]
  have he (B A : State G) : (if (size (larger G B A).val:ℝ) < a then (1:ℝ) else 0) =
      (if (size B.val:ℝ) < a then 1 else 0)*(if (size A.val:ℝ) < a then 1 else 0) := by
    rw [size_larger, Nat.cast_max]
    by_cases hB : (size B.val:ℝ) < a <;> by_cases hA : (size A.val:ℝ) < a <;>
      simp [max_lt_iff, hB, hA]
  simp_rw [he]
  have he' (B : State G) : (∑ A, runLargest G lam I T A *
      ((if (size B.val:ℝ) < a then 1 else 0)*(if (size A.val:ℝ) < a then 1 else 0))) =
      (if (size B.val:ℝ) < a then 1 else 0)*expectation (runLargest G lam I T) (fun A => if (size A.val:ℝ) < a then 1 else 0) := by
    unfold expectation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A _
    ring
  simp_rw [he', ← mul_assoc, ← Finset.sum_mul]
  rfl

lemma failure_power (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (I : State G) (T R : ℕ) (ν : State G → ℝ) (a : ℝ) :
    failure G (push ν (repetitionKernel G lam I T^R)) a =
      failure G ν a*(failure G (runLargest G lam I T) a)^R := by
  induction R with
  | zero => simp [push]
  | succ R ih => rw [pow_succ, ← push_push, failure_step, ih, pow_succ]; ring

lemma failure_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] {ν : State G → ℝ}
    (hν : MarkovMixing.IsDist ν) (a : ℝ) : 0 ≤ failure G ν a := by
  unfold failure expectation
  apply Finset.sum_nonneg
  intro I _
  exact mul_nonneg (hν.1 I) (by dsimp only; split_ifs <;> norm_num)

lemma failure_le_one (G : SimpleGraph V) [DecidableRel G.Adj] {ν : State G → ℝ}
    (hν : MarkovMixing.IsDist ν) (a : ℝ) : failure G ν a ≤ 1 := by
  have hh := success_add_failure G hν a
  have hs := success_nonneg G hν a
  linarith

lemma amplification_bound [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam) (I : State G) (T R : ℕ) {a q : ℝ}
    (hq : q ≤ success G (runLargest G lam I T) a) :
    1-Real.exp (-q*R) ≤ success G (amplifiedLaw G lam I T R) a := by
  have hr := runLargest_dist G hlam I T
  have hp := point_dist I
  have hpow : failure G (runLargest G lam I T) a ^ R ≤ Real.exp (-q*R) := by
    have hf : failure G (runLargest G lam I T) a ≤ Real.exp (-q) := by
      have hs := success_add_failure G hr a
      have he := Real.one_sub_le_exp_neg q
      linarith
    calc
      _ ≤ (Real.exp (-q))^R := pow_le_pow_left₀ (failure_nonneg G hr a) hf R
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hb : failure G (amplifiedLaw G lam I T R) a ≤ Real.exp (-q*R) := by
    unfold amplifiedLaw
    rw [failure_power]
    calc
      _ ≤ 1*(failure G (runLargest G lam I T) a)^R :=
        mul_le_mul_of_nonneg_right (failure_le_one G hp a) (pow_nonneg (failure_nonneg G hr a) R)
      _ ≤ _ := by simpa using hpow
  have hs := success_add_failure G (amplified_dist G hlam I T R) a
  linarith

lemma computed_repetition_bound [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {Δ : ℕ} {lam c ε δ : ℝ} (hlam : 0 < lam) (hΓ : 0 < Gamma Δ lam c)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (I : State G) (T : ℕ) {a : ℝ}
    (hs : ε/(2*Gamma Δ lam c) ≤ success G (runLargest G lam I T) a) :
    1-δ ≤ success G (amplifiedLaw G lam I T (repeats Δ lam c ε δ)) a := by
  let q := ε/(2*Gamma Δ lam c)
  have hq : 0 < q := by dsimp [q]; positivity
  have hceil : (2*Gamma Δ lam c/ε)*Real.log (1/δ) ≤ (repeats Δ lam c ε δ:ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 _)
  have hprod : Real.log (1/δ) ≤ q*(repeats Δ lam c ε δ) := by
    have hh := mul_le_mul_of_nonneg_left hceil hq.le
    dsimp [q] at hh ⊢
    calc
      _ = (ε/(2*Gamma Δ lam c))*((2*Gamma Δ lam c/ε)*Real.log (1/δ)) := by field_simp <;> ring
      _ ≤ _ := hh
  have hexp : Real.exp (-q*(repeats Δ lam c ε δ)) ≤ δ := by
    calc
      _ ≤ Real.exp (-Real.log (1/δ)) := Real.exp_le_exp.mpr (by linarith)
      _ = δ := by rw [one_div, Real.log_inv, neg_neg, Real.exp_log hδ]
  have hh := amplification_bound G hlam I T (repeats Δ lam c ε δ) hs
  linarith

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma larger_assoc (G : SimpleGraph V) (A B C : State G) :
    larger G (larger G A B) C = larger G A (larger G B C) := by
  unfold larger
  split_ifs <;> simp_all <;> omega

lemma larger_eq_left (G : SimpleGraph V) {A B : State G} (h : size B.val ≤ size A.val) : larger G A B = A := by
  unfold larger
  rw [if_neg (not_lt.mpr h)]

 def recordExpect (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) (T : ℕ)
    (x : State G × State G) (f : State G × State G → ℝ) : ℝ := ∑ y,(recordKernel G lam^T) x y*f y

lemma recordExpect_zero (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (x : State G × State G) (f : State G × State G → ℝ) : recordExpect G lam 0 x f = f x := by
  simp [recordExpect,Matrix.one_apply]

lemma matrix_power_expect_succ {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (A : Matrix Ω Ω ℝ) (T : ℕ) (x : Ω) (f : Ω → ℝ) :
    (∑ y,(A^(T+1)) x y*f y) = ∑ z,A x z*(∑ y,(A^T) z y*f y) := by
  rw [pow_succ']
  change (∑ y,(∑ z,A x z*(A^T) z y)*f y) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma recordExpect_succ (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) (T : ℕ)
    (x : State G × State G) (f : State G × State G → ℝ) :
    recordExpect G lam (T+1) x f = ∑ J,K G lam x.1 J*recordExpect G lam T (J,larger G x.2 J) f := by
  change (∑ y,(recordKernel G lam^(T+1)) x y*f y) = _
  rw [matrix_power_expect_succ]
  exact record_row_average G lam x _

lemma recordExpect_max (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) (T : ℕ)
    (I A B : State G) (f : State G × State G → ℝ) :
    recordExpect G lam T (I,larger G B A) f =
      recordExpect G lam T (I,A) (fun x => f (x.1,larger G B x.2)) := by
  induction T generalizing I A with
  | zero => simp [recordExpect_zero]
  | succ T ih =>
    rw [recordExpect_succ,recordExpect_succ]
    apply Finset.sum_congr rfl
    intro J _
    congr 1
    rw [larger_assoc,ih]

 def afterRuns (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (I : State G) (T R : ℕ) (B : State G) (f : State G → ℝ) : ℝ :=
  ∑ C,(repetitionKernel G lam I T^R) B C*f C

lemma afterRuns_zero (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (I B : State G) (T : ℕ) (f : State G → ℝ) : afterRuns G lam I T 0 B f = f B := by
  simp [afterRuns,Matrix.one_apply]

lemma afterRuns_succ (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (I B : State G) (T R : ℕ) (f : State G → ℝ) :
    afterRuns G lam I T (R+1) B f = ∑ A,runLargest G lam I T A*afterRuns G lam I T R (larger G B A) f := by
  change (∑ C,(repetitionKernel G lam I T^(R+1)) B C*f C) = _
  rw [matrix_power_expect_succ]
  exact repetition_row_average G lam I T B _

lemma recordExpect_reset (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (I B : State G) (T R : ℕ) (f : State G → ℝ) (hB : size I.val ≤ size B.val) :
    recordExpect G lam T (I,B) (fun x => afterRuns G lam I T R x.2 f) = afterRuns G lam I T (R+1) B f := by
  have hh := recordExpect_max G lam T I I B (fun x => afterRuns G lam I T R x.2 f)
  rw [larger_eq_left G hB] at hh
  rw [hh,afterRuns_succ]
  unfold recordExpect runLargest
  simp_rw [Finset.sum_mul]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]

lemma stochastic_row_bounds {Ω : Type} [Fintype Ω] {K : Matrix Ω Ω ℝ}
    (hK : MarkovMixing.IsStochastic K) (x : Ω) {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    0 ≤ (∑ y,K x y*f y) ∧ (∑ y,K x y*f y) ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun y _ => mul_nonneg (hK.1 x y) (hf y).1)
  · calc
      _ ≤ ∑ y,K x y*1 := Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hf y).2 (hK.1 x y))
      _ = _ := by simpa using hK.2 x

lemma afterRuns_bounds [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (I B : State G) (T R : ℕ) {f : State G → ℝ} (hf : ∀ I, 0 ≤ f I ∧ f I ≤ 1) :
    0 ≤ afterRuns G lam I T R B f ∧ afterRuns G lam I T R B f ≤ 1 := by
  exact stochastic_row_bounds (stochastic_pow (repetition_stochastic G hlam I T) R) B hf

lemma recordExpect_bounds [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (T : ℕ) (x : State G × State G) {f : State G × State G → ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    0 ≤ recordExpect G lam T x f ∧ recordExpect G lam T x f ≤ 1 := by
  exact stochastic_row_bounds (stochastic_pow (record_stochastic G hlam) T) x hf

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section

 def bitRecord {n : ℕ} (best next : Fin n → Bool) : Fin n → Bool :=
  if bitSize best < bitSize next then next else best

 def proposalMean (q : ℕ) (f : Bool → ℝ) : ℝ := (f true+q*f false)/(q+1)

 def bitAverage {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q : ℕ)
    (current : Fin n → Bool) (f : (Fin n → Bool) → ℝ) : ℝ :=
  (∑ u : Fin n, proposalMean q (fun coin => f (bitSpin G current u coin)))/n

 def bitRun {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q : ℕ)
    (f : (Fin n → Bool) → ℝ) : ℕ → (Fin n → Bool) → (Fin n → Bool) → ℝ
  | 0,_,best => f best
  | T+1,current,best => bitAverage G q current (fun next => bitRun G q f T next (bitRecord best next))

 def bitRuns {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q T : ℕ)
    (initial : Fin n → Bool) (f : (Fin n → Bool) → ℝ) : ℕ → (Fin n → Bool) → ℝ
  | 0,best => f best
  | R+1,best => bitRun G q (bitRuns G q T initial f R) T initial best

 def bitTail {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q T : ℕ)
    (initial : Fin n → Bool) (f : (Fin n → Bool) → ℝ) (runs remaining : ℕ)
    (current best : Fin n → Bool) : ℝ :=
  bitRun G q (bitRuns G q T initial f (runs-1)) remaining current best

lemma proposalMean_bounds (q : ℕ) {f : Bool → ℝ} (hf : ∀ b,0 ≤ f b ∧ f b ≤ 1) :
    0 ≤ proposalMean q f ∧ proposalMean q f ≤ 1 := by
  have hq : (0:ℝ) < q+1 := by positivity
  unfold proposalMean
  constructor
  · positivity [ (hf true).1, (hf false).1 ]
  · apply (div_le_iff₀ hq).mpr
    nlinarith [(hf true).2,(hf false).2]

lemma bitAverage_bounds {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (q : ℕ) (current : Fin n → Bool) {f : (Fin n → Bool) → ℝ}
    (hf : ∀ s,0 ≤ f s ∧ f s ≤ 1) : 0 ≤ bitAverage G q current f ∧ bitAverage G q current f ≤ 1 := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  unfold bitAverage
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun u _ => (proposalMean_bounds q (fun _ => hf _)).1)) hn'.le
  · apply (div_le_iff₀ hn').mpr
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun (u : Fin n) _ => (proposalMean_bounds q (fun _ => hf _)).2)

lemma bitRun_bounds {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (q T : ℕ) {f : (Fin n → Bool) → ℝ} (hf : ∀ s,0 ≤ f s ∧ f s ≤ 1)
    (current best : Fin n → Bool) : 0 ≤ bitRun G q f T current best ∧ bitRun G q f T current best ≤ 1 := by
  induction T generalizing current best with
  | zero => exact hf best
  | succ T ih => exact bitAverage_bounds hn G q current (fun _ => ih _ _)

lemma bitRuns_bounds {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (q T R : ℕ) (initial best : Fin n → Bool) {f : (Fin n → Bool) → ℝ}
    (hf : ∀ s,0 ≤ f s ∧ f s ≤ 1) : 0 ≤ bitRuns G q T initial f R best ∧ bitRuns G q T initial f R best ≤ 1 := by
  induction R generalizing best with
  | zero => exact hf best
  | succ R ih => exact bitRun_bounds hn G q T (fun _ => ih _) initial best

lemma bitTail_finish {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q T : ℕ)
    (initial : Fin n → Bool) (f : (Fin n → Bool) → ℝ) {runs : ℕ} (hr : 1 ≤ runs)
    (current best : Fin n → Bool) :
    bitTail G q T initial f runs 0 current best =
      if 1 < runs then bitTail G q T initial f (runs-1) T initial best else f best := by
  unfold bitTail
  simp only [bitRun]
  split_ifs with h
  · obtain ⟨R,hR⟩ := Nat.exists_eq_add_of_le (show 1 ≤ runs-1 by omega)
    rw [hR]
    simp only [Nat.add_comm 1 R,bitRuns,Nat.add_sub_cancel_left,Nat.add_sub_cancel_right]
  · have hh : runs=1 := by omega
    simp [hh,bitRuns]

lemma bitTail_step {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q T : ℕ)
    (initial : Fin n → Bool) (f : (Fin n → Bool) → ℝ) {remaining : ℕ} (ht : 1 ≤ remaining)
    (runs : ℕ) (current best : Fin n → Bool) :
    bitTail G q T initial f runs remaining current best = bitAverage G q current
      (fun next => bitTail G q T initial f runs (remaining-1) next (bitRecord best next)) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le ht
  simp [bitTail,bitRun,Nat.add_comm]

lemma uniform_proposal (q : ℕ) (f : Bool → ℝ) :
    uniformMean (q+1) (fun a => f (decide (a=0))) = proposalMean q f := by
  unfold uniformMean proposalMean
  rw [Finset.sum_range_succ']
  simp only [Nat.add_eq_zero_iff,one_ne_zero,and_false,decide_false,decide_true]
  simp
  ring

lemma uniform_site {n : ℕ} (f : Fin n → ℝ) (default : ℝ) :
    uniformMean n (fun a => if h : a<n then f ⟨a,h⟩ else default) = (∑ u : Fin n,f u)/n := by
  unfold uniformMean
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  simp

lemma bitRecord_hardcore {n : ℕ} (G : SimpleGraph (Fin n)) {B J : Fin n → Bool}
    (hB : MarkovMixing.IsHardcore G B) (hJ : MarkovMixing.IsHardcore G J) :
    MarkovMixing.IsHardcore G (bitRecord B J) := by unfold bitRecord; split_ifs <;> assumption

lemma bitRecord_eq_larger {n : ℕ} (G : SimpleGraph (Fin n)) (B J : State G) :
    bitRecord B.val J.val = (larger G B J).val := by
  unfold bitRecord larger
  simp only [bitSize_eq_size]
  split_ifs <;> rfl

lemma bitAverage_eq_scan {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {q : ℕ} (hq : 1 ≤ q) (I : State G) (f : (Fin n → Bool) → ℝ) :
    bitAverage G q I.val f = ∑ J,K G (1/q) I J*f J.val := by
  have hq' : (0:ℝ) < q := by exact_mod_cast (show 0<q by omega)
  have hp : p (1/(q:ℝ)) = 1/(q+1) := by unfold p; field_simp <;> ring
  rw [scan_eq]
  simp only [Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul,Fintype.card_fin]
  change _ = ∑ J,((n:ℝ)⁻¹*(∑ u : Fin n,P G (1/q) u I J))*f J.val
  simp_rw [mul_assoc,Finset.sum_mul,← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [single_site_average G (one_div_pos.mpr hq') I _ (fun J => f J.val),hp]
  unfold bitAverage proposalMean
  rw [div_eq_mul_inv,mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  simp only [bitSpin_eq_update,spinState]
  field_simp
  <;> ring

lemma bitRun_eq_record {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {q : ℕ} (hq : 1 ≤ q) (T : ℕ) (I B : State G) (f : (Fin n → Bool) → ℝ) :
    bitRun G q f T I.val B.val = recordExpect G (1/q) T (I,B) (fun x => f x.2.val) := by
  induction T generalizing I B with
  | zero => simp [bitRun,recordExpect_zero]
  | succ T ih =>
    rw [bitRun,bitAverage_eq_scan G hq,recordExpect_succ]
    apply Finset.sum_congr rfl
    intro J _
    rw [bitRecord_eq_larger,ih]

lemma bitRuns_eq_afterRuns {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {q : ℕ} (hq : 1 ≤ q) (T R : ℕ) (I B : State G) (f : (Fin n → Bool) → ℝ)
    (hB : size I.val ≤ size B.val) :
    bitRuns G q T I.val f R B.val = afterRuns G (1/q) I T R B (fun J => f J.val) := by
  induction R generalizing B with
  | zero => simp [bitRuns,afterRuns_zero]
  | succ R ih =>
    rw [bitRuns,bitRun_eq_record G hq]
    have he : recordExpect G (1/q) T (I,B)
        (fun x => bitRuns G q T I.val f R x.2.val) =
      recordExpect G (1/q) T (I,B)
        (fun x => afterRuns G (1/q) I T R x.2 (fun J => f J.val)) := by
      have hm := recordExpect_max G (1/q) T I I B
        (fun x => bitRuns G q T I.val f R x.2.val)
      have hm' := recordExpect_max G (1/q) T I I B
        (fun x => afterRuns G (1/q) I T R x.2 (fun J => f J.val))
      rw [larger_eq_left G hB] at hm hm'
      rw [hm,hm']
      unfold recordExpect
      apply Finset.sum_congr rfl
      intro x _
      exact congrArg (fun a : ℝ => (recordKernel G (1/q)^T) (I,I) x*a)
        (ih (larger G B x.2) (hB.trans (by rw [size_larger]; exact le_max_left _ _)))
    rw [he,recordExpect_reset G _ I B T R _ hB]

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section

 def firstMassENN {S : Type} (step : S → Bool → S) (live : S → Bool) (f : S → ℝ)
    (s : S) (j : ℕ) : ENNReal :=
  ∑ tape : Fin (j+1) → Bool, if live (((List.ofFn tape).take j).foldl step s) then
    ENNReal.ofReal (f ((List.ofFn tape).foldl step s))*(2:ENNReal)⁻¹^(j+1) else 0

lemma firstMassENN_ofReal {S : Type} (step : S → Bool → S) (live : S → Bool) (f : S → ℝ)
    (hf : ∀ s, 0 ≤ f s) (s : S) (j : ℕ) :
    ENNReal.ofReal (firstMass step live f s j) = firstMassENN step live f s j := by
  unfold firstMass firstMassENN
  rw [ENNReal.ofReal_sum_of_nonneg (by
    intro tape _
    split_ifs
    · exact mul_nonneg (hf _) (by positivity)
    · exact le_rfl)]
  apply Finset.sum_congr rfl
  intro tape _
  split_ifs
  · rw [ENNReal.ofReal_mul (hf _),ENNReal.ofReal_pow (by norm_num)]
    rw [show ENNReal.ofReal (1/2:ℝ) = (2:ENNReal)⁻¹ by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num]
  · simp

 def bitLive {n : ℕ} (s : BitState n) : Bool := !(isDone s)
 def bitTerminal {n : ℕ} (out : Fin n → Bool) : BitState n → ℝ
  | .done B => if B = out then 1 else 0
  | _ => 0

lemma bitTerminal_nonneg {n : ℕ} (out : Fin n → Bool) (s : BitState n) : 0 ≤ bitTerminal out s := by
  cases s <;> simp [bitTerminal] <;> split_ifs <;> norm_num

lemma bitLaw_firstMass {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b : ℚ) (initial out : Fin n → Bool) (m : ℕ) :
    bitLaw G Δ t b initial m out = ∑' j,ENNReal.ofReal
      (firstMass (bitStep G Δ t b initial m) bitLive (bitTerminal out) (.prepare 1) j) := by
  classical
  unfold bitLaw
  apply tsum_congr
  intro j
  rw [firstMassENN_ofReal _ _ _ (bitTerminal_nonneg out)]
  unfold firstMassENN
  apply Finset.sum_congr rfl
  intro tape _
  change (if isDone (bitEval G Δ t b initial m ((List.ofFn tape).take j)) then 0 else
      match bitEval G Δ t b initial m (List.ofFn tape) with
      | .done B => if B = out then (2:ENNReal)⁻¹^(j+1) else 0
      | _ => 0) =
    (if !(isDone (bitEval G Δ t b initial m ((List.ofFn tape).take j))) then
      ENNReal.ofReal (bitTerminal out (bitEval G Δ t b initial m (List.ofFn tape)))*(2:ENNReal)⁻¹^(j+1) else 0)
  cases hp : isDone (bitEval G Δ t b initial m ((List.ofFn tape).take j)) <;>
    cases he : bitEval G Δ t b initial m (List.ofFn tape) <;> simp [hp,he,bitTerminal]
  split_ifs <;> norm_num

 def liftBitStep {S : Type} (P : S → Prop) (step : S → Bool → S)
    (hc : ∀ s, P s → ∀ b, P (step s b)) (s : Subtype P) (b : Bool) : Subtype P := ⟨step s.val b,hc _ s.property b⟩

lemma liftBitStep_fold {S : Type} (P : S → Prop) (step : S → Bool → S)
    (hc : ∀ s, P s → ∀ b, P (step s b)) (s : Subtype P) (tape : List Bool) :
    (tape.foldl (liftBitStep P step hc) s).val = tape.foldl step s.val := by
  induction tape generalizing s with
  | nil => rfl
  | cons b tape ih => simp only [List.foldl_cons]; exact ih _

lemma tapeMean_lift {S : Type} (P : S → Prop) (step : S → Bool → S)
    (hc : ∀ s, P s → ∀ b, P (step s b)) (s : Subtype P) (f : S → ℝ) (j : ℕ) :
    tapeMean (liftBitStep P step hc) s (fun s => f s.val) j = tapeMean step s.val f j := by
  unfold tapeMean tapeSum
  simp_rw [liftBitStep_fold]

lemma firstMass_lift {S : Type} (P : S → Prop) (step : S → Bool → S)
    (hc : ∀ s, P s → ∀ b, P (step s b)) (s : Subtype P) (live : S → Bool) (f : S → ℝ) (j : ℕ) :
    firstMass (liftBitStep P step hc) (fun s => live s.val) (fun s => f s.val) s j = firstMass step live f s.val j := by
  unfold firstMass
  simp_rw [liftBitStep_fold]

lemma tapeMean_ofReal {S : Type} (step : S → Bool → S) (s : S) (f : S → ℝ)
    (hf : ∀ s, 0 ≤ f s) (j : ℕ) :
    ENNReal.ofReal (tapeMean step s f j) =
      ∑ tape : Fin j → Bool,ENNReal.ofReal (f ((List.ofFn tape).foldl step s))*(2:ENNReal)⁻¹^j := by
  unfold tapeMean tapeSum
  rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_sum_of_nonneg (by intro tape _; exact hf _),Finset.mul_sum]
  rw [show ENNReal.ofReal (1/2:ℝ) = (2:ENNReal)⁻¹ by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num]
  apply Finset.sum_congr rfl
  intro tape _
  exact mul_comm _ _

lemma firstMass_nonneg {S : Type} (step : S → Bool → S) (live : S → Bool)
    {f : S → ℝ} (hf : ∀ s,0 ≤ f s) (s : S) (j : ℕ) : 0 ≤ firstMass step live f s j := by
  unfold firstMass
  apply Finset.sum_nonneg
  intro tape _
  split_ifs
  · exact mul_nonneg (hf _) (by positivity)
  · exact le_rfl

lemma firstMass_summable {S : Type} (step : S → Bool → S) (live : S → Bool) (f : S → ℝ)
    (hf : ∀ s,0 ≤ f s ∧ f s ≤ 1)
    (hf0 : ∀ s, live s = true → f s = 0)
    (hfend : ∀ s, live s = false → ∀ b,f (step s b)=f s) (s : S) :
    Summable (firstMass step live f s) := by
  change Summable (fun j => firstMass step live f s j)
  simp_rw [firstMass_eq_rate]
  exact haltRate_summable step live f hf hf0 hfend s

lemma bitLaw_of_certificate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b : ℚ) (initial out : Fin n → Bool) (m : ℕ)
    (P : BitState n → Prop) (hc : ∀ s,P s → ∀ coin,P (bitStep G Δ t b initial m s coin))
    (hstart : P (.prepare 1)) (H V : Subtype P → ℝ)
    (hH : ∀ s,0 ≤ H s ∧ H s ≤ 1) (hV : ∀ s,0 ≤ V s)
    (hend : ∀ s : Subtype P, bitLive s.val = false → H s = bitTerminal out s.val)
    (hharm : ∀ s,(H (liftBitStep P _ hc s true)+H (liftBitStep P _ hc s false))/2=H s)
    (hstep : ∀ s,(bitStepCost G Δ t b m s.val:ℝ)+
      (V (liftBitStep P _ hc s true)+V (liftBitStep P _ hc s false))/2 ≤ V s) :
    bitLaw G Δ t b initial m out = ENNReal.ofReal (H ⟨.prepare 1,hstart⟩) := by
  let step := liftBitStep P (bitStep G Δ t b initial m) hc
  let s : Subtype P := ⟨.prepare 1,hstart⟩
  let live := fun s : Subtype P => bitLive s.val
  let f := fun s : Subtype P => bitTerminal out s.val
  have hf : ∀ s,0 ≤ f s ∧ f s ≤ 1 := by
    intro s
    change 0 ≤ bitTerminal out s.val ∧ bitTerminal out s.val ≤ 1
    cases s.val <;> simp [bitTerminal] <;> split_ifs <;> norm_num
  have hf0 : ∀ s,live s=true → f s=0 := by
    intro s hs
    cases he : s.val with
    | prepare h => simp only [f,he,bitTerminal]
    | draw q runs rem cur best prop site j acc => simp only [f,he,bitTerminal]
    | done best => simp only [live,he,bitLive,isDone,Bool.not_true,Bool.false_eq_true] at hs
  have hfend : ∀ s,live s=false → ∀ coin,f (step s coin)=f s := by
    intro s hs coin
    change bitTerminal out (bitStep G Δ t b initial m s.val coin) = bitTerminal out s.val
    cases he : s.val with
    | prepare h => simp only [live,he,bitLive,isDone,Bool.not_false,Bool.true_eq_false] at hs
    | draw q runs rem cur best prop site j acc => simp only [live,he,bitLive,isDone,Bool.not_false,Bool.true_eq_false] at hs
    | done best => rfl
  have hcost : ∀ s : Subtype P, (if live s then (1:ℝ) else 0) ≤ (bitStepCost G Δ t b m s.val:ℝ) := by
    intro s
    cases he : s.val <;> simp only [live,he,bitLive,isDone,Bool.not_true,Bool.not_false,ite_true,ite_false,bitStepCost]
    · exact_mod_cast (show 1 ≤ 1+(bits _+1)^3+((parameterStage Δ t b _).run 0).2 by omega)
    · exact_mod_cast (show 1 ≤ 1+(_)^3+(if _ then _ else 0) by omega)
    · norm_num
  have htail := survival_tendsto_of_potential step live
    (fun s => (bitStepCost G Δ t b m s.val:ℝ)) V (fun s => Nat.cast_nonneg _) hV hstep
    hcost s
  have hlaw := harmonic_halt_law step live f H hf hH hf0 hfend hend hharm s (by rfl) htail
  simp_rw [← firstMass_eq_rate] at hlaw
  have hsum := firstMass_summable step live f hf hf0 hfend s
  have heq (j : ℕ) : firstMass step live f s j =
      firstMass (bitStep G Δ t b initial m) bitLive (bitTerminal out) (.prepare 1) j :=
    firstMass_lift P _ hc s _ _ j
  rw [bitLaw_firstMass]
  simp_rw [← heq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (firstMass_nonneg step live (fun s => (hf s).1) s) hsum,hlaw]

lemma expectedBitCost_of_certificate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b : ℚ) (I : State G) (m : ℕ)
    (P : BitState n → Prop) (hc : ∀ s,P s → ∀ coin,P (bitStep G Δ t b I.val m s coin))
    (hstart : P (.prepare 1)) (V : Subtype P → ℝ) (hV : ∀ s,0 ≤ V s)
    (hstep : ∀ s,(bitStepCost G Δ t b m s.val:ℝ)+
      (V (liftBitStep P _ hc s true)+V (liftBitStep P _ hc s false))/2 ≤ V s) :
    expectedBitCost G Δ t b I m ≤
      ENNReal.ofReal ((n^2+ratBits b+bits t+m+1:ℕ)+V ⟨.prepare 1,hstart⟩) := by
  let step := liftBitStep P (bitStep G Δ t b I.val m) hc
  let s : Subtype P := ⟨.prepare 1,hstart⟩
  let cost := fun s : Subtype P => (bitStepCost G Δ t b m s.val:ℝ)
  have hs := tape_cost_summable step cost V (fun s => Nat.cast_nonneg _) hV hstep s
  have heq (j : ℕ) : (∑ tape : Fin j → Bool,
      (bitStepCost G Δ t b m (bitEval G Δ t b I.val m (List.ofFn tape)):ENNReal)*2⁻¹^j) =
      ENNReal.ofReal (tapeMean step s cost j) := by
    rw [tapeMean_ofReal step s cost (fun s => Nat.cast_nonneg _)]
    apply Finset.sum_congr rfl
    intro tape _
    simp only [cost,step,liftBitStep_fold,ENNReal.ofReal_natCast,bitEval,s]
  unfold expectedBitCost
  simp_rw [heq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => tapeMean_nonneg step s (fun s => Nat.cast_nonneg _) j) hs.1]
  rw [ENNReal.ofReal_add (by positivity) (hV _)]
  simp only [ENNReal.ofReal_natCast]
  exact add_le_add_right (ENNReal.ofReal_le_ofReal hs.2) _

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section

 def rejectValue (m j acc : ℕ) (f : ℕ → ℝ) : ℝ :=
  blockMean (drawWidth m) j acc (fun a => if a < m then f a else uniformMean m f)

lemma rejectValue_start {m : ℕ} (hm : 1  ≤  m) (f : ℕ → ℝ) :
    rejectValue m 0 0 f = uniformMean m f := blockMean_rejection_start hm f

lemma rejectValue_end (m acc : ℕ) (f : ℕ → ℝ) :
    rejectValue m (drawWidth m) acc f = if acc < m then f acc else uniformMean m f :=
  blockMean_end _ _ _

lemma rejectValue_step (m j acc : ℕ) (hj : j  <  drawWidth m) (f : ℕ → ℝ) :
    (rejectValue m (j+1) (2*acc+1) f+rejectValue m (j+1) (2*acc) f)/2 = rejectValue m j acc f := by
  unfold rejectValue
  conv_rhs => rw [blockMean_step _ _ _ hj]
  ring

lemma uniformMean_bounds {m : ℕ} (hm : 1  ≤  m) {f : ℕ → ℝ}
    (hf : ∀ a,0  ≤  f a ∧ f a  ≤  1) : 0  ≤  uniformMean m f ∧ uniformMean m f  ≤  1 := by
  have hm' : (0:ℝ)  <  m := by exact_mod_cast (show 0 < m by omega)
  unfold uniformMean
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun a _ => (hf a).1)) hm'.le
  · apply (div_le_iff₀ hm').mpr
    simpa using Finset.sum_le_sum (s := Finset.range m) (fun a _ => (hf a).2)

lemma rejectValue_bounds {m : ℕ} (hm : 1  ≤  m) (j acc : ℕ) {f : ℕ → ℝ}
    (hf : ∀ a,0  ≤  f a ∧ f a  ≤  1) : 0  ≤  rejectValue m j acc f ∧ rejectValue m j acc f  ≤  1 := by
  have hb := uniformMean_bounds hm hf
  constructor
  · apply blockMean_nonneg
    intro a; split_ifs  <;> exact (by first | exact (hf a).1 | exact hb.1)
  · apply blockMean_le
    intro a; split_ifs  <;> exact (by first | exact (hf a).2 | exact hb.2)

 def bitAfter {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q T : ℕ)
    (initial : Fin n → Bool) (f : (Fin n → Bool) → ℝ) (runs remaining : ℕ)
    (next record : Fin n → Bool) : ℝ :=
  if 1  <  remaining then bitTail G q T initial f runs (remaining-1) next record
  else if 1  <  runs then bitTail G q T initial f (runs-1) T initial record else f record

lemma bitAfter_eq_tail {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q T : ℕ)
    (initial : Fin n → Bool) (f : (Fin n → Bool) → ℝ) {runs remaining : ℕ}
    (hr : 1  ≤  runs) (ht : 1  ≤  remaining) (next record : Fin n → Bool) :
    bitAfter G q T initial f runs remaining next record =
      bitTail G q T initial f runs (remaining-1) next record := by
  unfold bitAfter
  split_ifs with h hrun
  · rfl
  · have hh : remaining-1=0 := by omega
    rw [hh,bitTail_finish G q T initial f hr,if_pos hrun]
  · have hh : remaining-1=0 := by omega
    rw [hh,bitTail_finish G q T initial f hr,if_neg hrun]

 def bitAccepted {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q T : ℕ)
    (initial : Fin n → Bool) (f : (Fin n → Bool) → ℝ) (runs remaining : ℕ)
    (current best : Fin n → Bool) (u : Fin n) (coin : Bool) : ℝ :=
  let next := bitSpin G current u coin
  bitAfter G q T initial f runs remaining next (bitRecord best next)

 def bitSiteValue {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q T : ℕ)
    (initial : Fin n → Bool) (f : (Fin n → Bool) → ℝ) (runs remaining : ℕ)
    (current best : Fin n → Bool) (site : ℕ) : ℝ :=
  if h : site < n then proposalMean q (bitAccepted G q T initial f runs remaining current best ⟨site,h⟩) else 0

 def machineValue {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q T R : ℕ)
    (initial : Fin n → Bool) (f : (Fin n → Bool) → ℝ) : BitState n → ℝ
  | .prepare _ => bitRuns G q T initial f R initial
  | .done best => f best
  | .draw _ runs remaining current best proposal site j acc =>
    if proposal then
      rejectValue (q+1) j acc (fun a => if h : site < n then
        bitAccepted G q T initial f runs remaining current best ⟨site,h⟩ (decide (a=0)) else 0)
    else rejectValue n j acc (bitSiteValue G q T initial f runs remaining current best)

lemma machineValue_site_start {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (q T R : ℕ) (initial : Fin n → Bool) (f : (Fin n → Bool) → ℝ)
    {runs remaining : ℕ} (hr : 1  ≤  runs) (ht : 1  ≤  remaining) (current best : Fin n → Bool) :
    machineValue G q T R initial f (.draw q runs remaining current best false 0 0 0) =
      bitTail G q T initial f runs remaining current best := by
  simp only [machineValue,Bool.false_eq_true,ite_false,rejectValue_start (show 1 ≤ n by omega)]
  unfold bitSiteValue
  rw [uniform_site (fun u => proposalMean q (bitAccepted G q T initial f runs remaining current best u)) 0]
  rw [bitTail_step G q T initial f ht]
  unfold bitAverage bitAccepted
  simp_rw [bitAfter_eq_tail G q T initial f hr ht]

lemma machineValue_proposal_start {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (q T R : ℕ) (initial : Fin n → Bool) (f : (Fin n → Bool) → ℝ)
    (runs remaining : ℕ) (current best : Fin n → Bool) {site : ℕ} (hs : site < n) :
    machineValue G q T R initial f (.draw q runs remaining current best true site 0 0) =
      bitSiteValue G q T initial f runs remaining current best site := by
  simp only [machineValue,ite_true,dif_pos hs,rejectValue_start (Nat.succ_le_succ (Nat.zero_le q)),
    uniform_proposal,bitSiteValue]

lemma machineValue_bounds {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (q T R : ℕ) (initial : Fin n → Bool) {f : (Fin n → Bool) → ℝ}
    (hf : ∀ s,0  ≤  f s ∧ f s  ≤  1) (s : BitState n) :
    0  ≤  machineValue G q T R initial f s ∧ machineValue G q T R initial f s  ≤  1 := by
  have ht (runs remaining : ℕ) (cur best : Fin n → Bool) :
      0  ≤  bitTail G q T initial f runs remaining cur best ∧ bitTail G q T initial f runs remaining cur best  ≤  1 :=
    bitRun_bounds hn G q remaining (fun best => bitRuns_bounds hn G q T (runs-1) initial best hf) cur best
  have ha (runs remaining : ℕ) (cur best : Fin n → Bool) (u : Fin n) (coin : Bool) :
      0  ≤  bitAccepted G q T initial f runs remaining cur best u coin ∧
      bitAccepted G q T initial f runs remaining cur best u coin  ≤  1 := by
    unfold bitAccepted bitAfter
    split_ifs  <;> first | exact ht _ _ _ _ | exact hf _
  cases s with
  | prepare h => exact bitRuns_bounds hn G q T R initial initial hf
  | done best => exact hf best
  | draw qq runs rem cur best prop site j acc =>
    cases prop <;> simp only [machineValue,Bool.false_eq_true,ite_true,ite_false]
    · apply rejectValue_bounds (by omega)
      intro a
      unfold bitSiteValue
      split_ifs
      · exact proposalMean_bounds q (fun coin => ha _ _ _ _ _ coin)
      · constructor <;> norm_num
    · apply rejectValue_bounds (by omega)
      intro a
      split_ifs
      · exact ha _ _ _ _ _ _
      · constructor <;> norm_num

lemma machineValue_after {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (q T R : ℕ) (hT : 1 ≤ T) (initial : Fin n → Bool) (f : (Fin n → Bool) → ℝ)
    {runs remaining : ℕ} (hr : 1 ≤ runs) (next record : Fin n → Bool) :
    machineValue G q T R initial f (if 1 < remaining then
      .draw q runs (remaining-1) next record false 0 0 0 else if 1 < runs then
      .draw q (runs-1) T initial record false 0 0 0 else .done record) =
      bitAfter G q T initial f runs remaining next record := by
  unfold bitAfter
  split_ifs with ht hr'
  · exact machineValue_site_start hn G q T R initial f hr (by omega) next record
  · exact machineValue_site_start hn G q T R initial f (by omega) hT initial record
  · rfl

lemma machineValue_draw_harmonic {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b : ℚ) (I : State G) (m q R : ℕ) (hR : 1 ≤ R)
    (f : (Fin n → Bool) → ℝ) {s : BitState n}
    (hs : drawValid G I.val q (bitHorizon n) R s) :
    (machineValue G q (bitHorizon n) R I.val f (bitStep G Δ t b I.val m s true)+
      machineValue G q (bitHorizon n) R I.val f (bitStep G Δ t b I.val m s false))/2 =
      machineValue G q (bitHorizon n) R I.val f s := by
  cases s with
  | prepare h => exact False.elim hs
  | done best => simp only [bitStep,machineValue]; ring
  | draw qq runs rem cur best prop site j acc =>
    rcases hs with ⟨heq,hr1,hrR,ht1,htT,hcur,hbest,hinit,hrecord,hj,hacc,hsite⟩
    subst qq
    cases hp : prop  <;> simp only [hp,Bool.false_eq_true,ite_true,ite_false] at hj hsite
    · by_cases hbits : j < drawWidth n
      · simp only [bitStep,machineValue,Bool.false_eq_true,ite_false,if_pos hbits,ite_true]
        exact rejectValue_step n j acc hbits _
      · have hjeq : j=drawWidth n := by omega
        by_cases hrej : n ≤ acc
        · simp only [bitStep,Bool.not_false,Bool.false_eq_true,ite_false,if_neg hbits,if_pos hrej,machineValue]
          rw [hjeq,rejectValue_end,rejectValue_start (show 1 ≤ n by omega),if_neg (by omega : ¬acc < n)]
          ring
        · have ha : acc < n := by omega
          simp only [bitStep,Bool.not_false,Bool.false_eq_true,ite_false,if_neg hbits,if_neg hrej,ite_true]
          rw [machineValue_proposal_start G q (bitHorizon n) R I.val f runs rem cur best ha]
          simp only [machineValue,Bool.false_eq_true,ite_false,hjeq,rejectValue_end,if_pos ha]
          ring
    · have hsite' : site < n := hsite True.intro
      by_cases hbits : j < drawWidth (q+1)
      · simp only [bitStep,machineValue,ite_true,if_pos hbits,dif_pos hsite']
        exact rejectValue_step (q+1) j acc hbits _
      · have hjeq : j=drawWidth (q+1) := by omega
        by_cases hrej : q+1 ≤ acc
        · simp only [bitStep,ite_true,if_neg hbits,if_pos hrej,machineValue,dif_pos hsite']
          rw [hjeq,rejectValue_end,rejectValue_start (by omega : 1 ≤ q+1),if_neg (by omega : ¬acc < q+1)]
          ring
        · have ha : acc < q+1 := by omega
          simp only [bitStep,Bool.not_true,Bool.false_eq_true,ite_true,if_neg hbits,if_neg hrej,ite_false,dif_pos hsite']
          rw [machineValue_after hn G q (bitHorizon n) R (by simp [bitHorizon]) I.val f hr1]
          simp only [machineValue,ite_true,hjeq,rejectValue_end,if_pos ha,dif_pos hsite',bitAccepted,bitRecord]
          ring

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

 def updatesLeft (T runs remaining : ℕ) : ℕ := (runs-1)*T+remaining
 def workBase (n q T runs remaining : ℕ) (C : ℝ) : ℝ :=
  updatesLeft T runs remaining * (drawCost n C+drawCost (q+1) C)
 def drawWork {n : ℕ} (q T : ℕ) (C : ℝ) : BitState n → ℝ
  | .prepare _ => 0
  | .done _ => 0
  | .draw _ runs rem _ _ prop _ j acc =>
    let left := ((updatesLeft T runs rem-1:ℕ):ℝ)*(drawCost n C+drawCost (q+1) C)
    if prop then drawPotential (q+1) C left j acc
    else drawPotential n C (drawCost (q+1) C+left) j acc

lemma updatesLeft_pos {T runs rem : ℕ} (ht : 1 ≤ rem) : 1 ≤ updatesLeft T runs rem := by
  unfold updatesLeft; omega

lemma drawWork_start {n : ℕ} (hn : 1 ≤ n) (q T runs rem : ℕ) (ht : 1 ≤ rem)
    (C : ℝ) (cur best : Fin n → Bool) :
    drawWork q T C (.draw q runs rem cur best false 0 0 0) = workBase n q T runs rem C := by
  simp only [drawWork,Bool.false_eq_true,ite_false,drawPotential_start hn]
  unfold workBase
  have hh := updatesLeft_pos (T := T) (runs := runs) ht
  have he : ((updatesLeft T runs rem-1:ℕ):ℝ) = updatesLeft T runs rem-1 := by
    rw [Nat.cast_sub hh,Nat.cast_one]
  rw [he]
  ring

lemma updatesLeft_after {T runs rem : ℕ} (hr : 1 ≤ runs) (ht : 1 ≤ rem) :
    (if 1 < rem then updatesLeft T runs (rem-1) else if 1 < runs then updatesLeft T (runs-1) T else 0) =
      updatesLeft T runs rem-1 := by
  unfold updatesLeft
  split_ifs with ht' hr'
  · omega
  · have hrem : rem=1 := by omega
    have hr2 : runs-1=(runs-2)+1 := by omega
    simp only [hrem,hr2,Nat.add_mul,Nat.one_mul,Nat.add_sub_cancel_right]
  · have hr1 : runs=1 := by omega
    have ht1 : rem=1 := by omega
    simp [hr1,ht1]

lemma drawWork_after {n : ℕ} (hn : 1 ≤ n) (q T : ℕ) (hT : 1 ≤ T) (C : ℝ)
    {runs rem : ℕ} (hr : 1 ≤ runs) (ht : 1 ≤ rem) (initial next record : Fin n → Bool) :
    drawWork q T C (if 1 < rem then .draw q runs (rem-1) next record false 0 0 0 else
      if 1 < runs then .draw q (runs-1) T initial record false 0 0 0 else .done record) =
    ((updatesLeft T runs rem-1:ℕ):ℝ)*(drawCost n C+drawCost (q+1) C) := by
  have he := updatesLeft_after (T := T) hr ht
  split_ifs with hrem hruns
  · rw [drawWork_start hn q T runs (rem-1) (by omega)]
    unfold workBase
    simp only [if_pos hrem] at he
    rw [he]
  · rw [drawWork_start hn q T (runs-1) T hT]
    unfold workBase
    simp only [if_neg hrem,if_pos hruns] at he
    rw [he]
  · simp only [if_neg hrem,if_neg hruns] at he
    simp only [drawWork,← he,Nat.cast_zero,zero_mul]

lemma drawWork_nonneg {n : ℕ} (q T : ℕ) {C : ℝ} (hC : 0 ≤ C) (s : BitState n) :
    0 ≤ drawWork q T C s := by
  cases s with
  | prepare h => exact le_rfl
  | done best => exact le_rfl
  | draw qq runs rem cur best prop site j acc =>
    simp only [drawWork]
    split_ifs
    · apply drawPotential_nonneg _ hC
      exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg (drawCost_nonneg n hC) (drawCost_nonneg (q+1) hC))
    · apply drawPotential_nonneg _ hC
      exact add_nonneg (drawCost_nonneg (q+1) hC)
        (mul_nonneg (Nat.cast_nonneg _) (add_nonneg (drawCost_nonneg n hC) (drawCost_nonneg (q+1) hC)))

lemma drawWork_bellman {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b : ℚ) (I : State G) (m q R : ℕ) {C : ℝ} (hC : 0 ≤ C)
    {s : BitState n} (hs : drawValid G I.val q (bitHorizon n) R s) :
    (if isDone s then 0 else C)+
      (drawWork q (bitHorizon n) C (bitStep G Δ t b I.val m s true)+
      drawWork q (bitHorizon n) C (bitStep G Δ t b I.val m s false))/2 = drawWork q (bitHorizon n) C s := by
  cases s with
  | prepare h => exact False.elim hs
  | done best => simp only [bitStep,isDone,ite_true,drawWork]; ring
  | draw qq runs rem cur best prop site j acc =>
    rcases hs with ⟨heq,hr1,hrR,ht1,htT,hcur,hbest,hinit,hrecord,hj,hacc,hsite⟩
    subst qq
    simp only [isDone,Bool.false_eq_true,ite_false]
    cases hp : prop <;> simp only [hp,Bool.false_eq_true,ite_true,ite_false] at hj hsite
    · by_cases hbits : j < drawWidth n
      · simp only [bitStep,drawWork,Bool.false_eq_true,ite_false,if_pos hbits,ite_true]
        convert drawPotential_step n C (drawCost (q+1) C+((updatesLeft (bitHorizon n) runs rem-1:ℕ):ℝ)*
          (drawCost n C+drawCost (q+1) C)) j acc hbits using 1 <;> ring
      · have hjeq : j=drawWidth n := by omega
        by_cases hrej : n ≤ acc
        · simp only [bitStep,Bool.not_false,Bool.false_eq_true,ite_false,if_neg hbits,if_pos hrej,drawWork]
          rw [hjeq,drawPotential_end,drawPotential_start hn,if_neg (by omega : ¬acc < n)]
          ring
        · have ha : acc < n := by omega
          simp only [bitStep,Bool.not_false,Bool.false_eq_true,ite_false,if_neg hbits,if_neg hrej,ite_true,drawWork]
          rw [hjeq,drawPotential_end,drawPotential_start (by omega : 1 ≤ q+1),if_pos ha]
          ring
    · by_cases hbits : j < drawWidth (q+1)
      · simp only [bitStep,drawWork,ite_true,if_pos hbits,Bool.false_eq_true,ite_false]
        convert drawPotential_step (q+1) C (((updatesLeft (bitHorizon n) runs rem-1:ℕ):ℝ)*
          (drawCost n C+drawCost (q+1) C)) j acc hbits using 1 <;> ring
      · have hjeq : j=drawWidth (q+1) := by omega
        by_cases hrej : q+1 ≤ acc
        · simp only [bitStep,ite_true,if_neg hbits,if_pos hrej,drawWork]
          rw [hjeq,drawPotential_end,drawPotential_start (by omega : 1 ≤ q+1),if_neg (by omega : ¬acc < q+1)]
          ring
        · have ha : acc < q+1 := by omega
          have hsite' : site < n := hsite True.intro
          simp only [bitStep,Bool.not_true,Bool.false_eq_true,ite_true,if_neg hbits,if_neg hrej,ite_false,dif_pos hsite']
          rw [drawWork_after hn q (bitHorizon n) (by simp [bitHorizon]) C hr1 ht1]
          simp only [drawWork,ite_true,hjeq,drawPotential_end,if_pos ha]
          ring

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section

 def machineValid {n : ℕ} (G : SimpleGraph (Fin n)) (I : State G) (m h q : ℕ) : BitState n → Prop
  | .prepare j => 1 ≤ j ∧ j ≤ h
  | s => drawValid G I.val q (bitHorizon n) (bitRepeats n m) s

lemma machineValid_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b : ℚ) (I : State G) (m h q : ℕ) (l u : ℚ)
    (hfirst : ∀ j,1 ≤ j → j < h → ((parameterStage Δ t b j).run 0).1=none)
    (hstage : ((parameterStage Δ t b h).run 0).1=some (q,l,u))
    (s : BitState n) (hs : machineValid G I m h q s) (coin : Bool) :
    machineValid G I m h q (bitStep G Δ t b I.val m s coin) := by
  cases s with
  | prepare j =>
    rcases hs with ⟨hj1,hjh⟩
    by_cases he : j=h
    · subst j
      simp only [bitStep,hstage]
      exact drawValid_start G I q (bitHorizon n) (bitRepeats n m)
        (by simp [bitHorizon]) (by simp [bitRepeats])
    · simp only [bitStep,hfirst j hj1 (by omega)]
      exact ⟨by omega,by omega⟩
  | done best => exact hs
  | draw qq runs rem cur best prop site j acc =>
    have hh := drawValid_step G Δ t b I m q (bitRepeats n m)
      (s := .draw qq runs rem cur best prop site j acc) (by simp [bitRepeats]) hs coin
    cases he : bitStep G Δ t b I.val m (.draw qq runs rem cur best prop site j acc) coin with
    | prepare j => rw [he] at hh; exact False.elim hh
    | done best => simpa only [he,machineValid] using hh
    | draw qq runs rem cur best prop site j acc => simpa only [he,machineValid] using hh

lemma bitTail_full {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q T R : ℕ)
    (hR : 1 ≤ R) (initial : Fin n → Bool) (f : (Fin n → Bool) → ℝ) :
    bitTail G q T initial f R T initial initial = bitRuns G q T initial f R initial := by
  obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le hR
  rw [hr,Nat.add_comm 1 r]
  simp [bitTail,bitRuns]

lemma machineValue_harmonic {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b : ℚ) (I : State G) (m h q : ℕ) (l u : ℚ)
    (hfirst : ∀ j,1 ≤ j → j < h → ((parameterStage Δ t b j).run 0).1=none)
    (hstage : ((parameterStage Δ t b h).run 0).1=some (q,l,u))
    (f : (Fin n → Bool) → ℝ) (s : BitState n) (hs : machineValid G I m h q s) :
    (machineValue G q (bitHorizon n) (bitRepeats n m) I.val f (bitStep G Δ t b I.val m s true)+
    machineValue G q (bitHorizon n) (bitRepeats n m) I.val f (bitStep G Δ t b I.val m s false))/2 =
    machineValue G q (bitHorizon n) (bitRepeats n m) I.val f s := by
  cases s with
  | prepare j =>
    rcases hs with ⟨hj1,hjh⟩
    by_cases he : j=h
    · subst j
      simp only [bitStep,hstage]
      rw [machineValue_site_start hn G q (bitHorizon n) (bitRepeats n m) I.val f
        (by simp [bitRepeats]) (by simp [bitHorizon]),bitTail_full G q (bitHorizon n) (bitRepeats n m)
        (by simp [bitRepeats])]
      simp only [machineValue]
      ring
    · simp only [bitStep,hfirst j hj1 (by omega),machineValue]
      ring
  | done best => exact machineValue_draw_harmonic hn G Δ t b I m q (bitRepeats n m) (by simp [bitRepeats]) f hs
  | draw qq runs rem cur best prop site j acc =>
    exact machineValue_draw_harmonic hn G Δ t b I m q (bitRepeats n m) (by simp [bitRepeats]) f hs

 def prepareWork {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b : ℚ) (m h j : ℕ) : ℝ :=
  ∑ a ∈ Finset.Ico j (h+1),(bitStepCost G Δ t b m (.prepare a):ℝ)

 def machineWork {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b : ℚ) (m h q : ℕ) (C : ℝ) : BitState n → ℝ
  | .prepare j => prepareWork G Δ t b m h j+workBase n q (bitHorizon n) (bitRepeats n m) (bitHorizon n) C
  | s => drawWork q (bitHorizon n) C s

lemma machineWork_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b : ℚ) (m h q : ℕ) {C : ℝ} (hC : 0 ≤ C) (s : BitState n) :
    0 ≤ machineWork G Δ t b m h q C s := by
  cases s with
  | prepare j =>
    apply add_nonneg (Finset.sum_nonneg (fun a _ => Nat.cast_nonneg _))
    unfold workBase
    exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg (drawCost_nonneg n hC) (drawCost_nonneg (q+1) hC))
  | done best => exact le_rfl
  | draw qq runs rem cur best prop site j acc => exact drawWork_nonneg q (bitHorizon n) hC (.draw qq runs rem cur best prop site j acc)

lemma machineWork_bellman {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b : ℚ) (I : State G) (m h q : ℕ) (l u : ℚ)
    (hfirst : ∀ j,1 ≤ j → j < h → ((parameterStage Δ t b j).run 0).1=none)
    (hstage : ((parameterStage Δ t b h).run 0).1=some (q,l,u))
    {C : ℝ} (hC : 0 ≤ C)
    (hcost : ∀ s,drawValid G I.val q (bitHorizon n) (bitRepeats n m) s →
      (bitStepCost G Δ t b m s:ℝ) ≤ if isDone s then 0 else C)
    (s : BitState n) (hs : machineValid G I m h q s) :
    (bitStepCost G Δ t b m s:ℝ)+
      (machineWork G Δ t b m h q C (bitStep G Δ t b I.val m s true)+
      machineWork G Δ t b m h q C (bitStep G Δ t b I.val m s false))/2 ≤ machineWork G Δ t b m h q C s := by
  have hcompat (coin : Bool) {s : BitState n}
      (hs : drawValid G I.val q (bitHorizon n) (bitRepeats n m) s) :
      machineWork G Δ t b m h q C (bitStep G Δ t b I.val m s coin) =
        drawWork q (bitHorizon n) C (bitStep G Δ t b I.val m s coin) := by
    have hh := drawValid_step G Δ t b I m q (bitRepeats n m) (by simp [bitRepeats]) hs coin
    cases he : bitStep G Δ t b I.val m s coin with
    | prepare j => rw [he] at hh; exact False.elim hh
    | done best => rfl
    | draw qq runs rem cur best prop site j acc => rfl
  cases s with
  | prepare j =>
    rcases hs with ⟨hj1,hjh⟩
    by_cases he : j=h
    · subst j
      simp only [bitStep,hstage,machineWork]
      rw [drawWork_start hn q (bitHorizon n) (bitRepeats n m) (bitHorizon n) (by simp [bitHorizon])]
      simp [prepareWork]
    · have hlt : j < h := by omega
      simp only [bitStep,hfirst j hj1 hlt,machineWork]
      have heq := Finset.sum_eq_sum_Ico_succ_bot (show j < h+1 by omega)
        (fun a => (bitStepCost G Δ t b m (.prepare a):ℝ))
      unfold prepareWork
      rw [heq]
      linarith
  | done best =>
    rw [hcompat true (s := .done best) hs,hcompat false (s := .done best) hs]
    have hh := hcost (.done best) hs
    have hb := drawWork_bellman hn G Δ t b I m q (bitRepeats n m) hC (s := .done best) hs
    change _ ≤ drawWork q (bitHorizon n) C (.done best)
    linarith only [hh,hb]
  | draw qq runs rem cur best prop site j acc =>
    rw [hcompat true (s := .draw qq runs rem cur best prop site j acc) hs,
      hcompat false (s := .draw qq runs rem cur best prop site j acc) hs]
    have hh := hcost (.draw qq runs rem cur best prop site j acc) hs
    have hb := drawWork_bellman hn G Δ t b I m q (bitRepeats n m) hC (s := .draw qq runs rem cur best prop site j acc) hs
    change _ ≤ drawWork q (bitHorizon n) C (.draw qq runs rem cur best prop site j acc)
    linarith only [hh,hb]

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section


 def drawCharge (n q T R m : ℕ) : ℕ :=
  1+(10*(n+q+T+R+m+2))^3+(8*n+8)*(n+2)^3

lemma drawCharge_bounds {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b : ℚ) (I : State G) (m q R : ℕ) {s : BitState n}
    (hs : drawValid G I.val q (bitHorizon n) R s) :
    bitStepCost G Δ t b m s ≤ if isDone s then 0 else drawCharge n q (bitHorizon n) R m := by
  cases s with
  | prepare h => exact False.elim hs
  | done best => exact le_rfl
  | draw qq runs rem cur best prop site j acc =>
    rcases hs with ⟨heq,hr1,hrR,ht1,htT,hcur,hbest,hinit,hrecord,hj,hacc,hsite⟩
    subst qq
    have htarget : 1 ≤ if prop then q+1 else n := by cases prop <;> simp_all
    have hwidth := drawWidth_bounds htarget
    have hj' : j ≤ n+q+2 := by
      have hb := bits_le ((if prop then q+1 else n)-1)
      change j ≤ bits _ at hj
      cases prop <;> simp_all <;> omega
    have hacc' : acc ≤ 2*(n+q+1) := by
      have hh := (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hj)
      cases prop <;> simp_all <;> omega
    have hsum : bits n+bits q+bits runs+bits rem+bits j+bits acc+bits m+1 ≤
        10*(n+q+bitHorizon n+R+m+2) := by
      have hbn := bits_le n
      have hbq := bits_le q
      have hbr := bits_le runs
      have hbt := bits_le rem
      have hbj := bits_le j
      have hba := bits_le acc
      have hbm := bits_le m
      omega
    have hscan : (8*n+8)*(bits n+1)^3 ≤ (8*n+8)*(n+2)^3 := by
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      have hh := bits_le n
      omega
    simp only [bitStepCost,isDone,Bool.false_eq_true,ite_false]
    unfold drawCharge
    have hpow := Nat.pow_le_pow_left hsum 3
    split_ifs <;> omega

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
 def precisionStage (n : ℕ) : ℕ := 20*(n+1)^2+2

end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
 def stageCostExpr (n t Y h : CostExpr) : CostExpr :=
  let R := 2*t
  let Z := h+4*Y+12
  let S := logSizeExpr (2*n+2*Z+10) h
  let L := logCostExpr (2*n+2*Z+10) h
  let U := (20*(Z+S+1)*(R+1))^3
  let Croot := (h+2*Y+7)*(R+3)*(20*(h+4*Y+13)*(R+1))^3
  (2*Y+7)^3+(Croot+(L+(L+(L+(U+(U+(R*U+(U+(R*U+(U+(U+(U+(U+0)))))))))))))

lemma stageCostExpr_eval (n t Y h : CostExpr) (xs : ℕ → ℕ) :
    (stageCostExpr n t Y h).eval xs=stageCost (n.eval xs) (t.eval xs) (Y.eval xs) (h.eval xs) := rfl

lemma stageCost_mono {n t Y h N T Z k : ℕ} (hn : n ≤ N) (ht : t ≤ T) (hY : Y ≤ Z) (hh : h ≤ k) :
    stageCost n t Y h ≤ stageCost N T Z k := by
  let xs := fun i : ℕ => if i=0 then n else if i=1 then t else if i=2 then Y else h
  let ys := fun i : ℕ => if i=0 then N else if i=1 then T else if i=2 then Z else k
  have hx : ∀ i,xs i ≤ ys i := by intro i; dsimp only [xs,ys]; split_ifs <;> assumption
  have hm := (stageCostExpr (.input 0) (.input 1) (.input 2) (.input 3)).eval_mono hx
  rw [stageCostExpr_eval,stageCostExpr_eval] at hm
  simpa only [CostExpr.eval,xs,ys,ite_true,ite_false,if_neg (by decide : ¬(1:ℕ)=0),
    if_neg (by decide : ¬(2:ℕ)=0),if_neg (by decide : ¬(2:ℕ)=1),if_neg (by decide : ¬(3:ℕ)=0),
    if_neg (by decide : ¬(3:ℕ)=1),if_neg (by decide : ¬(3:ℕ)=2)] using hm

 def preprocessingCost (n Y : ℕ) : ℕ :=
  precisionStage n*(1+(precisionStage n+2)^3+stageCost n n Y (precisionStage n))

lemma prepareWork_bound {n Δ t h : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (b : ℚ) (m : ℕ) (hΔn : Δ ≤ n) (htn : t ≤ n) (hh : h ≤ precisionStage n) :
    prepareWork G Δ t b m h 1 ≤ (preprocessingCost n (ratBits b):ℝ) := by
  have hb (a : ℕ) (ha : a∈Finset.Ico 1 (h+1)) :
      bitStepCost G Δ t b m (.prepare a) ≤ 1+(precisionStage n+2)^3+stageCost n n (ratBits b) (precisionStage n) := by
    have ha' : a ≤ precisionStage n := by have hx := Finset.mem_Ico.mp ha; omega
    have hc := (parameterStage_budget Δ t n b a hΔn 0).2
    have hs := stageCost_mono (n := n) le_rfl htn (Nat.le_refl (ratBits b)) ha'
    have hbits : bits a+1 ≤ precisionStage n+2 := by have hx := bits_le a; omega
    have hp := Nat.pow_le_pow_left hbits 3
    simp only [bitStepCost]
    omega
  have hsum := Finset.sum_le_sum hb
  have hcnt : (Finset.Ico 1 (h+1)).card=h := by simp
  simp only [Finset.sum_const,hcnt,nsmul_eq_mul] at hsum
  have hh' := Nat.mul_le_mul_right (1+(precisionStage n+2)^3+stageCost n n (ratBits b) (precisionStage n)) hh
  have hc := hsum.trans hh'
  unfold prepareWork preprocessingCost
  exact_mod_cast hc

 def drawCostBound (n m : ℕ) : ℕ :=
  let T := 1+n^8
  let R := 1+n^3*(m+1)
  R*T*(4*n+14)*drawCharge n (n+2) T R m

lemma drawCharge_mono {n q T R m N p U S k : ℕ}
    (hn : n ≤ N) (hq : q ≤ p) (hT : T ≤ U) (hR : R ≤ S) (hm : m ≤ k) :
    drawCharge n q T R m ≤ drawCharge N p U S k := by unfold drawCharge; gcongr

lemma workBase_bound (n q m : ℕ) (hn : 1 ≤ n) (hq : q ≤ n+2) :
    workBase n q (bitHorizon n) (bitRepeats n m) (bitHorizon n)
      (drawCharge n q (bitHorizon n) (bitRepeats n m) m) ≤ (drawCostBound n m:ℝ) := by
  let T := bitHorizon n
  let R := bitRepeats n m
  let C : ℝ := drawCharge n q T R m
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hT : T ≤ 1+n^8 := max_le (by omega) (by omega)
  have hR : R ≤ 1+n^3*(m+1) := max_le (by omega) (by omega)
  have hCc : drawCharge n q T R m ≤ drawCharge n (n+2) (1+n^8) (1+n^3*(m+1)) m :=
    drawCharge_mono le_rfl hq hT hR le_rfl
  have hwidthn : drawWidth n+1 ≤ n+2 := by have hh := bits_le (n-1); unfold drawWidth; omega
  have hwidthq : drawWidth (q+1)+1 ≤ n+5 := by have hh := bits_le q; simp only [drawWidth,Nat.add_sub_cancel] ; omega
  have hcostn := drawCost_le hn hC
  have hcostq := drawCost_le (show 1 ≤ q+1 by omega) hC
  have hw : drawCost n C+drawCost (q+1) C ≤ (4*n+14)*C := by
    have hn' : ((drawWidth n+1:ℕ):ℝ) ≤ n+2 := by exact_mod_cast hwidthn
    have hq' : ((drawWidth (q+1)+1:ℕ):ℝ) ≤ n+5 := by exact_mod_cast hwidthq
    have h1 := mul_le_mul_of_nonneg_left hn' (show 0 ≤ 2*C by exact mul_nonneg (by norm_num) hC)
    have h2 := mul_le_mul_of_nonneg_left hq' (show 0 ≤ 2*C by exact mul_nonneg (by norm_num) hC)
    push_cast at h1 h2
    nlinarith
  have hR1 : 1 ≤ R := le_max_left _ _
  have hU : updatesLeft T R T=R*T := by
    unfold updatesLeft
    calc
      _ = ((R-1)+1)*T := by ring
      _ = R*T := by rw [Nat.sub_add_cancel hR1]
  unfold workBase
  rw [hU]
  have hprod : R*T ≤ (1+n^3*(m+1))*(1+n^8) := Nat.mul_le_mul hR hT
  have hprod' : ((R*T:ℕ):ℝ) ≤ ((1+n^3*(m+1))*(1+n^8):ℕ) := by exact_mod_cast hprod
  have hCc' : C ≤ (drawCharge n (n+2) (1+n^8) (1+n^3*(m+1)) m:ℝ) := by
    dsimp only [C]
    exact_mod_cast hCc
  calc
    _ ≤ ((R*T:ℕ):ℝ)*((4*n+14)*C) := mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)
    _ ≤ (((1+n^3*(m+1))*(1+n^8):ℕ):ℝ)*((4*n+14)*(drawCharge n (n+2) (1+n^8) (1+n^3*(m+1)) m:ℝ)) :=
      mul_le_mul hprod' (mul_le_mul_of_nonneg_left hCc'
        (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]))
        (mul_nonneg (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]) hC) (Nat.cast_nonneg _)
    _=_ := by unfold drawCostBound; push_cast; ring

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section

lemma machine_execution_law {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b : ℚ) (I : State G) (m h q : ℕ) (hh : 1 ≤ h) (hq : 1 ≤ q) (l u : ℚ)
    (hfirst : ∀ j,1 ≤ j → j < h → ((parameterStage Δ t b j).run 0).1=none)
    (hstage : ((parameterStage Δ t b h).run 0).1=some (q,l,u)) (out : Fin n → Bool) :
    bitLaw G Δ t b I.val m out = ENNReal.ofReal
      (∑ J : State G,amplifiedLaw G (1/q) I (bitHorizon n) (bitRepeats n m) J *
        (if J.val=out then 1 else 0)) := by
  classical
  let f := fun B : Fin n → Bool => if B=out then (1:ℝ) else 0
  let P := machineValid G I m h q
  let closed := machineValid_closed G Δ t b I m h q l u hfirst hstage
  let C : ℝ := drawCharge n q (bitHorizon n) (bitRepeats n m) m
  let V : Subtype P → ℝ := fun s => machineWork G Δ t b m h q C s.val
  let H : Subtype P → ℝ := fun s => machineValue G q (bitHorizon n) (bitRepeats n m) I.val f s.val
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hcost : ∀ s, drawValid G I.val q (bitHorizon n) (bitRepeats n m) s →
      (bitStepCost G Δ t b m s:ℝ) ≤ if isDone s then 0 else C := by
    intro s hs
    have hc := drawCharge_bounds (show 1≤n by omega) G Δ t b I m q (bitRepeats n m) hs
    dsimp only [C]
    cases he : isDone s <;> simp only [he,Bool.false_eq_true,ite_true,ite_false] at hc ⊢ <;> exact_mod_cast hc
  have hlaw := bitLaw_of_certificate G Δ t b I.val out m P closed ⟨le_rfl,hh⟩ H V
    (fun s => machineValue_bounds hn G q (bitHorizon n) (bitRepeats n m) I.val
      (fun B => by dsimp [f]; split_ifs <;> constructor <;> norm_num) s.val)
    (fun s => machineWork_nonneg G Δ t b m h q hC s.val)
    (by intro s hs; change machineValue G q (bitHorizon n) (bitRepeats n m) I.val f s.val = bitTerminal out s.val
        cases he:s.val <;> simp_all only [bitLive,isDone,Bool.not_true,Bool.not_false,Bool.true_eq_false,machineValue,bitTerminal,f])
    (fun s => machineValue_harmonic hn G Δ t b I m h q l u hfirst hstage f s.val s.property)
    (fun s => machineWork_bellman (show 1≤n by omega) G Δ t b I m h q l u hfirst hstage hC hcost s.val s.property)
  rw [hlaw]
  change ENNReal.ofReal (bitRuns G q (bitHorizon n) I.val f (bitRepeats n m) I.val) = _
  rw [bitRuns_eq_afterRuns G hq (bitHorizon n) (bitRepeats n m) I I f le_rfl]
  unfold afterRuns amplifiedLaw
  rw [point_push]

lemma machine_execution_cost {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b : ℚ) (I : State G) (m h q : ℕ) (hh : 1 ≤ h) (l u : ℚ)
    (hfirst : ∀ j,1 ≤ j → j < h → ((parameterStage Δ t b j).run 0).1=none)
    (hstage : ((parameterStage Δ t b h).run 0).1=some (q,l,u)) :
    expectedBitCost G Δ t b I m ≤ ENNReal.ofReal
      ((n^2+ratBits b+bits t+m+1:ℕ)+prepareWork G Δ t b m h 1+
      workBase n q (bitHorizon n) (bitRepeats n m) (bitHorizon n)
        (drawCharge n q (bitHorizon n) (bitRepeats n m) m)) := by
  let P := machineValid G I m h q
  let closed := machineValid_closed G Δ t b I m h q l u hfirst hstage
  let C : ℝ := drawCharge n q (bitHorizon n) (bitRepeats n m) m
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hcost : ∀ s, drawValid G I.val q (bitHorizon n) (bitRepeats n m) s →
      (bitStepCost G Δ t b m s:ℝ) ≤ if isDone s then 0 else C := by
    intro s hs
    have hc := drawCharge_bounds (show 1≤n by omega) G Δ t b I m q (bitRepeats n m) hs
    dsimp only [C]
    cases he : isDone s <;> simp only [he,Bool.false_eq_true,ite_true,ite_false] at hc ⊢ <;> exact_mod_cast hc
  have hc := expectedBitCost_of_certificate G Δ t b I m P closed ⟨le_rfl,hh⟩
    (fun s => machineWork G Δ t b m h q C s.val)
    (fun s => machineWork_nonneg G Δ t b m h q hC s.val)
    (fun s => machineWork_bellman (show 1≤n by omega) G Δ t b I m h q l u hfirst hstage hC hcost s.val s.property)
  simpa only [machineWork,add_assoc] using hc

lemma bit_execution_output {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Δ t : ℕ) (b : ℚ) (I : State G) (m h q : ℕ) (hh : 1 ≤ h) (hq : 1 ≤ q) (l u : ℚ)
    (hfirst : ∀ j,1 ≤ j → j < h → ((parameterStage Δ t b j).run 0).1=none)
    (hstage : ((parameterStage Δ t b h).run 0).1=some (q,l,u)) :
    (∑ σ : Fin n → Bool,bitLaw G Δ t b I.val m σ)=1 ∧
    MarkovMixing.IsDist (bitOutput G Δ t b I m) ∧
    bitOutput G Δ t b I m = amplifiedLaw G (1/q) I (bitHorizon n) (bitRepeats n m) := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hq' : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
  let ν := amplifiedLaw G (1/q) I (bitHorizon n) (bitRepeats n m)
  have hν := amplified_dist G (one_div_pos.mpr hq') I (bitHorizon n) (bitRepeats n m)
  have hlaw := machine_execution_law hn G Δ t b I m h q hh hq l u hfirst hstage
  have hout (J : State G) : bitLaw G Δ t b I.val m J.val = ENNReal.ofReal (ν J) := by
    rw [hlaw]
    congr 1
    have he (A : State G) : A.val=J.val ↔ A=J := Subtype.val_inj
    simp only [he,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rfl
  have heq : bitOutput G Δ t b I m=ν := by
    funext J
    rw [bitOutput,hout,ENNReal.toReal_ofReal (hν.1 J)]
  refine ⟨?_,by rw [heq]; exact hν,heq⟩
  simp_rw [hlaw]
  change (∑ σ : Fin n → Bool,ENNReal.ofReal (∑ J : State G,ν J*(if J.val=σ then 1 else 0)))=1
  have hsplit (σ : Fin n → Bool) : ENNReal.ofReal (∑ J : State G,ν J*(if J.val=σ then 1 else 0)) =
      ∑ J : State G,ENNReal.ofReal (ν J*(if J.val=σ then 1 else 0)) :=
    ENNReal.ofReal_sum_of_nonneg (fun J _ => mul_nonneg (hν.1 J) (by split_ifs <;> norm_num))
  simp_rw [hsplit]
  rw [Finset.sum_comm]
  have he (J : State G) : (∑ σ : Fin n → Bool,ENNReal.ofReal (ν J*(if J.val=σ then 1 else 0))) = ENNReal.ofReal (ν J) := by
    simp only [mul_ite,mul_one,mul_zero,apply_ite ENNReal.ofReal,ENNReal.ofReal_zero]
    simp
  simp_rw [he]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun J _ => hν.1 J),hν.2]
  norm_num

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section
set_option maxRecDepth 100000

 def totalBitPolynomial (n Y m : ℕ) : ℕ := n^2+Y+n+m+2+preprocessingCost n Y+drawCostBound n m
 def precisionStageExpr (n : CostExpr) : CostExpr := 20*(n+1)^2+2
 def drawChargeExpr (n q T R m : CostExpr) : CostExpr := 1+(10*(n+q+T+R+m+2))^3+(8*n+8)*(n+2)^3
 def preprocessingCostExpr (n Y : CostExpr) : CostExpr :=
  precisionStageExpr n*(1+(precisionStageExpr n+2)^3+stageCostExpr n n Y (precisionStageExpr n))
 def drawCostBoundExpr (n m : CostExpr) : CostExpr :=
  let T := 1+n^8
  let R := 1+n^3*(m+1)
  R*T*(4*n+14)*drawChargeExpr n (n+2) T R m
 def totalBitPolynomialExpr (n Y m : CostExpr) : CostExpr := n^2+Y+n+m+2+preprocessingCostExpr n Y+drawCostBoundExpr n m

lemma totalBitPolynomialExpr_eval (n Y m : CostExpr) (xs : ℕ → ℕ) :
    (totalBitPolynomialExpr n Y m).eval xs=totalBitPolynomial (n.eval xs) (Y.eval xs) (m.eval xs) := rfl

 def bitCostCoefficient : ℕ := (totalBitPolynomialExpr (.input 0) (.input 1) (.input 2)).mass

lemma totalBitPolynomial_bound (n Y m t : ℕ) :
    totalBitPolynomial n Y m ≤ bitCostCoefficient*(n+Y+m+bits t+1)^1000 := by
  let E := n+Y+m+bits t+1
  let xs := fun i : ℕ => if i=0 then n else if i=1 then Y else m
  have hE : 1 ≤ E := by dsimp [E]; omega
  have hx : ∀ i,xs i ≤ E := by intro i; dsimp [xs,E]; split_ifs <;> omega
  have hd : (totalBitPolynomialExpr (.input 0) (.input 1) (.input 2)).degree ≤ 1000 := by decide
  have hb := (totalBitPolynomialExpr (.input 0) (.input 1) (.input 2)).bound_larger hE hx hd
  rw [totalBitPolynomialExpr_eval] at hb
  simpa only [CostExpr.eval,xs,E,bitCostCoefficient,ite_true,ite_false,
    if_neg (by decide : ¬(1:ℕ)=0),if_neg (by decide : ¬(2:ℕ)=0),if_neg (by decide : ¬(2:ℕ)=1)] using hb

lemma bit_machine_cost_polynomial {n Δ t : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (b : ℚ) (I : State G) (m h q : ℕ) (l u : ℚ) (hΔn : Δ ≤ n) (htn : t ≤ n)
    (hh : 1 ≤ h) (hbound : h ≤ precisionStage n) (hq : q ≤ n+2)
    (hfirst : ∀ j,1 ≤ j → j < h → ((parameterStage Δ t b j).run 0).1=none)
    (hstage : ((parameterStage Δ t b h).run 0).1=some (q,l,u)) :
    expectedBitCost G Δ t b I m ≤ ENNReal.ofReal
      ((bitCostCoefficient:ℝ)*(n+ratBits b+m+bits t+1)^1000) := by
  have hc := machine_execution_cost hn G Δ t b I m h q hh l u hfirst hstage
  have hp := prepareWork_bound G b m hΔn htn hbound
  have hw := workBase_bound n q m (by omega) hq
  have hinput : n^2+ratBits b+bits t+m+1 ≤ n^2+ratBits b+n+m+2 := by
    have hh := bits_le t
    omega
  have hinput' : ((n^2+ratBits b+bits t+m+1:ℕ):ℝ) ≤ ((n^2+ratBits b+n+m+2:ℕ):ℝ) := by exact_mod_cast hinput
  have htot : ((n^2+ratBits b+bits t+m+1:ℕ):ℝ)+prepareWork G Δ t b m h 1+
      workBase n q (bitHorizon n) (bitRepeats n m) (bitHorizon n)
        (drawCharge n q (bitHorizon n) (bitRepeats n m) m) ≤ (totalBitPolynomial n (ratBits b) m:ℝ) := by
    unfold totalBitPolynomial
    push_cast
    push_cast at hinput' hp hw
    linarith only [hinput',hp,hw]
  have hpoly : (totalBitPolynomial n (ratBits b) m:ℝ) ≤ (bitCostCoefficient:ℝ)*(n+ratBits b+m+bits t+1)^1000 := by
    exact_mod_cast totalBitPolynomial_bound n (ratBits b) m t
  exact hc.trans (ENNReal.ofReal_le_ofReal (htot.trans hpoly))

end
end LocalOccupancyIS.Glauber

open LocalOccupancyIS.Glauber

theorem solution :
    ∃ B : ℝ, 1000000 ≤ B ∧
    ∀ n Δ t : ℕ, ∀ G : SimpleGraph (Fin n), ∀ _ : DecidableRel G.Adj,
    ∀ b : ℚ, ∀ I : State G, ∀ m h q : ℕ, ∀ l u : ℚ,
      0 < n → Δ ≤ n → t ≤ n → 1 ≤ h → h ≤ 20*(n+1)^2+2 → 1 ≤ q → q ≤ n+2 →
      (∀ j : ℕ,1 ≤ j → j < h → ((parameterStage Δ t b j).run 0).1=none) →
      ((parameterStage Δ t b h).run 0).1=some (q,l,u) →
      (∑ σ : Fin n → Bool,bitLaw G Δ t b I.val m σ)=1 ∧
      MarkovMixing.IsDist (bitOutput G Δ t b I m) ∧
      bitOutput G Δ t b I m=amplifiedLaw G (1/(q:ℝ)) I (bitHorizon n) (bitRepeats n m) ∧
      expectedBitCost G Δ t b I m ≤ ENNReal.ofReal (B*(n+ratBits b+m+bits t+1)^1000) := by
  refine ⟨(bitCostCoefficient:ℝ)+1000002,by have hh : (0:ℝ) ≤ bitCostCoefficient := Nat.cast_nonneg _; linarith,?_⟩
  intro n Δ t G inst b I m h q l u hn hΔn htn hh hbound hq1 hq hfirst hstage
  have hlaw := bit_execution_output hn G Δ t b I m h q hh hq1 l u hfirst hstage
  have hcost := bit_machine_cost_polynomial hn G b I m h q l u hΔn htn hh hbound hq hfirst hstage
  refine ⟨hlaw.1,hlaw.2.1,hlaw.2.2,?_⟩
  exact hcost.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) (by positivity)))
