-- Prove2me | solution 1 for KoanaKPaths.Machine.Wedge.wedgeCost_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:43:51.789136+00:00
-- url     : https://prove2.me/submissions/0eda550e-59db-4a22-a6cf-fdae9746eb01

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Machine_Wedge_wedgeReverse_width
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine

variable {S P : ℕ}



































lemma nbits_eq_bits (n : ℕ) : nbits n = Nat.bits n := by
  induction n using Nat.binaryRec' with
  | zero => simp [nbits]
  | bit b n hn ih =>
    have hne : Nat.bit b n ≠ 0 := by
      intro hz
      cases b <;> simp_all [Nat.bit]
    rw [nbits,dif_neg hne,Nat.bit_mod_two,Nat.bit_div_two,ih,Nat.bits_append_bit n b hn]
    cases b <;> rfl

















end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}









lemma moveIntsCost_le (xs : List ℤ) (w : ℕ) (hw : ∀ z ∈ xs, zsz z ≤ w) :
    moveIntsCost xs ≤ (76*w+131)*xs.length+30 := by
  unfold moveIntsCost
  have h : (xs.map (fun z => 2*moveCost (zsz z)+49)).sum ≤ (76*w+131)*xs.length := by
    induction xs with
    | nil => simp
    | cons z xs ih =>
      have hz := hw z (by simp)
      have hr := ih (fun x hx => hw x (by simp [hx]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      unfold moveCost at *
      nlinarith
  omega




























lemma zsz_neg (z : ℤ) : zsz (-z)=zsz z := by simp [zsz,zbits]



end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}







lemma growMarksCost_identity (m d : ℕ) :
    growMarksCost m d+97*m=97*m*2^d+91*d+30 := by
  induction d generalizing m with
  | zero => simp [growMarksCost]; omega
  | succ d ih =>
    simp only [growMarksCost]
    have hh := ih (2*m)
    rw [pow_succ]
    nlinarith

lemma growMarksCost_le (m d : ℕ) : growMarksCost m d ≤ (97*m+121)*2^d := by
  have h := growMarksCost_identity m d
  have hd : d ≤ 2^d := Nat.le_of_lt (Nat.lt_two_pow_self)
  have hp : 1 ≤ 2^d := Nat.one_le_pow d 2 (by omega)
  nlinarith






lemma powerMarks_cost (d : ℕ) : 1+(65*d+60)+growMarksCost 1 d ≤ 400*2^d := by
  have hg := growMarksCost_le 1 d
  have hd : d ≤ 2^d := Nat.le_of_lt (Nat.lt_two_pow_self)
  have hp : 1 ≤ 2^d := Nat.one_le_pow d 2 (by omega)
  nlinarith

end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
namespace KoanaKPaths.ExteriorCoordinates







lemma wedgeReverse_length (vs A : List ℤ) (h : A.length=2^vs.length) :
    (wedgeReverse vs A).length=2^vs.length := by
  induction vs generalizing A with
  | nil => rfl
  | cons z vs ih =>
    have hp : 2^vs.length ≤ A.length := by rw [h,List.length_cons,pow_succ]; omega
    have ha : (A.take (2^vs.length)).length=2^vs.length := by simp [List.length_take,Nat.min_eq_left hp]
    have hb : (A.drop (2^vs.length)).length=2^vs.length := by simp [List.length_drop,h,pow_succ]; omega
    simp only [wedgeReverse,List.length_append,List.length_zipWith,ih _ ha,ih _ hb,ha,Nat.min_self,
      List.length_cons,pow_succ]
    omega

end KoanaKPaths.ExteriorCoordinates

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Wedge
open KoanaKPaths.ExteriorCoordinates

lemma zsz_eq_size (z : ℤ) : zsz z=z.natAbs.size := by
  simp [zsz,zbits,nbits_eq_bits,Nat.size_eq_bits_len]

lemma zsz_le_iff (z : ℤ) (w : ℕ) : zsz z ≤ w ↔ z.natAbs<2^w := by
  rw [zsz_eq_size,Nat.size_le]

lemma zsz_add_le (x y : ℤ) (w : ℕ) (hx : zsz x≤w) (hy : zsz y≤w) : zsz (x+y)≤w+1 := by
  apply (zsz_le_iff _ _).mpr
  have hx' := (zsz_le_iff x w).mp hx
  have hy' := (zsz_le_iff y w).mp hy
  have ha := Int.natAbs_add_le x y
  rw [pow_succ]
  omega



lemma zsz_sign (z : ℤ) (hz : z=1 ∨ z = -1) : zsz z=1 := by
  rcases hz with rfl|rfl <;> simp [zsz_eq_size]

lemma zipWith_all {α β γ : Type} (f : α → β → γ) (P : γ → Prop) (xs : List α) (ys : List β)
    (h : ∀ x∈xs, ∀ y∈ys, P (f x y)) : ∀ z∈List.zipWith f xs ys, P z := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      intro z hz
      simp only [List.zipWith_cons_cons,List.mem_cons] at hz
      rcases hz with rfl|hz
      · exact h x (by simp) y (by simp)
      · exact ih ys (fun a ha b hb => h a (by simp [ha]) b (by simp [hb])) z hz



lemma sum_map_le_mul {α : Type} (f : α → ℕ) (xs : List α) (C : ℕ)
    (h : ∀ x∈xs, f x≤C) : (xs.map f).sum ≤ C*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hh := ih (fun a ha => h a (by simp [ha]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

lemma moveIntsCost_bound (xs : List ℤ) (w : ℕ) (h : ∀ z∈xs, zsz z≤w) :
    moveIntsCost xs ≤ 200*(w+1)*(xs.length+1) := by
  have hh := moveIntsCost_le xs w h
  nlinarith

lemma duplicateTakeIntsCost_bound (xs : List ℤ) (w : ℕ) (h : ∀ z∈xs, zsz z≤w) :
    duplicateTakeIntsCost xs ≤ 400*(w+1)*(xs.length+1) := by
  have hh := sum_map_le_mul (fun z => dupCost (zsz z)+17+(2*moveCost (zsz z)+19)+31)
    xs (211*w+314) (by
      intro z hz
      have hh := h z hz
      simp only [dupCost,zipCost,moveCost]
      nlinarith)
  unfold duplicateTakeIntsCost
  nlinarith

lemma addIntCost_formula (L : ℕ) : addIntCost L=297*L+393 := by
  simp only [addIntCost,addMagCost,subMagCost,zipCost,moveCost]
  ring

lemma zipAddIntsCost_bound (xs ys : List ℤ) (w : ℕ)
    (hx : ∀ z∈xs, zsz z≤w) (hy : ∀ z∈ys, zsz z≤w) :
    zipAddIntsCost xs ys ≤ 1000*(w+1)*(xs.length+1) := by
  have ha : ∀ z∈List.zipWith (fun x y => addIntCost (zsz x+zsz y)+30) xs ys,
      z≤594*w+423 := by
    apply zipWith_all
    intro x hxm y hym
    rw [addIntCost_formula]
    have hx' := hx x hxm
    have hy' := hy y hym
    omega
  have hs := sum_map_le_mul id
    (List.zipWith (fun x y => addIntCost (zsz x+zsz y)+30) xs ys) (594*w+423) ha
  simp only [List.map_id_fun,id_eq,List.map_id] at hs
  have hl : (List.zipWith (fun x y => addIntCost (zsz x+zsz y)+30) xs ys).length≤xs.length := by
    simp [List.length_zipWith]
  unfold zipAddIntsCost
  nlinarith


lemma signedList_width (z : ℤ) (xs : List ℤ) (w : ℕ) (hx : ∀ x∈xs, zsz x≤w) :
    ∀ x∈signedList z xs, zsz x≤w := by
  unfold signedList
  split
  · intro x hx'
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx'
    simpa [zsz_neg] using hx a ha
  · exact hx

lemma signedList_length (z : ℤ) (xs : List ℤ) : (signedList z xs).length=xs.length := by
  unfold signedList
  split <;> simp

lemma prepareCost_bound (d w : ℕ) (z : ℤ) (xs ys : List ℤ)
    (hz : z=1 ∨ z = -1) (hx : xs.length=2^d) (hy : ys.length=2^d)
    (hxs : ∀ x∈xs, zsz x≤w) (hys : ∀ y∈ys, zsz y≤w) :
    prepareCost d z xs ys ≤ 4000*(w+1)*2^d := by
  have hm0 := moveIntsCost_bound xs.reverse w (by simpa using hxs)
  have hm1 := moveIntsCost_bound ys w hys
  have hd := duplicateTakeIntsCost_bound xs w hxs
  have hp := powerMarks_cost d
  simp only [List.length_reverse,hx,hy] at hm0 hm1 hd
  have hp' : 1 ≤ 2^d := Nat.one_le_pow d 2 (by omega)
  unfold prepareCost
  rw [zsz_sign z hz]
  simp only [List.sum_cons,List.sum_nil,Nat.add_zero,moveCost]
  nlinarith

lemma betweenCost_bound (P w : ℕ) (lower next : List ℤ) (hP : 1≤P)
    (hl : lower.length=P) (hn : next.length=P)
    (hlw : ∀ x∈lower, zsz x≤w) (hnw : ∀ x∈next, zsz x≤w) :
    moveIntsCost lower+moveIntsCost next.reverse+5 ≤ 1000*(w+1)*P := by
  have hm0 := moveIntsCost_bound lower w hlw
  have hm1 := moveIntsCost_bound next.reverse w (by simpa using hnw)
  simp only [List.length_reverse,hl,hn] at hm0 hm1
  nlinarith

lemma finishCost_bound (P w : ℕ) (z : ℤ) (xs lower upper : List ℤ) (hP : 1≤P)
    (hz : z=1 ∨ z = -1) (hx : xs.length=P) (hl : lower.length=P) (hu : upper.length=P)
    (hxw : ∀ x∈xs, zsz x≤w) (hlw : ∀ x∈lower, zsz x≤w) (huw : ∀ x∈upper, zsz x≤w) :
    finishCost z xs lower upper ≤ 10000*(w+2)*P := by
  let sig := signedList z xs
  let neg := upper.map (fun x => -x)
  let blk := List.zipWith (·+·) sig neg
  have hsw : ∀ x∈sig, zsz x≤w := signedList_width z xs w hxw
  have hnw : ∀ x∈neg, zsz x≤w := by
    intro x hm
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    simpa [zsz_neg] using huw a ha
  have hbw : ∀ x∈blk, zsz x≤w+1 := zipWith_all _ _ sig neg
    (fun x hxm y hym => zsz_add_le x y w (hsw x hxm) (hnw y hym))
  have hslen : sig.length=P := (signedList_length z xs).trans hx
  have hnlen : neg.length=P := by simp [neg,hu]
  have hblen : blk.length=P := by simp [blk,List.length_zipWith,hslen,hnlen]
  have hmx := moveIntsCost_bound xs w hxw
  have hmxr := moveIntsCost_bound xs.reverse w (by simpa using hxw)
  have hmu := moveIntsCost_bound upper w huw
  have hml := moveIntsCost_bound lower.reverse w (by simpa using hlw)
  have hmb := moveIntsCost_bound blk.reverse (w+1) (by simpa using hbw)
  have hzip := zipAddIntsCost_bound sig neg w hsw hnw
  simp only [List.length_reverse,hx,hu,hl,hblen,hslen] at hmx hmxr hmu hml hmb hzip
  have hbranch : (if z<0 then 2*moveIntsCost xs+20*xs.length+3 else 1) ≤
      2*moveIntsCost xs+20*P+3 := by split <;> simp_all
  simp only [hx] at hbranch
  unfold finishCost
  change ([_ , _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] : List ℕ).sum+1 ≤ _
  rw [zsz_sign z hz]
  change ([1, moveIntsCost xs.reverse, 1, 2*moveCost 1+19,
    (if z<0 then 2*moveIntsCost xs+20*xs.length+3 else 1)+25,
    2*moveIntsCost upper+20*upper.length+3, 1, zipAddIntsCost sig neg, 1, 1, 1,
    moveIntsCost blk.reverse, 1, moveIntsCost lower.reverse, 1, 1] : List ℕ).sum+1 ≤ _
  simp only [List.sum_cons,List.sum_nil,Nat.add_zero,hx,hu,moveCost]
  nlinarith


theorem wedgeCost_bound (vs xs : List ℤ) (w : ℕ) (hlen : xs.length=2^vs.length)
    (hv : ∀ z∈vs, z=1 ∨ z = -1) (hx : ∀ x∈xs, zsz x≤w) :
    wedgeCost vs xs ≤ 100000*(vs.length+1)*2^vs.length*(w+vs.length+1) := by
  induction vs generalizing xs with
  | nil =>
    have hh : xs.length=1 := by simpa using hlen
    obtain ⟨x,rfl⟩ := List.length_eq_one_iff.mp hh
    have hh := hx x (by simp)
    simp only [wedgeCost,List.headD_cons,List.length_nil,pow_zero,mul_one,Nat.add_zero,zero_add]
    omega
  | cons z vs ih =>
    let d := vs.length
    let x0 := xs.take (2^d)
    let x1 := xs.drop (2^d)
    let lower := wedgeReverse vs x0
    let upper := wedgeReverse vs x1
    have hp : 1≤2^d := Nat.one_le_pow d 2 (by omega)
    have hlen' : xs.length=2^d*2 := by simpa [d,pow_succ] using hlen
    have hx0 : x0.length=2^d := by simp [x0,List.length_take,Nat.min_eq_left (by omega : 2^d≤xs.length)]
    have hx1 : x1.length=2^d := by simp only [x1,List.length_drop]; omega
    have hxs0 : ∀ x∈x0, zsz x≤w := fun x hm => hx x (List.mem_of_mem_take hm)
    have hxs1 : ∀ x∈x1, zsz x≤w := fun x hm => hx x (List.mem_of_mem_drop hm)
    have hvs : ∀ a∈vs, a=1 ∨ a = -1 := fun a hm => hv a (by simp [hm])
    have hz : z=1 ∨ z = -1 := hv z (by simp)
    have hlowlen : lower.length=2^d := wedgeReverse_length vs x0 hx0
    have huplen : upper.length=2^d := wedgeReverse_length vs x1 hx1
    have hloww : ∀ x∈lower, zsz x≤w+d := wedgeReverse_width vs x0 w hvs hxs0
    have huppw : ∀ x∈upper, zsz x≤w+d := wedgeReverse_width vs x1 w hvs hxs1
    have hxs0' : ∀ x∈x0, zsz x≤w+d := fun x hm => (hxs0 x hm).trans (Nat.le_add_right _ _)
    have hxs1' : ∀ x∈x1, zsz x≤w+d := fun x hm => (hxs1 x hm).trans (Nat.le_add_right _ _)
    have hprep := prepareCost_bound d w z x0 x1 hz hx0 hx1 hxs0 hxs1
    have hbet := betweenCost_bound (2^d) (w+d) lower x1 hp hlowlen hx1 hloww hxs1'
    have hfin := finishCost_bound (2^d) (w+d) z x0 lower upper hp hz hx0 hlowlen huplen hxs0' hloww huppw
    have hi0 := ih x0 hx0 hvs hxs0
    have hi1 := ih x1 hx1 hvs hxs1
    change wedgeCost vs x0 ≤ 100000*(d+1)*2^d*(w+d+1) at hi0
    change wedgeCost vs x1 ≤ 100000*(d+1)*2^d*(w+d+1) at hi1
    have hnode : prepareCost d z x0 x1 + (moveIntsCost lower+moveIntsCost x1.reverse+5) +
        finishCost z x0 lower upper+27 ≤ 20000*(w+d+2)*2^d := by
      nlinarith
    change prepareCost d z x0 x1+wedgeCost vs x0+
      (moveIntsCost lower+moveIntsCost x1.reverse+5)+wedgeCost vs x1+finishCost z x0 lower upper+27 ≤ _
    calc
      _ ≤ 2*(100000*(d+1)*2^d*(w+d+1))+20000*(w+d+2)*2^d := by omega
      _ ≤ 100000*((z::vs).length+1)*2^(z::vs).length*(w+(z::vs).length+1) := by
        simp only [List.length_cons,show vs.length=d from rfl,pow_succ]
        nlinarith [Nat.zero_le (w*2^d),Nat.zero_le (d*2^d)]

end KoanaKPaths.Machine.Wedge

end

theorem solution :
∀ (vs xs : List.{0} Int) (w : Nat)
  (hlen :
    @Eq.{1} Nat (@List.length.{0} Int xs)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Int vs)))
  (hv :
    ∀ (z : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) vs z →
        Or (@Eq.{1} Int z (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@Eq.{1} Int z (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
  (hx :
    ∀ (x : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) xs x →
        @LE.le.{0} Nat instLENat (NLogN.zsz x) w),
  @LE.le.{0} Nat instLENat (KoanaKPaths.Machine.Wedge.wedgeCost vs xs)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 100000) (instOfNatNat (nat_lit 100000)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Int vs)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Int vs)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w (@List.length.{0} Int vs))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  exact @KoanaKPaths.Machine.Wedge.wedgeCost_bound
