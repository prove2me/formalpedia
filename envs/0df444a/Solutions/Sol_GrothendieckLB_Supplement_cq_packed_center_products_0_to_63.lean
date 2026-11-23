-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_packed_center_products_0_to_63
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:30:58.038872+00:00
-- url     : https://prove2.me/submissions/3ffd54f9-52d5-462c-886d-60803cc57efa

import Definitions.Def_GrothendieckLB_Supplement_cqHeadSumProducts
open GrothendieckLB.Supplement CQHeadArithmetic CQHeadCertificate CQHeadSum
set_option maxHeartbeats 120000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace FastEvidence
private def wpar (a : ℕ) := (a+1)%2
private def rawB (u : Packed) (k : ℕ) : Interval := ⟨getN u 2 16 k 0,getN u 2 16 k 1⟩
private def X (a : ℕ) (u : Packed) (k : ℕ) :=
  if a+2*k+wpar a ≤ 251 then rawB u k else zeroInterval
private def Y (a : ℕ) (v : Packed) (k : ℕ) :=
  if a ≤ 2*k+a%2 then rawB v k else zeroInterval
private def G (a : ℕ) (u v : Packed) (k : ℕ) : Bool :=
  let x := X a u k
  let y := Y a v k
  decide (|center x| ≤ 2^148 ∧ 0 ≤ width x ∧ width x ≤ 1 ∧
    |center y| ≤ 2^146 ∧ 0 ≤ width y ∧ width y ≤ 256)
private def A (a : ℕ) (u : Packed) (k : ℕ) : ℤ := ((if wpar a=0 then 1 else -1):ℤ)*center (X a u k)
private def V (a : ℕ) (v : Packed) (k : ℕ) : ℤ := center (Y a v k)
private def U (a : ℕ) := entry default weightsData a
private def T (a : ℕ) := entry default powersData a
private theorem wp (a j : ℕ) (h : j%2=wpar a) : w a j=X a (U a) (j/2) := by
  unfold wpar at h
  have e : a+2*(j/2)+(a+1)%2=a+j := by omega
  simp only [w,weight,getB,h,if_true,X,U,rawB,wpar,e]
private theorem pp (a j : ℕ) (h : j%2=a%2) : p a j=Y a (T a) (j/2) := by
  have e : 2*(j/2)+a%2=j := by omega
  simp only [p,power,getB,h,if_true,Y,T,rawB,e]
private theorem wn (a j : ℕ) (h : j%2 ≠ wpar a) : w a j=zeroInterval := by
  unfold w weight getB
  simp [wpar] at h
  split <;> simp_all
private theorem pn (a j : ℕ) (h : j%2 ≠ a%2) : p a j=zeroInterval := by
  simp [p,power,getB,h]
private theorem wpSign (a j : ℕ) (h : j%2=wpar a) :
    (-1:ℤ)^j=(if wpar a=0 then 1 else -1) := by
  rw [←h]
  have h0 : j=2*(j/2)+j%2 := by omega
  conv_lhs => rw [h0,pow_add,pow_mul]
  by_cases h1 : j%2=0
  · simp [h1]
  · have h2 : j%2=1 := by omega
    simp [h2]
private theorem eW (a j : ℕ) :
    wc a j=if j%2=wpar a then A a (U a) (j/2) else 0 := by
  split
  · rename_i h; rw [wc,wp _ _ h,wpSign _ _ h];rfl
  · rename_i h; simp [wc,wn _ _ h,center,zeroInterval]
private theorem eP (a j : ℕ) :
    pc a j=if j%2=a%2 then V a (T a) (j/2) else 0 := by
  split
  · rename_i h; rw [pc,pp _ _ h];rfl
  · rename_i h; simp [pc,pn _ _ h,center,zeroInterval]

private def fast (f : ℕ → ℤ) (n i : ℕ) : ℤ :=
  match n with | 0 => 0 | k+1 => f i+(base*base)*fast f k (i+1)
private theorem pairEval {f g : ℕ → ℤ} {par : ℕ} (hp : par < 2)
    (h : ∀ j, f j=if j%2=par then g (j/2) else 0) (n i : ℕ) :
    pack base (fun j => f (2*i+j)) (2*n)=base^par*fast g n i := by
  induction n generalizing i with
  | zero => simp [pack,fast]
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega,pack,pack,fast]
    have ee : (fun j => f (2*i+(j+1+1))) = fun j => f (2*(i+1)+j) := by funext j;congr 1;omega
    rw [ee,ih,h (2*i+0),h (2*i+(0+1))]
    have p0 : (2*i+0)%2=0 := by omega
    have p1 : (2*i+(0+1))%2=1 := by omega
    have d0 : (2*i+0)/2=i := by omega
    have d1 : (2*i+(0+1))/2=i := by omega
    rcases (show par=0 ∨ par=1 by omega) with rfl|rfl <;> simp [p0,p1,d0,d1,mul_assoc]

private theorem fastRow (a : ℕ) {u v : Packed} (hu : U a=u) (hv : T a=v)
    (hprod : row a=(base^(wpar a)*fast (A a u) 126 0)*(base^(a%2)*fast (V a v) 126 0))
    (hg : (List.range 126).all (G a u v)=true) : rowHolds a := by
  subst u v
  refine ⟨?_,?_⟩
  · have he := pairEval (Nat.mod_lt (a+1) (by decide) : wpar a < 2) (eW a) 126 0
    have hf := pairEval (Nat.mod_lt a (by decide)) (eP a) 126 0
    have he' : pack base (wc a) 252=base^(wpar a)*fast (A a (U a)) 126 0 := by
      simpa only [Nat.mul_zero,Nat.zero_add,show 2*126=252 by decide] using! he
    have hf' : pack base (pc a) 252=base^(a%2)*fast (V a (T a)) 126 0 := by
      simpa only [Nat.mul_zero,Nat.zero_add,show 2*126=252 by decide] using! hf
    rw [rowProduct,he',hf']
    exact hprod
  · apply List.all_eq_true.mpr
    intro j hj
    have hn := List.mem_range.mp hj
    have hex := of_decide_eq_true (List.all_eq_true.mp hg (j/2) (List.mem_range.mpr (by omega)))
    unfold good
    apply decide_eq_true
    by_cases h0 : j%2=wpar a
    · have h1 : j%2 ≠ a%2 := by unfold wpar at h0;omega
      rw [wp _ _ h0,pn _ _ h1]
      exact ⟨hex.1,hex.2.1,hex.2.2.1,by decide +kernel⟩
    · have h1 : j%2=a%2 := by unfold wpar at h0; omega
      rw [wn _ _ h0,pp _ _ h1]
      exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,hex.2.2.2⟩
private def W0 : Packed := eval% U 0
private def P0 : Packed := eval% T 0
private theorem ok0 : rowHolds 0 := fastRow 0 (u:=W0) (v:=P0) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W1 : Packed := eval% U 1
private def P1 : Packed := eval% T 1
private theorem ok1 : rowHolds 1 := fastRow 1 (u:=W1) (v:=P1) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W2 : Packed := eval% U 2
private def P2 : Packed := eval% T 2
private theorem ok2 : rowHolds 2 := fastRow 2 (u:=W2) (v:=P2) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W3 : Packed := eval% U 3
private def P3 : Packed := eval% T 3
private theorem ok3 : rowHolds 3 := fastRow 3 (u:=W3) (v:=P3) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W4 : Packed := eval% U 4
private def P4 : Packed := eval% T 4
private theorem ok4 : rowHolds 4 := fastRow 4 (u:=W4) (v:=P4) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W5 : Packed := eval% U 5
private def P5 : Packed := eval% T 5
private theorem ok5 : rowHolds 5 := fastRow 5 (u:=W5) (v:=P5) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W6 : Packed := eval% U 6
private def P6 : Packed := eval% T 6
private theorem ok6 : rowHolds 6 := fastRow 6 (u:=W6) (v:=P6) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W7 : Packed := eval% U 7
private def P7 : Packed := eval% T 7
private theorem ok7 : rowHolds 7 := fastRow 7 (u:=W7) (v:=P7) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W8 : Packed := eval% U 8
private def P8 : Packed := eval% T 8
private theorem ok8 : rowHolds 8 := fastRow 8 (u:=W8) (v:=P8) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W9 : Packed := eval% U 9
private def P9 : Packed := eval% T 9
private theorem ok9 : rowHolds 9 := fastRow 9 (u:=W9) (v:=P9) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W10 : Packed := eval% U 10
private def P10 : Packed := eval% T 10
private theorem ok10 : rowHolds 10 := fastRow 10 (u:=W10) (v:=P10) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W11 : Packed := eval% U 11
private def P11 : Packed := eval% T 11
private theorem ok11 : rowHolds 11 := fastRow 11 (u:=W11) (v:=P11) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W12 : Packed := eval% U 12
private def P12 : Packed := eval% T 12
private theorem ok12 : rowHolds 12 := fastRow 12 (u:=W12) (v:=P12) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W13 : Packed := eval% U 13
private def P13 : Packed := eval% T 13
private theorem ok13 : rowHolds 13 := fastRow 13 (u:=W13) (v:=P13) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W14 : Packed := eval% U 14
private def P14 : Packed := eval% T 14
private theorem ok14 : rowHolds 14 := fastRow 14 (u:=W14) (v:=P14) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W15 : Packed := eval% U 15
private def P15 : Packed := eval% T 15
private theorem ok15 : rowHolds 15 := fastRow 15 (u:=W15) (v:=P15) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W16 : Packed := eval% U 16
private def P16 : Packed := eval% T 16
private theorem ok16 : rowHolds 16 := fastRow 16 (u:=W16) (v:=P16) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W17 : Packed := eval% U 17
private def P17 : Packed := eval% T 17
private theorem ok17 : rowHolds 17 := fastRow 17 (u:=W17) (v:=P17) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W18 : Packed := eval% U 18
private def P18 : Packed := eval% T 18
private theorem ok18 : rowHolds 18 := fastRow 18 (u:=W18) (v:=P18) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W19 : Packed := eval% U 19
private def P19 : Packed := eval% T 19
private theorem ok19 : rowHolds 19 := fastRow 19 (u:=W19) (v:=P19) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W20 : Packed := eval% U 20
private def P20 : Packed := eval% T 20
private theorem ok20 : rowHolds 20 := fastRow 20 (u:=W20) (v:=P20) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W21 : Packed := eval% U 21
private def P21 : Packed := eval% T 21
private theorem ok21 : rowHolds 21 := fastRow 21 (u:=W21) (v:=P21) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W22 : Packed := eval% U 22
private def P22 : Packed := eval% T 22
private theorem ok22 : rowHolds 22 := fastRow 22 (u:=W22) (v:=P22) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W23 : Packed := eval% U 23
private def P23 : Packed := eval% T 23
private theorem ok23 : rowHolds 23 := fastRow 23 (u:=W23) (v:=P23) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W24 : Packed := eval% U 24
private def P24 : Packed := eval% T 24
private theorem ok24 : rowHolds 24 := fastRow 24 (u:=W24) (v:=P24) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W25 : Packed := eval% U 25
private def P25 : Packed := eval% T 25
private theorem ok25 : rowHolds 25 := fastRow 25 (u:=W25) (v:=P25) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W26 : Packed := eval% U 26
private def P26 : Packed := eval% T 26
private theorem ok26 : rowHolds 26 := fastRow 26 (u:=W26) (v:=P26) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W27 : Packed := eval% U 27
private def P27 : Packed := eval% T 27
private theorem ok27 : rowHolds 27 := fastRow 27 (u:=W27) (v:=P27) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W28 : Packed := eval% U 28
private def P28 : Packed := eval% T 28
private theorem ok28 : rowHolds 28 := fastRow 28 (u:=W28) (v:=P28) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W29 : Packed := eval% U 29
private def P29 : Packed := eval% T 29
private theorem ok29 : rowHolds 29 := fastRow 29 (u:=W29) (v:=P29) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W30 : Packed := eval% U 30
private def P30 : Packed := eval% T 30
private theorem ok30 : rowHolds 30 := fastRow 30 (u:=W30) (v:=P30) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W31 : Packed := eval% U 31
private def P31 : Packed := eval% T 31
private theorem ok31 : rowHolds 31 := fastRow 31 (u:=W31) (v:=P31) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W32 : Packed := eval% U 32
private def P32 : Packed := eval% T 32
private theorem ok32 : rowHolds 32 := fastRow 32 (u:=W32) (v:=P32) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W33 : Packed := eval% U 33
private def P33 : Packed := eval% T 33
private theorem ok33 : rowHolds 33 := fastRow 33 (u:=W33) (v:=P33) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W34 : Packed := eval% U 34
private def P34 : Packed := eval% T 34
private theorem ok34 : rowHolds 34 := fastRow 34 (u:=W34) (v:=P34) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W35 : Packed := eval% U 35
private def P35 : Packed := eval% T 35
private theorem ok35 : rowHolds 35 := fastRow 35 (u:=W35) (v:=P35) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W36 : Packed := eval% U 36
private def P36 : Packed := eval% T 36
private theorem ok36 : rowHolds 36 := fastRow 36 (u:=W36) (v:=P36) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W37 : Packed := eval% U 37
private def P37 : Packed := eval% T 37
private theorem ok37 : rowHolds 37 := fastRow 37 (u:=W37) (v:=P37) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W38 : Packed := eval% U 38
private def P38 : Packed := eval% T 38
private theorem ok38 : rowHolds 38 := fastRow 38 (u:=W38) (v:=P38) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W39 : Packed := eval% U 39
private def P39 : Packed := eval% T 39
private theorem ok39 : rowHolds 39 := fastRow 39 (u:=W39) (v:=P39) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W40 : Packed := eval% U 40
private def P40 : Packed := eval% T 40
private theorem ok40 : rowHolds 40 := fastRow 40 (u:=W40) (v:=P40) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W41 : Packed := eval% U 41
private def P41 : Packed := eval% T 41
private theorem ok41 : rowHolds 41 := fastRow 41 (u:=W41) (v:=P41) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W42 : Packed := eval% U 42
private def P42 : Packed := eval% T 42
private theorem ok42 : rowHolds 42 := fastRow 42 (u:=W42) (v:=P42) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W43 : Packed := eval% U 43
private def P43 : Packed := eval% T 43
private theorem ok43 : rowHolds 43 := fastRow 43 (u:=W43) (v:=P43) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W44 : Packed := eval% U 44
private def P44 : Packed := eval% T 44
private theorem ok44 : rowHolds 44 := fastRow 44 (u:=W44) (v:=P44) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W45 : Packed := eval% U 45
private def P45 : Packed := eval% T 45
private theorem ok45 : rowHolds 45 := fastRow 45 (u:=W45) (v:=P45) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W46 : Packed := eval% U 46
private def P46 : Packed := eval% T 46
private theorem ok46 : rowHolds 46 := fastRow 46 (u:=W46) (v:=P46) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W47 : Packed := eval% U 47
private def P47 : Packed := eval% T 47
private theorem ok47 : rowHolds 47 := fastRow 47 (u:=W47) (v:=P47) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W48 : Packed := eval% U 48
private def P48 : Packed := eval% T 48
private theorem ok48 : rowHolds 48 := fastRow 48 (u:=W48) (v:=P48) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W49 : Packed := eval% U 49
private def P49 : Packed := eval% T 49
private theorem ok49 : rowHolds 49 := fastRow 49 (u:=W49) (v:=P49) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W50 : Packed := eval% U 50
private def P50 : Packed := eval% T 50
private theorem ok50 : rowHolds 50 := fastRow 50 (u:=W50) (v:=P50) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W51 : Packed := eval% U 51
private def P51 : Packed := eval% T 51
private theorem ok51 : rowHolds 51 := fastRow 51 (u:=W51) (v:=P51) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W52 : Packed := eval% U 52
private def P52 : Packed := eval% T 52
private theorem ok52 : rowHolds 52 := fastRow 52 (u:=W52) (v:=P52) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W53 : Packed := eval% U 53
private def P53 : Packed := eval% T 53
private theorem ok53 : rowHolds 53 := fastRow 53 (u:=W53) (v:=P53) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W54 : Packed := eval% U 54
private def P54 : Packed := eval% T 54
private theorem ok54 : rowHolds 54 := fastRow 54 (u:=W54) (v:=P54) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W55 : Packed := eval% U 55
private def P55 : Packed := eval% T 55
private theorem ok55 : rowHolds 55 := fastRow 55 (u:=W55) (v:=P55) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W56 : Packed := eval% U 56
private def P56 : Packed := eval% T 56
private theorem ok56 : rowHolds 56 := fastRow 56 (u:=W56) (v:=P56) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W57 : Packed := eval% U 57
private def P57 : Packed := eval% T 57
private theorem ok57 : rowHolds 57 := fastRow 57 (u:=W57) (v:=P57) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W58 : Packed := eval% U 58
private def P58 : Packed := eval% T 58
private theorem ok58 : rowHolds 58 := fastRow 58 (u:=W58) (v:=P58) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W59 : Packed := eval% U 59
private def P59 : Packed := eval% T 59
private theorem ok59 : rowHolds 59 := fastRow 59 (u:=W59) (v:=P59) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W60 : Packed := eval% U 60
private def P60 : Packed := eval% T 60
private theorem ok60 : rowHolds 60 := fastRow 60 (u:=W60) (v:=P60) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W61 : Packed := eval% U 61
private def P61 : Packed := eval% T 61
private theorem ok61 : rowHolds 61 := fastRow 61 (u:=W61) (v:=P61) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W62 : Packed := eval% U 62
private def P62 : Packed := eval% T 62
private theorem ok62 : rowHolds 62 := fastRow 62 (u:=W62) (v:=P62) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
private def W63 : Packed := eval% U 63
private def P63 : Packed := eval% T 63
private theorem ok63 : rowHolds 63 := fastRow 63 (u:=W63) (v:=P63) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)
end FastEvidence
open FastEvidence in
theorem solution : ∀ a : ℕ, 0 ≤ a → a < 64 → rowHolds a := by
  intro a hl hu
  by_cases h32 : a < 32
  ·
    by_cases h16 : a < 16
    ·
      by_cases h8 : a < 8
      ·
        by_cases h4 : a < 4
        ·
          rcases (show a=0 ∨ a=1 ∨ a=2 ∨ a=3 by omega) with rfl|rfl|rfl|rfl
          · exact ok0
          · exact ok1
          · exact ok2
          · exact ok3
        ·
          rcases (show a=4 ∨ a=5 ∨ a=6 ∨ a=7 by omega) with rfl|rfl|rfl|rfl
          · exact ok4
          · exact ok5
          · exact ok6
          · exact ok7
      ·
        by_cases h12 : a < 12
        ·
          rcases (show a=8 ∨ a=9 ∨ a=10 ∨ a=11 by omega) with rfl|rfl|rfl|rfl
          · exact ok8
          · exact ok9
          · exact ok10
          · exact ok11
        ·
          rcases (show a=12 ∨ a=13 ∨ a=14 ∨ a=15 by omega) with rfl|rfl|rfl|rfl
          · exact ok12
          · exact ok13
          · exact ok14
          · exact ok15
    ·
      by_cases h24 : a < 24
      ·
        by_cases h20 : a < 20
        ·
          rcases (show a=16 ∨ a=17 ∨ a=18 ∨ a=19 by omega) with rfl|rfl|rfl|rfl
          · exact ok16
          · exact ok17
          · exact ok18
          · exact ok19
        ·
          rcases (show a=20 ∨ a=21 ∨ a=22 ∨ a=23 by omega) with rfl|rfl|rfl|rfl
          · exact ok20
          · exact ok21
          · exact ok22
          · exact ok23
      ·
        by_cases h28 : a < 28
        ·
          rcases (show a=24 ∨ a=25 ∨ a=26 ∨ a=27 by omega) with rfl|rfl|rfl|rfl
          · exact ok24
          · exact ok25
          · exact ok26
          · exact ok27
        ·
          rcases (show a=28 ∨ a=29 ∨ a=30 ∨ a=31 by omega) with rfl|rfl|rfl|rfl
          · exact ok28
          · exact ok29
          · exact ok30
          · exact ok31
  ·
    by_cases h48 : a < 48
    ·
      by_cases h40 : a < 40
      ·
        by_cases h36 : a < 36
        ·
          rcases (show a=32 ∨ a=33 ∨ a=34 ∨ a=35 by omega) with rfl|rfl|rfl|rfl
          · exact ok32
          · exact ok33
          · exact ok34
          · exact ok35
        ·
          rcases (show a=36 ∨ a=37 ∨ a=38 ∨ a=39 by omega) with rfl|rfl|rfl|rfl
          · exact ok36
          · exact ok37
          · exact ok38
          · exact ok39
      ·
        by_cases h44 : a < 44
        ·
          rcases (show a=40 ∨ a=41 ∨ a=42 ∨ a=43 by omega) with rfl|rfl|rfl|rfl
          · exact ok40
          · exact ok41
          · exact ok42
          · exact ok43
        ·
          rcases (show a=44 ∨ a=45 ∨ a=46 ∨ a=47 by omega) with rfl|rfl|rfl|rfl
          · exact ok44
          · exact ok45
          · exact ok46
          · exact ok47
    ·
      by_cases h56 : a < 56
      ·
        by_cases h52 : a < 52
        ·
          rcases (show a=48 ∨ a=49 ∨ a=50 ∨ a=51 by omega) with rfl|rfl|rfl|rfl
          · exact ok48
          · exact ok49
          · exact ok50
          · exact ok51
        ·
          rcases (show a=52 ∨ a=53 ∨ a=54 ∨ a=55 by omega) with rfl|rfl|rfl|rfl
          · exact ok52
          · exact ok53
          · exact ok54
          · exact ok55
      ·
        by_cases h60 : a < 60
        ·
          rcases (show a=56 ∨ a=57 ∨ a=58 ∨ a=59 by omega) with rfl|rfl|rfl|rfl
          · exact ok56
          · exact ok57
          · exact ok58
          · exact ok59
        ·
          rcases (show a=60 ∨ a=61 ∨ a=62 ∨ a=63 by omega) with rfl|rfl|rfl|rfl
          · exact ok60
          · exact ok61
          · exact ok62
          · exact ok63
