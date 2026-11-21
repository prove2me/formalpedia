-- Prove2me | solution 1 for NymanBeurling.finite_rational_remainder_energy_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:59:44.502826+00:00
-- url     : https://prove2.me/submissions/130bfc1f-c456-4cca-940d-238f07a6a654

import Mathlib
import Theorems.Thm_NymanBeurling_large_sieve_remainder_tail

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace BagchiNumericalWitness
def entries : List (ℕ × ℤ) := [
  (2, 477963), (3, 317607), (4, 18624), (5, 172645), (6, -124873), (7, 115426),
  (10, -65108), (11, 62086), (13, 49792), (14, -44466), (15, -40926), (17, 35841),
  (19, 30678), (21, -29760), (22, -20736), (23, 22142), (26, -18716), (29, 16028),
  (30, 17387), (31, 14259), (33, -13819), (34, -10256), (35, -16096), (37, 10806),
  (38, -10953), (39, -10559), (41, 9286), (42, 14386), (43, 6676), (46, -7646),
  (47, 5859), (51, -5174), (53, 4542), (55, -4357), (57, -6020), (58, -5731),
  (59, 4067), (61, 4154), (62, -3932), (65, -3388), (66, 6730), (69, -5069),
  (70, 7590), (71, 4245), (77, -2839), (78, 4635), (85, -3392), (87, -4393),
  (93, -4386), (95, -4146), (97, 3457), (103, 4592), (105, 5346), (114, 2893),
  (119, -4292), (123, -2629), (138, 3085), (142, -2094), (145, -1752), (174, 2581),
  (190, 2167), (206, -1996), (210, -3270), (238, 2025)
]

def intR (n : ℕ) : ℤ := 1000000 - (entries.map fun e => e.2 * ((n % e.1 : ℕ) : ℤ)).sum
def tick (m : ℕ) : ℕ := 1000000000000 * (intR m).natAbs^2 / (1000000^2*m*(m+1)) + 1
def ticksum : ℕ → ℕ
  | 0 => 0
  | n+1 => ticksum n + tick (n+1)
def csum : ℤ := 2000000 - (entries.map fun e => e.2 * ((e.1 : ℤ)-1)).sum
def covsum : ℤ := (entries.map fun e =>
  (entries.map fun f => e.2*f.2*((e.1.gcd f.1 : ℤ)^2-1)).sum).sum
def absSum : ℕ := (entries.map fun e => e.2.natAbs*e.1).sum
private def ripple (m : ℕ) : ℤ := 1000000 - ((477963:ℤ) * (((m%2):ℕ):ℤ) + ((317607:ℤ) * (((m%3):ℕ):ℤ) + ((18624:ℤ) * (((m%4):ℕ):ℤ) + ((172645:ℤ) * (((m%5):ℕ):ℤ) + ((-124873:ℤ) * (((m%6):ℕ):ℤ) + ((115426:ℤ) * (((m%7):ℕ):ℤ) + ((-65108:ℤ) * (((m%10):ℕ):ℤ) + ((62086:ℤ) * (((m%11):ℕ):ℤ) + ((49792:ℤ) * (((m%13):ℕ):ℤ) + ((-44466:ℤ) * (((m%14):ℕ):ℤ) + ((-40926:ℤ) * (((m%15):ℕ):ℤ) + ((35841:ℤ) * (((m%17):ℕ):ℤ) + ((30678:ℤ) * (((m%19):ℕ):ℤ) + ((-29760:ℤ) * (((m%21):ℕ):ℤ) + ((-20736:ℤ) * (((m%22):ℕ):ℤ) + ((22142:ℤ) * (((m%23):ℕ):ℤ) + ((-18716:ℤ) * (((m%26):ℕ):ℤ) + ((16028:ℤ) * (((m%29):ℕ):ℤ) + ((17387:ℤ) * (((m%30):ℕ):ℤ) + ((14259:ℤ) * (((m%31):ℕ):ℤ) + ((-13819:ℤ) * (((m%33):ℕ):ℤ) + ((-10256:ℤ) * (((m%34):ℕ):ℤ) + ((-16096:ℤ) * (((m%35):ℕ):ℤ) + ((10806:ℤ) * (((m%37):ℕ):ℤ) + ((-10953:ℤ) * (((m%38):ℕ):ℤ) + ((-10559:ℤ) * (((m%39):ℕ):ℤ) + ((9286:ℤ) * (((m%41):ℕ):ℤ) + ((14386:ℤ) * (((m%42):ℕ):ℤ) + ((6676:ℤ) * (((m%43):ℕ):ℤ) + ((-7646:ℤ) * (((m%46):ℕ):ℤ) + ((5859:ℤ) * (((m%47):ℕ):ℤ) + ((-5174:ℤ) * (((m%51):ℕ):ℤ) + ((4542:ℤ) * (((m%53):ℕ):ℤ) + ((-4357:ℤ) * (((m%55):ℕ):ℤ) + ((-6020:ℤ) * (((m%57):ℕ):ℤ) + ((-5731:ℤ) * (((m%58):ℕ):ℤ) + ((4067:ℤ) * (((m%59):ℕ):ℤ) + ((4154:ℤ) * (((m%61):ℕ):ℤ) + ((-3932:ℤ) * (((m%62):ℕ):ℤ) + ((-3388:ℤ) * (((m%65):ℕ):ℤ) + ((6730:ℤ) * (((m%66):ℕ):ℤ) + ((-5069:ℤ) * (((m%69):ℕ):ℤ) + ((7590:ℤ) * (((m%70):ℕ):ℤ) + ((4245:ℤ) * (((m%71):ℕ):ℤ) + ((-2839:ℤ) * (((m%77):ℕ):ℤ) + ((4635:ℤ) * (((m%78):ℕ):ℤ) + ((-3392:ℤ) * (((m%85):ℕ):ℤ) + ((-4393:ℤ) * (((m%87):ℕ):ℤ) + ((-4386:ℤ) * (((m%93):ℕ):ℤ) + ((-4146:ℤ) * (((m%95):ℕ):ℤ) + ((3457:ℤ) * (((m%97):ℕ):ℤ) + ((4592:ℤ) * (((m%103):ℕ):ℤ) + ((5346:ℤ) * (((m%105):ℕ):ℤ) + ((2893:ℤ) * (((m%114):ℕ):ℤ) + ((-4292:ℤ) * (((m%119):ℕ):ℤ) + ((-2629:ℤ) * (((m%123):ℕ):ℤ) + ((3085:ℤ) * (((m%138):ℕ):ℤ) + ((-2094:ℤ) * (((m%142):ℕ):ℤ) + ((-1752:ℤ) * (((m%145):ℕ):ℤ) + ((2581:ℤ) * (((m%174):ℕ):ℤ) + ((2167:ℤ) * (((m%190):ℕ):ℤ) + ((-1996:ℤ) * (((m%206):ℕ):ℤ) + ((-3270:ℤ) * (((m%210):ℕ):ℤ) + ((2025:ℤ) * (((m%238):ℕ):ℤ) + 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private def fastTick (n : ℕ) : ℕ := 1000000000000*(ripple n).natAbs^2/(1000000^2*n*(n+1))+1
private def spanSum (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => spanSum a n + fastTick (a+n+1)
private theorem congrTick (n : ℕ) : tick n=fastTick n := by
  have he : intR n=ripple n := by simp only [intR,entries,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,ripple]
  unfold tick fastTick;rw [he]
private theorem prefix_span (n : ℕ) : ticksum n = spanSum 0 n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ticksum,spanSum,ih,congrTick,Nat.zero_add]
private theorem span_split (a n k : ℕ) : spanSum a (n+k)=spanSum a n+spanSum (a+n) k := by
  induction k with
  | zero => simp [spanSum]
  | succ k ih =>
    change spanSum a (n+k)+fastTick (a+(n+k)+1) = spanSum a n+(spanSum (a+n) k+fastTick ((a+n)+k+1))
    rw [ih,Nat.add_assoc a n k,Nat.add_assoc (spanSum a n)]
private theorem compose (a n k u v : ℕ) (ha : spanSum a n=u) (hb : spanSum (a+n) k=v) :
    spanSum a (n+k)=u+v := (span_split a n k).trans (congrArg₂ Nat.add ha hb)
private theorem block0 : spanSum 0 512=8340278571 := by decide +kernel
private theorem block512 : spanSum 512 512=493909775 := by decide +kernel
private theorem block1024 : spanSum 1024 512=160108451 := by decide +kernel
private theorem block1536 : spanSum 1536 512=73922770 := by decide +kernel
private theorem block2048 : spanSum 2048 512=37343386 := by decide +kernel
private theorem block2560 : spanSum 2560 512=30225493 := by decide +kernel
private theorem block3072 : spanSum 3072 512=21688768 := by decide +kernel
private theorem block3584 : spanSum 3584 512=15183093 := by decide +kernel
private theorem block4096 : spanSum 4096 512=9075488 := by decide +kernel
private theorem block4608 : spanSum 4608 512=8927227 := by decide +kernel
private theorem block5120 : spanSum 5120 512=7663597 := by decide +kernel
private theorem block5632 : spanSum 5632 512=5578087 := by decide +kernel
private theorem joined512 : spanSum 0 1024=8834188346 := @compose 0 512 512 8340278571 493909775 block0 block512
private theorem joined1024 : spanSum 0 1536=8994296797 := @compose 0 1024 512 8834188346 160108451 joined512 block1024
private theorem joined1536 : spanSum 0 2048=9068219567 := @compose 0 1536 512 8994296797 73922770 joined1024 block1536
private theorem joined2048 : spanSum 0 2560=9105562953 := @compose 0 2048 512 9068219567 37343386 joined1536 block2048
private theorem joined2560 : spanSum 0 3072=9135788446 := @compose 0 2560 512 9105562953 30225493 joined2048 block2560
private theorem joined3072 : spanSum 0 3584=9157477214 := @compose 0 3072 512 9135788446 21688768 joined2560 block3072
private theorem joined3584 : spanSum 0 4096=9172660307 := @compose 0 3584 512 9157477214 15183093 joined3072 block3584
private theorem joined4096 : spanSum 0 4608=9181735795 := @compose 0 4096 512 9172660307 9075488 joined3584 block4096
private theorem joined4608 : spanSum 0 5120=9190663022 := @compose 0 4608 512 9181735795 8927227 joined4096 block4608
private theorem joined5120 : spanSum 0 5632=9198326619 := @compose 0 5120 512 9190663022 7663597 joined4608 block5120
private theorem joined5632 : spanSum 0 6144=9203904706 := @compose 0 5632 512 9198326619 5578087 joined5120 block5632
theorem tick_check : ticksum 6144 ≤ 9203904706 := le_of_eq ((prefix_span _).trans joined5632)
theorem center_check : csum = -5987 := by decide +kernel
theorem cov_check : covsum = 5189638853267 := by decide +kernel
theorem abs_check : absSum = 28821603 := by decide +kernel

end BagchiNumericalWitness

open Finset
namespace BagchiNumericalWitness
private def keys := entries.map Prod.fst
private def nums (d : ℕ) : ℤ := (entries.lookup d).getD 0
private def supportD := keys.toFinset
private theorem hkeys : keys.Nodup := by decide +kernel
private theorem data_agree : keys.map (fun d => (d,nums d))=entries := by decide +kernel
private theorem valid : ∀ d∈supportD, 2≤d ∧ d≤240 ∧ nums d≠0 := by decide +kernel

private theorem list_sum {M : Type*} [AddCommMonoid M] (g : ℕ→ℤ→M) :
    (entries.map fun e => g e.1 e.2).sum=∑ d∈supportD,g d (nums d) := by
  rw [show (∑ d∈supportD,g d (nums d))=(keys.map fun d => g d (nums d)).sum from List.sum_toFinset _ hkeys]
  conv_lhs => rw [←data_agree]
  simp [List.map_map,Function.comp_def]

private def cQ (d : ℕ) : ℚ := (nums d:ℚ)*d/1000000
private noncomputable def cR (d : ℕ) : ℝ := (nums d:ℝ)*d/1000000
private def dMinusTwo (d : ℕ) := d-2
private def ix := supportD.image dMinusTwo
private noncomputable def coeff : ℕ→₀ℚ := Finsupp.onFinset ix (fun k => if k∈ix then cQ (k+2) else 0)
  (by intro k h;by_contra hh;exact h (if_neg hh))
private theorem coeff_mem {k : ℕ} (hk : k∈ix) : coeff k = cQ (k+2) := by simp [coeff,hk]
private theorem coeff_sup : coeff.support = ix := by
  ext k;rw [Finsupp.mem_support_iff]
  by_cases hk : k∈ix
  · rw [coeff_mem hk];simp only [hk,iff_true]
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hk
    have hw : dMinusTwo d+2=d := Nat.sub_add_cancel (valid d hd).1
    rw [hw];unfold cQ;apply div_ne_zero (mul_ne_zero (by exact_mod_cast (valid d hd).2.2) (by exact_mod_cast (show d≠0 by have := (valid d hd).1;omega))) (by norm_num)
  · simp [coeff,hk]
private theorem coeff_sum {M : Type*} [AddCommMonoid M] (g : ℕ→ℚ→M) :
    ∑ k∈coeff.support,g (k+2) (coeff k)=∑ d∈supportD,g d (cQ d) := by
  rw [coeff_sup,ix,sum_image]
  · apply sum_congr rfl;intro d hd
    have hk : dMinusTwo d∈ix := mem_image_of_mem _ hd
    rw [coeff_mem hk,show dMinusTwo d+2=d from Nat.sub_add_cancel (valid d hd).1]
  · intro d hd e he hh
    dsimp [dMinusTwo] at hh;have := (valid d hd).1;have := (valid e he).1;omega

private noncomputable def reser (n : ℕ) : ℝ := 1 - ∑ d∈supportD,cR d*((n%d:ℕ):ℝ)/d
private noncomputable def mc : ℝ := (1-∑ d∈supportD,cR d*((d:ℝ)-1)/(2*d))^2+
  ∑ d∈supportD,∑ e∈supportD,cR d*cR e*((d.gcd e:ℝ)^2-1)/(12*d*e)
private noncomputable def resq (n : ℕ) : ℚ := 1-∑ k∈coeff.support,coeff k*(((n%(k+2):ℕ):ℚ)/(k+2:ℚ))
private theorem resq_cast (n : ℕ) : (resq n:ℝ)=reser n := by
  unfold resq reser
  have h := coeff_sum (fun d v => v*(((n%d:ℕ):ℚ)/d))
  simp only [Nat.cast_add,Nat.cast_ofNat] at h
  rw [h];push_cast;norm_num [cQ,cR,mul_div_assoc]
private theorem reser_int (n : ℕ) : reser n=(intR n:ℝ)/1000000 := by
  have hsum := list_sum (fun d a => a*((n%d:ℕ):ℤ))
  rw [intR,hsum];simp only [Int.cast_sub,Int.cast_ofNat,Int.cast_sum,Int.cast_mul, Int.cast_natCast]
  unfold reser
  rw [sub_div,show (1000000:ℝ)/1000000=1 by norm_num,Finset.sum_div]
  congr 1
  apply sum_congr rfl;intro d hd
  have h : (d:ℝ)≠0 := by exact_mod_cast (show d≠0 by have := (valid d hd).1;omega)
  unfold cR;field_simp
private theorem mean_center :
    1-∑ d∈supportD,cR d*((d:ℝ)-1)/(2*d)=(csum:ℝ)/2000000 := by
  rw [csum,list_sum (fun d a => a*((d:ℤ)-1))];push_cast
  rw [sub_div,show (2000000:ℝ)/2000000=1 by norm_num,Finset.sum_div]
  congr 1
  apply sum_congr rfl;intro d hd
  have h : (d:ℝ)≠0 := by exact_mod_cast (show d≠0 by have := (valid d hd).1;omega)
  unfold cR;field_simp;ring
private theorem covariance :
    ∑ d∈supportD,∑ e∈supportD,cR d*cR e*((d.gcd e:ℝ)^2-1)/(12*d*e)
    =(covsum:ℝ)/12000000000000 := by
  dsimp only [covsum]
  rw [list_sum (fun d a => (entries.map fun f => a*f.2*((d.gcd f.1:ℤ)^2-1)).sum)]
  have hr (d : ℕ) : (entries.map fun f => nums d*f.2*((d.gcd f.1:ℤ)^2-1)).sum =
      ∑ e∈supportD,nums d*nums e*((d.gcd e:ℤ)^2-1) :=
    list_sum (fun e b => nums d*b*((d.gcd e:ℤ)^2-1))
  simp_rw [hr]
  push_cast
  rw [Finset.sum_div];apply sum_congr rfl;intro d hd
  rw [Finset.sum_div];apply sum_congr rfl;intro e he
  have h1 : (d:ℝ)≠0 := by exact_mod_cast (show d≠0 by have := (valid d hd).1;omega)
  have h2 : (e:ℝ)≠0 := by exact_mod_cast (show e≠0 by have := (valid e he).1;omega)
  unfold cR;field_simp;ring
private theorem exact_mean : mc=2594873192887/6000000000000 := by
  rw [mc,mean_center,covariance,center_check,cov_check];norm_num

private noncomputable def costTerm (i : ℕ) := reser (i+1)^2/((i+1:ℝ)*(i+2:ℝ))
private noncomputable def headSum (H : ℕ) := ∑ i∈range H,costTerm i
private theorem term_nonnegative (i : ℕ) : 0 ≤ costTerm i := by dsimp [costTerm];positivity
private theorem abs_nat_real (z : ℤ) : (z.natAbs:ℝ)=|(z:ℝ)| := by
  simpa only [Int.cast_natCast,Int.cast_abs] using congrArg (fun q : ℤ => (q:ℝ)) (Int.natCast_natAbs z)
private theorem tick_bound (i : ℕ) : costTerm i ≤ (tick (i+1):ℝ)/1000000000000 := by
  let m := i+1
  have hpos : 0 < 1000000^2*m*(m+1) := by dsimp [m];positivity
  have hn := (Nat.lt_mul_div_succ (1000000000000*(intR m).natAbs^2) hpos).le
  change 1000000000000*(intR m).natAbs^2 ≤ (1000000^2*m*(m+1))*tick m at hn
  have hr : (1000000000000:ℝ)*((intR m).natAbs:ℝ)^2 ≤
      (1000000^2*(m:ℝ)*(m+1))*(tick m:ℝ) := by exact_mod_cast hn
  rw [abs_nat_real,sq_abs] at hr
  have hm : (0:ℝ) < m := by dsimp [m];positivity
  rw [costTerm,reser_int]
  change _ ≤ (tick m:ℝ)/1000000000000
  rw [show (i+1:ℝ)=(m:ℝ) by dsimp [m];push_cast;rfl,
    show (i+2:ℝ)=(m:ℝ)+1 by dsimp [m];push_cast;ring]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  change ((intR m:ℝ)/1000000)^2*1000000000000 ≤ _
  nlinarith only [hr]
private theorem finite_ticks (n : ℕ) : headSum n ≤ (ticksum n:ℝ)/1000000000000 := by
  induction n with
  | zero => simp [headSum,ticksum]
  | succ n ih =>
    change ∑ i∈range (n+1),costTerm i ≤ (ticksum n+tick (n+1):ℕ)/1000000000000
    rw [sum_range_succ];push_cast
    change (headSum n)+_≤_
    linarith only [ih,tick_bound n]
private theorem head_bound : headSum 6144 ≤ 9203904706/1000000000000 := by
  apply (finite_ticks _).trans
  gcongr
  exact_mod_cast tick_check
private theorem every_prefix (H : ℕ) : headSum H < 994/100000 := by
  by_cases hH : H≤6144
  · have hle : headSum H≤headSum 6144 := sum_le_sum_of_subset_of_nonneg
      (range_mono hH) (fun i _ _ => term_nonnegative i)
    exact hle.trans_lt (head_bound.trans_lt (by norm_num))
  · let j := H-6144
    have h : H=6144+j := by dsimp [j];omega
    have hb := (NymanBeurling.large_sieve_remainder_tail supportD cR 240 (by decide)
      (fun d hd => ⟨(show 0<d by have := (valid d hd).1;omega),(valid d hd).2.1⟩)).2 6144
    have ht : ∑ i∈range j,costTerm (6144+i) ≤ mc*(1/(6144+1:ℝ)+(240:ℝ)^2/((6144+1:ℝ)*(6144+2:ℝ))) := by
      simpa only [mc,costTerm,reser,Nat.cast_add, Nat.cast_ofNat] using hb.1 j
    rw [exact_mean] at ht
    rw [h,headSum,sum_range_add]
    change headSum 6144 + _ < _
    linarith only [head_bound,ht]
private theorem abs_coeffs : (∑ k∈coeff.support,|coeff k|) = 28821603/1000000 := by
  have h := coeff_sum (fun _ v => |v|)
  rw [h]
  have hi := list_sum (fun d (a : ℤ) => a.natAbs*d)
  change absSum = ∑ d∈supportD,(nums d).natAbs*d at hi
  rw [abs_check] at hi
  have hq := congrArg (fun b : ℕ => (b:ℚ)/1000000) hi.symm
  change (∑ d∈supportD,|cQ d|) = (28821603:ℚ)/1000000
  calc
    _ = ((∑ d∈supportD,(nums d).natAbs*d:ℕ):ℚ)/1000000 := by
      push_cast
      rw [sum_div];apply sum_congr rfl;intro d hd
      rw [cQ,abs_div,abs_mul,abs_of_nonneg (by positivity : (0:ℚ)≤d),abs_of_pos (by norm_num : (0:ℚ)<1000000)]
      congr 2
      simpa only [Int.cast_natCast,Int.cast_abs] using congrArg (fun z : ℤ => (z:ℚ)) (Int.natCast_natAbs (nums d)).symm
    _ = _ := by rw [←hi];norm_num
private noncomputable def partQ (H : ℕ) := ∑ i∈range H,resq (i+1)^2/((i+1:ℚ)*(i+2:ℚ))
private theorem cast_part (H : ℕ) : (partQ H:ℝ)=headSum H := by
  simp only [partQ,headSum,costTerm,Rat.cast_sum,Rat.cast_div,Rat.cast_pow,resq_cast,
    Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,Rat.cast_one,Rat.cast_ofNat]
private theorem lower_than_hundred (H : ℕ) : partQ H < 994/100000 := by
  apply (Rat.cast_lt (K:=ℝ)).mp
  rw [cast_part];push_cast;exact every_prefix H

private theorem prefix_nonneg (H : ℕ) : 0 ≤ partQ H :=
  sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (by positivity))

private theorem package (P : ℕ→ℚ) (b : ℚ) (hb : b=28821603/1000000)
    (hu : ∀ n,P n<994/100000) (hn : 0 ≤ P 100000000) :
    (let C : ℚ := P 100000000+(1+b)^2/100000001
     C<1/100 ∧ (∀ H,P H<1/100) ∧ ∀ J L : ℕ,J≤99 →
       ∃ H : ℕ,L≤H ∧ P H≤1/(J+1:ℚ) ∧ C^(J+1)≤(H+1:ℚ)) := by
  subst b
  let C : ℚ := P 100000000+(1+28821603/1000000)^2/100000001
  have hc : C < 1/100 := by dsimp [C];linarith only [hu 100000000]
  have hp : 0 ≤ C := add_nonneg hn (by norm_num)
  have ht (H : ℕ) : P H<1/100 := (hu H).trans (by norm_num)
  refine ⟨hc,ht,?_⟩
  intro J L hJ;refine ⟨L,le_rfl,(ht L).le.trans ?_,?_⟩
  · apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast (show J+1≤100 by omega)
  · exact (pow_le_one₀ hp (hc.le.trans (by norm_num))).trans (by have := (Nat.cast_nonneg L : (0:ℚ)≤L);linarith)

end BagchiNumericalWitness

open BagchiNumericalWitness

theorem solution :
    ∃ c : ℕ →₀ ℚ, c.support.card = 64 ∧ (∀ k ∈ c.support, k+2 ≤ 240) ∧
      (let R := fun n : ℕ => 1 - ∑ k ∈ c.support, c k * ((((n+1) % (k+2) : ℕ) : ℚ) / (k+2 : ℚ))
       let E := fun n : ℕ => (R n)^2 / ((n+1 : ℚ)*(n+2 : ℚ))
       let C := (∑ n ∈ Finset.range 100000000, E n) + (1 + ∑ k ∈ c.support, |c k|)^2/100000001
       C < 1/100 ∧
       (∀ H : ℕ, ∑ n ∈ Finset.range H, E n < 1/100) ∧
       ∀ (J L : ℕ), J ≤ 99 → ∃ H : ℕ, L ≤ H ∧
         (∑ n ∈ Finset.range H, E n) ≤ 1/(J+1 : ℚ) ∧ C^(J+1) ≤ (H+1 : ℚ)) := by
  refine ⟨coeff,?_,?_,?_⟩
  · rw [coeff_sup];decide +kernel
  · intro k hk;rw [coeff_sup] at hk
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hk
    rw [show dMinusTwo d+2=d from Nat.sub_add_cancel (valid d hd).1]
    exact (valid d hd).2.1
  · exact package partQ _ abs_coeffs lower_than_hundred (prefix_nonneg _)
