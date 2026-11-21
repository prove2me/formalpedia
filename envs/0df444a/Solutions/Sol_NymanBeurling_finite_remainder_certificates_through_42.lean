-- Prove2me | solution 1 for NymanBeurling.finite_remainder_certificates_through_42
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T00:48:44.049686+00:00
-- url     : https://prove2.me/submissions/7da2d2f6-2519-422f-be23-b5fc5b392745

import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option maxRecDepth 100000
set_option maxHeartbeats 9000000

private def coeff (k : ℕ) : ℚ :=
  if k = 0 then 7/8 else if k = 1 then 7/8 else if k = 2 then 1/8 else if k = 3 then 5/8 else if k = 4 then -3/8 else if k = 5 then 4/8 else if k = 8 then -1/8 else if k = 9 then 3/8 else 0

private def C : ℕ →₀ ℚ where
  support := {0,1,2,3,4,5,8,9}
  toFun := coeff
  mem_support_toFun := by
    intro k
    simp only [Finset.mem_insert, Finset.mem_singleton, coeff]
    split_ifs <;> norm_num <;> omega

private def err (m : ℕ) : ℚ :=
  1 - ∑ k ∈ C.support, C k * ((m % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ)

private def r30 (m : ℕ) : ℤ :=
  16170*(m%2:ℕ) + 10780*(m%3:ℕ) + 4620*(m%5:ℕ) - 2310*(m%6:ℕ) - 462*(m%10:ℕ)

private def numerator (m : ℕ) : ℤ :=
  36960 - r30 m - 1155*(m%4:ℕ) - 2640*(m%7:ℕ) - 1260*(m%11:ℕ)

private lemma err_eq (m : ℕ) : err m = (numerator m : ℚ)/36960 := by
  have hm (d : ℕ) : (((m:ℤ) % d : ℤ) : ℚ) = ((m%d:ℕ):ℚ) := by
    rw [← Int.natCast_mod, Int.cast_natCast]
  norm_num [err, C, coeff, Finset.sum_insert, numerator, r30]
  erw [hm 2, hm 3, hm 4, hm 5, hm 6, hm 7, hm 10, hm 11]
  ring

private lemma r30_bounds (m : ℕ) : 0 ≤ r30 m ∧ r30 m ≤ 40502 := by
  have he : r30 m = r30 (m%30) := by
    unfold r30
    repeat rw [Nat.mod_mod_of_dvd _ (by decide)]
  rw [he]
  exact (by decide +kernel : ∀ j : Fin 30, 0 ≤ r30 j ∧ r30 j ≤ 40502) ⟨m%30, Nat.mod_lt _ (by decide)⟩

private lemma square_le (m : ℕ) : (err m)^2 ≤ 1 := by
  have hr := r30_bounds m
  have hi : -36960 ≤ numerator m ∧ numerator m ≤ 36960 := by
    unfold numerator
    have h4 := Nat.mod_lt m (show 0<4 by decide)
    have h7 := Nat.mod_lt m (show 0<7 by decide)
    have h11 := Nat.mod_lt m (show 0<11 by decide)
    omega
  have h1 : (-36960:ℚ) ≤ (numerator m : ℚ) := by exact_mod_cast hi.1
  have h2 : (numerator m : ℚ) ≤ 36960 := by exact_mod_cast hi.2
  rw [err_eq]
  nlinarith [mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h1)]

private def weight (n : ℕ) : ℚ := 1/(((n:ℚ)+1)*((n:ℚ)+2))

private def T (n : ℕ) : ℚ := (err (n+1))^2 / (((n:ℚ)+1)*((n:ℚ)+2))

private lemma T_le (n : ℕ) : T n ≤ weight n := by
  exact div_le_div_of_nonneg_right (square_le (n+1)) (by positivity)

private lemma weight_sum (a b : ℕ) :
    ∑ i ∈ Finset.range b, weight (a+i) = 1/((a:ℚ)+1) - 1/((a:ℚ)+(b:ℚ)+1) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, ih]
    unfold weight
    push_cast
    have h1 : (a:ℚ)+b+1 ≠ 0 := by positivity
    have h2 : (a:ℚ)+b+2 ≠ 0 := by positivity
    have h3 : (a:ℚ)+1 ≠ 0 := by positivity
    field_simp
    ring

private def fast (n : ℕ) : ℚ :=
  ((numerator (n+1):ℚ)/36960)^2 / (((n:ℚ)+1)*((n:ℚ)+2))

private lemma T_eq (n : ℕ) : T n = fast n := by
  simp only [T, fast, err_eq]

private lemma block0 : ∑ i ∈ Finset.range 64, fast (0+i) ≤ (2046953/100000000 : ℚ) := by decide +kernel
private lemma prefix0 : ∑ i ∈ Finset.range 64, fast i ≤ (2046953/100000000 : ℚ) := by
  simpa only [Nat.zero_add] using block0

private lemma block1 : ∑ i ∈ Finset.range 64, fast (64+i) ≤ (108706/100000000 : ℚ) := by decide +kernel
private lemma prefix1 : ∑ i ∈ Finset.range 128, fast i ≤ (2155659/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 64, fast i) + ∑ i ∈ Finset.range 64, fast (64+i) := Finset.sum_range_add fast 64 64
    _ ≤ (2046953/100000000 : ℚ) + 108706/100000000 := add_le_add prefix0 block1
    _ = _ := by norm_num

private lemma block2 : ∑ i ∈ Finset.range 64, fast (128+i) ≤ (37251/100000000 : ℚ) := by decide +kernel
private lemma prefix2 : ∑ i ∈ Finset.range 192, fast i ≤ (2192910/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 128, fast i) + ∑ i ∈ Finset.range 64, fast (128+i) := Finset.sum_range_add fast 128 64
    _ ≤ (2155659/100000000 : ℚ) + 37251/100000000 := add_le_add prefix1 block2
    _ = _ := by norm_num

private lemma block3 : ∑ i ∈ Finset.range 64, fast (192+i) ≤ (18327/100000000 : ℚ) := by decide +kernel
private lemma prefix3 : ∑ i ∈ Finset.range 256, fast i ≤ (2211237/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 192, fast i) + ∑ i ∈ Finset.range 64, fast (192+i) := Finset.sum_range_add fast 192 64
    _ ≤ (2192910/100000000 : ℚ) + 18327/100000000 := add_le_add prefix2 block3
    _ = _ := by norm_num

private lemma block4 : ∑ i ∈ Finset.range 64, fast (256+i) ≤ (11231/100000000 : ℚ) := by decide +kernel
private lemma prefix4 : ∑ i ∈ Finset.range 320, fast i ≤ (2222468/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 256, fast i) + ∑ i ∈ Finset.range 64, fast (256+i) := Finset.sum_range_add fast 256 64
    _ ≤ (2211237/100000000 : ℚ) + 11231/100000000 := add_le_add prefix3 block4
    _ = _ := by norm_num

private lemma block5 : ∑ i ∈ Finset.range 64, fast (320+i) ≤ (7059/100000000 : ℚ) := by decide +kernel
private lemma prefix5 : ∑ i ∈ Finset.range 384, fast i ≤ (2229527/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 320, fast i) + ∑ i ∈ Finset.range 64, fast (320+i) := Finset.sum_range_add fast 320 64
    _ ≤ (2222468/100000000 : ℚ) + 7059/100000000 := add_le_add prefix4 block5
    _ = _ := by norm_num

private lemma block6 : ∑ i ∈ Finset.range 64, fast (384+i) ≤ (5220/100000000 : ℚ) := by decide +kernel
private lemma prefix6 : ∑ i ∈ Finset.range 448, fast i ≤ (2234747/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 384, fast i) + ∑ i ∈ Finset.range 64, fast (384+i) := Finset.sum_range_add fast 384 64
    _ ≤ (2229527/100000000 : ℚ) + 5220/100000000 := add_le_add prefix5 block6
    _ = _ := by norm_num

private lemma block7 : ∑ i ∈ Finset.range 64, fast (448+i) ≤ (3905/100000000 : ℚ) := by decide +kernel
private lemma prefix7 : ∑ i ∈ Finset.range 512, fast i ≤ (2238652/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 448, fast i) + ∑ i ∈ Finset.range 64, fast (448+i) := Finset.sum_range_add fast 448 64
    _ ≤ (2234747/100000000 : ℚ) + 3905/100000000 := add_le_add prefix6 block7
    _ = _ := by norm_num

private lemma block8 : ∑ i ∈ Finset.range 64, fast (512+i) ≤ (3091/100000000 : ℚ) := by decide +kernel
private lemma prefix8 : ∑ i ∈ Finset.range 576, fast i ≤ (2241743/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 512, fast i) + ∑ i ∈ Finset.range 64, fast (512+i) := Finset.sum_range_add fast 512 64
    _ ≤ (2238652/100000000 : ℚ) + 3091/100000000 := add_le_add prefix7 block8
    _ = _ := by norm_num

private lemma block9 : ∑ i ∈ Finset.range 64, fast (576+i) ≤ (2357/100000000 : ℚ) := by decide +kernel
private lemma prefix9 : ∑ i ∈ Finset.range 640, fast i ≤ (2244100/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 576, fast i) + ∑ i ∈ Finset.range 64, fast (576+i) := Finset.sum_range_add fast 576 64
    _ ≤ (2241743/100000000 : ℚ) + 2357/100000000 := add_le_add prefix8 block9
    _ = _ := by norm_num

private lemma block10 : ∑ i ∈ Finset.range 64, fast (640+i) ≤ (2067/100000000 : ℚ) := by decide +kernel
private lemma prefix10 : ∑ i ∈ Finset.range 704, fast i ≤ (2246167/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 640, fast i) + ∑ i ∈ Finset.range 64, fast (640+i) := Finset.sum_range_add fast 640 64
    _ ≤ (2244100/100000000 : ℚ) + 2067/100000000 := add_le_add prefix9 block10
    _ = _ := by norm_num

private lemma block11 : ∑ i ∈ Finset.range 64, fast (704+i) ≤ (1558/100000000 : ℚ) := by decide +kernel
private lemma prefix11 : ∑ i ∈ Finset.range 768, fast i ≤ (2247725/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 704, fast i) + ∑ i ∈ Finset.range 64, fast (704+i) := Finset.sum_range_add fast 704 64
    _ ≤ (2246167/100000000 : ℚ) + 1558/100000000 := add_le_add prefix10 block11
    _ = _ := by norm_num

private lemma block12 : ∑ i ∈ Finset.range 64, fast (768+i) ≤ (1509/100000000 : ℚ) := by decide +kernel
private lemma prefix12 : ∑ i ∈ Finset.range 832, fast i ≤ (2249234/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 768, fast i) + ∑ i ∈ Finset.range 64, fast (768+i) := Finset.sum_range_add fast 768 64
    _ ≤ (2247725/100000000 : ℚ) + 1509/100000000 := add_le_add prefix11 block12
    _ = _ := by norm_num

private lemma block13 : ∑ i ∈ Finset.range 64, fast (832+i) ≤ (1156/100000000 : ℚ) := by decide +kernel
private lemma prefix13 : ∑ i ∈ Finset.range 896, fast i ≤ (2250390/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 832, fast i) + ∑ i ∈ Finset.range 64, fast (832+i) := Finset.sum_range_add fast 832 64
    _ ≤ (2249234/100000000 : ℚ) + 1156/100000000 := add_le_add prefix12 block13
    _ = _ := by norm_num

private lemma block14 : ∑ i ∈ Finset.range 64, fast (896+i) ≤ (1117/100000000 : ℚ) := by decide +kernel
private lemma prefix14 : ∑ i ∈ Finset.range 960, fast i ≤ (2251507/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 896, fast i) + ∑ i ∈ Finset.range 64, fast (896+i) := Finset.sum_range_add fast 896 64
    _ ≤ (2250390/100000000 : ℚ) + 1117/100000000 := add_le_add prefix13 block14
    _ = _ := by norm_num

private lemma block15 : ∑ i ∈ Finset.range 64, fast (960+i) ≤ (853/100000000 : ℚ) := by decide +kernel
private lemma prefix15 : ∑ i ∈ Finset.range 1024, fast i ≤ (2252360/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 960, fast i) + ∑ i ∈ Finset.range 64, fast (960+i) := Finset.sum_range_add fast 960 64
    _ ≤ (2251507/100000000 : ℚ) + 853/100000000 := add_le_add prefix14 block15
    _ = _ := by norm_num

private lemma block16 : ∑ i ∈ Finset.range 64, fast (1024+i) ≤ (818/100000000 : ℚ) := by decide +kernel
private lemma prefix16 : ∑ i ∈ Finset.range 1088, fast i ≤ (2253178/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 1024, fast i) + ∑ i ∈ Finset.range 64, fast (1024+i) := Finset.sum_range_add fast 1024 64
    _ ≤ (2252360/100000000 : ℚ) + 818/100000000 := add_le_add prefix15 block16
    _ = _ := by norm_num

private lemma block17 : ∑ i ∈ Finset.range 64, fast (1088+i) ≤ (670/100000000 : ℚ) := by decide +kernel
private lemma prefix17 : ∑ i ∈ Finset.range 1152, fast i ≤ (2253848/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 1088, fast i) + ∑ i ∈ Finset.range 64, fast (1088+i) := Finset.sum_range_add fast 1088 64
    _ ≤ (2253178/100000000 : ℚ) + 670/100000000 := add_le_add prefix16 block17
    _ = _ := by norm_num

private lemma block18 : ∑ i ∈ Finset.range 64, fast (1152+i) ≤ (692/100000000 : ℚ) := by decide +kernel
private lemma prefix18 : ∑ i ∈ Finset.range 1216, fast i ≤ (2254540/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 1152, fast i) + ∑ i ∈ Finset.range 64, fast (1152+i) := Finset.sum_range_add fast 1152 64
    _ ≤ (2253848/100000000 : ℚ) + 692/100000000 := add_le_add prefix17 block18
    _ = _ := by norm_num

private lemma block19 : ∑ i ∈ Finset.range 64, fast (1216+i) ≤ (602/100000000 : ℚ) := by decide +kernel
private lemma prefix19 : ∑ i ∈ Finset.range 1280, fast i ≤ (2255142/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 1216, fast i) + ∑ i ∈ Finset.range 64, fast (1216+i) := Finset.sum_range_add fast 1216 64
    _ ≤ (2254540/100000000 : ℚ) + 602/100000000 := add_le_add prefix18 block19
    _ = _ := by norm_num

private lemma block20 : ∑ i ∈ Finset.range 64, fast (1280+i) ≤ (522/100000000 : ℚ) := by decide +kernel
private lemma prefix20 : ∑ i ∈ Finset.range 1344, fast i ≤ (2255664/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 1280, fast i) + ∑ i ∈ Finset.range 64, fast (1280+i) := Finset.sum_range_add fast 1280 64
    _ ≤ (2255142/100000000 : ℚ) + 522/100000000 := add_le_add prefix19 block20
    _ = _ := by norm_num

private lemma block21 : ∑ i ∈ Finset.range 64, fast (1344+i) ≤ (475/100000000 : ℚ) := by decide +kernel
private lemma prefix21 : ∑ i ∈ Finset.range 1408, fast i ≤ (2256139/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 1344, fast i) + ∑ i ∈ Finset.range 64, fast (1344+i) := Finset.sum_range_add fast 1344 64
    _ ≤ (2255664/100000000 : ℚ) + 475/100000000 := add_le_add prefix20 block21
    _ = _ := by norm_num

private lemma block22 : ∑ i ∈ Finset.range 64, fast (1408+i) ≤ (431/100000000 : ℚ) := by decide +kernel
private lemma prefix22 : ∑ i ∈ Finset.range 1472, fast i ≤ (2256570/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 1408, fast i) + ∑ i ∈ Finset.range 64, fast (1408+i) := Finset.sum_range_add fast 1408 64
    _ ≤ (2256139/100000000 : ℚ) + 431/100000000 := add_le_add prefix21 block22
    _ = _ := by norm_num

private lemma block23 : ∑ i ∈ Finset.range 64, fast (1472+i) ≤ (378/100000000 : ℚ) := by decide +kernel
private lemma prefix23 : ∑ i ∈ Finset.range 1536, fast i ≤ (2256948/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 1472, fast i) + ∑ i ∈ Finset.range 64, fast (1472+i) := Finset.sum_range_add fast 1472 64
    _ ≤ (2256570/100000000 : ℚ) + 378/100000000 := add_le_add prefix22 block23
    _ = _ := by norm_num

private lemma block24 : ∑ i ∈ Finset.range 64, fast (1536+i) ≤ (387/100000000 : ℚ) := by decide +kernel
private lemma prefix24 : ∑ i ∈ Finset.range 1600, fast i ≤ (2257335/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 1536, fast i) + ∑ i ∈ Finset.range 64, fast (1536+i) := Finset.sum_range_add fast 1536 64
    _ ≤ (2256948/100000000 : ℚ) + 387/100000000 := add_le_add prefix23 block24
    _ = _ := by norm_num

private lemma block25 : ∑ i ∈ Finset.range 64, fast (1600+i) ≤ (343/100000000 : ℚ) := by decide +kernel
private lemma prefix25 : ∑ i ∈ Finset.range 1664, fast i ≤ (2257678/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 1600, fast i) + ∑ i ∈ Finset.range 64, fast (1600+i) := Finset.sum_range_add fast 1600 64
    _ ≤ (2257335/100000000 : ℚ) + 343/100000000 := add_le_add prefix24 block25
    _ = _ := by norm_num

private lemma block26 : ∑ i ∈ Finset.range 64, fast (1664+i) ≤ (317/100000000 : ℚ) := by decide +kernel
private lemma prefix26 : ∑ i ∈ Finset.range 1728, fast i ≤ (2257995/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 1664, fast i) + ∑ i ∈ Finset.range 64, fast (1664+i) := Finset.sum_range_add fast 1664 64
    _ ≤ (2257678/100000000 : ℚ) + 317/100000000 := add_le_add prefix25 block26
    _ = _ := by norm_num

private lemma block27 : ∑ i ∈ Finset.range 64, fast (1728+i) ≤ (299/100000000 : ℚ) := by decide +kernel
private lemma prefix27 : ∑ i ∈ Finset.range 1792, fast i ≤ (2258294/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 1728, fast i) + ∑ i ∈ Finset.range 64, fast (1728+i) := Finset.sum_range_add fast 1728 64
    _ ≤ (2257995/100000000 : ℚ) + 299/100000000 := add_le_add prefix26 block27
    _ = _ := by norm_num

private lemma block28 : ∑ i ∈ Finset.range 64, fast (1792+i) ≤ (262/100000000 : ℚ) := by decide +kernel
private lemma prefix28 : ∑ i ∈ Finset.range 1856, fast i ≤ (2258556/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 1792, fast i) + ∑ i ∈ Finset.range 64, fast (1792+i) := Finset.sum_range_add fast 1792 64
    _ ≤ (2258294/100000000 : ℚ) + 262/100000000 := add_le_add prefix27 block28
    _ = _ := by norm_num

private lemma block29 : ∑ i ∈ Finset.range 64, fast (1856+i) ≤ (256/100000000 : ℚ) := by decide +kernel
private lemma prefix29 : ∑ i ∈ Finset.range 1920, fast i ≤ (2258812/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 1856, fast i) + ∑ i ∈ Finset.range 64, fast (1856+i) := Finset.sum_range_add fast 1856 64
    _ ≤ (2258556/100000000 : ℚ) + 256/100000000 := add_le_add prefix28 block29
    _ = _ := by norm_num

private lemma block30 : ∑ i ∈ Finset.range 64, fast (1920+i) ≤ (231/100000000 : ℚ) := by decide +kernel
private lemma prefix30 : ∑ i ∈ Finset.range 1984, fast i ≤ (2259043/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 1920, fast i) + ∑ i ∈ Finset.range 64, fast (1920+i) := Finset.sum_range_add fast 1920 64
    _ ≤ (2258812/100000000 : ℚ) + 231/100000000 := add_le_add prefix29 block30
    _ = _ := by norm_num

private lemma block31 : ∑ i ∈ Finset.range 64, fast (1984+i) ≤ (233/100000000 : ℚ) := by decide +kernel
private lemma prefix31 : ∑ i ∈ Finset.range 2048, fast i ≤ (2259276/100000000 : ℚ) := by
  calc
    _ = (∑ i ∈ Finset.range 1984, fast i) + ∑ i ∈ Finset.range 64, fast (1984+i) := Finset.sum_range_add fast 1984 64
    _ ≤ (2259043/100000000 : ℚ) + 233/100000000 := add_le_add prefix30 block31
    _ = _ := by norm_num

private lemma numerical :
    (∑ n ∈ Finset.range 262143, T n) + (1+∑ k ∈ C.support, |C k|)^2/(262143+1) < (1/43:ℚ) := by
  have hp : ∑ n ∈ Finset.range 2048, T n ≤ (2259276/100000000:ℚ) := by
    simpa only [T_eq] using prefix31
  have htail : ∑ i ∈ Finset.range 260095, T (2048+i) ≤ (1/(2049:ℚ) - 1/262144) := by
    calc
      _ ≤ ∑ i ∈ Finset.range 260095, weight (2048+i) := Finset.sum_le_sum (fun i _ => T_le _)
      _ = _ := (weight_sum 2048 260095).trans (by norm_num)
  have hmass : (1 + ∑ k ∈ C.support, |C k|)^2 = (1521/64:ℚ) := by decide +kernel
  rw [hmass, show 262143 = 2048 + 260095 by rfl, Finset.sum_range_add]
  exact lt_of_le_of_lt (add_le_add (add_le_add hp htail) (le_refl _)) (by norm_num)

theorem solution (J : ℕ) (hJ : J ≤ 42) :
    ∃ (c : ℕ →₀ ℚ) (H : ℕ), ((∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
      (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) : ℚ) < 1/(J+1 : ℚ) := by
  refine ⟨C, 262143, lt_of_lt_of_le numerical ?_⟩
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast (by omega : J + 1 ≤ 43)
