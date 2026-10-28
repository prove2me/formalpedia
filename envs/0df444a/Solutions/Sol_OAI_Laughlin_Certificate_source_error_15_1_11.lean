-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_15_1_11
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:14:01.579126+00:00
-- url     : https://prove2.me/submissions/cedfbda0-ea40-47ca-ab4a-43f8885b1ca9

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0111Batch15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_15_1_11_0 : RowCompute.yRowIntegralFast 15 1 11 (RowCompute.rows[0]!) =
    (394118557857054113712789839998745941750938651878483904430080000000 : ℤ) := by
  decide +kernel

theorem computeRow_15_1_11_1 : RowCompute.yRowIntegralFast 15 1 11 (RowCompute.rows[1]!) =
    (220511337542759103247808122466784880510034318151823392768000000 : ℤ) := by
  decide +kernel

theorem computeRow_15_1_11_2 : RowCompute.yRowIntegralFast 15 1 11 (RowCompute.rows[2]!) =
    (101554139241819336687998474995884262440244713824179508477952000000 : ℤ) := by
  decide +kernel

theorem computeRow_15_1_11_3 : RowCompute.yRowIntegralFast 15 1 11 (RowCompute.rows[3]!) =
    (44692335261648477957768632835611508196439670694695080558592000000 : ℤ) := by
  decide +kernel

theorem computeRow_15_1_11_4 : RowCompute.yRowIntegralFast 15 1 11 (RowCompute.rows[4]!) =
    (11297428479494088360133057135596852018075961388480015106048000000 : ℤ) := by
  decide +kernel

theorem computeRow_15_1_11_5 : RowCompute.yRowIntegralFast 15 1 11 (RowCompute.rows[5]!) =
    (-41857869627893355296531626737382808590607515478618032570368000000 : ℤ) := by
  decide +kernel

theorem computeRow_15_1_11_6 : RowCompute.yRowIntegralFast 15 1 11 (RowCompute.rows[6]!) =
    (7323815329494751435954814917547646047099371903654060621824000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped BigOperators Matrix

theorem Y_expand (D r s : ℕ) : Y D r s =
    -(yRow D r s (rows[0]!) + (yRow D r s (rows[1]!) +
      (yRow D r s (rows[2]!) + (yRow D r s (rows[3]!) +
        (yRow D r s (rows[4]!) + (yRow D r s (rows[5]!) +
          (yRow D r s (rows[6]!) + 0))))))) / (10^14 : ℚ) := by rfl

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Integral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yEntry_eq_integral (D r s t : ℕ) (e f : ℕ × ℕ × ℤ)
    (ht : t ≤ 16) (hT : e.1 + e.2.1 + (f.1 + f.2.1 - t) ≤ 24) :
    yEntry D r s t e f = (yEntryIntegral D r s t e f : ℚ) / arithmeticScale := by
  rcases e with ⟨p,j,a⟩
  rcases f with ⟨q,l,b⟩
  dsimp at hT
  let T := p+j+(q+l-t)
  let z : ℤ := 1-2*((p : ℤ)+(j : ℤ)+(q+l-t : ℕ))+(p : ℤ)+(q : ℤ)-(t : ℤ)+((r : ℤ)+(s : ℤ))/2
  have hz : 0 ≤ 64+z := by dsimp [z,T]; omega
  have hexp : 65-2*((p : ℤ)+(j : ℤ)+(q+l-t : ℕ))+(p : ℤ)+(q : ℤ)-(t : ℤ)+((r : ℤ)+(s : ℤ))/2 = 64+z := by dsimp [z]; ring
  have hp : (2 : ℚ)^((64+z).toNat) = (2 : ℚ)^64 * (2 : ℚ)^z := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hz, zpow_add₀ (by norm_num)]
    norm_num
  have hTD : T-D ≤ 24 := by dsimp [T]; omega
  have hf : ((T-D).factorial : ℚ) * ((24 : ℕ).descFactorial (24-(T-D)) : ℚ) = (Nat.factorial 24 : ℚ) := by
    have hn := Nat.factorial_mul_descFactorial (n := 24) (k := 24-(T-D)) (by omega)
    rw [Nat.sub_sub_self hTD] at hn
    exact_mod_cast hn
  dsimp [yEntry, yEntryIntegral]
  split_ifs with hd
  · change _ = _ / arithmeticScale
    rw [hexp]
    push_cast
    rw [hp]
    change _ = _ / ((2 : ℚ)^64 * (Nat.factorial 24 : ℚ))
    rw [← hf]
    have hn : ((T-D).factorial : ℚ) ≠ 0 := by positivity
    have hm : ((24 : ℕ).descFactorial (24-(T-D)) : ℚ) ≠ 0 := by
      intro h
      rw [h, mul_zero] at hf
      exact (ne_of_gt (show (0 : ℚ) < (Nat.factorial 24 : ℚ) by positivity)) hf.symm
    change _ = _ / ((2 : ℚ)^64 * (((T-D).factorial : ℚ) * ((24 : ℕ).descFactorial (24-(T-D)) : ℚ)))
    field_simp
    ring
  · simp

private theorem sum_integral {Element : Type*} (xs : List Element) (f : Element → ℤ) (c : ℚ) :
    (xs.map (fun x => (f x : ℚ)/c)).sum = ((xs.map f).sum : ℚ)/c := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, add_div]

theorem yRow_eq_integral (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ))
    (ht : row.1 ≤ 16)
    (hT : ∀ e ∈ row.2.2, ∀ f ∈ row.2.2,
      e.1 + e.2.1 + (f.1 + f.2.1 - row.1) ≤ 24) :
    yRow D r s row = (yRowIntegral D r s row : ℚ) / arithmeticScale := by
  unfold yRow yRowIntegral
  calc
    _ = (row.2.2.map (fun e => (row.2.2.map (fun f =>
        (yEntryIntegral D r s row.1 e f : ℚ)/arithmeticScale)).sum)).sum := by
      congr 1
      apply List.map_congr_left
      intro e he
      congr 1
      apply List.map_congr_left
      intro f hf
      exact yEntry_eq_integral D r s row.1 e f ht (hT e he f hf)
    _ = _ := by simp_rw [sum_integral]

theorem rows_integral_bounds : ∀ row ∈ rows, row.1 ≤ 16 ∧
    ∀ e ∈ row.2.2, ∀ f ∈ row.2.2,
      e.1 + e.2.1 + (f.1 + f.2.1 - row.1) ≤ 24 := by
  decide +kernel

theorem source_yRow_eq_integral (D r s n : ℕ) (hn : n < 7) :
    yRow D r s (rows[n]!) = (yRowIntegral D r s (rows[n]!) : ℚ) / arithmeticScale := by
  have hm : rows[n]! ∈ rows := by
    interval_cases n <;> decide +kernel
  exact yRow_eq_integral D r s _ (rows_integral_bounds _ hm).1 (rows_integral_bounds _ hm).2

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_FastChoose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem U_eq_fast (c z T p : ℕ) : U c z T p = UFast c z T p := by
  simp only [U, UFast, Nat.choose_eq_fast_choose]

theorem V_eq_fast (r D T p j k : ℕ) : V r D T p j k = VFast r D T p j k := by
  simp only [V, VFast, U_eq_fast]

theorem yEntryIntegral_eq_fast (D r s t : ℕ) (e f : ℕ × ℕ × ℤ) :
    yEntryIntegral D r s t e f = yEntryIntegralFast D r s t e f := by
  simp only [yEntryIntegral, yEntryIntegralFast, V_eq_fast]

theorem yRowIntegral_eq_fast (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) :
    yRowIntegral D r s row = yRowIntegralFast D r s row := by
  simp only [yRowIntegral, yRowIntegralFast, yEntryIntegral_eq_fast]

theorem source_yRow_eq_fastIntegral (D r s n : ℕ) (hn : n < 7) :
    yRow D r s (rows[n]!) = (yRowIntegralFast D r s (rows[n]!) : ℚ) / arithmeticScale := by
  rw [source_yRow_eq_integral D r s n hn, yRowIntegral_eq_fast]

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_RowBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_yRow_eq_rowCompute (D r s n : ℕ) (hn : n < 7) :
    yRow D r s (rows[n]!) = (RowCompute.yRowIntegralFast D r s (RowCompute.rows[n]!) : ℚ) / arithmeticScale := by
  exact source_yRow_eq_fastIntegral D r s n hn

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_GramData15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_error_15_1_11_oai : Y 15 1 11 = (-236988935373506936612565573/524288000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 1 11 0 (by decide),
    source_yRow_eq_rowCompute 15 1 11 1 (by decide),
    source_yRow_eq_rowCompute 15 1 11 2 (by decide),
    source_yRow_eq_rowCompute 15 1 11 3 (by decide),
    source_yRow_eq_rowCompute 15 1 11 4 (by decide),
    source_yRow_eq_rowCompute 15 1 11 5 (by decide),
    source_yRow_eq_rowCompute 15 1 11 6 (by decide),
    computeRow_15_1_11_0, computeRow_15_1_11_1, computeRow_15_1_11_2, computeRow_15_1_11_3, computeRow_15_1_11_4, computeRow_15_1_11_5, computeRow_15_1_11_6]
  norm_num [arithmeticScale, Nat.factorial]

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.source_error_15_1_11_oai := @OAI.Laughlin.Certificate.source_error_15_1_11_oai
