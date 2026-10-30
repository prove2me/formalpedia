-- Prove2me | solution 1 for OAI.SnakyCertificate.certificate_correct
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T00:04:09.351832+00:00
-- url     : https://prove2.me/submissions/6bef760a-a84c-48d5-a272-264ac19f4082

import Mathlib
import Definitions.Def_SnakyCertificate
import Definitions.Def_OAIQ114S000
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_equation_608
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_equation_609
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_equation_610
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_equation_611
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_equation_612
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_equation_613
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_equation_614
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_equation_615
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_equations_range_0_144
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_equations_range_144_304
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_equations_range_304_464
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_equations_range_464_544
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_equations_range_544_576
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_equations_range_576
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_equations_range_592
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_omits_557
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_omits_595
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_omits_603
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_omits_615
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_summary_557
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_summary_595
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_summary_603
import Theorems.Thm_OAI_SnakyCertificate_Check_cache_summary_615

section
-- module Solutions.OAIQ114_SC.Compat
attribute [-instance] _root_.OAI.SnakyCertificate.digitModulus_neZero _root_.OAI.SnakyCertificate.rotationModulus_neZero
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_TableList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate

theorem table_toList : table.toList = tableList := by
  simp only [table, Array.toList_append]
  rfl

theorem table_getElem?_eq (k : ℕ) : table[k]? = tableList[k]? := by
  rw [← Array.getElem?_toList, table_toList]

theorem merge_ranges {P : ℕ → Prop} {a b c : ℕ}
    (left : ∀ i, a ≤ i → i < b → P i)
    (right : ∀ i, b ≤ i → i < c → P i) :
    ∀ i, a ≤ i → i < c → P i := by
  intro i hlo hhi
  by_cases h : i < b
  · exact left i hlo h
  · exact right i (by omega) hhi

theorem fin_block_range {P : ℕ → Prop} {a n : ℕ}
    (h : ∀ j : Fin n, P (a + j.val)) : ∀ i, a ≤ i → i < a + n → P i := by
  intro i hlo hhi
  have ht := h ⟨i - a, by omega⟩
  simpa only [Nat.add_sub_of_le hlo] using ht

end SnakyCertificate

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Heights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem cache_height_block_0 : ∀ j : Fin 16, (cached (0 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_0 : ∀ i, 0 ≤ i → i < 16 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 0) (n := 16) cache_height_block_0

theorem cache_height_block_16 : ∀ j : Fin 16, (cached (16 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_16 : ∀ i, 16 ≤ i → i < 32 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 16) (n := 16) cache_height_block_16

theorem cache_height_block_32 : ∀ j : Fin 16, (cached (32 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_32 : ∀ i, 32 ≤ i → i < 48 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 32) (n := 16) cache_height_block_32

theorem cache_height_block_48 : ∀ j : Fin 16, (cached (48 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_48 : ∀ i, 48 ≤ i → i < 64 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 48) (n := 16) cache_height_block_48

theorem cache_height_block_64 : ∀ j : Fin 16, (cached (64 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_64 : ∀ i, 64 ≤ i → i < 80 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 64) (n := 16) cache_height_block_64

theorem cache_height_block_80 : ∀ j : Fin 16, (cached (80 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_80 : ∀ i, 80 ≤ i → i < 96 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 80) (n := 16) cache_height_block_80

theorem cache_height_block_96 : ∀ j : Fin 16, (cached (96 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_96 : ∀ i, 96 ≤ i → i < 112 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 96) (n := 16) cache_height_block_96

theorem cache_height_block_112 : ∀ j : Fin 16, (cached (112 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_112 : ∀ i, 112 ≤ i → i < 128 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 112) (n := 16) cache_height_block_112

theorem cache_height_block_128 : ∀ j : Fin 16, (cached (128 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_128 : ∀ i, 128 ≤ i → i < 144 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 128) (n := 16) cache_height_block_128

theorem cache_height_block_144 : ∀ j : Fin 16, (cached (144 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_144 : ∀ i, 144 ≤ i → i < 160 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 144) (n := 16) cache_height_block_144

theorem cache_height_block_160 : ∀ j : Fin 16, (cached (160 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_160 : ∀ i, 160 ≤ i → i < 176 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 160) (n := 16) cache_height_block_160

theorem cache_height_block_176 : ∀ j : Fin 16, (cached (176 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_176 : ∀ i, 176 ≤ i → i < 192 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 176) (n := 16) cache_height_block_176

theorem cache_height_block_192 : ∀ j : Fin 16, (cached (192 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_192 : ∀ i, 192 ≤ i → i < 208 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 192) (n := 16) cache_height_block_192

theorem cache_height_block_208 : ∀ j : Fin 16, (cached (208 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_208 : ∀ i, 208 ≤ i → i < 224 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 208) (n := 16) cache_height_block_208

theorem cache_height_block_224 : ∀ j : Fin 16, (cached (224 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_224 : ∀ i, 224 ≤ i → i < 240 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 224) (n := 16) cache_height_block_224

theorem cache_height_block_240 : ∀ j : Fin 16, (cached (240 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_240 : ∀ i, 240 ≤ i → i < 256 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 240) (n := 16) cache_height_block_240

theorem cache_height_block_256 : ∀ j : Fin 16, (cached (256 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_256 : ∀ i, 256 ≤ i → i < 272 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 256) (n := 16) cache_height_block_256

theorem cache_height_block_272 : ∀ j : Fin 16, (cached (272 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_272 : ∀ i, 272 ≤ i → i < 288 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 272) (n := 16) cache_height_block_272

theorem cache_height_block_288 : ∀ j : Fin 16, (cached (288 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_288 : ∀ i, 288 ≤ i → i < 304 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 288) (n := 16) cache_height_block_288

theorem cache_height_block_304 : ∀ j : Fin 16, (cached (304 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_304 : ∀ i, 304 ≤ i → i < 320 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 304) (n := 16) cache_height_block_304

theorem cache_height_block_320 : ∀ j : Fin 16, (cached (320 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_320 : ∀ i, 320 ≤ i → i < 336 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 320) (n := 16) cache_height_block_320

theorem cache_height_block_336 : ∀ j : Fin 16, (cached (336 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_336 : ∀ i, 336 ≤ i → i < 352 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 336) (n := 16) cache_height_block_336

theorem cache_height_block_352 : ∀ j : Fin 16, (cached (352 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_352 : ∀ i, 352 ≤ i → i < 368 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 352) (n := 16) cache_height_block_352

theorem cache_height_block_368 : ∀ j : Fin 16, (cached (368 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_368 : ∀ i, 368 ≤ i → i < 384 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 368) (n := 16) cache_height_block_368

theorem cache_height_block_384 : ∀ j : Fin 16, (cached (384 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_384 : ∀ i, 384 ≤ i → i < 400 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 384) (n := 16) cache_height_block_384

theorem cache_height_block_400 : ∀ j : Fin 16, (cached (400 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_400 : ∀ i, 400 ≤ i → i < 416 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 400) (n := 16) cache_height_block_400

theorem cache_height_block_416 : ∀ j : Fin 16, (cached (416 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_416 : ∀ i, 416 ≤ i → i < 432 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 416) (n := 16) cache_height_block_416

theorem cache_height_block_432 : ∀ j : Fin 16, (cached (432 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_432 : ∀ i, 432 ≤ i → i < 448 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 432) (n := 16) cache_height_block_432

theorem cache_height_block_448 : ∀ j : Fin 16, (cached (448 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_448 : ∀ i, 448 ≤ i → i < 464 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 448) (n := 16) cache_height_block_448

theorem cache_height_block_464 : ∀ j : Fin 16, (cached (464 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_464 : ∀ i, 464 ≤ i → i < 480 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 464) (n := 16) cache_height_block_464

theorem cache_height_block_480 : ∀ j : Fin 16, (cached (480 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_480 : ∀ i, 480 ≤ i → i < 496 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 480) (n := 16) cache_height_block_480

theorem cache_height_block_496 : ∀ j : Fin 16, (cached (496 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_496 : ∀ i, 496 ≤ i → i < 512 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 496) (n := 16) cache_height_block_496

theorem cache_height_block_512 : ∀ j : Fin 16, (cached (512 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_512 : ∀ i, 512 ≤ i → i < 528 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 512) (n := 16) cache_height_block_512

theorem cache_height_block_528 : ∀ j : Fin 16, (cached (528 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_528 : ∀ i, 528 ≤ i → i < 544 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 528) (n := 16) cache_height_block_528

theorem cache_height_block_544 : ∀ j : Fin 16, (cached (544 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_544 : ∀ i, 544 ≤ i → i < 560 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 544) (n := 16) cache_height_block_544

theorem cache_height_block_560 : ∀ j : Fin 16, (cached (560 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_560 : ∀ i, 560 ≤ i → i < 576 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 560) (n := 16) cache_height_block_560

theorem cache_height_block_576 : ∀ j : Fin 16, (cached (576 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_576 : ∀ i, 576 ≤ i → i < 592 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 576) (n := 16) cache_height_block_576

theorem cache_height_block_592 : ∀ j : Fin 16, (cached (592 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_592 : ∀ i, 592 ≤ i → i < 608 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 592) (n := 16) cache_height_block_592

theorem cache_height_block_608 : ∀ j : Fin 8, (cached (608 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_608 : ∀ i, 608 ≤ i → i < 616 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 608) (n := 8) cache_height_block_608

theorem cache_height_range_0_32 : ∀ i, 0 ≤ i → i < 32 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_0 cache_height_range_16

theorem cache_height_range_32_64 : ∀ i, 32 ≤ i → i < 64 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_32 cache_height_range_48

theorem cache_height_range_0_64 : ∀ i, 0 ≤ i → i < 64 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_0_32 cache_height_range_32_64

theorem cache_height_range_64_96 : ∀ i, 64 ≤ i → i < 96 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_64 cache_height_range_80

theorem cache_height_range_112_144 : ∀ i, 112 ≤ i → i < 144 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_112 cache_height_range_128

theorem cache_height_range_96_144 : ∀ i, 96 ≤ i → i < 144 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_96 cache_height_range_112_144

theorem cache_height_range_64_144 : ∀ i, 64 ≤ i → i < 144 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_64_96 cache_height_range_96_144

theorem cache_height_range_0_144 : ∀ i, 0 ≤ i → i < 144 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_0_64 cache_height_range_64_144

theorem cache_height_range_144_176 : ∀ i, 144 ≤ i → i < 176 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_144 cache_height_range_160

theorem cache_height_range_192_224 : ∀ i, 192 ≤ i → i < 224 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_192 cache_height_range_208

theorem cache_height_range_176_224 : ∀ i, 176 ≤ i → i < 224 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_176 cache_height_range_192_224

theorem cache_height_range_144_224 : ∀ i, 144 ≤ i → i < 224 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_144_176 cache_height_range_176_224

theorem cache_height_range_224_256 : ∀ i, 224 ≤ i → i < 256 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_224 cache_height_range_240

theorem cache_height_range_272_304 : ∀ i, 272 ≤ i → i < 304 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_272 cache_height_range_288

theorem cache_height_range_256_304 : ∀ i, 256 ≤ i → i < 304 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_256 cache_height_range_272_304

theorem cache_height_range_224_304 : ∀ i, 224 ≤ i → i < 304 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_224_256 cache_height_range_256_304

theorem cache_height_range_144_304 : ∀ i, 144 ≤ i → i < 304 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_144_224 cache_height_range_224_304

theorem cache_height_range_0_304 : ∀ i, 0 ≤ i → i < 304 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_0_144 cache_height_range_144_304

theorem cache_height_range_304_336 : ∀ i, 304 ≤ i → i < 336 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_304 cache_height_range_320

theorem cache_height_range_352_384 : ∀ i, 352 ≤ i → i < 384 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_352 cache_height_range_368

theorem cache_height_range_336_384 : ∀ i, 336 ≤ i → i < 384 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_336 cache_height_range_352_384

theorem cache_height_range_304_384 : ∀ i, 304 ≤ i → i < 384 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_304_336 cache_height_range_336_384

theorem cache_height_range_384_416 : ∀ i, 384 ≤ i → i < 416 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_384 cache_height_range_400

theorem cache_height_range_432_464 : ∀ i, 432 ≤ i → i < 464 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_432 cache_height_range_448

theorem cache_height_range_416_464 : ∀ i, 416 ≤ i → i < 464 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_416 cache_height_range_432_464

theorem cache_height_range_384_464 : ∀ i, 384 ≤ i → i < 464 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_384_416 cache_height_range_416_464

theorem cache_height_range_304_464 : ∀ i, 304 ≤ i → i < 464 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_304_384 cache_height_range_384_464

theorem cache_height_range_464_496 : ∀ i, 464 ≤ i → i < 496 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_464 cache_height_range_480

theorem cache_height_range_512_544 : ∀ i, 512 ≤ i → i < 544 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_512 cache_height_range_528

theorem cache_height_range_496_544 : ∀ i, 496 ≤ i → i < 544 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_496 cache_height_range_512_544

theorem cache_height_range_464_544 : ∀ i, 464 ≤ i → i < 544 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_464_496 cache_height_range_496_544

theorem cache_height_range_544_576 : ∀ i, 544 ≤ i → i < 576 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_544 cache_height_range_560

theorem cache_height_range_592_616 : ∀ i, 592 ≤ i → i < 616 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_592 cache_height_range_608

theorem cache_height_range_576_616 : ∀ i, 576 ≤ i → i < 616 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_576 cache_height_range_592_616

theorem cache_height_range_544_616 : ∀ i, 544 ≤ i → i < 616 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_544_576 cache_height_range_576_616

theorem cache_height_range_464_616 : ∀ i, 464 ≤ i → i < 616 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_464_544 cache_height_range_544_616

theorem cache_height_range_304_616 : ∀ i, 304 ≤ i → i < 616 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_304_464 cache_height_range_464_616

theorem cache_height_range_0_616 : ∀ i, 0 ≤ i → i < 616 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_0_304 cache_height_range_304_616

theorem cache_heights (i : ℕ) (hi : i < 616) : (cached i).height ≤ 34 :=
  cache_height_range_0_616 i (Nat.zero_le _) hi

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Invariants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate

theorem unionA_subset_unionH (ds : List RowData)
    (h : ∀ d ∈ ds, d.A ⊆ d.H) : unionA ds ⊆ unionH ds := by
  induction ds with
  | nil => simp [unionA, unionH]
  | cons d ds ih =>
    change d.A ∪ unionA ds ⊆ d.H ∪ unionH ds
    exact Finset.union_subset_union (h d (by simp))
      (ih (fun e he => h e (by simp only [List.mem_cons]; exact Or.inr he)))

theorem fold_inter_subset (ss : List (Finset Cell)) (s : Finset Cell) :
    ss.foldr (· ∩ ·) s ⊆ s := by
  induction ss with
  | nil => exact Finset.Subset.refl s
  | cons t ts ih => exact Finset.inter_subset_right.trans ih

theorem commonH_subset_unionH (ds : List RowData) : commonH ds ⊆ unionH ds := by
  cases ds with
  | nil => simp [commonH, unionH]
  | cons d ds =>
    change (ds.map RowData.H).foldr (· ∩ ·) d.H ⊆ d.H ∪ unionH ds
    exact (fold_inter_subset _ _).trans Finset.subset_union_left

theorem forkRow_subset (ds : List RowData) (h : ∀ d ∈ ds, d.A ⊆ d.H) :
    (forkRow ds).A ⊆ (forkRow ds).H := by
  intro p hp
  have hp' : p ∈ unionA ds ∪ commonH ds := Finset.mem_of_mem_erase hp
  exact Finset.mem_insert_of_mem
    ((Finset.union_subset (unionA_subset_unionH ds h) (commonH_subset_unionH ds)) hp')

theorem forkRow_RowSubset (ds : List RowData) (h : ∀ d ∈ ds, RowSubset d) :
    RowSubset (forkRow ds) := forkRow_subset ds h

theorem rowAt_RowSubset (i : ℕ) : RowSubset (rowAt i) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    rw [rowAt]
    split
    · exact Finset.erase_subset _ _
    · refine forkRow_RowSubset
        ((entryAt i).terms.map fun t =>
          placeRow t (if hc : t.child < i then rowAt t.child else emptyRow)) ?_
      intro d hd
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hd
      change (placeRow t (if hc : t.child < i then rowAt t.child else emptyRow)).A ⊆
        (placeRow t (if hc : t.child < i then rowAt t.child else emptyRow)).H
      exact Finset.image_subset_image (by
        split
        · rename_i hc
          exact ih t.child hc
        · exact Finset.Subset.refl ∅)

theorem rowAt_subset (i : ℕ) : (rowAt i).A ⊆ (rowAt i).H := rowAt_RowSubset i

theorem baseRow_origin (i : Fin 6) :
    origin ∈ (baseRow i).H ∧ origin ∉ (baseRow i).A := by
  fin_cases i <;> decide

theorem rowAt_origin (i : ℕ) : origin ∈ (rowAt i).H ∧ origin ∉ (rowAt i).A := by
  rw [rowAt]
  split
  · exact baseRow_origin _
  · simp [forkRow]

theorem rowAt_unique (f : ℕ → RowData) (bound : ℕ)
    (backward : ∀ i, 6 ≤ i → i < bound →
      ∀ t ∈ (entryAt i).terms, t.child < i)
    (equations : ∀ i, i < bound →
      if h : i < 6 then baseRow ⟨i, h⟩ = f i else
        forkRow ((entryAt i).terms.map fun t => placeRow t (f t.child)) = f i) :
    ∀ i, i < bound → rowAt i = f i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    rw [rowAt]
    by_cases hb : i < 6
    · simpa only [dite_eq_left hb] using equations i hi
    · rw [dite_eq_right hb]
      have he := equations i hi
      rw [dite_eq_right hb] at he
      rw [← he]
      apply congrArg forkRow
      apply List.map_congr_left
      intro t ht
      have hc := backward i (by omega) hi t ht
      rw [dite_eq_left hc, ih t.child hc (hc.trans hi)]

end SnakyCertificate

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Reconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem cache_equations_range_608 : ∀ i, 608 ≤ i → i < 616 → CacheEquation i := by
  intro i hlo hhi
  interval_cases i
  · exact cache_equation_608
  · exact cache_equation_609
  · exact cache_equation_610
  · exact cache_equation_611
  · exact cache_equation_612
  · exact cache_equation_613
  · exact cache_equation_614
  · exact cache_equation_615

theorem cache_equations_range_0_304 : ∀ i, 0 ≤ i → i < 304 → CacheEquation i :=
  merge_ranges cache_equations_range_0_144 cache_equations_range_144_304

theorem cache_equations_range_592_616 : ∀ i, 592 ≤ i → i < 616 → CacheEquation i :=
  merge_ranges cache_equations_range_592 cache_equations_range_608

theorem cache_equations_range_576_616 : ∀ i, 576 ≤ i → i < 616 → CacheEquation i :=
  merge_ranges cache_equations_range_576 cache_equations_range_592_616

theorem cache_equations_range_544_616 : ∀ i, 544 ≤ i → i < 616 → CacheEquation i :=
  merge_ranges cache_equations_range_544_576 cache_equations_range_576_616

theorem cache_equations_range_464_616 : ∀ i, 464 ≤ i → i < 616 → CacheEquation i :=
  merge_ranges cache_equations_range_464_544 cache_equations_range_544_616

theorem cache_equations_range_304_616 : ∀ i, 304 ≤ i → i < 616 → CacheEquation i :=
  merge_ranges cache_equations_range_304_464 cache_equations_range_464_616

theorem cache_equations_range_0_616 : ∀ i, 0 ≤ i → i < 616 → CacheEquation i :=
  merge_ranges cache_equations_range_0_304 cache_equations_range_304_616

theorem cache_equations (i : ℕ) (hi : i < 616) : CacheEquation i :=
  cache_equations_range_0_616 i (Nat.zero_le _) hi

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Summaries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem output_of_row_eq (i : ℕ) (d : ListRow) (p : Cell) (size height : ℕ)
    (omitted : Set Cell) (he : rowAt i = denote d)
    (summary : (denote d).A = {p} ∧ (denote d).H.card = size ∧
      (denote d).height = height)
    (omits : ∀ q ∈ d.H, q ∉ omitted) : Output i p size height omitted := by
  unfold Output
  rw [he]
  refine ⟨summary.1, summary.2.1, summary.2.2, ?_⟩
  apply Set.disjoint_left.mpr
  intro q hq hq'
  exact omits q (List.mem_toFinset.mp hq) hq'

end SnakyCertificate.Check

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_TableValidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate

theorem table_size : table.size = 610 := by
  simp only [table, Array.size_append]
  decide +kernel

theorem table_entries_block_0 : ∀ j : Fin 10, TableEntryOk (0 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_0 : ∀ k, 0 ≤ k → k < 10 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 0) (n := 10) table_entries_block_0

theorem table_entries_block_10 : ∀ j : Fin 10, TableEntryOk (10 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_10 : ∀ k, 10 ≤ k → k < 20 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 10) (n := 10) table_entries_block_10

theorem table_entries_block_20 : ∀ j : Fin 10, TableEntryOk (20 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_20 : ∀ k, 20 ≤ k → k < 30 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 20) (n := 10) table_entries_block_20

theorem table_entries_block_30 : ∀ j : Fin 10, TableEntryOk (30 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_30 : ∀ k, 30 ≤ k → k < 40 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 30) (n := 10) table_entries_block_30

theorem table_entries_block_40 : ∀ j : Fin 10, TableEntryOk (40 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_40 : ∀ k, 40 ≤ k → k < 50 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 40) (n := 10) table_entries_block_40

theorem table_entries_block_50 : ∀ j : Fin 10, TableEntryOk (50 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_50 : ∀ k, 50 ≤ k → k < 60 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 50) (n := 10) table_entries_block_50

theorem table_entries_block_60 : ∀ j : Fin 10, TableEntryOk (60 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_60 : ∀ k, 60 ≤ k → k < 70 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 60) (n := 10) table_entries_block_60

theorem table_entries_block_70 : ∀ j : Fin 10, TableEntryOk (70 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_70 : ∀ k, 70 ≤ k → k < 80 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 70) (n := 10) table_entries_block_70

theorem table_entries_block_80 : ∀ j : Fin 10, TableEntryOk (80 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_80 : ∀ k, 80 ≤ k → k < 90 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 80) (n := 10) table_entries_block_80

theorem table_entries_block_90 : ∀ j : Fin 10, TableEntryOk (90 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_90 : ∀ k, 90 ≤ k → k < 100 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 90) (n := 10) table_entries_block_90

theorem table_entries_block_100 : ∀ j : Fin 10, TableEntryOk (100 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_100 : ∀ k, 100 ≤ k → k < 110 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 100) (n := 10) table_entries_block_100

theorem table_entries_block_110 : ∀ j : Fin 10, TableEntryOk (110 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_110 : ∀ k, 110 ≤ k → k < 120 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 110) (n := 10) table_entries_block_110

theorem table_entries_block_120 : ∀ j : Fin 10, TableEntryOk (120 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_120 : ∀ k, 120 ≤ k → k < 130 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 120) (n := 10) table_entries_block_120

theorem table_entries_block_130 : ∀ j : Fin 10, TableEntryOk (130 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_130 : ∀ k, 130 ≤ k → k < 140 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 130) (n := 10) table_entries_block_130

theorem table_entries_block_140 : ∀ j : Fin 10, TableEntryOk (140 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_140 : ∀ k, 140 ≤ k → k < 150 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 140) (n := 10) table_entries_block_140

theorem table_entries_block_150 : ∀ j : Fin 10, TableEntryOk (150 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_150 : ∀ k, 150 ≤ k → k < 160 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 150) (n := 10) table_entries_block_150

theorem table_entries_block_160 : ∀ j : Fin 10, TableEntryOk (160 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_160 : ∀ k, 160 ≤ k → k < 170 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 160) (n := 10) table_entries_block_160

theorem table_entries_block_170 : ∀ j : Fin 10, TableEntryOk (170 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_170 : ∀ k, 170 ≤ k → k < 180 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 170) (n := 10) table_entries_block_170

theorem table_entries_block_180 : ∀ j : Fin 10, TableEntryOk (180 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_180 : ∀ k, 180 ≤ k → k < 190 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 180) (n := 10) table_entries_block_180

theorem table_entries_block_190 : ∀ j : Fin 10, TableEntryOk (190 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_190 : ∀ k, 190 ≤ k → k < 200 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 190) (n := 10) table_entries_block_190

theorem table_entries_block_200 : ∀ j : Fin 10, TableEntryOk (200 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_200 : ∀ k, 200 ≤ k → k < 210 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 200) (n := 10) table_entries_block_200

theorem table_entries_block_210 : ∀ j : Fin 10, TableEntryOk (210 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_210 : ∀ k, 210 ≤ k → k < 220 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 210) (n := 10) table_entries_block_210

theorem table_entries_block_220 : ∀ j : Fin 10, TableEntryOk (220 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_220 : ∀ k, 220 ≤ k → k < 230 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 220) (n := 10) table_entries_block_220

theorem table_entries_block_230 : ∀ j : Fin 10, TableEntryOk (230 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_230 : ∀ k, 230 ≤ k → k < 240 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 230) (n := 10) table_entries_block_230

theorem table_entries_block_240 : ∀ j : Fin 10, TableEntryOk (240 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_240 : ∀ k, 240 ≤ k → k < 250 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 240) (n := 10) table_entries_block_240

theorem table_entries_block_250 : ∀ j : Fin 10, TableEntryOk (250 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_250 : ∀ k, 250 ≤ k → k < 260 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 250) (n := 10) table_entries_block_250

theorem table_entries_block_260 : ∀ j : Fin 10, TableEntryOk (260 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_260 : ∀ k, 260 ≤ k → k < 270 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 260) (n := 10) table_entries_block_260

theorem table_entries_block_270 : ∀ j : Fin 10, TableEntryOk (270 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_270 : ∀ k, 270 ≤ k → k < 280 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 270) (n := 10) table_entries_block_270

theorem table_entries_block_280 : ∀ j : Fin 10, TableEntryOk (280 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_280 : ∀ k, 280 ≤ k → k < 290 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 280) (n := 10) table_entries_block_280

theorem table_entries_block_290 : ∀ j : Fin 10, TableEntryOk (290 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_290 : ∀ k, 290 ≤ k → k < 300 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 290) (n := 10) table_entries_block_290

theorem table_entries_block_300 : ∀ j : Fin 10, TableEntryOk (300 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_300 : ∀ k, 300 ≤ k → k < 310 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 300) (n := 10) table_entries_block_300

theorem table_entries_block_310 : ∀ j : Fin 10, TableEntryOk (310 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_310 : ∀ k, 310 ≤ k → k < 320 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 310) (n := 10) table_entries_block_310

theorem table_entries_block_320 : ∀ j : Fin 10, TableEntryOk (320 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_320 : ∀ k, 320 ≤ k → k < 330 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 320) (n := 10) table_entries_block_320

theorem table_entries_block_330 : ∀ j : Fin 10, TableEntryOk (330 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_330 : ∀ k, 330 ≤ k → k < 340 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 330) (n := 10) table_entries_block_330

theorem table_entries_block_340 : ∀ j : Fin 10, TableEntryOk (340 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_340 : ∀ k, 340 ≤ k → k < 350 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 340) (n := 10) table_entries_block_340

theorem table_entries_block_350 : ∀ j : Fin 10, TableEntryOk (350 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_350 : ∀ k, 350 ≤ k → k < 360 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 350) (n := 10) table_entries_block_350

theorem table_entries_block_360 : ∀ j : Fin 10, TableEntryOk (360 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_360 : ∀ k, 360 ≤ k → k < 370 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 360) (n := 10) table_entries_block_360

theorem table_entries_block_370 : ∀ j : Fin 10, TableEntryOk (370 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_370 : ∀ k, 370 ≤ k → k < 380 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 370) (n := 10) table_entries_block_370

theorem table_entries_block_380 : ∀ j : Fin 10, TableEntryOk (380 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_380 : ∀ k, 380 ≤ k → k < 390 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 380) (n := 10) table_entries_block_380

theorem table_entries_block_390 : ∀ j : Fin 10, TableEntryOk (390 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_390 : ∀ k, 390 ≤ k → k < 400 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 390) (n := 10) table_entries_block_390

theorem table_entries_block_400 : ∀ j : Fin 10, TableEntryOk (400 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_400 : ∀ k, 400 ≤ k → k < 410 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 400) (n := 10) table_entries_block_400

theorem table_entries_block_410 : ∀ j : Fin 10, TableEntryOk (410 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_410 : ∀ k, 410 ≤ k → k < 420 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 410) (n := 10) table_entries_block_410

theorem table_entries_block_420 : ∀ j : Fin 10, TableEntryOk (420 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_420 : ∀ k, 420 ≤ k → k < 430 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 420) (n := 10) table_entries_block_420

theorem table_entries_block_430 : ∀ j : Fin 10, TableEntryOk (430 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_430 : ∀ k, 430 ≤ k → k < 440 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 430) (n := 10) table_entries_block_430

theorem table_entries_block_440 : ∀ j : Fin 10, TableEntryOk (440 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_440 : ∀ k, 440 ≤ k → k < 450 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 440) (n := 10) table_entries_block_440

theorem table_entries_block_450 : ∀ j : Fin 10, TableEntryOk (450 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_450 : ∀ k, 450 ≤ k → k < 460 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 450) (n := 10) table_entries_block_450

theorem table_entries_block_460 : ∀ j : Fin 10, TableEntryOk (460 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_460 : ∀ k, 460 ≤ k → k < 470 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 460) (n := 10) table_entries_block_460

theorem table_entries_block_470 : ∀ j : Fin 10, TableEntryOk (470 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_470 : ∀ k, 470 ≤ k → k < 480 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 470) (n := 10) table_entries_block_470

theorem table_entries_block_480 : ∀ j : Fin 10, TableEntryOk (480 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_480 : ∀ k, 480 ≤ k → k < 490 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 480) (n := 10) table_entries_block_480

theorem table_entries_block_490 : ∀ j : Fin 10, TableEntryOk (490 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_490 : ∀ k, 490 ≤ k → k < 500 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 490) (n := 10) table_entries_block_490

theorem table_entries_block_500 : ∀ j : Fin 10, TableEntryOk (500 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_500 : ∀ k, 500 ≤ k → k < 510 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 500) (n := 10) table_entries_block_500

theorem table_entries_block_510 : ∀ j : Fin 10, TableEntryOk (510 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_510 : ∀ k, 510 ≤ k → k < 520 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 510) (n := 10) table_entries_block_510

theorem table_entries_block_520 : ∀ j : Fin 10, TableEntryOk (520 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_520 : ∀ k, 520 ≤ k → k < 530 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 520) (n := 10) table_entries_block_520

theorem table_entries_block_530 : ∀ j : Fin 10, TableEntryOk (530 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_530 : ∀ k, 530 ≤ k → k < 540 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 530) (n := 10) table_entries_block_530

theorem table_entries_block_540 : ∀ j : Fin 10, TableEntryOk (540 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_540 : ∀ k, 540 ≤ k → k < 550 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 540) (n := 10) table_entries_block_540

theorem table_entries_block_550 : ∀ j : Fin 10, TableEntryOk (550 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_550 : ∀ k, 550 ≤ k → k < 560 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 550) (n := 10) table_entries_block_550

theorem table_entries_block_560 : ∀ j : Fin 10, TableEntryOk (560 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_560 : ∀ k, 560 ≤ k → k < 570 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 560) (n := 10) table_entries_block_560

theorem table_entries_block_570 : ∀ j : Fin 10, TableEntryOk (570 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_570 : ∀ k, 570 ≤ k → k < 580 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 570) (n := 10) table_entries_block_570

theorem table_entries_block_580 : ∀ j : Fin 10, TableEntryOk (580 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_580 : ∀ k, 580 ≤ k → k < 590 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 580) (n := 10) table_entries_block_580

theorem table_entries_block_590 : ∀ j : Fin 10, TableEntryOk (590 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_590 : ∀ k, 590 ≤ k → k < 600 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 590) (n := 10) table_entries_block_590

theorem table_entries_block_600 : ∀ j : Fin 10, TableEntryOk (600 + j.val) := by
  unfold TableEntryOk
  simp only [table_getElem?_eq]
  decide +kernel

theorem table_entries_range_600 : ∀ k, 600 ≤ k → k < 610 → TableEntryOk k :=
  fin_block_range (P := TableEntryOk) (a := 600) (n := 10) table_entries_block_600

theorem table_entries_range_10_30 : ∀ i, 10 ≤ i → i < 30 → TableEntryOk i :=
  merge_ranges table_entries_range_10 table_entries_range_20

theorem table_entries_range_0_30 : ∀ i, 0 ≤ i → i < 30 → TableEntryOk i :=
  merge_ranges table_entries_range_0 table_entries_range_10_30

theorem table_entries_range_30_50 : ∀ i, 30 ≤ i → i < 50 → TableEntryOk i :=
  merge_ranges table_entries_range_30 table_entries_range_40

theorem table_entries_range_50_70 : ∀ i, 50 ≤ i → i < 70 → TableEntryOk i :=
  merge_ranges table_entries_range_50 table_entries_range_60

theorem table_entries_range_30_70 : ∀ i, 30 ≤ i → i < 70 → TableEntryOk i :=
  merge_ranges table_entries_range_30_50 table_entries_range_50_70

theorem table_entries_range_0_70 : ∀ i, 0 ≤ i → i < 70 → TableEntryOk i :=
  merge_ranges table_entries_range_0_30 table_entries_range_30_70

theorem table_entries_range_70_90 : ∀ i, 70 ≤ i → i < 90 → TableEntryOk i :=
  merge_ranges table_entries_range_70 table_entries_range_80

theorem table_entries_range_90_110 : ∀ i, 90 ≤ i → i < 110 → TableEntryOk i :=
  merge_ranges table_entries_range_90 table_entries_range_100

theorem table_entries_range_70_110 : ∀ i, 70 ≤ i → i < 110 → TableEntryOk i :=
  merge_ranges table_entries_range_70_90 table_entries_range_90_110

theorem table_entries_range_110_130 : ∀ i, 110 ≤ i → i < 130 → TableEntryOk i :=
  merge_ranges table_entries_range_110 table_entries_range_120

theorem table_entries_range_130_150 : ∀ i, 130 ≤ i → i < 150 → TableEntryOk i :=
  merge_ranges table_entries_range_130 table_entries_range_140

theorem table_entries_range_110_150 : ∀ i, 110 ≤ i → i < 150 → TableEntryOk i :=
  merge_ranges table_entries_range_110_130 table_entries_range_130_150

theorem table_entries_range_70_150 : ∀ i, 70 ≤ i → i < 150 → TableEntryOk i :=
  merge_ranges table_entries_range_70_110 table_entries_range_110_150

theorem table_entries_range_0_150 : ∀ i, 0 ≤ i → i < 150 → TableEntryOk i :=
  merge_ranges table_entries_range_0_70 table_entries_range_70_150

theorem table_entries_range_160_180 : ∀ i, 160 ≤ i → i < 180 → TableEntryOk i :=
  merge_ranges table_entries_range_160 table_entries_range_170

theorem table_entries_range_150_180 : ∀ i, 150 ≤ i → i < 180 → TableEntryOk i :=
  merge_ranges table_entries_range_150 table_entries_range_160_180

theorem table_entries_range_180_200 : ∀ i, 180 ≤ i → i < 200 → TableEntryOk i :=
  merge_ranges table_entries_range_180 table_entries_range_190

theorem table_entries_range_200_220 : ∀ i, 200 ≤ i → i < 220 → TableEntryOk i :=
  merge_ranges table_entries_range_200 table_entries_range_210

theorem table_entries_range_180_220 : ∀ i, 180 ≤ i → i < 220 → TableEntryOk i :=
  merge_ranges table_entries_range_180_200 table_entries_range_200_220

theorem table_entries_range_150_220 : ∀ i, 150 ≤ i → i < 220 → TableEntryOk i :=
  merge_ranges table_entries_range_150_180 table_entries_range_180_220

theorem table_entries_range_220_240 : ∀ i, 220 ≤ i → i < 240 → TableEntryOk i :=
  merge_ranges table_entries_range_220 table_entries_range_230

theorem table_entries_range_240_260 : ∀ i, 240 ≤ i → i < 260 → TableEntryOk i :=
  merge_ranges table_entries_range_240 table_entries_range_250

theorem table_entries_range_220_260 : ∀ i, 220 ≤ i → i < 260 → TableEntryOk i :=
  merge_ranges table_entries_range_220_240 table_entries_range_240_260

theorem table_entries_range_260_280 : ∀ i, 260 ≤ i → i < 280 → TableEntryOk i :=
  merge_ranges table_entries_range_260 table_entries_range_270

theorem table_entries_range_280_300 : ∀ i, 280 ≤ i → i < 300 → TableEntryOk i :=
  merge_ranges table_entries_range_280 table_entries_range_290

theorem table_entries_range_260_300 : ∀ i, 260 ≤ i → i < 300 → TableEntryOk i :=
  merge_ranges table_entries_range_260_280 table_entries_range_280_300

theorem table_entries_range_220_300 : ∀ i, 220 ≤ i → i < 300 → TableEntryOk i :=
  merge_ranges table_entries_range_220_260 table_entries_range_260_300

theorem table_entries_range_150_300 : ∀ i, 150 ≤ i → i < 300 → TableEntryOk i :=
  merge_ranges table_entries_range_150_220 table_entries_range_220_300

theorem table_entries_range_0_300 : ∀ i, 0 ≤ i → i < 300 → TableEntryOk i :=
  merge_ranges table_entries_range_0_150 table_entries_range_150_300

theorem table_entries_range_310_330 : ∀ i, 310 ≤ i → i < 330 → TableEntryOk i :=
  merge_ranges table_entries_range_310 table_entries_range_320

theorem table_entries_range_300_330 : ∀ i, 300 ≤ i → i < 330 → TableEntryOk i :=
  merge_ranges table_entries_range_300 table_entries_range_310_330

theorem table_entries_range_330_350 : ∀ i, 330 ≤ i → i < 350 → TableEntryOk i :=
  merge_ranges table_entries_range_330 table_entries_range_340

theorem table_entries_range_350_370 : ∀ i, 350 ≤ i → i < 370 → TableEntryOk i :=
  merge_ranges table_entries_range_350 table_entries_range_360

theorem table_entries_range_330_370 : ∀ i, 330 ≤ i → i < 370 → TableEntryOk i :=
  merge_ranges table_entries_range_330_350 table_entries_range_350_370

theorem table_entries_range_300_370 : ∀ i, 300 ≤ i → i < 370 → TableEntryOk i :=
  merge_ranges table_entries_range_300_330 table_entries_range_330_370

theorem table_entries_range_370_390 : ∀ i, 370 ≤ i → i < 390 → TableEntryOk i :=
  merge_ranges table_entries_range_370 table_entries_range_380

theorem table_entries_range_390_410 : ∀ i, 390 ≤ i → i < 410 → TableEntryOk i :=
  merge_ranges table_entries_range_390 table_entries_range_400

theorem table_entries_range_370_410 : ∀ i, 370 ≤ i → i < 410 → TableEntryOk i :=
  merge_ranges table_entries_range_370_390 table_entries_range_390_410

theorem table_entries_range_410_430 : ∀ i, 410 ≤ i → i < 430 → TableEntryOk i :=
  merge_ranges table_entries_range_410 table_entries_range_420

theorem table_entries_range_430_450 : ∀ i, 430 ≤ i → i < 450 → TableEntryOk i :=
  merge_ranges table_entries_range_430 table_entries_range_440

theorem table_entries_range_410_450 : ∀ i, 410 ≤ i → i < 450 → TableEntryOk i :=
  merge_ranges table_entries_range_410_430 table_entries_range_430_450

theorem table_entries_range_370_450 : ∀ i, 370 ≤ i → i < 450 → TableEntryOk i :=
  merge_ranges table_entries_range_370_410 table_entries_range_410_450

theorem table_entries_range_300_450 : ∀ i, 300 ≤ i → i < 450 → TableEntryOk i :=
  merge_ranges table_entries_range_300_370 table_entries_range_370_450

theorem table_entries_range_450_470 : ∀ i, 450 ≤ i → i < 470 → TableEntryOk i :=
  merge_ranges table_entries_range_450 table_entries_range_460

theorem table_entries_range_470_490 : ∀ i, 470 ≤ i → i < 490 → TableEntryOk i :=
  merge_ranges table_entries_range_470 table_entries_range_480

theorem table_entries_range_450_490 : ∀ i, 450 ≤ i → i < 490 → TableEntryOk i :=
  merge_ranges table_entries_range_450_470 table_entries_range_470_490

theorem table_entries_range_490_510 : ∀ i, 490 ≤ i → i < 510 → TableEntryOk i :=
  merge_ranges table_entries_range_490 table_entries_range_500

theorem table_entries_range_510_530 : ∀ i, 510 ≤ i → i < 530 → TableEntryOk i :=
  merge_ranges table_entries_range_510 table_entries_range_520

theorem table_entries_range_490_530 : ∀ i, 490 ≤ i → i < 530 → TableEntryOk i :=
  merge_ranges table_entries_range_490_510 table_entries_range_510_530

theorem table_entries_range_450_530 : ∀ i, 450 ≤ i → i < 530 → TableEntryOk i :=
  merge_ranges table_entries_range_450_490 table_entries_range_490_530

theorem table_entries_range_530_550 : ∀ i, 530 ≤ i → i < 550 → TableEntryOk i :=
  merge_ranges table_entries_range_530 table_entries_range_540

theorem table_entries_range_550_570 : ∀ i, 550 ≤ i → i < 570 → TableEntryOk i :=
  merge_ranges table_entries_range_550 table_entries_range_560

theorem table_entries_range_530_570 : ∀ i, 530 ≤ i → i < 570 → TableEntryOk i :=
  merge_ranges table_entries_range_530_550 table_entries_range_550_570

theorem table_entries_range_570_590 : ∀ i, 570 ≤ i → i < 590 → TableEntryOk i :=
  merge_ranges table_entries_range_570 table_entries_range_580

theorem table_entries_range_590_610 : ∀ i, 590 ≤ i → i < 610 → TableEntryOk i :=
  merge_ranges table_entries_range_590 table_entries_range_600

theorem table_entries_range_570_610 : ∀ i, 570 ≤ i → i < 610 → TableEntryOk i :=
  merge_ranges table_entries_range_570_590 table_entries_range_590_610

theorem table_entries_range_530_610 : ∀ i, 530 ≤ i → i < 610 → TableEntryOk i :=
  merge_ranges table_entries_range_530_570 table_entries_range_570_610

theorem table_entries_range_450_610 : ∀ i, 450 ≤ i → i < 610 → TableEntryOk i :=
  merge_ranges table_entries_range_450_530 table_entries_range_530_610

theorem table_entries_range_300_610 : ∀ i, 300 ≤ i → i < 610 → TableEntryOk i :=
  merge_ranges table_entries_range_300_450 table_entries_range_450_610

theorem table_entries_range_0_610 : ∀ i, 0 ≤ i → i < 610 → TableEntryOk i :=
  merge_ranges table_entries_range_0_300 table_entries_range_300_610

theorem table_entries_valid : ∀ k : Fin 610,
    let e := table[k.val]?.getD emptyEntry
    e.index = k.val + 6 ∧ e.terms ≠ [] ∧ ∀ t ∈ e.terms, t.child < e.index := by
  intro k
  exact table_entries_range_0_610 k.val (Nat.zero_le _) k.isLt

theorem table_valid : TableValid := by
  refine ⟨table_size, ?_⟩
  intro k hk
  exact table_entries_valid ⟨k, by simpa only [table_size] using hk⟩

theorem placement_count : placementCount = 1837 := by
  rw [placementCount, table_toList]
  decide +kernel

theorem entryAt_index {i : ℕ} (hlo : 6 ≤ i) (hhi : i < 616) :
    (entryAt i).index = i := by
  have h := (table_entries_valid ⟨i - 6, by omega⟩).1
  simpa only [entryAt, Nat.sub_add_cancel hlo] using h

theorem entryAt_backward {i : ℕ} (hlo : 6 ≤ i) (hhi : i < 616)
    {t : Term} (ht : t ∈ (entryAt i).terms) : t.child < i := by
  have h := (table_entries_valid ⟨i - 6, by omega⟩).2.2 t ht
  change t.child < (entryAt i).index at h
  simpa only [entryAt_index hlo hhi] using h

end SnakyCertificate

end OAI
end

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem rowAt_eq_cached (i : ℕ) (hi : i < 616) : rowAt i = denote (cached i) :=
  rowAt_unique (fun j => denote (cached j)) 616
    (fun _ hlo hhi _ ht => entryAt_backward hlo hhi ht)
    cache_equations i hi

theorem output557 : Output 557 (-1, 0) 118 19 {p | p.1 ≤ -3 ∧ p.2 ≤ -2} := by
  apply output_of_row_eq 557 cache_557 (-1, 0) 118 19 _
  · exact rowAt_eq_cached 557 (by decide)
  · exact cache_summary_557
  · exact cache_omits_557

theorem output595 : Output 595 (-1, 0) 222 27 {p | p.1 = -2 ∧ p.2 ≤ -2} := by
  apply output_of_row_eq 595 cache_595 (-1, 0) 222 27 _
  · exact rowAt_eq_cached 595 (by decide)
  · exact cache_summary_595
  · exact cache_omits_595

theorem output603 : Output 603 (-1, 0) 275 27 {p | p.1 ≤ -3 ∧ p.2 = 0} := by
  apply output_of_row_eq 603 cache_603 (-1, 0) 275 27 _
  · exact rowAt_eq_cached 603 (by decide)
  · exact cache_summary_603
  · exact cache_omits_603

theorem output615 : Output 615 (1, 0) 686 34 {(1, -1)} := by
  apply output_of_row_eq 615 cache_615 (1, 0) 686 34 _
  · exact rowAt_eq_cached 615 (by decide)
  · exact cache_summary_615
  · exact cache_omits_615

theorem all_rows : AllRows := by
  intro i hi
  refine ⟨rowAt_subset i, (rowAt_origin i).1, (rowAt_origin i).2, ?_⟩
  rw [rowAt_eq_cached i hi]
  exact cache_heights i hi

end SnakyCertificate.Check

namespace SnakyCertificate

theorem certificate_correct_oai :
    TableValid ∧ placementCount = 1837 ∧
    Output 557 (-1, 0) 118 19 {p | p.1 ≤ -3 ∧ p.2 ≤ -2} ∧
    Output 595 (-1, 0) 222 27 {p | p.1 = -2 ∧ p.2 ≤ -2} ∧
    Output 603 (-1, 0) 275 27 {p | p.1 ≤ -3 ∧ p.2 = 0} ∧
    Output 615 (1, 0) 686 34 {(1, -1)} ∧
    AllRows := by
  exact ⟨table_valid, placement_count, Check.output557, Check.output595,
    Check.output603, Check.output615, Check.all_rows⟩

end SnakyCertificate

end OAI
end

theorem solution : type_of% @OAI.SnakyCertificate.certificate_correct_oai := @OAI.SnakyCertificate.certificate_correct_oai
