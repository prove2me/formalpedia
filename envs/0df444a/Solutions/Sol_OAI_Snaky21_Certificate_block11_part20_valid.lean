-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block11_part20_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:27:07.170511+00:00
-- url     : https://prove2.me/submissions/c9f483a1-8d26-48e2-84e7-6e9a41984ced

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part10_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part15_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part16_valid
import Definitions.Def_Snaky21Calc11Part10
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block10_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part19_valid
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate
namespace OAI.Snaky21
theorem base_valid (i : Fin 6) : Valid (baseCard i) := claim_calculus.1 i
theorem placed_valid (r : Fin 8) (t : Cell) {c : Card} (h : Valid c) : Valid (placed r t c) := claim_calculus.2.1 r t c h
end OAI.Snaky21

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace OAI.Snaky21.Certificate
theorem computed_card_ext {c d : Card} (hA : c.required = d.required) (hT : c.envelope = d.envelope) (hh : c.height = d.height) : c = d := by
  cases c
  cases d
  cases hA
  cases hT
  cases hh
  rfl
theorem valid_7 : Valid card_7 := block00_valid.2.2.2.2.2.2.2.1
theorem valid_9 : Valid card_9 := block00_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_19 : Valid card_19 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_53 : Valid card_53 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_57 : Valid card_57 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_88 : Valid card_88 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_111 : Valid card_111 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_188 : Valid card_188 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_231 : Valid card_231 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_258 : Valid card_258 := block04_valid.2.2.1
theorem valid_267 : Valid card_267 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_279 : Valid card_279 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_390 : Valid card_390 := block06_valid.2.2.2.2.2.2.1
theorem valid_395 : Valid card_395 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_397 : Valid card_397 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_512 : Valid card_512 := block08_valid.1
theorem valid_523 : Valid card_523 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_524 : Valid card_524 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_600 : Valid card_600 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_604 : Valid card_604 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_621 : Valid card_621 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_637 : Valid card_637 := block09_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_677 : Valid card_677 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_702 : Valid card_702 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_714 : Valid card_714 := block11_part10_valid.1
theorem valid_719 : Valid card_719 := block11_part15_valid.1
theorem valid_720 : Valid card_720 := block11_part16_valid.1
theorem valid_723 : Valid card_723 := block11_part19_valid.1

theorem calc11_card_1992_eq : placed 0 (3, 5) card_57 = calc11_card_1992 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1993_eq : placed 4 (7, 5) card_111 = calc11_card_1993 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1994_eq : placed 3 (10, 7) card_390 = calc11_card_1994 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1995_eq : placed 0 (4, 5) card_397 = calc11_card_1995 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1996_eq : calc11_card_1995.required ∪ ∅ = calc11_set_1996 := by decide +kernel

theorem calc11_set_1997_eq : calc11_card_1995.envelope ∪ ∅ = calc11_set_1997 := by decide +kernel

theorem calc11_set_1998_eq : calc11_card_1994.required ∪ calc11_set_1996 = calc11_set_1998 := by decide +kernel

theorem calc11_set_1999_eq : calc11_card_1994.envelope ∪ calc11_set_1997 = calc11_set_1999 := by decide +kernel

theorem calc11_set_2000_eq : calc11_card_1993.required ∪ calc11_set_1998 = calc11_set_2000 := by decide +kernel

theorem calc11_set_2001_eq : calc11_card_1993.envelope ∪ calc11_set_1999 = calc11_set_2001 := by decide +kernel

theorem calc11_set_2002_eq : calc11_card_1992.required ∪ calc11_set_2000 = calc11_set_2002 := by decide +kernel

theorem calc11_set_2003_eq : calc11_card_1992.envelope ∪ calc11_set_2001 = calc11_set_2003 := by decide +kernel

theorem calc11_set_2004_eq : calc11_card_1995.envelope ∩ calc11_card_1992.envelope = calc11_set_2004 := by decide +kernel

theorem calc11_set_2005_eq : calc11_card_1994.envelope ∩ calc11_set_2004 = calc11_set_2005 := by decide +kernel

theorem calc11_set_2006_eq : calc11_card_1993.envelope ∩ calc11_set_2005 = calc11_set_2006 := by decide +kernel

theorem calc11_set_2007_eq : calc11_set_2002 ∪ calc11_set_2006 = calc11_set_2007 := by decide +kernel

theorem calc11_finishA_2008 : calc11_set_2007.erase (4, 8) = inline_889.required := by decide +kernel

theorem calc11_finishT_2008 : insert (4, 8) calc11_set_2003 = inline_889.envelope := by decide +kernel

theorem eq_inline_889 : inline_889 = combine (4, 8) [placed 0 (3, 5) card_57, placed 4 (7, 5) card_111, placed 3 (10, 7) card_390, placed 0 (4, 5) card_397] := by
  rw [calc11_card_1992_eq, calc11_card_1993_eq, calc11_card_1994_eq, calc11_card_1995_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1996_eq, calc11_set_1998_eq, calc11_set_2000_eq, calc11_set_2002_eq, calc11_set_2004_eq, calc11_set_2005_eq, calc11_set_2006_eq, calc11_set_2007_eq, calc11_finishA_2008]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1997_eq, calc11_set_1999_eq, calc11_set_2001_eq, calc11_set_2003_eq, calc11_finishT_2008]
  · decide +kernel

theorem valid_inline_889 : Valid inline_889 := by
  rw [eq_inline_889]
  apply combination_rule (4, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 5) valid_57
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 5) valid_111
  rcases hc with rfl | hc
  · exact placed_valid 3 (10, 7) valid_390
  subst c
  exact placed_valid 0 (4, 5) valid_397

theorem calc11_card_2009_eq : placed 3 (8, 7) card_19 = calc11_card_2009 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2010_eq : placed 7 (8, 9) card_19 = calc11_card_2010 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2011_eq : placed 0 (4, 6) card_395 = calc11_card_2011 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_2012_eq : calc11_card_2011.required ∪ ∅ = calc11_set_2012 := by decide +kernel

theorem calc11_set_2013_eq : calc11_card_2011.envelope ∪ ∅ = calc11_set_2013 := by decide +kernel

theorem calc11_set_2014_eq : calc11_card_2010.required ∪ calc11_set_2012 = calc11_set_2014 := by decide +kernel

theorem calc11_set_2015_eq : calc11_card_2010.envelope ∪ calc11_set_2013 = calc11_set_2015 := by decide +kernel

theorem calc11_set_2016_eq : calc11_card_2009.required ∪ calc11_set_2014 = calc11_set_2016 := by decide +kernel

theorem calc11_set_2017_eq : calc11_card_2009.envelope ∪ calc11_set_2015 = calc11_set_2017 := by decide +kernel

theorem calc11_set_2018_eq : calc11_card_2011.envelope ∩ calc11_card_2009.envelope = calc11_set_2018 := by decide +kernel

theorem calc11_set_2019_eq : calc11_card_2010.envelope ∩ calc11_set_2018 = calc11_set_2019 := by decide +kernel

theorem calc11_set_2020_eq : calc11_set_2016 ∪ calc11_set_2019 = calc11_set_2020 := by decide +kernel

theorem calc11_finishA_2021 : calc11_set_2020.erase (4, 8) = inline_890.required := by decide +kernel

theorem calc11_finishT_2021 : insert (4, 8) calc11_set_2017 = inline_890.envelope := by decide +kernel

theorem eq_inline_890 : inline_890 = combine (4, 8) [placed 3 (8, 7) card_19, placed 7 (8, 9) card_19, placed 0 (4, 6) card_395] := by
  rw [calc11_card_2009_eq, calc11_card_2010_eq, calc11_card_2011_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2012_eq, calc11_set_2014_eq, calc11_set_2016_eq, calc11_set_2018_eq, calc11_set_2019_eq, calc11_set_2020_eq, calc11_finishA_2021]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2013_eq, calc11_set_2015_eq, calc11_set_2017_eq, calc11_finishT_2021]
  · decide +kernel

theorem valid_inline_890 : Valid inline_890 := by
  rw [eq_inline_890]
  apply combination_rule (4, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 7) valid_19
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 9) valid_19
  subst c
  exact placed_valid 0 (4, 6) valid_395

theorem calc11_card_2022_eq : placed 3 (8, 7) card_19 = calc11_card_2022 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2023_eq : placed 4 (7, 5) card_231 = calc11_card_2023 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2024_eq : placed 0 (4, 5) card_279 = calc11_card_2024 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_2025_eq : calc11_card_2024.required ∪ ∅ = calc11_set_2025 := by decide +kernel

theorem calc11_set_2026_eq : calc11_card_2024.envelope ∪ ∅ = calc11_set_2026 := by decide +kernel

theorem calc11_set_2027_eq : calc11_card_2023.required ∪ calc11_set_2025 = calc11_set_2027 := by decide +kernel

theorem calc11_set_2028_eq : calc11_card_2023.envelope ∪ calc11_set_2026 = calc11_set_2028 := by decide +kernel

theorem calc11_set_2029_eq : calc11_card_2022.required ∪ calc11_set_2027 = calc11_set_2029 := by decide +kernel

theorem calc11_set_2030_eq : calc11_card_2022.envelope ∪ calc11_set_2028 = calc11_set_2030 := by decide +kernel

theorem calc11_set_2031_eq : calc11_card_2024.envelope ∩ calc11_card_2022.envelope = calc11_set_2031 := by decide +kernel

theorem calc11_set_2032_eq : calc11_card_2023.envelope ∩ calc11_set_2031 = calc11_set_2032 := by decide +kernel

theorem calc11_set_2033_eq : calc11_set_2029 ∪ calc11_set_2032 = calc11_set_2033 := by decide +kernel

theorem calc11_finishA_2034 : calc11_set_2033.erase (4, 8) = inline_891.required := by decide +kernel

theorem calc11_finishT_2034 : insert (4, 8) calc11_set_2030 = inline_891.envelope := by decide +kernel

theorem eq_inline_891 : inline_891 = combine (4, 8) [placed 3 (8, 7) card_19, placed 4 (7, 5) card_231, placed 0 (4, 5) card_279] := by
  rw [calc11_card_2022_eq, calc11_card_2023_eq, calc11_card_2024_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2025_eq, calc11_set_2027_eq, calc11_set_2029_eq, calc11_set_2031_eq, calc11_set_2032_eq, calc11_set_2033_eq, calc11_finishA_2034]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2026_eq, calc11_set_2028_eq, calc11_set_2030_eq, calc11_finishT_2034]
  · decide +kernel

theorem valid_inline_891 : Valid inline_891 := by
  rw [eq_inline_891]
  apply combination_rule (4, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 7) valid_19
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 5) valid_231
  subst c
  exact placed_valid 0 (4, 5) valid_279

theorem calc11_card_2035_eq : placed 6 (6, 11) card_53 = calc11_card_2035 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2036_eq : placed 0 (4, 6) card_637 = calc11_card_2036 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_2037_eq : calc11_card_2036.required ∪ ∅ = calc11_set_2037 := by decide +kernel

theorem calc11_set_2038_eq : calc11_card_2036.envelope ∪ ∅ = calc11_set_2038 := by decide +kernel

theorem calc11_set_2039_eq : calc11_card_2035.required ∪ calc11_set_2037 = calc11_set_2039 := by decide +kernel

theorem calc11_set_2040_eq : calc11_card_2035.envelope ∪ calc11_set_2038 = calc11_set_2040 := by decide +kernel

theorem calc11_set_2041_eq : calc11_card_2036.envelope ∩ calc11_card_2035.envelope = calc11_set_2041 := by decide +kernel

theorem calc11_set_2042_eq : calc11_set_2039 ∪ calc11_set_2041 = calc11_set_2042 := by decide +kernel

theorem calc11_finishA_2043 : calc11_set_2042.erase (6, 9) = inline_892.required := by decide +kernel

theorem calc11_finishT_2043 : insert (6, 9) calc11_set_2040 = inline_892.envelope := by decide +kernel

theorem eq_inline_892 : inline_892 = combine (6, 9) [placed 6 (6, 11) card_53, placed 0 (4, 6) card_637] := by
  rw [calc11_card_2035_eq, calc11_card_2036_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2037_eq, calc11_set_2039_eq, calc11_set_2041_eq, calc11_set_2042_eq, calc11_finishA_2043]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2038_eq, calc11_set_2040_eq, calc11_finishT_2043]
  · decide +kernel

theorem valid_inline_892 : Valid inline_892 := by
  rw [eq_inline_892]
  apply combination_rule (6, 9) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 11) valid_53
  subst c
  exact placed_valid 0 (4, 6) valid_637

theorem calc11_card_2044_eq : placed 1 (3, 6) card_188 = calc11_card_2044 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2045_eq : placed 5 (3, 10) card_188 = calc11_card_2045 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2046_eq : placed 0 (5, 5) card_258 = calc11_card_2046 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_2047_eq : inline_892.required ∪ ∅ = calc11_set_2047 := by decide +kernel

theorem calc11_set_2048_eq : inline_892.envelope ∪ ∅ = calc11_set_2048 := by decide +kernel

theorem calc11_set_2049_eq : inline_891.required ∪ calc11_set_2047 = calc11_set_2049 := by decide +kernel

theorem calc11_set_2050_eq : inline_891.envelope ∪ calc11_set_2048 = calc11_set_2050 := by decide +kernel

theorem calc11_set_2051_eq : inline_890.required ∪ calc11_set_2049 = calc11_set_2051 := by decide +kernel

theorem calc11_set_2052_eq : inline_890.envelope ∪ calc11_set_2050 = calc11_set_2052 := by decide +kernel

theorem calc11_set_2053_eq : calc11_card_2046.required ∪ calc11_set_2051 = calc11_set_2053 := by decide +kernel

theorem calc11_set_2054_eq : calc11_card_2046.envelope ∪ calc11_set_2052 = calc11_set_2054 := by decide +kernel

theorem calc11_set_2055_eq : calc11_card_2045.required ∪ calc11_set_2053 = calc11_set_2055 := by decide +kernel

theorem calc11_set_2056_eq : calc11_card_2045.envelope ∪ calc11_set_2054 = calc11_set_2056 := by decide +kernel

theorem calc11_set_2057_eq : calc11_card_2044.required ∪ calc11_set_2055 = calc11_set_2057 := by decide +kernel

theorem calc11_set_2058_eq : calc11_card_2044.envelope ∪ calc11_set_2056 = calc11_set_2058 := by decide +kernel

theorem calc11_set_2059_eq : inline_892.envelope ∩ calc11_card_2044.envelope = calc11_set_2059 := by decide +kernel

theorem calc11_set_2060_eq : inline_891.envelope ∩ calc11_set_2059 = calc11_set_2060 := by decide +kernel

theorem calc11_set_2061_eq : inline_890.envelope ∩ calc11_set_2060 = calc11_set_2061 := by decide +kernel

theorem calc11_set_2062_eq : calc11_card_2046.envelope ∩ calc11_set_2061 = calc11_set_2062 := by decide +kernel

theorem calc11_set_2063_eq : calc11_card_2045.envelope ∩ calc11_set_2062 = calc11_set_2063 := by decide +kernel

theorem calc11_set_2064_eq : calc11_set_2057 ∪ calc11_set_2063 = calc11_set_2064 := by decide +kernel

theorem calc11_finishA_2065 : calc11_set_2064.erase (7, 8) = inline_893.required := by decide +kernel

theorem calc11_finishT_2065 : insert (7, 8) calc11_set_2058 = inline_893.envelope := by decide +kernel

theorem eq_inline_893 : inline_893 = combine (7, 8) [placed 1 (3, 6) card_188, placed 5 (3, 10) card_188, placed 0 (5, 5) card_258, inline_890, inline_891, inline_892] := by
  rw [calc11_card_2044_eq, calc11_card_2045_eq, calc11_card_2046_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2047_eq, calc11_set_2049_eq, calc11_set_2051_eq, calc11_set_2053_eq, calc11_set_2055_eq, calc11_set_2057_eq, calc11_set_2059_eq, calc11_set_2060_eq, calc11_set_2061_eq, calc11_set_2062_eq, calc11_set_2063_eq, calc11_set_2064_eq, calc11_finishA_2065]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2048_eq, calc11_set_2050_eq, calc11_set_2052_eq, calc11_set_2054_eq, calc11_set_2056_eq, calc11_set_2058_eq, calc11_finishT_2065]
  · decide +kernel

theorem valid_inline_893 : Valid inline_893 := by
  rw [eq_inline_893]
  apply combination_rule (7, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 6) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 10) valid_188
  rcases hc with rfl | hc
  · exact placed_valid 0 (5, 5) valid_258
  rcases hc with rfl | hc
  · exact valid_inline_890
  rcases hc with rfl | hc
  · exact valid_inline_891
  subst c
  exact valid_inline_892

theorem calc11_card_2066_eq : placed 7 (8, 8) card_53 = calc11_card_2066 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2067_eq : placed 1 (2, 7) card_53 = calc11_card_2067 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2068_eq : placed 7 (10, 12) card_720 = calc11_card_2068 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2069_eq : placed 1 (0, 3) card_720 = calc11_card_2069 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_2070_eq : calc11_card_2069.required ∪ ∅ = calc11_set_2070 := by decide +kernel

theorem calc11_set_2071_eq : calc11_card_2069.envelope ∪ ∅ = calc11_set_2071 := by decide +kernel

theorem calc11_set_2072_eq : calc11_card_2068.required ∪ calc11_set_2070 = calc11_set_2072 := by decide +kernel

theorem calc11_set_2073_eq : calc11_card_2068.envelope ∪ calc11_set_2071 = calc11_set_2073 := by decide +kernel

theorem calc11_set_2074_eq : calc11_card_2067.required ∪ calc11_set_2072 = calc11_set_2074 := by decide +kernel

theorem calc11_set_2075_eq : calc11_card_2067.envelope ∪ calc11_set_2073 = calc11_set_2075 := by decide +kernel

theorem calc11_set_2076_eq : calc11_card_2066.required ∪ calc11_set_2074 = calc11_set_2076 := by decide +kernel

theorem calc11_set_2077_eq : calc11_card_2066.envelope ∪ calc11_set_2075 = calc11_set_2077 := by decide +kernel

theorem calc11_set_2078_eq : calc11_card_2069.envelope ∩ calc11_card_2066.envelope = calc11_set_2078 := by decide +kernel

theorem calc11_set_2079_eq : calc11_card_2068.envelope ∩ calc11_set_2078 = calc11_set_2079 := by decide +kernel

theorem calc11_set_2080_eq : calc11_card_2067.envelope ∩ calc11_set_2079 = calc11_set_2080 := by decide +kernel

theorem calc11_set_2081_eq : calc11_set_2076 ∪ calc11_set_2080 = calc11_set_2081 := by decide +kernel

theorem calc11_finishA_2082 : calc11_set_2081.erase (4, 7) = inline_894.required := by decide +kernel

theorem calc11_finishT_2082 : insert (4, 7) calc11_set_2077 = inline_894.envelope := by decide +kernel

theorem eq_inline_894 : inline_894 = combine (4, 7) [placed 7 (8, 8) card_53, placed 1 (2, 7) card_53, placed 7 (10, 12) card_720, placed 1 (0, 3) card_720] := by
  rw [calc11_card_2066_eq, calc11_card_2067_eq, calc11_card_2068_eq, calc11_card_2069_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2070_eq, calc11_set_2072_eq, calc11_set_2074_eq, calc11_set_2076_eq, calc11_set_2078_eq, calc11_set_2079_eq, calc11_set_2080_eq, calc11_set_2081_eq, calc11_finishA_2082]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2071_eq, calc11_set_2073_eq, calc11_set_2075_eq, calc11_set_2077_eq, calc11_finishT_2082]
  · decide +kernel

theorem valid_inline_894 : Valid inline_894 := by
  rw [eq_inline_894]
  apply combination_rule (4, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 8) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 7) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 7 (10, 12) valid_720
  subst c
  exact placed_valid 1 (0, 3) valid_720

theorem calc11_card_2083_eq : placed 0 (4, 4) card_512 = calc11_card_2083 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2084_eq : placed 5 (2, 10) card_600 = calc11_card_2084 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2085_eq : placed 6 (9, 11) card_621 = calc11_card_2085 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2086_eq : placed 1 (3, 6) card_702 = calc11_card_2086 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2087_eq : placed 4 (8, 3) card_714 = calc11_card_2087 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_2088_eq : calc11_card_2087.required ∪ ∅ = calc11_set_2088 := by decide +kernel

theorem calc11_set_2089_eq : calc11_card_2087.envelope ∪ ∅ = calc11_set_2089 := by decide +kernel

theorem calc11_set_2090_eq : calc11_card_2086.required ∪ calc11_set_2088 = calc11_set_2090 := by decide +kernel

theorem calc11_set_2091_eq : calc11_card_2086.envelope ∪ calc11_set_2089 = calc11_set_2091 := by decide +kernel

theorem calc11_set_2092_eq : calc11_card_2085.required ∪ calc11_set_2090 = calc11_set_2092 := by decide +kernel

theorem calc11_set_2093_eq : calc11_card_2085.envelope ∪ calc11_set_2091 = calc11_set_2093 := by decide +kernel

theorem calc11_set_2094_eq : calc11_card_2084.required ∪ calc11_set_2092 = calc11_set_2094 := by decide +kernel

theorem calc11_set_2095_eq : calc11_card_2084.envelope ∪ calc11_set_2093 = calc11_set_2095 := by decide +kernel

theorem calc11_set_2096_eq : calc11_card_2083.required ∪ calc11_set_2094 = calc11_set_2096 := by decide +kernel

theorem calc11_set_2097_eq : calc11_card_2083.envelope ∪ calc11_set_2095 = calc11_set_2097 := by decide +kernel

theorem calc11_set_2098_eq : calc11_card_2087.envelope ∩ calc11_card_2083.envelope = calc11_set_2098 := by decide +kernel

theorem calc11_set_2099_eq : calc11_card_2086.envelope ∩ calc11_set_2098 = calc11_set_2099 := by decide +kernel

theorem calc11_set_2100_eq : calc11_card_2085.envelope ∩ calc11_set_2099 = calc11_set_2100 := by decide +kernel

theorem calc11_set_2101_eq : calc11_card_2084.envelope ∩ calc11_set_2100 = calc11_set_2101 := by decide +kernel

theorem calc11_set_2102_eq : calc11_set_2096 ∪ calc11_set_2101 = calc11_set_2102 := by decide +kernel

theorem calc11_finishA_2103 : calc11_set_2102.erase (6, 7) = inline_895.required := by decide +kernel

theorem calc11_finishT_2103 : insert (6, 7) calc11_set_2097 = inline_895.envelope := by decide +kernel

theorem eq_inline_895 : inline_895 = combine (6, 7) [placed 0 (4, 4) card_512, placed 5 (2, 10) card_600, placed 6 (9, 11) card_621, placed 1 (3, 6) card_702, placed 4 (8, 3) card_714] := by
  rw [calc11_card_2083_eq, calc11_card_2084_eq, calc11_card_2085_eq, calc11_card_2086_eq, calc11_card_2087_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2088_eq, calc11_set_2090_eq, calc11_set_2092_eq, calc11_set_2094_eq, calc11_set_2096_eq, calc11_set_2098_eq, calc11_set_2099_eq, calc11_set_2100_eq, calc11_set_2101_eq, calc11_set_2102_eq, calc11_finishA_2103]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2089_eq, calc11_set_2091_eq, calc11_set_2093_eq, calc11_set_2095_eq, calc11_set_2097_eq, calc11_finishT_2103]
  · decide +kernel

theorem valid_inline_895 : Valid inline_895 := by
  rw [eq_inline_895]
  apply combination_rule (6, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 4) valid_512
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 10) valid_600
  rcases hc with rfl | hc
  · exact placed_valid 6 (9, 11) valid_621
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 6) valid_702
  subst c
  exact placed_valid 4 (8, 3) valid_714

theorem calc11_card_2104_eq : placed 5 (3, 8) card_7 = calc11_card_2104 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2105_eq : placed 1 (3, 7) card_9 = calc11_card_2105 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2106_eq : placed 0 (4, 5) card_604 = calc11_card_2106 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_2107_eq : calc11_card_2106.required ∪ ∅ = calc11_set_2107 := by decide +kernel

theorem calc11_set_2108_eq : calc11_card_2106.envelope ∪ ∅ = calc11_set_2108 := by decide +kernel

theorem calc11_set_2109_eq : calc11_card_2105.required ∪ calc11_set_2107 = calc11_set_2109 := by decide +kernel

theorem calc11_set_2110_eq : calc11_card_2105.envelope ∪ calc11_set_2108 = calc11_set_2110 := by decide +kernel

theorem calc11_set_2111_eq : calc11_card_2104.required ∪ calc11_set_2109 = calc11_set_2111 := by decide +kernel

theorem calc11_set_2112_eq : calc11_card_2104.envelope ∪ calc11_set_2110 = calc11_set_2112 := by decide +kernel

theorem calc11_set_2113_eq : calc11_card_2106.envelope ∩ calc11_card_2104.envelope = calc11_set_2113 := by decide +kernel

theorem calc11_set_2114_eq : calc11_card_2105.envelope ∩ calc11_set_2113 = calc11_set_2114 := by decide +kernel

theorem calc11_set_2115_eq : calc11_set_2111 ∪ calc11_set_2114 = calc11_set_2115 := by decide +kernel

theorem calc11_finishA_2116 : calc11_set_2115.erase (7, 8) = inline_896.required := by decide +kernel

theorem calc11_finishT_2116 : insert (7, 8) calc11_set_2112 = inline_896.envelope := by decide +kernel

theorem eq_inline_896 : inline_896 = combine (7, 8) [placed 5 (3, 8) card_7, placed 1 (3, 7) card_9, placed 0 (4, 5) card_604] := by
  rw [calc11_card_2104_eq, calc11_card_2105_eq, calc11_card_2106_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2107_eq, calc11_set_2109_eq, calc11_set_2111_eq, calc11_set_2113_eq, calc11_set_2114_eq, calc11_set_2115_eq, calc11_finishA_2116]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2108_eq, calc11_set_2110_eq, calc11_set_2112_eq, calc11_finishT_2116]
  · decide +kernel

theorem valid_inline_896 : Valid inline_896 := by
  rw [eq_inline_896]
  apply combination_rule (7, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 8) valid_7
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 7) valid_9
  subst c
  exact placed_valid 0 (4, 5) valid_604

theorem calc11_card_2117_eq : placed 0 (3, 5) card_88 = calc11_card_2117 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2118_eq : placed 4 (7, 5) card_231 = calc11_card_2118 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2119_eq : placed 3 (8, 6) card_267 = calc11_card_2119 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_2120_eq : inline_896.required ∪ ∅ = calc11_set_2120 := by decide +kernel

theorem calc11_set_2121_eq : inline_896.envelope ∪ ∅ = calc11_set_2121 := by decide +kernel

theorem calc11_set_2122_eq : calc11_card_2119.required ∪ calc11_set_2120 = calc11_set_2122 := by decide +kernel

theorem calc11_set_2123_eq : calc11_card_2119.envelope ∪ calc11_set_2121 = calc11_set_2123 := by decide +kernel

theorem calc11_set_2124_eq : calc11_card_2118.required ∪ calc11_set_2122 = calc11_set_2124 := by decide +kernel

theorem calc11_set_2125_eq : calc11_card_2118.envelope ∪ calc11_set_2123 = calc11_set_2125 := by decide +kernel

theorem calc11_set_2126_eq : calc11_card_2117.required ∪ calc11_set_2124 = calc11_set_2126 := by decide +kernel

theorem calc11_set_2127_eq : calc11_card_2117.envelope ∪ calc11_set_2125 = calc11_set_2127 := by decide +kernel

theorem calc11_set_2128_eq : inline_896.envelope ∩ calc11_card_2117.envelope = calc11_set_2128 := by decide +kernel

theorem calc11_set_2129_eq : calc11_card_2119.envelope ∩ calc11_set_2128 = calc11_set_2129 := by decide +kernel

theorem calc11_set_2130_eq : calc11_card_2118.envelope ∩ calc11_set_2129 = calc11_set_2130 := by decide +kernel

theorem calc11_set_2131_eq : calc11_set_2126 ∪ calc11_set_2130 = calc11_set_2131 := by decide +kernel

theorem calc11_finishA_2132 : calc11_set_2131.erase (4, 8) = inline_897.required := by decide +kernel

theorem calc11_finishT_2132 : insert (4, 8) calc11_set_2127 = inline_897.envelope := by decide +kernel

theorem eq_inline_897 : inline_897 = combine (4, 8) [placed 0 (3, 5) card_88, placed 4 (7, 5) card_231, placed 3 (8, 6) card_267, inline_896] := by
  rw [calc11_card_2117_eq, calc11_card_2118_eq, calc11_card_2119_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2120_eq, calc11_set_2122_eq, calc11_set_2124_eq, calc11_set_2126_eq, calc11_set_2128_eq, calc11_set_2129_eq, calc11_set_2130_eq, calc11_set_2131_eq, calc11_finishA_2132]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2121_eq, calc11_set_2123_eq, calc11_set_2125_eq, calc11_set_2127_eq, calc11_finishT_2132]
  · decide +kernel

theorem valid_inline_897 : Valid inline_897 := by
  rw [eq_inline_897]
  apply combination_rule (4, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 5) valid_88
  rcases hc with rfl | hc
  · exact placed_valid 4 (7, 5) valid_231
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 6) valid_267
  subst c
  exact valid_inline_896

theorem calc11_card_2133_eq : placed 3 (9, 5) card_523 = calc11_card_2133 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2134_eq : placed 3 (9, 5) card_524 = calc11_card_2134 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2135_eq : placed 1 (1, 5) card_677 = calc11_card_2135 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2136_eq : placed 7 (10, 10) card_719 = calc11_card_2136 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2137_eq : placed 6 (8, 13) card_723 = calc11_card_2137 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_2138_eq : calc11_card_2137.required ∪ ∅ = calc11_set_2138 := by decide +kernel

theorem calc11_set_2139_eq : calc11_card_2137.envelope ∪ ∅ = calc11_set_2139 := by decide +kernel

theorem calc11_set_2140_eq : inline_897.required ∪ calc11_set_2138 = calc11_set_2140 := by decide +kernel

theorem calc11_set_2141_eq : inline_897.envelope ∪ calc11_set_2139 = calc11_set_2141 := by decide +kernel

theorem calc11_set_2142_eq : inline_895.required ∪ calc11_set_2140 = calc11_set_2142 := by decide +kernel

theorem calc11_set_2143_eq : inline_895.envelope ∪ calc11_set_2141 = calc11_set_2143 := by decide +kernel

theorem calc11_set_2144_eq : inline_894.required ∪ calc11_set_2142 = calc11_set_2144 := by decide +kernel

theorem calc11_set_2145_eq : inline_894.envelope ∪ calc11_set_2143 = calc11_set_2145 := by decide +kernel

theorem calc11_set_2146_eq : calc11_card_2136.required ∪ calc11_set_2144 = calc11_set_2146 := by decide +kernel

theorem calc11_set_2147_eq : calc11_card_2136.envelope ∪ calc11_set_2145 = calc11_set_2147 := by decide +kernel

theorem calc11_set_2148_eq : inline_893.required ∪ calc11_set_2146 = calc11_set_2148 := by decide +kernel

theorem calc11_set_2149_eq : inline_893.envelope ∪ calc11_set_2147 = calc11_set_2149 := by decide +kernel

theorem calc11_set_2150_eq : inline_889.required ∪ calc11_set_2148 = calc11_set_2150 := by decide +kernel

theorem calc11_set_2151_eq : inline_889.envelope ∪ calc11_set_2149 = calc11_set_2151 := by decide +kernel

theorem calc11_set_2152_eq : calc11_card_2135.required ∪ calc11_set_2150 = calc11_set_2152 := by decide +kernel

theorem calc11_set_2153_eq : calc11_card_2135.envelope ∪ calc11_set_2151 = calc11_set_2153 := by decide +kernel

theorem calc11_set_2154_eq : calc11_card_2134.required ∪ calc11_set_2152 = calc11_set_2154 := by decide +kernel

theorem calc11_set_2155_eq : calc11_card_2134.envelope ∪ calc11_set_2153 = calc11_set_2155 := by decide +kernel

theorem calc11_set_2156_eq : calc11_card_2133.required ∪ calc11_set_2154 = calc11_set_2156 := by decide +kernel

theorem calc11_set_2157_eq : calc11_card_2133.envelope ∪ calc11_set_2155 = calc11_set_2157 := by decide +kernel

theorem calc11_set_2158_eq : calc11_card_2137.envelope ∩ calc11_card_2133.envelope = calc11_set_2158 := by decide +kernel

theorem calc11_set_2159_eq : inline_897.envelope ∩ calc11_set_2158 = calc11_set_2159 := by decide +kernel

theorem calc11_set_2160_eq : inline_895.envelope ∩ calc11_set_2159 = calc11_set_2160 := by decide +kernel

theorem calc11_set_2161_eq : inline_894.envelope ∩ calc11_set_2160 = calc11_set_2161 := by decide +kernel

theorem calc11_set_2162_eq : calc11_card_2136.envelope ∩ calc11_set_2161 = calc11_set_2162 := by decide +kernel

theorem calc11_set_2163_eq : inline_893.envelope ∩ calc11_set_2162 = calc11_set_2163 := by decide +kernel

theorem calc11_set_2164_eq : inline_889.envelope ∩ calc11_set_2163 = calc11_set_2164 := by decide +kernel

theorem calc11_set_2165_eq : calc11_card_2135.envelope ∩ calc11_set_2164 = calc11_set_2165 := by decide +kernel

theorem calc11_set_2166_eq : calc11_card_2134.envelope ∩ calc11_set_2165 = calc11_set_2166 := by decide +kernel

theorem calc11_set_2167_eq : calc11_set_2156 ∪ calc11_set_2166 = calc11_set_2167 := by decide +kernel

theorem calc11_finishA_2168 : calc11_set_2167.erase (6, 8) = card_724.required := by decide +kernel

theorem calc11_finishT_2168 : insert (6, 8) calc11_set_2157 = card_724.envelope := by decide +kernel

theorem eq_card_724 : card_724 = combine (6, 8) [placed 3 (9, 5) card_523, placed 3 (9, 5) card_524, placed 1 (1, 5) card_677, inline_889, inline_893, placed 7 (10, 10) card_719, inline_894, inline_895, inline_897, placed 6 (8, 13) card_723] := by
  rw [calc11_card_2133_eq, calc11_card_2134_eq, calc11_card_2135_eq, calc11_card_2136_eq, calc11_card_2137_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2138_eq, calc11_set_2140_eq, calc11_set_2142_eq, calc11_set_2144_eq, calc11_set_2146_eq, calc11_set_2148_eq, calc11_set_2150_eq, calc11_set_2152_eq, calc11_set_2154_eq, calc11_set_2156_eq, calc11_set_2158_eq, calc11_set_2159_eq, calc11_set_2160_eq, calc11_set_2161_eq, calc11_set_2162_eq, calc11_set_2163_eq, calc11_set_2164_eq, calc11_set_2165_eq, calc11_set_2166_eq, calc11_set_2167_eq, calc11_finishA_2168]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2139_eq, calc11_set_2141_eq, calc11_set_2143_eq, calc11_set_2145_eq, calc11_set_2147_eq, calc11_set_2149_eq, calc11_set_2151_eq, calc11_set_2153_eq, calc11_set_2155_eq, calc11_set_2157_eq, calc11_finishT_2168]
  · decide +kernel

theorem valid_724 : Valid card_724 := by
  rw [eq_card_724]
  apply combination_rule (6, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (9, 5) valid_523
  rcases hc with rfl | hc
  · exact placed_valid 3 (9, 5) valid_524
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 5) valid_677
  rcases hc with rfl | hc
  · exact valid_inline_889
  rcases hc with rfl | hc
  · exact valid_inline_893
  rcases hc with rfl | hc
  · exact placed_valid 7 (10, 10) valid_719
  rcases hc with rfl | hc
  · exact valid_inline_894
  rcases hc with rfl | hc
  · exact valid_inline_895
  rcases hc with rfl | hc
  · exact valid_inline_897
  subst c
  exact placed_valid 6 (8, 13) valid_723


end OAI.Snaky21.Certificate

theorem solution : Valid card_724 ∧ True :=
  ⟨valid_724, True.intro⟩
