-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block11_part05_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:06:40.054078+00:00
-- url     : https://prove2.me/submissions/ae81c495-0bb9-4d9c-b99e-7d96b56192d2

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Definitions.Def_Snaky21Calc11Part02
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block10_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part04_valid
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
theorem valid_6 : Valid card_6 := block00_valid.2.2.2.2.2.2.1
theorem valid_11 : Valid card_11 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_14 : Valid card_14 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_53 : Valid card_53 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_56 : Valid card_56 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_89 : Valid card_89 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_116 : Valid card_116 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_181 : Valid card_181 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_253 : Valid card_253 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_392 : Valid card_392 := block06_valid.2.2.2.2.2.2.2.2.1
theorem valid_521 : Valid card_521 := block08_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_524 : Valid card_524 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_536 : Valid card_536 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_545 : Valid card_545 := block08_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_655 : Valid card_655 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_664 : Valid card_664 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem calc11_card_809_eq : placed 1 (2, 5) card_53 = calc11_card_809 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_810_eq : placed 5 (2, 7) card_56 = calc11_card_810 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_811_eq : placed 0 (4, 3) card_392 = calc11_card_811 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_812_eq : calc11_card_811.required ∪ ∅ = calc11_set_812 := by decide +kernel

theorem calc11_set_813_eq : calc11_card_811.envelope ∪ ∅ = calc11_set_813 := by decide +kernel

theorem calc11_set_814_eq : calc11_card_810.required ∪ calc11_set_812 = calc11_set_814 := by decide +kernel

theorem calc11_set_815_eq : calc11_card_810.envelope ∪ calc11_set_813 = calc11_set_815 := by decide +kernel

theorem calc11_set_816_eq : calc11_card_809.required ∪ calc11_set_814 = calc11_set_816 := by decide +kernel

theorem calc11_set_817_eq : calc11_card_809.envelope ∪ calc11_set_815 = calc11_set_817 := by decide +kernel

theorem calc11_set_818_eq : calc11_card_811.envelope ∩ calc11_card_809.envelope = calc11_set_818 := by decide +kernel

theorem calc11_set_819_eq : calc11_card_810.envelope ∩ calc11_set_818 = calc11_set_819 := by decide +kernel

theorem calc11_set_820_eq : calc11_set_816 ∪ calc11_set_819 = calc11_set_820 := by decide +kernel

theorem calc11_finishA_821 : calc11_set_820.erase (4, 5) = inline_832.required := by decide +kernel

theorem calc11_finishT_821 : insert (4, 5) calc11_set_817 = inline_832.envelope := by decide +kernel

theorem eq_inline_832 : inline_832 = combine (4, 5) [placed 1 (2, 5) card_53, placed 5 (2, 7) card_56, placed 0 (4, 3) card_392] := by
  rw [calc11_card_809_eq, calc11_card_810_eq, calc11_card_811_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_812_eq, calc11_set_814_eq, calc11_set_816_eq, calc11_set_818_eq, calc11_set_819_eq, calc11_set_820_eq, calc11_finishA_821]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_813_eq, calc11_set_815_eq, calc11_set_817_eq, calc11_finishT_821]
  · decide +kernel

theorem valid_inline_832 : Valid inline_832 := by
  rw [eq_inline_832]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 5) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 7) valid_56
  subst c
  exact placed_valid 0 (4, 3) valid_392

theorem calc11_card_822_eq : placed 2 (5, 8) card_11 = calc11_card_822 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_823_eq : placed 7 (8, 7) card_253 = calc11_card_823 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_824_eq : inline_832.required ∪ ∅ = calc11_set_824 := by decide +kernel

theorem calc11_set_825_eq : inline_832.envelope ∪ ∅ = calc11_set_825 := by decide +kernel

theorem calc11_set_826_eq : calc11_card_823.required ∪ calc11_set_824 = calc11_set_826 := by decide +kernel

theorem calc11_set_827_eq : calc11_card_823.envelope ∪ calc11_set_825 = calc11_set_827 := by decide +kernel

theorem calc11_set_828_eq : calc11_card_822.required ∪ calc11_set_826 = calc11_set_828 := by decide +kernel

theorem calc11_set_829_eq : calc11_card_822.envelope ∪ calc11_set_827 = calc11_set_829 := by decide +kernel

theorem calc11_set_830_eq : inline_832.envelope ∩ calc11_card_822.envelope = calc11_set_830 := by decide +kernel

theorem calc11_set_831_eq : calc11_card_823.envelope ∩ calc11_set_830 = calc11_set_831 := by decide +kernel

theorem calc11_set_832_eq : calc11_set_828 ∪ calc11_set_831 = calc11_set_832 := by decide +kernel

theorem calc11_finishA_833 : calc11_set_832.erase (5, 4) = inline_833.required := by decide +kernel

theorem calc11_finishT_833 : insert (5, 4) calc11_set_829 = inline_833.envelope := by decide +kernel

theorem eq_inline_833 : inline_833 = combine (5, 4) [placed 2 (5, 8) card_11, placed 7 (8, 7) card_253, inline_832] := by
  rw [calc11_card_822_eq, calc11_card_823_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_824_eq, calc11_set_826_eq, calc11_set_828_eq, calc11_set_830_eq, calc11_set_831_eq, calc11_set_832_eq, calc11_finishA_833]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_825_eq, calc11_set_827_eq, calc11_set_829_eq, calc11_finishT_833]
  · decide +kernel

theorem valid_inline_833 : Valid inline_833 := by
  rw [eq_inline_833]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 8) valid_11
  rcases hc with rfl | hc
  · exact placed_valid 7 (8, 7) valid_253
  subst c
  exact valid_inline_832

theorem calc11_card_834_eq : placed 2 (5, 7) card_6 = calc11_card_834 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_835_eq : placed 6 (6, 6) card_89 = calc11_card_835 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_836_eq : calc11_card_835.required ∪ ∅ = calc11_set_836 := by decide +kernel

theorem calc11_set_837_eq : calc11_card_835.envelope ∪ ∅ = calc11_set_837 := by decide +kernel

theorem calc11_set_838_eq : calc11_card_834.required ∪ calc11_set_836 = calc11_set_838 := by decide +kernel

theorem calc11_set_839_eq : calc11_card_834.envelope ∪ calc11_set_837 = calc11_set_839 := by decide +kernel

theorem calc11_set_840_eq : calc11_card_835.envelope ∩ calc11_card_834.envelope = calc11_set_840 := by decide +kernel

theorem calc11_set_841_eq : calc11_set_838 ∪ calc11_set_840 = calc11_set_841 := by decide +kernel

theorem calc11_finishA_842 : calc11_set_841.erase (5, 3) = inline_834.required := by decide +kernel

theorem calc11_finishT_842 : insert (5, 3) calc11_set_839 = inline_834.envelope := by decide +kernel

theorem eq_inline_834 : inline_834 = combine (5, 3) [placed 2 (5, 7) card_6, placed 6 (6, 6) card_89] := by
  rw [calc11_card_834_eq, calc11_card_835_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_836_eq, calc11_set_838_eq, calc11_set_840_eq, calc11_set_841_eq, calc11_finishA_842]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_837_eq, calc11_set_839_eq, calc11_finishT_842]
  · decide +kernel

theorem valid_inline_834 : Valid inline_834 := by
  rw [eq_inline_834]
  apply combination_rule (5, 3) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 7) valid_6
  subst c
  exact placed_valid 6 (6, 6) valid_89

theorem calc11_card_843_eq : placed 2 (5, 8) card_11 = calc11_card_843 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_844_eq : placed 2 (4, 8) card_521 = calc11_card_844 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_845_eq : inline_834.required ∪ ∅ = calc11_set_845 := by decide +kernel

theorem calc11_set_846_eq : inline_834.envelope ∪ ∅ = calc11_set_846 := by decide +kernel

theorem calc11_set_847_eq : calc11_card_844.required ∪ calc11_set_845 = calc11_set_847 := by decide +kernel

theorem calc11_set_848_eq : calc11_card_844.envelope ∪ calc11_set_846 = calc11_set_848 := by decide +kernel

theorem calc11_set_849_eq : calc11_card_843.required ∪ calc11_set_847 = calc11_set_849 := by decide +kernel

theorem calc11_set_850_eq : calc11_card_843.envelope ∪ calc11_set_848 = calc11_set_850 := by decide +kernel

theorem calc11_set_851_eq : inline_834.envelope ∩ calc11_card_843.envelope = calc11_set_851 := by decide +kernel

theorem calc11_set_852_eq : calc11_card_844.envelope ∩ calc11_set_851 = calc11_set_852 := by decide +kernel

theorem calc11_set_853_eq : calc11_set_849 ∪ calc11_set_852 = calc11_set_853 := by decide +kernel

theorem calc11_finishA_854 : calc11_set_853.erase (5, 4) = inline_835.required := by decide +kernel

theorem calc11_finishT_854 : insert (5, 4) calc11_set_850 = inline_835.envelope := by decide +kernel

theorem eq_inline_835 : inline_835 = combine (5, 4) [placed 2 (5, 8) card_11, placed 2 (4, 8) card_521, inline_834] := by
  rw [calc11_card_843_eq, calc11_card_844_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_845_eq, calc11_set_847_eq, calc11_set_849_eq, calc11_set_851_eq, calc11_set_852_eq, calc11_set_853_eq, calc11_finishA_854]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_846_eq, calc11_set_848_eq, calc11_set_850_eq, calc11_finishT_854]
  · decide +kernel

theorem valid_inline_835 : Valid inline_835 := by
  rw [eq_inline_835]
  apply combination_rule (5, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 2 (5, 8) valid_11
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 8) valid_521
  subst c
  exact valid_inline_834

theorem calc11_card_855_eq : placed 3 (9, 3) card_524 = calc11_card_855 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_856_eq : placed 7 (9, 9) card_536 = calc11_card_856 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_857_eq : placed 7 (10, 7) card_545 = calc11_card_857 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_858_eq : placed 3 (10, 3) card_655 = calc11_card_858 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_859_eq : placed 2 (1, 11) card_664 = calc11_card_859 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_860_eq : inline_835.required ∪ ∅ = calc11_set_860 := by decide +kernel

theorem calc11_set_861_eq : inline_835.envelope ∪ ∅ = calc11_set_861 := by decide +kernel

theorem calc11_set_862_eq : inline_833.required ∪ calc11_set_860 = calc11_set_862 := by decide +kernel

theorem calc11_set_863_eq : inline_833.envelope ∪ calc11_set_861 = calc11_set_863 := by decide +kernel

theorem calc11_set_864_eq : calc11_card_859.required ∪ calc11_set_862 = calc11_set_864 := by decide +kernel

theorem calc11_set_865_eq : calc11_card_859.envelope ∪ calc11_set_863 = calc11_set_865 := by decide +kernel

theorem calc11_set_866_eq : calc11_card_858.required ∪ calc11_set_864 = calc11_set_866 := by decide +kernel

theorem calc11_set_867_eq : calc11_card_858.envelope ∪ calc11_set_865 = calc11_set_867 := by decide +kernel

theorem calc11_set_868_eq : calc11_card_857.required ∪ calc11_set_866 = calc11_set_868 := by decide +kernel

theorem calc11_set_869_eq : calc11_card_857.envelope ∪ calc11_set_867 = calc11_set_869 := by decide +kernel

theorem calc11_set_870_eq : calc11_card_856.required ∪ calc11_set_868 = calc11_set_870 := by decide +kernel

theorem calc11_set_871_eq : calc11_card_856.envelope ∪ calc11_set_869 = calc11_set_871 := by decide +kernel

theorem calc11_set_872_eq : calc11_card_855.required ∪ calc11_set_870 = calc11_set_872 := by decide +kernel

theorem calc11_set_873_eq : calc11_card_855.envelope ∪ calc11_set_871 = calc11_set_873 := by decide +kernel

theorem calc11_set_874_eq : inline_835.envelope ∩ calc11_card_855.envelope = calc11_set_874 := by decide +kernel

theorem calc11_set_875_eq : inline_833.envelope ∩ calc11_set_874 = calc11_set_875 := by decide +kernel

theorem calc11_set_876_eq : calc11_card_859.envelope ∩ calc11_set_875 = calc11_set_876 := by decide +kernel

theorem calc11_set_877_eq : calc11_card_858.envelope ∩ calc11_set_876 = calc11_set_877 := by decide +kernel

theorem calc11_set_878_eq : calc11_card_857.envelope ∩ calc11_set_877 = calc11_set_878 := by decide +kernel

theorem calc11_set_879_eq : calc11_card_856.envelope ∩ calc11_set_878 = calc11_set_879 := by decide +kernel

theorem calc11_set_880_eq : calc11_set_872 ∪ calc11_set_879 = calc11_set_880 := by decide +kernel

theorem calc11_finishA_881 : calc11_set_880.erase (6, 6) = inline_836.required := by decide +kernel

theorem calc11_finishT_881 : insert (6, 6) calc11_set_873 = inline_836.envelope := by decide +kernel

theorem eq_inline_836 : inline_836 = combine (6, 6) [placed 3 (9, 3) card_524, placed 7 (9, 9) card_536, placed 7 (10, 7) card_545, placed 3 (10, 3) card_655, placed 2 (1, 11) card_664, inline_833, inline_835] := by
  rw [calc11_card_855_eq, calc11_card_856_eq, calc11_card_857_eq, calc11_card_858_eq, calc11_card_859_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_860_eq, calc11_set_862_eq, calc11_set_864_eq, calc11_set_866_eq, calc11_set_868_eq, calc11_set_870_eq, calc11_set_872_eq, calc11_set_874_eq, calc11_set_875_eq, calc11_set_876_eq, calc11_set_877_eq, calc11_set_878_eq, calc11_set_879_eq, calc11_set_880_eq, calc11_finishA_881]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_861_eq, calc11_set_863_eq, calc11_set_865_eq, calc11_set_867_eq, calc11_set_869_eq, calc11_set_871_eq, calc11_set_873_eq, calc11_finishT_881]
  · decide +kernel

theorem valid_inline_836 : Valid inline_836 := by
  rw [eq_inline_836]
  apply combination_rule (6, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 3 (9, 3) valid_524
  rcases hc with rfl | hc
  · exact placed_valid 7 (9, 9) valid_536
  rcases hc with rfl | hc
  · exact placed_valid 7 (10, 7) valid_545
  rcases hc with rfl | hc
  · exact placed_valid 3 (10, 3) valid_655
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 11) valid_664
  rcases hc with rfl | hc
  · exact valid_inline_833
  subst c
  exact valid_inline_835

theorem calc11_card_882_eq : placed 4 (6, 3) card_14 = calc11_card_882 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_883_eq : placed 3 (8, 4) card_116 = calc11_card_883 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_884_eq : placed 3 (7, 4) card_181 = calc11_card_884 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_885_eq : inline_836.required ∪ ∅ = calc11_set_885 := by decide +kernel

theorem calc11_set_886_eq : inline_836.envelope ∪ ∅ = calc11_set_886 := by decide +kernel

theorem calc11_set_887_eq : calc11_card_884.required ∪ calc11_set_885 = calc11_set_887 := by decide +kernel

theorem calc11_set_888_eq : calc11_card_884.envelope ∪ calc11_set_886 = calc11_set_888 := by decide +kernel

theorem calc11_set_889_eq : calc11_card_883.required ∪ calc11_set_887 = calc11_set_889 := by decide +kernel

theorem calc11_set_890_eq : calc11_card_883.envelope ∪ calc11_set_888 = calc11_set_890 := by decide +kernel

theorem calc11_set_891_eq : calc11_card_882.required ∪ calc11_set_889 = calc11_set_891 := by decide +kernel

theorem calc11_set_892_eq : calc11_card_882.envelope ∪ calc11_set_890 = calc11_set_892 := by decide +kernel

theorem calc11_set_893_eq : inline_836.envelope ∩ calc11_card_882.envelope = calc11_set_893 := by decide +kernel

theorem calc11_set_894_eq : calc11_card_884.envelope ∩ calc11_set_893 = calc11_set_894 := by decide +kernel

theorem calc11_set_895_eq : calc11_card_883.envelope ∩ calc11_set_894 = calc11_set_895 := by decide +kernel

theorem calc11_set_896_eq : calc11_set_891 ∪ calc11_set_895 = calc11_set_896 := by decide +kernel

theorem calc11_finishA_897 : calc11_set_896.erase (5, 7) = card_709.required := by decide +kernel

theorem calc11_finishT_897 : insert (5, 7) calc11_set_892 = card_709.envelope := by decide +kernel

theorem eq_card_709 : card_709 = combine (5, 7) [placed 4 (6, 3) card_14, placed 3 (8, 4) card_116, placed 3 (7, 4) card_181, inline_836] := by
  rw [calc11_card_882_eq, calc11_card_883_eq, calc11_card_884_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_885_eq, calc11_set_887_eq, calc11_set_889_eq, calc11_set_891_eq, calc11_set_893_eq, calc11_set_894_eq, calc11_set_895_eq, calc11_set_896_eq, calc11_finishA_897]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_886_eq, calc11_set_888_eq, calc11_set_890_eq, calc11_set_892_eq, calc11_finishT_897]
  · decide +kernel

theorem valid_709 : Valid card_709 := by
  rw [eq_card_709]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_14
  rcases hc with rfl | hc
  · exact placed_valid 3 (8, 4) valid_116
  rcases hc with rfl | hc
  · exact placed_valid 3 (7, 4) valid_181
  subst c
  exact valid_inline_836


end OAI.Snaky21.Certificate

theorem solution : Valid card_709 ∧ True :=
  ⟨valid_709, True.intro⟩
