-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block11_part19_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:26:11.33376+00:00
-- url     : https://prove2.me/submissions/0aa0829a-4880-4d96-b894-ff578cfe8825

import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block03_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block04_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part17_valid
import Definitions.Def_Snaky21Calc11Part09
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block10_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part18_valid
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
theorem valid_9 : Valid card_9 := block00_valid.2.2.2.2.2.2.2.2.2.1
theorem valid_13 : Valid card_13 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_44 : Valid card_44 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_46 : Valid card_46 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_52 : Valid card_52 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_53 : Valid card_53 := block00_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_82 : Valid card_82 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_90 : Valid card_90 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_99 : Valid card_99 := block01_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_145 : Valid card_145 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_176 : Valid card_176 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_180 : Valid card_180 := block02_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_192 : Valid card_192 := block03_valid.1
theorem valid_218 : Valid card_218 := block03_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_310 : Valid card_310 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_314 : Valid card_314 := block04_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_321 : Valid card_321 := block05_valid.2.1
theorem valid_328 : Valid card_328 := block05_valid.2.2.2.2.2.2.2.2.1
theorem valid_330 : Valid card_330 := block05_valid.2.2.2.2.2.2.2.2.2.2.1
theorem valid_369 : Valid card_369 := block05_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_435 : Valid card_435 := block06_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_474 : Valid card_474 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_477 : Valid card_477 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_721 : Valid card_721 := block11_part17_valid.1
theorem valid_722 : Valid card_722 := block11_part18_valid.1

theorem calc11_card_1835_eq : placed 6 (5, 7) card_46 = calc11_card_1835 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1836_eq : placed 0 (2, 1) card_321 = calc11_card_1836 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1837_eq : calc11_card_1836.required ∪ ∅ = calc11_set_1837 := by decide +kernel

theorem calc11_set_1838_eq : calc11_card_1836.envelope ∪ ∅ = calc11_set_1838 := by decide +kernel

theorem calc11_set_1839_eq : calc11_card_1835.required ∪ calc11_set_1837 = calc11_set_1839 := by decide +kernel

theorem calc11_set_1840_eq : calc11_card_1835.envelope ∪ calc11_set_1838 = calc11_set_1840 := by decide +kernel

theorem calc11_set_1841_eq : calc11_card_1836.envelope ∩ calc11_card_1835.envelope = calc11_set_1841 := by decide +kernel

theorem calc11_set_1842_eq : calc11_set_1839 ∪ calc11_set_1841 = calc11_set_1842 := by decide +kernel

theorem calc11_finishA_1843 : calc11_set_1842.erase (4, 5) = inline_880.required := by decide +kernel

theorem calc11_finishT_1843 : insert (4, 5) calc11_set_1840 = inline_880.envelope := by decide +kernel

theorem eq_inline_880 : inline_880 = combine (4, 5) [placed 6 (5, 7) card_46, placed 0 (2, 1) card_321] := by
  rw [calc11_card_1835_eq, calc11_card_1836_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1837_eq, calc11_set_1839_eq, calc11_set_1841_eq, calc11_set_1842_eq, calc11_finishA_1843]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1838_eq, calc11_set_1840_eq, calc11_finishT_1843]
  · decide +kernel

theorem valid_inline_880 : Valid inline_880 := by
  rw [eq_inline_880]
  apply combination_rule (4, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (5, 7) valid_46
  subst c
  exact placed_valid 0 (2, 1) valid_321

theorem calc11_card_1844_eq : placed 6 (3, 8) card_53 = calc11_card_1844 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1845_eq : placed 0 (2, 2) card_53 = calc11_card_1845 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1846_eq : placed 1 (1, 4) card_310 = calc11_card_1846 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1847_eq : calc11_card_1846.required ∪ ∅ = calc11_set_1847 := by decide +kernel

theorem calc11_set_1848_eq : calc11_card_1846.envelope ∪ ∅ = calc11_set_1848 := by decide +kernel

theorem calc11_set_1849_eq : calc11_card_1845.required ∪ calc11_set_1847 = calc11_set_1849 := by decide +kernel

theorem calc11_set_1850_eq : calc11_card_1845.envelope ∪ calc11_set_1848 = calc11_set_1850 := by decide +kernel

theorem calc11_set_1851_eq : calc11_card_1844.required ∪ calc11_set_1849 = calc11_set_1851 := by decide +kernel

theorem calc11_set_1852_eq : calc11_card_1844.envelope ∪ calc11_set_1850 = calc11_set_1852 := by decide +kernel

theorem calc11_set_1853_eq : calc11_card_1846.envelope ∩ calc11_card_1844.envelope = calc11_set_1853 := by decide +kernel

theorem calc11_set_1854_eq : calc11_card_1845.envelope ∩ calc11_set_1853 = calc11_set_1854 := by decide +kernel

theorem calc11_set_1855_eq : calc11_set_1851 ∪ calc11_set_1854 = calc11_set_1855 := by decide +kernel

theorem calc11_finishA_1856 : calc11_set_1855.erase (2, 4) = inline_881.required := by decide +kernel

theorem calc11_finishT_1856 : insert (2, 4) calc11_set_1852 = inline_881.envelope := by decide +kernel

theorem eq_inline_881 : inline_881 = combine (2, 4) [placed 6 (3, 8) card_53, placed 0 (2, 2) card_53, placed 1 (1, 4) card_310] := by
  rw [calc11_card_1844_eq, calc11_card_1845_eq, calc11_card_1846_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1847_eq, calc11_set_1849_eq, calc11_set_1851_eq, calc11_set_1853_eq, calc11_set_1854_eq, calc11_set_1855_eq, calc11_finishA_1856]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1848_eq, calc11_set_1850_eq, calc11_set_1852_eq, calc11_finishT_1856]
  · decide +kernel

theorem valid_inline_881 : Valid inline_881 := by
  rw [eq_inline_881]
  apply combination_rule (2, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 8) valid_53
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 2) valid_53
  subst c
  exact placed_valid 1 (1, 4) valid_310

theorem calc11_card_1857_eq : placed 6 (4, 8) card_9 = calc11_card_1857 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1858_eq : placed 5 (2, 7) card_90 = calc11_card_1858 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1859_eq : placed 3 (6, 4) card_99 = calc11_card_1859 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1860_eq : calc11_card_1859.required ∪ ∅ = calc11_set_1860 := by decide +kernel

theorem calc11_set_1861_eq : calc11_card_1859.envelope ∪ ∅ = calc11_set_1861 := by decide +kernel

theorem calc11_set_1862_eq : calc11_card_1858.required ∪ calc11_set_1860 = calc11_set_1862 := by decide +kernel

theorem calc11_set_1863_eq : calc11_card_1858.envelope ∪ calc11_set_1861 = calc11_set_1863 := by decide +kernel

theorem calc11_set_1864_eq : calc11_card_1857.required ∪ calc11_set_1862 = calc11_set_1864 := by decide +kernel

theorem calc11_set_1865_eq : calc11_card_1857.envelope ∪ calc11_set_1863 = calc11_set_1865 := by decide +kernel

theorem calc11_set_1866_eq : calc11_card_1859.envelope ∩ calc11_card_1857.envelope = calc11_set_1866 := by decide +kernel

theorem calc11_set_1867_eq : calc11_card_1858.envelope ∩ calc11_set_1866 = calc11_set_1867 := by decide +kernel

theorem calc11_set_1868_eq : calc11_set_1864 ∪ calc11_set_1867 = calc11_set_1868 := by decide +kernel

theorem calc11_finishA_1869 : calc11_set_1868.erase (3, 4) = inline_882.required := by decide +kernel

theorem calc11_finishT_1869 : insert (3, 4) calc11_set_1865 = inline_882.envelope := by decide +kernel

theorem eq_inline_882 : inline_882 = combine (3, 4) [placed 6 (4, 8) card_9, placed 5 (2, 7) card_90, placed 3 (6, 4) card_99] := by
  rw [calc11_card_1857_eq, calc11_card_1858_eq, calc11_card_1859_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1860_eq, calc11_set_1862_eq, calc11_set_1864_eq, calc11_set_1866_eq, calc11_set_1867_eq, calc11_set_1868_eq, calc11_finishA_1869]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1861_eq, calc11_set_1863_eq, calc11_set_1865_eq, calc11_finishT_1869]
  · decide +kernel

theorem valid_inline_882 : Valid inline_882 := by
  rw [eq_inline_882]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (4, 8) valid_9
  rcases hc with rfl | hc
  · exact placed_valid 5 (2, 7) valid_90
  subst c
  exact placed_valid 3 (6, 4) valid_99

theorem calc11_card_1870_eq : placed 6 (3, 8) card_44 = calc11_card_1870 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1871_eq : placed 6 (3, 8) card_52 = calc11_card_1871 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1872_eq : placed 3 (5, 4) card_180 = calc11_card_1872 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1873_eq : inline_882.required ∪ ∅ = calc11_set_1873 := by decide +kernel

theorem calc11_set_1874_eq : inline_882.envelope ∪ ∅ = calc11_set_1874 := by decide +kernel

theorem calc11_set_1875_eq : calc11_card_1872.required ∪ calc11_set_1873 = calc11_set_1875 := by decide +kernel

theorem calc11_set_1876_eq : calc11_card_1872.envelope ∪ calc11_set_1874 = calc11_set_1876 := by decide +kernel

theorem calc11_set_1877_eq : calc11_card_1871.required ∪ calc11_set_1875 = calc11_set_1877 := by decide +kernel

theorem calc11_set_1878_eq : calc11_card_1871.envelope ∪ calc11_set_1876 = calc11_set_1878 := by decide +kernel

theorem calc11_set_1879_eq : calc11_card_1870.required ∪ calc11_set_1877 = calc11_set_1879 := by decide +kernel

theorem calc11_set_1880_eq : calc11_card_1870.envelope ∪ calc11_set_1878 = calc11_set_1880 := by decide +kernel

theorem calc11_set_1881_eq : inline_882.envelope ∩ calc11_card_1870.envelope = calc11_set_1881 := by decide +kernel

theorem calc11_set_1882_eq : calc11_card_1872.envelope ∩ calc11_set_1881 = calc11_set_1882 := by decide +kernel

theorem calc11_set_1883_eq : calc11_card_1871.envelope ∩ calc11_set_1882 = calc11_set_1883 := by decide +kernel

theorem calc11_set_1884_eq : calc11_set_1879 ∪ calc11_set_1883 = calc11_set_1884 := by decide +kernel

theorem calc11_finishA_1885 : calc11_set_1884.erase (3, 7) = inline_883.required := by decide +kernel

theorem calc11_finishT_1885 : insert (3, 7) calc11_set_1880 = inline_883.envelope := by decide +kernel

theorem eq_inline_883 : inline_883 = combine (3, 7) [placed 6 (3, 8) card_44, placed 6 (3, 8) card_52, placed 3 (5, 4) card_180, inline_882] := by
  rw [calc11_card_1870_eq, calc11_card_1871_eq, calc11_card_1872_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1873_eq, calc11_set_1875_eq, calc11_set_1877_eq, calc11_set_1879_eq, calc11_set_1881_eq, calc11_set_1882_eq, calc11_set_1883_eq, calc11_set_1884_eq, calc11_finishA_1885]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1874_eq, calc11_set_1876_eq, calc11_set_1878_eq, calc11_set_1880_eq, calc11_finishT_1885]
  · decide +kernel

theorem valid_inline_883 : Valid inline_883 := by
  rw [eq_inline_883]
  apply combination_rule (3, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 8) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 8) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 4) valid_180
  subst c
  exact valid_inline_882

theorem calc11_card_1886_eq : placed 0 (2, 4) card_82 = calc11_card_1886 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1887_eq : placed 2 (2, 8) card_176 = calc11_card_1887 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1888_eq : placed 1 (2, 5) card_218 = calc11_card_1888 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1889_eq : placed 6 (6, 10) card_369 = calc11_card_1889 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1890_eq : calc11_card_1889.required ∪ ∅ = calc11_set_1890 := by decide +kernel

theorem calc11_set_1891_eq : calc11_card_1889.envelope ∪ ∅ = calc11_set_1891 := by decide +kernel

theorem calc11_set_1892_eq : calc11_card_1888.required ∪ calc11_set_1890 = calc11_set_1892 := by decide +kernel

theorem calc11_set_1893_eq : calc11_card_1888.envelope ∪ calc11_set_1891 = calc11_set_1893 := by decide +kernel

theorem calc11_set_1894_eq : calc11_card_1887.required ∪ calc11_set_1892 = calc11_set_1894 := by decide +kernel

theorem calc11_set_1895_eq : calc11_card_1887.envelope ∪ calc11_set_1893 = calc11_set_1895 := by decide +kernel

theorem calc11_set_1896_eq : calc11_card_1886.required ∪ calc11_set_1894 = calc11_set_1896 := by decide +kernel

theorem calc11_set_1897_eq : calc11_card_1886.envelope ∪ calc11_set_1895 = calc11_set_1897 := by decide +kernel

theorem calc11_set_1898_eq : calc11_card_1889.envelope ∩ calc11_card_1886.envelope = calc11_set_1898 := by decide +kernel

theorem calc11_set_1899_eq : calc11_card_1888.envelope ∩ calc11_set_1898 = calc11_set_1899 := by decide +kernel

theorem calc11_set_1900_eq : calc11_card_1887.envelope ∩ calc11_set_1899 = calc11_set_1900 := by decide +kernel

theorem calc11_set_1901_eq : calc11_set_1896 ∪ calc11_set_1900 = calc11_set_1901 := by decide +kernel

theorem calc11_finishA_1902 : calc11_set_1901.erase (5, 6) = inline_884.required := by decide +kernel

theorem calc11_finishT_1902 : insert (5, 6) calc11_set_1897 = inline_884.envelope := by decide +kernel

theorem eq_inline_884 : inline_884 = combine (5, 6) [placed 0 (2, 4) card_82, placed 2 (2, 8) card_176, placed 1 (2, 5) card_218, placed 6 (6, 10) card_369] := by
  rw [calc11_card_1886_eq, calc11_card_1887_eq, calc11_card_1888_eq, calc11_card_1889_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1890_eq, calc11_set_1892_eq, calc11_set_1894_eq, calc11_set_1896_eq, calc11_set_1898_eq, calc11_set_1899_eq, calc11_set_1900_eq, calc11_set_1901_eq, calc11_finishA_1902]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1891_eq, calc11_set_1893_eq, calc11_set_1895_eq, calc11_set_1897_eq, calc11_finishT_1902]
  · decide +kernel

theorem valid_inline_884 : Valid inline_884 := by
  rw [eq_inline_884]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (2, 4) valid_82
  rcases hc with rfl | hc
  · exact placed_valid 2 (2, 8) valid_176
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 5) valid_218
  subst c
  exact placed_valid 6 (6, 10) valid_369

theorem calc11_card_1903_eq : placed 1 (2, 4) card_145 = calc11_card_1903 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1904_eq : placed 5 (2, 7) card_314 = calc11_card_1904 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1905_eq : calc11_card_1904.required ∪ ∅ = calc11_set_1905 := by decide +kernel

theorem calc11_set_1906_eq : calc11_card_1904.envelope ∪ ∅ = calc11_set_1906 := by decide +kernel

theorem calc11_set_1907_eq : calc11_card_1903.required ∪ calc11_set_1905 = calc11_set_1907 := by decide +kernel

theorem calc11_set_1908_eq : calc11_card_1903.envelope ∪ calc11_set_1906 = calc11_set_1908 := by decide +kernel

theorem calc11_set_1909_eq : calc11_card_1904.envelope ∩ calc11_card_1903.envelope = calc11_set_1909 := by decide +kernel

theorem calc11_set_1910_eq : calc11_set_1907 ∪ calc11_set_1909 = calc11_set_1910 := by decide +kernel

theorem calc11_finishA_1911 : calc11_set_1910.erase (3, 4) = inline_885.required := by decide +kernel

theorem calc11_finishT_1911 : insert (3, 4) calc11_set_1908 = inline_885.envelope := by decide +kernel

theorem eq_inline_885 : inline_885 = combine (3, 4) [placed 1 (2, 4) card_145, placed 5 (2, 7) card_314] := by
  rw [calc11_card_1903_eq, calc11_card_1904_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1905_eq, calc11_set_1907_eq, calc11_set_1909_eq, calc11_set_1910_eq, calc11_finishA_1911]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1906_eq, calc11_set_1908_eq, calc11_finishT_1911]
  · decide +kernel

theorem valid_inline_885 : Valid inline_885 := by
  rw [eq_inline_885]
  apply combination_rule (3, 4) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_145
  subst c
  exact placed_valid 5 (2, 7) valid_314

theorem calc11_card_1912_eq : placed 6 (3, 8) card_44 = calc11_card_1912 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1913_eq : placed 6 (3, 8) card_52 = calc11_card_1913 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1914_eq : placed 3 (5, 4) card_180 = calc11_card_1914 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1915_eq : inline_885.required ∪ ∅ = calc11_set_1915 := by decide +kernel

theorem calc11_set_1916_eq : inline_885.envelope ∪ ∅ = calc11_set_1916 := by decide +kernel

theorem calc11_set_1917_eq : calc11_card_1914.required ∪ calc11_set_1915 = calc11_set_1917 := by decide +kernel

theorem calc11_set_1918_eq : calc11_card_1914.envelope ∪ calc11_set_1916 = calc11_set_1918 := by decide +kernel

theorem calc11_set_1919_eq : calc11_card_1913.required ∪ calc11_set_1917 = calc11_set_1919 := by decide +kernel

theorem calc11_set_1920_eq : calc11_card_1913.envelope ∪ calc11_set_1918 = calc11_set_1920 := by decide +kernel

theorem calc11_set_1921_eq : calc11_card_1912.required ∪ calc11_set_1919 = calc11_set_1921 := by decide +kernel

theorem calc11_set_1922_eq : calc11_card_1912.envelope ∪ calc11_set_1920 = calc11_set_1922 := by decide +kernel

theorem calc11_set_1923_eq : inline_885.envelope ∩ calc11_card_1912.envelope = calc11_set_1923 := by decide +kernel

theorem calc11_set_1924_eq : calc11_card_1914.envelope ∩ calc11_set_1923 = calc11_set_1924 := by decide +kernel

theorem calc11_set_1925_eq : calc11_card_1913.envelope ∩ calc11_set_1924 = calc11_set_1925 := by decide +kernel

theorem calc11_set_1926_eq : calc11_set_1921 ∪ calc11_set_1925 = calc11_set_1926 := by decide +kernel

theorem calc11_finishA_1927 : calc11_set_1926.erase (3, 7) = inline_886.required := by decide +kernel

theorem calc11_finishT_1927 : insert (3, 7) calc11_set_1922 = inline_886.envelope := by decide +kernel

theorem eq_inline_886 : inline_886 = combine (3, 7) [placed 6 (3, 8) card_44, placed 6 (3, 8) card_52, placed 3 (5, 4) card_180, inline_885] := by
  rw [calc11_card_1912_eq, calc11_card_1913_eq, calc11_card_1914_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1915_eq, calc11_set_1917_eq, calc11_set_1919_eq, calc11_set_1921_eq, calc11_set_1923_eq, calc11_set_1924_eq, calc11_set_1925_eq, calc11_set_1926_eq, calc11_finishA_1927]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1916_eq, calc11_set_1918_eq, calc11_set_1920_eq, calc11_set_1922_eq, calc11_finishT_1927]
  · decide +kernel

theorem valid_inline_886 : Valid inline_886 := by
  rw [eq_inline_886]
  apply combination_rule (3, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 8) valid_44
  rcases hc with rfl | hc
  · exact placed_valid 6 (3, 8) valid_52
  rcases hc with rfl | hc
  · exact placed_valid 3 (5, 4) valid_180
  subst c
  exact valid_inline_885

theorem calc11_card_1928_eq : placed 4 (6, 3) card_13 = calc11_card_1928 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1929_eq : placed 2 (4, 9) card_192 = calc11_card_1929 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1930_eq : placed 6 (6, 10) card_369 = calc11_card_1930 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1931_eq : placed 1 (2, 4) card_435 = calc11_card_1931 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1932_eq : placed 1 (3, 4) card_474 = calc11_card_1932 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1933_eq : placed 5 (3, 8) card_477 = calc11_card_1933 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1934_eq : calc11_card_1933.required ∪ ∅ = calc11_set_1934 := by decide +kernel

theorem calc11_set_1935_eq : calc11_card_1933.envelope ∪ ∅ = calc11_set_1935 := by decide +kernel

theorem calc11_set_1936_eq : calc11_card_1932.required ∪ calc11_set_1934 = calc11_set_1936 := by decide +kernel

theorem calc11_set_1937_eq : calc11_card_1932.envelope ∪ calc11_set_1935 = calc11_set_1937 := by decide +kernel

theorem calc11_set_1938_eq : calc11_card_1931.required ∪ calc11_set_1936 = calc11_set_1938 := by decide +kernel

theorem calc11_set_1939_eq : calc11_card_1931.envelope ∪ calc11_set_1937 = calc11_set_1939 := by decide +kernel

theorem calc11_set_1940_eq : calc11_card_1930.required ∪ calc11_set_1938 = calc11_set_1940 := by decide +kernel

theorem calc11_set_1941_eq : calc11_card_1930.envelope ∪ calc11_set_1939 = calc11_set_1941 := by decide +kernel

theorem calc11_set_1942_eq : calc11_card_1929.required ∪ calc11_set_1940 = calc11_set_1942 := by decide +kernel

theorem calc11_set_1943_eq : calc11_card_1929.envelope ∪ calc11_set_1941 = calc11_set_1943 := by decide +kernel

theorem calc11_set_1944_eq : calc11_card_1928.required ∪ calc11_set_1942 = calc11_set_1944 := by decide +kernel

theorem calc11_set_1945_eq : calc11_card_1928.envelope ∪ calc11_set_1943 = calc11_set_1945 := by decide +kernel

theorem calc11_set_1946_eq : calc11_card_1933.envelope ∩ calc11_card_1928.envelope = calc11_set_1946 := by decide +kernel

theorem calc11_set_1947_eq : calc11_card_1932.envelope ∩ calc11_set_1946 = calc11_set_1947 := by decide +kernel

theorem calc11_set_1948_eq : calc11_card_1931.envelope ∩ calc11_set_1947 = calc11_set_1948 := by decide +kernel

theorem calc11_set_1949_eq : calc11_card_1930.envelope ∩ calc11_set_1948 = calc11_set_1949 := by decide +kernel

theorem calc11_set_1950_eq : calc11_card_1929.envelope ∩ calc11_set_1949 = calc11_set_1950 := by decide +kernel

theorem calc11_set_1951_eq : calc11_set_1944 ∪ calc11_set_1950 = calc11_set_1951 := by decide +kernel

theorem calc11_finishA_1952 : calc11_set_1951.erase (5, 6) = inline_887.required := by decide +kernel

theorem calc11_finishT_1952 : insert (5, 6) calc11_set_1945 = inline_887.envelope := by decide +kernel

theorem eq_inline_887 : inline_887 = combine (5, 6) [placed 4 (6, 3) card_13, placed 2 (4, 9) card_192, placed 6 (6, 10) card_369, placed 1 (2, 4) card_435, placed 1 (3, 4) card_474, placed 5 (3, 8) card_477] := by
  rw [calc11_card_1928_eq, calc11_card_1929_eq, calc11_card_1930_eq, calc11_card_1931_eq, calc11_card_1932_eq, calc11_card_1933_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1934_eq, calc11_set_1936_eq, calc11_set_1938_eq, calc11_set_1940_eq, calc11_set_1942_eq, calc11_set_1944_eq, calc11_set_1946_eq, calc11_set_1947_eq, calc11_set_1948_eq, calc11_set_1949_eq, calc11_set_1950_eq, calc11_set_1951_eq, calc11_finishA_1952]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1935_eq, calc11_set_1937_eq, calc11_set_1939_eq, calc11_set_1941_eq, calc11_set_1943_eq, calc11_set_1945_eq, calc11_finishT_1952]
  · decide +kernel

theorem valid_inline_887 : Valid inline_887 := by
  rw [eq_inline_887]
  apply combination_rule (5, 6) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 4 (6, 3) valid_13
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 9) valid_192
  rcases hc with rfl | hc
  · exact placed_valid 6 (6, 10) valid_369
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 4) valid_435
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 4) valid_474
  subst c
  exact placed_valid 5 (3, 8) valid_477

theorem calc11_card_1953_eq : placed 0 (0, 2) card_721 = calc11_card_1953 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1954_eq : placed 0 (1, 2) card_722 = calc11_card_1954 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1955_eq : calc11_card_1954.required ∪ ∅ = calc11_set_1955 := by decide +kernel

theorem calc11_set_1956_eq : calc11_card_1954.envelope ∪ ∅ = calc11_set_1956 := by decide +kernel

theorem calc11_set_1957_eq : calc11_card_1953.required ∪ calc11_set_1955 = calc11_set_1957 := by decide +kernel

theorem calc11_set_1958_eq : calc11_card_1953.envelope ∪ calc11_set_1956 = calc11_set_1958 := by decide +kernel

theorem calc11_set_1959_eq : inline_887.required ∪ calc11_set_1957 = calc11_set_1959 := by decide +kernel

theorem calc11_set_1960_eq : inline_887.envelope ∪ calc11_set_1958 = calc11_set_1960 := by decide +kernel

theorem calc11_set_1961_eq : inline_886.required ∪ calc11_set_1959 = calc11_set_1961 := by decide +kernel

theorem calc11_set_1962_eq : inline_886.envelope ∪ calc11_set_1960 = calc11_set_1962 := by decide +kernel

theorem calc11_set_1963_eq : inline_884.required ∪ calc11_set_1961 = calc11_set_1963 := by decide +kernel

theorem calc11_set_1964_eq : inline_884.envelope ∪ calc11_set_1962 = calc11_set_1964 := by decide +kernel

theorem calc11_set_1965_eq : inline_883.required ∪ calc11_set_1963 = calc11_set_1965 := by decide +kernel

theorem calc11_set_1966_eq : inline_883.envelope ∪ calc11_set_1964 = calc11_set_1966 := by decide +kernel

theorem calc11_set_1967_eq : calc11_card_1954.envelope ∩ inline_883.envelope = calc11_set_1967 := by decide +kernel

theorem calc11_set_1968_eq : calc11_card_1953.envelope ∩ calc11_set_1967 = calc11_set_1968 := by decide +kernel

theorem calc11_set_1969_eq : inline_887.envelope ∩ calc11_set_1968 = calc11_set_1969 := by decide +kernel

theorem calc11_set_1970_eq : inline_886.envelope ∩ calc11_set_1969 = calc11_set_1970 := by decide +kernel

theorem calc11_set_1971_eq : inline_884.envelope ∩ calc11_set_1970 = calc11_set_1971 := by decide +kernel

theorem calc11_set_1972_eq : calc11_set_1965 ∪ calc11_set_1971 = calc11_set_1972 := by decide +kernel

theorem calc11_finishA_1973 : calc11_set_1972.erase (5, 7) = inline_888.required := by decide +kernel

theorem calc11_finishT_1973 : insert (5, 7) calc11_set_1966 = inline_888.envelope := by decide +kernel

theorem eq_inline_888 : inline_888 = combine (5, 7) [inline_883, inline_884, inline_886, inline_887, placed 0 (0, 2) card_721, placed 0 (1, 2) card_722] := by
  rw [calc11_card_1953_eq, calc11_card_1954_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1955_eq, calc11_set_1957_eq, calc11_set_1959_eq, calc11_set_1961_eq, calc11_set_1963_eq, calc11_set_1965_eq, calc11_set_1967_eq, calc11_set_1968_eq, calc11_set_1969_eq, calc11_set_1970_eq, calc11_set_1971_eq, calc11_set_1972_eq, calc11_finishA_1973]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1956_eq, calc11_set_1958_eq, calc11_set_1960_eq, calc11_set_1962_eq, calc11_set_1964_eq, calc11_set_1966_eq, calc11_finishT_1973]
  · decide +kernel

theorem valid_inline_888 : Valid inline_888 := by
  rw [eq_inline_888]
  apply combination_rule (5, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact valid_inline_883
  rcases hc with rfl | hc
  · exact valid_inline_884
  rcases hc with rfl | hc
  · exact valid_inline_886
  rcases hc with rfl | hc
  · exact valid_inline_887
  rcases hc with rfl | hc
  · exact placed_valid 0 (0, 2) valid_721
  subst c
  exact placed_valid 0 (1, 2) valid_722

theorem calc11_card_1974_eq : placed 0 (1, 1) card_328 = calc11_card_1974 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_1975_eq : placed 0 (1, 1) card_330 = calc11_card_1975 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_1976_eq : inline_888.required ∪ ∅ = calc11_set_1976 := by decide +kernel

theorem calc11_set_1977_eq : inline_888.envelope ∪ ∅ = calc11_set_1977 := by decide +kernel

theorem calc11_set_1978_eq : inline_881.required ∪ calc11_set_1976 = calc11_set_1978 := by decide +kernel

theorem calc11_set_1979_eq : inline_881.envelope ∪ calc11_set_1977 = calc11_set_1979 := by decide +kernel

theorem calc11_set_1980_eq : inline_880.required ∪ calc11_set_1978 = calc11_set_1980 := by decide +kernel

theorem calc11_set_1981_eq : inline_880.envelope ∪ calc11_set_1979 = calc11_set_1981 := by decide +kernel

theorem calc11_set_1982_eq : calc11_card_1975.required ∪ calc11_set_1980 = calc11_set_1982 := by decide +kernel

theorem calc11_set_1983_eq : calc11_card_1975.envelope ∪ calc11_set_1981 = calc11_set_1983 := by decide +kernel

theorem calc11_set_1984_eq : calc11_card_1974.required ∪ calc11_set_1982 = calc11_set_1984 := by decide +kernel

theorem calc11_set_1985_eq : calc11_card_1974.envelope ∪ calc11_set_1983 = calc11_set_1985 := by decide +kernel

theorem calc11_set_1986_eq : inline_888.envelope ∩ calc11_card_1974.envelope = calc11_set_1986 := by decide +kernel

theorem calc11_set_1987_eq : inline_881.envelope ∩ calc11_set_1986 = calc11_set_1987 := by decide +kernel

theorem calc11_set_1988_eq : inline_880.envelope ∩ calc11_set_1987 = calc11_set_1988 := by decide +kernel

theorem calc11_set_1989_eq : calc11_card_1975.envelope ∩ calc11_set_1988 = calc11_set_1989 := by decide +kernel

theorem calc11_set_1990_eq : calc11_set_1984 ∪ calc11_set_1989 = calc11_set_1990 := by decide +kernel

theorem calc11_finishA_1991 : calc11_set_1990.erase (5, 5) = card_723.required := by decide +kernel

theorem calc11_finishT_1991 : insert (5, 5) calc11_set_1985 = card_723.envelope := by decide +kernel

theorem eq_card_723 : card_723 = combine (5, 5) [placed 0 (1, 1) card_328, placed 0 (1, 1) card_330, inline_880, inline_881, inline_888] := by
  rw [calc11_card_1974_eq, calc11_card_1975_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1976_eq, calc11_set_1978_eq, calc11_set_1980_eq, calc11_set_1982_eq, calc11_set_1984_eq, calc11_set_1986_eq, calc11_set_1987_eq, calc11_set_1988_eq, calc11_set_1989_eq, calc11_set_1990_eq, calc11_finishA_1991]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_1977_eq, calc11_set_1979_eq, calc11_set_1981_eq, calc11_set_1983_eq, calc11_set_1985_eq, calc11_finishT_1991]
  · decide +kernel

theorem valid_723 : Valid card_723 := by
  rw [eq_card_723]
  apply combination_rule (5, 5) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_328
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_330
  rcases hc with rfl | hc
  · exact valid_inline_880
  rcases hc with rfl | hc
  · exact valid_inline_881
  subst c
  exact valid_inline_888


end OAI.Snaky21.Certificate

theorem solution : Valid card_723 ∧ True :=
  ⟨valid_723, True.intro⟩
