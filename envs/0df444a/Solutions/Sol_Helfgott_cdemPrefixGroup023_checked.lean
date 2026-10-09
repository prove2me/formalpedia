-- Prove2me | solution 1 for Helfgott.cdemPrefixGroup023_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:24:58.964603+00:00
-- url     : https://prove2.me/submissions/2934427c-1f04-445d-aad0-fa31616e397c

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
set_option autoImplicit false
set_option Elab.async false
open Finset
open scoped BigOperators
namespace Helfgott

lemma cdem_prefix023_repair_join (g : ℕ → ℤ) (a c b : ℕ)
    (ha : a ≤ c) (hb : c ≤ b)
    (N Q : ℕ) (m1 m2 f1 f2 r1 r2 : ℤ) (s1 s2 : ℕ)
    (h1 : (∑ n ∈ Ico a c, g n) = m1 ∧
      (∑ n ∈ Ico a c, (g n).natAbs) = s1 ∧
      (∑ n ∈ Ico a c, g n*(N/n : ℕ)) = f1 ∧
      (∑ n ∈ Ico a c, g n*(Q/n : ℕ)) = r1)
    (h2 : (∑ n ∈ Ico c b, g n) = m2 ∧
      (∑ n ∈ Ico c b, (g n).natAbs) = s2 ∧
      (∑ n ∈ Ico c b, g n*(N/n : ℕ)) = f2 ∧
      (∑ n ∈ Ico c b, g n*(Q/n : ℕ)) = r2) :
    (∑ n ∈ Ico a b, g n) = m1+m2 ∧
    (∑ n ∈ Ico a b, (g n).natAbs) = s1+s2 ∧
    (∑ n ∈ Ico a b, g n*(N/n : ℕ)) = f1+f2 ∧
    (∑ n ∈ Ico a b, g n*(Q/n : ℕ)) = r1+r2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Finset.sum_Ico_consecutive g ha hb).symm.trans
      (congrArg₂ (fun u v : ℤ => u+v) h1.1 h2.1)
  · exact (Finset.sum_Ico_consecutive (fun n => (g n).natAbs) ha hb).symm.trans
      (congrArg₂ (fun u v : ℕ => u+v) h1.2.1 h2.2.1)
  · exact (Finset.sum_Ico_consecutive (fun n => g n*(N/n : ℕ)) ha hb).symm.trans
      (congrArg₂ (fun u v : ℤ => u+v) h1.2.2.1 h2.2.2.1)
  · exact (Finset.sum_Ico_consecutive (fun n => g n*(Q/n : ℕ)) ha hb).symm.trans
      (congrArg₂ (fun u v : ℤ => u+v) h1.2.2.2 h2.2.2.2)

end Helfgott
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset
open scoped BigOperators
namespace Helfgott
private theorem cdemPrefixStats_94208_94272 :
    (∑ n ∈ Ico 94208 94272, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 94208 94272, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 94208 94272, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (106097 : ℤ) ∧
    (∑ n ∈ Ico 94208 94272, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2121903324548583009993557801 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_94272_94336 :
    (∑ n ∈ Ico 94272 94336, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 94272 94336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 94272 94336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-158940 : ℤ) ∧
    (∑ n ∈ Ico 94272 94336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3178839954076282603380011059 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_94208_94336 :
    (∑ n ∈ Ico 94208 94336, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 94208 94336, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 94208 94336, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-52843 : ℤ) ∧
    (∑ n ∈ Ico 94208 94336, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1056936629527699593386453258 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    94208 94272 94336 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (2 : ℤ) (-3 : ℤ) (106097 : ℤ) (-158940 : ℤ) (2121903324548583009993557801 : ℤ) (-3178839954076282603380011059 : ℤ) 36 41
    cdemPrefixStats_94208_94272 cdemPrefixStats_94272_94336
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_94336_94400 :
    (∑ n ∈ Ico 94336 94400, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 94336 94400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 94336 94400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-688635 : ℤ) ∧
    (∑ n ∈ Ico 94336 94400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13772824857886559968433392452 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_94400_94464 :
    (∑ n ∈ Ico 94400 94464, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 94400 94464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 94400 94464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-529376 : ℤ) ∧
    (∑ n ∈ Ico 94400 94464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10587623572297295971332622216 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_94336_94464 :
    (∑ n ∈ Ico 94336 94464, mobiusTreeValue 16 mobiusTable1200001 n) = (-23 : ℤ) ∧
    (∑ n ∈ Ico 94336 94464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 94336 94464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1218011 : ℤ) ∧
    (∑ n ∈ Ico 94336 94464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-24360448430183855939766014668 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    94336 94400 94464 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-13 : ℤ) (-10 : ℤ) (-688635 : ℤ) (-529376 : ℤ) (-13772824857886559968433392452 : ℤ) (-10587623572297295971332622216 : ℤ) 41 38
    cdemPrefixStats_94336_94400 cdemPrefixStats_94400_94464
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_94208_94464 :
    (∑ n ∈ Ico 94208 94464, mobiusTreeValue 16 mobiusTable1200001 n) = (-24 : ℤ) ∧
    (∑ n ∈ Ico 94208 94464, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 94208 94464, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1270854 : ℤ) ∧
    (∑ n ∈ Ico 94208 94464, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-25417385059711555533152467926 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    94208 94336 94464 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-1 : ℤ) (-23 : ℤ) (-52843 : ℤ) (-1218011 : ℤ) (-1056936629527699593386453258 : ℤ) (-24360448430183855939766014668 : ℤ) 77 79
    cdemPrefixStats_94208_94336 cdemPrefixStats_94336_94464
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_94464_94528 :
    (∑ n ∈ Ico 94464 94528, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 94464 94528, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 94464 94528, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (105837 : ℤ) ∧
    (∑ n ∈ Ico 94464 94528, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2116805037033168573335322780 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_94528_94592 :
    (∑ n ∈ Ico 94528 94592, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 94528 94592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 94528 94592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-52971 : ℤ) ∧
    (∑ n ∈ Ico 94528 94592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1059408464794636387601107680 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_94464_94592 :
    (∑ n ∈ Ico 94464 94592, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 94464 94592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 94464 94592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (52866 : ℤ) ∧
    (∑ n ∈ Ico 94464 94592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1057396572238532185734215100 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    94464 94528 94592 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (2 : ℤ) (-1 : ℤ) (105837 : ℤ) (-52971 : ℤ) (2116805037033168573335322780 : ℤ) (-1059408464794636387601107680 : ℤ) 36 39
    cdemPrefixStats_94464_94528 cdemPrefixStats_94528_94592
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_94592_94656 :
    (∑ n ∈ Ico 94592 94656, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 94592 94656, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 94592 94656, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-369735 : ℤ) ∧
    (∑ n ∈ Ico 94592 94656, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7394819318351755231755301567 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_94656_94720 :
    (∑ n ∈ Ico 94656 94720, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 94656 94720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 94656 94720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (633705 : ℤ) ∧
    (∑ n ∈ Ico 94656 94720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12674249352010454205304095912 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_94592_94720 :
    (∑ n ∈ Ico 94592 94720, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 94592 94720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 94592 94720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (263970 : ℤ) ∧
    (∑ n ∈ Ico 94592 94720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5279430033658698973548794345 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    94592 94656 94720 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-7 : ℤ) (12 : ℤ) (-369735 : ℤ) (633705 : ℤ) (-7394819318351755231755301567 : ℤ) (12674249352010454205304095912 : ℤ) 39 40
    cdemPrefixStats_94592_94656 cdemPrefixStats_94656_94720
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_94464_94720 :
    (∑ n ∈ Ico 94464 94720, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 94464 94720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 94464 94720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (316836 : ℤ) ∧
    (∑ n ∈ Ico 94464 94720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6336826605897231159283009445 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    94464 94592 94720 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (1 : ℤ) (5 : ℤ) (52866 : ℤ) (263970 : ℤ) (1057396572238532185734215100 : ℤ) (5279430033658698973548794345 : ℤ) 75 79
    cdemPrefixStats_94464_94592 cdemPrefixStats_94592_94720
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_94208_94720 :
    (∑ n ∈ Ico 94208 94720, mobiusTreeValue 16 mobiusTable1200001 n) = (-18 : ℤ) ∧
    (∑ n ∈ Ico 94208 94720, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 94208 94720, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-954018 : ℤ) ∧
    (∑ n ∈ Ico 94208 94720, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19080558453814324373869458481 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    94208 94464 94720 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-24 : ℤ) (6 : ℤ) (-1270854 : ℤ) (316836 : ℤ) (-25417385059711555533152467926 : ℤ) (6336826605897231159283009445 : ℤ) 156 154
    cdemPrefixStats_94208_94464 cdemPrefixStats_94464_94720
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_94720_94784 :
    (∑ n ∈ Ico 94720 94784, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 94720 94784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 94720 94784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-52738 : ℤ) ∧
    (∑ n ∈ Ico 94720 94784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1054752303958276720962706682 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_94784_94848 :
    (∑ n ∈ Ico 94784 94848, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 94784 94848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 94784 94848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-580013 : ℤ) ∧
    (∑ n ∈ Ico 94784 94848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11600361710162224725905646688 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_94720_94848 :
    (∑ n ∈ Ico 94720 94848, mobiusTreeValue 16 mobiusTable1200001 n) = (-12 : ℤ) ∧
    (∑ n ∈ Ico 94720 94848, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (80 : ℕ) ∧
    (∑ n ∈ Ico 94720 94848, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-632751 : ℤ) ∧
    (∑ n ∈ Ico 94720 94848, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12655114014120501446868353370 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    94720 94784 94848 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-1 : ℤ) (-11 : ℤ) (-52738 : ℤ) (-580013 : ℤ) (-1054752303958276720962706682 : ℤ) (-11600361710162224725905646688 : ℤ) 39 41
    cdemPrefixStats_94720_94784 cdemPrefixStats_94784_94848
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_94848_94912 :
    (∑ n ∈ Ico 94848 94912, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 94848 94912, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 94848 94912, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (158163 : ℤ) ∧
    (∑ n ∈ Ico 94848 94912, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3163298961092020308968412214 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_94912_94976 :
    (∑ n ∈ Ico 94912 94976, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 94912 94976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 94912 94976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-315989 : ℤ) ∧
    (∑ n ∈ Ico 94912 94976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6319791769978390774671140527 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_94848_94976 :
    (∑ n ∈ Ico 94848 94976, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 94848 94976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 94848 94976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-157826 : ℤ) ∧
    (∑ n ∈ Ico 94848 94976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3156492808886370465702728313 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    94848 94912 94976 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (3 : ℤ) (-6 : ℤ) (158163 : ℤ) (-315989 : ℤ) (3163298961092020308968412214 : ℤ) (-6319791769978390774671140527 : ℤ) 41 38
    cdemPrefixStats_94848_94912 cdemPrefixStats_94912_94976
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_94720_94976 :
    (∑ n ∈ Ico 94720 94976, mobiusTreeValue 16 mobiusTable1200001 n) = (-15 : ℤ) ∧
    (∑ n ∈ Ico 94720 94976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (159 : ℕ) ∧
    (∑ n ∈ Ico 94720 94976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-790577 : ℤ) ∧
    (∑ n ∈ Ico 94720 94976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-15811606823006871912571081683 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    94720 94848 94976 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-12 : ℤ) (-3 : ℤ) (-632751 : ℤ) (-157826 : ℤ) (-12655114014120501446868353370 : ℤ) (-3156492808886370465702728313 : ℤ) 80 79
    cdemPrefixStats_94720_94848 cdemPrefixStats_94848_94976
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_94976_95040 :
    (∑ n ∈ Ico 94976 95040, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 94976 95040, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 94976 95040, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (8 : ℤ) ∧
    (∑ n ∈ Ico 94976 95040, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (188369950492245273950522 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_95040_95104 :
    (∑ n ∈ Ico 95040 95104, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 95040 95104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 95040 95104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-52463 : ℤ) ∧
    (∑ n ∈ Ico 95040 95104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1049201301329638544150732782 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_94976_95104 :
    (∑ n ∈ Ico 94976 95104, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 94976 95104, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 94976 95104, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-52455 : ℤ) ∧
    (∑ n ∈ Ico 94976 95104, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1049012931379146298876782260 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    94976 95040 95104 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (0 : ℤ) (-1 : ℤ) (8 : ℤ) (-52463 : ℤ) (188369950492245273950522 : ℤ) (-1049201301329638544150732782 : ℤ) 36 39
    cdemPrefixStats_94976_95040 cdemPrefixStats_95040_95104
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_95104_95168 :
    (∑ n ∈ Ico 95104 95168, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 95104 95168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 95104 95168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-157719 : ℤ) ∧
    (∑ n ∈ Ico 95104 95168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3154397007778733186597156676 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_95168_95232 :
    (∑ n ∈ Ico 95168 95232, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 95168 95232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 95168 95232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (97 : ℤ) ∧
    (∑ n ∈ Ico 95168 95232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1865115420907491350391238 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_95104_95232 :
    (∑ n ∈ Ico 95104 95232, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 95104 95232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 95104 95232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-157622 : ℤ) ∧
    (∑ n ∈ Ico 95104 95232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3152531892357825695246765438 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    95104 95168 95232 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-3 : ℤ) (0 : ℤ) (-157719 : ℤ) (97 : ℤ) (-3154397007778733186597156676 : ℤ) (1865115420907491350391238 : ℤ) 37 40
    cdemPrefixStats_95104_95168 cdemPrefixStats_95168_95232
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_94976_95232 :
    (∑ n ∈ Ico 94976 95232, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 94976 95232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (152 : ℕ) ∧
    (∑ n ∈ Ico 94976 95232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-210077 : ℤ) ∧
    (∑ n ∈ Ico 94976 95232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4201544823736971994123547698 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    94976 95104 95232 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-1 : ℤ) (-3 : ℤ) (-52455 : ℤ) (-157622 : ℤ) (-1049012931379146298876782260 : ℤ) (-3152531892357825695246765438 : ℤ) 75 77
    cdemPrefixStats_94976_95104 cdemPrefixStats_95104_95232
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_94720_95232 :
    (∑ n ∈ Ico 94720 95232, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 94720 95232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (311 : ℕ) ∧
    (∑ n ∈ Ico 94720 95232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1000654 : ℤ) ∧
    (∑ n ∈ Ico 94720 95232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-20013151646743843906694629381 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    94720 94976 95232 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-15 : ℤ) (-4 : ℤ) (-790577 : ℤ) (-210077 : ℤ) (-15811606823006871912571081683 : ℤ) (-4201544823736971994123547698 : ℤ) 159 152
    cdemPrefixStats_94720_94976 cdemPrefixStats_94976_95232
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_94208_95232 :
    (∑ n ∈ Ico 94208 95232, mobiusTreeValue 16 mobiusTable1200001 n) = (-37 : ℤ) ∧
    (∑ n ∈ Ico 94208 95232, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (621 : ℕ) ∧
    (∑ n ∈ Ico 94208 95232, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1954672 : ℤ) ∧
    (∑ n ∈ Ico 94208 95232, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-39093710100558168280564087862 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    94208 94720 95232 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-18 : ℤ) (-19 : ℤ) (-954018 : ℤ) (-1000654 : ℤ) (-19080558453814324373869458481 : ℤ) (-20013151646743843906694629381 : ℤ) 310 311
    cdemPrefixStats_94208_94720 cdemPrefixStats_94720_95232
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_95232_95296 :
    (∑ n ∈ Ico 95232 95296, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 95232 95296, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 95232 95296, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-262536 : ℤ) ∧
    (∑ n ∈ Ico 95232 95296, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5250776314794330720164762700 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_95296_95360 :
    (∑ n ∈ Ico 95296 95360, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 95296 95360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 95296 95360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (209855 : ℤ) ∧
    (∑ n ∈ Ico 95296 95360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4197162039820302418639064270 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_95232_95360 :
    (∑ n ∈ Ico 95232 95360, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 95232 95360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 95232 95360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-52681 : ℤ) ∧
    (∑ n ∈ Ico 95232 95360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1053614274974028301525698430 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    95232 95296 95360 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-5 : ℤ) (4 : ℤ) (-262536 : ℤ) (209855 : ℤ) (-5250776314794330720164762700 : ℤ) (4197162039820302418639064270 : ℤ) 41 38
    cdemPrefixStats_95232_95296 cdemPrefixStats_95296_95360
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_95360_95424 :
    (∑ n ∈ Ico 95360 95424, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 95360 95424, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 95360 95424, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-104763 : ℤ) ∧
    (∑ n ∈ Ico 95360 95424, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2095260173591083004572622115 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_95424_95488 :
    (∑ n ∈ Ico 95424 95488, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 95424 95488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 95424 95488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-314199 : ℤ) ∧
    (∑ n ∈ Ico 95424 95488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6284016139222813757292012952 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_95360_95488 :
    (∑ n ∈ Ico 95360 95488, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 95360 95488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 95360 95488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-418962 : ℤ) ∧
    (∑ n ∈ Ico 95360 95488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8379276312813896761864635067 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    95360 95424 95488 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-2 : ℤ) (-6 : ℤ) (-104763 : ℤ) (-314199 : ℤ) (-2095260173591083004572622115 : ℤ) (-6284016139222813757292012952 : ℤ) 40 38
    cdemPrefixStats_95360_95424 cdemPrefixStats_95424_95488
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_95232_95488 :
    (∑ n ∈ Ico 95232 95488, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 95232 95488, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 95232 95488, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-471643 : ℤ) ∧
    (∑ n ∈ Ico 95232 95488, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9432890587787925063390333497 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    95232 95360 95488 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-1 : ℤ) (-8 : ℤ) (-52681 : ℤ) (-418962 : ℤ) (-1053614274974028301525698430 : ℤ) (-8379276312813896761864635067 : ℤ) 79 78
    cdemPrefixStats_95232_95360 cdemPrefixStats_95360_95488
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_95488_95552 :
    (∑ n ∈ Ico 95488 95552, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 95488 95552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 95488 95552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-366452 : ℤ) ∧
    (∑ n ∈ Ico 95488 95552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7329042730724245611403772874 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_95552_95616 :
    (∑ n ∈ Ico 95552 95616, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 95552 95616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 95552 95616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (366176 : ℤ) ∧
    (∑ n ∈ Ico 95552 95616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7323533099044804390704993026 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_95488_95616 :
    (∑ n ∈ Ico 95488 95616, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 95488 95616, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 95488 95616, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-276 : ℤ) ∧
    (∑ n ∈ Ico 95488 95616, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5509631679441220698779848 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    95488 95552 95616 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-7 : ℤ) (7 : ℤ) (-366452 : ℤ) (366176 : ℤ) (-7329042730724245611403772874 : ℤ) (7323533099044804390704993026 : ℤ) 39 39
    cdemPrefixStats_95488_95552 cdemPrefixStats_95552_95616
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_95616_95680 :
    (∑ n ∈ Ico 95616 95680, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 95616 95680, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 95616 95680, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (261284 : ℤ) ∧
    (∑ n ∈ Ico 95616 95680, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5225762860807221144729278915 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_95680_95744 :
    (∑ n ∈ Ico 95680 95744, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 95680 95744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 95680 95744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (156784 : ℤ) ∧
    (∑ n ∈ Ico 95680 95744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3135724661738440440519347915 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_95616_95744 :
    (∑ n ∈ Ico 95616 95744, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 95616 95744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 95616 95744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (418068 : ℤ) ∧
    (∑ n ∈ Ico 95616 95744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8361487522545661585248626830 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    95616 95680 95744 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (5 : ℤ) (3 : ℤ) (261284 : ℤ) (156784 : ℤ) (5225762860807221144729278915 : ℤ) (3135724661738440440519347915 : ℤ) 37 41
    cdemPrefixStats_95616_95680 cdemPrefixStats_95680_95744
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_95488_95744 :
    (∑ n ∈ Ico 95488 95744, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 95488 95744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 95488 95744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (417792 : ℤ) ∧
    (∑ n ∈ Ico 95488 95744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8355977890866220364549846982 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    95488 95616 95744 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (0 : ℤ) (8 : ℤ) (-276 : ℤ) (418068 : ℤ) (-5509631679441220698779848 : ℤ) (8361487522545661585248626830 : ℤ) 78 78
    cdemPrefixStats_95488_95616 cdemPrefixStats_95616_95744
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_95232_95744 :
    (∑ n ∈ Ico 95232 95744, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 95232 95744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (313 : ℕ) ∧
    (∑ n ∈ Ico 95232 95744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-53851 : ℤ) ∧
    (∑ n ∈ Ico 95232 95744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1076912696921704698840486515 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    95232 95488 95744 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-9 : ℤ) (8 : ℤ) (-471643 : ℤ) (417792 : ℤ) (-9432890587787925063390333497 : ℤ) (8355977890866220364549846982 : ℤ) 157 156
    cdemPrefixStats_95232_95488 cdemPrefixStats_95488_95744
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_95744_95808 :
    (∑ n ∈ Ico 95744 95808, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 95744 95808, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 95744 95808, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-469803 : ℤ) ∧
    (∑ n ∈ Ico 95744 95808, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9396141353035872398478033353 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_95808_95872 :
    (∑ n ∈ Ico 95808 95872, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 95808 95872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 95808 95872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-208722 : ℤ) ∧
    (∑ n ∈ Ico 95808 95872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4174461115126448574904831001 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_95744_95872 :
    (∑ n ∈ Ico 95744 95872, mobiusTreeValue 16 mobiusTable1200001 n) = (-13 : ℤ) ∧
    (∑ n ∈ Ico 95744 95872, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 95744 95872, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-678525 : ℤ) ∧
    (∑ n ∈ Ico 95744 95872, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-13570602468162320973382864354 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    95744 95808 95872 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-9 : ℤ) (-4 : ℤ) (-469803 : ℤ) (-208722 : ℤ) (-9396141353035872398478033353 : ℤ) (-4174461115126448574904831001 : ℤ) 37 40
    cdemPrefixStats_95744_95808 cdemPrefixStats_95808_95872
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_95872_95936 :
    (∑ n ∈ Ico 95872 95936, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 95872 95936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 95872 95936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-208510 : ℤ) ∧
    (∑ n ∈ Ico 95872 95936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4170283355292946210560719583 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_95936_96000 :
    (∑ n ∈ Ico 95936 96000, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 95936 96000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 95936 96000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-104186 : ℤ) ∧
    (∑ n ∈ Ico 95936 96000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2083702278555796551705616720 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_95872_96000 :
    (∑ n ∈ Ico 95872 96000, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 95872 96000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 95872 96000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-312696 : ℤ) ∧
    (∑ n ∈ Ico 95872 96000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6253985633848742762266336303 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    95872 95936 96000 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-4 : ℤ) (-2 : ℤ) (-208510 : ℤ) (-104186 : ℤ) (-4170283355292946210560719583 : ℤ) (-2083702278555796551705616720 : ℤ) 38 38
    cdemPrefixStats_95872_95936 cdemPrefixStats_95936_96000
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_95744_96000 :
    (∑ n ∈ Ico 95744 96000, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 95744 96000, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 95744 96000, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-991221 : ℤ) ∧
    (∑ n ∈ Ico 95744 96000, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-19824588102011063735649200657 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    95744 95872 96000 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-13 : ℤ) (-6 : ℤ) (-678525 : ℤ) (-312696 : ℤ) (-13570602468162320973382864354 : ℤ) (-6253985633848742762266336303 : ℤ) 77 76
    cdemPrefixStats_95744_95872 cdemPrefixStats_95872_96000
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_96000_96064 :
    (∑ n ∈ Ico 96000 96064, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 96000 96064, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 96000 96064, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (312311 : ℤ) ∧
    (∑ n ∈ Ico 96000 96064, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6246279953949368655729207954 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_96064_96128 :
    (∑ n ∈ Ico 96064 96128, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 96064 96128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 96064 96128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (780423 : ℤ) ∧
    (∑ n ∈ Ico 96064 96128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15608568406685088441902830612 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_96000_96128 :
    (∑ n ∈ Ico 96000 96128, mobiusTreeValue 16 mobiusTable1200001 n) = (21 : ℤ) ∧
    (∑ n ∈ Ico 96000 96128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 96000 96128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1092734 : ℤ) ∧
    (∑ n ∈ Ico 96000 96128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (21854848360634457097632038566 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    96000 96064 96128 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (6 : ℤ) (15 : ℤ) (312311 : ℤ) (780423 : ℤ) (6246279953949368655729207954 : ℤ) (15608568406685088441902830612 : ℤ) 40 39
    cdemPrefixStats_96000_96064 cdemPrefixStats_96064_96128
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_96128_96192 :
    (∑ n ∈ Ico 96128 96192, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 96128 96192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 96128 96192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-104036 : ℤ) ∧
    (∑ n ∈ Ico 96128 96192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2080743080441081627504401849 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_96192_96256 :
    (∑ n ∈ Ico 96192 96256, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 96192 96256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 96192 96256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-363931 : ℤ) ∧
    (∑ n ∈ Ico 96192 96256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7278666958125661161111878021 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_96128_96256 :
    (∑ n ∈ Ico 96128 96256, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 96128 96256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 96128 96256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-467967 : ℤ) ∧
    (∑ n ∈ Ico 96128 96256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9359410038566742788616279870 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    96128 96192 96256 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-2 : ℤ) (-7 : ℤ) (-104036 : ℤ) (-363931 : ℤ) (-2080743080441081627504401849 : ℤ) (-7278666958125661161111878021 : ℤ) 38 39
    cdemPrefixStats_96128_96192 cdemPrefixStats_96192_96256
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_96000_96256 :
    (∑ n ∈ Ico 96000 96256, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 96000 96256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 96000 96256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (624767 : ℤ) ∧
    (∑ n ∈ Ico 96000 96256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12495438322067714309015758696 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    96000 96128 96256 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (21 : ℤ) (-9 : ℤ) (1092734 : ℤ) (-467967 : ℤ) (21854848360634457097632038566 : ℤ) (-9359410038566742788616279870 : ℤ) 79 77
    cdemPrefixStats_96000_96128 cdemPrefixStats_96128_96256
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_95744_96256 :
    (∑ n ∈ Ico 95744 96256, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 95744 96256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 95744 96256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-366454 : ℤ) ∧
    (∑ n ∈ Ico 95744 96256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-7329149779943349426633441961 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    95744 96000 96256 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-19 : ℤ) (12 : ℤ) (-991221 : ℤ) (624767 : ℤ) (-19824588102011063735649200657 : ℤ) (12495438322067714309015758696 : ℤ) 153 156
    cdemPrefixStats_95744_96000 cdemPrefixStats_96000_96256
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_95232_96256 :
    (∑ n ∈ Ico 95232 96256, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 95232 96256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (622 : ℕ) ∧
    (∑ n ∈ Ico 95232 96256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-420305 : ℤ) ∧
    (∑ n ∈ Ico 95232 96256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8406062476865054125473928476 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    95232 95744 96256 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-1 : ℤ) (-7 : ℤ) (-53851 : ℤ) (-366454 : ℤ) (-1076912696921704698840486515 : ℤ) (-7329149779943349426633441961 : ℤ) 313 309
    cdemPrefixStats_95232_95744 cdemPrefixStats_95744_96256
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_94208_96256 :
    (∑ n ∈ Ico 94208 96256, mobiusTreeValue 16 mobiusTable1200001 n) = (-45 : ℤ) ∧
    (∑ n ∈ Ico 94208 96256, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1243 : ℕ) ∧
    (∑ n ∈ Ico 94208 96256, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2374977 : ℤ) ∧
    (∑ n ∈ Ico 94208 96256, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-47499772577423222406038016338 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    94208 95232 96256 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-37 : ℤ) (-8 : ℤ) (-1954672 : ℤ) (-420305 : ℤ) (-39093710100558168280564087862 : ℤ) (-8406062476865054125473928476 : ℤ) 621 622
    cdemPrefixStats_94208_95232 cdemPrefixStats_95232_96256
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_96256_96320 :
    (∑ n ∈ Ico 96256 96320, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 96256 96320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 96256 96320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-207741 : ℤ) ∧
    (∑ n ∈ Ico 96256 96320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4154840479698947918993381046 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_96320_96384 :
    (∑ n ∈ Ico 96320 96384, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 96320 96384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 96320 96384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (51752 : ℤ) ∧
    (∑ n ∈ Ico 96320 96384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1035092803791319554929630808 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_96256_96384 :
    (∑ n ∈ Ico 96256 96384, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 96256 96384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 96256 96384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-155989 : ℤ) ∧
    (∑ n ∈ Ico 96256 96384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3119747675907628364063750238 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    96256 96320 96384 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-4 : ℤ) (1 : ℤ) (-207741 : ℤ) (51752 : ℤ) (-4154840479698947918993381046 : ℤ) (1035092803791319554929630808 : ℤ) 40 37
    cdemPrefixStats_96256_96320 cdemPrefixStats_96320_96384
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_96384_96448 :
    (∑ n ∈ Ico 96384 96448, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 96384 96448, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 96384 96448, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-51835 : ℤ) ∧
    (∑ n ∈ Ico 96384 96448, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1036698912080927013136429501 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_96448_96512 :
    (∑ n ∈ Ico 96448 96512, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 96448 96512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 96448 96512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-207325 : ℤ) ∧
    (∑ n ∈ Ico 96448 96512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4146549469887467401979918590 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_96384_96512 :
    (∑ n ∈ Ico 96384 96512, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 96384 96512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 96384 96512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-259160 : ℤ) ∧
    (∑ n ∈ Ico 96384 96512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5183248381968394415116348091 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    96384 96448 96512 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-1 : ℤ) (-4 : ℤ) (-51835 : ℤ) (-207325 : ℤ) (-1036698912080927013136429501 : ℤ) (-4146549469887467401979918590 : ℤ) 39 38
    cdemPrefixStats_96384_96448 cdemPrefixStats_96448_96512
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_96256_96512 :
    (∑ n ∈ Ico 96256 96512, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 96256 96512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 96256 96512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-415149 : ℤ) ∧
    (∑ n ∈ Ico 96256 96512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8302996057876022779180098329 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    96256 96384 96512 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-3 : ℤ) (-5 : ℤ) (-155989 : ℤ) (-259160 : ℤ) (-3119747675907628364063750238 : ℤ) (-5183248381968394415116348091 : ℤ) 77 77
    cdemPrefixStats_96256_96384 cdemPrefixStats_96384_96512
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_96512_96576 :
    (∑ n ∈ Ico 96512 96576, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 96512 96576, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 96512 96576, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (310690 : ℤ) ∧
    (∑ n ∈ Ico 96512 96576, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6213860491976718143557651200 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_96576_96640 :
    (∑ n ∈ Ico 96576 96640, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 96576 96640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 96576 96640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (465696 : ℤ) ∧
    (∑ n ∈ Ico 96576 96640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9314027458921511233198668029 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_96512_96640 :
    (∑ n ∈ Ico 96512 96640, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 96512 96640, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 96512 96640, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (776386 : ℤ) ∧
    (∑ n ∈ Ico 96512 96640, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15527887950898229376756319229 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    96512 96576 96640 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (6 : ℤ) (9 : ℤ) (310690 : ℤ) (465696 : ℤ) (6213860491976718143557651200 : ℤ) (9314027458921511233198668029 : ℤ) 38 41
    cdemPrefixStats_96512_96576 cdemPrefixStats_96576_96640
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_96640_96704 :
    (∑ n ∈ Ico 96640 96704, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 96640 96704, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 96640 96704, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-51592 : ℤ) ∧
    (∑ n ∈ Ico 96640 96704, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1031879046289754553556987629 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_96704_96768 :
    (∑ n ∈ Ico 96704 96768, mobiusTreeValue 16 mobiusTable1200001 n) = (-9 : ℤ) ∧
    (∑ n ∈ Ico 96704 96768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 96704 96768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-465079 : ℤ) ∧
    (∑ n ∈ Ico 96704 96768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9301673814833311474676970568 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_96640_96768 :
    (∑ n ∈ Ico 96640 96768, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 96640 96768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 96640 96768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-516671 : ℤ) ∧
    (∑ n ∈ Ico 96640 96768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10333552861123066028233958197 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    96640 96704 96768 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-1 : ℤ) (-9 : ℤ) (-51592 : ℤ) (-465079 : ℤ) (-1031879046289754553556987629 : ℤ) (-9301673814833311474676970568 : ℤ) 39 37
    cdemPrefixStats_96640_96704 cdemPrefixStats_96704_96768
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_96512_96768 :
    (∑ n ∈ Ico 96512 96768, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 96512 96768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 96512 96768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (259715 : ℤ) ∧
    (∑ n ∈ Ico 96512 96768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5194335089775163348522361032 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    96512 96640 96768 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (15 : ℤ) (-10 : ℤ) (776386 : ℤ) (-516671 : ℤ) (15527887950898229376756319229 : ℤ) (-10333552861123066028233958197 : ℤ) 79 76
    cdemPrefixStats_96512_96640 cdemPrefixStats_96640_96768
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_96256_96768 :
    (∑ n ∈ Ico 96256 96768, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 96256 96768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 96256 96768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-155434 : ℤ) ∧
    (∑ n ∈ Ico 96256 96768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3108660968100859430657737297 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    96256 96512 96768 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-8 : ℤ) (5 : ℤ) (-415149 : ℤ) (259715 : ℤ) (-8302996057876022779180098329 : ℤ) (5194335089775163348522361032 : ℤ) 154 155
    cdemPrefixStats_96256_96512 cdemPrefixStats_96512_96768
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_96768_96832 :
    (∑ n ∈ Ico 96768 96832, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 96768 96832, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 96768 96832, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-154975 : ℤ) ∧
    (∑ n ∈ Ico 96768 96832, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3099557747102990307032084394 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_96832_96896 :
    (∑ n ∈ Ico 96832 96896, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 96832 96896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 96832 96896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-258156 : ℤ) ∧
    (∑ n ∈ Ico 96832 96896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-5163240948778869394900488202 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_96768_96896 :
    (∑ n ∈ Ico 96768 96896, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 96768 96896, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 96768 96896, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-413131 : ℤ) ∧
    (∑ n ∈ Ico 96768 96896, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8262798695881859701932572596 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    96768 96832 96896 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-3 : ℤ) (-5 : ℤ) (-154975 : ℤ) (-258156 : ℤ) (-3099557747102990307032084394 : ℤ) (-5163240948778869394900488202 : ℤ) 37 39
    cdemPrefixStats_96768_96832 cdemPrefixStats_96832_96896
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_96896_96960 :
    (∑ n ∈ Ico 96896 96960, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 96896 96960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 96896 96960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (206355 : ℤ) ∧
    (∑ n ∈ Ico 96896 96960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4127168443977095522728666731 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_96960_97024 :
    (∑ n ∈ Ico 96960 97024, mobiusTreeValue 16 mobiusTable1200001 n) = (3 : ℤ) ∧
    (∑ n ∈ Ico 96960 97024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (41 : ℕ) ∧
    (∑ n ∈ Ico 96960 97024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (154788 : ℤ) ∧
    (∑ n ∈ Ico 96960 97024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (3095760135231999440705113689 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_96896_97024 :
    (∑ n ∈ Ico 96896 97024, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 96896 97024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (81 : ℕ) ∧
    (∑ n ∈ Ico 96896 97024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (361143 : ℤ) ∧
    (∑ n ∈ Ico 96896 97024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7222928579209094963433780420 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    96896 96960 97024 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (4 : ℤ) (3 : ℤ) (206355 : ℤ) (154788 : ℤ) (4127168443977095522728666731 : ℤ) (3095760135231999440705113689 : ℤ) 40 41
    cdemPrefixStats_96896_96960 cdemPrefixStats_96960_97024
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_96768_97024 :
    (∑ n ∈ Ico 96768 97024, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 96768 97024, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (157 : ℕ) ∧
    (∑ n ∈ Ico 96768 97024, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-51988 : ℤ) ∧
    (∑ n ∈ Ico 96768 97024, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1039870116672764738498792176 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    96768 96896 97024 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-8 : ℤ) (7 : ℤ) (-413131 : ℤ) (361143 : ℤ) (-8262798695881859701932572596 : ℤ) (7222928579209094963433780420 : ℤ) 76 81
    cdemPrefixStats_96768_96896 cdemPrefixStats_96896_97024
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_97024_97088 :
    (∑ n ∈ Ico 97024 97088, mobiusTreeValue 16 mobiusTable1200001 n) = (18 : ℤ) ∧
    (∑ n ∈ Ico 97024 97088, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 97024 97088, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (927225 : ℤ) ∧
    (∑ n ∈ Ico 97024 97088, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18544699653813496255741362068 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_97088_97152 :
    (∑ n ∈ Ico 97088 97152, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 97088 97152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 97088 97152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (257349 : ℤ) ∧
    (∑ n ∈ Ico 97088 97152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5147030149064808084205326864 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_97024_97152 :
    (∑ n ∈ Ico 97024 97152, mobiusTreeValue 16 mobiusTable1200001 n) = (23 : ℤ) ∧
    (∑ n ∈ Ico 97024 97152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (75 : ℕ) ∧
    (∑ n ∈ Ico 97024 97152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1184574 : ℤ) ∧
    (∑ n ∈ Ico 97024 97152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (23691729802878304339946688932 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    97024 97088 97152 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (18 : ℤ) (5 : ℤ) (927225 : ℤ) (257349 : ℤ) (18544699653813496255741362068 : ℤ) (5147030149064808084205326864 : ℤ) 36 39
    cdemPrefixStats_97024_97088 cdemPrefixStats_97088_97152
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_97152_97216 :
    (∑ n ∈ Ico 97152 97216, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 97152 97216, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 97152 97216, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-154408 : ℤ) ∧
    (∑ n ∈ Ico 97152 97216, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3088198770212048380913083975 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_97216_97280 :
    (∑ n ∈ Ico 97216 97280, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 97216 97280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 97216 97280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (359932 : ℤ) ∧
    (∑ n ∈ Ico 97216 97280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7198726192714280285284916303 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_97152_97280 :
    (∑ n ∈ Ico 97152 97280, mobiusTreeValue 16 mobiusTable1200001 n) = (4 : ℤ) ∧
    (∑ n ∈ Ico 97152 97280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 97152 97280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (205524 : ℤ) ∧
    (∑ n ∈ Ico 97152 97280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (4110527422502231904371832328 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    97152 97216 97280 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-3 : ℤ) (7 : ℤ) (-154408 : ℤ) (359932 : ℤ) (-3088198770212048380913083975 : ℤ) (7198726192714280285284916303 : ℤ) 39 39
    cdemPrefixStats_97152_97216 cdemPrefixStats_97216_97280
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_97024_97280 :
    (∑ n ∈ Ico 97024 97280, mobiusTreeValue 16 mobiusTable1200001 n) = (27 : ℤ) ∧
    (∑ n ∈ Ico 97024 97280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (153 : ℕ) ∧
    (∑ n ∈ Ico 97024 97280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1390098 : ℤ) ∧
    (∑ n ∈ Ico 97024 97280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (27802257225380536244318521260 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    97024 97152 97280 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (23 : ℤ) (4 : ℤ) (1184574 : ℤ) (205524 : ℤ) (23691729802878304339946688932 : ℤ) (4110527422502231904371832328 : ℤ) 75 78
    cdemPrefixStats_97024_97152 cdemPrefixStats_97152_97280
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_96768_97280 :
    (∑ n ∈ Ico 96768 97280, mobiusTreeValue 16 mobiusTable1200001 n) = (26 : ℤ) ∧
    (∑ n ∈ Ico 96768 97280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (310 : ℕ) ∧
    (∑ n ∈ Ico 96768 97280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1338110 : ℤ) ∧
    (∑ n ∈ Ico 96768 97280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (26762387108707771505819729084 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    96768 97024 97280 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-1 : ℤ) (27 : ℤ) (-51988 : ℤ) (1390098 : ℤ) (-1039870116672764738498792176 : ℤ) (27802257225380536244318521260 : ℤ) 157 153
    cdemPrefixStats_96768_97024 cdemPrefixStats_97024_97280
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_96256_97280 :
    (∑ n ∈ Ico 96256 97280, mobiusTreeValue 16 mobiusTable1200001 n) = (23 : ℤ) ∧
    (∑ n ∈ Ico 96256 97280, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (619 : ℕ) ∧
    (∑ n ∈ Ico 96256 97280, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1182676 : ℤ) ∧
    (∑ n ∈ Ico 96256 97280, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (23653726140606912075161991787 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    96256 96768 97280 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-3 : ℤ) (26 : ℤ) (-155434 : ℤ) (1338110 : ℤ) (-3108660968100859430657737297 : ℤ) (26762387108707771505819729084 : ℤ) 309 310
    cdemPrefixStats_96256_96768 cdemPrefixStats_96768_97280
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_97280_97344 :
    (∑ n ∈ Ico 97280 97344, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 97280 97344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 97280 97344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (411032 : ℤ) ∧
    (∑ n ∈ Ico 97280 97344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (8220652692564650482305918300 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_97344_97408 :
    (∑ n ∈ Ico 97344 97408, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 97344 97408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 97344 97408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-51298 : ℤ) ∧
    (∑ n ∈ Ico 97344 97408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-1025976393151764549967757222 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_97280_97408 :
    (∑ n ∈ Ico 97280 97408, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 97280 97408, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 97280 97408, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (359734 : ℤ) ∧
    (∑ n ∈ Ico 97280 97408, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7194676299412885932338161078 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    97280 97344 97408 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (8 : ℤ) (-1 : ℤ) (411032 : ℤ) (-51298 : ℤ) (8220652692564650482305918300 : ℤ) (-1025976393151764549967757222 : ℤ) 40 37
    cdemPrefixStats_97280_97344 cdemPrefixStats_97344_97408
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_97408_97472 :
    (∑ n ∈ Ico 97408 97472, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 97408 97472, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (42 : ℕ) ∧
    (∑ n ∈ Ico 97408 97472, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-307961 : ℤ) ∧
    (∑ n ∈ Ico 97408 97472, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6159268137860000659819777650 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_97472_97536 :
    (∑ n ∈ Ico 97472 97536, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 97472 97536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (37 : ℕ) ∧
    (∑ n ∈ Ico 97472 97536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (769158 : ℤ) ∧
    (∑ n ∈ Ico 97472 97536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (15383322534300177182217463670 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_97408_97536 :
    (∑ n ∈ Ico 97408 97536, mobiusTreeValue 16 mobiusTable1200001 n) = (9 : ℤ) ∧
    (∑ n ∈ Ico 97408 97536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 97408 97536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (461197 : ℤ) ∧
    (∑ n ∈ Ico 97408 97536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9224054396440176522397686020 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    97408 97472 97536 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-6 : ℤ) (15 : ℤ) (-307961 : ℤ) (769158 : ℤ) (-6159268137860000659819777650 : ℤ) (15383322534300177182217463670 : ℤ) 42 37
    cdemPrefixStats_97408_97472 cdemPrefixStats_97472_97536
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_97280_97536 :
    (∑ n ∈ Ico 97280 97536, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 97280 97536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (156 : ℕ) ∧
    (∑ n ∈ Ico 97280 97536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (820931 : ℤ) ∧
    (∑ n ∈ Ico 97280 97536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (16418730695853062454735847098 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    97280 97408 97536 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (7 : ℤ) (9 : ℤ) (359734 : ℤ) (461197 : ℤ) (7194676299412885932338161078 : ℤ) (9224054396440176522397686020 : ℤ) 77 79
    cdemPrefixStats_97280_97408 cdemPrefixStats_97408_97536
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_97536_97600 :
    (∑ n ∈ Ico 97536 97600, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 97536 97600, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 97536 97600, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (20 : ℤ) ∧
    (∑ n ∈ Ico 97536 97600, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (389126716236054423110209 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_97600_97664 :
    (∑ n ∈ Ico 97600 97664, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 97600 97664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 97600 97664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (255942 : ℤ) ∧
    (∑ n ∈ Ico 97600 97664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5118827152040030042448317759 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_97536_97664 :
    (∑ n ∈ Ico 97536 97664, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 97536 97664, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 97536 97664, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (255962 : ℤ) ∧
    (∑ n ∈ Ico 97536 97664, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5119216278756266096871427968 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    97536 97600 97664 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (0 : ℤ) (5 : ℤ) (20 : ℤ) (255942 : ℤ) (389126716236054423110209 : ℤ) (5118827152040030042448317759 : ℤ) 40 39
    cdemPrefixStats_97536_97600 cdemPrefixStats_97600_97664
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_97664_97728 :
    (∑ n ∈ Ico 97664 97728, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 97664 97728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 97664 97728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (51082 : ℤ) ∧
    (∑ n ∈ Ico 97664 97728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1021644969512458637505529202 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_97728_97792 :
    (∑ n ∈ Ico 97728 97792, mobiusTreeValue 16 mobiusTable1200001 n) = (6 : ℤ) ∧
    (∑ n ∈ Ico 97728 97792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 97728 97792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (306955 : ℤ) ∧
    (∑ n ∈ Ico 97728 97792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (6139090664004908032646332747 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_97664_97792 :
    (∑ n ∈ Ico 97664 97792, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 97664 97792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (79 : ℕ) ∧
    (∑ n ∈ Ico 97664 97792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (358037 : ℤ) ∧
    (∑ n ∈ Ico 97664 97792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7160735633517366670151861949 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    97664 97728 97792 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (1 : ℤ) (6 : ℤ) (51082 : ℤ) (306955 : ℤ) (1021644969512458637505529202 : ℤ) (6139090664004908032646332747 : ℤ) 39 40
    cdemPrefixStats_97664_97728 cdemPrefixStats_97728_97792
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_97536_97792 :
    (∑ n ∈ Ico 97536 97792, mobiusTreeValue 16 mobiusTable1200001 n) = (12 : ℤ) ∧
    (∑ n ∈ Ico 97536 97792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (158 : ℕ) ∧
    (∑ n ∈ Ico 97536 97792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (613999 : ℤ) ∧
    (∑ n ∈ Ico 97536 97792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12279951912273632767023289917 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    97536 97664 97792 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (5 : ℤ) (7 : ℤ) (255962 : ℤ) (358037 : ℤ) (5119216278756266096871427968 : ℤ) (7160735633517366670151861949 : ℤ) 79 79
    cdemPrefixStats_97536_97664 cdemPrefixStats_97664_97792
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_97280_97792 :
    (∑ n ∈ Ico 97280 97792, mobiusTreeValue 16 mobiusTable1200001 n) = (28 : ℤ) ∧
    (∑ n ∈ Ico 97280 97792, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (314 : ℕ) ∧
    (∑ n ∈ Ico 97280 97792, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1434930 : ℤ) ∧
    (∑ n ∈ Ico 97280 97792, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (28698682608126695221759137015 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    97280 97536 97792 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (16 : ℤ) (12 : ℤ) (820931 : ℤ) (613999 : ℤ) (16418730695853062454735847098 : ℤ) (12279951912273632767023289917 : ℤ) 156 158
    cdemPrefixStats_97280_97536 cdemPrefixStats_97536_97792
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_97792_97856 :
    (∑ n ∈ Ico 97792 97856, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 97792 97856, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 97792 97856, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-102275 : ℤ) ∧
    (∑ n ∈ Ico 97792 97856, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2045522495312660440273879497 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_97856_97920 :
    (∑ n ∈ Ico 97856 97920, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 97856 97920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 97856 97920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-204327 : ℤ) ∧
    (∑ n ∈ Ico 97856 97920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4086595363994730269022346274 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_97792_97920 :
    (∑ n ∈ Ico 97792 97920, mobiusTreeValue 16 mobiusTable1200001 n) = (-6 : ℤ) ∧
    (∑ n ∈ Ico 97792 97920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 97792 97920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-306602 : ℤ) ∧
    (∑ n ∈ Ico 97792 97920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6132117859307390709296225771 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    97792 97856 97920 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-2 : ℤ) (-4 : ℤ) (-102275 : ℤ) (-204327 : ℤ) (-2045522495312660440273879497 : ℤ) (-4086595363994730269022346274 : ℤ) 38 40
    cdemPrefixStats_97792_97856 cdemPrefixStats_97856_97920
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_97920_97984 :
    (∑ n ∈ Ico 97920 97984, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 97920 97984, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (36 : ℕ) ∧
    (∑ n ∈ Ico 97920 97984, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (101987 : ℤ) ∧
    (∑ n ∈ Ico 97920 97984, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2039804933922441718793017036 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_97984_98048 :
    (∑ n ∈ Ico 97984 98048, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 97984 98048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 97984 98048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-204028 : ℤ) ∧
    (∑ n ∈ Ico 97984 98048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-4080602190992922555672628255 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_97920_98048 :
    (∑ n ∈ Ico 97920 98048, mobiusTreeValue 16 mobiusTable1200001 n) = (-2 : ℤ) ∧
    (∑ n ∈ Ico 97920 98048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (76 : ℕ) ∧
    (∑ n ∈ Ico 97920 98048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-102041 : ℤ) ∧
    (∑ n ∈ Ico 97920 98048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2040797257070480836879611219 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    97920 97984 98048 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (2 : ℤ) (-4 : ℤ) (101987 : ℤ) (-204028 : ℤ) (2039804933922441718793017036 : ℤ) (-4080602190992922555672628255 : ℤ) 36 40
    cdemPrefixStats_97920_97984 cdemPrefixStats_97984_98048
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_97792_98048 :
    (∑ n ∈ Ico 97792 98048, mobiusTreeValue 16 mobiusTable1200001 n) = (-8 : ℤ) ∧
    (∑ n ∈ Ico 97792 98048, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (154 : ℕ) ∧
    (∑ n ∈ Ico 97792 98048, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-408643 : ℤ) ∧
    (∑ n ∈ Ico 97792 98048, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-8172915116377871546175836990 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    97792 97920 98048 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-6 : ℤ) (-2 : ℤ) (-306602 : ℤ) (-102041 : ℤ) (-6132117859307390709296225771 : ℤ) (-2040797257070480836879611219 : ℤ) 78 76
    cdemPrefixStats_97792_97920 cdemPrefixStats_97920_98048
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_98048_98112 :
    (∑ n ∈ Ico 98048 98112, mobiusTreeValue 16 mobiusTable1200001 n) = (5 : ℤ) ∧
    (∑ n ∈ Ico 98048 98112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (39 : ℕ) ∧
    (∑ n ∈ Ico 98048 98112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (254972 : ℤ) ∧
    (∑ n ∈ Ico 98048 98112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (5099438509018807999106726102 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_98112_98176 :
    (∑ n ∈ Ico 98112 98176, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 98112 98176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 98112 98176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (101938 : ℤ) ∧
    (∑ n ∈ Ico 98112 98176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (2038829194570636004423569001 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_98048_98176 :
    (∑ n ∈ Ico 98048 98176, mobiusTreeValue 16 mobiusTable1200001 n) = (7 : ℤ) ∧
    (∑ n ∈ Ico 98048 98176, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (77 : ℕ) ∧
    (∑ n ∈ Ico 98048 98176, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (356910 : ℤ) ∧
    (∑ n ∈ Ico 98048 98176, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7138267703589444003530295103 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    98048 98112 98176 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (5 : ℤ) (2 : ℤ) (254972 : ℤ) (101938 : ℤ) (5099438509018807999106726102 : ℤ) (2038829194570636004423569001 : ℤ) 39 38
    cdemPrefixStats_98048_98112 cdemPrefixStats_98112_98176
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_98176_98240 :
    (∑ n ∈ Ico 98176 98240, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 98176 98240, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (40 : ℕ) ∧
    (∑ n ∈ Ico 98176 98240, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-509212 : ℤ) ∧
    (∑ n ∈ Ico 98176 98240, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10184356879778318742508680179 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_98240_98304 :
    (∑ n ∈ Ico 98240 98304, mobiusTreeValue 16 mobiusTable1200001 n) = (0 : ℤ) ∧
    (∑ n ∈ Ico 98240 98304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (38 : ℕ) ∧
    (∑ n ∈ Ico 98240 98304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (67 : ℤ) ∧
    (∑ n ∈ Ico 98240 98304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1284204945815585079119214 : ℤ) := by
  decide +kernel



private theorem cdemPrefixStats_98176_98304 :
    (∑ n ∈ Ico 98176 98304, mobiusTreeValue 16 mobiusTable1200001 n) = (-10 : ℤ) ∧
    (∑ n ∈ Ico 98176 98304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (78 : ℕ) ∧
    (∑ n ∈ Ico 98176 98304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-509145 : ℤ) ∧
    (∑ n ∈ Ico 98176 98304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-10183072674832503157429560965 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    98176 98240 98304 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-10 : ℤ) (0 : ℤ) (-509212 : ℤ) (67 : ℤ) (-10184356879778318742508680179 : ℤ) (1284204945815585079119214 : ℤ) 40 38
    cdemPrefixStats_98176_98240 cdemPrefixStats_98240_98304
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_98048_98304 :
    (∑ n ∈ Ico 98048 98304, mobiusTreeValue 16 mobiusTable1200001 n) = (-3 : ℤ) ∧
    (∑ n ∈ Ico 98048 98304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (155 : ℕ) ∧
    (∑ n ∈ Ico 98048 98304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-152235 : ℤ) ∧
    (∑ n ∈ Ico 98048 98304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3044804971243059153899265862 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    98048 98176 98304 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (7 : ℤ) (-10 : ℤ) (356910 : ℤ) (-509145 : ℤ) (7138267703589444003530295103 : ℤ) (-10183072674832503157429560965 : ℤ) 77 78
    cdemPrefixStats_98048_98176 cdemPrefixStats_98176_98304
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_97792_98304 :
    (∑ n ∈ Ico 97792 98304, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 97792 98304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (309 : ℕ) ∧
    (∑ n ∈ Ico 97792 98304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-560878 : ℤ) ∧
    (∑ n ∈ Ico 97792 98304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-11217720087620930700075102852 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    97792 98048 98304 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-8 : ℤ) (-3 : ℤ) (-408643 : ℤ) (-152235 : ℤ) (-8172915116377871546175836990 : ℤ) (-3044804971243059153899265862 : ℤ) 154 155
    cdemPrefixStats_97792_98048 cdemPrefixStats_98048_98304
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_97280_98304 :
    (∑ n ∈ Ico 97280 98304, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 97280 98304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (623 : ℕ) ∧
    (∑ n ∈ Ico 97280 98304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (874052 : ℤ) ∧
    (∑ n ∈ Ico 97280 98304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17480962520505764521684034163 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    97280 97792 98304 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (28 : ℤ) (-11 : ℤ) (1434930 : ℤ) (-560878 : ℤ) (28698682608126695221759137015 : ℤ) (-11217720087620930700075102852 : ℤ) 314 309
    cdemPrefixStats_97280_97792 cdemPrefixStats_97792_98304
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_96256_98304 :
    (∑ n ∈ Ico 96256 98304, mobiusTreeValue 16 mobiusTable1200001 n) = (40 : ℤ) ∧
    (∑ n ∈ Ico 96256 98304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1242 : ℕ) ∧
    (∑ n ∈ Ico 96256 98304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2056728 : ℤ) ∧
    (∑ n ∈ Ico 96256 98304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (41134688661112676596846025950 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    96256 97280 98304 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (23 : ℤ) (17 : ℤ) (1182676 : ℤ) (874052 : ℤ) (23653726140606912075161991787 : ℤ) (17480962520505764521684034163 : ℤ) 619 623
    cdemPrefixStats_96256_97280 cdemPrefixStats_97280_98304
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


private theorem cdemPrefixStats_94208_98304 :
    (∑ n ∈ Ico 94208 98304, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 94208 98304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2485 : ℕ) ∧
    (∑ n ∈ Ico 94208 98304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-318249 : ℤ) ∧
    (∑ n ∈ Ico 94208 98304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6365083916310545809191990388 : ℤ) := by
  have h := cdem_prefix023_repair_join (fun n => mobiusTreeValue 16 mobiusTable1200001 n)
    94208 96256 98304 (by decide) (by decide) 5000000000 100000000000000000000000000000000
    (-45 : ℤ) (40 : ℤ) (-2374977 : ℤ) (2056728 : ℤ) (-47499772577423222406038016338 : ℤ) (41134688661112676596846025950 : ℤ) 1243 1242
    cdemPrefixStats_94208_96256 cdemPrefixStats_96256_98304
  exact ⟨h.1.trans (by decide), h.2.1.trans (by decide),
    h.2.2.1.trans (by decide), h.2.2.2.trans (by decide)⟩


theorem cdemPrefixGroup023_fast_checked_complete :
    (∑ n ∈ Ico 94208 98304, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 94208 98304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2485 : ℕ) ∧
    (∑ n ∈ Ico 94208 98304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-318249 : ℤ) ∧
    (∑ n ∈ Ico 94208 98304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6365083916310545809191990388 : ℤ) := cdemPrefixStats_94208_98304
end Helfgott
#print axioms Helfgott.cdemPrefixGroup023_fast_checked_complete

open Helfgott Finset
open scoped BigOperators
theorem solution :
    (∑ n ∈ Ico 94208 98304, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 94208 98304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2485 : ℕ) ∧
    (∑ n ∈ Ico 94208 98304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-318249 : ℤ) ∧
    (∑ n ∈ Ico 94208 98304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6365083916310545809191990388 : ℤ) := Helfgott.cdemPrefixGroup023_fast_checked_complete
#print axioms solution
