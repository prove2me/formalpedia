-- Prove2me | solution 1 for Helfgott.mobiusHarmonic1078853_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:21:04.615334+00:00
-- url     : https://prove2.me/submissions/ac820e7f-61d4-40fc-a7ec-8f54f851bad4

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
import Theorems.Thm_Helfgott_mobiusHarmonicPair000_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair001_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair002_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair003_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair004_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair005_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair006_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair007_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair008_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair009_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair010_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair011_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair012_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair013_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair014_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair015_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair016_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair017_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair018_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair019_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair020_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair021_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair022_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair023_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair024_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair025_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair026_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair027_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair028_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair029_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair030_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair031_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair032_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair033_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair034_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair035_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair036_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair037_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair038_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair039_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair040_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair041_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair042_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair043_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair044_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair045_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair046_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair047_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair048_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair049_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair050_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair051_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair052_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair053_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair054_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair055_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair056_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair057_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair058_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair059_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair060_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair061_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair062_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair063_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair064_checked
import Theorems.Thm_Helfgott_mobiusHarmonicPair065_checked
import Mathlib.Tactic


set_option autoImplicit false
namespace Helfgott

lemma mobiusTreeCheck_join (g : ℕ → ℤ) (B d offset : ℕ) (l r : MobiusCertTree)
    (hl : mobiusTreeCheck g B d offset l = true)
    (hr : mobiusTreeCheck g B d (offset + 32 * 2 ^ d) r = true) :
    mobiusTreeCheck g B (d + 1) offset (.branch l r) = true := by
  by_cases hoff : B ≤ offset
  · simp [mobiusTreeCheck, hoff]
  · simpa [mobiusTreeCheck, hoff] using And.intro hl hr

lemma mobiusHarmonicTreeCheck_join (g M : ℕ → ℤ) (Q B d offset upper : ℕ)
    (l r : MobiusHarmonicTree) (hoff : offset < B)
    (hl : mobiusHarmonicTreeCheck g M Q B d offset l = true)
    (hr : mobiusHarmonicTreeCheck g M Q B d (offset + 32 * 2 ^ d) r = true)
    (hu : upper = mobiusHarmonicUpper l + mobiusHarmonicUpper r) :
    mobiusHarmonicTreeCheck g M Q B (d + 1) offset (.branch upper l r) = true := by
  have hoff' : ¬B ≤ offset := not_le.mpr hoff
  simpa [mobiusHarmonicTreeCheck, hoff', Bool.and_assoc, and_assoc] using ⟨hl, hr, hu⟩

end Helfgott
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Helfgott

private abbrev cg : ℕ → ℤ := mobiusTreeValue 16 mobiusTable1200001
private abbrev cm : ℕ → ℤ := mobiusPrefixValue 16 mobiusHarmonic1078853
private def rootNode10_0 : MobiusHarmonicTree := .branch 57637715881 (MobiusHarmonicTree.branch 41222702608 mobiusHarmonicBlock000 mobiusHarmonicBlock001) (MobiusHarmonicTree.branch 16415013273 mobiusHarmonicBlock002 mobiusHarmonicBlock003)
private theorem rootNode10_0_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 0 rootNode10_0 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 0 57637715881 _ _ (by decide) mobiusHarmonicPair000_checked mobiusHarmonicPair001_checked (by decide +kernel)

private def rootNode10_32768 : MobiusHarmonicTree := .branch 22039497675 (MobiusHarmonicTree.branch 10651587885 mobiusHarmonicBlock004 mobiusHarmonicBlock005) (MobiusHarmonicTree.branch 11387909790 mobiusHarmonicBlock006 mobiusHarmonicBlock007)
private theorem rootNode10_32768_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 32768 rootNode10_32768 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 32768 22039497675 _ _ (by decide) mobiusHarmonicPair002_checked mobiusHarmonicPair003_checked (by decide +kernel)

private def rootNode11_0 : MobiusHarmonicTree := .branch 79677213556 rootNode10_0 rootNode10_32768
private theorem rootNode11_0_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 11 0 rootNode11_0 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 10 0 79677213556 _ _ (by decide) rootNode10_0_checked rootNode10_32768_checked (by decide +kernel)

private def rootNode10_65536 : MobiusHarmonicTree := .branch 14700461708 (MobiusHarmonicTree.branch 6341275950 mobiusHarmonicBlock008 mobiusHarmonicBlock009) (MobiusHarmonicTree.branch 8359185758 mobiusHarmonicBlock010 mobiusHarmonicBlock011)
private theorem rootNode10_65536_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 65536 rootNode10_65536 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 65536 14700461708 _ _ (by decide) mobiusHarmonicPair004_checked mobiusHarmonicPair005_checked (by decide +kernel)

private def rootNode10_98304 : MobiusHarmonicTree := .branch 12856621122 (MobiusHarmonicTree.branch 4796742205 mobiusHarmonicBlock012 mobiusHarmonicBlock013) (MobiusHarmonicTree.branch 8059878917 mobiusHarmonicBlock014 mobiusHarmonicBlock015)
private theorem rootNode10_98304_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 98304 rootNode10_98304 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 98304 12856621122 _ _ (by decide) mobiusHarmonicPair006_checked mobiusHarmonicPair007_checked (by decide +kernel)

private def rootNode11_65536 : MobiusHarmonicTree := .branch 27557082830 rootNode10_65536 rootNode10_98304
private theorem rootNode11_65536_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 11 65536 rootNode11_65536 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 10 65536 27557082830 _ _ (by decide) rootNode10_65536_checked rootNode10_98304_checked (by decide +kernel)

private def rootNode12_0 : MobiusHarmonicTree := .branch 107234296386 rootNode11_0 rootNode11_65536
private theorem rootNode12_0_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 12 0 rootNode12_0 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 11 0 107234296386 _ _ (by decide) rootNode11_0_checked rootNode11_65536_checked (by decide +kernel)

private def rootNode10_131072 : MobiusHarmonicTree := .branch 12391832746 (MobiusHarmonicTree.branch 6309953364 mobiusHarmonicBlock016 mobiusHarmonicBlock017) (MobiusHarmonicTree.branch 6081879382 mobiusHarmonicBlock018 mobiusHarmonicBlock019)
private theorem rootNode10_131072_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 131072 rootNode10_131072 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 131072 12391832746 _ _ (by decide) mobiusHarmonicPair008_checked mobiusHarmonicPair009_checked (by decide +kernel)

private def rootNode10_163840 : MobiusHarmonicTree := .branch 10346490245 (MobiusHarmonicTree.branch 6719072402 mobiusHarmonicBlock020 mobiusHarmonicBlock021) (MobiusHarmonicTree.branch 3627417843 mobiusHarmonicBlock022 mobiusHarmonicBlock023)
private theorem rootNode10_163840_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 163840 rootNode10_163840 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 163840 10346490245 _ _ (by decide) mobiusHarmonicPair010_checked mobiusHarmonicPair011_checked (by decide +kernel)

private def rootNode11_131072 : MobiusHarmonicTree := .branch 22738322991 rootNode10_131072 rootNode10_163840
private theorem rootNode11_131072_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 11 131072 rootNode11_131072 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 10 131072 22738322991 _ _ (by decide) rootNode10_131072_checked rootNode10_163840_checked (by decide +kernel)

private def rootNode10_196608 : MobiusHarmonicTree := .branch 5894857612 (MobiusHarmonicTree.branch 2612904564 mobiusHarmonicBlock024 mobiusHarmonicBlock025) (MobiusHarmonicTree.branch 3281953048 mobiusHarmonicBlock026 mobiusHarmonicBlock027)
private theorem rootNode10_196608_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 196608 rootNode10_196608 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 196608 5894857612 _ _ (by decide) mobiusHarmonicPair012_checked mobiusHarmonicPair013_checked (by decide +kernel)

private def rootNode10_229376 : MobiusHarmonicTree := .branch 5671517948 (MobiusHarmonicTree.branch 3910707266 mobiusHarmonicBlock028 mobiusHarmonicBlock029) (MobiusHarmonicTree.branch 1760810682 mobiusHarmonicBlock030 mobiusHarmonicBlock031)
private theorem rootNode10_229376_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 229376 rootNode10_229376 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 229376 5671517948 _ _ (by decide) mobiusHarmonicPair014_checked mobiusHarmonicPair015_checked (by decide +kernel)

private def rootNode11_196608 : MobiusHarmonicTree := .branch 11566375560 rootNode10_196608 rootNode10_229376
private theorem rootNode11_196608_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 11 196608 rootNode11_196608 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 10 196608 11566375560 _ _ (by decide) rootNode10_196608_checked rootNode10_229376_checked (by decide +kernel)

private def rootNode12_131072 : MobiusHarmonicTree := .branch 34304698551 rootNode11_131072 rootNode11_196608
private theorem rootNode12_131072_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 12 131072 rootNode12_131072 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 11 131072 34304698551 _ _ (by decide) rootNode11_131072_checked rootNode11_196608_checked (by decide +kernel)

private def rootNode13_0 : MobiusHarmonicTree := .branch 141538994937 rootNode12_0 rootNode12_131072
private theorem rootNode13_0_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 13 0 rootNode13_0 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 12 0 141538994937 _ _ (by decide) rootNode12_0_checked rootNode12_131072_checked (by decide +kernel)

private def rootNode10_262144 : MobiusHarmonicTree := .branch 6038515657 (MobiusHarmonicTree.branch 1479898051 mobiusHarmonicBlock032 mobiusHarmonicBlock033) (MobiusHarmonicTree.branch 4558617606 mobiusHarmonicBlock034 mobiusHarmonicBlock035)
private theorem rootNode10_262144_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 262144 rootNode10_262144 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 262144 6038515657 _ _ (by decide) mobiusHarmonicPair016_checked mobiusHarmonicPair017_checked (by decide +kernel)

private def rootNode10_294912 : MobiusHarmonicTree := .branch 13755334431 (MobiusHarmonicTree.branch 9482992829 mobiusHarmonicBlock036 mobiusHarmonicBlock037) (MobiusHarmonicTree.branch 4272341602 mobiusHarmonicBlock038 mobiusHarmonicBlock039)
private theorem rootNode10_294912_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 294912 rootNode10_294912 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 294912 13755334431 _ _ (by decide) mobiusHarmonicPair018_checked mobiusHarmonicPair019_checked (by decide +kernel)

private def rootNode11_262144 : MobiusHarmonicTree := .branch 19793850088 rootNode10_262144 rootNode10_294912
private theorem rootNode11_262144_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 11 262144 rootNode11_262144 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 10 262144 19793850088 _ _ (by decide) rootNode10_262144_checked rootNode10_294912_checked (by decide +kernel)

private def rootNode10_327680 : MobiusHarmonicTree := .branch 17007357004 (MobiusHarmonicTree.branch 7176745740 mobiusHarmonicBlock040 mobiusHarmonicBlock041) (MobiusHarmonicTree.branch 9830611264 mobiusHarmonicBlock042 mobiusHarmonicBlock043)
private theorem rootNode10_327680_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 327680 rootNode10_327680 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 327680 17007357004 _ _ (by decide) mobiusHarmonicPair020_checked mobiusHarmonicPair021_checked (by decide +kernel)

private def rootNode10_360448 : MobiusHarmonicTree := .branch 4930549043 (MobiusHarmonicTree.branch 3815231848 mobiusHarmonicBlock044 mobiusHarmonicBlock045) (MobiusHarmonicTree.branch 1115317195 mobiusHarmonicBlock046 mobiusHarmonicBlock047)
private theorem rootNode10_360448_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 360448 rootNode10_360448 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 360448 4930549043 _ _ (by decide) mobiusHarmonicPair022_checked mobiusHarmonicPair023_checked (by decide +kernel)

private def rootNode11_327680 : MobiusHarmonicTree := .branch 21937906047 rootNode10_327680 rootNode10_360448
private theorem rootNode11_327680_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 11 327680 rootNode11_327680 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 10 327680 21937906047 _ _ (by decide) rootNode10_327680_checked rootNode10_360448_checked (by decide +kernel)

private def rootNode12_262144 : MobiusHarmonicTree := .branch 41731756135 rootNode11_262144 rootNode11_327680
private theorem rootNode12_262144_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 12 262144 rootNode12_262144 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 11 262144 41731756135 _ _ (by decide) rootNode11_262144_checked rootNode11_327680_checked (by decide +kernel)

private def rootNode10_393216 : MobiusHarmonicTree := .branch 7267678035 (MobiusHarmonicTree.branch 1662894335 mobiusHarmonicBlock048 mobiusHarmonicBlock049) (MobiusHarmonicTree.branch 5604783700 mobiusHarmonicBlock050 mobiusHarmonicBlock051)
private theorem rootNode10_393216_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 393216 rootNode10_393216 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 393216 7267678035 _ _ (by decide) mobiusHarmonicPair024_checked mobiusHarmonicPair025_checked (by decide +kernel)

private def rootNode10_425984 : MobiusHarmonicTree := .branch 3491977607 (MobiusHarmonicTree.branch 1883257961 mobiusHarmonicBlock052 mobiusHarmonicBlock053) (MobiusHarmonicTree.branch 1608719646 mobiusHarmonicBlock054 mobiusHarmonicBlock055)
private theorem rootNode10_425984_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 425984 rootNode10_425984 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 425984 3491977607 _ _ (by decide) mobiusHarmonicPair026_checked mobiusHarmonicPair027_checked (by decide +kernel)

private def rootNode11_393216 : MobiusHarmonicTree := .branch 10759655642 rootNode10_393216 rootNode10_425984
private theorem rootNode11_393216_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 11 393216 rootNode11_393216 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 10 393216 10759655642 _ _ (by decide) rootNode10_393216_checked rootNode10_425984_checked (by decide +kernel)

private def rootNode10_458752 : MobiusHarmonicTree := .branch 6224388448 (MobiusHarmonicTree.branch 5353667806 mobiusHarmonicBlock056 mobiusHarmonicBlock057) (MobiusHarmonicTree.branch 870720642 mobiusHarmonicBlock058 mobiusHarmonicBlock059)
private theorem rootNode10_458752_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 458752 rootNode10_458752 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 458752 6224388448 _ _ (by decide) mobiusHarmonicPair028_checked mobiusHarmonicPair029_checked (by decide +kernel)

private def rootNode10_491520 : MobiusHarmonicTree := .branch 3522213989 (MobiusHarmonicTree.branch 1207592973 mobiusHarmonicBlock060 mobiusHarmonicBlock061) (MobiusHarmonicTree.branch 2314621016 mobiusHarmonicBlock062 mobiusHarmonicBlock063)
private theorem rootNode10_491520_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 491520 rootNode10_491520 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 491520 3522213989 _ _ (by decide) mobiusHarmonicPair030_checked mobiusHarmonicPair031_checked (by decide +kernel)

private def rootNode11_458752 : MobiusHarmonicTree := .branch 9746602437 rootNode10_458752 rootNode10_491520
private theorem rootNode11_458752_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 11 458752 rootNode11_458752 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 10 458752 9746602437 _ _ (by decide) rootNode10_458752_checked rootNode10_491520_checked (by decide +kernel)

private def rootNode12_393216 : MobiusHarmonicTree := .branch 20506258079 rootNode11_393216 rootNode11_458752
private theorem rootNode12_393216_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 12 393216 rootNode12_393216 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 11 393216 20506258079 _ _ (by decide) rootNode11_393216_checked rootNode11_458752_checked (by decide +kernel)

private def rootNode13_262144 : MobiusHarmonicTree := .branch 62238014214 rootNode12_262144 rootNode12_393216
private theorem rootNode13_262144_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 13 262144 rootNode13_262144 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 12 262144 62238014214 _ _ (by decide) rootNode12_262144_checked rootNode12_393216_checked (by decide +kernel)

private def rootNode14_0 : MobiusHarmonicTree := .branch 203777009151 rootNode13_0 rootNode13_262144
private theorem rootNode14_0_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 14 0 rootNode14_0 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 13 0 203777009151 _ _ (by decide) rootNode13_0_checked rootNode13_262144_checked (by decide +kernel)

private def rootNode10_524288 : MobiusHarmonicTree := .branch 4123282555 (MobiusHarmonicTree.branch 3411807190 mobiusHarmonicBlock064 mobiusHarmonicBlock065) (MobiusHarmonicTree.branch 711475365 mobiusHarmonicBlock066 mobiusHarmonicBlock067)
private theorem rootNode10_524288_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 524288 rootNode10_524288 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 524288 4123282555 _ _ (by decide) mobiusHarmonicPair032_checked mobiusHarmonicPair033_checked (by decide +kernel)

private def rootNode10_557056 : MobiusHarmonicTree := .branch 3037392680 (MobiusHarmonicTree.branch 616139408 mobiusHarmonicBlock068 mobiusHarmonicBlock069) (MobiusHarmonicTree.branch 2421253272 mobiusHarmonicBlock070 mobiusHarmonicBlock071)
private theorem rootNode10_557056_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 557056 rootNode10_557056 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 557056 3037392680 _ _ (by decide) mobiusHarmonicPair034_checked mobiusHarmonicPair035_checked (by decide +kernel)

private def rootNode11_524288 : MobiusHarmonicTree := .branch 7160675235 rootNode10_524288 rootNode10_557056
private theorem rootNode11_524288_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 11 524288 rootNode11_524288 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 10 524288 7160675235 _ _ (by decide) rootNode10_524288_checked rootNode10_557056_checked (by decide +kernel)

private def rootNode10_589824 : MobiusHarmonicTree := .branch 11324062384 (MobiusHarmonicTree.branch 5694130537 mobiusHarmonicBlock072 mobiusHarmonicBlock073) (MobiusHarmonicTree.branch 5629931847 mobiusHarmonicBlock074 mobiusHarmonicBlock075)
private theorem rootNode10_589824_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 589824 rootNode10_589824 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 589824 11324062384 _ _ (by decide) mobiusHarmonicPair036_checked mobiusHarmonicPair037_checked (by decide +kernel)

private def rootNode10_622592 : MobiusHarmonicTree := .branch 4456673833 (MobiusHarmonicTree.branch 1781374855 mobiusHarmonicBlock076 mobiusHarmonicBlock077) (MobiusHarmonicTree.branch 2675298978 mobiusHarmonicBlock078 mobiusHarmonicBlock079)
private theorem rootNode10_622592_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 622592 rootNode10_622592 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 622592 4456673833 _ _ (by decide) mobiusHarmonicPair038_checked mobiusHarmonicPair039_checked (by decide +kernel)

private def rootNode11_589824 : MobiusHarmonicTree := .branch 15780736217 rootNode10_589824 rootNode10_622592
private theorem rootNode11_589824_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 11 589824 rootNode11_589824 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 10 589824 15780736217 _ _ (by decide) rootNode10_589824_checked rootNode10_622592_checked (by decide +kernel)

private def rootNode12_524288 : MobiusHarmonicTree := .branch 22941411452 rootNode11_524288 rootNode11_589824
private theorem rootNode12_524288_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 12 524288 rootNode12_524288 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 11 524288 22941411452 _ _ (by decide) rootNode11_524288_checked rootNode11_589824_checked (by decide +kernel)

private def rootNode10_655360 : MobiusHarmonicTree := .branch 9234382755 (MobiusHarmonicTree.branch 4623516487 mobiusHarmonicBlock080 mobiusHarmonicBlock081) (MobiusHarmonicTree.branch 4610866268 mobiusHarmonicBlock082 mobiusHarmonicBlock083)
private theorem rootNode10_655360_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 655360 rootNode10_655360 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 655360 9234382755 _ _ (by decide) mobiusHarmonicPair040_checked mobiusHarmonicPair041_checked (by decide +kernel)

private def rootNode10_688128 : MobiusHarmonicTree := .branch 8278641553 (MobiusHarmonicTree.branch 5006194560 mobiusHarmonicBlock084 mobiusHarmonicBlock085) (MobiusHarmonicTree.branch 3272446993 mobiusHarmonicBlock086 mobiusHarmonicBlock087)
private theorem rootNode10_688128_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 688128 rootNode10_688128 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 688128 8278641553 _ _ (by decide) mobiusHarmonicPair042_checked mobiusHarmonicPair043_checked (by decide +kernel)

private def rootNode11_655360 : MobiusHarmonicTree := .branch 17513024308 rootNode10_655360 rootNode10_688128
private theorem rootNode11_655360_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 11 655360 rootNode11_655360 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 10 655360 17513024308 _ _ (by decide) rootNode10_655360_checked rootNode10_688128_checked (by decide +kernel)

private def rootNode10_720896 : MobiusHarmonicTree := .branch 3113333985 (MobiusHarmonicTree.branch 1296381492 mobiusHarmonicBlock088 mobiusHarmonicBlock089) (MobiusHarmonicTree.branch 1816952493 mobiusHarmonicBlock090 mobiusHarmonicBlock091)
private theorem rootNode10_720896_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 720896 rootNode10_720896 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 720896 3113333985 _ _ (by decide) mobiusHarmonicPair044_checked mobiusHarmonicPair045_checked (by decide +kernel)

private def rootNode10_753664 : MobiusHarmonicTree := .branch 2279516164 (MobiusHarmonicTree.branch 1687422084 mobiusHarmonicBlock092 mobiusHarmonicBlock093) (MobiusHarmonicTree.branch 592094080 mobiusHarmonicBlock094 mobiusHarmonicBlock095)
private theorem rootNode10_753664_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 753664 rootNode10_753664 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 753664 2279516164 _ _ (by decide) mobiusHarmonicPair046_checked mobiusHarmonicPair047_checked (by decide +kernel)

private def rootNode11_720896 : MobiusHarmonicTree := .branch 5392850149 rootNode10_720896 rootNode10_753664
private theorem rootNode11_720896_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 11 720896 rootNode11_720896 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 10 720896 5392850149 _ _ (by decide) rootNode10_720896_checked rootNode10_753664_checked (by decide +kernel)

private def rootNode12_655360 : MobiusHarmonicTree := .branch 22905874457 rootNode11_655360 rootNode11_720896
private theorem rootNode12_655360_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 12 655360 rootNode12_655360 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 11 655360 22905874457 _ _ (by decide) rootNode11_655360_checked rootNode11_720896_checked (by decide +kernel)

private def rootNode13_524288 : MobiusHarmonicTree := .branch 45847285909 rootNode12_524288 rootNode12_655360
private theorem rootNode13_524288_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 13 524288 rootNode13_524288 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 12 524288 45847285909 _ _ (by decide) rootNode12_524288_checked rootNode12_655360_checked (by decide +kernel)

private def rootNode10_786432 : MobiusHarmonicTree := .branch 2072955733 (MobiusHarmonicTree.branch 687150476 mobiusHarmonicBlock096 mobiusHarmonicBlock097) (MobiusHarmonicTree.branch 1385805257 mobiusHarmonicBlock098 mobiusHarmonicBlock099)
private theorem rootNode10_786432_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 786432 rootNode10_786432 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 786432 2072955733 _ _ (by decide) mobiusHarmonicPair048_checked mobiusHarmonicPair049_checked (by decide +kernel)

private def rootNode10_819200 : MobiusHarmonicTree := .branch 6803434967 (MobiusHarmonicTree.branch 3451397252 mobiusHarmonicBlock100 mobiusHarmonicBlock101) (MobiusHarmonicTree.branch 3352037715 mobiusHarmonicBlock102 mobiusHarmonicBlock103)
private theorem rootNode10_819200_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 819200 rootNode10_819200 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 819200 6803434967 _ _ (by decide) mobiusHarmonicPair050_checked mobiusHarmonicPair051_checked (by decide +kernel)

private def rootNode11_786432 : MobiusHarmonicTree := .branch 8876390700 rootNode10_786432 rootNode10_819200
private theorem rootNode11_786432_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 11 786432 rootNode11_786432 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 10 786432 8876390700 _ _ (by decide) rootNode10_786432_checked rootNode10_819200_checked (by decide +kernel)

private def rootNode10_851968 : MobiusHarmonicTree := .branch 4836397577 (MobiusHarmonicTree.branch 2432626304 mobiusHarmonicBlock104 mobiusHarmonicBlock105) (MobiusHarmonicTree.branch 2403771273 mobiusHarmonicBlock106 mobiusHarmonicBlock107)
private theorem rootNode10_851968_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 851968 rootNode10_851968 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 851968 4836397577 _ _ (by decide) mobiusHarmonicPair052_checked mobiusHarmonicPair053_checked (by decide +kernel)

private def rootNode10_884736 : MobiusHarmonicTree := .branch 7150920884 (MobiusHarmonicTree.branch 3476922321 mobiusHarmonicBlock108 mobiusHarmonicBlock109) (MobiusHarmonicTree.branch 3673998563 mobiusHarmonicBlock110 mobiusHarmonicBlock111)
private theorem rootNode10_884736_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 884736 rootNode10_884736 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 884736 7150920884 _ _ (by decide) mobiusHarmonicPair054_checked mobiusHarmonicPair055_checked (by decide +kernel)

private def rootNode11_851968 : MobiusHarmonicTree := .branch 11987318461 rootNode10_851968 rootNode10_884736
private theorem rootNode11_851968_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 11 851968 rootNode11_851968 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 10 851968 11987318461 _ _ (by decide) rootNode10_851968_checked rootNode10_884736_checked (by decide +kernel)

private def rootNode12_786432 : MobiusHarmonicTree := .branch 20863709161 rootNode11_786432 rootNode11_851968
private theorem rootNode12_786432_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 12 786432 rootNode12_786432 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 11 786432 20863709161 _ _ (by decide) rootNode11_786432_checked rootNode11_851968_checked (by decide +kernel)

private def rootNode10_917504 : MobiusHarmonicTree := .branch 8564553133 (MobiusHarmonicTree.branch 4645284997 mobiusHarmonicBlock112 mobiusHarmonicBlock113) (MobiusHarmonicTree.branch 3919268136 mobiusHarmonicBlock114 mobiusHarmonicBlock115)
private theorem rootNode10_917504_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 917504 rootNode10_917504 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 917504 8564553133 _ _ (by decide) mobiusHarmonicPair056_checked mobiusHarmonicPair057_checked (by decide +kernel)

private def rootNode10_950272 : MobiusHarmonicTree := .branch 1935996363 (MobiusHarmonicTree.branch 899790853 mobiusHarmonicBlock116 mobiusHarmonicBlock117) (MobiusHarmonicTree.branch 1036205510 mobiusHarmonicBlock118 mobiusHarmonicBlock119)
private theorem rootNode10_950272_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 950272 rootNode10_950272 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 950272 1935996363 _ _ (by decide) mobiusHarmonicPair058_checked mobiusHarmonicPair059_checked (by decide +kernel)

private def rootNode11_917504 : MobiusHarmonicTree := .branch 10500549496 rootNode10_917504 rootNode10_950272
private theorem rootNode11_917504_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 11 917504 rootNode11_917504 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 10 917504 10500549496 _ _ (by decide) rootNode10_917504_checked rootNode10_950272_checked (by decide +kernel)

private def rootNode10_983040 : MobiusHarmonicTree := .branch 6593007913 (MobiusHarmonicTree.branch 3696918227 mobiusHarmonicBlock120 mobiusHarmonicBlock121) (MobiusHarmonicTree.branch 2896089686 mobiusHarmonicBlock122 mobiusHarmonicBlock123)
private theorem rootNode10_983040_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 983040 rootNode10_983040 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 983040 6593007913 _ _ (by decide) mobiusHarmonicPair060_checked mobiusHarmonicPair061_checked (by decide +kernel)

private def rootNode10_1015808 : MobiusHarmonicTree := .branch 4775058883 (MobiusHarmonicTree.branch 1386111687 mobiusHarmonicBlock124 mobiusHarmonicBlock125) (MobiusHarmonicTree.branch 3388947196 mobiusHarmonicBlock126 mobiusHarmonicBlock127)
private theorem rootNode10_1015808_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 1015808 rootNode10_1015808 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 1015808 4775058883 _ _ (by decide) mobiusHarmonicPair062_checked mobiusHarmonicPair063_checked (by decide +kernel)

private def rootNode11_983040 : MobiusHarmonicTree := .branch 11368066796 rootNode10_983040 rootNode10_1015808
private theorem rootNode11_983040_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 11 983040 rootNode11_983040 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 10 983040 11368066796 _ _ (by decide) rootNode10_983040_checked rootNode10_1015808_checked (by decide +kernel)

private def rootNode12_917504 : MobiusHarmonicTree := .branch 21868616292 rootNode11_917504 rootNode11_983040
private theorem rootNode12_917504_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 12 917504 rootNode12_917504 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 11 917504 21868616292 _ _ (by decide) rootNode11_917504_checked rootNode11_983040_checked (by decide +kernel)

private def rootNode13_786432 : MobiusHarmonicTree := .branch 42732325453 rootNode12_786432 rootNode12_917504
private theorem rootNode13_786432_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 13 786432 rootNode13_786432 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 12 786432 42732325453 _ _ (by decide) rootNode12_786432_checked rootNode12_917504_checked (by decide +kernel)

private def rootNode14_524288 : MobiusHarmonicTree := .branch 88579611362 rootNode13_524288 rootNode13_786432
private theorem rootNode14_524288_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 14 524288 rootNode14_524288 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 13 524288 88579611362 _ _ (by decide) rootNode13_524288_checked rootNode13_786432_checked (by decide +kernel)

private def rootNode15_0 : MobiusHarmonicTree := .branch 292356620513 rootNode14_0 rootNode14_524288
private theorem rootNode15_0_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 15 0 rootNode15_0 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 14 0 292356620513 _ _ (by decide) rootNode14_0_checked rootNode14_524288_checked (by decide +kernel)

private def rootNode10_1048576 : MobiusHarmonicTree := .branch 10124410872 (MobiusHarmonicTree.branch 5393034776 mobiusHarmonicBlock128 mobiusHarmonicBlock129) (MobiusHarmonicTree.branch 4731376096 mobiusHarmonicBlock130 mobiusHarmonicBlock131)
private theorem rootNode10_1048576_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 1048576 rootNode10_1048576 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 9 1048576 10124410872 _ _ (by decide) mobiusHarmonicPair064_checked mobiusHarmonicPair065_checked (by decide +kernel)

private def rootNode10_1081344 : MobiusHarmonicTree := .leaf 0 0
private theorem rootNode10_1081344_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 10 1081344 rootNode10_1081344 = true := by decide +kernel

private def rootNode11_1048576 : MobiusHarmonicTree := .branch 10124410872 rootNode10_1048576 rootNode10_1081344
private theorem rootNode11_1048576_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 11 1048576 rootNode11_1048576 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 10 1048576 10124410872 _ _ (by decide) rootNode10_1048576_checked rootNode10_1081344_checked (by decide +kernel)

private def rootNode11_1114112 : MobiusHarmonicTree := .leaf 0 0
private theorem rootNode11_1114112_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 11 1114112 rootNode11_1114112 = true := by decide +kernel

private def rootNode12_1048576 : MobiusHarmonicTree := .branch 10124410872 rootNode11_1048576 rootNode11_1114112
private theorem rootNode12_1048576_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 12 1048576 rootNode12_1048576 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 11 1048576 10124410872 _ _ (by decide) rootNode11_1048576_checked rootNode11_1114112_checked (by decide +kernel)

private def rootNode12_1179648 : MobiusHarmonicTree := .leaf 0 0
private theorem rootNode12_1179648_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 12 1179648 rootNode12_1179648 = true := by decide +kernel

private def rootNode13_1048576 : MobiusHarmonicTree := .branch 10124410872 rootNode12_1048576 rootNode12_1179648
private theorem rootNode13_1048576_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 13 1048576 rootNode13_1048576 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 12 1048576 10124410872 _ _ (by decide) rootNode12_1048576_checked rootNode12_1179648_checked (by decide +kernel)

private def rootNode13_1310720 : MobiusHarmonicTree := .leaf 0 0
private theorem rootNode13_1310720_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 13 1310720 rootNode13_1310720 = true := by decide +kernel

private def rootNode14_1048576 : MobiusHarmonicTree := .branch 10124410872 rootNode13_1048576 rootNode13_1310720
private theorem rootNode14_1048576_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 14 1048576 rootNode14_1048576 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 13 1048576 10124410872 _ _ (by decide) rootNode13_1048576_checked rootNode13_1310720_checked (by decide +kernel)

private def rootNode14_1572864 : MobiusHarmonicTree := .leaf 0 0
private theorem rootNode14_1572864_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 14 1572864 rootNode14_1572864 = true := by decide +kernel

private def rootNode15_1048576 : MobiusHarmonicTree := .branch 10124410872 rootNode14_1048576 rootNode14_1572864
private theorem rootNode15_1048576_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 15 1048576 rootNode15_1048576 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 14 1048576 10124410872 _ _ (by decide) rootNode14_1048576_checked rootNode14_1572864_checked (by decide +kernel)

private def rootNode16_0 : MobiusHarmonicTree := .branch 302481031385 rootNode15_0 rootNode15_1048576
private theorem rootNode16_0_checked : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 16 0 rootNode16_0 = true :=
  mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 15 0 302481031385 _ _ (by decide) rootNode15_0_checked rootNode15_1048576_checked (by decide +kernel)

end Helfgott
open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 16 0 mobiusHarmonic1078853 = true := Helfgott.rootNode16_0_checked
#print axioms solution
