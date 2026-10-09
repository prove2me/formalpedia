-- Prove2me | solution 1 for Helfgott.mobiusTable1200001_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:27:12.172986+00:00
-- url     : https://prove2.me/submissions/75a6ee62-bf70-4f39-a567-a771ce14f959

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Theorems.Thm_Helfgott_mobiusValuePair000_checked
import Theorems.Thm_Helfgott_mobiusValuePair001_checked
import Theorems.Thm_Helfgott_mobiusValuePair002_checked
import Theorems.Thm_Helfgott_mobiusValuePair003_checked
import Theorems.Thm_Helfgott_mobiusValuePair004_checked
import Theorems.Thm_Helfgott_mobiusValuePair005_checked
import Theorems.Thm_Helfgott_mobiusValuePair006_checked
import Theorems.Thm_Helfgott_mobiusValuePair007_checked
import Theorems.Thm_Helfgott_mobiusValuePair008_checked
import Theorems.Thm_Helfgott_mobiusValuePair009_checked
import Theorems.Thm_Helfgott_mobiusValuePair010_checked
import Theorems.Thm_Helfgott_mobiusValuePair011_checked
import Theorems.Thm_Helfgott_mobiusValuePair012_checked
import Theorems.Thm_Helfgott_mobiusValuePair013_checked
import Theorems.Thm_Helfgott_mobiusValuePair014_checked
import Theorems.Thm_Helfgott_mobiusValuePair015_checked
import Theorems.Thm_Helfgott_mobiusValuePair016_checked
import Theorems.Thm_Helfgott_mobiusValuePair017_checked
import Theorems.Thm_Helfgott_mobiusValuePair018_checked
import Theorems.Thm_Helfgott_mobiusValuePair019_checked
import Theorems.Thm_Helfgott_mobiusValuePair020_checked
import Theorems.Thm_Helfgott_mobiusValuePair021_checked
import Theorems.Thm_Helfgott_mobiusValuePair022_checked
import Theorems.Thm_Helfgott_mobiusValuePair023_checked
import Theorems.Thm_Helfgott_mobiusValuePair024_checked
import Theorems.Thm_Helfgott_mobiusValuePair025_checked
import Theorems.Thm_Helfgott_mobiusValuePair026_checked
import Theorems.Thm_Helfgott_mobiusValuePair027_checked
import Theorems.Thm_Helfgott_mobiusValuePair028_checked
import Theorems.Thm_Helfgott_mobiusValuePair029_checked
import Theorems.Thm_Helfgott_mobiusValuePair030_checked
import Theorems.Thm_Helfgott_mobiusValuePair031_checked
import Theorems.Thm_Helfgott_mobiusValuePair032_checked
import Theorems.Thm_Helfgott_mobiusValuePair033_checked
import Theorems.Thm_Helfgott_mobiusValuePair034_checked
import Theorems.Thm_Helfgott_mobiusValuePair035_checked
import Theorems.Thm_Helfgott_mobiusValuePair036_checked
import Theorems.Thm_Helfgott_mobiusValuePair037_checked
import Theorems.Thm_Helfgott_mobiusValuePair038_checked
import Theorems.Thm_Helfgott_mobiusValuePair039_checked
import Theorems.Thm_Helfgott_mobiusValuePair040_checked
import Theorems.Thm_Helfgott_mobiusValuePair041_checked
import Theorems.Thm_Helfgott_mobiusValuePair042_checked
import Theorems.Thm_Helfgott_mobiusValuePair043_checked
import Theorems.Thm_Helfgott_mobiusValuePair044_checked
import Theorems.Thm_Helfgott_mobiusValuePair045_checked
import Theorems.Thm_Helfgott_mobiusValuePair046_checked
import Theorems.Thm_Helfgott_mobiusValuePair047_checked
import Theorems.Thm_Helfgott_mobiusValuePair048_checked
import Theorems.Thm_Helfgott_mobiusValuePair049_checked
import Theorems.Thm_Helfgott_mobiusValuePair050_checked
import Theorems.Thm_Helfgott_mobiusValuePair051_checked
import Theorems.Thm_Helfgott_mobiusValuePair052_checked
import Theorems.Thm_Helfgott_mobiusValuePair053_checked
import Theorems.Thm_Helfgott_mobiusValuePair054_checked
import Theorems.Thm_Helfgott_mobiusValuePair055_checked
import Theorems.Thm_Helfgott_mobiusValuePair056_checked
import Theorems.Thm_Helfgott_mobiusValuePair057_checked
import Theorems.Thm_Helfgott_mobiusValuePair058_checked
import Theorems.Thm_Helfgott_mobiusValuePair059_checked
import Theorems.Thm_Helfgott_mobiusValuePair060_checked
import Theorems.Thm_Helfgott_mobiusValuePair061_checked
import Theorems.Thm_Helfgott_mobiusValuePair062_checked
import Theorems.Thm_Helfgott_mobiusValuePair063_checked
import Theorems.Thm_Helfgott_mobiusValuePair064_checked
import Theorems.Thm_Helfgott_mobiusValuePair065_checked
import Theorems.Thm_Helfgott_mobiusValuePair066_checked
import Theorems.Thm_Helfgott_mobiusValuePair067_checked
import Theorems.Thm_Helfgott_mobiusValuePair068_checked
import Theorems.Thm_Helfgott_mobiusValuePair069_checked
import Theorems.Thm_Helfgott_mobiusValuePair070_checked
import Theorems.Thm_Helfgott_mobiusValuePair071_checked
import Theorems.Thm_Helfgott_mobiusValuePair072_checked
import Theorems.Thm_Helfgott_mobiusValuePair073_checked
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
private def rootNode10_0 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock000 mobiusTableBlock001) (MobiusCertTree.branch mobiusTableBlock002 mobiusTableBlock003)
private theorem rootNode10_0_checked : mobiusTreeCheck cg 1200001 10 0 rootNode10_0 = true :=
  mobiusTreeCheck_join cg 1200001 9 0 _ _ mobiusValuePair000_checked mobiusValuePair001_checked

private def rootNode10_32768 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock004 mobiusTableBlock005) (MobiusCertTree.branch mobiusTableBlock006 mobiusTableBlock007)
private theorem rootNode10_32768_checked : mobiusTreeCheck cg 1200001 10 32768 rootNode10_32768 = true :=
  mobiusTreeCheck_join cg 1200001 9 32768 _ _ mobiusValuePair002_checked mobiusValuePair003_checked

private def rootNode11_0 : MobiusCertTree := .branch rootNode10_0 rootNode10_32768
private theorem rootNode11_0_checked : mobiusTreeCheck cg 1200001 11 0 rootNode11_0 = true :=
  mobiusTreeCheck_join cg 1200001 10 0 _ _ rootNode10_0_checked rootNode10_32768_checked

private def rootNode10_65536 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock008 mobiusTableBlock009) (MobiusCertTree.branch mobiusTableBlock010 mobiusTableBlock011)
private theorem rootNode10_65536_checked : mobiusTreeCheck cg 1200001 10 65536 rootNode10_65536 = true :=
  mobiusTreeCheck_join cg 1200001 9 65536 _ _ mobiusValuePair004_checked mobiusValuePair005_checked

private def rootNode10_98304 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock012 mobiusTableBlock013) (MobiusCertTree.branch mobiusTableBlock014 mobiusTableBlock015)
private theorem rootNode10_98304_checked : mobiusTreeCheck cg 1200001 10 98304 rootNode10_98304 = true :=
  mobiusTreeCheck_join cg 1200001 9 98304 _ _ mobiusValuePair006_checked mobiusValuePair007_checked

private def rootNode11_65536 : MobiusCertTree := .branch rootNode10_65536 rootNode10_98304
private theorem rootNode11_65536_checked : mobiusTreeCheck cg 1200001 11 65536 rootNode11_65536 = true :=
  mobiusTreeCheck_join cg 1200001 10 65536 _ _ rootNode10_65536_checked rootNode10_98304_checked

private def rootNode12_0 : MobiusCertTree := .branch rootNode11_0 rootNode11_65536
private theorem rootNode12_0_checked : mobiusTreeCheck cg 1200001 12 0 rootNode12_0 = true :=
  mobiusTreeCheck_join cg 1200001 11 0 _ _ rootNode11_0_checked rootNode11_65536_checked

private def rootNode10_131072 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock016 mobiusTableBlock017) (MobiusCertTree.branch mobiusTableBlock018 mobiusTableBlock019)
private theorem rootNode10_131072_checked : mobiusTreeCheck cg 1200001 10 131072 rootNode10_131072 = true :=
  mobiusTreeCheck_join cg 1200001 9 131072 _ _ mobiusValuePair008_checked mobiusValuePair009_checked

private def rootNode10_163840 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock020 mobiusTableBlock021) (MobiusCertTree.branch mobiusTableBlock022 mobiusTableBlock023)
private theorem rootNode10_163840_checked : mobiusTreeCheck cg 1200001 10 163840 rootNode10_163840 = true :=
  mobiusTreeCheck_join cg 1200001 9 163840 _ _ mobiusValuePair010_checked mobiusValuePair011_checked

private def rootNode11_131072 : MobiusCertTree := .branch rootNode10_131072 rootNode10_163840
private theorem rootNode11_131072_checked : mobiusTreeCheck cg 1200001 11 131072 rootNode11_131072 = true :=
  mobiusTreeCheck_join cg 1200001 10 131072 _ _ rootNode10_131072_checked rootNode10_163840_checked

private def rootNode10_196608 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock024 mobiusTableBlock025) (MobiusCertTree.branch mobiusTableBlock026 mobiusTableBlock027)
private theorem rootNode10_196608_checked : mobiusTreeCheck cg 1200001 10 196608 rootNode10_196608 = true :=
  mobiusTreeCheck_join cg 1200001 9 196608 _ _ mobiusValuePair012_checked mobiusValuePair013_checked

private def rootNode10_229376 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock028 mobiusTableBlock029) (MobiusCertTree.branch mobiusTableBlock030 mobiusTableBlock031)
private theorem rootNode10_229376_checked : mobiusTreeCheck cg 1200001 10 229376 rootNode10_229376 = true :=
  mobiusTreeCheck_join cg 1200001 9 229376 _ _ mobiusValuePair014_checked mobiusValuePair015_checked

private def rootNode11_196608 : MobiusCertTree := .branch rootNode10_196608 rootNode10_229376
private theorem rootNode11_196608_checked : mobiusTreeCheck cg 1200001 11 196608 rootNode11_196608 = true :=
  mobiusTreeCheck_join cg 1200001 10 196608 _ _ rootNode10_196608_checked rootNode10_229376_checked

private def rootNode12_131072 : MobiusCertTree := .branch rootNode11_131072 rootNode11_196608
private theorem rootNode12_131072_checked : mobiusTreeCheck cg 1200001 12 131072 rootNode12_131072 = true :=
  mobiusTreeCheck_join cg 1200001 11 131072 _ _ rootNode11_131072_checked rootNode11_196608_checked

private def rootNode13_0 : MobiusCertTree := .branch rootNode12_0 rootNode12_131072
private theorem rootNode13_0_checked : mobiusTreeCheck cg 1200001 13 0 rootNode13_0 = true :=
  mobiusTreeCheck_join cg 1200001 12 0 _ _ rootNode12_0_checked rootNode12_131072_checked

private def rootNode10_262144 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock032 mobiusTableBlock033) (MobiusCertTree.branch mobiusTableBlock034 mobiusTableBlock035)
private theorem rootNode10_262144_checked : mobiusTreeCheck cg 1200001 10 262144 rootNode10_262144 = true :=
  mobiusTreeCheck_join cg 1200001 9 262144 _ _ mobiusValuePair016_checked mobiusValuePair017_checked

private def rootNode10_294912 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock036 mobiusTableBlock037) (MobiusCertTree.branch mobiusTableBlock038 mobiusTableBlock039)
private theorem rootNode10_294912_checked : mobiusTreeCheck cg 1200001 10 294912 rootNode10_294912 = true :=
  mobiusTreeCheck_join cg 1200001 9 294912 _ _ mobiusValuePair018_checked mobiusValuePair019_checked

private def rootNode11_262144 : MobiusCertTree := .branch rootNode10_262144 rootNode10_294912
private theorem rootNode11_262144_checked : mobiusTreeCheck cg 1200001 11 262144 rootNode11_262144 = true :=
  mobiusTreeCheck_join cg 1200001 10 262144 _ _ rootNode10_262144_checked rootNode10_294912_checked

private def rootNode10_327680 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock040 mobiusTableBlock041) (MobiusCertTree.branch mobiusTableBlock042 mobiusTableBlock043)
private theorem rootNode10_327680_checked : mobiusTreeCheck cg 1200001 10 327680 rootNode10_327680 = true :=
  mobiusTreeCheck_join cg 1200001 9 327680 _ _ mobiusValuePair020_checked mobiusValuePair021_checked

private def rootNode10_360448 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock044 mobiusTableBlock045) (MobiusCertTree.branch mobiusTableBlock046 mobiusTableBlock047)
private theorem rootNode10_360448_checked : mobiusTreeCheck cg 1200001 10 360448 rootNode10_360448 = true :=
  mobiusTreeCheck_join cg 1200001 9 360448 _ _ mobiusValuePair022_checked mobiusValuePair023_checked

private def rootNode11_327680 : MobiusCertTree := .branch rootNode10_327680 rootNode10_360448
private theorem rootNode11_327680_checked : mobiusTreeCheck cg 1200001 11 327680 rootNode11_327680 = true :=
  mobiusTreeCheck_join cg 1200001 10 327680 _ _ rootNode10_327680_checked rootNode10_360448_checked

private def rootNode12_262144 : MobiusCertTree := .branch rootNode11_262144 rootNode11_327680
private theorem rootNode12_262144_checked : mobiusTreeCheck cg 1200001 12 262144 rootNode12_262144 = true :=
  mobiusTreeCheck_join cg 1200001 11 262144 _ _ rootNode11_262144_checked rootNode11_327680_checked

private def rootNode10_393216 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock048 mobiusTableBlock049) (MobiusCertTree.branch mobiusTableBlock050 mobiusTableBlock051)
private theorem rootNode10_393216_checked : mobiusTreeCheck cg 1200001 10 393216 rootNode10_393216 = true :=
  mobiusTreeCheck_join cg 1200001 9 393216 _ _ mobiusValuePair024_checked mobiusValuePair025_checked

private def rootNode10_425984 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock052 mobiusTableBlock053) (MobiusCertTree.branch mobiusTableBlock054 mobiusTableBlock055)
private theorem rootNode10_425984_checked : mobiusTreeCheck cg 1200001 10 425984 rootNode10_425984 = true :=
  mobiusTreeCheck_join cg 1200001 9 425984 _ _ mobiusValuePair026_checked mobiusValuePair027_checked

private def rootNode11_393216 : MobiusCertTree := .branch rootNode10_393216 rootNode10_425984
private theorem rootNode11_393216_checked : mobiusTreeCheck cg 1200001 11 393216 rootNode11_393216 = true :=
  mobiusTreeCheck_join cg 1200001 10 393216 _ _ rootNode10_393216_checked rootNode10_425984_checked

private def rootNode10_458752 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock056 mobiusTableBlock057) (MobiusCertTree.branch mobiusTableBlock058 mobiusTableBlock059)
private theorem rootNode10_458752_checked : mobiusTreeCheck cg 1200001 10 458752 rootNode10_458752 = true :=
  mobiusTreeCheck_join cg 1200001 9 458752 _ _ mobiusValuePair028_checked mobiusValuePair029_checked

private def rootNode10_491520 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock060 mobiusTableBlock061) (MobiusCertTree.branch mobiusTableBlock062 mobiusTableBlock063)
private theorem rootNode10_491520_checked : mobiusTreeCheck cg 1200001 10 491520 rootNode10_491520 = true :=
  mobiusTreeCheck_join cg 1200001 9 491520 _ _ mobiusValuePair030_checked mobiusValuePair031_checked

private def rootNode11_458752 : MobiusCertTree := .branch rootNode10_458752 rootNode10_491520
private theorem rootNode11_458752_checked : mobiusTreeCheck cg 1200001 11 458752 rootNode11_458752 = true :=
  mobiusTreeCheck_join cg 1200001 10 458752 _ _ rootNode10_458752_checked rootNode10_491520_checked

private def rootNode12_393216 : MobiusCertTree := .branch rootNode11_393216 rootNode11_458752
private theorem rootNode12_393216_checked : mobiusTreeCheck cg 1200001 12 393216 rootNode12_393216 = true :=
  mobiusTreeCheck_join cg 1200001 11 393216 _ _ rootNode11_393216_checked rootNode11_458752_checked

private def rootNode13_262144 : MobiusCertTree := .branch rootNode12_262144 rootNode12_393216
private theorem rootNode13_262144_checked : mobiusTreeCheck cg 1200001 13 262144 rootNode13_262144 = true :=
  mobiusTreeCheck_join cg 1200001 12 262144 _ _ rootNode12_262144_checked rootNode12_393216_checked

private def rootNode14_0 : MobiusCertTree := .branch rootNode13_0 rootNode13_262144
private theorem rootNode14_0_checked : mobiusTreeCheck cg 1200001 14 0 rootNode14_0 = true :=
  mobiusTreeCheck_join cg 1200001 13 0 _ _ rootNode13_0_checked rootNode13_262144_checked

private def rootNode10_524288 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock064 mobiusTableBlock065) (MobiusCertTree.branch mobiusTableBlock066 mobiusTableBlock067)
private theorem rootNode10_524288_checked : mobiusTreeCheck cg 1200001 10 524288 rootNode10_524288 = true :=
  mobiusTreeCheck_join cg 1200001 9 524288 _ _ mobiusValuePair032_checked mobiusValuePair033_checked

private def rootNode10_557056 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock068 mobiusTableBlock069) (MobiusCertTree.branch mobiusTableBlock070 mobiusTableBlock071)
private theorem rootNode10_557056_checked : mobiusTreeCheck cg 1200001 10 557056 rootNode10_557056 = true :=
  mobiusTreeCheck_join cg 1200001 9 557056 _ _ mobiusValuePair034_checked mobiusValuePair035_checked

private def rootNode11_524288 : MobiusCertTree := .branch rootNode10_524288 rootNode10_557056
private theorem rootNode11_524288_checked : mobiusTreeCheck cg 1200001 11 524288 rootNode11_524288 = true :=
  mobiusTreeCheck_join cg 1200001 10 524288 _ _ rootNode10_524288_checked rootNode10_557056_checked

private def rootNode10_589824 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock072 mobiusTableBlock073) (MobiusCertTree.branch mobiusTableBlock074 mobiusTableBlock075)
private theorem rootNode10_589824_checked : mobiusTreeCheck cg 1200001 10 589824 rootNode10_589824 = true :=
  mobiusTreeCheck_join cg 1200001 9 589824 _ _ mobiusValuePair036_checked mobiusValuePair037_checked

private def rootNode10_622592 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock076 mobiusTableBlock077) (MobiusCertTree.branch mobiusTableBlock078 mobiusTableBlock079)
private theorem rootNode10_622592_checked : mobiusTreeCheck cg 1200001 10 622592 rootNode10_622592 = true :=
  mobiusTreeCheck_join cg 1200001 9 622592 _ _ mobiusValuePair038_checked mobiusValuePair039_checked

private def rootNode11_589824 : MobiusCertTree := .branch rootNode10_589824 rootNode10_622592
private theorem rootNode11_589824_checked : mobiusTreeCheck cg 1200001 11 589824 rootNode11_589824 = true :=
  mobiusTreeCheck_join cg 1200001 10 589824 _ _ rootNode10_589824_checked rootNode10_622592_checked

private def rootNode12_524288 : MobiusCertTree := .branch rootNode11_524288 rootNode11_589824
private theorem rootNode12_524288_checked : mobiusTreeCheck cg 1200001 12 524288 rootNode12_524288 = true :=
  mobiusTreeCheck_join cg 1200001 11 524288 _ _ rootNode11_524288_checked rootNode11_589824_checked

private def rootNode10_655360 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock080 mobiusTableBlock081) (MobiusCertTree.branch mobiusTableBlock082 mobiusTableBlock083)
private theorem rootNode10_655360_checked : mobiusTreeCheck cg 1200001 10 655360 rootNode10_655360 = true :=
  mobiusTreeCheck_join cg 1200001 9 655360 _ _ mobiusValuePair040_checked mobiusValuePair041_checked

private def rootNode10_688128 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock084 mobiusTableBlock085) (MobiusCertTree.branch mobiusTableBlock086 mobiusTableBlock087)
private theorem rootNode10_688128_checked : mobiusTreeCheck cg 1200001 10 688128 rootNode10_688128 = true :=
  mobiusTreeCheck_join cg 1200001 9 688128 _ _ mobiusValuePair042_checked mobiusValuePair043_checked

private def rootNode11_655360 : MobiusCertTree := .branch rootNode10_655360 rootNode10_688128
private theorem rootNode11_655360_checked : mobiusTreeCheck cg 1200001 11 655360 rootNode11_655360 = true :=
  mobiusTreeCheck_join cg 1200001 10 655360 _ _ rootNode10_655360_checked rootNode10_688128_checked

private def rootNode10_720896 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock088 mobiusTableBlock089) (MobiusCertTree.branch mobiusTableBlock090 mobiusTableBlock091)
private theorem rootNode10_720896_checked : mobiusTreeCheck cg 1200001 10 720896 rootNode10_720896 = true :=
  mobiusTreeCheck_join cg 1200001 9 720896 _ _ mobiusValuePair044_checked mobiusValuePair045_checked

private def rootNode10_753664 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock092 mobiusTableBlock093) (MobiusCertTree.branch mobiusTableBlock094 mobiusTableBlock095)
private theorem rootNode10_753664_checked : mobiusTreeCheck cg 1200001 10 753664 rootNode10_753664 = true :=
  mobiusTreeCheck_join cg 1200001 9 753664 _ _ mobiusValuePair046_checked mobiusValuePair047_checked

private def rootNode11_720896 : MobiusCertTree := .branch rootNode10_720896 rootNode10_753664
private theorem rootNode11_720896_checked : mobiusTreeCheck cg 1200001 11 720896 rootNode11_720896 = true :=
  mobiusTreeCheck_join cg 1200001 10 720896 _ _ rootNode10_720896_checked rootNode10_753664_checked

private def rootNode12_655360 : MobiusCertTree := .branch rootNode11_655360 rootNode11_720896
private theorem rootNode12_655360_checked : mobiusTreeCheck cg 1200001 12 655360 rootNode12_655360 = true :=
  mobiusTreeCheck_join cg 1200001 11 655360 _ _ rootNode11_655360_checked rootNode11_720896_checked

private def rootNode13_524288 : MobiusCertTree := .branch rootNode12_524288 rootNode12_655360
private theorem rootNode13_524288_checked : mobiusTreeCheck cg 1200001 13 524288 rootNode13_524288 = true :=
  mobiusTreeCheck_join cg 1200001 12 524288 _ _ rootNode12_524288_checked rootNode12_655360_checked

private def rootNode10_786432 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock096 mobiusTableBlock097) (MobiusCertTree.branch mobiusTableBlock098 mobiusTableBlock099)
private theorem rootNode10_786432_checked : mobiusTreeCheck cg 1200001 10 786432 rootNode10_786432 = true :=
  mobiusTreeCheck_join cg 1200001 9 786432 _ _ mobiusValuePair048_checked mobiusValuePair049_checked

private def rootNode10_819200 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock100 mobiusTableBlock101) (MobiusCertTree.branch mobiusTableBlock102 mobiusTableBlock103)
private theorem rootNode10_819200_checked : mobiusTreeCheck cg 1200001 10 819200 rootNode10_819200 = true :=
  mobiusTreeCheck_join cg 1200001 9 819200 _ _ mobiusValuePair050_checked mobiusValuePair051_checked

private def rootNode11_786432 : MobiusCertTree := .branch rootNode10_786432 rootNode10_819200
private theorem rootNode11_786432_checked : mobiusTreeCheck cg 1200001 11 786432 rootNode11_786432 = true :=
  mobiusTreeCheck_join cg 1200001 10 786432 _ _ rootNode10_786432_checked rootNode10_819200_checked

private def rootNode10_851968 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock104 mobiusTableBlock105) (MobiusCertTree.branch mobiusTableBlock106 mobiusTableBlock107)
private theorem rootNode10_851968_checked : mobiusTreeCheck cg 1200001 10 851968 rootNode10_851968 = true :=
  mobiusTreeCheck_join cg 1200001 9 851968 _ _ mobiusValuePair052_checked mobiusValuePair053_checked

private def rootNode10_884736 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock108 mobiusTableBlock109) (MobiusCertTree.branch mobiusTableBlock110 mobiusTableBlock111)
private theorem rootNode10_884736_checked : mobiusTreeCheck cg 1200001 10 884736 rootNode10_884736 = true :=
  mobiusTreeCheck_join cg 1200001 9 884736 _ _ mobiusValuePair054_checked mobiusValuePair055_checked

private def rootNode11_851968 : MobiusCertTree := .branch rootNode10_851968 rootNode10_884736
private theorem rootNode11_851968_checked : mobiusTreeCheck cg 1200001 11 851968 rootNode11_851968 = true :=
  mobiusTreeCheck_join cg 1200001 10 851968 _ _ rootNode10_851968_checked rootNode10_884736_checked

private def rootNode12_786432 : MobiusCertTree := .branch rootNode11_786432 rootNode11_851968
private theorem rootNode12_786432_checked : mobiusTreeCheck cg 1200001 12 786432 rootNode12_786432 = true :=
  mobiusTreeCheck_join cg 1200001 11 786432 _ _ rootNode11_786432_checked rootNode11_851968_checked

private def rootNode10_917504 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock112 mobiusTableBlock113) (MobiusCertTree.branch mobiusTableBlock114 mobiusTableBlock115)
private theorem rootNode10_917504_checked : mobiusTreeCheck cg 1200001 10 917504 rootNode10_917504 = true :=
  mobiusTreeCheck_join cg 1200001 9 917504 _ _ mobiusValuePair056_checked mobiusValuePair057_checked

private def rootNode10_950272 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock116 mobiusTableBlock117) (MobiusCertTree.branch mobiusTableBlock118 mobiusTableBlock119)
private theorem rootNode10_950272_checked : mobiusTreeCheck cg 1200001 10 950272 rootNode10_950272 = true :=
  mobiusTreeCheck_join cg 1200001 9 950272 _ _ mobiusValuePair058_checked mobiusValuePair059_checked

private def rootNode11_917504 : MobiusCertTree := .branch rootNode10_917504 rootNode10_950272
private theorem rootNode11_917504_checked : mobiusTreeCheck cg 1200001 11 917504 rootNode11_917504 = true :=
  mobiusTreeCheck_join cg 1200001 10 917504 _ _ rootNode10_917504_checked rootNode10_950272_checked

private def rootNode10_983040 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock120 mobiusTableBlock121) (MobiusCertTree.branch mobiusTableBlock122 mobiusTableBlock123)
private theorem rootNode10_983040_checked : mobiusTreeCheck cg 1200001 10 983040 rootNode10_983040 = true :=
  mobiusTreeCheck_join cg 1200001 9 983040 _ _ mobiusValuePair060_checked mobiusValuePair061_checked

private def rootNode10_1015808 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock124 mobiusTableBlock125) (MobiusCertTree.branch mobiusTableBlock126 mobiusTableBlock127)
private theorem rootNode10_1015808_checked : mobiusTreeCheck cg 1200001 10 1015808 rootNode10_1015808 = true :=
  mobiusTreeCheck_join cg 1200001 9 1015808 _ _ mobiusValuePair062_checked mobiusValuePair063_checked

private def rootNode11_983040 : MobiusCertTree := .branch rootNode10_983040 rootNode10_1015808
private theorem rootNode11_983040_checked : mobiusTreeCheck cg 1200001 11 983040 rootNode11_983040 = true :=
  mobiusTreeCheck_join cg 1200001 10 983040 _ _ rootNode10_983040_checked rootNode10_1015808_checked

private def rootNode12_917504 : MobiusCertTree := .branch rootNode11_917504 rootNode11_983040
private theorem rootNode12_917504_checked : mobiusTreeCheck cg 1200001 12 917504 rootNode12_917504 = true :=
  mobiusTreeCheck_join cg 1200001 11 917504 _ _ rootNode11_917504_checked rootNode11_983040_checked

private def rootNode13_786432 : MobiusCertTree := .branch rootNode12_786432 rootNode12_917504
private theorem rootNode13_786432_checked : mobiusTreeCheck cg 1200001 13 786432 rootNode13_786432 = true :=
  mobiusTreeCheck_join cg 1200001 12 786432 _ _ rootNode12_786432_checked rootNode12_917504_checked

private def rootNode14_524288 : MobiusCertTree := .branch rootNode13_524288 rootNode13_786432
private theorem rootNode14_524288_checked : mobiusTreeCheck cg 1200001 14 524288 rootNode14_524288 = true :=
  mobiusTreeCheck_join cg 1200001 13 524288 _ _ rootNode13_524288_checked rootNode13_786432_checked

private def rootNode15_0 : MobiusCertTree := .branch rootNode14_0 rootNode14_524288
private theorem rootNode15_0_checked : mobiusTreeCheck cg 1200001 15 0 rootNode15_0 = true :=
  mobiusTreeCheck_join cg 1200001 14 0 _ _ rootNode14_0_checked rootNode14_524288_checked

private def rootNode10_1048576 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock128 mobiusTableBlock129) (MobiusCertTree.branch mobiusTableBlock130 mobiusTableBlock131)
private theorem rootNode10_1048576_checked : mobiusTreeCheck cg 1200001 10 1048576 rootNode10_1048576 = true :=
  mobiusTreeCheck_join cg 1200001 9 1048576 _ _ mobiusValuePair064_checked mobiusValuePair065_checked

private def rootNode10_1081344 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock132 mobiusTableBlock133) (MobiusCertTree.branch mobiusTableBlock134 mobiusTableBlock135)
private theorem rootNode10_1081344_checked : mobiusTreeCheck cg 1200001 10 1081344 rootNode10_1081344 = true :=
  mobiusTreeCheck_join cg 1200001 9 1081344 _ _ mobiusValuePair066_checked mobiusValuePair067_checked

private def rootNode11_1048576 : MobiusCertTree := .branch rootNode10_1048576 rootNode10_1081344
private theorem rootNode11_1048576_checked : mobiusTreeCheck cg 1200001 11 1048576 rootNode11_1048576 = true :=
  mobiusTreeCheck_join cg 1200001 10 1048576 _ _ rootNode10_1048576_checked rootNode10_1081344_checked

private def rootNode10_1114112 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock136 mobiusTableBlock137) (MobiusCertTree.branch mobiusTableBlock138 mobiusTableBlock139)
private theorem rootNode10_1114112_checked : mobiusTreeCheck cg 1200001 10 1114112 rootNode10_1114112 = true :=
  mobiusTreeCheck_join cg 1200001 9 1114112 _ _ mobiusValuePair068_checked mobiusValuePair069_checked

private def rootNode10_1146880 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock140 mobiusTableBlock141) (MobiusCertTree.branch mobiusTableBlock142 mobiusTableBlock143)
private theorem rootNode10_1146880_checked : mobiusTreeCheck cg 1200001 10 1146880 rootNode10_1146880 = true :=
  mobiusTreeCheck_join cg 1200001 9 1146880 _ _ mobiusValuePair070_checked mobiusValuePair071_checked

private def rootNode11_1114112 : MobiusCertTree := .branch rootNode10_1114112 rootNode10_1146880
private theorem rootNode11_1114112_checked : mobiusTreeCheck cg 1200001 11 1114112 rootNode11_1114112 = true :=
  mobiusTreeCheck_join cg 1200001 10 1114112 _ _ rootNode10_1114112_checked rootNode10_1146880_checked

private def rootNode12_1048576 : MobiusCertTree := .branch rootNode11_1048576 rootNode11_1114112
private theorem rootNode12_1048576_checked : mobiusTreeCheck cg 1200001 12 1048576 rootNode12_1048576 = true :=
  mobiusTreeCheck_join cg 1200001 11 1048576 _ _ rootNode11_1048576_checked rootNode11_1114112_checked

private def rootNode10_1179648 : MobiusCertTree := .branch (MobiusCertTree.branch mobiusTableBlock144 mobiusTableBlock145) (MobiusCertTree.branch mobiusTableBlock146 (MobiusCertTree.leaf 0 0))
private theorem rootNode10_1179648_checked : mobiusTreeCheck cg 1200001 10 1179648 rootNode10_1179648 = true :=
  mobiusTreeCheck_join cg 1200001 9 1179648 _ _ mobiusValuePair072_checked mobiusValuePair073_checked

private def rootNode10_1212416 : MobiusCertTree := .leaf 0 0
private theorem rootNode10_1212416_checked : mobiusTreeCheck cg 1200001 10 1212416 rootNode10_1212416 = true := by decide +kernel

private def rootNode11_1179648 : MobiusCertTree := .branch rootNode10_1179648 rootNode10_1212416
private theorem rootNode11_1179648_checked : mobiusTreeCheck cg 1200001 11 1179648 rootNode11_1179648 = true :=
  mobiusTreeCheck_join cg 1200001 10 1179648 _ _ rootNode10_1179648_checked rootNode10_1212416_checked

private def rootNode11_1245184 : MobiusCertTree := .leaf 0 0
private theorem rootNode11_1245184_checked : mobiusTreeCheck cg 1200001 11 1245184 rootNode11_1245184 = true := by decide +kernel

private def rootNode12_1179648 : MobiusCertTree := .branch rootNode11_1179648 rootNode11_1245184
private theorem rootNode12_1179648_checked : mobiusTreeCheck cg 1200001 12 1179648 rootNode12_1179648 = true :=
  mobiusTreeCheck_join cg 1200001 11 1179648 _ _ rootNode11_1179648_checked rootNode11_1245184_checked

private def rootNode13_1048576 : MobiusCertTree := .branch rootNode12_1048576 rootNode12_1179648
private theorem rootNode13_1048576_checked : mobiusTreeCheck cg 1200001 13 1048576 rootNode13_1048576 = true :=
  mobiusTreeCheck_join cg 1200001 12 1048576 _ _ rootNode12_1048576_checked rootNode12_1179648_checked

private def rootNode13_1310720 : MobiusCertTree := .leaf 0 0
private theorem rootNode13_1310720_checked : mobiusTreeCheck cg 1200001 13 1310720 rootNode13_1310720 = true := by decide +kernel

private def rootNode14_1048576 : MobiusCertTree := .branch rootNode13_1048576 rootNode13_1310720
private theorem rootNode14_1048576_checked : mobiusTreeCheck cg 1200001 14 1048576 rootNode14_1048576 = true :=
  mobiusTreeCheck_join cg 1200001 13 1048576 _ _ rootNode13_1048576_checked rootNode13_1310720_checked

private def rootNode14_1572864 : MobiusCertTree := .leaf 0 0
private theorem rootNode14_1572864_checked : mobiusTreeCheck cg 1200001 14 1572864 rootNode14_1572864 = true := by decide +kernel

private def rootNode15_1048576 : MobiusCertTree := .branch rootNode14_1048576 rootNode14_1572864
private theorem rootNode15_1048576_checked : mobiusTreeCheck cg 1200001 15 1048576 rootNode15_1048576 = true :=
  mobiusTreeCheck_join cg 1200001 14 1048576 _ _ rootNode14_1048576_checked rootNode14_1572864_checked

private def rootNode16_0 : MobiusCertTree := .branch rootNode15_0 rootNode15_1048576
private theorem rootNode16_0_checked : mobiusTreeCheck cg 1200001 16 0 rootNode16_0 = true :=
  mobiusTreeCheck_join cg 1200001 15 0 _ _ rootNode15_0_checked rootNode15_1048576_checked

end Helfgott
open Helfgott
theorem solution : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 16 0 mobiusTable1200001 = true := Helfgott.rootNode16_0_checked
#print axioms solution
