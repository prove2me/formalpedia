-- Prove2me | solution 1 for Helfgott.mobiusReciprocalSqrt1200001_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T05:49:05.407429+00:00
-- url     : https://prove2.me/submissions/be553c75-6e39-4706-bd82-c28e150df7fb

import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001
import Mathlib.Tactic
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair000_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair001_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair002_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair003_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair004_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair005_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair006_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair007_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair008_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair009_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair010_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair011_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair012_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair013_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair014_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair015_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair016_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair017_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair018_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair019_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair020_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair021_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair022_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair023_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair024_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair025_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair026_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair027_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair028_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair029_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair030_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair031_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair032_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair033_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair034_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair035_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair036_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair037_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair038_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair039_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair040_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair041_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair042_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair043_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair044_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair045_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair046_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair047_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair048_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair049_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair050_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair051_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair052_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair053_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair054_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair055_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair056_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair057_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair058_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair059_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair060_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair061_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair062_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair063_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair064_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair065_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair066_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair067_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair068_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair069_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair070_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair071_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair072_checked
import Theorems.Thm_Helfgott_mobiusReciprocalSqrtPair073_checked


set_option autoImplicit false
namespace Helfgott

theorem closedSqrtRootJoin (g : ℕ → ℤ) (Q B d offset : ℕ)
    (l r : MobiusReciprocalTree) (hoff : offset < B)
    (hl : mobiusReciprocalSqrtTreeCheck g Q B d offset l = true)
    (hr : mobiusReciprocalSqrtTreeCheck g Q B d (offset + 32 * 2 ^ d) r = true)
    (hjoin : mobiusReciprocalFinish l = mobiusReciprocalStart r) :
    mobiusReciprocalSqrtTreeCheck g Q B (d + 1) offset (.branch l r) = true := by
  have hnot : ¬ B ≤ offset := by omega
  simp only [mobiusReciprocalSqrtTreeCheck, if_neg hnot, hl, hr, hjoin,
    beq_self_eq_true, Bool.and_self]

end Helfgott
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Helfgott

private def recipFullNode10_0 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block000 mobiusReciprocal1200001Block001) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block002 mobiusReciprocal1200001Block003)
private theorem recipFullNode10_0_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 0 recipFullNode10_0 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 0 _ _ (by decide) mobiusReciprocalSqrtPair000_checked mobiusReciprocalSqrtPair001_checked (by decide +kernel)

private def recipFullNode10_32768 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block004 mobiusReciprocal1200001Block005) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block006 mobiusReciprocal1200001Block007)
private theorem recipFullNode10_32768_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 32768 recipFullNode10_32768 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 32768 _ _ (by decide) mobiusReciprocalSqrtPair002_checked mobiusReciprocalSqrtPair003_checked (by decide +kernel)

private def recipFullNode11_0 : MobiusReciprocalTree := .branch recipFullNode10_0 recipFullNode10_32768
private theorem recipFullNode11_0_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 0 recipFullNode11_0 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 0 _ _ (by decide) recipFullNode10_0_checked recipFullNode10_32768_checked (by decide +kernel)

private def recipFullNode10_65536 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block008 mobiusReciprocal1200001Block009) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block010 mobiusReciprocal1200001Block011)
private theorem recipFullNode10_65536_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 65536 recipFullNode10_65536 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 65536 _ _ (by decide) mobiusReciprocalSqrtPair004_checked mobiusReciprocalSqrtPair005_checked (by decide +kernel)

private def recipFullNode10_98304 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block012 mobiusReciprocal1200001Block013) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block014 mobiusReciprocal1200001Block015)
private theorem recipFullNode10_98304_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 98304 recipFullNode10_98304 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 98304 _ _ (by decide) mobiusReciprocalSqrtPair006_checked mobiusReciprocalSqrtPair007_checked (by decide +kernel)

private def recipFullNode11_65536 : MobiusReciprocalTree := .branch recipFullNode10_65536 recipFullNode10_98304
private theorem recipFullNode11_65536_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 65536 recipFullNode11_65536 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 65536 _ _ (by decide) recipFullNode10_65536_checked recipFullNode10_98304_checked (by decide +kernel)

private def recipFullNode12_0 : MobiusReciprocalTree := .branch recipFullNode11_0 recipFullNode11_65536
private theorem recipFullNode12_0_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 12 0 recipFullNode12_0 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 0 _ _ (by decide) recipFullNode11_0_checked recipFullNode11_65536_checked (by decide +kernel)

private def recipFullNode10_131072 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block016 mobiusReciprocal1200001Block017) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block018 mobiusReciprocal1200001Block019)
private theorem recipFullNode10_131072_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 131072 recipFullNode10_131072 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 131072 _ _ (by decide) mobiusReciprocalSqrtPair008_checked mobiusReciprocalSqrtPair009_checked (by decide +kernel)

private def recipFullNode10_163840 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block020 mobiusReciprocal1200001Block021) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block022 mobiusReciprocal1200001Block023)
private theorem recipFullNode10_163840_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 163840 recipFullNode10_163840 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 163840 _ _ (by decide) mobiusReciprocalSqrtPair010_checked mobiusReciprocalSqrtPair011_checked (by decide +kernel)

private def recipFullNode11_131072 : MobiusReciprocalTree := .branch recipFullNode10_131072 recipFullNode10_163840
private theorem recipFullNode11_131072_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 131072 recipFullNode11_131072 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 131072 _ _ (by decide) recipFullNode10_131072_checked recipFullNode10_163840_checked (by decide +kernel)

private def recipFullNode10_196608 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block024 mobiusReciprocal1200001Block025) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block026 mobiusReciprocal1200001Block027)
private theorem recipFullNode10_196608_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 196608 recipFullNode10_196608 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 196608 _ _ (by decide) mobiusReciprocalSqrtPair012_checked mobiusReciprocalSqrtPair013_checked (by decide +kernel)

private def recipFullNode10_229376 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block028 mobiusReciprocal1200001Block029) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block030 mobiusReciprocal1200001Block031)
private theorem recipFullNode10_229376_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 229376 recipFullNode10_229376 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 229376 _ _ (by decide) mobiusReciprocalSqrtPair014_checked mobiusReciprocalSqrtPair015_checked (by decide +kernel)

private def recipFullNode11_196608 : MobiusReciprocalTree := .branch recipFullNode10_196608 recipFullNode10_229376
private theorem recipFullNode11_196608_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 196608 recipFullNode11_196608 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 196608 _ _ (by decide) recipFullNode10_196608_checked recipFullNode10_229376_checked (by decide +kernel)

private def recipFullNode12_131072 : MobiusReciprocalTree := .branch recipFullNode11_131072 recipFullNode11_196608
private theorem recipFullNode12_131072_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 12 131072 recipFullNode12_131072 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 131072 _ _ (by decide) recipFullNode11_131072_checked recipFullNode11_196608_checked (by decide +kernel)

private def recipFullNode13_0 : MobiusReciprocalTree := .branch recipFullNode12_0 recipFullNode12_131072
private theorem recipFullNode13_0_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 13 0 recipFullNode13_0 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 12 0 _ _ (by decide) recipFullNode12_0_checked recipFullNode12_131072_checked (by decide +kernel)

private def recipFullNode10_262144 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block032 mobiusReciprocal1200001Block033) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block034 mobiusReciprocal1200001Block035)
private theorem recipFullNode10_262144_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 262144 recipFullNode10_262144 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 262144 _ _ (by decide) mobiusReciprocalSqrtPair016_checked mobiusReciprocalSqrtPair017_checked (by decide +kernel)

private def recipFullNode10_294912 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block036 mobiusReciprocal1200001Block037) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block038 mobiusReciprocal1200001Block039)
private theorem recipFullNode10_294912_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 294912 recipFullNode10_294912 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 294912 _ _ (by decide) mobiusReciprocalSqrtPair018_checked mobiusReciprocalSqrtPair019_checked (by decide +kernel)

private def recipFullNode11_262144 : MobiusReciprocalTree := .branch recipFullNode10_262144 recipFullNode10_294912
private theorem recipFullNode11_262144_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 262144 recipFullNode11_262144 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 262144 _ _ (by decide) recipFullNode10_262144_checked recipFullNode10_294912_checked (by decide +kernel)

private def recipFullNode10_327680 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block040 mobiusReciprocal1200001Block041) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block042 mobiusReciprocal1200001Block043)
private theorem recipFullNode10_327680_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 327680 recipFullNode10_327680 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 327680 _ _ (by decide) mobiusReciprocalSqrtPair020_checked mobiusReciprocalSqrtPair021_checked (by decide +kernel)

private def recipFullNode10_360448 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block044 mobiusReciprocal1200001Block045) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block046 mobiusReciprocal1200001Block047)
private theorem recipFullNode10_360448_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 360448 recipFullNode10_360448 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 360448 _ _ (by decide) mobiusReciprocalSqrtPair022_checked mobiusReciprocalSqrtPair023_checked (by decide +kernel)

private def recipFullNode11_327680 : MobiusReciprocalTree := .branch recipFullNode10_327680 recipFullNode10_360448
private theorem recipFullNode11_327680_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 327680 recipFullNode11_327680 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 327680 _ _ (by decide) recipFullNode10_327680_checked recipFullNode10_360448_checked (by decide +kernel)

private def recipFullNode12_262144 : MobiusReciprocalTree := .branch recipFullNode11_262144 recipFullNode11_327680
private theorem recipFullNode12_262144_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 12 262144 recipFullNode12_262144 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 262144 _ _ (by decide) recipFullNode11_262144_checked recipFullNode11_327680_checked (by decide +kernel)

private def recipFullNode10_393216 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block048 mobiusReciprocal1200001Block049) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block050 mobiusReciprocal1200001Block051)
private theorem recipFullNode10_393216_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 393216 recipFullNode10_393216 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 393216 _ _ (by decide) mobiusReciprocalSqrtPair024_checked mobiusReciprocalSqrtPair025_checked (by decide +kernel)

private def recipFullNode10_425984 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block052 mobiusReciprocal1200001Block053) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block054 mobiusReciprocal1200001Block055)
private theorem recipFullNode10_425984_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 425984 recipFullNode10_425984 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 425984 _ _ (by decide) mobiusReciprocalSqrtPair026_checked mobiusReciprocalSqrtPair027_checked (by decide +kernel)

private def recipFullNode11_393216 : MobiusReciprocalTree := .branch recipFullNode10_393216 recipFullNode10_425984
private theorem recipFullNode11_393216_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 393216 recipFullNode11_393216 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 393216 _ _ (by decide) recipFullNode10_393216_checked recipFullNode10_425984_checked (by decide +kernel)

private def recipFullNode10_458752 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block056 mobiusReciprocal1200001Block057) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block058 mobiusReciprocal1200001Block059)
private theorem recipFullNode10_458752_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 458752 recipFullNode10_458752 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 458752 _ _ (by decide) mobiusReciprocalSqrtPair028_checked mobiusReciprocalSqrtPair029_checked (by decide +kernel)

private def recipFullNode10_491520 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block060 mobiusReciprocal1200001Block061) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block062 mobiusReciprocal1200001Block063)
private theorem recipFullNode10_491520_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 491520 recipFullNode10_491520 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 491520 _ _ (by decide) mobiusReciprocalSqrtPair030_checked mobiusReciprocalSqrtPair031_checked (by decide +kernel)

private def recipFullNode11_458752 : MobiusReciprocalTree := .branch recipFullNode10_458752 recipFullNode10_491520
private theorem recipFullNode11_458752_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 458752 recipFullNode11_458752 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 458752 _ _ (by decide) recipFullNode10_458752_checked recipFullNode10_491520_checked (by decide +kernel)

private def recipFullNode12_393216 : MobiusReciprocalTree := .branch recipFullNode11_393216 recipFullNode11_458752
private theorem recipFullNode12_393216_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 12 393216 recipFullNode12_393216 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 393216 _ _ (by decide) recipFullNode11_393216_checked recipFullNode11_458752_checked (by decide +kernel)

private def recipFullNode13_262144 : MobiusReciprocalTree := .branch recipFullNode12_262144 recipFullNode12_393216
private theorem recipFullNode13_262144_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 13 262144 recipFullNode13_262144 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 12 262144 _ _ (by decide) recipFullNode12_262144_checked recipFullNode12_393216_checked (by decide +kernel)

private def recipFullNode14_0 : MobiusReciprocalTree := .branch recipFullNode13_0 recipFullNode13_262144
private theorem recipFullNode14_0_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 14 0 recipFullNode14_0 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 13 0 _ _ (by decide) recipFullNode13_0_checked recipFullNode13_262144_checked (by decide +kernel)

private def recipFullNode10_524288 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block064 mobiusReciprocal1200001Block065) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block066 mobiusReciprocal1200001Block067)
private theorem recipFullNode10_524288_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 524288 recipFullNode10_524288 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 524288 _ _ (by decide) mobiusReciprocalSqrtPair032_checked mobiusReciprocalSqrtPair033_checked (by decide +kernel)

private def recipFullNode10_557056 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block068 mobiusReciprocal1200001Block069) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block070 mobiusReciprocal1200001Block071)
private theorem recipFullNode10_557056_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 557056 recipFullNode10_557056 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 557056 _ _ (by decide) mobiusReciprocalSqrtPair034_checked mobiusReciprocalSqrtPair035_checked (by decide +kernel)

private def recipFullNode11_524288 : MobiusReciprocalTree := .branch recipFullNode10_524288 recipFullNode10_557056
private theorem recipFullNode11_524288_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 524288 recipFullNode11_524288 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 524288 _ _ (by decide) recipFullNode10_524288_checked recipFullNode10_557056_checked (by decide +kernel)

private def recipFullNode10_589824 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block072 mobiusReciprocal1200001Block073) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block074 mobiusReciprocal1200001Block075)
private theorem recipFullNode10_589824_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 589824 recipFullNode10_589824 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 589824 _ _ (by decide) mobiusReciprocalSqrtPair036_checked mobiusReciprocalSqrtPair037_checked (by decide +kernel)

private def recipFullNode10_622592 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block076 mobiusReciprocal1200001Block077) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block078 mobiusReciprocal1200001Block079)
private theorem recipFullNode10_622592_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 622592 recipFullNode10_622592 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 622592 _ _ (by decide) mobiusReciprocalSqrtPair038_checked mobiusReciprocalSqrtPair039_checked (by decide +kernel)

private def recipFullNode11_589824 : MobiusReciprocalTree := .branch recipFullNode10_589824 recipFullNode10_622592
private theorem recipFullNode11_589824_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 589824 recipFullNode11_589824 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 589824 _ _ (by decide) recipFullNode10_589824_checked recipFullNode10_622592_checked (by decide +kernel)

private def recipFullNode12_524288 : MobiusReciprocalTree := .branch recipFullNode11_524288 recipFullNode11_589824
private theorem recipFullNode12_524288_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 12 524288 recipFullNode12_524288 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 524288 _ _ (by decide) recipFullNode11_524288_checked recipFullNode11_589824_checked (by decide +kernel)

private def recipFullNode10_655360 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block080 mobiusReciprocal1200001Block081) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block082 mobiusReciprocal1200001Block083)
private theorem recipFullNode10_655360_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 655360 recipFullNode10_655360 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 655360 _ _ (by decide) mobiusReciprocalSqrtPair040_checked mobiusReciprocalSqrtPair041_checked (by decide +kernel)

private def recipFullNode10_688128 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block084 mobiusReciprocal1200001Block085) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block086 mobiusReciprocal1200001Block087)
private theorem recipFullNode10_688128_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 688128 recipFullNode10_688128 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 688128 _ _ (by decide) mobiusReciprocalSqrtPair042_checked mobiusReciprocalSqrtPair043_checked (by decide +kernel)

private def recipFullNode11_655360 : MobiusReciprocalTree := .branch recipFullNode10_655360 recipFullNode10_688128
private theorem recipFullNode11_655360_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 655360 recipFullNode11_655360 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 655360 _ _ (by decide) recipFullNode10_655360_checked recipFullNode10_688128_checked (by decide +kernel)

private def recipFullNode10_720896 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block088 mobiusReciprocal1200001Block089) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block090 mobiusReciprocal1200001Block091)
private theorem recipFullNode10_720896_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 720896 recipFullNode10_720896 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 720896 _ _ (by decide) mobiusReciprocalSqrtPair044_checked mobiusReciprocalSqrtPair045_checked (by decide +kernel)

private def recipFullNode10_753664 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block092 mobiusReciprocal1200001Block093) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block094 mobiusReciprocal1200001Block095)
private theorem recipFullNode10_753664_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 753664 recipFullNode10_753664 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 753664 _ _ (by decide) mobiusReciprocalSqrtPair046_checked mobiusReciprocalSqrtPair047_checked (by decide +kernel)

private def recipFullNode11_720896 : MobiusReciprocalTree := .branch recipFullNode10_720896 recipFullNode10_753664
private theorem recipFullNode11_720896_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 720896 recipFullNode11_720896 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 720896 _ _ (by decide) recipFullNode10_720896_checked recipFullNode10_753664_checked (by decide +kernel)

private def recipFullNode12_655360 : MobiusReciprocalTree := .branch recipFullNode11_655360 recipFullNode11_720896
private theorem recipFullNode12_655360_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 12 655360 recipFullNode12_655360 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 655360 _ _ (by decide) recipFullNode11_655360_checked recipFullNode11_720896_checked (by decide +kernel)

private def recipFullNode13_524288 : MobiusReciprocalTree := .branch recipFullNode12_524288 recipFullNode12_655360
private theorem recipFullNode13_524288_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 13 524288 recipFullNode13_524288 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 12 524288 _ _ (by decide) recipFullNode12_524288_checked recipFullNode12_655360_checked (by decide +kernel)

private def recipFullNode10_786432 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block096 mobiusReciprocal1200001Block097) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block098 mobiusReciprocal1200001Block099)
private theorem recipFullNode10_786432_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 786432 recipFullNode10_786432 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 786432 _ _ (by decide) mobiusReciprocalSqrtPair048_checked mobiusReciprocalSqrtPair049_checked (by decide +kernel)

private def recipFullNode10_819200 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block100 mobiusReciprocal1200001Block101) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block102 mobiusReciprocal1200001Block103)
private theorem recipFullNode10_819200_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 819200 recipFullNode10_819200 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 819200 _ _ (by decide) mobiusReciprocalSqrtPair050_checked mobiusReciprocalSqrtPair051_checked (by decide +kernel)

private def recipFullNode11_786432 : MobiusReciprocalTree := .branch recipFullNode10_786432 recipFullNode10_819200
private theorem recipFullNode11_786432_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 786432 recipFullNode11_786432 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 786432 _ _ (by decide) recipFullNode10_786432_checked recipFullNode10_819200_checked (by decide +kernel)

private def recipFullNode10_851968 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block104 mobiusReciprocal1200001Block105) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block106 mobiusReciprocal1200001Block107)
private theorem recipFullNode10_851968_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 851968 recipFullNode10_851968 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 851968 _ _ (by decide) mobiusReciprocalSqrtPair052_checked mobiusReciprocalSqrtPair053_checked (by decide +kernel)

private def recipFullNode10_884736 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block108 mobiusReciprocal1200001Block109) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block110 mobiusReciprocal1200001Block111)
private theorem recipFullNode10_884736_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 884736 recipFullNode10_884736 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 884736 _ _ (by decide) mobiusReciprocalSqrtPair054_checked mobiusReciprocalSqrtPair055_checked (by decide +kernel)

private def recipFullNode11_851968 : MobiusReciprocalTree := .branch recipFullNode10_851968 recipFullNode10_884736
private theorem recipFullNode11_851968_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 851968 recipFullNode11_851968 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 851968 _ _ (by decide) recipFullNode10_851968_checked recipFullNode10_884736_checked (by decide +kernel)

private def recipFullNode12_786432 : MobiusReciprocalTree := .branch recipFullNode11_786432 recipFullNode11_851968
private theorem recipFullNode12_786432_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 12 786432 recipFullNode12_786432 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 786432 _ _ (by decide) recipFullNode11_786432_checked recipFullNode11_851968_checked (by decide +kernel)

private def recipFullNode10_917504 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block112 mobiusReciprocal1200001Block113) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block114 mobiusReciprocal1200001Block115)
private theorem recipFullNode10_917504_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 917504 recipFullNode10_917504 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 917504 _ _ (by decide) mobiusReciprocalSqrtPair056_checked mobiusReciprocalSqrtPair057_checked (by decide +kernel)

private def recipFullNode10_950272 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block116 mobiusReciprocal1200001Block117) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block118 mobiusReciprocal1200001Block119)
private theorem recipFullNode10_950272_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 950272 recipFullNode10_950272 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 950272 _ _ (by decide) mobiusReciprocalSqrtPair058_checked mobiusReciprocalSqrtPair059_checked (by decide +kernel)

private def recipFullNode11_917504 : MobiusReciprocalTree := .branch recipFullNode10_917504 recipFullNode10_950272
private theorem recipFullNode11_917504_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 917504 recipFullNode11_917504 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 917504 _ _ (by decide) recipFullNode10_917504_checked recipFullNode10_950272_checked (by decide +kernel)

private def recipFullNode10_983040 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block120 mobiusReciprocal1200001Block121) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block122 mobiusReciprocal1200001Block123)
private theorem recipFullNode10_983040_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 983040 recipFullNode10_983040 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 983040 _ _ (by decide) mobiusReciprocalSqrtPair060_checked mobiusReciprocalSqrtPair061_checked (by decide +kernel)

private def recipFullNode10_1015808 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block124 mobiusReciprocal1200001Block125) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block126 mobiusReciprocal1200001Block127)
private theorem recipFullNode10_1015808_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 1015808 recipFullNode10_1015808 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 1015808 _ _ (by decide) mobiusReciprocalSqrtPair062_checked mobiusReciprocalSqrtPair063_checked (by decide +kernel)

private def recipFullNode11_983040 : MobiusReciprocalTree := .branch recipFullNode10_983040 recipFullNode10_1015808
private theorem recipFullNode11_983040_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 983040 recipFullNode11_983040 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 983040 _ _ (by decide) recipFullNode10_983040_checked recipFullNode10_1015808_checked (by decide +kernel)

private def recipFullNode12_917504 : MobiusReciprocalTree := .branch recipFullNode11_917504 recipFullNode11_983040
private theorem recipFullNode12_917504_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 12 917504 recipFullNode12_917504 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 917504 _ _ (by decide) recipFullNode11_917504_checked recipFullNode11_983040_checked (by decide +kernel)

private def recipFullNode13_786432 : MobiusReciprocalTree := .branch recipFullNode12_786432 recipFullNode12_917504
private theorem recipFullNode13_786432_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 13 786432 recipFullNode13_786432 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 12 786432 _ _ (by decide) recipFullNode12_786432_checked recipFullNode12_917504_checked (by decide +kernel)

private def recipFullNode14_524288 : MobiusReciprocalTree := .branch recipFullNode13_524288 recipFullNode13_786432
private theorem recipFullNode14_524288_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 14 524288 recipFullNode14_524288 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 13 524288 _ _ (by decide) recipFullNode13_524288_checked recipFullNode13_786432_checked (by decide +kernel)

private def recipFullNode15_0 : MobiusReciprocalTree := .branch recipFullNode14_0 recipFullNode14_524288
private theorem recipFullNode15_0_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 15 0 recipFullNode15_0 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 14 0 _ _ (by decide) recipFullNode14_0_checked recipFullNode14_524288_checked (by decide +kernel)

private def recipFullNode10_1048576 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block128 mobiusReciprocal1200001Block129) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block130 mobiusReciprocal1200001Block131)
private theorem recipFullNode10_1048576_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 1048576 recipFullNode10_1048576 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 1048576 _ _ (by decide) mobiusReciprocalSqrtPair064_checked mobiusReciprocalSqrtPair065_checked (by decide +kernel)

private def recipFullNode10_1081344 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block132 mobiusReciprocal1200001Block133) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block134 mobiusReciprocal1200001Block135)
private theorem recipFullNode10_1081344_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 1081344 recipFullNode10_1081344 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 1081344 _ _ (by decide) mobiusReciprocalSqrtPair066_checked mobiusReciprocalSqrtPair067_checked (by decide +kernel)

private def recipFullNode11_1048576 : MobiusReciprocalTree := .branch recipFullNode10_1048576 recipFullNode10_1081344
private theorem recipFullNode11_1048576_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 1048576 recipFullNode11_1048576 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 1048576 _ _ (by decide) recipFullNode10_1048576_checked recipFullNode10_1081344_checked (by decide +kernel)

private def recipFullNode10_1114112 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block136 mobiusReciprocal1200001Block137) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block138 mobiusReciprocal1200001Block139)
private theorem recipFullNode10_1114112_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 1114112 recipFullNode10_1114112 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 1114112 _ _ (by decide) mobiusReciprocalSqrtPair068_checked mobiusReciprocalSqrtPair069_checked (by decide +kernel)

private def recipFullNode10_1146880 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block140 mobiusReciprocal1200001Block141) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block142 mobiusReciprocal1200001Block143)
private theorem recipFullNode10_1146880_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 1146880 recipFullNode10_1146880 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 1146880 _ _ (by decide) mobiusReciprocalSqrtPair070_checked mobiusReciprocalSqrtPair071_checked (by decide +kernel)

private def recipFullNode11_1114112 : MobiusReciprocalTree := .branch recipFullNode10_1114112 recipFullNode10_1146880
private theorem recipFullNode11_1114112_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 1114112 recipFullNode11_1114112 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 1114112 _ _ (by decide) recipFullNode10_1114112_checked recipFullNode10_1146880_checked (by decide +kernel)

private def recipFullNode12_1048576 : MobiusReciprocalTree := .branch recipFullNode11_1048576 recipFullNode11_1114112
private theorem recipFullNode12_1048576_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 12 1048576 recipFullNode12_1048576 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 1048576 _ _ (by decide) recipFullNode11_1048576_checked recipFullNode11_1114112_checked (by decide +kernel)

private def recipFullNode10_1179648 : MobiusReciprocalTree := .branch (MobiusReciprocalTree.branch mobiusReciprocal1200001Block144 mobiusReciprocal1200001Block145) (MobiusReciprocalTree.branch mobiusReciprocal1200001Block146 (MobiusReciprocalTree.leaf (-119400916) (-119400916) 0 0))
private theorem recipFullNode10_1179648_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 1179648 recipFullNode10_1179648 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 1179648 _ _ (by decide) mobiusReciprocalSqrtPair072_checked mobiusReciprocalSqrtPair073_checked (by decide +kernel)

private def recipFullNode10_1212416 : MobiusReciprocalTree := .leaf (-119400916) (-119400916) 0 0
private theorem recipFullNode10_1212416_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 1212416 recipFullNode10_1212416 = true := by decide +kernel

private def recipFullNode11_1179648 : MobiusReciprocalTree := .branch recipFullNode10_1179648 recipFullNode10_1212416
private theorem recipFullNode11_1179648_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 1179648 recipFullNode11_1179648 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 10 1179648 _ _ (by decide) recipFullNode10_1179648_checked recipFullNode10_1212416_checked (by decide +kernel)

private def recipFullNode11_1245184 : MobiusReciprocalTree := .leaf (-119400916) (-119400916) 0 0
private theorem recipFullNode11_1245184_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 1245184 recipFullNode11_1245184 = true := by decide +kernel

private def recipFullNode12_1179648 : MobiusReciprocalTree := .branch recipFullNode11_1179648 recipFullNode11_1245184
private theorem recipFullNode12_1179648_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 12 1179648 recipFullNode12_1179648 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 11 1179648 _ _ (by decide) recipFullNode11_1179648_checked recipFullNode11_1245184_checked (by decide +kernel)

private def recipFullNode13_1048576 : MobiusReciprocalTree := .branch recipFullNode12_1048576 recipFullNode12_1179648
private theorem recipFullNode13_1048576_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 13 1048576 recipFullNode13_1048576 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 12 1048576 _ _ (by decide) recipFullNode12_1048576_checked recipFullNode12_1179648_checked (by decide +kernel)

private def recipFullNode13_1310720 : MobiusReciprocalTree := .leaf (-119400916) (-119400916) 0 0
private theorem recipFullNode13_1310720_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 13 1310720 recipFullNode13_1310720 = true := by decide +kernel

private def recipFullNode14_1048576 : MobiusReciprocalTree := .branch recipFullNode13_1048576 recipFullNode13_1310720
private theorem recipFullNode14_1048576_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 14 1048576 recipFullNode14_1048576 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 13 1048576 _ _ (by decide) recipFullNode13_1048576_checked recipFullNode13_1310720_checked (by decide +kernel)

private def recipFullNode14_1572864 : MobiusReciprocalTree := .leaf (-119400916) (-119400916) 0 0
private theorem recipFullNode14_1572864_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 14 1572864 recipFullNode14_1572864 = true := by decide +kernel

private def recipFullNode15_1048576 : MobiusReciprocalTree := .branch recipFullNode14_1048576 recipFullNode14_1572864
private theorem recipFullNode15_1048576_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 15 1048576 recipFullNode15_1048576 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 14 1048576 _ _ (by decide) recipFullNode14_1048576_checked recipFullNode14_1572864_checked (by decide +kernel)

private def recipFullNode16_0 : MobiusReciprocalTree := .branch recipFullNode15_0 recipFullNode15_1048576
private theorem recipFullNode16_0_checked : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 16 0 recipFullNode16_0 = true :=
  closedSqrtRootJoin (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 15 0 _ _ (by decide) recipFullNode15_0_checked recipFullNode15_1048576_checked (by decide +kernel)

theorem mobiusReciprocalSqrt1200001_checked_complete : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 16 0 mobiusReciprocal1200001 = true := recipFullNode16_0_checked

end Helfgott
open Helfgott
theorem solution : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 16 0 mobiusReciprocal1200001 = true := Helfgott.mobiusReciprocalSqrt1200001_checked_complete
#print axioms solution
