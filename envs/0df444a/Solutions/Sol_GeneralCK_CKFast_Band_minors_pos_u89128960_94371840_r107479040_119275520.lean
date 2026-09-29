-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u89128960_94371840_r107479040_119275520
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T05:12:12.257087+00:00
-- url     : https://prove2.me/submissions/f1ca61bd-8dc5-40aa-a0ee-ea39f053c65a

import Theorems.Thm_GeneralCK_CKFast_tree_sound
open GeneralCK.CKFast

/-! Cover of `u ∈ [17/160, 9/80]`, `ρ ∈ [41/320, 91/640]` by 23 cells of the computing
correction-band checker; each cell is kernel-checked in its own declaration. -/

theorem leaf_ok {U0 U1 R0 R1 : ℤ} {h : Hint} (hc : cellOK U0 U1 R0 R1 h = true) :
    treeOK U0 U1 R0 R1 (.leaf h) = true := by
  simpa only [treeOK] using hc

theorem join_su {U0 U1 R0 R1 m : ℤ} {l r : Tree} (hm : (decide (U0 ≤ m) && decide (m ≤ U1)) = true)
    (hl : treeOK U0 m R0 R1 l = true) (hr : treeOK m U1 R0 R1 r = true) :
    treeOK U0 U1 R0 R1 (.su m l r) = true := by
  simp only [treeOK, Bool.and_eq_true] at hm ⊢
  exact ⟨⟨hm, hl⟩, hr⟩

theorem join_sr {U0 U1 R0 R1 m : ℤ} {l r : Tree} (hm : (decide (R0 ≤ m) && decide (m ≤ R1)) = true)
    (hl : treeOK U0 U1 R0 m l = true) (hr : treeOK U0 U1 m R1 r = true) :
    treeOK U0 U1 R0 R1 (.sr m l r) = true := by
  simp only [treeOK, Bool.and_eq_true] at hm ⊢
  exact ⟨⟨hm, hl⟩, hr⟩

set_option maxRecDepth 100000 in
theorem cell0 : cellOK 89128960 89784320 107479040 110428160 ⟨⟨99843483923, 99843483932⟩, ⟨96132642087, 103607633322⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell1 : cellOK 89784320 90439680 107479040 110428160 ⟨⟨99293876144, 99293876146⟩, ⟨95604028441, 103036502061⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell2 : cellOK 89128960 90439680 110428160 113377280 ⟨⟨101931486340, 101931486351⟩, ⟨96211552964, 107778419696⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell3 : cellOK 90439680 91095040 107479040 110428160 ⟨⟨98749323686, 98749323694⟩, ⟨95080224960, 102470679561⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell4 : cellOK 91095040 91750400 107479040 110428160 ⟨⟨98209748067, 98209748075⟩, ⟨94561157503, 101910082799⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell5 : cellOK 90439680 91095040 110428160 113377280 ⟨⟨101097597737, 101097597748⟩, ⟨97421267343, 104825885421⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell6 : cellOK 91095040 91750400 110428160 113377280 ⟨⟨100547978889, 100547978898⟩, ⟨96892138610, 104255270045⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell7 : cellOK 89128960 90439680 113377280 116326400 ⟨⟨104280836354, 104280836363⟩, ⟨98548108659, 110139919519⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell8 : cellOK 89128960 90439680 116326400 119275520 ⟨⟨106616300996, 106616301007⟩, ⟨100871025144, 112487289475⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell9 : cellOK 90439680 91750400 113377280 116326400 ⟨⟨103151666452, 103151666463⟩, ⟨97479286631, 108948068615⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell10 : cellOK 90439680 91750400 116326400 119275520 ⟨⟨105467625578, 105467625589⟩, ⟨99782648301, 111276011333⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell11 : cellOK 91750400 92405760 107479040 110428160 ⟨⟨97675072439, 97675072448⟩, ⟨94046753479, 101354630512⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell12 : cellOK 92405760 93061120 107479040 110428160 ⟨⟨97145221569, 97145221577⟩, ⟨93536941803, 100804243146⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell13 : cellOK 91750400 92405760 110428160 113377280 ⟨⟨100003315220, 100003315229⟩, ⟨96367729851, 103689852819⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell14 : cellOK 92405760 93061120 110428160 113377280 ⟨⟨99463531112, 99463531123⟩, ⟨95847969557, 103129553856⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell15 : cellOK 93061120 93716480 107479040 110428160 ⟨⟨96620121781, 96620121783⟩, ⟨93031652854, 100258842811⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell16 : cellOK 93716480 94371840 107479040 110428160 ⟨⟨96099700914, 96099700923⟩, ⟨92530818442, 99718353233⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell17 : cellOK 93061120 93716480 110428160 113377280 ⟨⟨98928552513, 98928552519⟩, ⟨95332787680, 102574294935⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell18 : cellOK 93716480 94371840 110428160 113377280 ⟨⟨98398306880, 98398306889⟩, ⟨94822115603, 102023999448⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell19 : cellOK 91750400 93061120 113377280 116326400 ⟨⟨102042684112, 102042684121⟩, ⟨96429258494, 107777869406⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell20 : cellOK 91750400 93061120 116326400 119275520 ⟨⟨104339339731, 104339339742⟩, ⟨98713275186, 110086577695⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell21 : cellOK 93061120 94371840 113377280 116326400 ⟨⟨100953281566, 100953281575⟩, ⟨95397464556, 106628663178⟩⟩ = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cell22 : cellOK 93061120 94371840 116326400 119275520 ⟨⟨103230833306, 103230833317⟩, ⟨97662343211, 108918328053⟩⟩ = true := by
  decide +kernel

theorem chunk_ok : ∃ t : Tree, treeOK 89128960 94371840 107479040 119275520 t = true :=
  ⟨_, (join_su (m := 91750400) (by decide) (join_sr (m := 113377280) (by decide) (join_su (m := 90439680) (by decide) (join_sr (m := 110428160) (by decide) (join_su (m := 89784320) (by decide) (leaf_ok cell0) (leaf_ok cell1)) (leaf_ok cell2)) (join_sr (m := 110428160) (by decide) (join_su (m := 91095040) (by decide) (leaf_ok cell3) (leaf_ok cell4)) (join_su (m := 91095040) (by decide) (leaf_ok cell5) (leaf_ok cell6)))) (join_su (m := 90439680) (by decide) (join_sr (m := 116326400) (by decide) (leaf_ok cell7) (leaf_ok cell8)) (join_sr (m := 116326400) (by decide) (leaf_ok cell9) (leaf_ok cell10)))) (join_sr (m := 113377280) (by decide) (join_su (m := 93061120) (by decide) (join_sr (m := 110428160) (by decide) (join_su (m := 92405760) (by decide) (leaf_ok cell11) (leaf_ok cell12)) (join_su (m := 92405760) (by decide) (leaf_ok cell13) (leaf_ok cell14))) (join_sr (m := 110428160) (by decide) (join_su (m := 93716480) (by decide) (leaf_ok cell15) (leaf_ok cell16)) (join_su (m := 93716480) (by decide) (leaf_ok cell17) (leaf_ok cell18)))) (join_su (m := 93061120) (by decide) (join_sr (m := 116326400) (by decide) (leaf_ok cell19) (leaf_ok cell20)) (join_sr (m := 116326400) (by decide) (leaf_ok cell21) (leaf_ok cell22)))))⟩

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (17/160 : ℝ) (9/80 : ℝ) →
    rho ∈ Set.Icc (41/320 : ℝ) (91/640 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  have e0 : (((89128960 : ℤ) : ℝ) / (D : ℝ)) = (17/160 : ℝ) := by norm_num [D]
  have e1 : (((94371840 : ℤ) : ℝ) / (D : ℝ)) = (9/80 : ℝ) := by norm_num [D]
  have e2 : (((107479040 : ℤ) : ℝ) / (D : ℝ)) = (41/320 : ℝ) := by norm_num [D]
  have e3 : (((119275520 : ℤ) : ℝ) / (D : ℝ)) = (91/640 : ℝ) := by norm_num [D]
  obtain ⟨t, ht⟩ := chunk_ok
  exact tree_sound ht u rho (by rw [e0, e1]; exact hu) (by rw [e2, e3]; exact hr) hr1
