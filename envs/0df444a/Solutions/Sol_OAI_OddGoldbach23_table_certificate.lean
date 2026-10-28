-- Prove2me | solution 1 for OAI.OddGoldbach23.table_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-25T07:40:26.924145+00:00
-- url     : https://prove2.me/submissions/8dc0dacd-b4e9-4a76-90f1-18c613b8beee

import Definitions.Def_OAI_OddGoldbach23_CertificateData
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.List.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
open Finset Real
set_option Elab.async false
set_option maxHeartbeats 20000000
set_option maxRecDepth 10000
namespace OAI.OddGoldbach23.Cert
theorem table0 : ∀ j : Fin 100, WC (j.val+0) ≤ WP (j.val+0) := by decide +kernel
theorem table1 : ∀ j : Fin 100, WC (j.val+100) ≤ WP (j.val+100) := by decide +kernel
theorem table2 : ∀ j : Fin 100, WC (j.val+200) ≤ WP (j.val+200) := by decide +kernel
theorem table3 : ∀ j : Fin 100, WC (j.val+300) ≤ WP (j.val+300) := by decide +kernel
theorem table4 : ∀ j : Fin 100, WC (j.val+400) ≤ WP (j.val+400) := by decide +kernel
theorem table5 : ∀ j : Fin 100, WC (j.val+500) ≤ WP (j.val+500) := by decide +kernel
theorem table6 : ∀ j : Fin 100, WC (j.val+600) ≤ WP (j.val+600) := by decide +kernel
theorem table7 : ∀ j : Fin 100, WC (j.val+700) ≤ WP (j.val+700) := by decide +kernel
theorem table8 : ∀ j : Fin 100, WC (j.val+800) ≤ WP (j.val+800) := by decide +kernel
theorem table9 : ∀ j : Fin 100, WC (j.val+900) ≤ WP (j.val+900) := by decide +kernel
theorem table10 : ∀ j : Fin 100, WC (j.val+1000) ≤ WP (j.val+1000) := by decide +kernel
theorem table11 : ∀ j : Fin 100, WC (j.val+1100) ≤ WP (j.val+1100) := by decide +kernel
theorem table12 : ∀ j : Fin 100, WC (j.val+1200) ≤ WP (j.val+1200) := by decide +kernel
theorem table13 : ∀ j : Fin 100, WC (j.val+1300) ≤ WP (j.val+1300) := by decide +kernel
theorem table14 : ∀ j : Fin 100, WC (j.val+1400) ≤ WP (j.val+1400) := by decide +kernel
theorem table15 : ∀ j : Fin 100, WC (j.val+1500) ≤ WP (j.val+1500) := by decide +kernel
theorem table16 : ∀ j : Fin 100, WC (j.val+1600) ≤ WP (j.val+1600) := by decide +kernel
theorem table17 : ∀ j : Fin 100, WC (j.val+1700) ≤ WP (j.val+1700) := by decide +kernel
theorem table18 : ∀ j : Fin 100, WC (j.val+1800) ≤ WP (j.val+1800) := by decide +kernel
theorem table19 : ∀ j : Fin 100, WC (j.val+1900) ≤ WP (j.val+1900) := by decide +kernel
theorem table20 : ∀ j : Fin 100, WC (j.val+2000) ≤ WP (j.val+2000) := by decide +kernel
theorem table21 : ∀ j : Fin 100, WC (j.val+2100) ≤ WP (j.val+2100) := by decide +kernel
theorem table22 : ∀ j : Fin 100, WC (j.val+2200) ≤ WP (j.val+2200) := by decide +kernel
theorem table23 : ∀ j : Fin 100, WC (j.val+2300) ≤ WP (j.val+2300) := by decide +kernel
theorem table24 : ∀ j : Fin 100, WC (j.val+2400) ≤ WP (j.val+2400) := by decide +kernel
theorem table25 : ∀ j : Fin 100, WC (j.val+2500) ≤ WP (j.val+2500) := by decide +kernel
theorem table26 : ∀ j : Fin 100, WC (j.val+2600) ≤ WP (j.val+2600) := by decide +kernel
theorem table27 : ∀ j : Fin 100, WC (j.val+2700) ≤ WP (j.val+2700) := by decide +kernel
theorem table28 : ∀ j : Fin 100, WC (j.val+2800) ≤ WP (j.val+2800) := by decide +kernel
theorem table29 : ∀ j : Fin 100, WC (j.val+2900) ≤ WP (j.val+2900) := by decide +kernel
theorem table30 : ∀ j : Fin 100, WC (j.val+3000) ≤ WP (j.val+3000) := by decide +kernel
theorem table31 : ∀ j : Fin 100, WC (j.val+3100) ≤ WP (j.val+3100) := by decide +kernel
theorem table32 : ∀ j : Fin 100, WC (j.val+3200) ≤ WP (j.val+3200) := by decide +kernel
theorem table33 : ∀ j : Fin 100, WC (j.val+3300) ≤ WP (j.val+3300) := by decide +kernel
theorem table34 : ∀ j : Fin 100, WC (j.val+3400) ≤ WP (j.val+3400) := by decide +kernel
theorem table35 : ∀ j : Fin 100, WC (j.val+3500) ≤ WP (j.val+3500) := by decide +kernel
theorem table36 : ∀ j : Fin 100, WC (j.val+3600) ≤ WP (j.val+3600) := by decide +kernel
theorem table37 : ∀ j : Fin 100, WC (j.val+3700) ≤ WP (j.val+3700) := by decide +kernel
theorem table38 : ∀ j : Fin 100, WC (j.val+3800) ≤ WP (j.val+3800) := by decide +kernel
theorem table39 : ∀ j : Fin 100, WC (j.val+3900) ≤ WP (j.val+3900) := by decide +kernel
theorem table40 : ∀ j : Fin 100, WC (j.val+4000) ≤ WP (j.val+4000) := by decide +kernel
theorem table41 : ∀ j : Fin 100, WC (j.val+4100) ≤ WP (j.val+4100) := by decide +kernel
theorem table42 : ∀ j : Fin 100, WC (j.val+4200) ≤ WP (j.val+4200) := by decide +kernel
theorem table43 : ∀ j : Fin 100, WC (j.val+4300) ≤ WP (j.val+4300) := by decide +kernel
theorem table44 : ∀ j : Fin 100, WC (j.val+4400) ≤ WP (j.val+4400) := by decide +kernel
theorem table45 : ∀ j : Fin 100, WC (j.val+4500) ≤ WP (j.val+4500) := by decide +kernel
theorem table46 : ∀ j : Fin 100, WC (j.val+4600) ≤ WP (j.val+4600) := by decide +kernel
theorem table47 : ∀ j : Fin 100, WC (j.val+4700) ≤ WP (j.val+4700) := by decide +kernel
theorem table48 : ∀ j : Fin 100, WC (j.val+4800) ≤ WP (j.val+4800) := by decide +kernel
theorem table49 : ∀ j : Fin 100, WC (j.val+4900) ≤ WP (j.val+4900) := by decide +kernel
theorem table50 : ∀ j : Fin 100, WC (j.val+5000) ≤ WP (j.val+5000) := by decide +kernel
theorem table51 : ∀ j : Fin 100, WC (j.val+5100) ≤ WP (j.val+5100) := by decide +kernel
theorem table52 : ∀ j : Fin 100, WC (j.val+5200) ≤ WP (j.val+5200) := by decide +kernel
theorem table53 : ∀ j : Fin 100, WC (j.val+5300) ≤ WP (j.val+5300) := by decide +kernel
theorem table54 : ∀ j : Fin 100, WC (j.val+5400) ≤ WP (j.val+5400) := by decide +kernel
theorem table55 : ∀ j : Fin 100, WC (j.val+5500) ≤ WP (j.val+5500) := by decide +kernel
theorem table56 : ∀ j : Fin 100, WC (j.val+5600) ≤ WP (j.val+5600) := by decide +kernel
theorem table57 : ∀ j : Fin 100, WC (j.val+5700) ≤ WP (j.val+5700) := by decide +kernel
theorem table58 : ∀ j : Fin 100, WC (j.val+5800) ≤ WP (j.val+5800) := by decide +kernel
theorem table59 : ∀ j : Fin 100, WC (j.val+5900) ≤ WP (j.val+5900) := by decide +kernel
theorem table60 : ∀ j : Fin 100, WC (j.val+6000) ≤ WP (j.val+6000) := by decide +kernel
theorem table61 : ∀ j : Fin 100, WC (j.val+6100) ≤ WP (j.val+6100) := by decide +kernel
theorem table62 : ∀ j : Fin 100, WC (j.val+6200) ≤ WP (j.val+6200) := by decide +kernel
theorem table63 : ∀ j : Fin 100, WC (j.val+6300) ≤ WP (j.val+6300) := by decide +kernel
theorem table64 : ∀ j : Fin 100, WC (j.val+6400) ≤ WP (j.val+6400) := by decide +kernel
theorem table65 : ∀ j : Fin 100, WC (j.val+6500) ≤ WP (j.val+6500) := by decide +kernel
theorem table66 : ∀ j : Fin 100, WC (j.val+6600) ≤ WP (j.val+6600) := by decide +kernel
theorem table67 : ∀ j : Fin 100, WC (j.val+6700) ≤ WP (j.val+6700) := by decide +kernel
theorem table68 : ∀ j : Fin 100, WC (j.val+6800) ≤ WP (j.val+6800) := by decide +kernel
theorem table69 : ∀ j : Fin 100, WC (j.val+6900) ≤ WP (j.val+6900) := by decide +kernel
theorem table70 : ∀ j : Fin 100, WC (j.val+7000) ≤ WP (j.val+7000) := by decide +kernel
theorem table71 : ∀ j : Fin 100, WC (j.val+7100) ≤ WP (j.val+7100) := by decide +kernel
theorem table72 : ∀ j : Fin 100, WC (j.val+7200) ≤ WP (j.val+7200) := by decide +kernel
theorem table73 : ∀ j : Fin 100, WC (j.val+7300) ≤ WP (j.val+7300) := by decide +kernel
theorem table74 : ∀ j : Fin 100, WC (j.val+7400) ≤ WP (j.val+7400) := by decide +kernel
theorem table75 : ∀ j : Fin 100, WC (j.val+7500) ≤ WP (j.val+7500) := by decide +kernel
theorem table76 : ∀ j : Fin 100, WC (j.val+7600) ≤ WP (j.val+7600) := by decide +kernel
theorem table77 : ∀ j : Fin 100, WC (j.val+7700) ≤ WP (j.val+7700) := by decide +kernel
theorem table78 : ∀ j : Fin 100, WC (j.val+7800) ≤ WP (j.val+7800) := by decide +kernel
theorem table79 : ∀ j : Fin 28, WC (j.val+7900) ≤ WP (j.val+7900) := by decide +kernel
theorem table_bound (d : ℕ) (hd : d < 7928) : WC d ≤ WP d := by
  rcases lt_or_ge d 100 with hb0 | ha0
  · simpa only [Nat.sub_add_cancel (by omega : 0 ≤ d)] using table0 ⟨d-0, by omega⟩
  rcases lt_or_ge d 200 with hb1 | ha1
  · simpa only [Nat.sub_add_cancel (by omega : 100 ≤ d)] using table1 ⟨d-100, by omega⟩
  rcases lt_or_ge d 300 with hb2 | ha2
  · simpa only [Nat.sub_add_cancel (by omega : 200 ≤ d)] using table2 ⟨d-200, by omega⟩
  rcases lt_or_ge d 400 with hb3 | ha3
  · simpa only [Nat.sub_add_cancel (by omega : 300 ≤ d)] using table3 ⟨d-300, by omega⟩
  rcases lt_or_ge d 500 with hb4 | ha4
  · simpa only [Nat.sub_add_cancel (by omega : 400 ≤ d)] using table4 ⟨d-400, by omega⟩
  rcases lt_or_ge d 600 with hb5 | ha5
  · simpa only [Nat.sub_add_cancel (by omega : 500 ≤ d)] using table5 ⟨d-500, by omega⟩
  rcases lt_or_ge d 700 with hb6 | ha6
  · simpa only [Nat.sub_add_cancel (by omega : 600 ≤ d)] using table6 ⟨d-600, by omega⟩
  rcases lt_or_ge d 800 with hb7 | ha7
  · simpa only [Nat.sub_add_cancel (by omega : 700 ≤ d)] using table7 ⟨d-700, by omega⟩
  rcases lt_or_ge d 900 with hb8 | ha8
  · simpa only [Nat.sub_add_cancel (by omega : 800 ≤ d)] using table8 ⟨d-800, by omega⟩
  rcases lt_or_ge d 1000 with hb9 | ha9
  · simpa only [Nat.sub_add_cancel (by omega : 900 ≤ d)] using table9 ⟨d-900, by omega⟩
  rcases lt_or_ge d 1100 with hb10 | ha10
  · simpa only [Nat.sub_add_cancel (by omega : 1000 ≤ d)] using table10 ⟨d-1000, by omega⟩
  rcases lt_or_ge d 1200 with hb11 | ha11
  · simpa only [Nat.sub_add_cancel (by omega : 1100 ≤ d)] using table11 ⟨d-1100, by omega⟩
  rcases lt_or_ge d 1300 with hb12 | ha12
  · simpa only [Nat.sub_add_cancel (by omega : 1200 ≤ d)] using table12 ⟨d-1200, by omega⟩
  rcases lt_or_ge d 1400 with hb13 | ha13
  · simpa only [Nat.sub_add_cancel (by omega : 1300 ≤ d)] using table13 ⟨d-1300, by omega⟩
  rcases lt_or_ge d 1500 with hb14 | ha14
  · simpa only [Nat.sub_add_cancel (by omega : 1400 ≤ d)] using table14 ⟨d-1400, by omega⟩
  rcases lt_or_ge d 1600 with hb15 | ha15
  · simpa only [Nat.sub_add_cancel (by omega : 1500 ≤ d)] using table15 ⟨d-1500, by omega⟩
  rcases lt_or_ge d 1700 with hb16 | ha16
  · simpa only [Nat.sub_add_cancel (by omega : 1600 ≤ d)] using table16 ⟨d-1600, by omega⟩
  rcases lt_or_ge d 1800 with hb17 | ha17
  · simpa only [Nat.sub_add_cancel (by omega : 1700 ≤ d)] using table17 ⟨d-1700, by omega⟩
  rcases lt_or_ge d 1900 with hb18 | ha18
  · simpa only [Nat.sub_add_cancel (by omega : 1800 ≤ d)] using table18 ⟨d-1800, by omega⟩
  rcases lt_or_ge d 2000 with hb19 | ha19
  · simpa only [Nat.sub_add_cancel (by omega : 1900 ≤ d)] using table19 ⟨d-1900, by omega⟩
  rcases lt_or_ge d 2100 with hb20 | ha20
  · simpa only [Nat.sub_add_cancel (by omega : 2000 ≤ d)] using table20 ⟨d-2000, by omega⟩
  rcases lt_or_ge d 2200 with hb21 | ha21
  · simpa only [Nat.sub_add_cancel (by omega : 2100 ≤ d)] using table21 ⟨d-2100, by omega⟩
  rcases lt_or_ge d 2300 with hb22 | ha22
  · simpa only [Nat.sub_add_cancel (by omega : 2200 ≤ d)] using table22 ⟨d-2200, by omega⟩
  rcases lt_or_ge d 2400 with hb23 | ha23
  · simpa only [Nat.sub_add_cancel (by omega : 2300 ≤ d)] using table23 ⟨d-2300, by omega⟩
  rcases lt_or_ge d 2500 with hb24 | ha24
  · simpa only [Nat.sub_add_cancel (by omega : 2400 ≤ d)] using table24 ⟨d-2400, by omega⟩
  rcases lt_or_ge d 2600 with hb25 | ha25
  · simpa only [Nat.sub_add_cancel (by omega : 2500 ≤ d)] using table25 ⟨d-2500, by omega⟩
  rcases lt_or_ge d 2700 with hb26 | ha26
  · simpa only [Nat.sub_add_cancel (by omega : 2600 ≤ d)] using table26 ⟨d-2600, by omega⟩
  rcases lt_or_ge d 2800 with hb27 | ha27
  · simpa only [Nat.sub_add_cancel (by omega : 2700 ≤ d)] using table27 ⟨d-2700, by omega⟩
  rcases lt_or_ge d 2900 with hb28 | ha28
  · simpa only [Nat.sub_add_cancel (by omega : 2800 ≤ d)] using table28 ⟨d-2800, by omega⟩
  rcases lt_or_ge d 3000 with hb29 | ha29
  · simpa only [Nat.sub_add_cancel (by omega : 2900 ≤ d)] using table29 ⟨d-2900, by omega⟩
  rcases lt_or_ge d 3100 with hb30 | ha30
  · simpa only [Nat.sub_add_cancel (by omega : 3000 ≤ d)] using table30 ⟨d-3000, by omega⟩
  rcases lt_or_ge d 3200 with hb31 | ha31
  · simpa only [Nat.sub_add_cancel (by omega : 3100 ≤ d)] using table31 ⟨d-3100, by omega⟩
  rcases lt_or_ge d 3300 with hb32 | ha32
  · simpa only [Nat.sub_add_cancel (by omega : 3200 ≤ d)] using table32 ⟨d-3200, by omega⟩
  rcases lt_or_ge d 3400 with hb33 | ha33
  · simpa only [Nat.sub_add_cancel (by omega : 3300 ≤ d)] using table33 ⟨d-3300, by omega⟩
  rcases lt_or_ge d 3500 with hb34 | ha34
  · simpa only [Nat.sub_add_cancel (by omega : 3400 ≤ d)] using table34 ⟨d-3400, by omega⟩
  rcases lt_or_ge d 3600 with hb35 | ha35
  · simpa only [Nat.sub_add_cancel (by omega : 3500 ≤ d)] using table35 ⟨d-3500, by omega⟩
  rcases lt_or_ge d 3700 with hb36 | ha36
  · simpa only [Nat.sub_add_cancel (by omega : 3600 ≤ d)] using table36 ⟨d-3600, by omega⟩
  rcases lt_or_ge d 3800 with hb37 | ha37
  · simpa only [Nat.sub_add_cancel (by omega : 3700 ≤ d)] using table37 ⟨d-3700, by omega⟩
  rcases lt_or_ge d 3900 with hb38 | ha38
  · simpa only [Nat.sub_add_cancel (by omega : 3800 ≤ d)] using table38 ⟨d-3800, by omega⟩
  rcases lt_or_ge d 4000 with hb39 | ha39
  · simpa only [Nat.sub_add_cancel (by omega : 3900 ≤ d)] using table39 ⟨d-3900, by omega⟩
  rcases lt_or_ge d 4100 with hb40 | ha40
  · simpa only [Nat.sub_add_cancel (by omega : 4000 ≤ d)] using table40 ⟨d-4000, by omega⟩
  rcases lt_or_ge d 4200 with hb41 | ha41
  · simpa only [Nat.sub_add_cancel (by omega : 4100 ≤ d)] using table41 ⟨d-4100, by omega⟩
  rcases lt_or_ge d 4300 with hb42 | ha42
  · simpa only [Nat.sub_add_cancel (by omega : 4200 ≤ d)] using table42 ⟨d-4200, by omega⟩
  rcases lt_or_ge d 4400 with hb43 | ha43
  · simpa only [Nat.sub_add_cancel (by omega : 4300 ≤ d)] using table43 ⟨d-4300, by omega⟩
  rcases lt_or_ge d 4500 with hb44 | ha44
  · simpa only [Nat.sub_add_cancel (by omega : 4400 ≤ d)] using table44 ⟨d-4400, by omega⟩
  rcases lt_or_ge d 4600 with hb45 | ha45
  · simpa only [Nat.sub_add_cancel (by omega : 4500 ≤ d)] using table45 ⟨d-4500, by omega⟩
  rcases lt_or_ge d 4700 with hb46 | ha46
  · simpa only [Nat.sub_add_cancel (by omega : 4600 ≤ d)] using table46 ⟨d-4600, by omega⟩
  rcases lt_or_ge d 4800 with hb47 | ha47
  · simpa only [Nat.sub_add_cancel (by omega : 4700 ≤ d)] using table47 ⟨d-4700, by omega⟩
  rcases lt_or_ge d 4900 with hb48 | ha48
  · simpa only [Nat.sub_add_cancel (by omega : 4800 ≤ d)] using table48 ⟨d-4800, by omega⟩
  rcases lt_or_ge d 5000 with hb49 | ha49
  · simpa only [Nat.sub_add_cancel (by omega : 4900 ≤ d)] using table49 ⟨d-4900, by omega⟩
  rcases lt_or_ge d 5100 with hb50 | ha50
  · simpa only [Nat.sub_add_cancel (by omega : 5000 ≤ d)] using table50 ⟨d-5000, by omega⟩
  rcases lt_or_ge d 5200 with hb51 | ha51
  · simpa only [Nat.sub_add_cancel (by omega : 5100 ≤ d)] using table51 ⟨d-5100, by omega⟩
  rcases lt_or_ge d 5300 with hb52 | ha52
  · simpa only [Nat.sub_add_cancel (by omega : 5200 ≤ d)] using table52 ⟨d-5200, by omega⟩
  rcases lt_or_ge d 5400 with hb53 | ha53
  · simpa only [Nat.sub_add_cancel (by omega : 5300 ≤ d)] using table53 ⟨d-5300, by omega⟩
  rcases lt_or_ge d 5500 with hb54 | ha54
  · simpa only [Nat.sub_add_cancel (by omega : 5400 ≤ d)] using table54 ⟨d-5400, by omega⟩
  rcases lt_or_ge d 5600 with hb55 | ha55
  · simpa only [Nat.sub_add_cancel (by omega : 5500 ≤ d)] using table55 ⟨d-5500, by omega⟩
  rcases lt_or_ge d 5700 with hb56 | ha56
  · simpa only [Nat.sub_add_cancel (by omega : 5600 ≤ d)] using table56 ⟨d-5600, by omega⟩
  rcases lt_or_ge d 5800 with hb57 | ha57
  · simpa only [Nat.sub_add_cancel (by omega : 5700 ≤ d)] using table57 ⟨d-5700, by omega⟩
  rcases lt_or_ge d 5900 with hb58 | ha58
  · simpa only [Nat.sub_add_cancel (by omega : 5800 ≤ d)] using table58 ⟨d-5800, by omega⟩
  rcases lt_or_ge d 6000 with hb59 | ha59
  · simpa only [Nat.sub_add_cancel (by omega : 5900 ≤ d)] using table59 ⟨d-5900, by omega⟩
  rcases lt_or_ge d 6100 with hb60 | ha60
  · simpa only [Nat.sub_add_cancel (by omega : 6000 ≤ d)] using table60 ⟨d-6000, by omega⟩
  rcases lt_or_ge d 6200 with hb61 | ha61
  · simpa only [Nat.sub_add_cancel (by omega : 6100 ≤ d)] using table61 ⟨d-6100, by omega⟩
  rcases lt_or_ge d 6300 with hb62 | ha62
  · simpa only [Nat.sub_add_cancel (by omega : 6200 ≤ d)] using table62 ⟨d-6200, by omega⟩
  rcases lt_or_ge d 6400 with hb63 | ha63
  · simpa only [Nat.sub_add_cancel (by omega : 6300 ≤ d)] using table63 ⟨d-6300, by omega⟩
  rcases lt_or_ge d 6500 with hb64 | ha64
  · simpa only [Nat.sub_add_cancel (by omega : 6400 ≤ d)] using table64 ⟨d-6400, by omega⟩
  rcases lt_or_ge d 6600 with hb65 | ha65
  · simpa only [Nat.sub_add_cancel (by omega : 6500 ≤ d)] using table65 ⟨d-6500, by omega⟩
  rcases lt_or_ge d 6700 with hb66 | ha66
  · simpa only [Nat.sub_add_cancel (by omega : 6600 ≤ d)] using table66 ⟨d-6600, by omega⟩
  rcases lt_or_ge d 6800 with hb67 | ha67
  · simpa only [Nat.sub_add_cancel (by omega : 6700 ≤ d)] using table67 ⟨d-6700, by omega⟩
  rcases lt_or_ge d 6900 with hb68 | ha68
  · simpa only [Nat.sub_add_cancel (by omega : 6800 ≤ d)] using table68 ⟨d-6800, by omega⟩
  rcases lt_or_ge d 7000 with hb69 | ha69
  · simpa only [Nat.sub_add_cancel (by omega : 6900 ≤ d)] using table69 ⟨d-6900, by omega⟩
  rcases lt_or_ge d 7100 with hb70 | ha70
  · simpa only [Nat.sub_add_cancel (by omega : 7000 ≤ d)] using table70 ⟨d-7000, by omega⟩
  rcases lt_or_ge d 7200 with hb71 | ha71
  · simpa only [Nat.sub_add_cancel (by omega : 7100 ≤ d)] using table71 ⟨d-7100, by omega⟩
  rcases lt_or_ge d 7300 with hb72 | ha72
  · simpa only [Nat.sub_add_cancel (by omega : 7200 ≤ d)] using table72 ⟨d-7200, by omega⟩
  rcases lt_or_ge d 7400 with hb73 | ha73
  · simpa only [Nat.sub_add_cancel (by omega : 7300 ≤ d)] using table73 ⟨d-7300, by omega⟩
  rcases lt_or_ge d 7500 with hb74 | ha74
  · simpa only [Nat.sub_add_cancel (by omega : 7400 ≤ d)] using table74 ⟨d-7400, by omega⟩
  rcases lt_or_ge d 7600 with hb75 | ha75
  · simpa only [Nat.sub_add_cancel (by omega : 7500 ≤ d)] using table75 ⟨d-7500, by omega⟩
  rcases lt_or_ge d 7700 with hb76 | ha76
  · simpa only [Nat.sub_add_cancel (by omega : 7600 ≤ d)] using table76 ⟨d-7600, by omega⟩
  rcases lt_or_ge d 7800 with hb77 | ha77
  · simpa only [Nat.sub_add_cancel (by omega : 7700 ≤ d)] using table77 ⟨d-7700, by omega⟩
  rcases lt_or_ge d 7900 with hb78 | ha78
  · simpa only [Nat.sub_add_cancel (by omega : 7800 ≤ d)] using table78 ⟨d-7800, by omega⟩
  simpa only [Nat.sub_add_cancel (by omega : 7900 ≤ d)] using table79 ⟨d-7900, by omega⟩
end OAI.OddGoldbach23.Cert
theorem solution (d : ℕ) (hd : d < 7928) : OAI.OddGoldbach23.Cert.WC d ≤ OAI.OddGoldbach23.Cert.WP d :=
  OAI.OddGoldbach23.Cert.table_bound d hd
#print axioms solution
