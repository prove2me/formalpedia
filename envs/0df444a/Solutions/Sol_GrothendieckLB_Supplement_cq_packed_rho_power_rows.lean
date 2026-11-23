-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_packed_rho_power_rows
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T19:44:31.106344+00:00
-- url     : https://prove2.me/submissions/3b1478d2-c0f8-437a-a0b9-af01cb69ccd1

import Theorems.Thm_GrothendieckLB_Supplement_cq_primary_power_rows_1_to_48
import Theorems.Thm_GrothendieckLB_Supplement_cq_primary_power_rows_49_to_96
import Theorems.Thm_GrothendieckLB_Supplement_cq_primary_power_rows_97_to_144
import Theorems.Thm_GrothendieckLB_Supplement_cq_primary_power_rows_145_to_192
import Theorems.Thm_GrothendieckLB_Supplement_cq_primary_power_rows_193_to_224
import Theorems.Thm_GrothendieckLB_Supplement_cq_primary_power_rows_225_to_251

open GrothendieckLB.Supplement CQHeadCertificate

theorem solution : ∀ c : ℕ, c < 16 → powerChecks c=true := by
  intro c hc
  apply List.all_eq_true.mpr
  intro k hk
  have hk' := List.mem_range.mp hk
  let p := 16*c+k
  have hp : p < 251 := by dsimp [p]; omega
  change (List.range 252).all (fun j => decide (power (p+1) j=powerAt p j))=true
  by_cases h0 : p < 48
  · exact cq_primary_power_rows_1_to_48 p (by omega) h0
  by_cases h1 : p < 96
  · exact cq_primary_power_rows_49_to_96 p (by omega) h1
  by_cases h2 : p < 144
  · exact cq_primary_power_rows_97_to_144 p (by omega) h2
  by_cases h3 : p < 192
  · exact cq_primary_power_rows_145_to_192 p (by omega) h3
  by_cases h4 : p < 224
  · exact cq_primary_power_rows_193_to_224 p (by omega) h4
  exact cq_primary_power_rows_225_to_251 p (by omega) hp
