-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_packed_base_checks
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:06:59.191946+00:00
-- url     : https://prove2.me/submissions/ab84e3da-6d81-4ece-81e2-8b21714fe8a3

import Theorems.Thm_GrothendieckLB_Supplement_cq_certified_raw_moment_and_factorial_tables
import Theorems.Thm_GrothendieckLB_Supplement_cq_certified_zeroth_hermite_and_primary_rows
import Theorems.Thm_GrothendieckLB_Supplement_cq_certified_125_terminal_comparisons

open GrothendieckLB.Supplement GrothendieckLB.Supplement.CQHeadCertificate

theorem solution : rawChecks=true ∧ initialChecks=true ∧ factChecks=true ∧ totalChecks=true :=
  ⟨cq_certified_raw_moment_and_factorial_tables.1,cq_certified_zeroth_hermite_and_primary_rows,cq_certified_raw_moment_and_factorial_tables.2,cq_certified_125_terminal_comparisons⟩
