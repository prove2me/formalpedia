-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block09_part01_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T06:34:13.531527+00:00
-- url     : https://prove2.me/submissions/82395d73-179c-4d9a-96d7-6d64f2d62964

import Theorems.Thm_OAI_Snaky21_Certificate_block09_part01_group00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part01_group01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part01_group02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part01_group03_valid
import Definitions.Def_Snaky21Data09
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part00_valid
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate

theorem solution : Valid card_592 ∧ Valid card_593 ∧ Valid card_594 ∧ Valid card_595 ∧ Valid card_596 ∧ Valid card_597 ∧ Valid card_598 ∧ Valid card_599 ∧ Valid card_600 ∧ Valid card_601 ∧ Valid card_602 ∧ Valid card_603 ∧ Valid card_604 ∧ Valid card_605 ∧ Valid card_606 ∧ Valid card_607 ∧ True :=
  ⟨block09_part01_group00_valid.1, block09_part01_group00_valid.2.1, block09_part01_group00_valid.2.2.1, block09_part01_group00_valid.2.2.2.1, block09_part01_group01_valid.1, block09_part01_group01_valid.2.1, block09_part01_group01_valid.2.2.1, block09_part01_group01_valid.2.2.2.1, block09_part01_group02_valid.1, block09_part01_group02_valid.2.1, block09_part01_group02_valid.2.2.1, block09_part01_group02_valid.2.2.2.1, block09_part01_group03_valid.1, block09_part01_group03_valid.2.1, block09_part01_group03_valid.2.2.1, block09_part01_group03_valid.2.2.2.1, True.intro⟩
