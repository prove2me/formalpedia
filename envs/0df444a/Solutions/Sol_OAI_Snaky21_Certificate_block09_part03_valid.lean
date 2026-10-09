-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block09_part03_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T06:56:13.207405+00:00
-- url     : https://prove2.me/submissions/edbca14c-6f51-4e82-9002-e2da47dd602c

import Theorems.Thm_OAI_Snaky21_Certificate_block09_part03_group00_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part03_group01_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part03_group02_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part03_group03_valid
import Definitions.Def_Snaky21Data09
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part02_valid
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate

theorem solution : Valid card_624 ∧ Valid card_625 ∧ Valid card_626 ∧ Valid card_627 ∧ Valid card_628 ∧ Valid card_629 ∧ Valid card_630 ∧ Valid card_631 ∧ Valid card_632 ∧ Valid card_633 ∧ Valid card_634 ∧ Valid card_635 ∧ Valid card_636 ∧ Valid card_637 ∧ Valid card_638 ∧ Valid card_639 ∧ True :=
  ⟨block09_part03_group00_valid.1, block09_part03_group00_valid.2.1, block09_part03_group00_valid.2.2.1, block09_part03_group00_valid.2.2.2.1, block09_part03_group01_valid.1, block09_part03_group01_valid.2.1, block09_part03_group01_valid.2.2.1, block09_part03_group01_valid.2.2.2.1, block09_part03_group02_valid.1, block09_part03_group02_valid.2.1, block09_part03_group02_valid.2.2.1, block09_part03_group02_valid.2.2.2.1, block09_part03_group03_valid.1, block09_part03_group03_valid.2.1, block09_part03_group03_valid.2.2.1, block09_part03_group03_valid.2.2.2.1, True.intro⟩
