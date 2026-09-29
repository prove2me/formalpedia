-- Prove2me | solution 1 for LiouvilleDiffAlg.constants_isSubfield
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T22:41:49.989377+00:00
-- url     : https://prove2.me/submissions/6903a420-44a4-408a-a98a-b54ad998013d

import Mathlib
import Definitions.Def_LiouvilleDiffAlg_Basic

open scoped Differential
open LiouvilleDiffAlg

theorem solution (F : Type*) [Field F] [Differential F] :
    ∃ S : Subfield F, (S : Set F) = constants F := by
  refine ⟨{ carrier := constants F
            mul_mem' := fun {a b} ha hb => by
              show (a * b)′ = 0
              rw [Derivation.leibniz, show a′ = 0 from ha, show b′ = 0 from hb, smul_zero,
                smul_zero, add_zero]
            one_mem' := by
              show (1 : F)′ = 0
              exact Derivation.map_one_eq_zero _
            add_mem' := fun {a b} ha hb => by
              show (a + b)′ = 0
              rw [map_add, show a′ = 0 from ha, show b′ = 0 from hb, add_zero]
            zero_mem' := by
              show (0 : F)′ = 0
              exact map_zero _
            neg_mem' := fun {a} ha => by
              show (-a)′ = 0
              rw [map_neg, show a′ = 0 from ha, neg_zero]
            inv_mem' := fun a ha => by
              show (a⁻¹)′ = 0
              rw [Derivation.leibniz_inv, show a′ = 0 from ha, smul_zero] }, rfl⟩
