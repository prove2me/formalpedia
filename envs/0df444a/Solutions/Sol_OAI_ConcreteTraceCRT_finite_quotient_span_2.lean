-- Prove2me | solution 2 for OAI.ConcreteTraceCRT.finite_quotient_span
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:10:12.228242+00:00
-- url     : https://prove2.me/submissions/acdb28c4-6306-4d68-a1ec-b9a54ee4af40

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
set_option autoImplicit false
open OAI.EisensteinEmbedding

theorem solution {a : O} (ha : a ≠ 0) :
    Finite (O ⧸ Ideal.span {a}) := by
  apply Ring.HasFiniteQuotients.finiteQuotient
  intro h
  exact ha (Ideal.span_singleton_eq_bot.mp h)
