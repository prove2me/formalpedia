-- Prove2me | solution 1 for ModularCurve.adjoin_jqModC_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/86674353-34e6-5861-89c4-d5d02ff872bc

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_adjoin_jqModC_eq_top

set_option autoImplicit false

open Polynomial ModularCurve

namespace GaussPencil

theorem modularFunctionFieldFullC_one_eq_adjoin (k₀ : Type*) [Field k₀] :
    modularFunctionFieldFullC k₀ 1 = IntermediateField.adjoin k₀ {jqModC k₀} := by
  have hS : divisorExpansionsC k₀ 1 = {jqModC k₀} := by
    ext y
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨d, _, hd, rfl⟩
      obtain rfl : d = 1 := Nat.dvd_one.mp hd
      rw [qExpand_one_apply]
    · rintro rfl
      exact ⟨1, inferInstance, dvd_refl 1, (qExpand_one_apply _).symm⟩
  show IntermediateField.adjoin k₀ (divisorExpansionsC k₀ 1) = _
  rw [hS]

theorem adjoin_jqModC_eq_top (k₀ : Type*) [Field k₀] :
    IntermediateField.adjoin k₀
      ({⟨jqModC k₀, jqModC_mem_full k₀ 1⟩} : Set ↥(modularFunctionFieldFullC k₀ 1)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  have hx : (x : LaurentSeries k₀) ∈ IntermediateField.adjoin k₀ {jqModC k₀} := by
    rw [← modularFunctionFieldFullC_one_eq_adjoin]; exact x.2
  rw [IntermediateField.mem_adjoin_simple_iff] at hx ⊢
  obtain ⟨r, t, hrt⟩ := hx
  refine ⟨r, t, Subtype.ext ?_⟩
  have hval : ∀ p : k₀[X], aeval (jqModC k₀) p
      = ((aeval (⟨jqModC k₀, jqModC_mem_full k₀ 1⟩ : ↥(modularFunctionFieldFullC k₀ 1)) p :
          ↥(modularFunctionFieldFullC k₀ 1)) : LaurentSeries k₀) :=
    fun p => aeval_algHom_apply (IntermediateField.val (modularFunctionFieldFullC k₀ 1))
      (⟨jqModC k₀, jqModC_mem_full k₀ 1⟩ : ↥(modularFunctionFieldFullC k₀ 1)) p
  rw [hrt, hval r, hval t]
  exact (map_div₀ (IntermediateField.val (modularFunctionFieldFullC k₀ 1)) _ _).symm

end GaussPencil

theorem solution (k₀ : Type*) [Field k₀] :
    IntermediateField.adjoin k₀
      ({⟨jqModC k₀, jqModC_mem_full k₀ 1⟩} : Set ↥(modularFunctionFieldFullC k₀ 1)) = ⊤ :=
  GaussPencil.adjoin_jqModC_eq_top k₀

end S_ModularCurve_adjoin_jqModC_eq_top
end P2MW
export P2MW.S_ModularCurve_adjoin_jqModC_eq_top (solution)
