-- Prove2me | solution 1 for Newton.su2StructureConstant_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:15:56.865203+00:00
-- url     : https://prove2.me/submissions/09f80ab6-dcfd-4116-a87e-da463421d3af

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
import Theorems.Thm_Newton_SuNAlgebra_lie_matrix
attribute [local simp] Newton.SuNAlgebra.lie_matrix



set_option autoImplicit false
open Matrix
open Newton
namespace Newton
theorem _root_.solution (a b c : Fin 3) :
    su2StructureConstant b a c = -su2StructureConstant a b c := by
  simp only [su2StructureConstant]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp
end Newton
