-- Prove2me | solution 1 for O3.Stage2RouteD.pairing_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:13:09.809613+00:00
-- url     : https://prove2.me/submissions/662ce088-f607-4eaf-9b40-57df1c586bdc

import Definitions.Def_O3_GeometryExperimental
import Definitions.Def_O3_Stage2RouteD
import Theorems.Thm_O3_Stage2RouteD_pairing_smul_left
import Theorems.Thm_O3_pairing_comm


set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteD
namespace O3.Stage2RouteD
theorem _root_.solution {d : ℕ} (a : ℝ) (x y : Point d) :
    pairing x (a • y) = a * pairing x y := by
  rw [pairing_comm, pairing_smul_left, pairing_comm]
end O3.Stage2RouteD
