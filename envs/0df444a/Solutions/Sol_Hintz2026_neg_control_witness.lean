-- Prove2me | solution 1 for Hintz2026.neg_control_witness
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T13:56:31.766475+00:00
-- url     : https://prove2.me/submissions/b741a626-7dfa-4509-bf42-1713b5910c02

import Definitions.Def_Hintz2026_AnalysisV2
import Theorems.Thm_Hintz2026_Dbad_X_ne_AX

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) : (of fun i j => Dbad p0 (fun z => X p0 z i j) x0) ≠ A p0 x0 * X p0 x0 :=
  Dbad_X_ne_AX p0 x0_mem (show p0.a ≠ 0 from one_ne_zero)

end
