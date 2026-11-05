-- Prove2me | solution 1 for GeneralPieces.GenF.JmT_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:54:19.7298+00:00
-- url     : https://prove2.me/submissions/cddb51d9-0ef0-426c-834e-46742b8d9566

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_GenF_DDComm
import Theorems.Thm_GeneralPieces_GenF_JmU_comm
import Theorems.Thm_GeneralPieces_GenF_hder_comm


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson
namespace GeneralPieces.GenF
theorem _root_.solution (n m : ℕ) (f : Tv) : JmT n (JmT m f) = JmT m (JmT n f) := hder_comm (fun a => JmU_comm n m a) f
end GeneralPieces.GenF
