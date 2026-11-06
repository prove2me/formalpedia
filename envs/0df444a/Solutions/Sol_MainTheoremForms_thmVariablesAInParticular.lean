-- Prove2me | solution 1 for MainTheoremForms.thmVariablesAInParticular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:56:20.930898+00:00
-- url     : https://prove2.me/submissions/52ee527b-6066-48a5-bc2e-569b63cb8dfe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_StepSparsify
import Definitions.Def_VariableBound_Printed_VariablesA_Setting
import Definitions.Def_VariableBound_Printed_VariablesA_Main
import Definitions.Def_VariableBound_Params_Ineq
import Definitions.Def_UniformInK_Top_Correct
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_ParityChecks_CertOL
import Definitions.Def_UniformInK_Cert_Top
import Definitions.Def_UniformInK_Tree_Tree
import Definitions.Def_UniformInK_Tree_Defs
import Definitions.Def_UniformInK_Tree_Stack
import Definitions.Def_UniformInK_Spars_Main
import Definitions.Def_UniformInK_Cert_Walk
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_UniformInK_Top_ArithDefs
import Definitions.Def_FixedWidthVariableBoundStatement
import Definitions.Def_ClauseBound_ParityChecks_MasterOL
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_Alg_CertTopNet
import Definitions.Def_PaddedDescent_Col_CertG
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_CountKSatRate_Walk
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_CountKSat_InOut
import Definitions.Def_VariableBound_Printed_ThmVariablesA
import Theorems.Thm_VariableBound_VariablesA_thmVariablesAInParticular


set_option autoImplicit false
section
section
open MainTheoremForms
open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.ParityChecks UniformInK VariableBound.VariablesA
namespace MainTheoremForms
theorem _root_.solution : ThmVariablesAInParticular := VariableBound.VariablesA.thmVariablesAInParticular
end MainTheoremForms
