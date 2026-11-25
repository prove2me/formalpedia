-- Prove2me | solution 1 for Konig.lineGraph_chromaticNumber_of_colorable_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:07:45.720903+00:00
-- url     : https://prove2.me/submissions/327555e7-ca29-4f4e-a3a9-f4331fde6f22

module
public import Definitions.Def_LeanPool_Vizing_Main
public import Definitions.Def_Konig_Basic
public import Theorems.Thm_Konig_lineGraph_colorable_of_colorable_two
public import Theorems.Thm_Konig_maxDegree_le_lineGraph_chromaticNumber

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Konig
open LeanPool.Vizing LeanPool.Vizing.PEC
variable {V : Type*} {C : Type*} {G : SimpleGraph V}
namespace Konig
theorem _root_.solution [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : G.Colorable 2) :
    G.lineGraph.chromaticNumber = G.maxDegree :=
  le_antisymm (lineGraph_colorable_of_colorable_two G h).chromaticNumber_le
    (maxDegree_le_lineGraph_chromaticNumber G)
end Konig
