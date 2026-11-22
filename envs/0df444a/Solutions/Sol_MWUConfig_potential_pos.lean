-- Prove2me | solution 1 for MWUConfig.potential_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:32:42.589259+00:00
-- url     : https://prove2.me/submissions/aa25a8dc-ceca-40b3-bc1d-52198fe6976e

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
namespace MWUConfig
theorem _root_.solution {C : Type*} [Fintype C] [Nonempty C]
    (cfg : MWUConfig C) : 0 < cfg.potential :=
  Finset.sum_pos (fun c _ => cfg.weights_pos c) univ_nonempty
end MWUConfig
