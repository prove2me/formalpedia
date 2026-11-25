-- Prove2me | solution 1 for GlobalTheory.DRFil.FilV_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:12:03.726714+00:00
-- url     : https://prove2.me/submissions/2d567fc8-1cf4-4aa0-8965-6f7cbeede89b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_LocCoh
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Theorems.Thm_GlobalTheory_DRFil_fil_antitone
import Theorems.Thm_GlobalTheory_DRFil_tmul_mem_FilV
import Theorems.Thm_GlobalTheory_DRFil_FilV_induction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DRFil
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']
namespace GlobalTheory.DRFil
theorem _root_.solution : Antitone (FilV PD (LL := LL) (V := V)) := fun a _ hab _ hx =>
  FilV_induction PD (p := fun x => x ∈ FilV PD (LL := LL) (V := V) a) (Submodule.zero_mem _)
    (fun v _ hb => tmul_mem_FilV PD v (fil_antitone PD hab hb)) (fun _ _ => Submodule.add_mem _) hx
end GlobalTheory.DRFil
