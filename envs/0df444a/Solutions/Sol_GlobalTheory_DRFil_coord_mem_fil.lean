-- Prove2me | solution 1 for GlobalTheory.DRFil.coord_mem_fil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:12:46.127911+00:00
-- url     : https://prove2.me/submissions/addae27a-be06-4ffd-bb53-1ec5202786f2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_LocCoh
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
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
theorem _root_.solution {ι : Type} [DecidableEq ι] (b : Basis ι Qp V) {a : ℤ} {x : V ⊗[Qp] F}
    (hx : x ∈ FilV PD (LL := LL) (V := V) a) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft (N := F) b x i ∈ PD.Fil a := by
  refine FilV_induction PD
    (p := fun x => TensorProduct.equivFinsuppOfBasisLeft (N := F) b x i ∈ PD.Fil a) ?_ ?_ ?_ hx
  · simp
  · intro v c hc
    simpa using ((PD.Fil a).restrictScalars Qp).smul_mem (b.repr v i) hc
  · intro x y hx hy
    simpa only [map_add, Finsupp.add_apply] using Submodule.add_mem _ hx hy
end GlobalTheory.DRFil
