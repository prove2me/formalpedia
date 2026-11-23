-- Prove2me | solution 1 for GlobalTheory.DRFil.bil_mem_FilV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:08:01.685011+00:00
-- url     : https://prove2.me/submissions/1bed3e87-300b-4d4f-a187-a73a81d2c2da

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_LocCoh
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
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
theorem _root_.solution (β : V →ₗ[LL] V' →ₗ[LL] V'') {a b : ℤ} {x : V ⊗[Qp] F} {y : V' ⊗[Qp] F}
    (hx : x ∈ FilV PD (LL := LL) (V := V) a) (hy : y ∈ FilV PD (LL := LL) (V := V') b) :
    bil Qp F β x y ∈ FilV PD (LL := LL) (V := V'') (a + b) := by
  refine FilV_induction PD (p := fun x => bil Qp F β x y ∈ FilV PD (LL := LL) (V := V'') (a + b))
    (by simp) (fun v c hc => ?_) (fun x x' h h' => ?_) hx
  · refine FilV_induction PD
      (p := fun y => bil Qp F β (v ⊗ₜ[Qp] c) y ∈ FilV PD (LL := LL) (V := V'') (a + b))
      (by simp) (fun w d hd => ?_) (fun x x' h h' => ?_) hy
    · rw [bil_tmul]
      exact tmul_mem_FilV PD _ (PD.Fil_mul _ _ _ _ hc hd)
    · rw [map_add]
      exact Submodule.add_mem _ h h'
  · rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ h h'
end GlobalTheory.DRFil
