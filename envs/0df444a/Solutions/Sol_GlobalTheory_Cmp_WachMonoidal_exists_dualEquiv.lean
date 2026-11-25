-- Prove2me | solution 1 for GlobalTheory.Cmp.WachMonoidal.exists_dualEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:29:18.372325+00:00
-- url     : https://prove2.me/submissions/294e9b45-7936-4a9d-bf8e-fd205abbdd3d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersCompleteDVR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitSumTensorDualOfWachMonoidal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cmp GlobalTheory.Cmp.WachMonoidal
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
open GlobalTheory.IndefiniteRowSideFullHecke
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
namespace GlobalTheory.Cmp.WachMonoidal
theorem _root_.solution {A R D D' : Type} [CommRing A] [CommRing R] [Algebra A R]
    [AddCommGroup D] [Module R D] [Module A D] [IsScalarTower A R D]
    [AddCommGroup D'] [Module R D'] [Module A D'] [IsScalarTower A R D']
    (hinj : Function.Injective (algebraMap A R)) (N : Submodule A D) (N' : Submodule A D')
    (b : D →ₗ[R] D' →ₗ[R] R) (hv : ∀ y ∈ N', ∀ x ∈ N, ∃ a : A, b x y = algebraMap A R a)
    (hi : ∀ y, (∀ x ∈ N, b x y = 0) → y = 0)
    (hs : ∀ f : ↥N →ₗ[A] A, ∃ y ∈ N', ∀ x : ↥N, b (x : D) y = algebraMap A R (f x)) :
    ∃ δ : ↥N' ≃ₗ[A] Module.Dual A ↥N,
      ∀ (x : ↥N) (y : ↥N'), b (x : D) (y : D') = algebraMap A R (δ y x) := by
  choose c hc using hv
  have hl : ∀ (a : A) (x : D) (y : D'), b (a • x) y = algebraMap A R a * b x y := by
    intro a x y
    rw [← algebraMap_smul R a x, map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hr : ∀ (a : A) (x : D) (y : D'), b x (a • y) = algebraMap A R a * b x y := by
    intro a x y
    rw [← algebraMap_smul R a y, map_smul, smul_eq_mul]
  let d : ↥N' →ₗ[A] ↥N →ₗ[A] A := LinearMap.mk₂ A (fun y x => c y y.2 x x.2)
    (fun y y' x => hinj (by rw [map_add, ← hc, ← hc, ← hc, Submodule.coe_add, map_add]))
    (fun a y x => hinj (by rw [smul_eq_mul, map_mul, ← hc, ← hc, Submodule.coe_smul, hr]))
    (fun y x x' => hinj (by
      rw [map_add, ← hc, ← hc, ← hc, Submodule.coe_add, map_add, LinearMap.add_apply]))
    (fun a y x => hinj (by rw [smul_eq_mul, map_mul, ← hc, ← hc, Submodule.coe_smul, hl]))
  have hd : ∀ (x : ↥N) (y : ↥N'), b (x : D) (y : D') = algebraMap A R (d y x) :=
    fun x y => hc y y.2 x x.2
  refine ⟨LinearEquiv.ofBijective d ⟨?_, fun f => ?_⟩, hd⟩
  · rw [injective_iff_map_eq_zero]
    intro y hy
    refine Subtype.ext (hi y fun x hx => ?_)
    rw [hd ⟨x, hx⟩ y, hy, LinearMap.zero_apply, map_zero]
  · obtain ⟨y, hy, hf⟩ := hs f
    refine ⟨⟨y, hy⟩, LinearMap.ext fun x => hinj ?_⟩
    rw [← hd, hf]
end GlobalTheory.Cmp.WachMonoidal
