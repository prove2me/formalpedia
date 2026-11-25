-- Prove2me | solution 1 for GlobalTheory.AbCoh.mem_map_ann_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:36:02.459937+00:00
-- url     : https://prove2.me/submissions/66885d32-da36-4df7-923c-c1c3a6e550c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullSurjectiveAndKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveDeformationAffineSections
import Theorems.Thm_GlobalTheory_AbCoh_mem_map_of_smul_eq_zero_of_flat
import Theorems.Thm_GlobalTheory_AbLaw_SecOnR_smul_def
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_smul
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_smul
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
import Theorems.Thm_GlobalTheory_Cris_Thick_Hom_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AbCoh
namespace GlobalTheory.AbCoh
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (t : R) (J : Ideal R) (hJ : ∀ a, a ∈ J ↔ a * t = 0) (b : S) :
    b ∈ J.map (algebraMap R S) ↔ t • b = 0 := by
  refine ⟨fun hb ↦ ?_, mem_map_of_smul_eq_zero_of_flat t J hJ b⟩
  rw [Algebra.smul_def]
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [← map_mul, _root_.mul_comm, (hJ a).1 ha, map_zero]
  | zero => exact MulZeroClass.mul_zero _
  | add x y _ _ hx hy => rw [_root_.mul_add, hx, hy, _root_.add_zero]
  | smul a x _ hx => rw [smul_eq_mul, _root_.mul_left_comm, hx, MulZeroClass.mul_zero]
end GlobalTheory.AbCoh
