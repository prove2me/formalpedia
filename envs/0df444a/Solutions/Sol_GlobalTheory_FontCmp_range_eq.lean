-- Prove2me | solution 1 for GlobalTheory.FontCmp.range_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:02:20.912585+00:00
-- url     : https://prove2.me/submissions/f685a7eb-29d9-4906-9bf7-98fa9cf2c0cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FontaineFormalismTensorEquiv
import Theorems.Thm_GlobalTheory_FontCmp_mB_mul
import Theorems.Thm_GlobalTheory_FontCmp_cmp_ind
import Theorems.Thm_GlobalTheory_FontCmp_exists_proj
import Theorems.Thm_GlobalTheory_FontCmp_prod_mB_left
import Theorems.Thm_GlobalTheory_FontCmp_prod_mB_right
import Theorems.Thm_GlobalTheory_FontCmp_prod_mem
import Theorems.Thm_GlobalTheory_FontCmp_mulDcris_tmul
import Theorems.Thm_GlobalTheory_FontCmp_range_le
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CrystallineSubrepresentation_prodB_tmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FontCmp
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct GlobalTheory.IndefiniteRowSideFullHecke
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
namespace GlobalTheory.FontCmp
theorem _root_.solution {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (h : Function.Bijective (CrystallineSubrepresentation.comparison PD ρ))
    (h' : Function.Bijective (CrystallineSubrepresentation.comparison PD ρ'))
    (h'' : Function.Bijective (CrystallineSubrepresentation.comparison PD (ρ.tprod ρ'))) :
    LinearMap.range (TensorMultiplication.mulDcris PD ρ ρ') = Dcris PD (ρ.tprod ρ') := by
  refine le_antisymm (range_le PD) fun z hz => ?_
  obtain ⟨lam, π, hπ, hid, -, -⟩ := exists_proj PD h''
  have key : ∀ (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B),
      (π (CrystallineSubrepresentation.prodB (LL := LL) (x ⊗ₜ[LL] y)) : (V ⊗[LL] V') ⊗[Qp] B) ∈
        LinearMap.range (TensorMultiplication.mulDcris PD ρ ρ') := by
    intro x y
    induction x using cmp_ind PD h with
    | h0 => simp
    | hadd a c ha hc =>
      simp only [add_tmul, map_add, Submodule.coe_add]; exact Submodule.add_mem _ ha hc
    | hb b d =>
      induction y using cmp_ind PD h' with
      | h0 => simp
      | hadd a c ha hc =>
        simp only [tmul_add, map_add, Submodule.coe_add]; exact Submodule.add_mem _ ha hc
      | hb b' d' =>
        rw [prod_mB_left, prod_mB_right, ← mB_mul]
        have := hπ (b * b') ⟨_, prod_mem PD d d'⟩
        simp only at this
        rw [this, coe_mK]
        exact ⟨mK PD ρ (lam (b * b')) d ⊗ₜ d', by rw [mulDcris_tmul, coe_mK, prod_mB_left]⟩
  have all : ∀ z : (V ⊗[LL] V') ⊗[Qp] B, (π z : (V ⊗[LL] V') ⊗[Qp] B) ∈
      LinearMap.range (TensorMultiplication.mulDcris PD ρ ρ') := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, Submodule.coe_add]; exact Submodule.add_mem _ ha hc
    | tmul u b =>
      induction u using TensorProduct.induction_on with
      | zero => simp
      | add a c ha hc =>
        simp only [add_tmul, map_add, Submodule.coe_add]; exact Submodule.add_mem _ ha hc
      | tmul v v' =>
        have := key (v ⊗ₜ b) (v' ⊗ₜ 1)
        rwa [CrystallineSubrepresentation.prodB_tmul, mul_one] at this
  have := all z
  rwa [show π z = ⟨z, hz⟩ from hid ⟨z, hz⟩] at this
end GlobalTheory.FontCmp
