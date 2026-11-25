-- Prove2me | solution 1 for GlobalTheory.FontCmp.letter_of_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:02:15.858667+00:00
-- url     : https://prove2.me/submissions/959e0013-1bbf-4619-a480-928811121cc8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FontaineFormalismTensorEquiv
import Theorems.Thm_GlobalTheory_FontCmp_mB_one
import Theorems.Thm_GlobalTheory_FontCmp_prod_mB_left
import Theorems.Thm_GlobalTheory_FontCmp_prod_mem
import Theorems.Thm_GlobalTheory_FontCmp_mulDcris_tmul
import Theorems.Thm_GlobalTheory_FontCmp_actKK_tmul
import Theorems.Thm_GlobalTheory_FontCmp_mem_DcrisL
import Theorems.Thm_GlobalTheory_FontCmp_actKK_mul
import Theorems.Thm_GlobalTheory_FontCmp_actKK_mem
import Theorems.Thm_GlobalTheory_FontCmp_actKK_eigen
import Theorems.Thm_GlobalTheory_FontCmp_prod_actKK_left
import Theorems.Thm_GlobalTheory_FontCmp_prod_actKK_right

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
theorem _root_.solution [Algebra.IsSeparable Qp K₀]
    {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (hr : LinearMap.range (TensorMultiplication.mulDcris PD ρ ρ') = Dcris PD (ρ.tprod ρ'))
    (hk : LinearMap.ker (TensorMultiplication.mulDcris PD ρ ρ') = TensorMultiplication.balK PD ρ ρ') (τ : K₀ →ₐ[Qp] LL) :
    Function.Injective ((CrystallineSubrepresentation.prodB (LL := LL)).comp
        (TensorProduct.map (DcrisL PD ρ τ).subtype (DcrisL PD ρ' τ).subtype)) ∧
      LinearMap.range ((CrystallineSubrepresentation.prodB (LL := LL)).comp
        (TensorProduct.map (DcrisL PD ρ τ).subtype (DcrisL PD ρ' τ).subtype)) =
        DcrisL PD (ρ.tprod ρ') τ := by
  haveI := PD.finK₀
  haveI : Algebra.FormallyUnramified Qp K₀ := Algebra.FormallyUnramified.of_isSeparable Qp K₀
  obtain ⟨t, ht, ht1⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := Qp)
    (S := K₀)).1 inferInstance
  have hE : ∀ (U : Type) [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]
      (x : U ⊗[Qp] B) (c : K₀),
      mB LL (algebraMap K₀ B c) (actKK LL U τ t x) = τ c • actKK LL U τ t x := by
    intro U _ _ _ _ x c
    have h1 : actKK LL U τ ((1 : K₀) ⊗ₜ[Qp] c * t) x = actKK LL U τ (c ⊗ₜ[Qp] (1 : K₀) * t) x := by
      rw [sub_eq_zero.1 ((sub_mul _ _ _).symm.trans (ht c))]
    rw [actKK_mul, actKK_mul, actKK_tmul, actKK_tmul] at h1
    simpa [mB_one] using h1
  have hI : ∀ (U : Type) [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]
      (x : U ⊗[Qp] B), (∀ c : K₀, mB LL (algebraMap K₀ B c) x = τ c • x) →
      actKK LL U τ t x = x := by
    intro U _ _ _ _ x hx
    rw [actKK_eigen τ t x hx, ht1, map_one, one_smul]
  have hC : ∀ (U : Type) [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]
      (x : U ⊗[Qp] B) (c : K₀),
      actKK LL U τ t (mB LL (algebraMap K₀ B c) x) = τ c • actKK LL U τ t x := by
    intro U _ _ _ _ x c
    have h1 : actKK LL U τ (t * (1 : K₀) ⊗ₜ[Qp] c) x = actKK LL U τ ((1 : K₀) ⊗ₜ[Qp] c * t) x := by
      rw [mul_comm]
    rw [actKK_mul, actKK_mul, actKK_tmul, actKK_tmul, hE] at h1
    simpa using h1
  let p : ↥(Dcris PD ρ) →ₗ[LL] ↥(DcrisL PD ρ τ) :=
    (actKK LL V τ t).restrict fun x hx => (mem_DcrisL PD ρ τ _).2 ⟨actKK_mem PD ρ τ t x hx, hE V x⟩
  let p' : ↥(Dcris PD ρ') →ₗ[LL] ↥(DcrisL PD ρ' τ) :=
    (actKK LL V' τ t).restrict
      fun x hx => (mem_DcrisL PD ρ' τ _).2 ⟨actKK_mem PD ρ' τ t x hx, hE V' x⟩
  let i : ↥(DcrisL PD ρ τ) →ₗ[LL] ↥(Dcris PD ρ) := Submodule.inclusion inf_le_left
  let i' : ↥(DcrisL PD ρ' τ) →ₗ[LL] ↥(Dcris PD ρ') := Submodule.inclusion inf_le_left
  have hfac : ∀ w, ((CrystallineSubrepresentation.prodB (LL := LL)).comp
      (TensorProduct.map (DcrisL PD ρ τ).subtype (DcrisL PD ρ' τ).subtype)) w =
      TensorMultiplication.mulDcris PD ρ ρ' (TensorProduct.map i i' w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, ha, hc]
    | tmul x y => rfl
  have hpi : ∀ w, TensorProduct.map p p' (TensorProduct.map i i' w) = w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, ha, hc]
    | tmul x y =>
      rw [map_tmul, map_tmul]
      congr 1
      · exact Subtype.ext (hI V x ((mem_DcrisL PD ρ τ _).1 x.2).2)
      · exact Subtype.ext (hI V' y ((mem_DcrisL PD ρ' τ _).1 y.2).2)
  have hbal : TensorMultiplication.balK PD ρ ρ' ≤ LinearMap.ker (TensorProduct.map p p') := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, x, cx, y, cy, hx, hy, rfl⟩
    change TensorProduct.map p p' _ = 0
    have h1 : p cx = τ c • p x := Subtype.ext (by
      change actKK LL V τ t (cx : V ⊗[Qp] B) = τ c • actKK LL V τ t (x : V ⊗[Qp] B)
      rw [hx, mulVB_eq, hC])
    have h2 : p' cy = τ c • p' y := Subtype.ext (by
      change actKK LL V' τ t (cy : V' ⊗[Qp] B) = τ c • actKK LL V' τ t (y : V' ⊗[Qp] B)
      rw [hy, mulVB_eq, hC])
    rw [map_sub, map_tmul, map_tmul, h1, h2, smul_tmul, sub_self]
  refine ⟨(injective_iff_map_eq_zero _).2 fun w hw => ?_, le_antisymm ?_ fun z hz => ?_⟩
  · rw [hfac, ← LinearMap.mem_ker, hk] at hw
    rw [← hpi w]
    exact hbal hw
  · rintro _ ⟨w, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => rw [map_add]; exact Submodule.add_mem _ ha hc
    | tmul x y =>
      rw [mem_DcrisL]
      refine ⟨prod_mem PD (i x) (i' y), fun c => ?_⟩
      change mB LL _ (CrystallineSubrepresentation.prodB ((x : V ⊗[Qp] B) ⊗ₜ[LL] (y : V' ⊗[Qp] B))) =
        τ c • CrystallineSubrepresentation.prodB ((x : V ⊗[Qp] B) ⊗ₜ[LL] (y : V' ⊗[Qp] B))
      rw [← prod_mB_left, ((mem_DcrisL PD ρ τ _).1 x.2).2, ← smul_tmul', map_smul]
  · obtain ⟨hz1, hz2⟩ := (mem_DcrisL PD _ τ _).1 hz
    rw [← hr] at hz1
    obtain ⟨w, rfl⟩ := hz1
    refine ⟨TensorProduct.map p p' w, ?_⟩
    rw [← hI _ _ hz2]
    clear hz hz2
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, ha, hc]
    | tmul x y =>
      change CrystallineSubrepresentation.prodB (LL := LL) (actKK LL V τ t (x : V ⊗[Qp] B) ⊗ₜ[LL]
        actKK LL V' τ t (y : V' ⊗[Qp] B)) = _
      rw [mulDcris_tmul, prod_actKK_left, prod_actKK_right, hI _ _ (hE _ _)]
end GlobalTheory.FontCmp
