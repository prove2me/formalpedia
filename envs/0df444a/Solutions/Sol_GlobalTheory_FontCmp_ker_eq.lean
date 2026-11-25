-- Prove2me | solution 1 for GlobalTheory.FontCmp.ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:02:08.727659+00:00
-- url     : https://prove2.me/submissions/d9a05073-e472-4d92-bedd-0d4b9117dd84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FontaineFormalismTensorEquiv
import Theorems.Thm_GlobalTheory_FontCmp_exists_liftAdd
import Theorems.Thm_GlobalTheory_FontCmp_mB_mul
import Theorems.Thm_GlobalTheory_FontCmp_mB_one
import Theorems.Thm_GlobalTheory_FontCmp_cmp_ind
import Theorems.Thm_GlobalTheory_FontCmp_cmp_lift
import Theorems.Thm_GlobalTheory_FontCmp_exists_proj
import Theorems.Thm_GlobalTheory_FontCmp_prod_mB_left
import Theorems.Thm_GlobalTheory_FontCmp_prod_mB_right
import Theorems.Thm_GlobalTheory_FontCmp_mulDcris_tmul
import Theorems.Thm_GlobalTheory_FontCmp_bal_mem
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
    (h' : Function.Bijective (CrystallineSubrepresentation.comparison PD ρ')) :
    LinearMap.ker (TensorMultiplication.mulDcris PD ρ ρ') = TensorMultiplication.balK PD ρ ρ' := by
  refine le_antisymm ?_ ?_
  swap
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, x, cx, y, cy, hx, hy, rfl⟩
    change TensorMultiplication.mulDcris PD ρ ρ' _ = 0
    rw [map_sub, mulDcris_tmul, mulDcris_tmul, hx, hy, mulVB_eq, mulVB_eq, prod_mB_left,
      prod_mB_right, sub_self]
  obtain ⟨lam, π, hπ, hid, hπa, hπc⟩ := exists_proj PD h
  let q := (TensorMultiplication.balK PD ρ ρ').mkQ
  have hq : ∀ c x y, q (mK PD ρ c x ⊗ₜ y) = q (x ⊗ₜ mK PD ρ' c y) := fun c x y => by
    rw [← sub_eq_zero, ← map_sub]
    exact (Submodule.Quotient.mk_eq_zero _).2 (bal_mem PD c x y)
  have e1 := fun x : V ⊗[Qp] B => cmp_lift PD h' (fun b d' => q (π (mB LL b x) ⊗ₜ d'))
    (fun m m' n => by simp only [mB_add, map_add, add_tmul])
    (fun m n n' => by simp only [map_add, tmul_add])
    (fun c b d => by rw [mB_mul, hπc, hq])
  choose γ hγ using e1
  have γadd : ∀ x x' y, γ (x + x') y = γ x y + γ x' y := by
    intro x x' y
    induction y using cmp_ind PD h' with
    | h0 => simp
    | hadd a c ha hc => simp only [map_add, ha, hc]; abel
    | hb b d => simp only [hγ, map_add, add_tmul]
  have γsmul : ∀ (a : LL) x y, γ (a • x) y = γ x (a • y) := by
    intro a x y
    induction y using cmp_ind PD h' with
    | h0 => simp
    | hadd a c ha hc => simp only [smul_add, map_add, ha, hc]
    | hb b d =>
      rw [← map_smul, ← Submodule.coe_smul, hγ, hγ, map_smul, hπa, smul_tmul]
  have γB : ∀ (b : B) x y, γ (mB LL b x) y = γ x (mB LL b y) := by
    intro a x y
    induction y using cmp_ind PD h' with
    | h0 => simp
    | hadd a c ha hc => simp only [map_add, ha, hc]
    | hb b d => rw [← mB_mul, hγ, hγ, ← mB_mul, mul_comm]
  have e2 := fun b : B => exists_liftAdd (R := LL)
    (fun (v : V) (v' : V') => γ (v ⊗ₜ[Qp] b) (v' ⊗ₜ[Qp] (1 : B)))
    (fun m m' n => by simp only [add_tmul, γadd])
    (fun m n n' => by simp only [add_tmul, map_add])
    (fun r m n => by rw [← smul_tmul', γsmul, smul_tmul'])
  choose Φ₁ hΦ₁ using e2
  obtain ⟨Φ, hΦ⟩ := exists_liftAdd (R := Qp) (fun (u : V ⊗[LL] V') (b : B) => Φ₁ b u)
    (fun m m' n => by simp only [map_add])
    (fun u b b' => by
      induction u using TensorProduct.induction_on with
      | zero => simp
      | add a c ha hc => simp only [map_add, ha, hc]; abel
      | tmul v v' => simp only [hΦ₁, tmul_add, γadd])
    (fun r u b => by
      induction u using TensorProduct.induction_on with
      | zero => simp
      | add a c ha hc => simp only [smul_add, map_add, ha, hc]
      | tmul v v' => rw [smul_tmul', hΦ₁, hΦ₁, smul_tmul])
  have γ0 : ∀ y, γ 0 y = 0 := fun y => by
    have := γadd 0 0 y
    rw [add_zero] at this
    simpa using this
  have hprod : ∀ x y, Φ (CrystallineSubrepresentation.prodB (LL := LL) (x ⊗ₜ[LL] y)) = γ x y := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp [γ0]
    | add a c ha hc => simp only [map_add, add_tmul, ha, hc, γadd]
    | tmul v c =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add a c ha hc => simp only [map_add, tmul_add, ha, hc]
      | tmul v' c' =>
        rw [CrystallineSubrepresentation.prodB_tmul, hΦ, hΦ₁, mul_comm, ← mB_tmul (LL := LL), γB, mB_tmul, mul_one]
  have hall : ∀ w, Φ (TensorMultiplication.mulDcris PD ρ ρ' w) = q w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, ha, hc]
    | tmul x y =>
      rw [mulDcris_tmul, hprod, ← mB_one (LL := LL) (y : V' ⊗[Qp] B), hγ, mB_one, hid]
  intro w hw
  have := hall w
  rw [LinearMap.mem_ker.1 hw, map_zero] at this
  exact (Submodule.Quotient.mk_eq_zero _).1 this.symm
end GlobalTheory.FontCmp
