-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.tmul_mem_span_invariant_mul_sup_span_diagCasimir_of_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/c06e290e-d35d-5e0d-8725-fe7fddf1f1ab

import Mathlib
import Theorems.Thm_LinearAlgebra_exists_eigenvector_add_image_sum_sq_of_skew_of_posDef_hermitian
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul
import Theorems.Thm_LanglandsTunnell_CubicInduction_mem_span_invariant_mul_of_diagCasimir_add_two_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_tmul_mem_span_invariant_mul_sup_span_diagCasimir_of_isHomogeneous
p2m_attr_erase "instance" "NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion NumberField.AdelicCentre.locallyCompactSpace_adelicPGL2 NumberField.AdelicCentre.isTopologicalGroup_adelicPGL2 NumberField.AdelicCentre.t2Space_adelicPGL2 NumberField.AdelicCentre.isClosed_center FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.gl3AmbientRightTranslate_apply LanglandsTunnell.CubicInduction.CubicInductionForm.mk.injEq LanglandsTunnell.CubicInduction.CubicInductionForm.mk.sizeOf_spec LanglandsTunnell.CubicInduction.upperUnipotent3_zero LanglandsTunnell.CubicInduction.radicalP21_coe LanglandsTunnell.CubicInduction.coe_iotaGL LanglandsTunnell.CubicInduction.radicalP12_coe LanglandsTunnell.CubicInduction.radicalP12_zero LanglandsTunnell.CubicInduction.radicalP21_zero LanglandsTunnell.CubicInduction.upperUnipotent3_coe AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq"
p2m_attr_erase "simp" "LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LanglandsTunnell.RankinSelberg.mem_primeFibre HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul LanglandsTunnell.CubicInduction.coe_diagUnitGL2 LanglandsTunnell.CubicInduction.iotaTorusLocal_zero LanglandsTunnell.CubicInduction.coe_diagUnits2 LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply"

set_option autoImplicit false

open scoped TensorProduct

namespace WsC
namespace SplitAsm

open MvPolynomial

noncomputable section

abbrev admIdx : Type := {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2}
abbrev P : Type := MvPolynomial admIdx ℂ

def Y : Matrix (Fin 3) (Fin 3) P :=
  Matrix.of fun a b => if h : a ≤ b then MvPolynomial.X ⟨(a, b), h⟩ else MvPolynomial.X ⟨(b, a), le_of_not_ge h⟩
def K (i j : Fin 3) : Matrix (Fin 3) (Fin 3) P := Matrix.single i j 1 - Matrix.single j i 1
def D (i j : Fin 3) : Derivation ℂ P P := MvPolynomial.mkDerivation ℂ fun v => (K i j * Y - Y * K i j) v.1.1 v.1.2

variable {W : Type*} [AddCommGroup W] [Module ℂ W] (ρ : Fin 3 → Fin 3 → (W →ₗ[ℂ] W))

def θ (i j : Fin 3) : P ⊗[ℂ] W →ₗ[ℂ] P ⊗[ℂ] W :=
  TensorProduct.map LinearMap.id (ρ i j) - TensorProduct.map (D i j).toLinearMap LinearMap.id

def Ωd : P ⊗[ℂ] W →ₗ[ℂ] P ⊗[ℂ] W := θ ρ 0 1 ∘ₗ θ ρ 0 1 + θ ρ 0 2 ∘ₗ θ ρ 0 2 + θ ρ 1 2 ∘ₗ θ ρ 1 2

def S (N : ℕ) : Submodule ℂ (P ⊗[ℂ] W) :=
  Submodule.span ℂ {x | ∃ (q : P) (w : W), q.IsHomogeneous N ∧ x = q ⊗ₜ[ℂ] w}

def span₁ (n : ℕ) : Submodule ℂ (P ⊗[ℂ] W) :=
  Submodule.span ℂ {x : P ⊗[ℂ] W | ∃ (a d : ℕ) (s q : P) (w : W),
    s.IsHomogeneous a ∧ (∀ i j : Fin 3, D i j s = 0) ∧ q.IsHomogeneous d ∧ d ≤ 2 ∧ a + d = n + 1 ∧
      x = (s * q) ⊗ₜ[ℂ] w}

def gen₂ (q : P) (w : W) : P ⊗[ℂ] W :=
  ((D 0 1 (D 0 1 q)) ⊗ₜ[ℂ] w - ((D 0 1 q) ⊗ₜ[ℂ] (ρ 0 1 w) + (D 0 1 q) ⊗ₜ[ℂ] (ρ 0 1 w))) +
    ((D 0 2 (D 0 2 q)) ⊗ₜ[ℂ] w - ((D 0 2 q) ⊗ₜ[ℂ] (ρ 0 2 w) + (D 0 2 q) ⊗ₜ[ℂ] (ρ 0 2 w))) +
    ((D 1 2 (D 1 2 q)) ⊗ₜ[ℂ] w - ((D 1 2 q) ⊗ₜ[ℂ] (ρ 1 2 w) + (D 1 2 q) ⊗ₜ[ℂ] (ρ 1 2 w)))

def span₂ (n : ℕ) : Submodule ℂ (P ⊗[ℂ] W) :=
  Submodule.span ℂ {x : P ⊗[ℂ] W | ∃ (q : P) (w : W), q.IsHomogeneous (n + 1) ∧ x = gen₂ ρ q w}

theorem θ_tmul (i j : Fin 3) (q : P) (w : W) :
    θ ρ i j (q ⊗ₜ[ℂ] w) = q ⊗ₜ[ℂ] (ρ i j w) - (D i j q) ⊗ₜ[ℂ] w := by
  simp only [θ, LinearMap.sub_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  rfl

theorem θθ_tmul (i j : Fin 3) (q : P) (w : W) :
    θ ρ i j (θ ρ i j (q ⊗ₜ[ℂ] w)) =
      q ⊗ₜ[ℂ] (ρ i j (ρ i j w)) - ((D i j q) ⊗ₜ[ℂ] (ρ i j w) + (D i j q) ⊗ₜ[ℂ] (ρ i j w)) +
        (D i j (D i j q)) ⊗ₜ[ℂ] w := by
  rw [θ_tmul, map_sub, θ_tmul, θ_tmul]
  abel

theorem Ωd_add_two_tmul (hcas : ∀ x : W, ρ 0 1 (ρ 0 1 x) + ρ 0 2 (ρ 0 2 x) + ρ 1 2 (ρ 1 2 x) = -((2 : ℂ) • x))
    (q : P) (w : W) : Ωd ρ (q ⊗ₜ[ℂ] w) + (2 : ℂ) • (q ⊗ₜ[ℂ] w) = gen₂ ρ q w := by
  have hsum : q ⊗ₜ[ℂ] (ρ 0 1 (ρ 0 1 w)) + q ⊗ₜ[ℂ] (ρ 0 2 (ρ 0 2 w)) + q ⊗ₜ[ℂ] (ρ 1 2 (ρ 1 2 w)) +
      (2 : ℂ) • (q ⊗ₜ[ℂ] w) = 0 := by
    rw [← TensorProduct.tmul_add, ← TensorProduct.tmul_add, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_add,
      hcas, neg_add_cancel, TensorProduct.tmul_zero]
  simp only [Ωd, LinearMap.add_apply, LinearMap.comp_apply, θθ_tmul, gen₂]
  rw [← sub_eq_zero]
  rw [← hsum]
  abel

theorem Ωd_add_two_mem_span₂
    (hcas : ∀ x : W, ρ 0 1 (ρ 0 1 x) + ρ 0 2 (ρ 0 2 x) + ρ 1 2 (ρ 1 2 x) = -((2 : ℂ) • x))
    (n : ℕ) {y : P ⊗[ℂ] W} (hy : y ∈ S (n + 1)) : Ωd ρ y + (2 : ℂ) • y ∈ span₂ ρ n := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, w, hq, rfl⟩ := hx
    rw [Ωd_add_two_tmul ρ hcas]
    exact Submodule.subset_span ⟨q, w, hq, rfl⟩
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add, smul_add]
    have := add_mem ha hb
    convert this using 1
    abel
  | smul z a _ ha =>
    rw [map_smul, smul_comm, ← smul_add]
    exact Submodule.smul_mem _ z ha

theorem tmul_mem_sup
    (hcas : ∀ x : W, ρ 0 1 (ρ 0 1 x) + ρ 0 2 (ρ 0 2 x) + ρ 1 2 (ρ 1 2 x) = -((2 : ℂ) • x))
    (n : ℕ) (p : P) (hp : p.IsHomogeneous (n + 1)) (v : W)
    (hE : ∃ k ∈ S (W := W) (n + 1), ∃ y ∈ S (W := W) (n + 1),
      p ⊗ₜ[ℂ] v = k + (Ωd ρ y + (2 : ℂ) • y) ∧ Ωd ρ k + (2 : ℂ) • k = 0)
    (hK : ∀ k ∈ S (W := W) (n + 1), Ωd ρ k + (2 : ℂ) • k = 0 → k ∈ span₁ (W := W) n) :
    p ⊗ₜ[ℂ] v ∈ span₁ (W := W) n ⊔ span₂ ρ n := by
  obtain ⟨k, hk, y, hy, hsplit, hker⟩ := hE
  rw [hsplit]
  exact add_mem (Submodule.mem_sup_left (hK k hk hker)) (Submodule.mem_sup_right (Ωd_add_two_mem_span₂ ρ hcas n hy))

end

end WsC.SplitAsm

open scoped TensorProduct in
theorem solution
    (W : Type*) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Fin 3 → Fin 3 → (W →ₗ[ℂ] W))
    (hanti : ∀ (i j : Fin 3) (x : W), ρ j i x = -ρ i j x)
    (hrel₁ : ∀ x : W, ρ 0 1 (ρ 0 2 x) - ρ 0 2 (ρ 0 1 x) = -ρ 1 2 x)
    (hrel₂ : ∀ x : W, ρ 0 1 (ρ 1 2 x) - ρ 1 2 (ρ 0 1 x) = ρ 0 2 x)
    (hrel₃ : ∀ x : W, ρ 0 2 (ρ 1 2 x) - ρ 1 2 (ρ 0 2 x) = -ρ 0 1 x)
    (hcas : ∀ x : W, ρ 0 1 (ρ 0 1 x) + ρ 0 2 (ρ 0 2 x) + ρ 1 2 (ρ 1 2 x) = -((2 : ℂ) • x))
    (B : W → W → ℂ)
    (hlin : ∀ (z : ℂ) (w₁ w₂ w' : W), B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w w' : W, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w : W, w ≠ 0 → 0 < (B w w).re)
    (hskew : ∀ (i j : Fin 3) (x y : W), B (ρ i j x) y = -B x (ρ i j y))
    (n : ℕ) (p : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) (hp : p.IsHomogeneous (n + 1)) (v : W) :
    let Y : Matrix (Fin 3) (Fin 3) (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) :=
      Matrix.of fun a b => if h : a ≤ b then MvPolynomial.X ⟨(a, b), h⟩ else MvPolynomial.X ⟨(b, a), le_of_not_ge h⟩
    let K : Fin 3 → Fin 3 → Matrix (Fin 3) (Fin 3) (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) :=
      fun i j => Matrix.single i j 1 - Matrix.single j i 1
    let D : Fin 3 → Fin 3 →
        Derivation ℂ (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ)
          (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) :=
      fun i j => MvPolynomial.mkDerivation ℂ fun v => (K i j * Y - Y * K i j) v.1.1 v.1.2
    p ⊗ₜ[ℂ] v ∈
      Submodule.span ℂ {x : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W |
          ∃ (a d : ℕ) (s q : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) (w : W),
            s.IsHomogeneous a ∧ (∀ i j : Fin 3, D i j s = 0) ∧ q.IsHomogeneous d ∧ d ≤ 2 ∧ a + d = n + 1 ∧
              x = (s * q) ⊗ₜ[ℂ] w} ⊔
      Submodule.span ℂ {x : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ ⊗[ℂ] W |
          ∃ (q : MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) (w : W), q.IsHomogeneous (n + 1) ∧
            x = ((D 0 1 (D 0 1 q)) ⊗ₜ[ℂ] w - ((D 0 1 q) ⊗ₜ[ℂ] (ρ 0 1 w) + (D 0 1 q) ⊗ₜ[ℂ] (ρ 0 1 w))) +
                ((D 0 2 (D 0 2 q)) ⊗ₜ[ℂ] w - ((D 0 2 q) ⊗ₜ[ℂ] (ρ 0 2 w) + (D 0 2 q) ⊗ₜ[ℂ] (ρ 0 2 w))) +
                ((D 1 2 (D 1 2 q)) ⊗ₜ[ℂ] w - ((D 1 2 q) ⊗ₜ[ℂ] (ρ 1 2 w) + (D 1 2 q) ⊗ₜ[ℂ] (ρ 1 2 w)))} := by
  intro Y K D

  obtain ⟨hfin, hθS, ⟨B', hlin', hsymm', hpos', hskew'⟩, hgen⟩ :=
    LanglandsTunnell.CubicInduction.exists_posDef_hermitian_skew_diagAction_tensor_homogeneous_and_casimir_tmul
      W ρ hanti hcas B hlin hsymm hpos hskew (n + 1)

  change p ⊗ₜ[ℂ] v ∈ WsC.SplitAsm.span₁ (W := W) n ⊔ WsC.SplitAsm.span₂ ρ n
  have hpS : p ⊗ₜ[ℂ] v ∈ WsC.SplitAsm.S (W := W) (n + 1) := Submodule.subset_span ⟨p, v, hp, rfl⟩
  haveI : Module.Finite ℂ (WsC.SplitAsm.S (W := W) (n + 1)) := hfin

  have hθS' : ∀ i j : Fin 3, ∀ w ∈ WsC.SplitAsm.S (W := W) (n + 1),
      WsC.SplitAsm.θ ρ i j w ∈ WsC.SplitAsm.S (W := W) (n + 1) := fun i j => hθS i j
  have hskew'' : ∀ i j : Fin 3, ∀ w ∈ WsC.SplitAsm.S (W := W) (n + 1), ∀ w' ∈ WsC.SplitAsm.S (W := W) (n + 1),
      B' (WsC.SplitAsm.θ ρ i j w) w' = -B' w (WsC.SplitAsm.θ ρ i j w') := fun i j => hskew' i j

  obtain ⟨k, hk, x, hx, hkeig, hsplit⟩ :=
    LinearAlgebra.exists_eigenvector_add_image_sum_sq_of_skew_of_posDef_hermitian (WsC.SplitAsm.P ⊗[ℂ] W)
      (WsC.SplitAsm.S (W := W) (n + 1)) B' hlin' hsymm' hpos' (Fin 3)
      ![WsC.SplitAsm.θ ρ 0 1, WsC.SplitAsm.θ ρ 0 2, WsC.SplitAsm.θ ρ 1 2]
      (by
        intro i; fin_cases i
        · have h__af := hθS' 0 1
          simp only [Matrix.cons_val_zero] at h__af ⊢
          exact h__af
        · have h__af := hθS' 0 2
          simp only [Matrix.cons_val_one, Matrix.head_cons] at h__af ⊢
          exact h__af
        · have h__af := hθS' 1 2
          simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h__af ⊢
          exact h__af)
      (by
        intro i; fin_cases i
        · have h__af := hskew'' 0 1
          simp only [Matrix.cons_val_zero] at h__af ⊢
          exact h__af
        · have h__af := hskew'' 0 2
          simp only [Matrix.cons_val_one, Matrix.head_cons] at h__af ⊢
          exact h__af
        · have h__af := hskew'' 1 2
          simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h__af ⊢
          exact h__af)
      (-2) (p ⊗ₜ[ℂ] v) hpS
  have hΩ : (∑ i : Fin 3, (![WsC.SplitAsm.θ ρ 0 1, WsC.SplitAsm.θ ρ 0 2, WsC.SplitAsm.θ ρ 1 2] i) *
      (![WsC.SplitAsm.θ ρ 0 1, WsC.SplitAsm.θ ρ 0 2, WsC.SplitAsm.θ ρ 1 2] i)) = WsC.SplitAsm.Ωd ρ := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, WsC.SplitAsm.Ωd,
      Module.End.mul_eq_comp]
    rfl
  rw [hΩ] at hkeig hsplit
  refine WsC.SplitAsm.tmul_mem_sup ρ hcas n p hp v ⟨k, hk, x, hx, ?_, ?_⟩ ?_
  · rw [hsplit, neg_smul, sub_neg_eq_add]
  · rw [hkeig, neg_smul, neg_add_cancel]
  · intro k' hk' hker'
    exact LanglandsTunnell.CubicInduction.mem_span_invariant_mul_of_diagCasimir_add_two_eq_zero W ρ hanti hrel₁ hrel₂ hrel₃ hcas
      B hlin hsymm hpos hskew n k' hk' hker'

end S_LanglandsTunnell_CubicInduction_tmul_mem_span_invariant_mul_sup_span_diagCasimir_of_isHomogeneous
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_tmul_mem_span_invariant_mul_sup_span_diagCasimir_of_isHomogeneous (solution)
