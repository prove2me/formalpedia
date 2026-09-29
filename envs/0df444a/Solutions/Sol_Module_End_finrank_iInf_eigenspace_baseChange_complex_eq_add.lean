-- Prove2me | solution 1 for Module.End.finrank_iInf_eigenspace_baseChange_complex_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/6ff4611a-815a-554f-b7d8-5e20ec48c546

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_End_finrank_iInf_eigenspace_baseChange_complex_eq_add

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open TensorProduct

namespace ComplexifiedLattice

universe u x

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable (Λ : Submodule ℤ V) {n : ℕ} (b : Module.Basis (Fin n) ℤ Λ)

def w : (Fin n → ℂ) →ₗ[ℂ] V :=
  Fintype.linearCombination ℂ (fun i => ((b i : Λ) : V))

theorem w_apply (z : Fin n → ℂ) : w Λ b z = ∑ i, z i • ((b i : Λ) : V) := rfl

def P : ℂ ⊗[ℤ] Λ →ₗ[ℂ] V :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (Λ.subtype : Λ →ₗ[ℤ] V))

@[scoped simp] theorem P_tmul (z : ℂ) (l : Λ) : P Λ (z ⊗ₜ l) = z • (l : V) := by
  simp [P]

def conjZ : ℂ →ₗ[ℤ] ℂ := (starRingEnd ℂ).toAddMonoidHom.toIntLinearMap

@[scoped simp] theorem conjZ_apply (z : ℂ) : conjZ z = starRingEnd ℂ z := rfl

def Q : ℂ ⊗[ℤ] Λ →ₗ[ℤ] V :=
  ((P Λ).restrictScalars ℤ) ∘ₗ (LinearMap.rTensor Λ conjZ)

@[scoped simp] theorem Q_tmul (z : ℂ) (l : Λ) : Q Λ (z ⊗ₜ l) = (starRingEnd ℂ z) • (l : V) := by
  change P Λ (LinearMap.rTensor Λ conjZ (z ⊗ₜ l)) = _
  rw [LinearMap.rTensor_tmul, conjZ_apply, P_tmul]

theorem Q_smul (z : ℂ) (x : ℂ ⊗[ℤ] Λ) : Q Λ (z • x) = (starRingEnd ℂ z) • Q Λ x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul y l => rw [smul_tmul', Q_tmul, Q_tmul, smul_eq_mul, map_mul, mul_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

noncomputable def B : Module.Basis (Fin n) ℂ (ℂ ⊗[ℤ] Λ) := b.baseChange ℂ

theorem B_apply (i : Fin n) : B Λ b i = (1 : ℂ) ⊗ₜ (b i) := Module.Basis.baseChange_apply _ _ _

theorem P_coord (z : Fin n → ℂ) : P Λ (∑ i, z i • B Λ b i) = w Λ b z := by
  rw [map_sum, w_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, B_apply, P_tmul, one_smul]

theorem Q_coord (z : Fin n → ℂ) :
    Q Λ (∑ i, z i • B Λ b i) = w Λ b (fun i => starRingEnd ℂ (z i)) := by
  rw [map_sum, w_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Q_smul, B_apply, Q_tmul, map_one, one_smul]

theorem exists_coord (x : ℂ ⊗[ℤ] Λ) : ∃ z : Fin n → ℂ, x = ∑ i, z i • B Λ b i :=
  ⟨fun i => (B Λ b).repr x i, ((B Λ b).sum_repr x).symm⟩

variable {Λ b}
variable (hli : ∀ r : Fin n → ℝ, ∑ i, ((r i : ℂ)) • ((b i : Λ) : V) = 0 → r = 0)
variable (hsp : ∀ v : V, ∃ r : Fin n → ℝ, ∑ i, ((r i : ℂ)) • ((b i : Λ) : V) = v)

include hli in

theorem eq_zero_of_P_eq_zero_of_Q_eq_zero (x : ℂ ⊗[ℤ] Λ) (hP : P Λ x = 0) (hQ : Q Λ x = 0) :
    x = 0 := by
  obtain ⟨z, rfl⟩ := exists_coord Λ b x
  rw [P_coord] at hP
  rw [Q_coord] at hQ

  have hre : (fun i => 2 * (z i).re) = 0 := by
    apply hli
    have : w Λ b (z + fun i => starRingEnd ℂ (z i)) = 0 := by rw [map_add, hP, hQ, add_zero]
    rw [w_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [Pi.add_apply, Complex.add_conj]

  have him : (fun i => 2 * (z i).im) = 0 := by
    apply hli
    have h1 : w Λ b (z - fun i => starRingEnd ℂ (z i)) = 0 := by rw [map_sub, hP, hQ, sub_zero]
    have h2 : w Λ b ((-Complex.I) • (z - fun i => starRingEnd ℂ (z i))) = 0 := by
      rw [map_smul, h1, smul_zero]
    rw [w_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [Pi.smul_apply, Pi.sub_apply, Complex.sub_conj, smul_eq_mul]; push_cast
    ring_nf
    rw [Complex.I_sq]; ring
  have hz : z = 0 := by
    funext i
    have h1 := congrFun hre i
    have h2 := congrFun him i
    simp only [Pi.zero_apply, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at h1 h2
    exact Complex.ext h1 h2
  rw [hz]
  simp

include hsp in

theorem exists_P_eq_Q_eq (v₁ v₂ : V) : ∃ x : ℂ ⊗[ℤ] Λ, P Λ x = v₁ ∧ Q Λ x = v₂ := by
  obtain ⟨t, ht⟩ := hsp ((2 : ℂ)⁻¹ • (v₁ + v₂))
  obtain ⟨t', ht'⟩ := hsp ((-(Complex.I) / 2) • (v₁ - v₂))
  have hwt : w Λ b (fun i => (t i : ℂ)) = (2 : ℂ)⁻¹ • (v₁ + v₂) := by rw [w_apply]; exact ht
  have hwt' : w Λ b (fun i => (t' i : ℂ)) = (-(Complex.I) / 2) • (v₁ - v₂) := by
    rw [w_apply]; exact ht'
  let z : Fin n → ℂ := fun i => (t i : ℂ) + Complex.I * (t' i : ℂ)
  refine ⟨∑ i, z i • B Λ b i, ?_, ?_⟩
  · rw [P_coord]
    have hz : z = (fun i => (t i : ℂ)) + Complex.I • (fun i => (t' i : ℂ)) := by
      funext i; simp [z]
    rw [hz, map_add, map_smul, hwt, hwt', smul_smul]
    have h : Complex.I * (-Complex.I / 2) = (2 : ℂ)⁻¹ := by
      rw [mul_div_assoc', ← neg_mul_eq_mul_neg, Complex.I_mul_I, neg_neg, one_div]
    rw [h, ← smul_add]
    rw [show v₁ + v₂ + (v₁ - v₂) = (2 : ℂ) • v₁ by rw [two_smul]; abel, smul_smul]
    norm_num
  · rw [Q_coord]
    have hz : (fun i => starRingEnd ℂ (z i)) =
        (fun i => (t i : ℂ)) + (-Complex.I) • (fun i => (t' i : ℂ)) := by
      funext i; simp [z, Complex.conj_ofReal]
    rw [hz, map_add, map_smul, hwt, hwt', smul_smul]
    have h : -Complex.I * (-Complex.I / 2) = -(2 : ℂ)⁻¹ := by
      rw [mul_div_assoc', neg_mul_neg, Complex.I_mul_I, neg_div, one_div]
    rw [h, neg_smul, ← sub_eq_add_neg, ← smul_sub]
    rw [show v₁ + v₂ - (v₁ - v₂) = (2 : ℂ) • v₂ by rw [two_smul]; abel, smul_smul]
    norm_num

variable {ι : Type x} (D : ι → Module.End ℂ V) (A : ι → Module.End ℤ Λ)
  (hA : ∀ (i : ι) (x : Λ), ((A i x : Λ) : V) = D i (x : V)) (c : ι → ℂ)

include hA in
theorem P_baseChange (i : ι) (x : ℂ ⊗[ℤ] Λ) : P Λ ((A i).baseChange ℂ x) = D i (P Λ x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul z l => rw [LinearMap.baseChange_tmul, P_tmul, P_tmul, hA, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

include hA in
theorem Q_baseChange (i : ι) (x : ℂ ⊗[ℤ] Λ) : Q Λ ((A i).baseChange ℂ x) = D i (Q Λ x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul z l => rw [LinearMap.baseChange_tmul, Q_tmul, Q_tmul, hA, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

def EX : Submodule ℂ (ℂ ⊗[ℤ] Λ) := ⨅ i, Module.End.eigenspace ((A i).baseChange ℂ) (c i)

def E₁ : Submodule ℂ V := ⨅ i, Module.End.eigenspace (D i) (c i)

def E₂ : Submodule ℂ V := ⨅ i, Module.End.eigenspace (D i) (starRingEnd ℂ (c i))

theorem mem_EX {x : ℂ ⊗[ℤ] Λ} : x ∈ EX A c ↔ ∀ i, (A i).baseChange ℂ x = c i • x := by
  simp [EX, Submodule.mem_iInf]

theorem mem_E₁ {v : V} : v ∈ E₁ D c ↔ ∀ i, D i v = c i • v := by
  simp [E₁, Submodule.mem_iInf]

theorem mem_E₂ {v : V} : v ∈ E₂ D c ↔ ∀ i, D i v = (starRingEnd ℂ (c i)) • v := by
  simp [E₂, Submodule.mem_iInf]

include hA in
theorem P_mem {x : ℂ ⊗[ℤ] Λ} (hx : x ∈ EX A c) : P Λ x ∈ E₁ D c := by
  rw [mem_E₁]; intro i
  rw [← P_baseChange (hA := hA), (mem_EX A c).mp hx i, map_smul]

include hA in
theorem Q_mem {x : ℂ ⊗[ℤ] Λ} (hx : x ∈ EX A c) : Q Λ x ∈ E₂ D c := by
  rw [mem_E₂]; intro i
  rw [← Q_baseChange (hA := hA), (mem_EX A c).mp hx i, Q_smul]

include hli hA in

theorem mem_EX_of (x : ℂ ⊗[ℤ] Λ) (h₁ : P Λ x ∈ E₁ D c) (h₂ : Q Λ x ∈ E₂ D c) :
    x ∈ EX A c := by
  rw [mem_EX]; intro i
  rw [← sub_eq_zero]
  apply eq_zero_of_P_eq_zero_of_Q_eq_zero hli
  · rw [map_sub, map_smul, P_baseChange (hA := hA), (mem_E₁ D c).mp h₁ i, sub_self]
  · rw [map_sub, Q_smul, Q_baseChange (hA := hA), (mem_E₂ D c).mp h₂ i, sub_self]

def P₁ : EX A c →ₗ[ℂ] E₁ D c :=
  ((P Λ).domRestrict (EX A c)).codRestrict (E₁ D c) (fun x => P_mem D A hA c x.2)

@[scoped simp] theorem P₁_apply (x : EX A c) : ((P₁ D A hA c x : E₁ D c) : V) = P Λ (x : ℂ ⊗[ℤ] Λ) :=
  rfl

include hli hsp in
theorem P₁_surjective : Function.Surjective (P₁ D A hA c) := by
  intro v
  obtain ⟨x, hx₁, hx₂⟩ := exists_P_eq_Q_eq hsp (v : V) 0
  have hx : x ∈ EX A c :=
    mem_EX_of hli D A hA c x (hx₁ ▸ v.2) (hx₂ ▸ Submodule.zero_mem _)
  exact ⟨⟨x, hx⟩, Subtype.ext (by rw [P₁_apply, hx₁])⟩

include hli hsp in

theorem finrank_ker_P₁ :
    Module.finrank ℂ (LinearMap.ker (P₁ D A hA c)) = Module.finrank ℂ (E₂ D c) := by
  classical

  have hsurj : ∀ v : E₂ D c, ∃ x : LinearMap.ker (P₁ D A hA c),
      Q Λ ((x : EX A c) : ℂ ⊗[ℤ] Λ) = (v : V) := by
    intro v
    obtain ⟨x, hx₁, hx₂⟩ := exists_P_eq_Q_eq hsp 0 (v : V)
    have hx : x ∈ EX A c :=
      mem_EX_of hli D A hA c x (hx₁ ▸ Submodule.zero_mem _) (hx₂ ▸ v.2)
    refine ⟨⟨⟨x, hx⟩, ?_⟩, hx₂⟩
    rw [LinearMap.mem_ker]
    exact Subtype.ext (by rw [P₁_apply]; exact hx₁)
  let j : LinearMap.ker (P₁ D A hA c) ≃+ E₂ D c :=
    { toFun := fun x => ⟨Q Λ ((x : EX A c) : ℂ ⊗[ℤ] Λ), Q_mem D A hA c x.1.2⟩
      invFun := fun v => (hsurj v).choose
      left_inv := by
        intro x
        have h := (hsurj ⟨Q Λ ((x : EX A c) : ℂ ⊗[ℤ] Λ), Q_mem D A hA c x.1.2⟩).choose_spec

        apply Subtype.ext; apply Subtype.ext
        rw [← sub_eq_zero]
        apply eq_zero_of_P_eq_zero_of_Q_eq_zero hli
        · have h1 : P Λ (((hsurj ⟨Q Λ ((x : EX A c) : ℂ ⊗[ℤ] Λ),
              Q_mem D A hA c x.1.2⟩).choose : EX A c) : ℂ ⊗[ℤ] Λ) = 0 := by
            have := (hsurj ⟨Q Λ ((x : EX A c) : ℂ ⊗[ℤ] Λ), Q_mem D A hA c x.1.2⟩).choose.2
            rw [LinearMap.mem_ker] at this
            exact congrArg (fun v : E₁ D c => (v : V)) this
          have h2 : P Λ ((x : EX A c) : ℂ ⊗[ℤ] Λ) = 0 := by
            have := x.2
            rw [LinearMap.mem_ker] at this
            exact congrArg (fun v : E₁ D c => (v : V)) this
          rw [map_sub, h1, h2, sub_zero]
        · rw [map_sub, sub_eq_zero]
          exact h
      right_inv := by
        intro v
        exact Subtype.ext (hsurj v).choose_spec
      map_add' := by
        intro x y
        apply Subtype.ext
        simp only [Submodule.coe_add, map_add] }
  have hc : ∀ (r : ℂ) (m : LinearMap.ker (P₁ D A hA c)), j (r • m) = (starRingEnd ℂ r) • j m := by
    intro r m
    apply Subtype.ext
    show Q Λ (((r • m : LinearMap.ker (P₁ D A hA c)) : EX A c) : ℂ ⊗[ℤ] Λ) =
      starRingEnd ℂ r • Q Λ ((m : EX A c) : ℂ ⊗[ℤ] Λ)
    rw [Submodule.coe_smul, Submodule.coe_smul, Q_smul]
  have hrank := rank_eq_of_equiv_equiv (starRingEnd ℂ) j
    (Function.Involutive.bijective Complex.conj_conj) hc
  show Cardinal.toNat _ = Cardinal.toNat _
  rw [hrank]

include hli hsp hA in

theorem finrank_EX :
    Module.finrank ℂ (EX A c) = Module.finrank ℂ (E₁ D c) + Module.finrank ℂ (E₂ D c) := by
  haveI : Module.Finite ℂ (ℂ ⊗[ℤ] Λ) := Module.Finite.of_basis (B Λ b)
  have h := LinearMap.finrank_range_add_finrank_ker (P₁ D A hA c)
  rw [LinearMap.range_eq_top.mpr (P₁_surjective hli hsp D A hA c), finrank_top,
    finrank_ker_P₁ hli hsp D A hA c] at h
  exact h.symm

end ComplexifiedLattice
p2m_reactivate "P2MW.S_Module_End_finrank_iInf_eigenspace_baseChange_complex_eq_add.ComplexifiedLattice"

theorem solution
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (Λ : Submodule ℤ V) {n : ℕ} (b : Module.Basis (Fin n) ℤ Λ)
    (hli : ∀ r : Fin n → ℝ, ∑ i, ((r i : ℂ)) • ((b i : Λ) : V) = 0 → r = 0)
    (hsp : ∀ v : V, ∃ r : Fin n → ℝ, ∑ i, ((r i : ℂ)) • ((b i : Λ) : V) = v)
    {ι : Type*} (D : ι → Module.End ℂ V) (A : ι → Module.End ℤ Λ)
    (hA : ∀ (i : ι) (x : Λ), ((A i x : Λ) : V) = D i (x : V)) (c : ι → ℂ) :
    Module.finrank ℂ ↥(⨅ i, Module.End.eigenspace ((A i).baseChange ℂ) (c i)) =
      Module.finrank ℂ ↥(⨅ i, Module.End.eigenspace (D i) (c i)) +
        Module.finrank ℂ ↥(⨅ i, Module.End.eigenspace (D i) (starRingEnd ℂ (c i))) :=
  ComplexifiedLattice.finrank_EX hli hsp D A hA c

end
end S_Module_End_finrank_iInf_eigenspace_baseChange_complex_eq_add
end P2MW
export P2MW.S_Module_End_finrank_iInf_eigenspace_baseChange_complex_eq_add (solution)
