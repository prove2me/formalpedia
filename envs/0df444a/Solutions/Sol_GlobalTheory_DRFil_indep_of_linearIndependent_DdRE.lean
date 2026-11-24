-- Prove2me | solution 1 for GlobalTheory.DRFil.indep_of_linearIndependent_DdRE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:37:22.04283+00:00
-- url     : https://prove2.me/submissions/a61628f8-7327-4f71-82e3-038f8dbe333b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearIndependentOfInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndepOfLinearIndependentDdRE
import Theorems.Thm_GlobalTheory_DRFil_indep_of_invariant_isField
import Theorems.Thm_GlobalTheory_DRFil_exists_idem_mul_eq
import Theorems.Thm_GlobalTheory_DRFil_actVdR_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DRFil.actVdR_tmul


section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.DRFil
namespace GlobalTheory.DRFil
private theorem sm_tmul_tmul {Qp LL V F : Type} [Field Qp] [CommRing F] [Algebra Qp F] [Field LL]
    [Algebra Qp LL] [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (a : LL) (f : F) (v : V) (f' : F) :
    sm Qp F LL V (a ⊗ₜ[Qp] f) (v ⊗ₜ[Qp] f') = (a • v) ⊗ₜ[Qp] (f * f') := by
  simp [sm, bil]
private theorem sm_mul_inertia_eigenvalues {Qp LL V F : Type} [Field Qp] [CommRing F] [Algebra Qp F] [Field LL]
    [Algebra Qp LL] [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (x x' : LL ⊗[Qp] F) (y : V ⊗[Qp] F) :
    sm Qp F LL V (x * x') y = sm Qp F LL V x (sm Qp F LL V x' y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [add_mul, map_add, LinearMap.add_apply, h₁, h₂]
  | tmul a f =>
    induction x' using TensorProduct.induction_on with
    | zero => simp
    | add x₁ x₂ h₁ h₂ => simp only [mul_add, map_add, LinearMap.add_apply, h₁, h₂]
    | tmul a' f' =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
      | tmul v f'' =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, sm_tmul_tmul, sm_tmul_tmul, sm_tmul_tmul, mul_smul,
          mul_assoc]
end GlobalTheory.DRFil
end

set_option autoImplicit false
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.DRFil
open GlobalTheory GlobalTheory.DRFil
namespace GlobalTheory.DRFil
theorem _root_.solution {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B F : Type} [CommRing B]
    [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp F] [Algebra K₀ F]
    [Algebra K F] [IsScalarTower Qp K F] [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F) {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL]
    [FiniteDimensional Qp K] [CharZero Qp] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V]
    [IsScalarTower Qp LL V] [FiniteDimensional LL V] (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL)
    {ι : Type} [Fintype ι] (d : ι → V ⊗[Qp] F) (hF : IsField F) (hd : ∀ i, d i ∈ DdRE PD ρ τ)
    (hind : LinearIndependent LL d) (r : ι → LL ⊗[Qp] F)
    (hr : ∑ i, sm Qp F LL V (r i) (d i) = 0) : ∀ i, idem F τ * r i = 0 := by
  classical

  have hinvd : ∀ i g, actVdR PD ρ g (d i) = d i := by
    intro i g
    have h := hd i
    unfold DdRE DdR at h
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h
    exact h.1 g
  have hτd : ∀ i (c : K), mulVdR (K := K) (BdR := F) (V := V) (LL := LL) c (d i) = τ c • d i := by
    intro i c
    have h := hd i
    unfold DdRE DdR at h
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h
    exact h.2 c
  have hmul : ∀ (c : K) (y : V ⊗[Qp] F), sm Qp F LL V ((1 : LL) ⊗ₜ[Qp] algebraMap K F c) y =
      mulVdR (K := K) (BdR := F) (V := V) (LL := LL) c y := by
    intro c y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
    | tmul v f => simp [sm_tmul_tmul, mulVdR]
  have hleft : ∀ (a : LL) (f : F) (y : V ⊗[Qp] F),
      sm Qp F LL V (a ⊗ₜ[Qp] f) y = a • sm Qp F LL V ((1 : LL) ⊗ₜ[Qp] f) y := by
    intro a f y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, smul_add]
    | tmul v f' => rw [sm_tmul_tmul, sm_tmul_tmul, one_smul, TensorProduct.smul_tmul']

  have hfix : ∀ i, sm Qp F LL V (idem F τ) (d i) = d i := by
    intro i
    unfold idem
    generalize_proofs
    rename_i hex
    obtain ⟨h1, -⟩ := hex.choose_spec
    have key : ∀ e' : LL ⊗[Qp] K,
        sm Qp F LL V (Algebra.TensorProduct.map (AlgHom.id Qp LL) (IsScalarTower.toAlgHom Qp K F) e')
          (d i) = Algebra.TensorProduct.lift (AlgHom.id Qp LL) τ (fun _ _ => Commute.all _ _) e' • d i := by
      intro e'
      induction e' using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, add_smul]
      | tmul a k =>
        simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply,
          IsScalarTower.toAlgHom_apply]
        rw [hleft, hmul, hτd, mul_smul]
    rw [key]
    have h1' : Algebra.TensorProduct.lift (AlgHom.id Qp LL) τ (fun _ _ => Commute.all _ _) hex.choose = 1 :=
      h1
    rw [h1', one_smul]
  have hidem : ∀ i (X : LL ⊗[Qp] F), sm Qp F LL V (idem F τ * X) (d i) = sm Qp F LL V X (d i) := by
    intro i X
    rw [mul_comm, sm_mul_inertia_eigenvalues, hfix]

  letI : Algebra K LL := τ.toRingHom.toAlgebra
  haveI : IsScalarTower Qp K LL := IsScalarTower.of_algebraMap_eq (fun q => (τ.commutes q).symm)
  haveI : FiniteDimensional K LL := Module.Finite.of_restrictScalars_finite Qp K LL
  obtain ⟨n, l, hgen, hlind⟩ : ∃ (n : ℕ) (l : Fin n → LL),
      (∀ a : LL, ∃ c : Fin n → K, a = ∑ j, τ (c j) * l j) ∧
        (∀ c : Fin n → K, ∑ j, τ (c j) * l j = 0 → ∀ j, c j = 0) := by
    refine ⟨_, Module.finBasis K LL, fun a => ⟨fun j => (Module.finBasis K LL).repr a j, ?_⟩,
      fun c hc => Fintype.linearIndependent_iff.mp (Module.finBasis K LL).linearIndependent c hc⟩
    conv_lhs => rw [← (Module.finBasis K LL).sum_repr a]
    rfl
  choose b hb using fun i => exists_idem_mul_eq τ l hgen (r i)
  have hrel : ∑ i, sm Qp F LL V (∑ j, l j ⊗ₜ[Qp] b i j) (d i) = 0 := by
    rw [← hr]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hidem i, ← hb i, hidem i]

  let w : ι × Fin n → F ⊗[Qp] V := fun p => TensorProduct.comm Qp V F (l p.2 • d p.1)
  let ρ' : G → (F ⊗[Qp] V →+ F ⊗[Qp] V) := fun g => AddMonoidHom.mk'
    (fun m => TensorProduct.comm Qp V F (actVdR PD ρ g ((TensorProduct.comm Qp V F).symm m)))
    (fun x y => by simp only [map_add])
  let σ' : G → (F →+* F) := fun g => (PD.actdR g).toAlgHom.toRingHom
  have hρ' : ∀ g (e : F) (m : F ⊗[Qp] V), ρ' g (e • m) = σ' g e • ρ' g m := by
    intro g e m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
    | tmul f v => simp [ρ', σ', actVdR, TensorProduct.smul_tmul', smul_eq_mul, map_mul]
  have hv' : ∀ g p, ρ' g (w p) = w p := by
    intro g p
    simp only [ρ', w, AddMonoidHom.mk'_apply, LinearEquiv.symm_apply_apply, map_smul, hinvd]
  have hL1 : ∀ (k : K) (y : V ⊗[Qp] F), algebraMap K F k • TensorProduct.comm Qp V F y =
      TensorProduct.comm Qp V F (mulVdR (K := K) (BdR := F) (V := V) (LL := LL) k y) := by
    intro k y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, smul_add, hx, hy, map_add, map_add]
    | tmul v f =>
      simp only [mulVdR, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply,
        TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  have hind' : ∀ c : ι × Fin n → F, (∀ g p, σ' g (c p) = c p) → ∑ p, c p • w p = 0 → ∀ p, c p = 0 := by
    intro c hcinv hcsum
    have hk : ∀ p, ∃ k : K, algebraMap K F k = c p := fun p => PD.invdR (c p) (fun g => hcinv g p)
    choose k hk using hk
    have hterm : ∀ p, c p • w p = TensorProduct.comm Qp V F ((τ (k p) * l p.2) • d p.1) := by
      intro p
      show c p • TensorProduct.comm Qp V F (l p.2 • d p.1) = _
      rw [← hk p, hL1, map_smul, hτd, smul_smul, mul_comm]
    have hzero : ∑ i, (∑ j, τ (k (i, j)) * l j) • d i = 0 := by
      have h2 : TensorProduct.comm Qp V F (∑ i, (∑ j, τ (k (i, j)) * l j) • d i) = 0 := by
        rw [← hcsum, Fintype.sum_prod_type]
        simp only [hterm, map_sum, Finset.sum_smul]
      exact (TensorProduct.comm Qp V F).map_eq_zero_iff.mp h2
    have hcoef := Fintype.linearIndependent_iff.mp hind (fun i => ∑ j, τ (k (i, j)) * l j) hzero
    rintro ⟨i, j⟩
    have hkij : k (i, j) = 0 := hlind (fun j => k (i, j)) (hcoef i) j
    rw [← hk (i, j), hkij, map_zero]
  have hL2 : ∀ (a : LL) (f : F) (y : V ⊗[Qp] F),
      TensorProduct.comm Qp V F (sm Qp F LL V (a ⊗ₜ[Qp] f) y) = f • TensorProduct.comm Qp V F (a • y) := by
    intro a f y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
    | tmul v f' => simp [sm_tmul_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  have hcomb : ∑ p, b p.1 p.2 • w p = 0 := by
    have h2 := congrArg (TensorProduct.comm Qp V F) hrel
    rw [map_zero] at h2
    rw [← h2, Fintype.sum_prod_type]
    simp only [w, map_sum, LinearMap.sum_apply, hL2]
  have hb0 := indep_of_invariant_isField hF σ' ρ' hρ' w hv' hind' (fun p => b p.1 p.2) hcomb
  intro i
  have hbij : ∀ j, b i j = 0 := fun j => hb0 (i, j)
  rw [hb i]
  simp [hbij]
end GlobalTheory.DRFil
