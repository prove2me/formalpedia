-- Prove2me | solution 1 for HopfAlgebra.exists_bialgHom_forall_comp_eq_of_equivariant_of_bijective_evalPoints
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/0541a865-4c08-5072-8de5-fc360f5c9e8b

import Mathlib
import Theorems.Thm_HopfAlgebra_tensorProduct_eq_zero_of_forall_lift_points_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_bialgHom_forall_comp_eq_of_equivariant_of_bijective_evalPoints

set_option autoImplicit false
open scoped TensorProduct

namespace Desc1

variable (D : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (A : Type) [CommRing A] [HopfAlgebra ↥(IntermediateField.fixedField D) A]

set_option quotPrecheck false in
local notation "F′" => ↥(IntermediateField.fixedField D)
local notation "Qb" => AlgebraicClosure ℚ
set_option quotPrecheck false in
local notation "Pt" => WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ)

noncomputable def L : Qb ⊗[F′] A →ₐ[Qb] (Pt → Qb) :=
  Algebra.TensorProduct.lift
    (Algebra.ofId Qb (Pt → Qb))
    (Pi.algHom F′ _ fun ν : Pt => (WithConv.ofConv ν : A →ₐ[F′] Qb))
    (fun _ _ => Commute.all _ _)

theorem L_tmul (c : Qb) (a : A) (ν : Pt) : L D A (c ⊗ₜ a) ν = c * (WithConv.ofConv ν) a := by
  simp [L, Algebra.TensorProduct.lift_tmul]

noncomputable def galF (σ : Qb ≃ₐ[ℚ] Qb) (hσ : σ ∈ D) : Qb ≃ₐ[F′] Qb :=
  { σ with
    commutes' := fun r => (IntermediateField.mem_fixedField_iff _ _).mp r.2 σ hσ }

@[scoped simp] theorem galF_apply (σ : Qb ≃ₐ[ℚ] Qb) (hσ : σ ∈ D) (x : Qb) : galF D σ hσ x = σ x := rfl

noncomputable def galPt (σ : Qb ≃ₐ[ℚ] Qb) (hσ : σ ∈ D) (ν : Pt) : Pt :=
  WithConv.toConv (((galF D σ hσ : Qb ≃ₐ[F′] Qb) : Qb →ₐ[F′] Qb).comp (WithConv.ofConv ν))

@[scoped simp] theorem galPt_apply (σ : Qb ≃ₐ[ℚ] Qb) (hσ : σ ∈ D) (ν : Pt) (a : A) :
    WithConv.ofConv (galPt D A σ hσ ν) a = σ (WithConv.ofConv ν a) := rfl

noncomputable def τ (σ : Qb ≃ₐ[ℚ] Qb) (hσ : σ ∈ D) : Qb ⊗[F′] A →ₐ[F′] Qb ⊗[F′] A :=
  Algebra.TensorProduct.map ((galF D σ hσ : Qb ≃ₐ[F′] Qb) : Qb →ₐ[F′] Qb) (AlgHom.id F′ A)

@[scoped simp] theorem τ_tmul (σ : Qb ≃ₐ[ℚ] Qb) (hσ : σ ∈ D) (c : Qb) (a : A) :
    τ D A σ hσ (c ⊗ₜ a) = σ c ⊗ₜ a := by
  simp [τ]
  rfl

theorem exists_eq_includeRight_of_forall_τ_eq [Module.Finite F′ A]
    (x : Qb ⊗[F′] A) (hx : ∀ σ (hσ : σ ∈ D), τ D A σ hσ x = x) :
    ∃ a : A, x = (1 : Qb) ⊗ₜ a := by
  classical
  let b := Module.Free.chooseBasis F′ A
  let B := Algebra.TensorProduct.basis Qb b

  have hcoord : ∀ σ (hσ : σ ∈ D) (y : Qb ⊗[F′] A) (i : Module.Free.ChooseBasisIndex F′ A),
      B.repr (τ D A σ hσ y) i = σ (B.repr y i) := by
    intro σ hσ y i
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c m =>
      rw [τ_tmul]
      simp only [B, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
        smul_eq_mul, map_mul]
      congr 1
      exact ((IntermediateField.mem_fixedField_iff _ _).mp (b.repr m i).2 σ hσ).symm
    | add y z hy hz => simp [map_add, hy, hz]

  have hfix : ∀ i, B.repr x i ∈ IntermediateField.fixedField D := by
    intro i
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    rw [← hcoord σ hσ x i, hx σ hσ]
  refine ⟨∑ i, (⟨B.repr x i, hfix i⟩ : F′) • b i, ?_⟩
  calc x = ∑ i, B.repr x i • B i := (B.sum_repr x).symm
    _ = ∑ i, (1 : Qb) ⊗ₜ[F′] ((⟨B.repr x i, hfix i⟩ : F′) • b i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hc : B.repr x i = algebraMap F′ Qb ⟨B.repr x i, hfix i⟩ := rfl
        conv_lhs =>
          rw [show B i = (1 : Qb) ⊗ₜ[F′] b i from Algebra.TensorProduct.basis_apply b i, hc,
            TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one,
            TensorProduct.smul_tmul]
    _ = (1 : Qb) ⊗ₜ ∑ i, (⟨B.repr x i, hfix i⟩ : F′) • b i := by rw [TensorProduct.tmul_sum]

variable (hev : Function.Bijective (L D A))

noncomputable def E : Qb ⊗[F′] A ≃ₐ[Qb] (Pt → Qb) := AlgEquiv.ofBijective (L D A) hev

noncomputable def U (phi : Pt →* Pt) : (Pt → Qb) →ₐ[Qb] (Pt → Qb) where
  toFun g := fun ν => g (phi ν)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[scoped simp] theorem U_apply (phi : Pt →* Pt) (g : Pt → Qb) (ν : Pt) : U D A phi g ν = g (phi ν) := rfl

theorem phi_galPt (phi : Pt →* Pt)
    (hphi : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ D → ∀ ν ν' : Pt,
      (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
      ∀ a : A, WithConv.ofConv (phi ν') a = σ (WithConv.ofConv (phi ν) a))
    (σ : Qb ≃ₐ[ℚ] Qb) (hσ : σ ∈ D) (ν : Pt) :
    phi (galPt D A σ hσ ν) = galPt D A σ hσ (phi ν) := by
  have h := hphi σ hσ ν (galPt D A σ hσ ν) (fun a => rfl)

  show phi (galPt D A σ hσ ν) = WithConv.toConv _
  rw [← WithConv.toConv_ofConv (phi (galPt D A σ hσ ν))]
  congr 1
  apply AlgHom.ext
  intro a
  exact h a

noncomputable def U' (phi : Pt →* Pt) : Qb ⊗[F′] A →ₐ[Qb] Qb ⊗[F′] A :=
  ((E D A hev).symm : (Pt → Qb) →ₐ[Qb] _).comp ((U D A phi).comp (E D A hev : Qb ⊗[F′] A →ₐ[Qb] (Pt → Qb)))

noncomputable def galFun (σ : Qb ≃ₐ[ℚ] Qb) (hσ : σ ∈ D) (g : Pt → Qb) : Pt → Qb :=
  fun ν => σ (g (galPt D A σ⁻¹ (inv_mem hσ) ν))

theorem galPt_inv_galPt (σ : Qb ≃ₐ[ℚ] Qb) (hσ : σ ∈ D) (ν : Pt) :
    galPt D A σ⁻¹ (inv_mem hσ) (galPt D A σ hσ ν) = ν := by
  apply (WithConv.toConv_ofConv ν).symm.trans ?_ |>.symm
  show WithConv.toConv _ = WithConv.toConv _
  congr 1
  apply AlgHom.ext
  intro a
  simp [galPt]

theorem E_apply (x : Qb ⊗[F′] A) : E D A hev x = L D A x := rfl

theorem E_τ (σ : Qb ≃ₐ[ℚ] Qb) (hσ : σ ∈ D) (x : Qb ⊗[F′] A) :
    E D A hev (τ D A σ hσ x) = galFun D A σ hσ (E D A hev x) := by
  induction x using TensorProduct.induction_on with
  | zero => funext ν; simp [galFun]
  | tmul c a =>
    funext ν
    rw [τ_tmul, E_apply, E_apply, L_tmul]
    simp only [galFun, L_tmul, map_mul, galPt_apply]
    congr 1
    exact (σ.apply_symm_apply _).symm
  | add x y hx hy =>
    funext ν
    simp only [map_add, hx, hy, Pi.add_apply, galFun, map_add]

theorem U_galFun (phi : Pt →* Pt)
    (hphi : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ D → ∀ ν ν' : Pt,
      (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
      ∀ a : A, WithConv.ofConv (phi ν') a = σ (WithConv.ofConv (phi ν) a))
    (σ : Qb ≃ₐ[ℚ] Qb) (hσ : σ ∈ D) (g : Pt → Qb) :
    U D A phi (galFun D A σ hσ g) = galFun D A σ hσ (U D A phi g) := by
  funext ν
  simp only [U_apply, galFun]
  rw [phi_galPt D A phi hphi σ⁻¹ (inv_mem hσ) ν]

theorem E_U' (phi : Pt →* Pt) (x : Qb ⊗[F′] A) :
    E D A hev (U' D A hev phi x) = U D A phi (E D A hev x) := by
  simp [U']

theorem τ_U' (phi : Pt →* Pt)
    (hphi : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ D → ∀ ν ν' : Pt,
      (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
      ∀ a : A, WithConv.ofConv (phi ν') a = σ (WithConv.ofConv (phi ν) a))
    (σ : Qb ≃ₐ[ℚ] Qb) (hσ : σ ∈ D) (x : Qb ⊗[F′] A) :
    U' D A hev phi (τ D A σ hσ x) = τ D A σ hσ (U' D A hev phi x) := by
  apply (E D A hev).injective
  rw [E_U', E_τ, E_τ, E_U', U_galFun D A phi hphi]

theorem exists_U'_tmul_eq (phi : Pt →* Pt)
    (hphi : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ D → ∀ ν ν' : Pt,
      (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
      ∀ a : A, WithConv.ofConv (phi ν') a = σ (WithConv.ofConv (phi ν) a)) [Module.Finite F′ A] (a : A) :
    ∃ a' : A, U' D A hev phi ((1 : Qb) ⊗ₜ a) = (1 : Qb) ⊗ₜ a' := by
  apply exists_eq_includeRight_of_forall_τ_eq
  intro σ hσ
  rw [← τ_U' D A hev phi hphi σ hσ, τ_tmul, map_one]

theorem tmul_one_injective : Function.Injective (fun a : A => ((1 : Qb) ⊗ₜ[F′] a : Qb ⊗[F′] A)) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap F′ Qb).injective

noncomputable def uFun (phi : Pt →* Pt)
    (hphi : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ D → ∀ ν ν' : Pt,
      (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
      ∀ a : A, WithConv.ofConv (phi ν') a = σ (WithConv.ofConv (phi ν) a)) [Module.Finite F′ A] (a : A) : A :=
  Classical.choose (exists_U'_tmul_eq D A hev phi hphi a)

theorem tmul_uFun (phi : Pt →* Pt)
    (hphi : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ D → ∀ ν ν' : Pt,
      (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
      ∀ a : A, WithConv.ofConv (phi ν') a = σ (WithConv.ofConv (phi ν) a)) [Module.Finite F′ A] (a : A) :
    ((1 : Qb) ⊗ₜ[F′] uFun D A hev phi hphi a : Qb ⊗[F′] A) = U' D A hev phi ((1 : Qb) ⊗ₜ a) :=
  (Classical.choose_spec (exists_U'_tmul_eq D A hev phi hphi a)).symm

theorem uFun_one (phi : Pt →* Pt)
    (hphi : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ D → ∀ ν ν' : Pt,
      (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
      ∀ a : A, WithConv.ofConv (phi ν') a = σ (WithConv.ofConv (phi ν) a)) [Module.Finite F′ A] : uFun D A hev phi hphi 1 = 1 := by
  apply tmul_one_injective D A
  show ((1 : Qb) ⊗ₜ[F′] uFun D A hev phi hphi 1 : Qb ⊗[F′] A) = (1 : Qb) ⊗ₜ[F′] (1 : A)
  rw [tmul_uFun, ← Algebra.TensorProduct.one_def, map_one]

theorem uFun_mul (phi : Pt →* Pt)
    (hphi : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ D → ∀ ν ν' : Pt,
      (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
      ∀ a : A, WithConv.ofConv (phi ν') a = σ (WithConv.ofConv (phi ν) a)) [Module.Finite F′ A] (a b : A) : uFun D A hev phi hphi (a * b) = uFun D A hev phi hphi a * uFun D A hev phi hphi b := by
  apply tmul_one_injective D A
  show ((1 : Qb) ⊗ₜ[F′] uFun D A hev phi hphi (a * b) : Qb ⊗[F′] A) =
    (1 : Qb) ⊗ₜ[F′] (uFun D A hev phi hphi a * uFun D A hev phi hphi b)
  have e1 : ((1 : Qb) ⊗ₜ[F′] (a * b) : Qb ⊗[F′] A) = ((1 : Qb) ⊗ₜ[F′] a) * ((1 : Qb) ⊗ₜ[F′] b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have e2 : ((1 : Qb) ⊗ₜ[F′] (uFun D A hev phi hphi a * uFun D A hev phi hphi b) : Qb ⊗[F′] A) =
      ((1 : Qb) ⊗ₜ[F′] uFun D A hev phi hphi a) * ((1 : Qb) ⊗ₜ[F′] uFun D A hev phi hphi b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [tmul_uFun, e1, map_mul, e2, tmul_uFun, tmul_uFun]

theorem uFun_add (phi : Pt →* Pt)
    (hphi : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ D → ∀ ν ν' : Pt,
      (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
      ∀ a : A, WithConv.ofConv (phi ν') a = σ (WithConv.ofConv (phi ν) a)) [Module.Finite F′ A] (a b : A) : uFun D A hev phi hphi (a + b) = uFun D A hev phi hphi a + uFun D A hev phi hphi b := by
  apply tmul_one_injective D A
  show ((1 : Qb) ⊗ₜ[F′] uFun D A hev phi hphi (a + b) : Qb ⊗[F′] A) =
    (1 : Qb) ⊗ₜ[F′] (uFun D A hev phi hphi a + uFun D A hev phi hphi b)
  rw [tmul_uFun, TensorProduct.tmul_add, map_add, TensorProduct.tmul_add, tmul_uFun, tmul_uFun]

theorem uFun_algebraMap (phi : Pt →* Pt)
    (hphi : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ D → ∀ ν ν' : Pt,
      (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
      ∀ a : A, WithConv.ofConv (phi ν') a = σ (WithConv.ofConv (phi ν) a)) [Module.Finite F′ A] (c : F′) : uFun D A hev phi hphi (algebraMap F′ A c) = algebraMap F′ A c := by
  apply tmul_one_injective D A
  show ((1 : Qb) ⊗ₜ[F′] uFun D A hev phi hphi (algebraMap F′ A c) : Qb ⊗[F′] A) =
    (1 : Qb) ⊗ₜ[F′] algebraMap F′ A c
  have e1 : ((1 : Qb) ⊗ₜ[F′] algebraMap F′ A c : Qb ⊗[F′] A) =
      algebraMap Qb (Qb ⊗[F′] A) (algebraMap F′ Qb c) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.algebraMap_eq_smul_one c, ← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
  rw [tmul_uFun, e1, AlgHom.commutes]

noncomputable def u (phi : Pt →* Pt)
    (hphi : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ D → ∀ ν ν' : Pt,
      (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
      ∀ a : A, WithConv.ofConv (phi ν') a = σ (WithConv.ofConv (phi ν) a)) [Module.Finite F′ A] : A →ₐ[F′] A where
  toFun := uFun D A hev phi hphi
  map_one' := uFun_one D A hev phi hphi
  map_mul' := uFun_mul D A hev phi hphi
  map_zero' := by simpa using uFun_add D A hev phi hphi 0 0
  map_add' := uFun_add D A hev phi hphi
  commutes' := uFun_algebraMap D A hev phi hphi

theorem tmul_u (phi : Pt →* Pt)
    (hphi : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ D → ∀ ν ν' : Pt,
      (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
      ∀ a : A, WithConv.ofConv (phi ν') a = σ (WithConv.ofConv (phi ν) a)) [Module.Finite F′ A] (a : A) :
    ((1 : Qb) ⊗ₜ[F′] u D A hev phi hphi a : Qb ⊗[F′] A) = U' D A hev phi ((1 : Qb) ⊗ₜ a) :=
  tmul_uFun D A hev phi hphi a

theorem apply_u (phi : Pt →* Pt)
    (hphi : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ D → ∀ ν ν' : Pt,
      (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
      ∀ a : A, WithConv.ofConv (phi ν') a = σ (WithConv.ofConv (phi ν) a)) [Module.Finite F′ A] (ν : Pt) (a : A) :
    WithConv.ofConv ν (u D A hev phi hphi a) = WithConv.ofConv (phi ν) a := by
  have h1 : L D A ((1 : Qb) ⊗ₜ u D A hev phi hphi a) ν = WithConv.ofConv ν (u D A hev phi hphi a) := by
    rw [L_tmul, one_mul]
  have h2 : L D A ((1 : Qb) ⊗ₜ a) (phi ν) = WithConv.ofConv (phi ν) a := by
    rw [L_tmul, one_mul]
  rw [← h1, ← h2, tmul_u, ← E_apply D A hev, E_U', U_apply, E_apply]

theorem comp_u (phi : Pt →* Pt)
    (hphi : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ D → ∀ ν ν' : Pt,
      (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
      ∀ a : A, WithConv.ofConv (phi ν') a = σ (WithConv.ofConv (phi ν) a)) [Module.Finite F′ A] (ν : Pt) :
    (WithConv.ofConv ν).comp (u D A hev phi hphi) = WithConv.ofConv (phi ν) :=
  AlgHom.ext fun a => apply_u D A hev phi hphi ν a

theorem counit_u (phi : Pt →* Pt)
    (hphi : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ D → ∀ ν ν' : Pt,
      (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
      ∀ a : A, WithConv.ofConv (phi ν') a = σ (WithConv.ofConv (phi ν) a)) [Module.Finite F′ A] (a : A) :
    Coalgebra.counit (R := F′) (u D A hev phi hphi a) = Coalgebra.counit (R := F′) a := by
  have h := apply_u D A hev phi hphi 1 a
  rw [map_one] at h
  have e1 : ∀ x : A, WithConv.ofConv (1 : Pt) x = algebraMap F′ Qb (Coalgebra.counit (R := F′) x) :=
    fun x => rfl
  rw [e1, e1] at h
  exact (algebraMap F′ Qb).injective h

theorem lift_comp_map_u (phi : Pt →* Pt)
    (hphi : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ D → ∀ ν ν' : Pt,
      (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
      ∀ a : A, WithConv.ofConv (phi ν') a = σ (WithConv.ofConv (phi ν) a)) [Module.Finite F′ A] (ν ν' : Pt) :
    (Algebra.TensorProduct.lift (WithConv.ofConv ν) (WithConv.ofConv ν') (fun _ _ => Commute.all _ _)).comp
        (Algebra.TensorProduct.map (u D A hev phi hphi) (u D A hev phi hphi)) =
      Algebra.TensorProduct.lift (WithConv.ofConv (phi ν)) (WithConv.ofConv (phi ν'))
        (fun _ _ => Commute.all _ _) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.lift_tmul, apply_u]

theorem lift_comul_u (phi : Pt →* Pt)
    (hphi : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ D → ∀ ν ν' : Pt,
      (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
      ∀ a : A, WithConv.ofConv (phi ν') a = σ (WithConv.ofConv (phi ν) a)) [Module.Finite F′ A] (ν ν' : Pt) (a : A) :
    Algebra.TensorProduct.lift (WithConv.ofConv ν) (WithConv.ofConv ν') (fun _ _ => Commute.all _ _)
        (Coalgebra.comul (R := F′) (u D A hev phi hphi a)) =
      Algebra.TensorProduct.lift (WithConv.ofConv ν) (WithConv.ofConv ν') (fun _ _ => Commute.all _ _)
        (Algebra.TensorProduct.map (u D A hev phi hphi) (u D A hev phi hphi) (Coalgebra.comul (R := F′) a)) := by
  rw [← AlgHom.convMul_apply, apply_u, map_mul, AlgHom.convMul_apply]
  show _ = ((Algebra.TensorProduct.lift (WithConv.ofConv ν) (WithConv.ofConv ν') (fun _ _ => Commute.all _ _)).comp
        (Algebra.TensorProduct.map (u D A hev phi hphi) (u D A hev phi hphi))) (Coalgebra.comul (R := F′) a)
  rw [lift_comp_map_u]

theorem map_comp_comul_u (phi : Pt →* Pt)
    (hphi : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ D → ∀ ν ν' : Pt,
      (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
      ∀ a : A, WithConv.ofConv (phi ν') a = σ (WithConv.ofConv (phi ν) a)) [Module.Finite F′ A]
    [Finite (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))] :
    (Algebra.TensorProduct.map (u D A hev phi hphi) (u D A hev phi hphi)).comp (Bialgebra.comulAlgHom F′ A) =
      (Bialgebra.comulAlgHom F′ A).comp (u D A hev phi hphi) := by
  apply AlgHom.ext
  intro a
  simp only [AlgHom.coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply]
  symm
  rw [← sub_eq_zero]
  apply HopfAlgebra.tensorProduct_eq_zero_of_forall_lift_points_eq_zero D A hev
  intro ν ν'
  rw [map_sub, sub_eq_zero]
  exact lift_comul_u D A hev phi hphi (WithConv.toConv ν) (WithConv.toConv ν') a

theorem counit_comp_u (phi : Pt →* Pt)
    (hphi : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ D → ∀ ν ν' : Pt,
      (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
      ∀ a : A, WithConv.ofConv (phi ν') a = σ (WithConv.ofConv (phi ν) a)) [Module.Finite F′ A] :
    (Bialgebra.counitAlgHom F′ A).comp (u D A hev phi hphi) = Bialgebra.counitAlgHom F′ A := by
  apply AlgHom.ext
  intro a
  exact counit_u D A hev phi hphi a

noncomputable def uB (phi : Pt →* Pt)
    (hphi : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ D → ∀ ν ν' : Pt,
      (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
      ∀ a : A, WithConv.ofConv (phi ν') a = σ (WithConv.ofConv (phi ν) a)) [Module.Finite F′ A]
    [Finite (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))] : A →ₐc[F′] A :=
  BialgHom.ofAlgHom (u D A hev phi hphi) (counit_comp_u D A hev phi hphi) (map_comp_comul_u D A hev phi hphi)

include hev in
theorem main (phi : Pt →* Pt)
    (hphi : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ D → ∀ ν ν' : Pt,
      (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
      ∀ a : A, WithConv.ofConv (phi ν') a = σ (WithConv.ofConv (phi ν) a)) [Module.Finite F′ A]
    [Finite (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))] :
    ∃ w : A →ₐc[F′] A, ∀ ν : Pt,
      WithConv.toConv ((WithConv.ofConv ν).comp (w : A →ₐ[F′] A)) = phi ν := by
  refine ⟨uB D A hev phi hphi, fun ν => ?_⟩
  have : ((uB D A hev phi hphi : A →ₐc[F′] A) : A →ₐ[F′] A) = u D A hev phi hphi := by
    apply AlgHom.ext; intro a; rfl
  rw [this, comp_u]

end Desc1
p2m_reactivate "P2MW.S_HopfAlgebra_exists_bialgHom_forall_comp_eq_of_equivariant_of_bijective_evalPoints.Desc1"

theorem solution
    (D : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (A : Type) [CommRing A] [HopfAlgebra ↥(IntermediateField.fixedField D) A]
    [Module.Finite ↥(IntermediateField.fixedField D) A]
    [Finite (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))]
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure ℚ) (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) → AlgebraicClosure ℚ))
        (Pi.algHom ↥(IntermediateField.fixedField D) _
          fun ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) =>
            (WithConv.ofConv ν : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure ℚ ⊗[↥(IntermediateField.fixedField D)] A →ₐ[AlgebraicClosure ℚ]
          (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) → AlgebraicClosure ℚ)))
    (φ : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) →* WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))
    (hφ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ D →
      ∀ ν ν' : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ),
        (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) →
        ∀ a : A, WithConv.ofConv (φ ν') a = σ (WithConv.ofConv (φ ν) a)) :
    ∃ u : A →ₐc[↥(IntermediateField.fixedField D)] A,
      ∀ ν : WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ),
        WithConv.toConv ((WithConv.ofConv ν).comp (u : A →ₐ[↥(IntermediateField.fixedField D)] A)) = φ ν :=
  Desc1.main D A hev φ hφ

end S_HopfAlgebra_exists_bialgHom_forall_comp_eq_of_equivariant_of_bijective_evalPoints
end P2MW
export P2MW.S_HopfAlgebra_exists_bialgHom_forall_comp_eq_of_equivariant_of_bijective_evalPoints (solution)
