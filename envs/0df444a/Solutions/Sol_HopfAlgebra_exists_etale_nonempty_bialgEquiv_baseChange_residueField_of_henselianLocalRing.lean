-- Prove2me | solution 1 for HopfAlgebra.exists_etale_nonempty_bialgEquiv_baseChange_residueField_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/dbbd53c9-a034-5ac0-8b2d-589e4fab35c3

import Mathlib
import Theorems.Thm_Algebra_Etale_existsUnique_algHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing
import Theorems.Thm_Algebra_Etale_exists_free_nonempty_algEquiv_baseChange_residueField_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_etale_nonempty_bialgEquiv_baseChange_residueField_of_henselianLocalRing

set_option autoImplicit false

open scoped TensorProduct

universe u v

namespace HopfLiftAux

open Algebra.TensorProduct

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

local notation "𝕜" => IsLocalRing.ResidueField R

section lift

variable {E : Type*} [CommRing E] [Algebra R E] [Module.Finite R E] [Algebra.Etale R E]
  {C : Type*} [CommRing C] [Algebra R C] [Module.Finite R C]

theorem algHom_ext_baseChange {f g : E →ₐ[R] C}
    (h : Algebra.TensorProduct.map (AlgHom.id 𝕜 𝕜) f = Algebra.TensorProduct.map (AlgHom.id 𝕜 𝕜) g) : f = g := by
  obtain ⟨ψ, -, huniq⟩ :=
    Algebra.Etale.existsUnique_algHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing R E C
      (Algebra.TensorProduct.map (AlgHom.id 𝕜 𝕜) g)
  exact (huniq f h).trans (huniq g rfl).symm

theorem algHom_ext_one_tmul {f g : E →ₐ[R] C} (h : ∀ e : E, (1 : 𝕜) ⊗ₜ[R] f e = (1 : 𝕜) ⊗ₜ[R] g e) :
    f = g := by
  apply algHom_ext_baseChange
  apply Algebra.TensorProduct.ext
  · ext
  · ext e
    simpa using h e

theorem exists_lift (ψbar : 𝕜 ⊗[R] E →ₐ[𝕜] 𝕜 ⊗[R] C) :
    ∃ ψ : E →ₐ[R] C, ∀ e : E, (1 : 𝕜) ⊗ₜ[R] ψ e = ψbar ((1 : 𝕜) ⊗ₜ[R] e) := by
  obtain ⟨ψ, hψ, -⟩ :=
    Algebra.Etale.existsUnique_algHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing R E C ψbar
  refine ⟨ψ, fun e => ?_⟩
  have := congrArg (fun F => F ((1 : 𝕜) ⊗ₜ[R] e)) hψ
  simpa using this

end lift

end HopfLiftAux

namespace HopfLiftAux

open Algebra.TensorProduct

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

local notation "𝕜" => IsLocalRing.ResidueField R

section gamma

variable {X Y : Type*} [CommRing X] [Algebra R X] [CommRing Y] [Algebra R Y]
  {X₀ Y₀ : Type*} [CommRing X₀] [Algebra (IsLocalRing.ResidueField R) X₀]
  [CommRing Y₀] [Algebra (IsLocalRing.ResidueField R) Y₀]
  [Algebra R X₀] [IsScalarTower R (IsLocalRing.ResidueField R) X₀]
  [Algebra R Y₀] [IsScalarTower R (IsLocalRing.ResidueField R) Y₀]
  (α : (IsLocalRing.ResidueField R) ⊗[R] X ≃ₐ[IsLocalRing.ResidueField R] X₀)
  (β : (IsLocalRing.ResidueField R) ⊗[R] Y ≃ₐ[IsLocalRing.ResidueField R] Y₀)

noncomputable def red (α : 𝕜 ⊗[R] X ≃ₐ[𝕜] X₀) : X →ₐ[R] X₀ :=
  (α.toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight

@[scoped simp] theorem red_apply (x : X) : red α x = α ((1 : 𝕜) ⊗ₜ[R] x) := rfl

noncomputable def red₂ : X ⊗[R] Y →ₐ[R] X₀ ⊗[𝕜] Y₀ :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft : X₀ →ₐ[R] X₀ ⊗[𝕜] Y₀).comp (red α))
    (((Algebra.TensorProduct.includeRight : Y₀ →ₐ[𝕜] X₀ ⊗[𝕜] Y₀).restrictScalars R).comp (red β))
    (fun _ _ => Commute.all _ _)

@[scoped simp] theorem red₂_tmul (x : X) (y : Y) :
    red₂ α β (x ⊗ₜ[R] y) = α ((1 : 𝕜) ⊗ₜ[R] x) ⊗ₜ[𝕜] β ((1 : 𝕜) ⊗ₜ[R] y) := by
  simp [red₂, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.tmul_mul_tmul]

noncomputable def gammaHom : 𝕜 ⊗[R] (X ⊗[R] Y) →ₐ[𝕜] X₀ ⊗[𝕜] Y₀ :=
  Algebra.TensorProduct.lift (Algebra.ofId 𝕜 _) (red₂ α β) (fun _ _ => Commute.all _ _)

@[scoped simp] theorem gammaHom_tmul (c : 𝕜) (x : X) (y : Y) :
    gammaHom α β (c ⊗ₜ[R] (x ⊗ₜ[R] y)) = c • (α ((1 : 𝕜) ⊗ₜ[R] x) ⊗ₜ[𝕜] β ((1 : 𝕜) ⊗ₜ[R] y)) := by
  simp [gammaHom, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.smul_def]

noncomputable def gammaInv : X₀ ⊗[𝕜] Y₀ →ₐ[𝕜] 𝕜 ⊗[R] (X ⊗[R] Y) :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.map (AlgHom.id 𝕜 𝕜)
      (Algebra.TensorProduct.includeLeft : X →ₐ[R] X ⊗[R] Y)).comp α.symm.toAlgHom)
    ((Algebra.TensorProduct.map (AlgHom.id 𝕜 𝕜)
      ((Algebra.TensorProduct.includeRight : Y →ₐ[R] X ⊗[R] Y))).comp β.symm.toAlgHom)
    (fun _ _ => @Commute.all ((IsLocalRing.ResidueField R) ⊗[R] (X ⊗[R] Y)) _ _ _)

omit [Algebra R X₀] [IsScalarTower R (IsLocalRing.ResidueField R) X₀]
  [Algebra R Y₀] [IsScalarTower R (IsLocalRing.ResidueField R) Y₀] in
theorem gammaInv_tmul_one (a : X₀) :
    gammaInv α β (a ⊗ₜ[𝕜] (1 : Y₀)) =
      Algebra.TensorProduct.map (AlgHom.id 𝕜 𝕜) (Algebra.TensorProduct.includeLeft : X →ₐ[R] X ⊗[R] Y)
        (α.symm a) := by
  simp [gammaInv, Algebra.TensorProduct.lift_tmul]

omit [Algebra R X₀] [IsScalarTower R (IsLocalRing.ResidueField R) X₀]
  [Algebra R Y₀] [IsScalarTower R (IsLocalRing.ResidueField R) Y₀] in
theorem gammaInv_one_tmul (b : Y₀) :
    gammaInv α β ((1 : X₀) ⊗ₜ[𝕜] b) =
      Algebra.TensorProduct.map (AlgHom.id 𝕜 𝕜) ((Algebra.TensorProduct.includeRight : Y →ₐ[R] X ⊗[R] Y))
        (β.symm b) := by
  simp [gammaInv, Algebra.TensorProduct.lift_tmul]

theorem gammaInv_comp_gammaHom : (gammaInv α β).comp (gammaHom α β) = AlgHom.id 𝕜 _ := by
  apply Algebra.TensorProduct.ext
  · ext
  · apply Algebra.TensorProduct.ext
    · ext x
      simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeLeft_apply, AlgHom.coe_id, id_eq]
      rw [gammaHom_tmul, one_smul, show β ((1 : 𝕜) ⊗ₜ[R] (1 : Y)) = β 1 from rfl, map_one,
        gammaInv_tmul_one, AlgEquiv.symm_apply_apply, Algebra.TensorProduct.map_tmul]
      rfl
    · ext y
      simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
        Algebra.TensorProduct.includeRight_apply, AlgHom.coe_id, id_eq]
      rw [gammaHom_tmul, one_smul, show α ((1 : 𝕜) ⊗ₜ[R] (1 : X)) = α 1 from rfl, map_one,
        gammaInv_one_tmul, AlgEquiv.symm_apply_apply, Algebra.TensorProduct.map_tmul]
      rfl

theorem gammaHom_map_includeLeft (cx : 𝕜 ⊗[R] X) :
    gammaHom α β (Algebra.TensorProduct.map (AlgHom.id 𝕜 𝕜)
      (Algebra.TensorProduct.includeLeft : X →ₐ[R] X ⊗[R] Y) cx) = α cx ⊗ₜ[𝕜] (1 : Y₀) := by
  induction cx using TensorProduct.induction_on with
  | zero => simp
  | tmul c x =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Algebra.TensorProduct.includeLeft_apply,
      gammaHom_tmul, show β ((1 : 𝕜) ⊗ₜ[R] (1 : Y)) = β 1 from rfl, map_one,
      show c ⊗ₜ[R] x = c • ((1 : 𝕜) ⊗ₜ[R] x) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      map_smul, TensorProduct.smul_tmul']
  | add u v hu hv => rw [map_add, map_add, hu, hv, map_add, TensorProduct.add_tmul]

theorem gammaHom_map_includeRight (cy : 𝕜 ⊗[R] Y) :
    gammaHom α β (Algebra.TensorProduct.map (AlgHom.id 𝕜 𝕜)
      ((Algebra.TensorProduct.includeRight : Y →ₐ[R] X ⊗[R] Y)) cy) = (1 : X₀) ⊗ₜ[𝕜] β cy := by
  induction cy using TensorProduct.induction_on with
  | zero => simp
  | tmul c y =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Algebra.TensorProduct.includeRight_apply,
      gammaHom_tmul, show α ((1 : 𝕜) ⊗ₜ[R] (1 : X)) = α 1 from rfl, map_one,
      show c ⊗ₜ[R] y = c • ((1 : 𝕜) ⊗ₜ[R] y) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      map_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul]
  | add u v hu hv => rw [map_add, map_add, hu, hv, map_add, TensorProduct.tmul_add]

theorem gammaHom_comp_gammaInv : (gammaHom α β).comp (gammaInv α β) = AlgHom.id 𝕜 _ := by
  apply Algebra.TensorProduct.ext
  · ext a
    simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeLeft_apply, AlgHom.coe_id, id_eq]
    rw [gammaInv_tmul_one, gammaHom_map_includeLeft, AlgEquiv.apply_symm_apply]
  · ext b
    simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
      Algebra.TensorProduct.includeRight_apply, AlgHom.coe_id, id_eq]
    rw [gammaInv_one_tmul, gammaHom_map_includeRight, AlgEquiv.apply_symm_apply]

noncomputable def gamma : 𝕜 ⊗[R] (X ⊗[R] Y) ≃ₐ[𝕜] X₀ ⊗[𝕜] Y₀ :=
  AlgEquiv.ofAlgHom (gammaHom α β) (gammaInv α β) (gammaHom_comp_gammaInv α β) (gammaInv_comp_gammaHom α β)

theorem gamma_apply (z : 𝕜 ⊗[R] (X ⊗[R] Y)) : gamma α β z = gammaHom α β z := rfl

theorem gamma_symm_apply (z : X₀ ⊗[𝕜] Y₀) : (gamma α β).symm z = gammaInv α β z := rfl

@[scoped simp] theorem gamma_one_tmul (x : X) (y : Y) :
    gamma α β ((1 : 𝕜) ⊗ₜ[R] (x ⊗ₜ[R] y)) = α ((1 : 𝕜) ⊗ₜ[R] x) ⊗ₜ[𝕜] β ((1 : 𝕜) ⊗ₜ[R] y) := by
  rw [gamma_apply, gammaHom_tmul, one_smul]

end gamma

end HopfLiftAux
p2m_reactivate "P2MW.S_HopfAlgebra_exists_etale_nonempty_bialgEquiv_baseChange_residueField_of_henselianLocalRing.HopfLiftAux"

namespace HopfLiftAux

open Algebra.TensorProduct

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

local notation "𝕜" => IsLocalRing.ResidueField R

section hopf

variable {E : Type*} [CommRing E] [Algebra R E] [Module.Finite R E] [Algebra.Etale R E]
  {E₀ : Type*} [CommRing E₀] [HopfAlgebra (IsLocalRing.ResidueField R) E₀]
  [Algebra R E₀] [IsScalarTower R (IsLocalRing.ResidueField R) E₀]
  (φ : (IsLocalRing.ResidueField R) ⊗[R] E ≃ₐ[IsLocalRing.ResidueField R] E₀)

theorem algHom_ext_red {C : Type*} [CommRing C] [Algebra R C] [Module.Finite R C]
    {C₀ : Type*} [Semiring C₀] [Algebra 𝕜 C₀] (J : 𝕜 ⊗[R] C ≃ₐ[𝕜] C₀) {f g : E →ₐ[R] C}
    (h : ∀ e : E, J ((1 : 𝕜) ⊗ₜ[R] f e) = J ((1 : 𝕜) ⊗ₜ[R] g e)) : f = g :=
  algHom_ext_one_tmul fun e => J.injective (h e)

noncomputable abbrev J₂ : 𝕜 ⊗[R] (E ⊗[R] E) ≃ₐ[𝕜] E₀ ⊗[𝕜] E₀ := gamma φ φ

noncomputable abbrev J₃ : 𝕜 ⊗[R] (E ⊗[R] (E ⊗[R] E)) ≃ₐ[𝕜] E₀ ⊗[𝕜] (E₀ ⊗[𝕜] E₀) := gamma φ (J₂ φ)

noncomputable abbrev J₃' : 𝕜 ⊗[R] ((E ⊗[R] E) ⊗[R] E) ≃ₐ[𝕜] (E₀ ⊗[𝕜] E₀) ⊗[𝕜] E₀ := gamma (J₂ φ) φ

noncomputable abbrev JR : 𝕜 ⊗[R] R ≃ₐ[𝕜] 𝕜 := Algebra.TensorProduct.rid R 𝕜 𝕜

noncomputable def antipodeAlgHom₀ : E₀ →ₐ[𝕜] E₀ :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode 𝕜) HopfAlgebra.antipode_one
    (fun a b => by rw [HopfAlgebra.antipode_mul, mul_comm])

omit [Algebra R E₀] [IsScalarTower R (IsLocalRing.ResidueField R) E₀] in
@[scoped simp] theorem antipodeAlgHom₀_apply (a : E₀) : antipodeAlgHom₀ (R := R) a = HopfAlgebra.antipode 𝕜 a := rfl

theorem exists_comulLift : ∃ Δ : E →ₐ[R] E ⊗[R] E,
    ∀ e : E, J₂ φ ((1 : 𝕜) ⊗ₜ[R] Δ e) = Bialgebra.comulAlgHom 𝕜 E₀ (φ ((1 : 𝕜) ⊗ₜ[R] e)) := by
  obtain ⟨Δ, hΔ⟩ := exists_lift (E := E)
    ((J₂ φ).symm.toAlgHom.comp ((Bialgebra.comulAlgHom 𝕜 E₀).comp φ.toAlgHom))
  exact ⟨Δ, fun e => by rw [hΔ]; simp⟩

noncomputable def comulLift : E →ₐ[R] E ⊗[R] E := (exists_comulLift φ).choose

theorem J₂_comulLift (e : E) :
    J₂ φ ((1 : 𝕜) ⊗ₜ[R] comulLift φ e) = Coalgebra.comul (R := 𝕜) (φ ((1 : 𝕜) ⊗ₜ[R] e)) :=
  (exists_comulLift φ).choose_spec e

omit [Algebra R E₀] [IsScalarTower R (IsLocalRing.ResidueField R) E₀] in
theorem exists_counitLift : ∃ ε : E →ₐ[R] R,
    ∀ e : E, JR ((1 : 𝕜) ⊗ₜ[R] ε e) = Bialgebra.counitAlgHom 𝕜 E₀ (φ ((1 : 𝕜) ⊗ₜ[R] e)) := by
  obtain ⟨ε, hε⟩ := exists_lift (E := E)
    ((JR (R := R)).symm.toAlgHom.comp ((Bialgebra.counitAlgHom 𝕜 E₀).comp φ.toAlgHom))
  exact ⟨ε, fun e => by rw [hε]; simp⟩

noncomputable def counitLift : E →ₐ[R] R := (exists_counitLift φ).choose

omit [Algebra R E₀] [IsScalarTower R (IsLocalRing.ResidueField R) E₀] in
theorem JR_counitLift (e : E) :
    JR ((1 : 𝕜) ⊗ₜ[R] counitLift φ e) = Coalgebra.counit (R := 𝕜) (φ ((1 : 𝕜) ⊗ₜ[R] e)) :=
  (exists_counitLift φ).choose_spec e

omit [Algebra R E₀] [IsScalarTower R (IsLocalRing.ResidueField R) E₀] in
theorem exists_antipodeLift : ∃ S : E →ₐ[R] E,
    ∀ e : E, φ ((1 : 𝕜) ⊗ₜ[R] S e) = antipodeAlgHom₀ (R := R) (φ ((1 : 𝕜) ⊗ₜ[R] e)) := by
  obtain ⟨S, hS⟩ := exists_lift (E := E) (φ.symm.toAlgHom.comp ((antipodeAlgHom₀ (R := R)).comp φ.toAlgHom))
  exact ⟨S, fun e => by rw [hS]; simp⟩

noncomputable def antipodeLift : E →ₐ[R] E := (exists_antipodeLift φ).choose

omit [Algebra R E₀] [IsScalarTower R (IsLocalRing.ResidueField R) E₀] in
theorem φ_antipodeLift (e : E) :
    φ ((1 : 𝕜) ⊗ₜ[R] antipodeLift φ e) = HopfAlgebra.antipode 𝕜 (φ ((1 : 𝕜) ⊗ₜ[R] e)) :=
  (exists_antipodeLift φ).choose_spec e

end hopf
p2m_reactivate "P2MW.S_HopfAlgebra_exists_etale_nonempty_bialgEquiv_baseChange_residueField_of_henselianLocalRing.HopfLiftAux"

end HopfLiftAux
p2m_reactivate "P2MW.S_HopfAlgebra_exists_etale_nonempty_bialgEquiv_baseChange_residueField_of_henselianLocalRing.HopfLiftAux"

namespace HopfLiftAux

open Algebra.TensorProduct

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

local notation "𝕜" => IsLocalRing.ResidueField R

section axioms

variable {E : Type*} [CommRing E] [Algebra R E] [Module.Finite R E] [Algebra.Etale R E]
  {E₀ : Type*} [CommRing E₀] [HopfAlgebra (IsLocalRing.ResidueField R) E₀]
  [Algebra R E₀] [IsScalarTower R (IsLocalRing.ResidueField R) E₀]
  (φ : (IsLocalRing.ResidueField R) ⊗[R] E ≃ₐ[IsLocalRing.ResidueField R] E₀)

omit [Module.Finite R E] [Algebra.Etale R E] in
theorem J₃_one_tmul_map_id (f : E →ₐ[R] E ⊗[R] E) (f₀ : E₀ →ₐ[𝕜] E₀ ⊗[𝕜] E₀)
    (hf : ∀ e, J₂ φ ((1 : 𝕜) ⊗ₜ[R] f e) = f₀ (φ ((1 : 𝕜) ⊗ₜ[R] e))) (u : E ⊗[R] E) :
    J₃ φ ((1 : 𝕜) ⊗ₜ[R] Algebra.TensorProduct.map (AlgHom.id R E) f u) =
      Algebra.TensorProduct.map (AlgHom.id 𝕜 E₀) f₀ (J₂ φ ((1 : 𝕜) ⊗ₜ[R] u)) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, gamma_one_tmul, hf, gamma_one_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
  | add u v hu hv => rw [map_add, TensorProduct.tmul_add, map_add, hu, hv, TensorProduct.tmul_add, map_add, map_add]

omit [Module.Finite R E] [Algebra.Etale R E] in
theorem J₃'_one_tmul_map_id (f : E →ₐ[R] E ⊗[R] E) (f₀ : E₀ →ₐ[𝕜] E₀ ⊗[𝕜] E₀)
    (hf : ∀ e, J₂ φ ((1 : 𝕜) ⊗ₜ[R] f e) = f₀ (φ ((1 : 𝕜) ⊗ₜ[R] e))) (u : E ⊗[R] E) :
    J₃' φ ((1 : 𝕜) ⊗ₜ[R] Algebra.TensorProduct.map f (AlgHom.id R E) u) =
      Algebra.TensorProduct.map f₀ (AlgHom.id 𝕜 E₀) (J₂ φ ((1 : 𝕜) ⊗ₜ[R] u)) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, gamma_one_tmul, hf, gamma_one_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
  | add u v hu hv => rw [map_add, TensorProduct.tmul_add, map_add, hu, hv, TensorProduct.tmul_add, map_add, map_add]

omit [Module.Finite R E] [Algebra.Etale R E] in
theorem J₃_one_tmul_assoc (w : (E ⊗[R] E) ⊗[R] E) :
    J₃ φ ((1 : 𝕜) ⊗ₜ[R] Algebra.TensorProduct.assoc R R R E E E w) =
      Algebra.TensorProduct.assoc 𝕜 𝕜 𝕜 E₀ E₀ E₀ (J₃' φ ((1 : 𝕜) ⊗ₜ[R] w)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul u z =>
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [Algebra.TensorProduct.assoc_tmul, gamma_one_tmul, gamma_one_tmul, gamma_one_tmul, gamma_one_tmul,
        Algebra.TensorProduct.assoc_tmul]
    | add u v hu hv =>
      rw [TensorProduct.add_tmul, map_add, TensorProduct.tmul_add, map_add, hu, hv, TensorProduct.tmul_add,
        map_add, map_add]
  | add u v hu hv => rw [map_add, TensorProduct.tmul_add, map_add, hu, hv, TensorProduct.tmul_add, map_add, map_add]

omit [Algebra R E₀] [IsScalarTower R (IsLocalRing.ResidueField R) E₀] in

theorem coassoc₀ (a : E₀) :
    Algebra.TensorProduct.assoc 𝕜 𝕜 𝕜 E₀ E₀ E₀
      (Algebra.TensorProduct.map (Bialgebra.comulAlgHom 𝕜 E₀) (AlgHom.id 𝕜 E₀) (Coalgebra.comul (R := 𝕜) a)) =
      Algebra.TensorProduct.map (AlgHom.id 𝕜 E₀) (Bialgebra.comulAlgHom 𝕜 E₀) (Coalgebra.comul (R := 𝕜) a) := by
  have h := Coalgebra.coassoc_apply (R := 𝕜) a
  have h1 : ∀ z : E₀ ⊗[𝕜] E₀, Algebra.TensorProduct.map (Bialgebra.comulAlgHom 𝕜 E₀) (AlgHom.id 𝕜 E₀) z =
      (Coalgebra.comul (R := 𝕜) (A := E₀)).rTensor E₀ z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [LinearMap.rTensor_tmul]
    | add u v hu hv => rw [map_add, map_add, hu, hv]
  have h2 : ∀ z : E₀ ⊗[𝕜] E₀, Algebra.TensorProduct.map (AlgHom.id 𝕜 E₀) (Bialgebra.comulAlgHom 𝕜 E₀) z =
      (Coalgebra.comul (R := 𝕜) (A := E₀)).lTensor E₀ z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [LinearMap.lTensor_tmul]
    | add u v hu hv => rw [map_add, map_add, hu, hv]
  rw [h1, h2, ← h]
  rfl

theorem comulLift_coassoc :
    (Algebra.TensorProduct.assoc R R R E E E).toAlgHom.comp
        ((Algebra.TensorProduct.map (comulLift φ) (AlgHom.id R E)).comp (comulLift φ)) =
      (Algebra.TensorProduct.map (AlgHom.id R E) (comulLift φ)).comp (comulLift φ) := by
  apply algHom_ext_red (J := J₃ φ)
  intro e
  change (J₃ φ) ((1 : 𝕜) ⊗ₜ[R] Algebra.TensorProduct.assoc R R R E E E
      (Algebra.TensorProduct.map (comulLift φ) (AlgHom.id R E) (comulLift φ e))) =
    (J₃ φ) ((1 : 𝕜) ⊗ₜ[R] Algebra.TensorProduct.map (AlgHom.id R E) (comulLift φ) (comulLift φ e))
  rw [J₃_one_tmul_assoc, J₃'_one_tmul_map_id φ (comulLift φ) (Bialgebra.comulAlgHom 𝕜 E₀) (J₂_comulLift φ),
    J₃_one_tmul_map_id φ (comulLift φ) (Bialgebra.comulAlgHom 𝕜 E₀) (J₂_comulLift φ), J₂_comulLift, coassoc₀]

end axioms
p2m_reactivate "P2MW.S_HopfAlgebra_exists_etale_nonempty_bialgEquiv_baseChange_residueField_of_henselianLocalRing.HopfLiftAux"

end HopfLiftAux
p2m_reactivate "P2MW.S_HopfAlgebra_exists_etale_nonempty_bialgEquiv_baseChange_residueField_of_henselianLocalRing.HopfLiftAux"

namespace HopfLiftAux

open Algebra.TensorProduct

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

local notation "𝕜" => IsLocalRing.ResidueField R

section axioms2

variable {E : Type*} [CommRing E] [Algebra R E] [Module.Finite R E] [Algebra.Etale R E]
  {E₀ : Type*} [CommRing E₀] [HopfAlgebra (IsLocalRing.ResidueField R) E₀]
  [Algebra R E₀] [IsScalarTower R (IsLocalRing.ResidueField R) E₀]
  (φ : (IsLocalRing.ResidueField R) ⊗[R] E ≃ₐ[IsLocalRing.ResidueField R] E₀)

theorem JRE_one_tmul_map_counit (u : E ⊗[R] E) :
    gamma (JR (R := R)) φ ((1 : 𝕜) ⊗ₜ[R] Algebra.TensorProduct.map (counitLift φ) (AlgHom.id R E) u) =
      Algebra.TensorProduct.map (Bialgebra.counitAlgHom 𝕜 E₀) (AlgHom.id 𝕜 E₀) (J₂ φ ((1 : 𝕜) ⊗ₜ[R] u)) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, gamma_one_tmul, JR_counitLift, gamma_one_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    rfl
  | add u v hu hv => rw [map_add, TensorProduct.tmul_add, map_add, hu, hv, TensorProduct.tmul_add, map_add, map_add]

theorem JER_one_tmul_map_counit (u : E ⊗[R] E) :
    gamma φ (JR (R := R)) ((1 : 𝕜) ⊗ₜ[R] Algebra.TensorProduct.map (AlgHom.id R E) (counitLift φ) u) =
      Algebra.TensorProduct.map (AlgHom.id 𝕜 E₀) (Bialgebra.counitAlgHom 𝕜 E₀) (J₂ φ ((1 : 𝕜) ⊗ₜ[R] u)) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, gamma_one_tmul, JR_counitLift, gamma_one_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    rfl
  | add u v hu hv => rw [map_add, TensorProduct.tmul_add, map_add, hu, hv, TensorProduct.tmul_add, map_add, map_add]

omit [Algebra R E₀] [IsScalarTower R (IsLocalRing.ResidueField R) E₀] in
theorem rTensor_counit₀ (a : E₀) :
    Algebra.TensorProduct.map (Bialgebra.counitAlgHom 𝕜 E₀) (AlgHom.id 𝕜 E₀) (Coalgebra.comul (R := 𝕜) a) =
      (1 : 𝕜) ⊗ₜ[𝕜] a := by
  have h := LinearMap.congr_fun (Coalgebra.rTensor_counit_comp_comul (R := 𝕜) (A := E₀)) a
  simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply] at h
  rw [← h]
  induction (Coalgebra.comul (R := 𝕜) a) using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul]
  | add u v hu hv => rw [map_add, map_add, hu, hv]

omit [Algebra R E₀] [IsScalarTower R (IsLocalRing.ResidueField R) E₀] in
theorem lTensor_counit₀ (a : E₀) :
    Algebra.TensorProduct.map (AlgHom.id 𝕜 E₀) (Bialgebra.counitAlgHom 𝕜 E₀) (Coalgebra.comul (R := 𝕜) a) =
      a ⊗ₜ[𝕜] (1 : 𝕜) := by
  have h := LinearMap.congr_fun (Coalgebra.lTensor_counit_comp_comul (R := 𝕜) (A := E₀)) a
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply] at h
  rw [← h]
  induction (Coalgebra.comul (R := 𝕜) a) using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [LinearMap.lTensor_tmul]
  | add u v hu hv => rw [map_add, map_add, hu, hv]

theorem comulLift_rTensor_counit :
    (Algebra.TensorProduct.map (counitLift φ) (AlgHom.id R E)).comp (comulLift φ) =
      (Algebra.TensorProduct.lid R E).symm.toAlgHom := by
  apply algHom_ext_red (J := gamma (JR (R := R)) φ)
  intro e
  change gamma (JR (R := R)) φ ((1 : 𝕜) ⊗ₜ[R]
      Algebra.TensorProduct.map (counitLift φ) (AlgHom.id R E) (comulLift φ e)) =
    gamma (JR (R := R)) φ ((1 : 𝕜) ⊗ₜ[R] ((1 : R) ⊗ₜ[R] e))
  rw [JRE_one_tmul_map_counit, J₂_comulLift, rTensor_counit₀, gamma_one_tmul]
  congr 1
  simp

theorem comulLift_lTensor_counit :
    (Algebra.TensorProduct.map (AlgHom.id R E) (counitLift φ)).comp (comulLift φ) =
      (Algebra.TensorProduct.rid R R E).symm.toAlgHom := by
  apply algHom_ext_red (J := gamma φ (JR (R := R)))
  intro e
  change gamma φ (JR (R := R)) ((1 : 𝕜) ⊗ₜ[R]
      Algebra.TensorProduct.map (AlgHom.id R E) (counitLift φ) (comulLift φ e)) =
    gamma φ (JR (R := R)) ((1 : 𝕜) ⊗ₜ[R] (e ⊗ₜ[R] (1 : R)))
  rw [JER_one_tmul_map_counit, J₂_comulLift, lTensor_counit₀, gamma_one_tmul]
  congr 1
  simp

theorem φ_one_tmul_lmul_map_antipode (u : E ⊗[R] E) :
    φ ((1 : 𝕜) ⊗ₜ[R] Algebra.TensorProduct.lmul' R
      (Algebra.TensorProduct.map (antipodeLift φ) (AlgHom.id R E) u)) =
      Algebra.TensorProduct.lmul' 𝕜
        (Algebra.TensorProduct.map (antipodeAlgHom₀ (R := R)) (AlgHom.id 𝕜 E₀) (J₂ φ ((1 : 𝕜) ⊗ₜ[R] u))) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Algebra.TensorProduct.lmul'_apply_tmul,
      gamma_one_tmul, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Algebra.TensorProduct.lmul'_apply_tmul,
      antipodeAlgHom₀_apply, ← φ_antipodeLift,
      ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add u v hu hv => rw [map_add, map_add, TensorProduct.tmul_add, map_add, hu, hv, TensorProduct.tmul_add,
      map_add, map_add, map_add]

theorem φ_one_tmul_lmul_map_id_antipode (u : E ⊗[R] E) :
    φ ((1 : 𝕜) ⊗ₜ[R] Algebra.TensorProduct.lmul' R
      (Algebra.TensorProduct.map (AlgHom.id R E) (antipodeLift φ) u)) =
      Algebra.TensorProduct.lmul' 𝕜
        (Algebra.TensorProduct.map (AlgHom.id 𝕜 E₀) (antipodeAlgHom₀ (R := R)) (J₂ φ ((1 : 𝕜) ⊗ₜ[R] u))) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Algebra.TensorProduct.lmul'_apply_tmul,
      gamma_one_tmul, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Algebra.TensorProduct.lmul'_apply_tmul,
      antipodeAlgHom₀_apply, ← φ_antipodeLift,
      ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add u v hu hv => rw [map_add, map_add, TensorProduct.tmul_add, map_add, hu, hv, TensorProduct.tmul_add,
      map_add, map_add, map_add]

omit [Algebra R E₀] [IsScalarTower R (IsLocalRing.ResidueField R) E₀] in
theorem antipode_rTensor₀ (a : E₀) :
    Algebra.TensorProduct.lmul' 𝕜
      (Algebra.TensorProduct.map (antipodeAlgHom₀ (R := R)) (AlgHom.id 𝕜 E₀) (Coalgebra.comul (R := 𝕜) a)) =
      algebraMap 𝕜 E₀ (Coalgebra.counit (R := 𝕜) a) := by
  rw [← HopfAlgebra.mul_antipode_rTensor_comul_apply]
  induction (Coalgebra.comul (R := 𝕜) a) using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul, antipodeAlgHom₀]
  | add u v hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]

omit [Algebra R E₀] [IsScalarTower R (IsLocalRing.ResidueField R) E₀] in
theorem antipode_lTensor₀ (a : E₀) :
    Algebra.TensorProduct.lmul' 𝕜
      (Algebra.TensorProduct.map (AlgHom.id 𝕜 E₀) (antipodeAlgHom₀ (R := R)) (Coalgebra.comul (R := 𝕜) a)) =
      algebraMap 𝕜 E₀ (Coalgebra.counit (R := 𝕜) a) := by
  rw [← HopfAlgebra.mul_antipode_lTensor_comul_apply]
  induction (Coalgebra.comul (R := 𝕜) a) using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [LinearMap.lTensor_tmul, antipodeAlgHom₀]
  | add u v hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]

omit [Module.Finite R E] [Algebra.Etale R E] in
theorem φ_one_tmul_algebraMap (r : R) :
    φ ((1 : 𝕜) ⊗ₜ[R] algebraMap R E r) = algebraMap 𝕜 E₀ (JR (R := R) ((1 : 𝕜) ⊗ₜ[R] r)) := by
  have h1 : φ ((1 : 𝕜) ⊗ₜ[R] algebraMap R E r) = algebraMap R E₀ r := by
    have := (φ.toAlgHom.restrictScalars R).commutes r
    rwa [← (Algebra.TensorProduct.includeRight : E →ₐ[R] 𝕜 ⊗[R] E).commutes r] at this
  rw [h1, Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_one, ← IsScalarTower.algebraMap_apply]

theorem antipodeLift_rTensor :
    (Algebra.TensorProduct.lmul' R).comp
        ((Algebra.TensorProduct.map (antipodeLift φ) (AlgHom.id R E)).comp (comulLift φ)) =
      (Algebra.ofId R E).comp (counitLift φ) := by
  apply algHom_ext_red (J := φ)
  intro e
  change φ ((1 : 𝕜) ⊗ₜ[R] Algebra.TensorProduct.lmul' R
      (Algebra.TensorProduct.map (antipodeLift φ) (AlgHom.id R E) (comulLift φ e))) =
    φ ((1 : 𝕜) ⊗ₜ[R] algebraMap R E (counitLift φ e))
  rw [φ_one_tmul_lmul_map_antipode, J₂_comulLift, antipode_rTensor₀, φ_one_tmul_algebraMap, JR_counitLift]

theorem antipodeLift_lTensor :
    (Algebra.TensorProduct.lmul' R).comp
        ((Algebra.TensorProduct.map (AlgHom.id R E) (antipodeLift φ)).comp (comulLift φ)) =
      (Algebra.ofId R E).comp (counitLift φ) := by
  apply algHom_ext_red (J := φ)
  intro e
  change φ ((1 : 𝕜) ⊗ₜ[R] Algebra.TensorProduct.lmul' R
      (Algebra.TensorProduct.map (AlgHom.id R E) (antipodeLift φ) (comulLift φ e))) =
    φ ((1 : 𝕜) ⊗ₜ[R] algebraMap R E (counitLift φ e))
  rw [φ_one_tmul_lmul_map_id_antipode, J₂_comulLift, antipode_lTensor₀, φ_one_tmul_algebraMap, JR_counitLift]

omit [Module.Finite R E] [Algebra.Etale R E] in
theorem J₂_one_tmul_comm (u : E ⊗[R] E) :
    J₂ φ ((1 : 𝕜) ⊗ₜ[R] Algebra.TensorProduct.comm R E E u) =
      Algebra.TensorProduct.comm 𝕜 E₀ E₀ (J₂ φ ((1 : 𝕜) ⊗ₜ[R] u)) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rw [Algebra.TensorProduct.comm_tmul, gamma_one_tmul, gamma_one_tmul, Algebra.TensorProduct.comm_tmul]
  | add u v hu hv => rw [map_add, TensorProduct.tmul_add, map_add, hu, hv, TensorProduct.tmul_add, map_add, map_add]

omit [Algebra R E₀] [IsScalarTower R (IsLocalRing.ResidueField R) E₀] in
theorem comm_comul₀ [Coalgebra.IsCocomm 𝕜 E₀] (a : E₀) :
    Algebra.TensorProduct.comm 𝕜 E₀ E₀ (Coalgebra.comul (R := 𝕜) a) = Coalgebra.comul (R := 𝕜) a := by
  have h := LinearMap.congr_fun (Coalgebra.IsCocomm.comm_comp_comul (R := 𝕜) (A := E₀)) a
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at h
  conv_rhs => rw [← h]
  rfl

end axioms2
p2m_reactivate "P2MW.S_HopfAlgebra_exists_etale_nonempty_bialgEquiv_baseChange_residueField_of_henselianLocalRing.HopfLiftAux"

end HopfLiftAux
p2m_reactivate "P2MW.S_HopfAlgebra_exists_etale_nonempty_bialgEquiv_baseChange_residueField_of_henselianLocalRing.HopfLiftAux"

namespace HopfLiftAux

open Algebra.TensorProduct

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

local notation "𝕜" => IsLocalRing.ResidueField R

section package

variable {E : Type*} [CommRing E] [Algebra R E] [Module.Finite R E] [Algebra.Etale R E]
  {E₀ : Type*} [CommRing E₀] [HopfAlgebra (IsLocalRing.ResidueField R) E₀]
  [Algebra R E₀] [IsScalarTower R (IsLocalRing.ResidueField R) E₀]
  (φ : (IsLocalRing.ResidueField R) ⊗[R] E ≃ₐ[IsLocalRing.ResidueField R] E₀)

theorem comulLift_comm [Coalgebra.IsCocomm 𝕜 E₀] :
    (Algebra.TensorProduct.comm R E E).toAlgHom.comp (comulLift φ) = comulLift φ := by
  apply algHom_ext_red (J := J₂ φ)
  intro e
  change J₂ φ ((1 : 𝕜) ⊗ₜ[R] Algebra.TensorProduct.comm R E E (comulLift φ e)) =
    J₂ φ ((1 : 𝕜) ⊗ₜ[R] comulLift φ e)
  rw [J₂_one_tmul_comm, J₂_comulLift, comm_comul₀]

noncomputable abbrev bialgebraLift : Bialgebra R E :=
  Bialgebra.ofAlgHom (comulLift φ) (counitLift φ) (comulLift_coassoc φ) (comulLift_rTensor_counit φ)
    (comulLift_lTensor_counit φ)

omit [HenselianLocalRing R] [Module.Finite R E] [Algebra.Etale R E] in
theorem mul'_rTensor (S : E →ₐ[R] E) (u : E ⊗[R] E) :
    LinearMap.mul' R E (LinearMap.rTensor E S.toLinearMap u) =
      Algebra.TensorProduct.lmul' R (Algebra.TensorProduct.map S (AlgHom.id R E) u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul]
  | add u v hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]

omit [HenselianLocalRing R] [Module.Finite R E] [Algebra.Etale R E] in
theorem mul'_lTensor (S : E →ₐ[R] E) (u : E ⊗[R] E) :
    LinearMap.mul' R E (LinearMap.lTensor E S.toLinearMap u) =
      Algebra.TensorProduct.lmul' R (Algebra.TensorProduct.map (AlgHom.id R E) S u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [LinearMap.lTensor_tmul]
  | add u v hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]

noncomputable abbrev hopfLift : HopfAlgebra R E :=
  { bialgebraLift φ with
    antipode := (antipodeLift φ).toLinearMap
    mul_antipode_rTensor_comul := by
      ext e
      have h := AlgHom.congr_fun (antipodeLift_rTensor φ) e
      simp only [AlgHom.coe_comp, Function.comp_apply] at h
      change LinearMap.mul' R E (LinearMap.rTensor E (antipodeLift φ).toLinearMap (comulLift φ e)) =
        algebraMap R E (counitLift φ e)
      rw [mul'_rTensor, h]
      rfl
    mul_antipode_lTensor_comul := by
      ext e
      have h := AlgHom.congr_fun (antipodeLift_lTensor φ) e
      simp only [AlgHom.coe_comp, Function.comp_apply] at h
      change LinearMap.mul' R E (LinearMap.lTensor E (antipodeLift φ).toLinearMap (comulLift φ e)) =
        algebraMap R E (counitLift φ e)
      rw [mul'_lTensor, h]
      rfl }

omit [HenselianLocalRing R] [Module.Finite R E] [Algebra.Etale R E] in
theorem algebraComm_eq_comm (u : E ⊗[R] E) :
    Algebra.TensorProduct.comm R E E u = TensorProduct.comm R E E u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add u v hu hv => rw [map_add, map_add, hu, hv]

theorem isCocomm_lift [Coalgebra.IsCocomm 𝕜 E₀] :
    @Coalgebra.IsCocomm R E _ _ _ (bialgebraLift φ).toCoalgebra := by
  letI := bialgebraLift φ
  refine ⟨?_⟩
  ext e
  have h := AlgHom.congr_fun (comulLift_comm φ) e
  simp only [AlgHom.coe_comp, Function.comp_apply] at h
  change TensorProduct.comm R E E (comulLift φ e) = comulLift φ e
  rw [← algebraComm_eq_comm]
  exact h

omit [Module.Finite R E] [Algebra.Etale R E] in
theorem map_φ_φ_ttt (u : E ⊗[R] E) :
    Algebra.TensorProduct.map (φ : 𝕜 ⊗[R] E →ₐ[𝕜] E₀) (φ : 𝕜 ⊗[R] E →ₐ[𝕜] E₀)
      (Algebra.TensorProduct.tensorTensorTensorComm R 𝕜 R 𝕜 𝕜 𝕜 E E
        (((1 : 𝕜) ⊗ₜ[𝕜] (1 : 𝕜)) ⊗ₜ[R] u)) = J₂ φ ((1 : 𝕜) ⊗ₜ[R] u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [Algebra.TensorProduct.tensorTensorTensorComm_tmul, Algebra.TensorProduct.map_tmul, gamma_one_tmul]
    rfl
  | add u v hu hv => rw [TensorProduct.tmul_add, map_add, map_add, hu, hv, TensorProduct.tmul_add, map_add]

theorem comul_compat :
    letI := bialgebraLift φ
    (Algebra.TensorProduct.map (φ : 𝕜 ⊗[R] E →ₐ[𝕜] E₀) (φ : 𝕜 ⊗[R] E →ₐ[𝕜] E₀)).comp
        (Bialgebra.comulAlgHom 𝕜 (𝕜 ⊗[R] E)) =
      (Bialgebra.comulAlgHom 𝕜 E₀).comp (φ : 𝕜 ⊗[R] E →ₐ[𝕜] E₀) := by
  letI := bialgebraLift φ
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · ext e
    simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
      Algebra.TensorProduct.includeRight_apply, Bialgebra.comulAlgHom_apply]
    rw [TensorProduct.comul_tmul]
    change Algebra.TensorProduct.map (φ : 𝕜 ⊗[R] E →ₐ[𝕜] E₀) (φ : 𝕜 ⊗[R] E →ₐ[𝕜] E₀)
      (Algebra.TensorProduct.tensorTensorTensorComm R 𝕜 R 𝕜 𝕜 𝕜 E E
        (((1 : 𝕜) ⊗ₜ[𝕜] (1 : 𝕜)) ⊗ₜ[R] comulLift φ e)) = _
    rw [map_φ_φ_ttt, J₂_comulLift]
    rfl

theorem counit_compat :
    letI := bialgebraLift φ
    (Bialgebra.counitAlgHom 𝕜 E₀).comp (φ : 𝕜 ⊗[R] E →ₐ[𝕜] E₀) = Bialgebra.counitAlgHom 𝕜 (𝕜 ⊗[R] E) := by
  letI := bialgebraLift φ
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · ext e
    simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
      Algebra.TensorProduct.includeRight_apply, Bialgebra.counitAlgHom_apply]
    rw [TensorProduct.counit_tmul]
    change Coalgebra.counit (R := 𝕜) (φ ((1 : 𝕜) ⊗ₜ[R] e)) = (counitLift φ e) • (1 : 𝕜)
    rw [← JR_counitLift, Algebra.TensorProduct.rid_tmul]

noncomputable def bialgEquivLift :
    letI := bialgebraLift φ
    𝕜 ⊗[R] E ≃ₐc[𝕜] E₀ :=
  letI := bialgebraLift φ
  BialgEquiv.ofAlgEquiv φ (counit_compat φ) (comul_compat φ)

end package
p2m_reactivate "P2MW.S_HopfAlgebra_exists_etale_nonempty_bialgEquiv_baseChange_residueField_of_henselianLocalRing.HopfLiftAux"

end HopfLiftAux
p2m_reactivate "P2MW.S_HopfAlgebra_exists_etale_nonempty_bialgEquiv_baseChange_residueField_of_henselianLocalRing.HopfLiftAux"

theorem solution
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (E₀ : Type v) [CommRing E₀] [HopfAlgebra (IsLocalRing.ResidueField R) E₀]
    [Coalgebra.IsCocomm (IsLocalRing.ResidueField R) E₀] [Module.Finite (IsLocalRing.ResidueField R) E₀]
    [Algebra.Etale (IsLocalRing.ResidueField R) E₀] :
    ∃ (E : Type (max u v)) (_ : CommRing E) (_ : HopfAlgebra R E) (_ : Coalgebra.IsCocomm R E)
      (_ : Module.Free R E) (_ : Module.Finite R E),
      Algebra.Etale R E ∧
      Nonempty (IsLocalRing.ResidueField R ⊗[R] E ≃ₐc[IsLocalRing.ResidueField R] E₀) := by
  obtain ⟨E, _, _, hfinE, hfreeE, hetE, ⟨φ⟩⟩ :=
    Algebra.Etale.exists_free_nonempty_algEquiv_baseChange_residueField_of_isLocalRing R E₀
  letI : Algebra R E₀ :=
    ((algebraMap (IsLocalRing.ResidueField R) E₀).comp (algebraMap R (IsLocalRing.ResidueField R))).toAlgebra
  haveI : IsScalarTower R (IsLocalRing.ResidueField R) E₀ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : HopfAlgebra R E := HopfLiftAux.hopfLift φ
  exact ⟨E, inferInstance, inferInstance, HopfLiftAux.isCocomm_lift φ, hfreeE, hfinE, hetE,
    ⟨HopfLiftAux.bialgEquivLift φ⟩⟩

end S_HopfAlgebra_exists_etale_nonempty_bialgEquiv_baseChange_residueField_of_henselianLocalRing
end P2MW
export P2MW.S_HopfAlgebra_exists_etale_nonempty_bialgEquiv_baseChange_residueField_of_henselianLocalRing (solution)
