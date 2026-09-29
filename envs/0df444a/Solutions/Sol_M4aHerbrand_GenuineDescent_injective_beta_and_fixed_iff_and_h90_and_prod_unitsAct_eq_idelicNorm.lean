-- Prove2me | solution 1 for M4aHerbrand.GenuineDescent.injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/aa8a33ee-aab3-5a49-bb63-2056328a081c

import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm

set_option autoImplicit false

section

open scoped TensorProduct

namespace NumberField
p2m_export "NumberField" "AdeleRing.algebraMap_injective AdeleRing"
namespace PrimeNormIndex
namespace TateCardPrimeDegree
p2m_open "NumberField"

section Fixed

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable (A : Type*) [CommRing A] [Algebra K A]

private noncomputable def actT (σ : L ≃ₐ[K] L) : A ⊗[K] L ≃ₐ[A] A ⊗[K] L :=
  Algebra.TensorProduct.congr AlgEquiv.refl σ

private theorem actT_tmul (σ : L ≃ₐ[K] L) (a : A) (l : L) : actT K L A σ (a ⊗ₜ l) = a ⊗ₜ σ l := rfl

private theorem actT_algebraMap (σ : L ≃ₐ[K] L) (a : A) :
    actT K L A σ (algebraMap A (A ⊗[K] L) a) = algebraMap A (A ⊗[K] L) a :=
  (actT K L A σ).commutes a

private theorem algebraMap_tensor_injective [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Function.Injective (algebraMap A (A ⊗[K] L)) := by
  obtain ⟨d, hd⟩ := Algebra.trace_surjective K L 1
  let ε : L →ₗ[K] K := (Algebra.trace K L).comp (LinearMap.mulLeft K d)
  have hε : ε 1 = 1 := by simp [ε, hd]
  let r : A ⊗[K] L →ₗ[A] A := (TensorProduct.AlgebraTensorModule.rid K A A).toLinearMap ∘ₗ (ε.baseChange A)
  intro a b hab
  have h := congrArg r hab
  simpa [r, Algebra.TensorProduct.algebraMap_apply, LinearMap.baseChange_tmul, hε] using h

section Transport

variable {C : Type*} [CommRing C] [Algebra A C]

private noncomputable def actOf (te : A ⊗[K] L ≃ₐ[A] C) (σ : L ≃ₐ[K] L) : C ≃ₐ[A] C :=
  te.symm.trans ((actT K L A σ).trans te)

private theorem actOf_apply (te : A ⊗[K] L ≃ₐ[A] C) (σ : L ≃ₐ[K] L) (c : C) :
    actOf K L A te σ c = te (actT K L A σ (te.symm c)) := rfl

end Transport

section FixedPoints

variable [FiniteDimensional K L] [IsGalois K L]

private theorem forall_actT_eq_self_iff (x : A ⊗[K] L) :
    (∀ σ : L ≃ₐ[K] L, actT K L A σ x = x) ↔ x ∈ Set.range (algebraMap A (A ⊗[K] L)) := by
  constructor
  · intro hx
    obtain ⟨d, hd⟩ := Algebra.trace_surjective K L 1
    let P : L →ₗ[K] L := (Algebra.linearMap K L) ∘ₗ (Algebra.trace K L) ∘ₗ (LinearMap.mulLeft K d)
    have hP : ∀ l : L, P l = ∑ σ : L ≃ₐ[K] L, σ (d * l) := fun l => by
      simp only [P, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply, Algebra.linearMap_apply]
      exact trace_eq_sum_automorphisms (d * l)
    let Q : A ⊗[K] L →ₗ[A] A ⊗[K] L := P.baseChange A
    have hQ : ∀ y : A ⊗[K] L, Q y = ∑ σ : L ≃ₐ[K] L, ((1 : A) ⊗ₜ[K] σ d) * actT K L A σ y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a l =>
          simp only [Q, LinearMap.baseChange_tmul, hP, actT_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
            map_mul, TensorProduct.tmul_sum]
      | add y z hy hz => simp only [map_add, hy, hz, mul_add, Finset.sum_add_distrib]
    have hQr : ∀ y : A ⊗[K] L, Q y ∈ Set.range (algebraMap A (A ⊗[K] L)) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | tmul a l =>
          refine ⟨Algebra.trace K L (d * l) • a, ?_⟩
          simp only [Q, LinearMap.baseChange_tmul]
          rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
            TensorProduct.smul_tmul]
          congr 1
          simp only [P, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply, Algebra.linearMap_apply,
            Algebra.algebraMap_eq_smul_one]
      | add y z hy hz =>
          obtain ⟨a, ha⟩ := hy; obtain ⟨b, hb⟩ := hz
          exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    have hfix : Q x = x := by
      rw [hQ]
      simp_rw [hx]
      rw [← Finset.sum_mul, ← TensorProduct.tmul_sum, ← trace_eq_sum_automorphisms, hd, map_one,
        ← Algebra.TensorProduct.one_def, one_mul]
    rw [← hfix]
    exact hQr x
  · rintro ⟨a, rfl⟩ σ
    exact actT_algebraMap K L A σ a

variable {C : Type*} [CommRing C] [Algebra A C]

private theorem forall_actOf_eq_self_iff (te : A ⊗[K] L ≃ₐ[A] C) (c : C) :
    (∀ σ : L ≃ₐ[K] L, actOf K L A te σ c = c) ↔ c ∈ Set.range (algebraMap A C) := by
  have key : (∀ σ : L ≃ₐ[K] L, actOf K L A te σ c = c) ↔ ∀ σ : L ≃ₐ[K] L, actT K L A σ (te.symm c) = te.symm c := by
    refine forall_congr' fun σ => ?_
    rw [actOf_apply, ← te.symm.injective.eq_iff, AlgEquiv.symm_apply_apply]
  rw [key, forall_actT_eq_self_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [← te.apply_symm_apply c, ← ha, AlgEquiv.commutes]
  · rintro ⟨a, rfl⟩
    exact ⟨a, by rw [AlgEquiv.commutes]⟩

private theorem algebraMap_injective_of_equiv (te : A ⊗[K] L ≃ₐ[A] C) : Function.Injective (algebraMap A C) := by
  intro a b h
  apply algebraMap_tensor_injective K L A
  apply te.injective
  rw [AlgEquiv.commutes, AlgEquiv.commutes, h]

private theorem forall_actOf_units_eq_self_iff (te : A ⊗[K] L ≃ₐ[A] C) (u : Cˣ) :
    (∀ σ : L ≃ₐ[K] L, actOf K L A te σ (u : C) = u) ↔
      u ∈ (Units.map (algebraMap A C : A →* C)).range := by
  constructor
  · intro hu
    obtain ⟨a, ha⟩ := (forall_actOf_eq_self_iff K L A te (u : C)).mp hu
    have hu' : ∀ σ : L ≃ₐ[K] L, actOf K L A te σ (↑u⁻¹ : C) = ↑u⁻¹ := by
      intro σ
      have h1 : actOf K L A te σ (↑u⁻¹ : C) * (u : C) = 1 := by
        conv_lhs => rw [← hu σ, ← map_mul, Units.inv_mul, map_one]
      calc actOf K L A te σ (↑u⁻¹ : C) = actOf K L A te σ (↑u⁻¹ : C) * (u : C) * (↑u⁻¹ : C) := by
            rw [mul_assoc, Units.mul_inv, mul_one]
        _ = ↑u⁻¹ := by rw [h1, one_mul]
    obtain ⟨b, hb⟩ := (forall_actOf_eq_self_iff K L A te (↑u⁻¹ : C)).mp hu'
    have hab : a * b = 1 := by
      apply algebraMap_injective_of_equiv K L A te
      rw [map_mul, ha, hb, Units.mul_inv, map_one]
    refine ⟨Units.mkOfMulEqOne a b hab, Units.ext ?_⟩
    simp [ha]
  · rintro ⟨v, rfl⟩ σ
    simp only [Units.coe_map, MonoidHom.coe_coe]
    exact (forall_actOf_eq_self_iff K L A te _).mpr ⟨v, rfl⟩ σ

end FixedPoints

end Fixed

section Split

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

private noncomputable def splitHom : L ⊗[K] L →ₐ[L] ((L ≃ₐ[K] L) → L) :=
  Algebra.TensorProduct.lift (Algebra.ofId L ((L ≃ₐ[K] L) → L))
    (Pi.algHom (R := K) (A := fun _ : L ≃ₐ[K] L => L) fun σ : L ≃ₐ[K] L => (σ : L →ₐ[K] L))
    (fun _ _ => Commute.all _ _)

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem splitHom_tmul (l m : L) : splitHom K L (l ⊗ₜ m) = fun σ : L ≃ₐ[K] L => l * σ m := by
  ext σ
  simp [splitHom, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]

omit [IsGalois K L] in
set_option maxHeartbeats 3200000 in
private theorem splitHom_surjective : Function.Surjective (splitHom K L) := by
  classical
  let e := Module.Free.chooseBasis K L
  have hq : Submodule.span L (Set.range fun k (j : L ≃ₐ[K] L) ↦ j (e k)) = ⊤ := by
    apply span_flip_eq_top_iff_linearIndependent.mpr <|
      ((linearIndependent_algHom_toLinearMap K L L).comp _
        (algEquivEquivAlgHom K L).injective).map' _ (e.constr L).symm.ker
  have hr : (⊤ : Submodule L ((L ≃ₐ[K] L) → L)) ≤ LinearMap.range (splitHom K L).toLinearMap := by
    rw [← hq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine ⟨(1 : L) ⊗ₜ e k, ?_⟩
    rw [AlgHom.toLinearMap_apply, splitHom_tmul]
    ext σ
    exact one_mul _
  intro v
  obtain ⟨x, hx⟩ := hr (Submodule.mem_top : v ∈ ⊤)
  exact ⟨x, hx⟩

private theorem splitHom_bijective : Function.Bijective (splitHom K L) := by
  classical
  refine ⟨?_, splitHom_surjective K L⟩
  let e := Module.Free.chooseBasis K L
  haveI : FiniteDimensional L (L ⊗[K] L) := Module.Finite.of_basis (Algebra.TensorProduct.basis L e)
  have hdim : Module.finrank L (L ⊗[K] L) = Module.finrank L ((L ≃ₐ[K] L) → L) := by
    rw [Module.finrank_eq_card_basis (Algebra.TensorProduct.basis L e), Module.finrank_fintype_fun_eq_card,
      ← Module.finrank_eq_card_basis e, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  have h := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (splitHom K L).toLinearMap)).mpr (splitHom_surjective K L)
  exact h

private noncomputable def splitEquiv : L ⊗[K] L ≃ₐ[L] ((L ≃ₐ[K] L) → L) :=
  AlgEquiv.ofBijective (splitHom K L) (splitHom_bijective K L)

private theorem splitEquiv_tmul (l m : L) : splitEquiv K L (l ⊗ₜ m) = fun σ : L ≃ₐ[K] L => l * σ m := by
  rw [splitEquiv, AlgEquiv.coe_ofBijective, splitHom_tmul]

end Split

section SplitOver

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (C : Type*) [CommRing C] [Algebra K C] [Algebra L C] [IsScalarTower K L C]

open Classical in

private noncomputable def splitEquivOver : C ⊗[K] L ≃ₐ[C] ((L ≃ₐ[K] L) → C) :=
  (Algebra.TensorProduct.cancelBaseChange K L C C L).symm.trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl : C ≃ₐ[C] C) (splitEquiv K L)).trans <|
      (Algebra.TensorProduct.piRight L C C (fun _ : L ≃ₐ[K] L => L)).trans <|
        AlgEquiv.piCongrRight fun _ => Algebra.TensorProduct.rid L C C

private theorem splitEquivOver_tmul (c : C) (m : L) :
    splitEquivOver K L C (c ⊗ₜ m) = fun σ : L ≃ₐ[K] L => c * algebraMap L C (σ m) := by
  classical
  ext σ
  simp [splitEquivOver, Algebra.TensorProduct.cancelBaseChange_symm_tmul, splitEquiv_tmul,
    Algebra.TensorProduct.piRight_tmul, Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_comm]

end SplitOver

section NormPi

private theorem norm_pi {ι : Type*} [Fintype ι] (C : Type*) [CommRing C] (c : ι → C) :
    Algebra.norm C c = ∏ i, c i := by
  classical
  rw [Algebra.norm_apply]
  have h : (Algebra.lmul C (ι → C) c : (ι → C) →ₗ[C] (ι → C)) =
      LinearMap.pi (fun i => (Algebra.lmul C C (c i) : C →ₗ[C] C).comp (LinearMap.proj i)) := by
    apply LinearMap.ext
    intro v
    funext i
    rfl
  rw [h, LinearMap.det_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Algebra.norm_apply, Algebra.norm_self, MonoidHom.id_apply]

end NormPi

section NormBaseChange

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S] {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem norm_one_tmul (b : Module.Basis ι A S) (A' : Type*) [CommRing A'] [Algebra A A'] (y : S) :
    Algebra.norm A' ((1 : A') ⊗ₜ[A] y) = algebraMap A A' (Algebra.norm A y) := by
  rw [Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis A' b), Algebra.norm_eq_matrix_det b,
    RingHom.map_det, RingHom.mapMatrix_apply, Algebra.leftMulMatrix_apply, Algebra.leftMulMatrix_apply]
  congr 1
  have h : (Algebra.lmul A' (A' ⊗[A] S) ((1 : A') ⊗ₜ[A] y) : A' ⊗[A] S →ₗ[A'] A' ⊗[A] S) =
      (Algebra.lmul A S y : S →ₗ[A] S).baseChange A' := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a s
    simp [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  rw [h, LinearMap.toMatrix_baseChange]

end NormBaseChange

section NormProd

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (A : Type*) [CommRing A] [Algebra K A]

private noncomputable local instance instAlgebraRight : Algebra L (A ⊗[K] L) := Algebra.TensorProduct.rightAlgebra

private local instance instIsScalarTowerRight : IsScalarTower K L (A ⊗[K] L) :=
  IsScalarTower.of_algebraMap_eq fun k => by
    show algebraMap K (A ⊗[K] L) k = (1 : A) ⊗ₜ[K] algebraMap K L k
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem algebraMap_right_apply (m : L) : algebraMap L (A ⊗[K] L) m = (1 : A) ⊗ₜ[K] m := rfl

private noncomputable def conjSplit :
    (A ⊗[K] L) ⊗[A] (A ⊗[K] L) ≃ₐ[A ⊗[K] L] ((L ≃ₐ[K] L) → A ⊗[K] L) :=
  (Algebra.TensorProduct.cancelBaseChange K A (A ⊗[K] L) (A ⊗[K] L) L).trans (splitEquivOver K L (A ⊗[K] L))

private theorem conjSplit_one_tmul (y : A ⊗[K] L) :
    conjSplit K L A ((1 : A ⊗[K] L) ⊗ₜ[A] y) = fun σ : L ≃ₐ[K] L => actT K L A σ y := by
  induction y using TensorProduct.induction_on with
  | zero => funext σ; simp
  | tmul a m =>
      funext σ
      simp only [conjSplit, AlgEquiv.trans_apply, Algebra.TensorProduct.cancelBaseChange_tmul, splitEquivOver_tmul,
        algebraMap_right_apply, actT_tmul, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply, mul_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add y z hy hz =>
      rw [TensorProduct.tmul_add, map_add, hy, hz]
      funext σ
      simp

private theorem algebraMap_norm_eq_prod_actT (y : A ⊗[K] L) :
    algebraMap A (A ⊗[K] L) (Algebra.norm A y) = ∏ σ : L ≃ₐ[K] L, actT K L A σ y := by
  classical
  let e := Module.Free.chooseBasis K L
  rw [← norm_one_tmul (Algebra.TensorProduct.basis A e) (A ⊗[K] L) y,
    ← Algebra.norm_eq_of_algEquiv (conjSplit K L A) ((1 : A ⊗[K] L) ⊗ₜ[A] y), conjSplit_one_tmul, norm_pi]

variable {C : Type*} [CommRing C] [Algebra A C]

private theorem algebraMap_norm_eq_prod_actOf (te : A ⊗[K] L ≃ₐ[A] C) (c : C) :
    algebraMap A C (Algebra.norm A c) = ∏ σ : L ≃ₐ[K] L, actOf K L A te σ c := by
  have h := congrArg te (algebraMap_norm_eq_prod_actT K L A (te.symm c))
  rw [AlgEquiv.commutes, Algebra.norm_eq_of_algEquiv, map_prod] at h
  simpa only [actOf_apply] using h

private theorem prod_map_actOf_units (te : A ⊗[K] L ≃ₐ[A] C) (u : Cˣ) :
    ∏ σ : L ≃ₐ[K] L, Units.map (actOf K L A te σ : C →* C) u =
      Units.map (algebraMap A C : A →* C) (Units.map (Algebra.norm A : C →* A) u) := by
  ext
  push_cast
  exact (algebraMap_norm_eq_prod_actOf K L A te (u : C)).symm

end NormProd

section Hilbert90

p2m_open "NumberField P2MW.S_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm.NumberField M4aHerbrand groupCohomology"

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private noncomputable abbrev ιL : Lˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)

private theorem ιL_injective : Function.Injective (ιL : Lˣ →* (AdeleRing (𝓞 L) L)ˣ) :=
  Units.map_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 L) L)

omit [NumberField K] in

private theorem unitsAct_ιL (D : IdeleGaloisDescent (𝓞 L) K L) (τ : L ≃ₐ[K] L) (x : Lˣ) :
    D.unitsAct τ (ιL x) = ιL (Units.map (τ : L →* L) x) :=
  Units.ext (D.compat τ x)

private theorem ideleClass_h90 (D : IdeleGaloisDescent (𝓞 L) K L)
    (β : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 L) L)
    (hfix : ∀ u : (AdeleRing (𝓞 L) L)ˣ, (∀ τ : L ≃ₐ[K] L, D.unitsAct τ u = u) ↔ u ∈ (Units.map β.toMonoidHom).range) :
    ∀ u : (AdeleRing (𝓞 L) L)ˣ, (∀ τ : L ≃ₐ[K] L, (D.unitsAct τ u)⁻¹ * u ∈ principalIdeles (𝓞 L) L) →
      u ∈ (Units.map β.toMonoidHom).range ⊔ principalIdeles (𝓞 L) L := by
  intro u hall
  let ℓ : (L ≃ₐ[K] L) → Lˣ := fun τ => (hall τ).choose
  have hℓ : ∀ τ, ιL (ℓ τ) = (D.unitsAct τ u)⁻¹ * u := fun τ => (hall τ).choose_spec
  have hcoc : IsMulCocycle₁ ℓ := by
    intro σ τ
    apply ιL_injective
    rw [AlgEquiv.smul_units_def, map_mul, ← unitsAct_ιL D σ, hℓ σ, hℓ τ, hℓ (σ * τ),
      map_mul D.unitsAct, MulAut.mul_apply, map_mul, map_inv]
    rw [mul_assoc, mul_inv_cancel_left]
  obtain ⟨b, hb⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units ℓ hcoc
  have hfixed : ∀ τ, D.unitsAct τ (u * ιL b) = u * ιL b := fun τ => by
    have : ιL (τ • b) = (D.unitsAct τ u)⁻¹ * u * ιL b := by
      rw [div_eq_iff_eq_mul.mp (hb τ), map_mul, hℓ τ]
    rw [map_mul, unitsAct_ιL D τ, ← AlgEquiv.smul_units_def, this, mul_comm u (ιL b),
      ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_comm]
  have hrange := (hfix (u * ιL b)).mp hfixed
  have : u = (u * ιL b) * (ιL b)⁻¹ := by rw [mul_inv_cancel_right]
  rw [this]
  exact Subgroup.mul_mem_sup hrange (Subgroup.inv_mem _ ⟨b, rfl⟩)

end Hilbert90

section Genuine

p2m_open "NumberField P2MW.S_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm.NumberField"

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem unitsAct_genuine_eq (τ : L ≃ₐ[K] L) (u : (AdeleRing (𝓞 L) L)ˣ) :
    (M4aHerbrand.GenuineDescent.genuineDescentDatum K L).unitsAct τ u =
      letI := (M4aHerbrand.Bridge.genuineβ K L).toAlgebra
      Units.map (actOf K L (AdeleRing (𝓞 K) K) (M4aHerbrand.Bridge.genuineTensorEquiv K L) τ :
        AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) u :=
  Units.ext rfl

private theorem algebraMap_genuine_eq :
    (letI := (M4aHerbrand.Bridge.genuineβ K L).toAlgebra; (algebraMap (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :
      AdeleRing (𝓞 K) K →* AdeleRing (𝓞 L) L)) = (M4aHerbrand.Bridge.genuineβ K L).toMonoidHom := rfl

private theorem genuineβ_injective [IsGalois K L] : Function.Injective (M4aHerbrand.Bridge.genuineβ K L) := by
  letI := (M4aHerbrand.Bridge.genuineβ K L).toAlgebra
  exact algebraMap_injective_of_equiv K L (AdeleRing (𝓞 K) K) (M4aHerbrand.Bridge.genuineTensorEquiv K L)

private theorem hfix_genuine [IsGalois K L] (u : (AdeleRing (𝓞 L) L)ˣ) :
    (∀ τ : L ≃ₐ[K] L, (M4aHerbrand.GenuineDescent.genuineDescentDatum K L).unitsAct τ u = u) ↔
      u ∈ (Units.map (M4aHerbrand.Bridge.genuineβ K L).toMonoidHom).range := by
  letI := (M4aHerbrand.Bridge.genuineβ K L).toAlgebra
  rw [← algebraMap_genuine_eq K L,
    ← forall_actOf_units_eq_self_iff K L (AdeleRing (𝓞 K) K) (M4aHerbrand.Bridge.genuineTensorEquiv K L) u]
  refine forall_congr' fun τ => ?_
  rw [unitsAct_genuine_eq K L τ u, Units.ext_iff, Units.coe_map, MonoidHom.coe_coe]

private theorem h90_genuine [IsGalois K L] (u : (AdeleRing (𝓞 L) L)ˣ)
    (hall : ∀ τ : L ≃ₐ[K] L, ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).unitsAct τ u)⁻¹ * u ∈
      M4aHerbrand.principalIdeles (𝓞 L) L) :
    u ∈ (Units.map (M4aHerbrand.Bridge.genuineβ K L).toMonoidHom).range ⊔ M4aHerbrand.principalIdeles (𝓞 L) L :=
  ideleClass_h90 (M4aHerbrand.GenuineDescent.genuineDescentDatum K L) (M4aHerbrand.Bridge.genuineβ K L)
    (hfix_genuine K L) u hall

private theorem hnorm_genuine [IsGalois K L] (u : (AdeleRing (𝓞 L) L)ˣ) :
    ∏ τ : L ≃ₐ[K] L, (M4aHerbrand.GenuineDescent.genuineDescentDatum K L).unitsAct τ u =
      Units.map (M4aHerbrand.Bridge.genuineβ K L).toMonoidHom
        ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm u) := by
  letI := (M4aHerbrand.Bridge.genuineβ K L).toAlgebra
  have h := prod_map_actOf_units K L (AdeleRing (𝓞 K) K) (M4aHerbrand.Bridge.genuineTensorEquiv K L) u
  rw [Finset.prod_congr rfl fun τ _ => unitsAct_genuine_eq K L τ u, h]
  rfl

end Genuine

end NumberField.PrimeNormIndex.TateCardPrimeDegree

end

p2m_open "NumberField P2MW.S_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm.NumberField M4aHerbrand M4aHerbrand.GenuineDescent"

theorem solution
    (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F) :
    Function.Injective (genuineBaseChange E F).β ∧
    (∀ u : (AdeleRing (𝓞 F) F)ˣ, (∀ τ : F ≃ₐ[E] F, D.unitsAct τ u = u) ↔
      u ∈ (Units.map (genuineBaseChange E F).β.toMonoidHom).range) ∧
    (∀ u : (AdeleRing (𝓞 F) F)ˣ,
      (∀ τ : F ≃ₐ[E] F, (D.unitsAct τ u)⁻¹ * u ∈ principalIdeles (𝓞 F) F) →
      u ∈ (Units.map (genuineBaseChange E F).β.toMonoidHom).range ⊔ principalIdeles (𝓞 F) F) ∧
    (∀ u : (AdeleRing (𝓞 F) F)ˣ,
      ∏ τ : F ≃ₐ[E] F, D.unitsAct τ u =
        Units.map (genuineBaseChange E F).β.toMonoidHom ((genuineBaseChange E F).idelicNorm u)) := by
  haveI : Subsingleton (IdeleGaloisDescent (𝓞 F) E F) :=
    M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 F) E F
  obtain rfl : D = genuineDescentDatum E F := Subsingleton.elim _ _
  exact ⟨NumberField.PrimeNormIndex.TateCardPrimeDegree.genuineβ_injective E F,
    NumberField.PrimeNormIndex.TateCardPrimeDegree.hfix_genuine E F,
    NumberField.PrimeNormIndex.TateCardPrimeDegree.h90_genuine E F,
    NumberField.PrimeNormIndex.TateCardPrimeDegree.hnorm_genuine E F⟩

end S_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm
end P2MW
export P2MW.S_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm (solution)
