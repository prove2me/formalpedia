-- Prove2me | solution 1 for IsLocalRing.exists_ringEquiv_eqLocus_tensor_trivSqZeroExt_of_flat_of_mul_maximalIdeal_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/1a508b1a-659c-5e8a-b5e5-3119cfe25f64

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_ringEquiv_eqLocus_tensor_trivSqZeroExt_of_flat_of_mul_maximalIdeal_eq_bot

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open TensorProduct IsLocalRing

universe u

namespace Schl

noncomputable def μ {T' : Type u} [CommRing T'] (V : Type u) [AddCommGroup V] [Module T' V]
    (ι : V →ₗ[T'] T') (C : Type u) [CommRing C] [Algebra T' C] : C ⊗[T'] V →ₗ[C] C :=
  (Algebra.TensorProduct.rid T' C C).toLinearEquiv.toLinearMap ∘ₗ LinearMap.baseChange C ι

theorem μ_tmul {T' : Type u} [CommRing T'] (V : Type u) [AddCommGroup V] [Module T' V]
    (ι : V →ₗ[T'] T') (C : Type u) [CommRing C] [Algebra T' C] (c : C) (v : V) :
    μ V ι C (c ⊗ₜ v) = c * algebraMap T' C (ι v) := by
  simp [μ, LinearMap.baseChange_tmul, Algebra.smul_def, mul_comm]

theorem μ_injective {T' : Type u} [CommRing T'] (V : Type u) [AddCommGroup V] [Module T' V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C] :
    Function.Injective (μ V ι C) := by
  unfold μ
  rw [LinearMap.coe_comp]
  refine (Algebra.TensorProduct.rid T' C C).toLinearEquiv.injective.comp ?_
  have : (LinearMap.baseChange C ι : C ⊗[T'] V → C ⊗[T'] T') = LinearMap.lTensor C ι := by
    ext x; rfl
  rw [this]
  exact Module.Flat.lTensor_preserves_injective_linearMap ι hι

theorem range_μ {T' : Type u} [CommRing T'] (I : Ideal T') (V : Type u) [AddCommGroup V] [Module T' V]
    (ι : V →ₗ[T'] T') (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] :
    (LinearMap.range (μ V ι C) : Set C) = (I.map (algebraMap T' C) : Set C) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v =>
      rw [μ_tmul]
      apply Ideal.mul_mem_left
      apply Ideal.mem_map_of_mem
      have : ι v ∈ LinearMap.range ι := ⟨v, rfl⟩
      rw [hιI] at this; exact this
    | add x y hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
  · intro z hz
    simp only [SetLike.mem_coe] at hz ⊢
    rw [Ideal.map, ← Ideal.submodule_span_eq] at hz
    induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      have : i ∈ LinearMap.range ι := by rw [hιI]; exact hi
      obtain ⟨v, rfl⟩ := this
      exact ⟨1 ⊗ₜ v, by rw [μ_tmul, one_mul]⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul a y _ hy =>
      obtain ⟨x, rfl⟩ := hy
      exact ⟨a • x, by rw [map_smul, smul_eq_mul]⟩

theorem mem_range_μ_iff {T' : Type u} [CommRing T'] (I : Ideal T') (V : Type u) [AddCommGroup V] [Module T' V]
    (ι : V →ₗ[T'] T') (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] (z : C) :
    z ∈ LinearMap.range (μ V ι C) ↔ z ∈ I.map (algebraMap T' C) := by
  have := range_μ I V ι hιI C
  exact ⟨fun h => by rw [← SetLike.mem_coe, ← this]; exact h, fun h => by rw [← SetLike.mem_coe, this]; exact h⟩

theorem mul_eq_zero_of_mem_map {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T') (hI : I ≤ maximalIdeal T')
    (hsmall : I * maximalIdeal T' = ⊥) (C : Type u) [CommRing C] [Algebra T' C]
    {x y : C} (hx : x ∈ I.map (algebraMap T' C)) (hy : y ∈ I.map (algebraMap T' C)) :
    x * y = 0 := by
  have hJJ : I.map (algebraMap T' C) * I.map (algebraMap T' C) = ⊥ := by
    rw [← Ideal.map_mul]
    have : I * I = ⊥ := le_bot_iff.mp ((Ideal.mul_mono_right hI).trans hsmall.le)
    rw [this, Ideal.map_bot]
  have := Ideal.mul_mem_mul hx hy
  rw [hJJ] at this
  exact (Submodule.mem_bot C).mp this

section ESide
variable (T' : Type u) [CommRing T'] [IsLocalRing T']
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (C : Type u) [CommRing C] [Algebra T' C]

local notation "𝔈" => (ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] TrivSqZeroExt (ResidueField T') V

noncomputable def eV : (ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] V ≃ₗ[T'] C ⊗[T'] V :=
  (((TensorProduct.comm (ResidueField T') (ResidueField T' ⊗[T'] C) V).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange T' (ResidueField T') (ResidueField T') V C)).restrictScalars T').trans
    (TensorProduct.comm T' V C)

theorem eV_symm_tmul (c : C) (v : V) : (eV T' V C).symm (c ⊗ₜ v) = ((1 : ResidueField T') ⊗ₜ[T'] c) ⊗ₜ v := by
  apply (eV T' V C).injective
  rw [LinearEquiv.apply_symm_apply]
  simp [eV, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]

noncomputable def j : C ⊗[T'] V →ₗ[T'] 𝔈 :=
  ((LinearMap.lTensor (ResidueField T' ⊗[T'] C) (TrivSqZeroExt.inrHom (ResidueField T') V)).restrictScalars T') ∘ₗ
    (eV T' V C).symm.toLinearMap

theorem j_tmul (c : C) (v : V) : j T' V C (c ⊗ₜ v) = ((1 : ResidueField T') ⊗ₜ[T'] c) ⊗ₜ TrivSqZeroExt.inr v := by
  simp only [j, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_toLinearMap, eV_symm_tmul,
    LinearMap.coe_restrictScalars, LinearMap.lTensor_tmul]
  rfl

noncomputable def pr : 𝔈 →ₗ[T'] C ⊗[T'] V :=
  (eV T' V C).toLinearMap ∘ₗ
    ((LinearMap.lTensor (ResidueField T' ⊗[T'] C) (TrivSqZeroExt.sndHom (ResidueField T') V)).restrictScalars T')

theorem pr_j (x : C ⊗[T'] V) : pr T' V C (j T' V C x) = x := by
  simp only [pr, j, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_toLinearMap]
  rw [← LinearMap.comp_apply (LinearMap.lTensor _ _) (LinearMap.lTensor _ _), ← LinearMap.lTensor_comp]
  have : (TrivSqZeroExt.sndHom (ResidueField T') V) ∘ₗ (TrivSqZeroExt.inrHom (ResidueField T') V) = LinearMap.id := by
    ext v; rfl
  rw [this, LinearMap.lTensor_id, LinearMap.id_apply, LinearEquiv.apply_symm_apply]

theorem j_injective : Function.Injective (j T' V C) :=
  Function.LeftInverse.injective (g := pr T' V C) (pr_j T' V C)

theorem j_smul (a : C) (x : C ⊗[T'] V) :
    j T' V C (a • x) = ((((1 : ResidueField T') ⊗ₜ[T'] a) ⊗ₜ (1 : TrivSqZeroExt (ResidueField T') V)) : 𝔈) * j T' V C x := by
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [smul_zero, map_zero]
    exact (mul_zero ((((1 : ResidueField T') ⊗ₜ[T'] a) ⊗ₜ (1 : TrivSqZeroExt (ResidueField T') V)) : 𝔈)).symm
  | tmul c v =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, j_tmul, j_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
  | add x y hx hy =>
    rw [smul_add, map_add, map_add, hx, hy]
    exact (Distrib.left_distrib ((((1 : ResidueField T') ⊗ₜ[T'] a) ⊗ₜ (1 : TrivSqZeroExt (ResidueField T') V)) : 𝔈)
      (j T' V C x) (j T' V C y)).symm

theorem j_mul_j (x y : C ⊗[T'] V) : j T' V C x * j T' V C y = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mul (j T' V C y)
  | tmul c v =>
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact mul_zero (j T' V C (c ⊗ₜ v))
    | tmul c' w => rw [j_tmul, j_tmul, Algebra.TensorProduct.tmul_mul_tmul, TrivSqZeroExt.inr_mul_inr, TensorProduct.tmul_zero]
    | add y z hy hz => rw [map_add, Distrib.left_distrib (j T' V C (c ⊗ₜ v)) (j T' V C y) (j T' V C z), hy, hz, add_zero]
  | add x x' hx hx' => rw [map_add, Distrib.right_distrib (j T' V C x) (j T' V C x') (j T' V C y), hx, hx', add_zero]

noncomputable def aug : 𝔈 →+* ResidueField T' ⊗[T'] C :=
  (Algebra.TensorProduct.lift (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C))
    ((Algebra.ofId (ResidueField T') (ResidueField T' ⊗[T'] C)).comp
      (TrivSqZeroExt.fstHom (ResidueField T') (ResidueField T') V)) (fun _ _ => Commute.all _ _)).toRingHom

theorem aug_tmul (y : ResidueField T' ⊗[T'] C) (z : TrivSqZeroExt (ResidueField T') V) :
    aug T' V C (y ⊗ₜ z) = z.fst • y := by
  simp only [aug, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply,
    AlgHom.comp_apply]
  rw [Algebra.ofId_apply, Algebra.smul_def, mul_comm]
  rfl

theorem aug_tmul_one (y : ResidueField T' ⊗[T'] C) :
    aug T' V C (y ⊗ₜ (1 : TrivSqZeroExt (ResidueField T') V)) = y := by
  rw [aug_tmul, TrivSqZeroExt.fst_one, one_smul]

theorem aug_j (x : C ⊗[T'] V) : aug T' V C (j T' V C x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul c v => rw [j_tmul, aug_tmul, TrivSqZeroExt.fst_inr, zero_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

theorem exists_eq_aug_tmul_one_add_j (e : 𝔈) :
    ∃ x : C ⊗[T'] V, e = (aug T' V C e) ⊗ₜ (1 : TrivSqZeroExt (ResidueField T') V) + j T' V C x := by
  induction e using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero, map_zero, TensorProduct.zero_tmul, add_zero]⟩
  | tmul y z =>

    have hz : z = TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inr z.snd := (TrivSqZeroExt.inl_fst_add_inr_snd_eq z).symm

    have hinr : ∃ x : C ⊗[T'] V, (y ⊗ₜ TrivSqZeroExt.inr z.snd : 𝔈) = j T' V C x := by
      induction y using TensorProduct.induction_on with
      | zero => exact ⟨0, by rw [TensorProduct.zero_tmul, map_zero]⟩
      | tmul s c =>
        refine ⟨c ⊗ₜ (s • z.snd), ?_⟩
        rw [j_tmul, TrivSqZeroExt.inr_smul, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | add y y' hy hy' =>
        obtain ⟨x, hx⟩ := hy; obtain ⟨x', hx'⟩ := hy'
        exact ⟨x + x', by rw [TensorProduct.add_tmul, hx, hx', map_add]⟩
    obtain ⟨x, hx⟩ := hinr
    refine ⟨x, ?_⟩
    rw [aug_tmul]
    conv_lhs => rw [hz, TensorProduct.tmul_add, hx]
    congr 1
    have hinl : (TrivSqZeroExt.inl z.fst : TrivSqZeroExt (ResidueField T') V) = z.fst • (1 : TrivSqZeroExt (ResidueField T') V) := by
      rw [← Algebra.algebraMap_eq_smul_one]; rfl
    rw [hinl, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add e e' he he' =>
    obtain ⟨x, hx⟩ := he; obtain ⟨x', hx'⟩ := he'
    refine ⟨x + x', ?_⟩
    rw [map_add, map_add, TensorProduct.add_tmul]
    conv_lhs => rw [hx, hx']
    abel

end ESide

end Schl

open Schl in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C] :
    let k := ResidueField T'
    let σ : C →+* C ⧸ I.map (algebraMap T' C) := Ideal.Quotient.mk _
    let P : Subring (C × C) := RingHom.eqLocus (σ.comp (RingHom.fst C C)) (σ.comp (RingHom.snd C C))
    let toCk : C →+* k ⊗[T'] C := Algebra.TensorProduct.includeRight.toRingHom
    let E := (k ⊗[T'] C) ⊗[k] TrivSqZeroExt k V
    let aug : E →+* k ⊗[T'] C :=
      (Algebra.TensorProduct.lift (AlgHom.id k (k ⊗[T'] C))
        ((Algebra.ofId k (k ⊗[T'] C)).comp (TrivSqZeroExt.fstHom k k V)) (fun _ _ => Commute.all _ _)).toRingHom
    let Q : Subring (C × E) := RingHom.eqLocus (toCk.comp (RingHom.fst C E)) (aug.comp (RingHom.snd C E))
    ∃ Θ : P ≃+* Q,
      (∀ x : P, ((Θ x : Q) : C × E).1 = (x : C × C).1) ∧
      (∀ (a : C) (ha : (a, a) ∈ P), ((Θ ⟨(a, a), ha⟩ : Q) : C × E).2 = toCk a ⊗ₜ (1 : TrivSqZeroExt k V)) ∧
      (∀ (v : V) (c : C) (h : ((0 : C), algebraMap T' C (ι v) * c) ∈ P),
        ((Θ ⟨((0 : C), algebraMap T' C (ι v) * c), h⟩ : Q) : C × E).2 = toCk c ⊗ₜ TrivSqZeroExt.inr v) := by
  intro k σ P toCk E aug Q
  classical

  have hPmem : ∀ p : C × C, p ∈ P ↔ σ p.1 = σ p.2 := fun _ => Iff.rfl
  have hQmem : ∀ q : C × E, q ∈ Q ↔ toCk q.1 = aug q.2 := fun _ => Iff.rfl
  have htoCk : ∀ c : C, toCk c = (1 : k) ⊗ₜ[T'] c := fun c => Algebra.TensorProduct.includeRight_apply c
  have haug : ∀ e : E, aug e = Schl.aug T' V C e := fun _ => rfl
  have hμinj := Schl.μ_injective V ι hι C
  let ν : (C ⊗[T'] V) ≃ₗ[C] ↥(LinearMap.range (Schl.μ V ι C)) := LinearEquiv.ofInjective (Schl.μ V ι C) hμinj
  have hμν : ∀ y : ↥(LinearMap.range (Schl.μ V ι C)), Schl.μ V ι C (ν.symm y) = (y : C) := by
    intro y
    have : ((ν (ν.symm y) : ↥(LinearMap.range (Schl.μ V ι C))) : C) = Schl.μ V ι C (ν.symm y) := rfl
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  have hνμ : ∀ (z : C ⊗[T'] V) (hz : Schl.μ V ι C z ∈ LinearMap.range (Schl.μ V ι C)), ν.symm ⟨_, hz⟩ = z := by
    intro z hz
    apply hμinj; rw [hμν]

  have hPdiff : ∀ p : C × C, p ∈ P ↔ p.2 - p.1 ∈ LinearMap.range (Schl.μ V ι C) := by
    intro p
    rw [hPmem, Schl.mem_range_μ_iff I V ι hιI C, eq_comm]
    exact Ideal.Quotient.eq
  have hJ0 : ∀ {x y : C}, x ∈ LinearMap.range (Schl.μ V ι C) → y ∈ LinearMap.range (Schl.μ V ι C) → x * y = 0 := by
    intro x y hx hy
    exact Schl.mul_eq_zero_of_mem_map I hI hsmall C ((Schl.mem_range_μ_iff I V ι hιI C x).mp hx)
      ((Schl.mem_range_μ_iff I V ι hιI C y).mp hy)

  let d : ↥P → ↥(LinearMap.range (Schl.μ V ι C)) := fun x => ⟨x.1.2 - x.1.1, (hPdiff x.1).mp x.2⟩
  let θ₂ : ↥P → E := fun x => toCk x.1.1 ⊗ₜ (1 : TrivSqZeroExt k V) + Schl.j T' V C (ν.symm (d x))
  have hd_add : ∀ x y : ↥P, d (x + y) = d x + d y := by
    intro x y; apply Subtype.ext
    show (x.1.2 + y.1.2) - (x.1.1 + y.1.1) = (x.1.2 - x.1.1) + (y.1.2 - y.1.1); ring
  have hd_mul : ∀ x y : ↥P, ν.symm (d (x * y)) = x.1.1 • ν.symm (d y) + y.1.1 • ν.symm (d x) := by
    intro x y
    apply hμinj
    rw [hμν, map_add, map_smul, map_smul, hμν, hμν, smul_eq_mul, smul_eq_mul]
    show x.1.2 * y.1.2 - x.1.1 * y.1.1 = x.1.1 * (y.1.2 - y.1.1) + y.1.1 * (x.1.2 - x.1.1)
    have h0 : (x.1.2 - x.1.1) * (y.1.2 - y.1.1) = 0 := hJ0 (d x).2 (d y).2
    linear_combination h0

  let Θ₀ : ↥P →+* C × E :=
    { toFun := fun x => (x.1.1, θ₂ x)
      map_one' := by
        apply Prod.ext
        · rfl
        · show toCk 1 ⊗ₜ (1 : TrivSqZeroExt k V) + Schl.j T' V C (ν.symm (d 1)) = 1
          have : d 1 = 0 := Subtype.ext (by show (1 : C) - 1 = 0; ring)
          rw [this, map_zero, map_zero, add_zero, htoCk]
          rfl
      map_mul' := by
        intro x y
        apply Prod.ext
        · rfl
        · show toCk (x.1.1 * y.1.1) ⊗ₜ (1 : TrivSqZeroExt k V) + Schl.j T' V C (ν.symm (d (x * y))) =
            (toCk x.1.1 ⊗ₜ (1 : TrivSqZeroExt k V) + Schl.j T' V C (ν.symm (d x))) *
              (toCk y.1.1 ⊗ₜ (1 : TrivSqZeroExt k V) + Schl.j T' V C (ν.symm (d y)))
          rw [hd_mul, map_add, Schl.j_smul, Schl.j_smul, htoCk, htoCk, htoCk]
          have hXY := Schl.j_mul_j T' V C (ν.symm (d x)) (ν.symm (d y))
          have hAA : (((1 : k) ⊗ₜ[T'] x.1.1) ⊗ₜ (1 : TrivSqZeroExt k V) : E) * (((1 : k) ⊗ₜ[T'] y.1.1) ⊗ₜ (1 : TrivSqZeroExt k V)) =
              ((1 : k) ⊗ₜ[T'] (x.1.1 * y.1.1)) ⊗ₜ (1 : TrivSqZeroExt k V) := by
            rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
          linear_combination (-1 : E) * hAA - hXY
      map_zero' := by
        apply Prod.ext
        · rfl
        · show toCk 0 ⊗ₜ (1 : TrivSqZeroExt k V) + Schl.j T' V C (ν.symm (d 0)) = 0
          have : d 0 = 0 := Subtype.ext (by show (0 : C) - 0 = 0; ring)
          rw [this]
          simp only [map_zero, TensorProduct.zero_tmul, add_zero]
      map_add' := by
        intro x y
        apply Prod.ext
        · rfl
        · show toCk (x.1.1 + y.1.1) ⊗ₜ (1 : TrivSqZeroExt k V) + Schl.j T' V C (ν.symm (d (x + y))) =
            (toCk x.1.1 ⊗ₜ (1 : TrivSqZeroExt k V) + Schl.j T' V C (ν.symm (d x))) +
              (toCk y.1.1 ⊗ₜ (1 : TrivSqZeroExt k V) + Schl.j T' V C (ν.symm (d y)))
          rw [hd_add, map_add, map_add, map_add, TensorProduct.add_tmul]
          abel }
  have hΘ₀ : ∀ x : ↥P, Θ₀ x = (x.1.1, θ₂ x) := fun _ => rfl

  have hΘQ : ∀ x : ↥P, Θ₀ x ∈ Q := by
    intro x
    rw [hQmem, hΘ₀]
    show toCk x.1.1 = aug (toCk x.1.1 ⊗ₜ (1 : TrivSqZeroExt k V) + Schl.j T' V C (ν.symm (d x)))
    rw [map_add, haug, haug, Schl.aug_tmul_one, Schl.aug_j, add_zero]
  let Θ₁ : ↥P →+* ↥Q := Θ₀.codRestrict Q hΘQ
  have hΘ₁ : ∀ x : ↥P, (Θ₁ x : C × E) = (x.1.1, θ₂ x) := fun _ => rfl

  have hinj : Function.Injective Θ₁ := by
    intro x y hxy
    have h : (Θ₁ x : C × E) = (Θ₁ y : C × E) := congrArg Subtype.val hxy
    rw [hΘ₁, hΘ₁, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h3 : Schl.j T' V C (ν.symm (d x)) = Schl.j T' V C (ν.symm (d y)) := by
      have := h2
      simp only [θ₂, h1] at this
      exact add_left_cancel this
    have h4 := ν.symm.injective (Schl.j_injective T' V C h3)
    have h5 : x.1.2 - x.1.1 = y.1.2 - y.1.1 := congrArg Subtype.val h4
    apply Subtype.ext; apply Prod.ext h1
    rw [h1] at h5; exact sub_left_inj.mp h5
  have hsurj : Function.Surjective Θ₁ := by
    intro q
    obtain ⟨x, hx⟩ := Schl.exists_eq_aug_tmul_one_add_j T' V C q.1.2
    have hq : toCk q.1.1 = aug q.1.2 := (hQmem q.1).mp q.2
    have hP' : (q.1.1, q.1.1 + Schl.μ V ι C x) ∈ P := (hPdiff _).mpr (by
      show q.1.1 + Schl.μ V ι C x - q.1.1 ∈ LinearMap.range (Schl.μ V ι C)
      rw [add_sub_cancel_left]; exact ⟨x, rfl⟩)
    refine ⟨⟨(q.1.1, q.1.1 + Schl.μ V ι C x), hP'⟩, ?_⟩
    apply Subtype.ext
    rw [hΘ₁]
    apply Prod.ext
    · rfl
    · show toCk q.1.1 ⊗ₜ (1 : TrivSqZeroExt k V) + Schl.j T' V C (ν.symm (d ⟨(q.1.1, q.1.1 + Schl.μ V ι C x), hP'⟩)) = q.1.2
      have : ν.symm (d ⟨(q.1.1, q.1.1 + Schl.μ V ι C x), hP'⟩) = x := by
        apply hμinj; rw [hμν]; show q.1.1 + Schl.μ V ι C x - q.1.1 = Schl.μ V ι C x; ring
      rw [this, hq, haug]; exact hx.symm
  let Θ : ↥P ≃+* ↥Q := RingEquiv.ofBijective Θ₁ ⟨hinj, hsurj⟩
  have hΘ : ∀ x : ↥P, ((Θ x : ↥Q) : C × E) = (x.1.1, θ₂ x) := fun x => hΘ₁ x
  refine ⟨Θ, fun x => by rw [hΘ], ?_, ?_⟩
  · intro a ha
    rw [hΘ]
    show toCk a ⊗ₜ (1 : TrivSqZeroExt k V) + Schl.j T' V C (ν.symm (d ⟨(a, a), ha⟩)) = toCk a ⊗ₜ (1 : TrivSqZeroExt k V)
    have : d ⟨(a, a), ha⟩ = 0 := Subtype.ext (by show a - a = 0; ring)
    rw [this, map_zero, map_zero, add_zero]
  · intro v c h
    rw [hΘ]
    show toCk 0 ⊗ₜ (1 : TrivSqZeroExt k V) + Schl.j T' V C (ν.symm (d ⟨((0 : C), algebraMap T' C (ι v) * c), h⟩)) =
      toCk c ⊗ₜ TrivSqZeroExt.inr v
    have : ν.symm (d ⟨((0 : C), algebraMap T' C (ι v) * c), h⟩) = c ⊗ₜ v := by
      apply hμinj; rw [hμν, Schl.μ_tmul]; show algebraMap T' C (ι v) * c - 0 = c * algebraMap T' C (ι v); ring
    rw [this, map_zero, TensorProduct.zero_tmul, zero_add, Schl.j_tmul, htoCk]

end S_IsLocalRing_exists_ringEquiv_eqLocus_tensor_trivSqZeroExt_of_flat_of_mul_maximalIdeal_eq_bot
end P2MW
export P2MW.S_IsLocalRing_exists_ringEquiv_eqLocus_tensor_trivSqZeroExt_of_flat_of_mul_maximalIdeal_eq_bot (solution)
