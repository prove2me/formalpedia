-- Prove2me | solution 1 for HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/18412cec-4b87-5b78-a7d5-bf28f85346fc

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_HopfAlgebra_isHopfGalois_of_surjective
import Theorems.Thm_HopfAlgebra_finite_projective_hopfKer_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000

universe u v w

noncomputable section

open scoped TensorProduct
open HopfAlgebra

namespace QuotRank

section Retraction

variable {C : Type*} [CommRing C] {A : Type*} [CommRing A] [Algebra C A]

theorem exists_linearMap_apply_one_eq_one [Module.Finite C A] [Module.Projective C A]
    (hinj : Function.Injective (algebraMap C A)) : ∃ r : A →ₗ[C] C, r 1 = 1 := by

  let ev : (A →ₗ[C] C) →ₗ[C] C := LinearMap.applyₗ (1 : A)
  let τ : Ideal C := LinearMap.range ev
  have hmemτ : ∀ (φ : A →ₗ[C] C) (x : A), φ x ∈ τ := by
    intro φ x
    refine ⟨φ.comp (LinearMap.mulRight C x), ?_⟩
    change φ (1 * x) = φ x
    rw [one_mul]

  have htop : (⊤ : Submodule C A) ≤ τ • ⊤ := by
    intro x _
    obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective C A)
    have hx : x = (s x).sum fun a c => c • a := by
      have := DFunLike.congr_fun hs x
      simp only [LinearMap.comp_apply, LinearMap.id_apply, Finsupp.linearCombination_apply] at this
      exact this.symm
    rw [hx]
    refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
    exact hmemτ ((Finsupp.lapply a).comp s) x

  have hτ : τ = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal τ hne
    have hle' : (⊤ : Submodule C A) ≤ 𝔪 • ⊤ := htop.trans (Submodule.smul_mono_left hle)
    obtain ⟨c, hc1, hc⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪 ⊤ Module.Finite.fg_top hle'
    have hc0 : c = 0 := by
      have h1 : c • (1 : A) = 0 := hc 1 Submodule.mem_top
      rw [Algebra.smul_def, mul_one] at h1
      exact hinj (by rw [h1, map_zero])
    rw [hc0, zero_sub] at hc1
    exact h𝔪.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using 𝔪.neg_mem hc1))
  have h1 : (1 : C) ∈ τ := by rw [hτ]; exact Submodule.mem_top
  obtain ⟨r, hr⟩ := h1
  exact ⟨r, hr⟩

end Retraction

variable {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]
variable {B : Type w} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
variable (π : A →ₐc[R] B) (hπ : Function.Surjective π)

include hπ in
theorem exists_retraction :
    ∃ r : A →ₗ[↥(hopfKer π)] ↥(hopfKer π), ∀ c : ↥(hopfKer π), r (c : A) = c := by
  obtain ⟨hfin, hproj⟩ := HopfAlgebra.finite_projective_hopfKer_of_surjective π hπ
  haveI := hfin
  haveI := hproj
  obtain ⟨r, hr⟩ := exists_linearMap_apply_one_eq_one (C := ↥(hopfKer π)) (A := A)
    Subtype.val_injective
  refine ⟨r, fun c => ?_⟩
  have h : (c : A) = c • (1 : A) := by rw [Algebra.smul_def, mul_one]; rfl
  rw [h, LinearMap.map_smul, hr, smul_eq_mul, mul_one]

include hπ in
theorem finite_projective_base :
    Module.Finite R ↥(hopfKer π) ∧ Module.Projective R ↥(hopfKer π) := by
  obtain ⟨r, hr⟩ := exists_retraction π hπ
  let rR : A →ₗ[R] ↥(hopfKer π) := r.restrictScalars R
  have hsplit : rR.comp (hopfKer π).val.toLinearMap = LinearMap.id := LinearMap.ext fun c => hr c
  refine ⟨Module.Finite.of_surjective rR fun c => ⟨c, hr c⟩, ?_⟩
  exact Module.Projective.of_split (hopfKer π).val.toLinearMap rR hsplit

def qC : A ⊗[R] A →ₗ[R] A ⊗[↥(hopfKer π)] A :=
  TensorProduct.lift
    (LinearMap.mk₂ R (fun a a' => a ⊗ₜ[↥(hopfKer π)] a')
      (fun a₁ a₂ a' => TensorProduct.add_tmul a₁ a₂ a')
      (fun t a a' => by simp only [TensorProduct.smul_tmul'])
      (fun a a₁ a₂ => TensorProduct.tmul_add a a₁ a₂)
      (fun t a a' => by simp only [TensorProduct.tmul_smul]))

@[scoped simp] theorem qC_tmul (a a' : A) : qC π (a ⊗ₜ[R] a') = a ⊗ₜ[↥(hopfKer π)] a' := rfl

theorem qC_surjective : Function.Surjective (qC π) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a a' => exact ⟨a ⊗ₜ[R] a', rfl⟩
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add _ _ _⟩

theorem qC_balancing {z : A ⊗[R] A} (hz : z ∈ Submodule.span R (balancingRelations π)) :
    qC π z = 0 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, h, a', hh, rfl⟩ := hx
    rw [map_sub, qC_tmul, qC_tmul, sub_eq_zero, mul_comm a h,
      show h * a = (⟨h, hh⟩ : ↥(hopfKer π)) • a from rfl,
      show h * a' = (⟨h, hh⟩ : ↥(hopfKer π)) • a' from rfl, TensorProduct.smul_tmul]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul t x _ hx => rw [map_smul, hx, smul_zero]

omit [Module.Finite R A] [Module.Free R A] [Module.Finite R B] [Module.Free R B] in

theorem smul_AB (c : ↥(hopfKer π)) (X : A ⊗[R] B) : c • X = ((c : A) ⊗ₜ[R] (1 : B)) * X := by
  induction X using TensorProduct.induction_on with
  | zero => rw [smul_zero, mul_zero]
  | tmul x y =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    change ((c : A) • x) ⊗ₜ[R] y = _
    rw [smul_eq_mul]
  | add x y hx hy => rw [smul_add, hx, hy, mul_add]

def canC : A ⊗[↥(hopfKer π)] A →ₗ[A] A ⊗[R] B :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun a =>
        { toFun := fun a' => canMap π (a ⊗ₜ[R] a')
          map_add' := fun x y => by rw [TensorProduct.tmul_add, map_add]
          map_smul' := fun c a' => by
            rw [RingHom.id_apply, Subalgebra.smul_def, smul_eq_mul, ← canMap_mul_tmul π a a' c.2,
              canMap_tmul, canMap_tmul, smul_AB, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
              one_mul, mul_comm a] }
      map_add' := fun x y => by
        refine LinearMap.ext fun a' => ?_
        change canMap π ((x + y) ⊗ₜ[R] a') = canMap π (x ⊗ₜ[R] a') + canMap π (y ⊗ₜ[R] a')
        rw [TensorProduct.add_tmul, map_add]
      map_smul' := fun a₀ x => by
        refine LinearMap.ext fun a' => ?_
        change canMap π ((a₀ • x) ⊗ₜ[R] a') = a₀ • canMap π (x ⊗ₜ[R] a')
        rw [canMap_tmul, canMap_tmul, smul_eq_mul, ← smul_mul_assoc, TensorProduct.smul_tmul',
          smul_eq_mul] }

theorem canC_tmul (a a' : A) : canC π (a ⊗ₜ[↥(hopfKer π)] a') = canMap π (a ⊗ₜ[R] a') := rfl

theorem canC_qC (z : A ⊗[R] A) : canC π (qC π z) = canMap π z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a a' => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

include hπ in
theorem canC_bijective : Function.Bijective (canC π) := by
  have hGal := HopfAlgebra.isHopfGalois_of_surjective π hπ
  constructor
  · intro x y hxy
    rw [← sub_eq_zero] at hxy ⊢
    rw [← map_sub] at hxy
    obtain ⟨w, hw⟩ := qC_surjective π (x - y)
    rw [← hw, canC_qC] at hxy
    rw [← hw]
    exact qC_balancing π (hGal.2 w hxy)
  · intro y
    obtain ⟨z, rfl⟩ := hGal.1 y
    exact ⟨qC π z, canC_qC π z⟩

def canCEquiv : A ⊗[↥(hopfKer π)] A ≃ₗ[A] A ⊗[R] B :=
  LinearEquiv.ofBijective (canC π) (canC_bijective π hπ)

include hπ in

theorem rankAtStalk_hopfKer_eq (𝔮 : PrimeSpectrum ↥(hopfKer π)) :
    Module.rankAtStalk (R := ↥(hopfKer π)) A 𝔮 = Module.finrank R B := by
  obtain ⟨hfin, hproj⟩ := HopfAlgebra.finite_projective_hopfKer_of_surjective π hπ
  haveI := hfin
  haveI := hproj
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap ↥(hopfKer π) A)) :=
    PrimeSpectrum.comap_surjective_iff_injective_of_finite.2 Subtype.val_injective
  obtain ⟨𝔔, rfl⟩ := hsurj 𝔮
  rw [← Module.rankAtStalk_baseChange (S := A), Module.rankAtStalk_eq_of_equiv (canCEquiv π hπ),
    Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_finrank_of_free]
  rfl

section Fibre

variable (𝔭 : PrimeSpectrum R)

abbrev κ : Type u := 𝔭.asIdeal.ResidueField

abbrev Cκ : Type (max u v) := κ 𝔭 ⊗[R] ↥(hopfKer π)

@[reducible] def algebraCκ : Algebra ↥(hopfKer π) (Cκ π 𝔭) := Algebra.TensorProduct.rightAlgebra

attribute [local instance] algebraCκ

theorem smul_Cκ_def (c : ↥(hopfKer π)) (x : Cκ π 𝔭) : c • x = ((1 : κ 𝔭) ⊗ₜ[R] c) * x := rfl

scoped instance : SMulCommClass ↥(hopfKer π) R (Cκ π 𝔭) :=
  ⟨fun c t x => by rw [smul_Cκ_def, smul_Cκ_def, mul_smul_comm]⟩

scoped instance : SMulCommClass ↥(hopfKer π) (κ 𝔭) (Cκ π 𝔭) :=
  ⟨fun c t x => by rw [smul_Cκ_def, smul_Cκ_def, mul_smul_comm]⟩

scoped instance : IsScalarTower R ↥(hopfKer π) (Cκ π 𝔭) :=
  ⟨fun t c x => by rw [smul_Cκ_def, smul_Cκ_def, TensorProduct.tmul_smul, smul_mul_assoc]⟩

abbrev N : Type (max u v) := Cκ π 𝔭 ⊗[↥(hopfKer π)] A

def Ψ₀ : κ 𝔭 ⊗[R] A →ₗ[R] N π 𝔭 :=
  TensorProduct.lift
    (LinearMap.mk₂ R (fun t a => (t ⊗ₜ[R] (1 : ↥(hopfKer π))) ⊗ₜ[↥(hopfKer π)] a)
      (fun t t' a => by simp only [TensorProduct.add_tmul])
      (fun r t a => by simp only [TensorProduct.smul_tmul'])
      (fun t a a' => by simp only [TensorProduct.tmul_add])
      (fun r t a => by simp only [TensorProduct.tmul_smul]))

theorem Ψ₀_tmul (t : κ 𝔭) (a : A) :
    Ψ₀ π 𝔭 (t ⊗ₜ[R] a) = (t ⊗ₜ[R] (1 : ↥(hopfKer π))) ⊗ₜ[↥(hopfKer π)] a := rfl

theorem Ψ₀_smul (t : κ 𝔭) (z : κ 𝔭 ⊗[R] A) : Ψ₀ π 𝔭 (t • z) = t • Ψ₀ π 𝔭 z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul t' a =>
    rw [TensorProduct.smul_tmul', Ψ₀_tmul, Ψ₀_tmul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      smul_eq_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

def Ψ : κ 𝔭 ⊗[R] A →ₗ[κ 𝔭] N π 𝔭 :=
  { Ψ₀ π 𝔭 with map_smul' := fun t z => Ψ₀_smul π 𝔭 t z }

theorem Ψ_apply (z : κ 𝔭 ⊗[R] A) : Ψ π 𝔭 z = Ψ₀ π 𝔭 z := rfl

def valκ : Cκ π 𝔭 →ₐ[κ 𝔭] κ 𝔭 ⊗[R] A :=
  Algebra.TensorProduct.map (AlgHom.id (κ 𝔭) (κ 𝔭)) (hopfKer π).val

theorem valκ_tmul (t : κ 𝔭) (c : ↥(hopfKer π)) : valκ π 𝔭 (t ⊗ₜ[R] c) = t ⊗ₜ[R] (c : A) := rfl

def Gmap : N π 𝔭 →+ κ 𝔭 ⊗[R] A :=
  TensorProduct.liftAddHom
    { toFun := fun x =>
        { toFun := fun a => valκ π 𝔭 x * ((1 : κ 𝔭) ⊗ₜ[R] a)
          map_zero' := by rw [TensorProduct.tmul_zero, mul_zero]
          map_add' := fun a b => by rw [TensorProduct.tmul_add, mul_add] }
      map_zero' := by
        refine AddMonoidHom.ext fun a => ?_
        change valκ π 𝔭 0 * _ = 0
        rw [map_zero, zero_mul]
      map_add' := fun x y => by
        refine AddMonoidHom.ext fun a => ?_
        change valκ π 𝔭 (x + y) * _ = valκ π 𝔭 x * _ + valκ π 𝔭 y * _
        rw [map_add, add_mul] }
    (fun c x a => by
      change valκ π 𝔭 (c • x) * ((1 : κ 𝔭) ⊗ₜ[R] a) = valκ π 𝔭 x * ((1 : κ 𝔭) ⊗ₜ[R] (c • a))
      rw [smul_Cκ_def, map_mul, valκ_tmul, Subalgebra.smul_def, smul_eq_mul, mul_comm _ (valκ π 𝔭 x),
        mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul])

theorem Gmap_tmul (x : Cκ π 𝔭) (a : A) :
    Gmap π 𝔭 (x ⊗ₜ[↥(hopfKer π)] a) = valκ π 𝔭 x * ((1 : κ 𝔭) ⊗ₜ[R] a) := rfl

theorem Gmap_Ψ (z : κ 𝔭 ⊗[R] A) : Gmap π 𝔭 (Ψ π 𝔭 z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul t a =>
    rw [Ψ_apply, Ψ₀_tmul, Gmap_tmul, valκ_tmul, Subalgebra.coe_one,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem Ψ_surjective : Function.Surjective (Ψ π 𝔭) := by
  intro n
  induction n using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul x a =>
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [map_zero, TensorProduct.zero_tmul]⟩
    | tmul t c =>
      refine ⟨t ⊗ₜ[R] (c • a), ?_⟩
      rw [Ψ_apply, Ψ₀_tmul, ← TensorProduct.smul_tmul, smul_Cκ_def, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, mul_one]
    | add x y hx hy =>
      obtain ⟨x', hx'⟩ := hx
      obtain ⟨y', hy'⟩ := hy
      exact ⟨x' + y', by rw [map_add, hx', hy', TensorProduct.add_tmul]⟩
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add _ _ _⟩

def ΨEquiv : κ 𝔭 ⊗[R] A ≃ₗ[κ 𝔭] N π 𝔭 :=
  LinearEquiv.ofBijective (Ψ π 𝔭)
    ⟨Function.LeftInverse.injective (g := Gmap π 𝔭) (Gmap_Ψ π 𝔭), Ψ_surjective π 𝔭⟩

theorem nontrivial_Cκ : Nontrivial (Cκ π 𝔭) := by
  let e : Cκ π 𝔭 →ₐ[κ 𝔭] κ 𝔭 ⊗[R] R :=
    Algebra.TensorProduct.map (AlgHom.id (κ 𝔭) (κ 𝔭))
      ((Bialgebra.counitAlgHom R A).comp (hopfKer π).val)
  refine ⟨⟨1, 0, fun h10 => ?_⟩⟩
  have h := congrArg (fun x => Algebra.TensorProduct.rid R (κ 𝔭) (κ 𝔭) (e x)) h10
  simp only [map_one, map_zero] at h
  exact one_ne_zero h

end Fibre

include hπ in
theorem rankAtStalk_mul_finrank (𝔭 : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) ↥(hopfKer π) 𝔭 * Module.finrank R B = Module.finrank R A := by
  classical
  haveI : Nontrivial R := by
    by_contra hR
    rw [not_nontrivial_iff_subsingleton] at hR
    exact 𝔭.2.ne_top (Subsingleton.elim _ _)
  obtain ⟨hfin, hproj⟩ := HopfAlgebra.finite_projective_hopfKer_of_surjective π hπ
  obtain ⟨hfinR, hprojR⟩ := finite_projective_base π hπ
  haveI := hfin; haveI := hproj; haveI := hfinR; haveI := hprojR
  letI : Algebra ↥(hopfKer π) (Cκ π 𝔭) := algebraCκ π 𝔭
  haveI : Nontrivial (Cκ π 𝔭) := nontrivial_Cκ π 𝔭
  haveI : IsArtinianRing (Cκ π 𝔭) := IsArtinianRing.of_finite (κ 𝔭) (Cκ π 𝔭)
  haveI : Finite (MaximalSpectrum (Cκ π 𝔭)) := IsArtinianRing.instFiniteMaximalSpectrum _

  set b := Module.finrank R B with hb
  have hrk : ∀ P : MaximalSpectrum (Cκ π 𝔭),
      Module.finrank (Cκ π 𝔭 ⧸ P.asIdeal) ((Cκ π 𝔭 ⧸ P.asIdeal) ⊗[Cκ π 𝔭] N π 𝔭) = b := by
    intro P
    let q₀ : PrimeSpectrum (Cκ π 𝔭 ⧸ P.asIdeal) := ⟨⊥, Ideal.isPrime_bot⟩
    have h1 : Module.rankAtStalk (R := Cκ π 𝔭 ⧸ P.asIdeal) ((Cκ π 𝔭 ⧸ P.asIdeal) ⊗[Cκ π 𝔭] N π 𝔭) q₀ =
        Module.finrank (Cκ π 𝔭 ⧸ P.asIdeal) ((Cκ π 𝔭 ⧸ P.asIdeal) ⊗[Cκ π 𝔭] N π 𝔭) := by
      letI := Ideal.Quotient.field P.asIdeal
      rw [Module.rankAtStalk_eq_finrank_of_free]
      rfl
    rw [← h1, Module.rankAtStalk_baseChange (R := Cκ π 𝔭) (M := N π 𝔭) (S := Cκ π 𝔭 ⧸ P.asIdeal) q₀]
    first
      | rw [Module.rankAtStalk_baseChange]; exact rankAtStalk_hopfKer_eq π hπ _
      | exact rankAtStalk_hopfKer_eq π hπ _
  obtain ⟨bN⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (Cκ π 𝔭) (N π 𝔭) b hrk
  haveI : Module.Free (Cκ π 𝔭) (N π 𝔭) := Module.Free.of_basis bN
  have hN : Module.finrank (Cκ π 𝔭) (N π 𝔭) = b := by
    rw [Module.finrank_eq_card_basis bN, Fintype.card_fin]

  have hdimN : Module.finrank (κ 𝔭) (N π 𝔭) = Module.finrank (κ 𝔭) (Cκ π 𝔭) * b := by
    rw [← hN, Module.finrank_mul_finrank]
  have hdimA : Module.finrank (κ 𝔭) (N π 𝔭) = Module.finrank R A := by
    rw [← (ΨEquiv π 𝔭).finrank_eq, Module.finrank_baseChange]
  have hC : Module.rankAtStalk (R := R) ↥(hopfKer π) 𝔭 = Module.finrank (κ 𝔭) (Cκ π 𝔭) :=
    Module.rankAtStalk_eq 𝔭
  rw [hC, ← hdimN, hdimA]

include hπ in
theorem main :
    (∃ r : A →ₗ[↥(hopfKer π)] ↥(hopfKer π), ∀ c : ↥(hopfKer π), r (c : A) = c) ∧
      Module.Finite R ↥(hopfKer π) ∧ Module.Projective R ↥(hopfKer π) ∧
      ∀ 𝔭 : PrimeSpectrum R,
        Module.rankAtStalk (R := R) ↥(hopfKer π) 𝔭 * Module.finrank R B = Module.finrank R A :=
  ⟨exists_retraction π hπ, (finite_projective_base π hπ).1, (finite_projective_base π hπ).2,
    rankAtStalk_mul_finrank π hπ⟩

end QuotRank
p2m_reactivate "P2MW.S_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective.QuotRank"

end
p2m_reactivate "P2MW.S_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective.QuotRank"

theorem solution
    {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]
    {B : Type w} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    (∃ r : A →ₗ[↥(HopfAlgebra.hopfKer π)] ↥(HopfAlgebra.hopfKer π),
        ∀ c : ↥(HopfAlgebra.hopfKer π), r (c : A) = c) ∧
      Module.Finite R ↥(HopfAlgebra.hopfKer π) ∧ Module.Projective R ↥(HopfAlgebra.hopfKer π) ∧
      ∀ 𝔭 : PrimeSpectrum R,
        Module.rankAtStalk (R := R) ↥(HopfAlgebra.hopfKer π) 𝔭 * Module.finrank R B =
          Module.finrank R A :=
  QuotRank.main π hπ

end S_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
end P2MW
export P2MW.S_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective (solution)
