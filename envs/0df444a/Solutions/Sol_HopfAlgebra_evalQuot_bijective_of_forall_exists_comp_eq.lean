-- Prove2me | solution 1 for HopfAlgebra.evalQuot_bijective_of_forall_exists_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/1e6aa9b9-72f0-5c0a-8489-aee3c28d9b91

import Mathlib
import Definitions.Def_HopfAlgebra_CharacterClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_evalQuot_bijective_of_forall_exists_comp_eq

set_option autoImplicit false

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section
open scoped Pointwise

namespace P2MMultPerm

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section Setup

variable (Γ : Subgroup Gal) (X : Type) [MulAction Γ X]

def IsFixedVec (c : X → ℚ̄) : Prop := ∀ (γ : Γ) (x : X), c (γ • x) = (γ : Gal) (c x)

variable (E : IntermediateField ℚ ℚ̄) [Normal ℚ E]

def res : Γ →* (E ≃ₐ[ℚ] E) := (AlgEquiv.restrictNormalHom E).comp Γ.subtype

variable {Γ} in
theorem res_apply_coe (γ : Γ) (e : E) : ((res Γ E γ e : E) : ℚ̄) = (γ : Gal) e := by
  show ((AlgEquiv.restrictNormal (γ : Gal) E) e : ℚ̄) = _
  exact AlgEquiv.restrictNormal_commutes (γ : Gal) E e

variable (x₀ : X)

def stabBar : Subgroup (E ≃ₐ[ℚ] E) := (MulAction.stabilizer (↥Γ) x₀).map (res Γ E)

def ptField : IntermediateField ℚ E := IntermediateField.fixedField (stabBar Γ X E x₀)

end Setup

section Main

variable {Γ : Subgroup Gal} {X : Type} [MulAction Γ X]
variable {E : IntermediateField ℚ ℚ̄} [Normal ℚ E]
variable {x₀ : X}

theorem apply_eq_of_smul_eq (a : ptField Γ X E x₀) {γ γ' : Γ} (h : γ • x₀ = γ' • x₀) :
    (γ : Gal) ((a : E) : ℚ̄) = (γ' : Gal) ((a : E) : ℚ̄) := by
  have hst : γ'⁻¹ * γ ∈ MulAction.stabilizer (↥Γ) x₀ := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, h, inv_smul_smul]
  have hfix : res Γ E (γ'⁻¹ * γ) (a : E) = (a : E) :=
    (IntermediateField.mem_fixedField_iff (stabBar Γ X E x₀) (a : E)).mp a.2 _ ⟨_, hst, rfl⟩
  have := congrArg (fun e : E => (e : ℚ̄)) hfix
  simp only [res_apply_coe] at this
  rw [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply] at this
  have h2 := congrArg (γ' : Gal) this
  rwa [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at h2

open Classical in

def bvec (x₀ : X) (a : ptField Γ X E x₀) : X → ℚ̄ := fun x =>
  if h : x ∈ MulAction.orbit (↥Γ) x₀ then ((Classical.choose h : Γ) : Gal) ((a : E) : ℚ̄) else 0

theorem bvec_smul (a : ptField Γ X E x₀) (γ : Γ) : bvec x₀ a (γ • x₀) = (γ : Gal) ((a : E) : ℚ̄) := by
  classical
  have h : γ • x₀ ∈ MulAction.orbit (↥Γ) x₀ := ⟨γ, rfl⟩
  rw [bvec, dif_pos h]
  exact apply_eq_of_smul_eq a (Classical.choose_spec h)

theorem bvec_of_not_mem (a : ptField Γ X E x₀) {x : X} (hx : x ∉ MulAction.orbit (↥Γ) x₀) : bvec x₀ a x = 0 := by
  classical
  rw [bvec, dif_neg hx]

theorem bvec_self (a : ptField Γ X E x₀) : bvec x₀ a x₀ = ((a : E) : ℚ̄) := by
  have := bvec_smul a (1 : Γ)
  rwa [one_smul, Subgroup.coe_one, AlgEquiv.one_apply] at this

theorem isFixedVec_bvec (a : ptField Γ X E x₀) : IsFixedVec Γ X (bvec x₀ a) := by
  intro γ x
  by_cases hx : x ∈ MulAction.orbit (↥Γ) x₀
  · obtain ⟨γ', rfl⟩ := hx
    show bvec x₀ a (γ • γ' • x₀) = _
    rw [← mul_smul, bvec_smul, bvec_smul, Subgroup.coe_mul, AlgEquiv.mul_apply]
  · have hx' : γ • x ∉ MulAction.orbit (↥Γ) x₀ := fun h => hx (by
      obtain ⟨γ', h'⟩ := h
      exact ⟨γ⁻¹ * γ', by show (γ⁻¹ * γ') • x₀ = x; rw [mul_smul]; exact (eq_inv_smul_iff.mpr h'.symm).symm⟩)
    rw [bvec_of_not_mem a hx, bvec_of_not_mem a hx', map_zero]

variable (hlev : ∀ γ : Γ, res Γ E γ = 1 → ∀ x : X, γ • x = x)
include hlev

theorem smul_eq_of_forall_apply_eq [FiniteDimensional ℚ E] {γ γ' : Γ}
    (h : ∀ a : ptField Γ X E x₀, (γ : Gal) ((a : E) : ℚ̄) = (γ' : Gal) ((a : E) : ℚ̄)) :
    γ • x₀ = γ' • x₀ := by
  have hmem : res Γ E (γ'⁻¹ * γ) ∈ (ptField Γ X E x₀).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro e he
    apply Subtype.ext
    rw [res_apply_coe, Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply, h ⟨e, he⟩, ← AlgEquiv.mul_apply,
      inv_mul_cancel, AlgEquiv.one_apply]
  have hcorr : (ptField Γ X E x₀).fixingSubgroup = stabBar Γ X E x₀ := IntermediateField.fixingSubgroup_fixedField _
  rw [hcorr] at hmem
  obtain ⟨δ, hδ, hδeq⟩ := hmem
  have htriv : res Γ E (γ'⁻¹ * γ * δ⁻¹) = 1 := by rw [map_mul, map_inv, ← hδeq, mul_inv_cancel]
  have h1 := hlev _ htriv (δ • x₀)
  have hδ' : δ • x₀ = x₀ := hδ

  rw [← mul_smul, inv_mul_cancel_right, hδ'] at h1

  calc γ • x₀ = γ' • ((γ'⁻¹ * γ) • x₀) := by rw [mul_smul, smul_inv_smul]
    _ = γ' • x₀ := by rw [h1]

theorem single_mem_span [FiniteDimensional ℚ E] [DecidableEq X] [Fintype X] :
    (Pi.single x₀ (1 : ℚ̄) : X → ℚ̄) ∈ Submodule.span ℚ̄ (Set.range (bvec (Γ := Γ) (E := E) x₀)) := by
  classical
  by_contra hnot
  obtain ⟨f, hf0, hfspan⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance

  have hfb : ∀ a : ptField Γ X E x₀, f (bvec x₀ a) = 0 := by
    intro a
    have : f (bvec x₀ a) ∈ Submodule.map f (Submodule.span ℚ̄ (Set.range (bvec (Γ := Γ) (E := E) x₀))) :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨a, rfl⟩)
    rw [hfspan] at this
    exact (Submodule.mem_bot ℚ̄).mp this

  set w : X → ℚ̄ := fun x => f (Pi.single x 1) with hw
  have hexp : ∀ c : X → ℚ̄, f c = ∑ x, c x * w x := by
    intro c
    conv_lhs => rw [← Finset.univ_sum_single c]
    rw [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have : (Pi.single x (c x) : X → ℚ̄) = c x • (Pi.single x (1 : ℚ̄) : X → ℚ̄) := by
      ext y; simp [Pi.single_apply]
    rw [this, map_smul, smul_eq_mul]

  let O := {x : X // x ∈ MulAction.orbit (↥Γ) x₀}
  let rep : O → Γ := fun x => Classical.choose x.2
  have hrep : ∀ x : O, rep x • x₀ = (x : X) := fun x => Classical.choose_spec x.2
  let χ : O → (ptField Γ X E x₀ →* ℚ̄) := fun x =>
    { toFun := fun a => ((rep x : Γ) : Gal) ((a : E) : ℚ̄)
      map_one' := by simp
      map_mul' := fun a b => by simp }
  have hχ : ∀ (x : O) (a : ptField Γ X E x₀), χ x a = ((rep x : Γ) : Gal) ((a : E) : ℚ̄) := fun _ _ => rfl
  have hχinj : Function.Injective χ := by
    intro x y hxy
    apply Subtype.ext
    rw [← hrep x, ← hrep y]
    exact smul_eq_of_forall_apply_eq hlev fun a => by rw [← hχ x a, ← hχ y a, hxy]
  have hli : LinearIndependent ℚ̄ (fun x : O => ((χ x : ptField Γ X E x₀ →* ℚ̄) : ptField Γ X E x₀ → ℚ̄)) :=
    (linearIndependent_monoidHom (ptField Γ X E x₀) ℚ̄).comp χ hχinj

  have hbO : ∀ (a : ptField Γ X E x₀) (x : O), bvec x₀ a (x : X) = χ x a := by
    intro a x
    rw [hχ]
    conv_lhs => rw [← hrep x]
    exact bvec_smul a (rep x)

  have hrel : ∑ x : O, w (x : X) • ((χ x : ptField Γ X E x₀ →* ℚ̄) : ptField Γ X E x₀ → ℚ̄) = 0 := by
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have h := hfb a
    rw [hexp] at h

    have hsplit : ∑ x, bvec x₀ a x * w x = ∑ x : O, bvec x₀ a (x : X) * w (x : X) := by
      let g : X → ℚ̄ := fun x => bvec x₀ a x * w x
      have e1 : ∑ x ∈ Finset.univ.filter (fun x => x ∈ MulAction.orbit (↥Γ) x₀), g x = ∑ x, g x := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro x _ hx
        rw [Finset.mem_filter, not_and] at hx
        show bvec x₀ a x * w x = 0
        rw [bvec_of_not_mem a (hx (Finset.mem_univ x)), zero_mul]
      have e2 : ∑ x ∈ Finset.univ.filter (fun x => x ∈ MulAction.orbit (↥Γ) x₀), g x = ∑ x : O, g (x : X) :=
        Finset.sum_subtype _ (fun x => by simp) g
      show ∑ x, g x = ∑ x : O, g (x : X)
      rw [← e1, e2]
    rw [hsplit] at h
    rw [← h]
    exact Finset.sum_congr rfl fun x _ => by rw [hbO a x, mul_comm]
  have hw0 := Fintype.linearIndependent_iff.mp hli (fun x : O => w (x : X)) hrel ⟨x₀, MulAction.mem_orbit_self x₀⟩
  exact hf0 hw0

theorem mem_span_fixed [FiniteDimensional ℚ E] [Fintype X] (c : X → ℚ̄) :
    c ∈ Submodule.span ℚ̄ {b : X → ℚ̄ | IsFixedVec Γ X b} := by
  classical
  rw [← Finset.univ_sum_single c]
  refine Submodule.sum_mem _ fun x _ => ?_
  have : (Pi.single x (c x) : X → ℚ̄) = c x • (Pi.single x (1 : ℚ̄) : X → ℚ̄) := by
    ext y; simp [Pi.single_apply]
  rw [this]
  refine Submodule.smul_mem _ _ (Submodule.span_mono ?_ (single_mem_span (E := E) (x₀ := x) hlev))
  rintro _ ⟨a, rfl⟩
  exact isFixedVec_bvec a

theorem exists_fixed_apply_ne [FiniteDimensional ℚ E] [Finite X] {x y : X} (hxy : x ≠ y) :
    ∃ b : X → ℚ̄, IsFixedVec Γ X b ∧ b x ≠ b y := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  by_contra hall
  push Not at hall

  let φ : (X → ℚ̄) →ₗ[ℚ̄] ℚ̄ :=
    (LinearMap.proj (R := ℚ̄) (φ := fun _ : X => ℚ̄) x) - (LinearMap.proj (R := ℚ̄) (φ := fun _ : X => ℚ̄) y)
  have hker : Submodule.span ℚ̄ {b : X → ℚ̄ | IsFixedVec Γ X b} ≤ LinearMap.ker φ := by
    rw [Submodule.span_le]
    intro b hb
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    show b x - b y = 0
    rw [hall b hb, sub_self]
  have h1 := hker (mem_span_fixed (E := E) hlev (Pi.single x (1 : ℚ̄)))
  rw [LinearMap.mem_ker] at h1
  change (Pi.single x (1 : ℚ̄) : X → ℚ̄) x - (Pi.single x (1 : ℚ̄) : X → ℚ̄) y = 0 at h1
  rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hxy), sub_zero] at h1
  exact one_ne_zero h1

end Main

end P2MMultPerm
end

namespace P2MMultHev

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open scoped TensorProduct
open HopfAlgebra

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (D : Subgroup Gal)

abbrev Fd : IntermediateField ℚ ℚ̄ := IntermediateField.fixedField D

def sigmaF (σ : ↥D) : ℚ̄ →ₐ[Fd D] ℚ̄ :=
  { (σ : Gal).toAlgHom.toRingHom with
    commutes' := fun f => (IntermediateField.mem_fixedField_iff D (f : ℚ̄)).mp f.2 σ σ.2 }

@[scoped simp] theorem sigmaF_apply (σ : ↥D) (t : ℚ̄) : sigmaF D σ t = (σ : Gal) t := rfl

variable (A : Type) [CommRing A] [HopfAlgebra (Fd D) A] [Module.Finite (Fd D) A]

abbrev P : Type := WithConv (A →ₐ[Fd D] ℚ̄)

def actPt (σ : ↥D) (ν : P D A) : P D A := WithConv.toConv ((sigmaF D σ).comp (WithConv.ofConv ν))

@[scoped simp] theorem ofConv_actPt_apply (σ : ↥D) (ν : P D A) (a : A) :
    WithConv.ofConv (actPt D A σ ν) a = (σ : Gal) (WithConv.ofConv ν a) := rfl

scoped instance instMulActionP : MulAction (↥D) (P D A) where
  smul := actPt D A
  one_smul ν := rfl
  mul_smul σ τ ν := rfl

theorem smul_P_def (σ : ↥D) (ν : P D A) : σ • ν = actPt D A σ ν := rfl

def ev0 : ℚ̄ ⊗[Fd D] A →ₐ[ℚ̄] (P D A → ℚ̄) :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ̄ _)
    (Pi.algHom (Fd D) _ fun ν : P D A => (WithConv.ofConv ν : A →ₐ[Fd D] ℚ̄)) (fun _ _ => Commute.all _ _)

theorem ev0_tmul (t : ℚ̄) (a : A) (ν : P D A) : ev0 D A (t ⊗ₜ[Fd D] a) ν = t * (WithConv.ofConv ν) a := by
  simp only [ev0, Algebra.TensorProduct.lift_tmul, Pi.mul_apply, Pi.algHom_apply]
  rw [Algebra.ofId_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

def galT0 (σ : ↥D) : ℚ̄ ⊗[Fd D] A →ₐ[Fd D] ℚ̄ ⊗[Fd D] A := Algebra.TensorProduct.map (sigmaF D σ) (AlgHom.id _ A)

theorem galT0_tmul (σ : ↥D) (t : ℚ̄) (a : A) : galT0 D A σ (t ⊗ₜ[Fd D] a) = (σ : Gal) t ⊗ₜ[Fd D] a := rfl

theorem ev0_galT0 (σ : ↥D) (x : ℚ̄ ⊗[Fd D] A) (ν : P D A) :
    ev0 D A (galT0 D A σ x) ν = (σ : Gal) (ev0 D A x (σ⁻¹ • ν)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t a =>
      rw [galT0_tmul, ev0_tmul, ev0_tmul, map_mul, smul_P_def D A, ofConv_actPt_apply, ← AlgEquiv.mul_apply]
      rw [show ((σ : Gal) * ((σ⁻¹ : ↥D) : Gal)) = 1 from by rw [Subgroup.coe_inv, mul_inv_cancel], AlgEquiv.one_apply]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem basis_repr_galT0 {ι : Type} (b : Module.Basis ι (Fd D) A) (σ : ↥D) (x : ℚ̄ ⊗[Fd D] A) (i : ι) :
    (Algebra.TensorProduct.basis ℚ̄ b).repr (galT0 D A σ x) i = (σ : Gal) ((Algebra.TensorProduct.basis ℚ̄ b).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.zero_apply]
  | tmul t a =>
      rw [galT0_tmul, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul,
        Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, smul_eq_mul, map_mul]
      congr 1
      exact ((sigmaF D σ).commutes _).symm ▸ rfl
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem exists_eq_one_tmul_of_fixed (x : ℚ̄ ⊗[Fd D] A) (hx : ∀ σ : ↥D, galT0 D A σ x = x) :
    ∃ a : A, x = (1 : ℚ̄) ⊗ₜ[Fd D] a := by
  classical
  let b := Module.Free.chooseBasis (Fd D) A
  let B := Algebra.TensorProduct.basis ℚ̄ b

  have hcoord : ∀ i, ∃ f : Fd D, (f : ℚ̄) = B.repr x i := by
    intro i
    refine ⟨⟨B.repr x i, (IntermediateField.mem_fixedField_iff D _).mpr fun σ hσ => ?_⟩, rfl⟩
    have := congrArg (fun y => B.repr y i) (hx ⟨σ, hσ⟩)
    exact (basis_repr_galT0 D A b ⟨σ, hσ⟩ x i).symm.trans this
  choose f hf using hcoord

  let g : _ →₀ (Fd D) := Finsupp.onFinset (B.repr x).support f (by
    intro i hi
    rw [Finsupp.mem_support_iff, ← hf i]
    exact fun h0 => hi (Subtype.ext (by rw [h0]; rfl)))
  have hg : ∀ i, g i = f i := fun i => Finsupp.onFinset_apply
  refine ⟨b.repr.symm g, ?_⟩
  apply B.repr.injective
  ext i
  rw [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply, LinearEquiv.apply_symm_apply, hg, ← hf i]
  rfl

theorem sigma_algebraMap (σ : ↥D) (f : Fd D) : (σ : Gal) (algebraMap (Fd D) ℚ̄ f) = algebraMap (Fd D) ℚ̄ f :=
  (sigmaF D σ).commutes f

theorem isAlgebraic_qbar' : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.isAlgebraic ℚ
  rfl
  rfl

theorem isAlgClosure_qbar' : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  (isAlgClosure_iff ℚ (AlgebraicClosure ℚ)).mpr ⟨inferInstance, isAlgebraic_qbar'⟩

scoped instance normal_qbar' : Normal ℚ ℚ̄ := @IsAlgClosure.normal ℚ ℚ̄ _ _ _ (isAlgClosure_qbar')

variable [Finite (P D A)]

theorem exists_level0 : ∃ E : IntermediateField ℚ ℚ̄, FiniteDimensional ℚ E ∧ Normal ℚ E ∧
    ∀ σ : ↥D, (∀ e : ℚ̄, e ∈ E → (σ : Gal) e = e) → ∀ ν : P D A, σ • ν = ν := by
  classical
  haveI : Fintype (P D A) := Fintype.ofFinite _
  obtain ⟨s, hs⟩ : (⊤ : Submodule (Fd D) A).FG := Module.finite_def.mp inferInstance
  let V : Finset ℚ̄ := (Finset.univ ×ˢ s).image fun p : P D A × A => (WithConv.ofConv p.1) p.2
  have hVint : ∀ x ∈ (V : Set ℚ̄), IsIntegral ℚ x := fun x _ => (isAlgebraic_qbar'.isAlgebraic x).isIntegral
  haveI : Finite (↑(V : Set ℚ̄)) := Finite.of_fintype _
  let K : IntermediateField ℚ ℚ̄ := IntermediateField.adjoin ℚ (V : Set ℚ̄)
  haveI hKfd : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin hVint
  let E : IntermediateField ℚ ℚ̄ := IntermediateField.normalClosure ℚ K ℚ̄
  refine ⟨E, normalClosure.is_finiteDimensional ℚ K ℚ̄, normalClosure.normal ℚ K ℚ̄, ?_⟩
  intro σ hσ ν
  have hKE : K ≤ E := IntermediateField.le_normalClosure K
  have hfix : ∀ a ∈ s, (σ : Gal) ((WithConv.ofConv ν) a) = (WithConv.ofConv ν) a := by
    intro a ha
    apply hσ; apply hKE; apply IntermediateField.subset_adjoin
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(ν, a), Finset.mem_product.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩)
  have hall : ∀ a : A, (σ : Gal) ((WithConv.ofConv ν) a) = (WithConv.ofConv ν) a := by
    intro a
    have hmem : a ∈ Submodule.span (Fd D) (s : Set A) := by rw [hs]; trivial
    induction hmem using Submodule.span_induction with
    | mem y hy => exact hfix y hy
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
    | smul r y _ hy =>
        show (σ : Gal) ((WithConv.ofConv ν) (r • y)) = (WithConv.ofConv ν) (r • y)
        rw [Algebra.smul_def, map_mul, AlgHom.commutes, map_mul, sigma_algebraMap D, hy]
  rw [smul_P_def D A]
  show WithConv.toConv ((sigmaF D σ).comp (WithConv.ofConv ν)) = ν
  have : (sigmaF D σ).comp (WithConv.ofConv ν) = WithConv.ofConv ν := AlgHom.ext fun a => hall a
  rw [this]

end

end P2MMultHev
p2m_reactivate "P2MW.S_HopfAlgebra_evalQuot_bijective_of_forall_exists_comp_eq.P2MMultHev"

namespace P2MMultHev

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open scoped TensorProduct
open HopfAlgebra

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (D : Subgroup Gal)
variable (A : Type) [CommRing A] [HopfAlgebra (Fd D) A] [Module.Finite (Fd D) A]
variable (S : Submonoid (P D A)) (hstab : ∀ σ : ↥D, ∀ ν ∈ S, σ • ν ∈ S)

abbrev Xc : Type := {ν : P D A // ν ∉ S}

variable {D A S} in
include hstab in
theorem smul_notMem (σ : ↥D) {ν : P D A} (hν : ν ∉ S) : σ • ν ∉ S := fun h => hν (by
  have := hstab σ⁻¹ _ h
  rwa [inv_smul_smul] at this)

def mulActionXc : MulAction (↥D) (Xc D A S) where
  smul σ x := ⟨σ • x.1, smul_notMem hstab σ x.2⟩
  one_smul x := Subtype.ext (one_smul _ x.1)
  mul_smul σ τ x := Subtype.ext (mul_smul σ τ x.1)

def ext0 : (Xc D A S → ℚ̄) →ₗ[ℚ̄] (P D A → ℚ̄) where
  toFun b ν := by classical exact if h : ν ∈ S then 0 else b ⟨ν, h⟩
  map_add' b c := by
    classical
    funext ν; by_cases h : ν ∈ S <;> simp [h]
  map_smul' t b := by
    classical
    funext ν; by_cases h : ν ∈ S <;> simp [h]

theorem ext0_apply_of_mem (b : Xc D A S → ℚ̄) {ν : P D A} (h : ν ∈ S) : ext0 D A S b ν = 0 := by
  classical
  show (if h : ν ∈ S then 0 else b ⟨ν, h⟩) = 0
  rw [dif_pos h]

theorem ext0_apply_of_notMem (b : Xc D A S → ℚ̄) {ν : P D A} (h : ν ∉ S) : ext0 D A S b ν = b ⟨ν, h⟩ := by
  classical
  show (if h : ν ∈ S then 0 else b ⟨ν, h⟩) = _
  rw [dif_neg h]

def Wsp : Submodule ℚ̄ (P D A → ℚ̄) :=
  Submodule.span ℚ̄ {v | ∃ a ∈ vanishingIdealOfPoints (ptSet S), v = ev0 D A ((1 : ℚ̄) ⊗ₜ[Fd D] a)}

variable (hev0 : Function.Bijective (ev0 D A))
variable [Finite (P D A)]

include hstab hev0 in

theorem ext0_mem_Wsp_of_fixed (b : Xc D A S → ℚ̄)
    (hb : letI := mulActionXc D A S hstab; P2MMultPerm.IsFixedVec D (Xc D A S) b) :
    ext0 D A S b ∈ Wsp D A S := by
  letI := mulActionXc D A S hstab

  have hfixP : ∀ (σ : ↥D) (ν : P D A), ext0 D A S b (σ • ν) = (σ : Gal) (ext0 D A S b ν) := by
    intro σ ν
    by_cases h : ν ∈ S
    · rw [ext0_apply_of_mem D A S b h, ext0_apply_of_mem D A S b (hstab σ ν h), map_zero]
    · rw [ext0_apply_of_notMem D A S b h, ext0_apply_of_notMem D A S b (smul_notMem hstab σ h)]
      exact hb σ ⟨ν, h⟩

  obtain ⟨x, hx⟩ := hev0.2 (ext0 D A S b)
  have hxfix : ∀ σ : ↥D, galT0 D A σ x = x := by
    intro σ
    apply hev0.1
    funext ν
    rw [ev0_galT0, hx, ← hfixP σ, smul_inv_smul]
  obtain ⟨a, rfl⟩ := exists_eq_one_tmul_of_fixed D A x hxfix
  refine Submodule.subset_span ⟨a, ?_, hx.symm⟩
  intro ν hν
  have := congrFun hx (WithConv.toConv ν)
  rw [ev0_tmul, one_mul, ext0_apply_of_mem D A S b hν] at this
  exact this

include hstab hev0 in

theorem mem_Wsp_of_vanish (v : P D A → ℚ̄) (hv : ∀ ν ∈ S, v ν = 0) : v ∈ Wsp D A S := by
  classical
  letI := mulActionXc D A S hstab
  haveI : Fintype (Xc D A S) := Fintype.ofFinite _

  obtain ⟨E, hEfd, hEn, hlev0⟩ := exists_level0 D A
  haveI := hEfd; haveI := hEn
  have hlev : ∀ γ : ↥D, P2MMultPerm.res D E γ = 1 → ∀ x : Xc D A S, γ • x = x := by
    intro γ hγ x
    apply Subtype.ext
    apply hlev0 γ
    intro e he
    have := P2MMultPerm.res_apply_coe (Γ := D) E γ ⟨e, he⟩
    rw [hγ] at this
    exact this.symm

  have hc := P2MMultPerm.mem_span_fixed (Γ := D) (X := Xc D A S) (E := E) hlev (fun x => v x.1)

  have hv' : v = ext0 D A S (fun x => v x.1) := by
    funext ν
    by_cases h : ν ∈ S
    · rw [ext0_apply_of_mem D A S _ h, hv ν h]
    · rw [ext0_apply_of_notMem D A S _ h]
  rw [hv', ← Submodule.mem_comap]
  revert hc
  apply Submodule.span_le.mpr
  intro b hb
  exact ext0_mem_Wsp_of_fixed D A S hstab hev0 b hb

def resS : (P D A → ℚ̄) →ₗ[ℚ̄] (↥S → ℚ̄) where
  toFun v ν := v ν.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem resS_surjective : Function.Surjective (resS D A S) := by
  classical
  intro w
  refine ⟨fun ν => if h : ν ∈ S then w ⟨ν, h⟩ else 0, ?_⟩
  funext ν
  show (if h : (ν : P D A) ∈ S then w ⟨ν, h⟩ else 0) = w ν
  rw [dif_pos ν.2]

theorem ker_resS_le_Wsp' (v : P D A → ℚ̄) (hv : v ∈ LinearMap.ker (resS D A S)) : ∀ ν ∈ S, v ν = 0 := by
  intro ν hν
  have := congrFun (LinearMap.mem_ker.mp hv) ⟨ν, hν⟩
  exact this

include hstab hev0 in
theorem finrank_ker_resS_le :
    Module.finrank ℚ̄ ↥(LinearMap.ker (resS D A S)) ≤
      Module.finrank (Fd D) ↥((vanishingIdealOfPoints (ptSet S)).restrictScalars (Fd D)) := by
  classical

  let I := (vanishingIdealOfPoints (ptSet S)).restrictScalars (Fd D)
  let bI := Module.Free.chooseBasis (Fd D) ↥I
  let u : Module.Free.ChooseBasisIndex (Fd D) ↥I → (P D A → ℚ̄) := fun j => ev0 D A ((1 : ℚ̄) ⊗ₜ[Fd D] ((bI j : ↥I) : A))
  have hW : Wsp D A S ≤ Submodule.span ℚ̄ (Set.range u) := by
    apply Submodule.span_le.mpr
    rintro v ⟨a, ha, rfl⟩

    have hrepr := bI.linearCombination_repr ⟨a, ha⟩
    have : a = ((Finsupp.linearCombination (Fd D) (fun j => (bI j : ↥I))) (bI.repr ⟨a, ha⟩) : ↥I) := by
      rw [hrepr]
    rw [this, Finsupp.linearCombination_apply, Finsupp.sum]
    simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul_of_tower, TensorProduct.tmul_sum,
      TensorProduct.tmul_smul, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← IsScalarTower.algebraMap_smul ℚ̄, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  calc Module.finrank ℚ̄ ↥(LinearMap.ker (resS D A S))
      ≤ Module.finrank ℚ̄ ↥(Submodule.span ℚ̄ (Set.range u)) := by
        apply Submodule.finrank_mono
        intro v hv
        exact hW (mem_Wsp_of_vanish D A S hstab hev0 v (ker_resS_le_Wsp' D A S v hv))
    _ ≤ Fintype.card (Module.Free.ChooseBasisIndex (Fd D) ↥I) := finrank_range_le_card u
    _ = Module.finrank (Fd D) ↥I := (Module.finrank_eq_card_chooseBasisIndex (Fd D) ↥I).symm

include hstab hev0 in

theorem finrank_QS_le : Module.finrank (Fd D) (pointQuot S) ≤ Nat.card ↥S := by
  classical
  haveI : Fintype (P D A) := Fintype.ofFinite _
  haveI : Fintype ↥S := Fintype.ofFinite _

  have hP : Module.finrank (Fd D) A = Fintype.card (P D A) := by
    rw [← Module.finrank_baseChange (R := ℚ̄), LinearEquiv.finrank_eq (AlgEquiv.ofBijective _ hev0).toLinearEquiv,
      Module.finrank_fintype_fun_eq_card]

  have hrn := LinearMap.finrank_range_add_finrank_ker (resS D A S)
  rw [LinearMap.range_eq_top.mpr (resS_surjective D A S), finrank_top, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card] at hrn

  have hq := Submodule.finrank_quotient_add_finrank ((vanishingIdealOfPoints (ptSet S)).restrictScalars (Fd D))
  have hQ : Module.finrank (Fd D) (pointQuot S) =
      Module.finrank (Fd D) (A ⧸ (vanishingIdealOfPoints (ptSet S)).restrictScalars (Fd D)) :=
    (LinearEquiv.finrank_eq (Submodule.Quotient.restrictScalarsEquiv (Fd D) (vanishingIdealOfPoints (ptSet S)))).symm
  have hk := finrank_ker_resS_le D A S hstab hev0
  rw [Nat.card_eq_fintype_card]
  omega

theorem evalQuot_surjective : Function.Surjective (evalQuot S) := by
  classical
  haveI : Fintype ↥S := Fintype.ofFinite _
  suffices h : LinearMap.range (evalQuot S).toLinearMap = ⊤ from LinearMap.range_eq_top.mp h
  by_contra hne
  obtain ⟨f, hf0, hfr⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
  have hker : ∀ x, f (evalQuot S x) = 0 := by
    intro x
    have : f (evalQuot S x) ∈ Submodule.map f (LinearMap.range (evalQuot S).toLinearMap) := Submodule.mem_map_of_mem ⟨x, rfl⟩
    rw [hfr] at this
    exact (Submodule.mem_bot ℚ̄).mp this
  set w : ↥S → ℚ̄ := fun ν => f (Pi.single ν 1)
  have hexp : ∀ c : ↥S → ℚ̄, f c = ∑ ν, c ν * w ν := by
    intro c
    conv_lhs => rw [← Finset.univ_sum_single c]
    rw [map_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    have : (Pi.single ν (c ν) : ↥S → ℚ̄) = c ν • (Pi.single ν (1 : ℚ̄) : ↥S → ℚ̄) := by
      ext ψ; simp [Pi.single_apply]
    rw [this, map_smul, smul_eq_mul]

  let χ : ↥S → (A →* ℚ̄) := fun ν => (WithConv.ofConv ν.1 : A →ₐ[Fd D] ℚ̄).toMonoidHom
  have hχ : Function.Injective χ := by
    intro ν ψ h
    apply Subtype.ext
    have : WithConv.ofConv ν.1 = WithConv.ofConv ψ.1 := AlgHom.ext fun a => by
      exact congrArg (fun m : A →* ℚ̄ => m a) h
    calc ν.1 = WithConv.toConv (WithConv.ofConv ν.1) := rfl
      _ = WithConv.toConv (WithConv.ofConv ψ.1) := by rw [this]
      _ = ψ.1 := rfl
  have hli := (linearIndependent_monoidHom A ℚ̄).comp χ hχ
  have hrel : ∑ ν, w ν • ((χ ν : A →* ℚ̄) : A → ℚ̄) = 0 := by
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have := hker ((1 : ℚ̄) ⊗ₜ[Fd D] Ideal.Quotient.mk _ a)
    rw [hexp] at this
    rw [← this]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [evalQuot_tmul, one_mul, mul_comm]
    rfl
  have hw0 : ∀ ν, w ν = 0 := Fintype.linearIndependent_iff.mp hli w hrel
  apply hf0
  apply LinearMap.ext
  intro c
  rw [hexp c, LinearMap.zero_apply]
  exact Finset.sum_eq_zero fun ν _ => by rw [hw0 ν, mul_zero]

include hstab hev0 in

theorem evalQuot_bijective : Function.Bijective (evalQuot S) := by
  classical
  haveI : Fintype ↥S := Fintype.ofFinite _
  have hsurj := evalQuot_surjective D A S
  have hsurj' : Function.Surjective (evalQuot S).toLinearMap := hsurj

  have h1 : Module.finrank ℚ̄ (ℚ̄ ⊗[Fd D] pointQuot S) ≤ Module.finrank ℚ̄ (↥S → ℚ̄) := by
    rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card]
    exact finrank_QS_le D A S hstab hev0
  have h2 : Module.finrank ℚ̄ (↥S → ℚ̄) ≤ Module.finrank ℚ̄ (ℚ̄ ⊗[Fd D] pointQuot S) := by
    have := LinearMap.finrank_range_le (evalQuot S).toLinearMap
    rw [LinearMap.range_eq_top.mpr hsurj', finrank_top] at this
    exact this
  have heq : Module.finrank ℚ̄ (ℚ̄ ⊗[Fd D] pointQuot S) = Module.finrank ℚ̄ (↥S → ℚ̄) := le_antisymm h1 h2
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq (f := (evalQuot S).toLinearMap)).mpr hsurj', hsurj⟩

end
p2m_reactivate "P2MW.S_HopfAlgebra_evalQuot_bijective_of_forall_exists_comp_eq.P2MMultHev"

end P2MMultHev
p2m_reactivate "P2MW.S_HopfAlgebra_evalQuot_bijective_of_forall_exists_comp_eq.P2MMultHev"

namespace P2MMultHev

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open scoped TensorProduct
open HopfAlgebra

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (D : Subgroup Gal)
variable (A : Type) [CommRing A] [HopfAlgebra (Fd D) A] [Module.Finite (Fd D) A]
variable (S : Submonoid (P D A))

def jS : pointQuot S →ₗ[Fd D] (↥S → ℚ̄) where
  toFun aq ν := liftPoint (ptSet S) (WithConv.ofConv ν.1) (ofConv_mem_ptSet ν) aq
  map_add' aq bq := by funext ν; simp only [map_add, Pi.add_apply]
  map_smul' c aq := by funext ν; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

theorem jS_mk (a : A) (ν : ↥S) : jS D A S (Ideal.Quotient.mk _ a) ν = (WithConv.ofConv ν.1) a := rfl

theorem jS_injective : Function.Injective (jS D A S) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro aq haq
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective aq
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  intro ν hν
  have := congrFun haq ⟨WithConv.toConv ν, hν⟩
  exact this

def testAt (ν' : ↥S) : pointQuot S ⊗[Fd D] pointQuot S →ₗ[Fd D] pointQuot S ⊗[Fd D] ℚ̄ :=
  LinearMap.lTensor (pointQuot S) (liftPoint (ptSet S) (WithConv.ofConv ν'.1) (ofConv_mem_ptSet ν')).toLinearMap

theorem testAt_tmul (ν' : ↥S) (aq bq : pointQuot S) :
    testAt D A S ν' (aq ⊗ₜ[Fd D] bq) = aq ⊗ₜ[Fd D] liftPoint (ptSet S) (WithConv.ofConv ν'.1) (ofConv_mem_ptSet ν') bq := rfl

variable [Finite (P D A)]

theorem piRight_lTensor_jS [Fintype ↥S] [DecidableEq ↥S] (y : pointQuot S ⊗[Fd D] pointQuot S) (ν' : ↥S) :
    (TensorProduct.piRight (Fd D) (Fd D) (pointQuot S) (fun _ : ↥S => ℚ̄)) (LinearMap.lTensor (pointQuot S) (jS D A S) y) ν'
      = testAt D A S ν' y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply]
  | tmul aq bq =>
      rw [LinearMap.lTensor_tmul, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, testAt_tmul]
      rfl
  | add y z hy hz => simp only [map_add, Pi.add_apply, hy, hz]

omit [Finite (P D A)] in
theorem evalQuot_comm_testAt (ν ν' : ↥S) (z : pointQuot S ⊗[Fd D] pointQuot S) :
    evalQuot S (TensorProduct.comm (Fd D) (pointQuot S) ℚ̄ (testAt D A S ν' z)) ν
      = evalPair (ptSet S) (WithConv.ofConv ν.1) (WithConv.ofConv ν'.1) (ofConv_mem_ptSet ν) (ofConv_mem_ptSet ν') z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply]
  | tmul aq bq =>
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective aq
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective bq
      rw [testAt_tmul, TensorProduct.comm_tmul, liftPoint_mk, evalQuot_tmul, evalPair_tmul, mul_comm]
  | add y z hy hz => rw [map_add, map_add, map_add, Pi.add_apply, hy, hz, map_add]

theorem sep_of_evalQuot_injective (hinj : Function.Injective (evalQuot S))
    (x : pointQuot S ⊗[Fd D] pointQuot S)
    (hx : ∀ ν ν' (hν : ν ∈ ptSet S) (hν' : ν' ∈ ptSet S), evalPair (ptSet S) ν ν' hν hν' x = 0) :
    x = 0 := by
  classical
  haveI : Fintype ↥S := Fintype.ofFinite _
  have hΘinj : Function.Injective
      ((TensorProduct.piRight (Fd D) (Fd D) (pointQuot S) (fun _ : ↥S => ℚ̄)).toLinearMap ∘ₗ
        LinearMap.lTensor (pointQuot S) (jS D A S)) := by
    rw [LinearMap.coe_comp]
    exact (TensorProduct.piRight (Fd D) (Fd D) (pointQuot S) (fun _ : ↥S => ℚ̄)).injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap _ (jS_injective D A S))
  apply hΘinj
  rw [map_zero]
  funext ν'
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, piRight_lTensor_jS, Pi.zero_apply]

  have h0 : TensorProduct.comm (Fd D) (pointQuot S) ℚ̄ (testAt D A S ν' x) = 0 := by
    apply hinj
    rw [map_zero]
    funext ν
    rw [evalQuot_comm_testAt, Pi.zero_apply]
    exact hx _ _ _ _
  simpa using congrArg (TensorProduct.comm (Fd D) (pointQuot S) ℚ̄).symm h0

end
p2m_reactivate "P2MW.S_HopfAlgebra_evalQuot_bijective_of_forall_exists_comp_eq.P2MMultHev"

end P2MMultHev
p2m_reactivate "P2MW.S_HopfAlgebra_evalQuot_bijective_of_forall_exists_comp_eq.P2MMultHev"

open scoped TensorProduct

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

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
    (S : Submonoid (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ)))
    (hstab : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ D → ∀ ν ∈ S, ∃ ν' ∈ S,
      ∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) :
    Function.Bijective (HopfAlgebra.evalQuot S) ∧
      ∀ x : HopfAlgebra.pointQuot S ⊗[↥(IntermediateField.fixedField D)] HopfAlgebra.pointQuot S,
        (∀ ν ν' (hν : ν ∈ HopfAlgebra.ptSet S) (hν' : ν' ∈ HopfAlgebra.ptSet S),
            HopfAlgebra.evalPair (HopfAlgebra.ptSet S) ν ν' hν hν' x = 0) → x = 0 := by

  have hstab' : ∀ σ : ↥D, ∀ ν ∈ S, σ • ν ∈ S := by
    intro σ ν hν
    obtain ⟨ν', hν', h⟩ := hstab σ σ.2 ν hν
    have : σ • ν = ν' := by
      apply WithConv.ext; apply AlgHom.ext; intro a
      exact (h a).symm
    rw [this]; exact hν'
  have hbij := P2MMultHev.evalQuot_bijective D A S hstab' hev
  exact ⟨hbij, P2MMultHev.sep_of_evalQuot_injective D A S hbij.1⟩

end S_HopfAlgebra_evalQuot_bijective_of_forall_exists_comp_eq
end P2MW
export P2MW.S_HopfAlgebra_evalQuot_bijective_of_forall_exists_comp_eq (solution)
