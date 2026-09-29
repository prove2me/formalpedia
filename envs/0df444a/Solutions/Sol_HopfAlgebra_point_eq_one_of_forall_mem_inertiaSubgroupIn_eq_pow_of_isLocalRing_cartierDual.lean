-- Prove2me | solution 1 for HopfAlgebra.point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/d68188dc-238f-5967-88e8-40d6a527715d

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CharacterClosure
import Theorems.Thm_ValuationSubring_exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq
import Theorems.Thm_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_multiplicativeType_sub
import Theorems.Thm_CartierDual_exists_algEquiv_monoidAlgebra_pi
import Theorems.Thm_CartierDual_dualBaseChangeLin_bijective_integral
import Theorems.Thm_GaloisRep_irreducible_natCast_ratLocalizedAt
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_IsLocalRing_tensorProduct_of_algHom_retraction_of_isLocalHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open scoped TensorProduct

namespace A2Glue

section S0

variable {p : ℕ} (O : Subring (AlgebraicClosure ℚ))
  (hOrat : ∀ r : ℚ, r.den.Coprime p → algebraMap ℚ (AlgebraicClosure ℚ) r ∈ O)

@[reducible] noncomputable def algebraRatLocalizedAt : Algebra (GaloisRep.ratLocalizedAt p) O :=
  ((algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)).codRestrict O
    (fun r => hOrat r r.2)).toAlgebra

theorem algebraMap_ratLocalizedAt_coe (r : GaloisRep.ratLocalizedAt p) :
    letI := algebraRatLocalizedAt O hOrat
    ((algebraMap (GaloisRep.ratLocalizedAt p) O r : O) : AlgebraicClosure ℚ)
      = algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ) := rfl

theorem isScalarTower_ratLocalizedAt :
    letI := algebraRatLocalizedAt O hOrat
    @IsScalarTower (GaloisRep.ratLocalizedAt p) O (AlgebraicClosure ℚ)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  letI := algebraRatLocalizedAt O hOrat
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem isLocalHom_ratLocalizedAt (hp : p.Prime) [IsLocalRing O] (hOp : ¬ IsUnit ((p : ℕ) : O)) :
    letI := algebraRatLocalizedAt O hOrat
    IsLocalHom (algebraMap (GaloisRep.ratLocalizedAt p) O) := by
  letI := algebraRatLocalizedAt O hOrat
  haveI := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p hp
  refine ((IsLocalRing.local_hom_TFAE (algebraMap (GaloisRep.ratLocalizedAt p) O)).out 2 0).mp ?_
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp
      (GaloisRep.irreducible_natCast_ratLocalizedAt p hp),
    Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff, map_natCast]
  exact hOp

theorem isLocalHom_ratLocalizedAt_of_irreducible (hp : p.Prime)
    (hOdvr : IsDiscreteValuationRing O) (hOirr : Irreducible ((p : ℕ) : O)) :
    letI := algebraRatLocalizedAt O hOrat
    IsLocalHom (algebraMap (GaloisRep.ratLocalizedAt p) O) :=
  isLocalHom_ratLocalizedAt O hOrat hp hOirr.not_isUnit

theorem isLocalRing_ratLocalizedAt (hp : p.Prime) : IsLocalRing (GaloisRep.ratLocalizedAt p) :=
  haveI := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p hp
  inferInstance

end S0

section S1

open WithConv

variable {R S L H : Type*} [CommRing R] [CommRing S] [CommRing L] [CommRing H]
  [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L]

section alg
variable [Algebra R H]

noncomputable def liftPt (φ : WithConv (H →ₐ[R] L)) : WithConv (S ⊗[R] H →ₐ[S] L) :=
  toConv (Algebra.TensorProduct.lift (Algebra.ofId S L) φ.ofConv fun _ _ => .all _ _)

theorem liftPt_tmul (φ : WithConv (H →ₐ[R] L)) (s : S) (h : H) :
    (liftPt (S := S) φ).ofConv (s ⊗ₜ[R] h) = algebraMap S L s * φ.ofConv h := by
  show Algebra.TensorProduct.lift (Algebra.ofId S L) φ.ofConv (fun _ _ => .all _ _) (s ⊗ₜ[R] h) = _
  rw [Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]

theorem liftPt_one_tmul (φ : WithConv (H →ₐ[R] L)) (h : H) :
    (liftPt (S := S) φ).ofConv ((1 : S) ⊗ₜ[R] h) = φ.ofConv h := by
  rw [liftPt_tmul, map_one, one_mul]

noncomputable def restrPt (ψ : WithConv (S ⊗[R] H →ₐ[S] L)) : WithConv (H →ₐ[R] L) :=
  toConv ((ψ.ofConv.restrictScalars R).comp Algebra.TensorProduct.includeRight)

theorem restrPt_apply (ψ : WithConv (S ⊗[R] H →ₐ[S] L)) (h : H) :
    (restrPt (R := R) ψ).ofConv h = ψ.ofConv ((1 : S) ⊗ₜ[R] h) := rfl

theorem restrPt_liftPt (φ : WithConv (H →ₐ[R] L)) : restrPt (liftPt (S := S) φ) = φ := by
  apply WithConv.ext
  apply AlgHom.ext
  intro h
  rw [restrPt_apply, liftPt_one_tmul]

theorem liftPt_restrPt (ψ : WithConv (S ⊗[R] H →ₐ[S] L)) : liftPt (restrPt (R := R) ψ) = ψ := by
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s h =>
    rw [liftPt_tmul, restrPt_apply, ← Algebra.smul_def, ← map_smul, TensorProduct.smul_tmul',
      smul_eq_mul, mul_one]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem comp_liftPt (σ : L →ₐ[S] L) (φ : WithConv (H →ₐ[R] L)) :
    σ.comp (liftPt (S := S) φ).ofConv
      = (liftPt (S := S) (toConv ((σ.restrictScalars R).comp φ.ofConv))).ofConv := by
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s h =>
    rw [AlgHom.comp_apply, liftPt_tmul, liftPt_tmul, map_mul, AlgHom.commutes]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end alg

section bialg
variable [Bialgebra R H]

theorem liftPt_mul (φ ψ : WithConv (H →ₐ[R] L)) :
    liftPt (S := S) (φ * ψ) = liftPt (S := S) φ * liftPt (S := S) ψ := by
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s h =>
    let rr := Coalgebra.Repr.arbitrary R h
    have hco : Coalgebra.comul (R := S) (s ⊗ₜ[R] h)
        = ∑ i ∈ rr.index, ((1 : S) ⊗ₜ[R] rr.left i) ⊗ₜ[S] (s ⊗ₜ[R] rr.right i) := by
      rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, ← rr.eq, TensorProduct.tmul_sum,
        map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
    rw [liftPt_tmul, AlgHom.convMul_apply, AlgHom.convMul_apply, ← rr.eq, map_sum, Finset.mul_sum,
      hco, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, liftPt_one_tmul,
      liftPt_tmul]
    ring
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem liftPt_one : liftPt (S := S) (1 : WithConv (H →ₐ[R] L)) = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s h =>
    rw [liftPt_tmul, AlgHom.convOne_apply, AlgHom.convOne_apply, TensorProduct.counit_tmul,
      CommSemiring.counit_apply, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
      mul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem liftPt_pow (φ : WithConv (H →ₐ[R] L)) (n : ℕ) :
    liftPt (S := S) (φ ^ n) = liftPt (S := S) φ ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, liftPt_one]
  | succ n ih => rw [pow_succ, pow_succ, liftPt_mul, ih]

noncomputable def liftPtEquiv : WithConv (H →ₐ[R] L) ≃* WithConv (S ⊗[R] H →ₐ[S] L) where
  toFun := liftPt
  invFun := restrPt
  left_inv := restrPt_liftPt
  right_inv := liftPt_restrPt
  map_mul' := liftPt_mul

theorem transport_eq_pow {Γ : Type*} (I : Set Γ) (act : Γ → L → L) (n : Γ → ℕ)
    (f : WithConv (H →ₐ[R] L))
    (hf : ∀ σ ∈ I, ∀ g : WithConv (H →ₐ[R] L),
      (∀ h : H, g.ofConv h = act σ (f.ofConv h)) → g = f ^ n σ) :
    ∀ σ ∈ I, ∀ g : WithConv (S ⊗[R] H →ₐ[S] L),
      (∀ x : S ⊗[R] H, g.ofConv x = act σ ((liftPt (S := S) f).ofConv x)) →
        g = liftPt (S := S) f ^ n σ := by
  intro σ hσ g hg
  have h1 : restrPt (R := R) g = f ^ n σ := by
    refine hf σ hσ _ fun h => ?_
    rw [restrPt_apply, hg, liftPt_one_tmul]
  rw [← liftPt_restrPt (R := R) g, h1, liftPt_pow]

end bialg

end S1

section S1b

open WithConv

variable {R L H : Type*} [CommRing R] [CommRing L] [Algebra R L] [CommRing H] [HopfAlgebra R H]

noncomputable def antipodeAlgHom : H →ₐ[R] H :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode R) HopfAlgebra.antipode_one fun a b => by
    rw [HopfAlgebra.antipode_mul, mul_comm]

@[scoped simp] theorem antipodeAlgHom_apply (h : H) :
    antipodeAlgHom (R := R) h = HopfAlgebra.antipode R h := rfl

noncomputable def invPt (κ : WithConv (H →ₐ[R] L)) : WithConv (H →ₐ[R] L) :=
  toConv (κ.ofConv.comp (antipodeAlgHom (R := R)))

theorem invPt_apply (κ : WithConv (H →ₐ[R] L)) (h : H) :
    (invPt κ).ofConv h = κ.ofConv (HopfAlgebra.antipode R h) := rfl

theorem invPt_mul (κ : WithConv (H →ₐ[R] L)) : invPt κ * κ = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro g
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
  let rr := Coalgebra.Repr.arbitrary R g
  conv_lhs => rw [← rr.eq]
  simp only [map_sum, Algebra.TensorProduct.lift_tmul]
  rw [← κ.ofConv.commutes, ← HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit rr, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, invPt_apply]

noncomputable scoped instance instCommGroupPoints [Coalgebra.IsCocomm R H] :
    CommGroup (WithConv (H →ₐ[R] L)) :=
  { (inferInstance : CommMonoid (WithConv (H →ₐ[R] L))) with
    inv := invPt
    inv_mul_cancel := invPt_mul }

theorem inv_def [Coalgebra.IsCocomm R H] (κ : WithConv (H →ₐ[R] L)) : κ⁻¹ = invPt κ := rfl

end S1b

section S7

theorem isIdempotentElem_eq_zero_or_one_of_isLocalRing {A : Type*} [CommRing A] [IsLocalRing A]
    {e : A} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
  · exact Or.inr (hu.mul_left_cancel (he.eq.trans (mul_one e).symm))
  · exact Or.inl (sub_eq_self.mp (hu.mul_left_cancel (he.one_sub.eq.trans (mul_one _).symm)))

theorem not_isLocalRing_of_injective_ringHom_pi {Γ O A : Type*} [CommRing O] [Nontrivial O]
    [CommRing A] [DecidableEq Γ] {x y : Γ} (hxy : x ≠ y)
    (f : (Γ → O) →+* A) (hf : Function.Injective f) : ¬ IsLocalRing A := by
  intro hA
  have he : IsIdempotentElem (Pi.single x (1 : O) : Γ → O) := by
    rw [IsIdempotentElem, ← Pi.single_mul, mul_one]
  rcases isIdempotentElem_eq_zero_or_one_of_isLocalRing (he.map f) with h0 | h1
  · have : (Pi.single x (1 : O) : Γ → O) = 0 := hf (by rw [h0, map_zero])
    exact (one_ne_zero (α := O)) (by simpa using congr_fun this x)
  · have : (Pi.single x (1 : O) : Γ → O) = 1 := hf (by rw [h1, map_one])
    exact (zero_ne_one (α := O)) (by simpa [Pi.single_eq_of_ne hxy.symm] using congr_fun this y)

end S7

section SMisc

open WithConv

theorem nontrivial_of_bialgebra (R H : Type*) [CommRing R] [Nontrivial R] [Semiring H]
    [Bialgebra R H] : Nontrivial H :=
  (Bialgebra.counitAlgHom R H).toRingHom.domain_nontrivial

section compPt
variable {R L L' H : Type*} [CommRing R] [CommRing L] [CommRing L'] [Algebra R L] [Algebra R L']
  [CommRing H] [Bialgebra R H]

noncomputable def compPt (τ : L →ₐ[R] L') : WithConv (H →ₐ[R] L) →* WithConv (H →ₐ[R] L') where
  toFun φ := toConv (τ.comp φ.ofConv)
  map_one' := by
    apply WithConv.ext
    apply AlgHom.ext
    intro h
    show τ ((1 : WithConv (H →ₐ[R] L)).ofConv h) = (1 : WithConv (H →ₐ[R] L')).ofConv h
    rw [AlgHom.convOne_apply, AlgHom.convOne_apply, AlgHom.commutes]
  map_mul' f g := by
    show toConv (τ.comp (f * g).ofConv) = _
    rw [AlgHom.comp_convMul_distrib]

@[scoped simp] theorem compPt_apply (τ : L →ₐ[R] L') (φ : WithConv (H →ₐ[R] L)) (h : H) :
    (compPt τ φ).ofConv h = τ (φ.ofConv h) := rfl

end compPt

theorem pow_eq_pow_of_forall_rootOfUnity {p : ℕ} [hp : Fact p.Prime] {a b : ℕ}
    (h : ∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → ζ ^ a = ζ ^ b)
    {M : Type*} [Monoid M] {x : M} (hx : x ^ p = 1) : x ^ a = x ^ b := by
  haveI : NeZero ((p : ℕ) : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := AlgebraicClosure ℚ) (n := p)
  have hp0 : 0 < p := hp.out.pos
  have hab : a % p = b % p := by
    have := h ζ hζ.pow_eq_one
    rw [pow_eq_pow_mod a hζ.pow_eq_one, pow_eq_pow_mod b hζ.pow_eq_one] at this
    exact hζ.pow_inj (Nat.mod_lt _ hp0) (Nat.mod_lt _ hp0) this
  rw [pow_eq_pow_mod a hx, pow_eq_pow_mod b hx, hab]

def withConvEquiv (X : Type*) : WithConv X ≃ X := ⟨WithConv.ofConv, WithConv.toConv, fun _ => rfl, fun _ => rfl⟩

theorem finite_points_of_natCard (R H K : Type*) [CommRing R] [Nontrivial R] [CommRing H]
    [Bialgebra R H] [Module.Finite R H] [Module.Free R H] [CommRing K] [Algebra R K]
    (hcard : Nat.card (H →ₐ[R] K) = Module.finrank R H) :
    Finite (WithConv (H →ₐ[R] K)) := by
  haveI := nontrivial_of_bialgebra R H
  have hpos : 0 < Module.finrank R H := by
    rw [Module.finrank_eq_card_chooseBasisIndex]
    exact Fintype.card_pos_iff.mpr (Module.Free.chooseBasis R H).index_nonempty
  haveI : Finite (H →ₐ[R] K) := Nat.finite_of_card_ne_zero (hcard ▸ hpos.ne')
  exact Finite.of_equiv _ (withConvEquiv (H →ₐ[R] K)).symm

def AlgEquiv.toAlgHomOfForallMemEq {K L : Type*} [Field K] [Field L] [Algebra K L]
    (O : Subring L) (σ : L ≃ₐ[K] L) (hσ : ∀ x ∈ O, σ x = x) : L →ₐ[O] L :=
  { σ.toRingEquiv.toRingHom with commutes' := fun r => hσ r r.2 }

@[scoped simp] theorem AlgEquiv.toAlgHomOfForallMemEq_apply {K L : Type*} [Field K] [Field L]
    [Algebra K L] (O : Subring L) (σ : L ≃ₐ[K] L) (hσ : ∀ x ∈ O, σ x = x) (y : L) :
    AlgEquiv.toAlgHomOfForallMemEq O σ hσ y = σ y := rfl

p2m_reactivate "P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual.A2Glue.AlgEquiv"
end SMisc
p2m_reactivate "P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual.A2Glue.AlgEquiv"

section S1c

open WithConv

variable {R L H H' : Type*} [CommRing R] [CommRing L] [Algebra R L]
  [CommRing H] [CommRing H'] [Bialgebra R H] [Bialgebra R H']

noncomputable def precompPt (θ : H →ₐc[R] H') : WithConv (H' →ₐ[R] L) →* WithConv (H →ₐ[R] L) where
  toFun φ := toConv (φ.ofConv.comp (θ : H →ₐ[R] H'))
  map_one' := by
    apply WithConv.ext
    apply AlgHom.ext
    intro h
    show (1 : WithConv (H' →ₐ[R] L)).ofConv (θ h) = (1 : WithConv (H →ₐ[R] L)).ofConv h
    rw [AlgHom.convOne_apply, AlgHom.convOne_apply, CoalgHomClass.counit_comp_apply]
  map_mul' f g := by
    show toConv (AlgHom.comp (f * g).ofConv (θ : H →ₐ[R] H')) = _
    rw [AlgHom.convMul_comp_bialgHom_distrib]

@[scoped simp] theorem precompPt_apply (θ : H →ₐc[R] H') (φ : WithConv (H' →ₐ[R] L)) (h : H) :
    (precompPt θ φ).ofConv h = φ.ofConv (θ h) := rfl

theorem precompPt_injective (θ : H →ₐc[R] H') (hθ : Function.Surjective θ) :
    Function.Injective (precompPt (L := L) θ) := by
  intro φ ψ h
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := hθ x
  have := congrArg (fun χ : WithConv (H →ₐ[R] L) => χ.ofConv a) h
  simpa using this

end S1c
p2m_reactivate "P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual.A2Glue.AlgEquiv"

section S1d

open WithConv

variable {G R L H : Type*} [Monoid G] [CommRing R] [CommRing L] [Algebra R L]
  [CommRing H] [Bialgebra R H]

@[reducible] noncomputable def pointsDistribMulAction (ρ : G →* (L →ₐ[R] L)) :
    DistribMulAction G (Additive (WithConv (H →ₐ[R] L))) where
  smul g m := Additive.ofMul (compPt (ρ g) (Additive.toMul m))
  one_smul m := by
    show Additive.ofMul (compPt (ρ 1) (Additive.toMul m)) = m
    rw [map_one]
    rfl
  mul_smul g g' m := by
    show Additive.ofMul (compPt (ρ (g * g')) (Additive.toMul m)) =
      Additive.ofMul (compPt (ρ g) (Additive.toMul (Additive.ofMul (compPt (ρ g') (Additive.toMul m)))))
    rw [map_mul]
    rfl
  smul_zero g := by
    show Additive.ofMul (compPt (ρ g) (Additive.toMul 0)) = 0
    rw [toMul_zero, map_one, ofMul_one]
  smul_add g m m' := by
    show Additive.ofMul (compPt (ρ g) (Additive.toMul (m + m'))) = _
    rw [toMul_add, map_mul, ofMul_mul]
    rfl

theorem pointsDistribMulAction_smul_def (ρ : G →* (L →ₐ[R] L)) (g : G)
    (m : Additive (WithConv (H →ₐ[R] L))) :
    letI := pointsDistribMulAction (H := H) ρ
    g • m = Additive.ofMul (compPt (ρ g) (Additive.toMul m)) := rfl

end S1d
p2m_reactivate "P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual.A2Glue.AlgEquiv"

section S1e

noncomputable def galRestrict (S : Subring ℚ) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (AlgebraicClosure ℚ →ₐ[S] AlgebraicClosure ℚ) where
  toFun σ := (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).restrictScalars S
  map_one' := by ext x; rfl
  map_mul' σ τ := by ext x; rfl

@[scoped simp] theorem galRestrict_apply (S : Subring ℚ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : AlgebraicClosure ℚ) : galRestrict S σ x = σ x := rfl

end S1e
p2m_reactivate "P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual.A2Glue.AlgEquiv"

end A2Glue
p2m_reactivate "P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual.A2Glue.AlgEquiv P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual.A2Glue"

example {R L H : Type} [CommRing R] [CommRing L] [CommRing H] [Algebra R L] [Bialgebra R H]
    (g : WithConv (H →ₐ[R] L)) (h : H) : g h = g.ofConv h := rfl

namespace A2Glue

section S4
open scoped TensorProduct

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]

noncomputable def dualPrecomp (θ : A →ₐc[R] B) : CartierDual R B →+* CartierDual R A where
  toFun φ := CartierDual.ofDual R A ((CartierDual.toDual R B φ) ∘ₗ θ.toLinearMap)
  map_one' := by
    refine CartierDual.ext fun a => ?_
    rw [CartierDual.ofDual_apply, LinearMap.comp_apply, CartierDual.toDual_apply,
      CartierDual.one_apply, CartierDual.one_apply]
    exact CoalgHomClass.counit_comp_apply θ a
  map_mul' φ ψ := by
    refine CartierDual.ext fun a => ?_
    rw [CartierDual.ofDual_apply, LinearMap.comp_apply, CartierDual.toDual_apply,
      CartierDual.mul_apply, CartierDual.mul_apply, CartierDual.toDual_ofDual,
      CartierDual.toDual_ofDual]
    show (TensorProduct.dualDistrib R B B) _ (Coalgebra.comul (R := R) (θ a)) = _
    rw [← CoalgHomClass.map_comp_comul_apply θ a]
    induction Coalgebra.comul (R := R) a using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      simp only [TensorProduct.map_tmul, TensorProduct.dualDistrib_apply, LinearMap.comp_apply]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  map_zero' := by
    refine CartierDual.ext fun a => ?_
    rw [CartierDual.ofDual_apply, LinearMap.comp_apply, CartierDual.toDual_apply,
      CartierDual.zero_apply_pt, CartierDual.zero_apply_pt]
  map_add' φ ψ := by
    refine CartierDual.ext fun a => ?_
    simp only [CartierDual.ofDual_apply, LinearMap.comp_apply, CartierDual.toDual_apply,
      CartierDual.add_apply_pt]

@[scoped simp] theorem dualPrecomp_apply (θ : A →ₐc[R] B) (φ : CartierDual R B) (a : A) :
    dualPrecomp θ φ a = φ (θ a) := rfl

theorem dualPrecomp_injective (θ : A →ₐc[R] B) (hθ : Function.Surjective θ) :
    Function.Injective (dualPrecomp θ) := by
  intro φ ψ h
  refine CartierDual.ext fun b => ?_
  obtain ⟨a, rfl⟩ := hθ b
  have := congrArg (fun χ : CartierDual R A => χ a) h
  simpa using this

end S4
p2m_reactivate "P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual.A2Glue.AlgEquiv P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual.A2Glue"

section S5
open scoped TensorProduct

noncomputable def dualBaseChangeRingEquiv (O : Type*) [CommRing O] (O' : Type*) [CommRing O']
    [Algebra O O'] (A : Type*) [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A] :
    O' ⊗[O] CartierDual O A ≃+* CartierDual O' (O' ⊗[O] A) :=
  let h := CartierDual.dualBaseChangeLin_bijective_integral O O' A
  RingEquiv.ofBijective
    ({ toFun := CartierDual.dualBaseChangeLin O O' A
       map_one' := h.2.1
       map_mul' := h.2.2.1
       map_zero' := map_zero _
       map_add' := map_add _ } : O' ⊗[O] CartierDual O A →+* CartierDual O' (O' ⊗[O] A)) h.1

theorem isLocalRing_cartierDual_baseChange (O : Type*) [CommRing O] (O' : Type*) [CommRing O']
    [Algebra O O'] (A : Type*) [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
    [Coalgebra.IsCocomm O A]
    (h : IsLocalRing (O' ⊗[O] CartierDual O A)) :
    IsLocalRing (CartierDual O' (O' ⊗[O] A)) := by
  haveI := h
  let e := dualBaseChangeRingEquiv O O' A
  haveI : Nontrivial (CartierDual O' (O' ⊗[O] A)) := e.symm.toRingHom.domain_nontrivial
  have hs : Function.Surjective e.toRingHom := fun x => ⟨e.symm x, e.apply_symm_apply x⟩
  exact IsLocalRing.of_surjective' e.toRingHom hs

end S5
p2m_reactivate "P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual.A2Glue.AlgEquiv P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual.A2Glue"

section S47
open scoped TensorProduct

theorem not_isLocalRing_cartierDual_of_surjective_monoidAlgebra
    (O : Type*) [CommRing O] [Nontrivial O] (H₀ : Type*) [CommRing H₀] [Bialgebra O H₀]
    [Coalgebra.IsCocomm O H₀] (Γ : Type*) [CommGroup Γ] [Fintype Γ] [DecidableEq Γ] {x y : Γ} (hxy : x ≠ y)
    (θ : H₀ →ₐc[O] MonoidAlgebra O Γ) (hθ : Function.Surjective θ) :
    ¬ IsLocalRing (CartierDual O H₀) := by
  obtain ⟨e, -, -, -⟩ := CartierDual.exists_algEquiv_monoidAlgebra_pi O Γ
  refine not_isLocalRing_of_injective_ringHom_pi hxy
    ((dualPrecomp θ).comp e.symm.toRingEquiv.toRingHom) ?_
  exact (dualPrecomp_injective θ hθ).comp e.symm.injective

end S47
p2m_reactivate "P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual.A2Glue.AlgEquiv P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual.A2Glue"

end A2Glue
p2m_reactivate "P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual.A2Glue.AlgEquiv P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual.A2Glue"

section A2Assembly

open scoped TensorProduct
open WithConv

theorem solution
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    [IsLocalRing (CartierDual (GaloisRep.ratLocalizedAt p) H)]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ)
    (hn : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ζ : AlgebraicClosure ℚ),
      ζ ^ p = 1 → σ ζ = ζ ^ n σ)
    (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) (hfp : f ^ p = 1)
    (hf : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g = f ^ n σ) :
    f = 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hne

  obtain ⟨O, hOA, hOrat, hOdvr, hOirr, hOval, hOfix, hOmax⟩ :=
    ValuationSubring.exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq p P hP
  letI : Algebra (GaloisRep.ratLocalizedAt p) O := A2Glue.algebraRatLocalizedAt O hOrat
  haveI := A2Glue.isScalarTower_ratLocalizedAt O hOrat
  haveI : IsDiscreteValuationRing O := hOdvr
  haveI : IsLocalHom (algebraMap (GaloisRep.ratLocalizedAt p) O) :=
    A2Glue.isLocalHom_ratLocalizedAt_of_irreducible O hOrat hp hOdvr hOirr
  haveI : IsLocalRing (GaloisRep.ratLocalizedAt p) := A2Glue.isLocalRing_ratLocalizedAt hp

  have hloc : IsLocalRing (CartierDual (↥O) (↥O ⊗[GaloisRep.ratLocalizedAt p] H)) :=
    A2Glue.isLocalRing_cartierDual_baseChange (GaloisRep.ratLocalizedAt p) (↥O) H
      (IsLocalRing.tensorProduct_of_algHom_retraction_of_isLocalHom (GaloisRep.ratLocalizedAt p)
        (CartierDual (GaloisRep.ratLocalizedAt p) H)
        (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) (CartierDual (GaloisRep.ratLocalizedAt p) H))
        (↥O))

  let Pt := WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)
  let J := Additive Pt
  letI : DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J :=
    A2Glue.pointsDistribMulAction (H := H) (A2Glue.galRestrict (GaloisRep.ratLocalizedAt p))
  have hsmul : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (m : J),
      σ • m = Additive.ofMul (A2Glue.compPt (A2Glue.galRestrict (GaloisRep.ratLocalizedAt p) σ)
        (Additive.toMul m)) := fun _ _ => rfl

  have hfσ : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      A2Glue.compPt (A2Glue.galRestrict (GaloisRep.ratLocalizedAt p) σ) f = f ^ n σ :=
    fun σ hσ => hf σ hσ _ (fun h => rfl)
  let HO := ↥O ⊗[GaloisRep.ratLocalizedAt p] H
  let PtO := WithConv (HO →ₐ[↥O] AlgebraicClosure ℚ)
  let M : AddSubgroup J := ⊤
  let S : AddSubgroup J := AddSubgroup.zmultiples (Additive.ofMul f)
  let ptsA : PtO ≃* Pt := (A2Glue.liftPtEquiv (S := ↥O)).symm
  let pts : PtO ≃ ↥M :=
    ptsA.toEquiv.trans (Additive.ofMul.trans (AddSubgroup.topEquiv (G := J)).symm.toEquiv)
  have hpts : ∀ g : PtO, ((pts g : ↥M) : J) = Additive.ofMul (A2Glue.restrPt g) := fun _ => rfl
  have hadd : ∀ f' g' : PtO, pts (f' * g') = pts f' + pts g' := by
    intro f' g'
    apply Subtype.ext
    show ((pts (f' * g') : ↥M) : J) = ((pts f' : ↥M) : J) + ((pts g' : ↥M) : J)
    rw [hpts, hpts, hpts, ← ofMul_mul]
    congr 1
    exact map_mul ptsA f' g'
  have hact : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f' g' : PtO,
      (∀ x : HO, g' x = σ (f' x)) → ((pts g' : ↥M) : J) = σ • ((pts f' : ↥M) : J) := by
    intro σ hσ f' g' hfg
    rw [hpts, hpts, hsmul, toMul_ofMul]
    congr 1
    apply WithConv.ext
    apply AlgHom.ext
    intro h
    exact hfg ((1 : ↥O) ⊗ₜ[GaloisRep.ratLocalizedAt p] h)
  have horder : orderOf f = p := orderOf_eq_prime hfp hne
  have hcardS : Nat.card ↥S = p ^ 1 := by
    rw [pow_one]
    show Nat.card (AddSubgroup.zmultiples (Additive.ofMul f)) = p
    rw [Nat.card_zmultiples, addOrderOf_ofMul_eq_orderOf, horder]
  have hS : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ c : ℕ,
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ ^ c) → ∀ x ∈ S, σ • x = c • x := by
    intro σ hσ c hc x hx
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    rw [hsmul]
    have hk : Additive.toMul (k • Additive.ofMul f) = f ^ k := rfl
    rw [hk, map_zpow, hfσ σ hσ, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    have hexp : (f ^ k) ^ n σ = (f ^ k) ^ c := by
      refine A2Glue.pow_eq_pow_of_forall_rootOfUnity (p := p) (fun ζ hζ => ?_) ?_
      · rw [← hn σ ζ hζ, hc ζ hζ]
      · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hfp, one_zpow]
    rw [hexp, ofMul_pow]
    rfl

  obtain ⟨θ, hθ, -⟩ :=
    HopfAlgebra.exists_surjective_bialgHom_monoidAlgebra_of_multiplicativeType_sub p hp2 P O
      hOA hOdvr hOirr hOfix hOmax HO M S le_top pts hadd hact 1 hcardS hS

  have hxy : (Multiplicative.ofAdd (0 : Fin 1 → ZMod p)) ≠ Multiplicative.ofAdd (fun _ => 1) := by
    intro h
    have h' := congr_fun (Multiplicative.ofAdd.injective h) 0
    haveI : Nontrivial (ZMod p) := ZMod.nontrivial_iff.mpr hp.one_lt.ne'
    exact zero_ne_one h'
  exact A2Glue.not_isLocalRing_cartierDual_of_surjective_monoidAlgebra (↥O) HO
    (Multiplicative (Fin 1 → ZMod p)) hxy θ hθ hloc

end A2Assembly
p2m_reactivate "P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual.A2Glue.AlgEquiv P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual.A2Glue"

end S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual
end P2MW
export P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual (solution)
