-- Prove2me | solution 1 for HopfAlgebra.point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/0a143519-425a-59e2-a6c8-2df26b86f710

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Theorems.Thm_PadicAlgCl_exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq
import Theorems.Thm_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid_of_isAlgClosed
import Theorems.Thm_CartierDual_nonempty_ringEquiv_baseChange
import Theorems.Thm_CartierDual_exists_algEquiv_monoidAlgebra_pi
import Theorems.Thm_IsLocalRing_tensorProduct_of_algHom_retraction_of_isLocalHom
import Theorems.Thm_IsLocalRing_isUnit_of_isUnit_mod_maximalIdeal_of_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual_padicInt
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq"

set_option autoImplicit false

open scoped TensorProduct NNReal

noncomputable section

namespace S17NoMult

open WithConv

section S1

variable {R S L H : Type*} [CommRing R] [CommRing S] [CommRing L] [CommRing H]
  [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L]

section alg
variable [Algebra R H]

def liftPt (φ : WithConv (H →ₐ[R] L)) : WithConv (S ⊗[R] H →ₐ[S] L) :=
  toConv (Algebra.TensorProduct.lift (Algebra.ofId S L) φ.ofConv fun _ _ => .all _ _)

theorem liftPt_tmul (φ : WithConv (H →ₐ[R] L)) (s : S) (h : H) :
    (liftPt (S := S) φ).ofConv (s ⊗ₜ[R] h) = algebraMap S L s * φ.ofConv h := by
  show Algebra.TensorProduct.lift (Algebra.ofId S L) φ.ofConv (fun _ _ => .all _ _) (s ⊗ₜ[R] h) = _
  rw [Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]

theorem liftPt_one_tmul (φ : WithConv (H →ₐ[R] L)) (h : H) :
    (liftPt (S := S) φ).ofConv ((1 : S) ⊗ₜ[R] h) = φ.ofConv h := by
  rw [liftPt_tmul, map_one, one_mul]

def restrPt (ψ : WithConv (S ⊗[R] H →ₐ[S] L)) : WithConv (H →ₐ[R] L) :=
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

theorem liftPt_injective : Function.Injective (liftPt (S := S) : WithConv (H →ₐ[R] L) → _) :=
  fun φ ψ h => by rw [← restrPt_liftPt (S := S) φ, h, restrPt_liftPt]

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

end bialg

end S1

section compPt
variable {R L L' H : Type*} [CommRing R] [CommRing L] [CommRing L'] [Algebra R L] [Algebra R L']
  [CommRing H] [Bialgebra R H]

def compPt (τ : L →ₐ[R] L') : WithConv (H →ₐ[R] L) →* WithConv (H →ₐ[R] L') where
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

section S4

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]

def dualPrecomp (θ : A →ₐc[R] B) : CartierDual R B →+* CartierDual R A where
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
    rfl
  map_add' φ ψ := by
    refine CartierDual.ext fun a => ?_
    rfl

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

section S47

theorem not_isLocalRing_cartierDual_of_surjective_monoidAlgebra
    (O : Type*) [CommRing O] [Nontrivial O] (H₀ : Type*) [CommRing H₀] [Bialgebra O H₀]
    [Coalgebra.IsCocomm O H₀] (Γ : Type*) [CommGroup Γ] [Fintype Γ] [DecidableEq Γ] {x y : Γ} (hxy : x ≠ y)
    (θ : H₀ →ₐc[O] MonoidAlgebra O Γ) (hθ : Function.Surjective θ) :
    ¬ IsLocalRing (CartierDual O H₀) := by
  obtain ⟨e, -, -, -⟩ := CartierDual.exists_algEquiv_monoidAlgebra_pi O Γ
  refine not_isLocalRing_of_injective_ringHom_pi hxy
    ((dualPrecomp θ).comp e.symm.toRingEquiv.toRingHom) ?_
  exact (dualPrecomp_injective θ hθ).comp e.symm.injective

theorem isLocalRing_cartierDual_baseChange (R : Type) [CommRing R] (S : Type) [CommRing S] [Algebra R S]
    (A : Type) [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A] [Coalgebra.IsCocomm R A]
    (h : IsLocalRing (S ⊗[R] CartierDual R A)) : IsLocalRing (CartierDual S (S ⊗[R] A)) := by
  obtain ⟨e⟩ := CartierDual.nonempty_ringEquiv_baseChange R S A
  haveI := h
  haveI : Nontrivial (CartierDual S (S ⊗[R] A)) := e.toRingHom.domain_nontrivial
  exact IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective

theorem isLocalRing_baseChange_cartierDual (R : Type) [CommRing R] (S : Type) [CommRing S] [Algebra R S]
    (A : Type) [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A] [Coalgebra.IsCocomm R A]
    (h : IsLocalRing (CartierDual S (S ⊗[R] A))) : IsLocalRing (S ⊗[R] CartierDual R A) := by
  obtain ⟨e⟩ := CartierDual.nonempty_ringEquiv_baseChange R S A
  haveI := h
  haveI : Nontrivial (S ⊗[R] CartierDual R A) := e.symm.toRingHom.domain_nontrivial
  exact IsLocalRing.of_surjective' e.toRingHom e.surjective

end S47

section LocalModM

theorem isLocalRing_of_isLocalRing_tensorProduct
    (R : Type*) [CommRing R] [IsLocalRing R] (S : Type*) [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (k : Type*) [CommRing k] [Algebra R k] (hk : Function.Surjective (algebraMap R k))
    (hkm : RingHom.ker (algebraMap R k) ≤ IsLocalRing.maximalIdeal R)
    (hT : IsLocalRing (k ⊗[R] S)) : IsLocalRing S := by
  haveI := hT
  let J : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  have hker : RingHom.ker (algebraMap R k) ≤ RingHom.ker (algebraMap R (S ⧸ J)) := by
    intro r hr
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply R S (S ⧸ J), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ (hkm hr)
  let g₀ : k →+* S ⧸ J := RingHom.liftOfSurjective (algebraMap R k) hk ⟨algebraMap R (S ⧸ J), hker⟩
  have hg₀ : ∀ r : R, g₀ (algebraMap R k r) = algebraMap R (S ⧸ J) r := fun r =>
    RingHom.liftOfSurjective_comp_apply (algebraMap R k) hk ⟨algebraMap R (S ⧸ J), hker⟩ r
  let g₁ : k →ₐ[R] S ⧸ J := { g₀ with commutes' := hg₀ }
  let π : k ⊗[R] S →ₐ[R] S ⧸ J :=
    Algebra.TensorProduct.lift g₁ (Ideal.Quotient.mkₐ R J) (fun _ _ => Commute.all _ _)
  have hπ : ∀ s : S, π ((1 : k) ⊗ₜ[R] s) = Ideal.Quotient.mk J s := by
    intro s
    show Algebra.TensorProduct.lift g₁ (Ideal.Quotient.mkₐ R J) _ ((1 : k) ⊗ₜ[R] s) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  haveI : Nontrivial S :=
    (Algebra.TensorProduct.includeRight : S →ₐ[R] k ⊗[R] S).toRingHom.domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self ((1 : k) ⊗ₜ[R] a) with h | h
  · left
    apply IsLocalRing.isUnit_of_isUnit_mod_maximalIdeal_of_isIntegral (R := R)
    rw [← hπ]
    exact h.map π
  · right
    apply IsLocalRing.isUnit_of_isUnit_mod_maximalIdeal_of_isIntegral (R := R)
    rw [← hπ, TensorProduct.tmul_sub]
    rw [Algebra.TensorProduct.one_def] at h
    exact h.map π

end LocalModM

section S0

theorem isLocalHom_padicInt (p : ℕ) [Fact p.Prime] (O : Type*) [CommRing O] [IsLocalRing O] [Algebra ℤ_[p] O]
    (hOp : ¬ IsUnit ((p : ℕ) : O)) : IsLocalHom (algebraMap ℤ_[p] O) := by
  refine ((IsLocalRing.local_hom_TFAE (algebraMap ℤ_[p] O)).out 2 0).mp ?_
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, Ideal.span_le,
    Set.singleton_subset_iff, map_natCast]
  exact hOp

end S0

end S17NoMult
p2m_reactivate "P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual_padicInt.S17NoMult"

end
p2m_reactivate "P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual_padicInt.S17NoMult"

open S17NoMult WithConv in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    [Algebra ℤ_[p] (ZMod p)] (hker : RingHom.ker (algebraMap ℤ_[p] (ZMod p)) = Ideal.span {(p : ℤ_[p])})
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    [Module.Finite ℤ_[p] H] [Module.Flat ℤ_[p] H] [Coalgebra.IsCocomm ℤ_[p] H]
    (hH : IsLocalRing (CartierDual (ZMod p) (TensorProduct ℤ_[p] (ZMod p) H)))
    (f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)) (hfp : f ^ p = 1)
    (hf : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      ∀ c : ℕ, (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → σ ζ = ζ ^ c) →
        ∀ g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p), (∀ h : H, g h = σ (f h)) → g = f ^ c) :
    f = 1 := by
  classical
  have hpp : p.Prime := Fact.out
  by_contra hne

  haveI : Module.Free ℤ_[p] H := Module.free_of_flat_of_isLocalRing

  haveI : IsLocalRing (CartierDual ℤ_[p] H) :=
    isLocalRing_of_isLocalRing_tensorProduct ℤ_[p] (CartierDual ℤ_[p] H) (ZMod p) (ZMod.ringHom_surjective _)
      (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _))
      (isLocalRing_baseChange_cartierDual ℤ_[p] (ZMod p) H hH)

  obtain ⟨Osub, hOsubA, hZpO, hOdvr, hOirr, -, hOfix, hOmax⟩ :=
    PadicAlgCl.exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq p
  haveI : IsDiscreteValuationRing ↥Osub := hOdvr
  letI : Algebra ℤ_[p] ↥Osub := (RingHom.codRestrict (algebraMap ℤ_[p] (PadicAlgCl p)) Osub hZpO).toAlgebra
  haveI : IsScalarTower ℤ_[p] ↥Osub (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsLocalHom (algebraMap ℤ_[p] ↥Osub) := isLocalHom_padicInt p ↥Osub hOirr.not_isUnit
  haveI : FaithfulSMul ↥Osub (PadicAlgCl p) :=
    (faithfulSMul_iff_algebraMap_injective ↥Osub (PadicAlgCl p)).mpr Subtype.val_injective
  have hOA : ∀ x : ↥Osub, algebraMap ↥Osub (PadicAlgCl p) x ∈ padicIntegers p := fun x => hOsubA x.2
  have hOfix' : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] ↔
        ∀ x : ↥Osub, σ (algebraMap ↥Osub (PadicAlgCl p) x) = algebraMap ↥Osub (PadicAlgCl p) x :=
    fun σ => (hOfix σ).trans ⟨fun h x => h x.1 x.2, fun h x hx => h ⟨x, hx⟩⟩
  have hOmax' : ∀ y ∈ padicIntegers p, (∀ σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], σ y = y) →
      ∃ x : ↥Osub, algebraMap ↥Osub (PadicAlgCl p) x = y :=
    fun y hy hfix => ⟨⟨y, hOmax y hy hfix⟩, rfl⟩

  have hloc : IsLocalRing (CartierDual ↥Osub (↥Osub ⊗[ℤ_[p]] H)) :=
    isLocalRing_cartierDual_baseChange ℤ_[p] ↥Osub H
      (IsLocalRing.tensorProduct_of_algHom_retraction_of_isLocalHom ℤ_[p] (CartierDual ℤ_[p] H)
        (Bialgebra.counitAlgHom ℤ_[p] (CartierDual ℤ_[p] H)) ↥Osub)

  let f' : WithConv (↥Osub ⊗[ℤ_[p]] H →ₐ[↥Osub] PadicAlgCl p) := liftPt (S := ↥Osub) f
  have hf'p : f' ^ p = 1 := by
    show liftPt (S := ↥Osub) f ^ p = 1
    rw [← liftPt_pow, hfp, liftPt_one]
  have hf'ne : f' ≠ 1 := by
    intro h
    apply hne
    apply liftPt_injective (S := ↥Osub)
    rw [liftPt_one]
    exact h
  have horder : orderOf f' = p := orderOf_eq_prime hf'p hf'ne
  have hcardD : Nat.card ↥(Submonoid.powers f') = p ^ 1 := by
    have hfin : IsOfFinOrder f' := isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hpp.pos, hf'p⟩
    rw [pow_one]
    calc Nat.card ↥(Submonoid.powers f') = Nat.card (Fin (orderOf f')) :=
          (Nat.card_congr (finEquivPowers hfin)).symm
      _ = p := by rw [Nat.card_eq_fintype_card, Fintype.card_fin, horder]
  have hD : ∀ σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], ∀ c : ℕ,
      (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → σ ζ = ζ ^ c) →
      ∀ d ∈ Submonoid.powers f', ∀ g : WithConv (↥Osub ⊗[ℤ_[p]] H →ₐ[↥Osub] PadicAlgCl p),
        (∀ x : ↥Osub ⊗[ℤ_[p]] H, g x = σ (d x)) → g = d ^ c := by
    intro σ hσ c hc d hd g hg
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hd
    let σR : PadicAlgCl p →ₐ[ℤ_[p]] PadicAlgCl p := (σ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p).restrictScalars ℤ_[p]
    have h1 : compPt σR f = f ^ c := hf σ hσ c hc _ (fun h => rfl)
    have h2 : restrPt (R := ℤ_[p]) g = (f ^ k) ^ c := by
      have h3 : restrPt (R := ℤ_[p]) g = compPt σR (f ^ k) := by
        apply WithConv.ext
        apply AlgHom.ext
        intro h
        rw [restrPt_apply, compPt_apply]
        show g.ofConv ((1 : ↥Osub) ⊗ₜ[ℤ_[p]] h) = σ ((f ^ k).ofConv h)
        rw [hg, ← liftPt_one_tmul (S := ↥Osub) (f ^ k) h, liftPt_pow]
      rw [h3, map_pow, h1, ← pow_mul, mul_comm, pow_mul]
    rw [← liftPt_restrPt (R := ℤ_[p]) g, h2, liftPt_pow, liftPt_pow]

  obtain ⟨θ, hθ, -⟩ :=
    HopfAlgebra.exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid_of_isAlgClosed p hp2
      (padicIntegers p) ↥Osub hOA hOdvr hOirr hOfix' hOmax' (↥Osub ⊗[ℤ_[p]] H) (Submonoid.powers f') 1 hcardD hD

  have hxy : (Multiplicative.ofAdd (0 : Fin 1 → ZMod p)) ≠ Multiplicative.ofAdd (fun _ => 1) := by
    intro h
    have h' := congr_fun (Multiplicative.ofAdd.injective h) 0
    haveI : Nontrivial (ZMod p) := ZMod.nontrivial_iff.mpr hpp.one_lt.ne'
    exact zero_ne_one h'
  exact not_isLocalRing_cartierDual_of_surjective_monoidAlgebra (↥Osub) (↥Osub ⊗[ℤ_[p]] H)
    (Multiplicative (Fin 1 → ZMod p)) hxy θ hθ hloc

end S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual_padicInt
end P2MW
export P2MW.S_HopfAlgebra_point_eq_one_of_forall_mem_inertiaSubgroupIn_eq_pow_of_isLocalRing_cartierDual_padicInt (solution)
