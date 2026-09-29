-- Prove2me | solution 1 for KummerO.exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/13b3409d-2294-5d4f-b9e3-238578597821

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_HopfAlgebra_CartierDualMap
import Theorems.Thm_CartierDual_exists_algHomEquiv_groupLike
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_CartierDual_exists_algEquiv_monoidAlgebra_pi
import Theorems.Thm_CartierDual_exists_bialgEquiv_bidual
import Theorems.Thm_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed
p2m_attr_erase "instance" "GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq"

variable {𝔎 : Type} [Field 𝔎] {𝔏 : Type} [Field 𝔏] [Algebra 𝔎 𝔏] [IsAlgClosed 𝔏] [CharZero 𝔏]

local notation "Γℚ" => (𝔏 ≃ₐ[𝔎] 𝔏)

open scoped TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace Ws25
namespace S3

open TensorProduct

namespace DualPairing

theorem eval_bijective_of_card_eq_finrank_of_residue_comp_ne
    {O : Type} [CommRing O] [IsLocalRing O]
    {B : Type} [CommRing B] [Algebra O B] [Module.Finite O B] [Module.Free O B]
    {ι : Type} [Fintype ι] (φ : ι → (B →ₐ[O] O))
    (hcard : Fintype.card ι = Module.finrank O B)
    (hdist : ∀ i j, i ≠ j →
      (IsLocalRing.residue O).comp (φ i).toRingHom ≠ (IsLocalRing.residue O).comp (φ j).toRingHom) :
    Function.Bijective (fun b : B => fun i : ι => φ i b) := by
  classical
  let ψ : ι → (B →+* IsLocalRing.ResidueField O) := fun i => (IsLocalRing.residue O).comp (φ i).toRingHom
  have hψapp : ∀ i b, ψ i b = IsLocalRing.residue O (φ i b) := fun i b => rfl
  have hψalg : ∀ i (o : O), ψ i (algebraMap O B o) = IsLocalRing.residue O o := by
    intro i o
    rw [hψapp, AlgHom.commutes, Algebra.algebraMap_self_apply]
  have hψsurj : ∀ i, Function.Surjective (ψ i) := by
    intro i r
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective r
    exact ⟨algebraMap O B o, hψalg i o⟩
  have hmax : ∀ i, (RingHom.ker (ψ i)).IsMaximal :=
    fun i => RingHom.ker_isMaximal_of_surjective (ψ i) (hψsurj i)
  have hker : ∀ i j, i ≠ j → RingHom.ker (ψ i) ≠ RingHom.ker (ψ j) := by
    intro i j hij hK
    apply hdist i j hij
    refine RingHom.ext fun b => ?_
    show ψ i b = ψ j b
    obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (ψ i b)
    have hb : b - algebraMap O B o ∈ RingHom.ker (ψ i) := by
      rw [RingHom.mem_ker, map_sub, hψalg, ho, sub_self]
    rw [hK, RingHom.mem_ker, map_sub, sub_eq_zero, hψalg] at hb
    rw [hb, ho]
  have hcop : Pairwise (Function.onFun IsCoprime fun i => RingHom.ker (ψ i)) := by
    intro i j hij
    show IsCoprime (RingHom.ker (ψ i)) (RingHom.ker (ψ j))
    haveI := hmax i
    haveI := hmax j
    exact Ideal.isCoprime_of_isMaximal (hker i j hij)
  have hΨ : ∀ c : ι → O, ∃ b : B, ∀ i, ψ i b = IsLocalRing.residue O (c i) := by
    intro c
    obtain ⟨x, hx⟩ := Ideal.quotientInfToPiQuotient_surj hcop
      (fun i => Ideal.Quotient.mk (RingHom.ker (ψ i)) (algebraMap O B (c i)))
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨b, fun i => ?_⟩
    have hi := congrFun hx i
    rw [Ideal.quotientInfToPiQuotient_mk', Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero] at hi
    rw [hi, hψalg]
  let ev : B →ₗ[O] (ι → O) := LinearMap.pi fun i => (φ i).toLinearMap
  have hev : ∀ b i, ev b i = φ i b := fun b i => rfl
  have hsurj : Function.Surjective ev := by
    rw [← LinearMap.range_eq_top]
    have hN : (⊤ : Submodule O (ι → O)) ≤ LinearMap.range ev ⊔ (IsLocalRing.maximalIdeal O) • ⊤ := by
      intro c _
      obtain ⟨b, hb⟩ := hΨ c
      have hcoord : ∀ i, (c - ev b) i ∈ IsLocalRing.maximalIdeal O := by
        intro i
        rw [← IsLocalRing.residue_eq_zero_iff, Pi.sub_apply, map_sub, hev, ← hψapp, hb, sub_self]
      have hdiff : c - ev b ∈ (IsLocalRing.maximalIdeal O) • (⊤ : Submodule O (ι → O)) := by
        rw [pi_eq_sum_univ (c - ev b)]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hcoord i) Submodule.mem_top
      have hsplit : ev b + (c - ev b) = c := add_sub_cancel _ _
      rw [← hsplit]
      exact Submodule.add_mem_sup (LinearMap.mem_range_self ev b) hdiff
    exact top_le_iff.mp
      (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson ⊥) hN)
  have hrank : Module.finrank O (ι → O) = Module.finrank O B := by
    rw [Module.finrank_pi, hcard]
  let e : (ι → O) ≃ₗ[O] B := LinearEquiv.ofFinrankEq (ι → O) B hrank
  have hg : Function.Surjective ((e : (ι → O) →ₗ[O] B) ∘ₗ ev) := e.surjective.comp hsurj
  have hginj : Function.Injective ((e : (ι → O) →ₗ[O] B) ∘ₗ ev) :=
    OrzechProperty.injective_of_surjective_endomorphism _ hg
  have hinj : Function.Injective ev := by
    intro b₁ b₂ h
    exact hginj (show e (ev b₁) = e (ev b₂) by rw [h])
  have hevf : (fun b : B => fun i : ι => φ i b) = ⇑ev := by
    funext b i
    exact (hev b i).symm
  rw [hevf]
  exact ⟨hinj, hsurj⟩

variable {O : Type} [CommRing O] {H : Type} [CommRing H] [HopfAlgebra O H]
variable {L : Type} [Field L] [Algebra O L]

noncomputable def evalAt (p : H →ₐ[O] L) : L ⊗[O] H →ₐ[L] L :=
  Algebra.TensorProduct.lift (AlgHom.id L L) p (fun _ _ => Commute.all _ _)

@[scoped simp] private theorem evalAt_tmul (p : H →ₐ[O] L) (c : L) (h : H) : evalAt p (c ⊗ₜ h) = c * p h := by
  simp [evalAt]

theorem evalAt_map_twist (τ : L →ₐ[O] L) (p p' : H →ₐ[O] L) (hpp' : ∀ h, p h = τ (p' h)) (x : L ⊗[O] H) :
    evalAt p (Algebra.TensorProduct.map τ (AlgHom.id O H) x) = τ (evalAt p' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c h => simp [hpp', map_mul]
  | add x y hx hy => simp [map_add, hx, hy]

theorem evalAt_convMul (p p' : WithConv (H →ₐ[O] L)) (x : L ⊗[O] H) (hx : IsGroupLikeElem L x) :
    evalAt (WithConv.ofConv (p * p')) x = evalAt (WithConv.ofConv p) x * evalAt (WithConv.ofConv p') x := by
  let E : (L ⊗[O] H) ⊗[L] (L ⊗[O] H) →ₐ[L] L :=
    Algebra.TensorProduct.productMap (evalAt (WithConv.ofConv p)) (evalAt (WithConv.ofConv p'))
  have hkey : (evalAt (WithConv.ofConv (p * p'))).toLinearMap
      = E.toLinearMap ∘ₗ Coalgebra.comul (R := L) (A := L ⊗[O] H) := by
    refine TensorProduct.AlgebraTensorModule.ext fun c h => ?_
    simp only [AlgHom.toLinearMap_apply, LinearMap.coe_comp, Function.comp_apply, evalAt_tmul,
      AlgHom.convMul_apply]
    rw [TensorProduct.comul_tmul, CommSemiring.comul_apply]
    induction (Coalgebra.comul (R := O) h) using TensorProduct.induction_on with
    | zero => rw [map_zero, mul_zero, TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero]
    | tmul a b =>
        rw [Algebra.TensorProduct.lift_tmul, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
        simp only [E, Algebra.TensorProduct.productMap_apply_tmul, evalAt_tmul, one_mul]
        ring
    | add s t hs ht =>
        rw [map_add, mul_add, hs, ht, TensorProduct.tmul_add, map_add, map_add]
  have := congrArg (fun f : L ⊗[O] H →ₗ[L] L => f x) hkey
  simp only [AlgHom.toLinearMap_apply, LinearMap.coe_comp, Function.comp_apply] at this
  rw [this, hx.comul_eq_tmul_self]
  simp [E, Algebra.TensorProduct.productMap_apply_tmul]

theorem evalAt_one (x : L ⊗[O] H) (hx : IsGroupLikeElem L x) :
    evalAt (WithConv.ofConv (1 : WithConv (H →ₐ[O] L))) x = 1 := by
  have hkey : (evalAt (WithConv.ofConv (1 : WithConv (H →ₐ[O] L)))).toLinearMap
      = Coalgebra.counit (R := L) (A := L ⊗[O] H) := by
    refine TensorProduct.AlgebraTensorModule.ext fun c h => ?_
    simp only [AlgHom.toLinearMap_apply, evalAt_tmul]
    rw [TensorProduct.counit_tmul, CommSemiring.counit_apply]
    show c * (1 : WithConv (H →ₐ[O] L)) h = Coalgebra.counit (R := O) h • c
    rw [AlgHom.convOne_apply, Algebra.smul_def, mul_comm]
  have := congrArg (fun f : L ⊗[O] H →ₗ[L] L => f x) hkey
  simp only [AlgHom.toLinearMap_apply] at this
  rw [this, hx.counit_eq_one]

theorem evalAt_pow (p : WithConv (H →ₐ[O] L)) (x : L ⊗[O] H) (hx : IsGroupLikeElem L x) (k : ℕ) :
    evalAt (WithConv.ofConv (p ^ k)) x = (evalAt (WithConv.ofConv p) x) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, evalAt_one x hx]
  | succ k ih => rw [pow_succ, pow_succ, evalAt_convMul _ _ x hx, ih]

theorem eval_injective [Nontrivial O] [Module.Finite O H] [Module.Free O H]
    {ι : Type} [Fintype ι] (pts : ι → (H →ₐ[O] L)) (hinj : Function.Injective pts)
    (hcard : Fintype.card ι = Module.finrank O H) :
    ∀ x y : L ⊗[O] H, (∀ i, evalAt (pts i) x = evalAt (pts i) y) → x = y := by
  have hcard' : Fintype.card ι = Module.finrank L (L ⊗[O] H) := by
    rw [Module.finrank_baseChange, hcard]
  have hdist : ∀ i j, i ≠ j →
      (IsLocalRing.residue L).comp (evalAt (pts i)).toRingHom ≠ (IsLocalRing.residue L).comp (evalAt (pts j)).toRingHom := by
    intro i j hij hEq
    apply hij
    apply hinj
    refine AlgHom.ext fun h => ?_
    have hres : Function.Injective (IsLocalRing.residue L) := by
      rw [RingHom.injective_iff_ker_eq_bot, IsLocalRing.ker_residue, IsLocalRing.maximalIdeal_eq_bot]
    have := congrArg (fun f : L ⊗[O] H →+* IsLocalRing.ResidueField L => f (1 ⊗ₜ h)) hEq
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, evalAt_tmul,
      one_mul] at this
    exact hres this
  have hbij := eval_bijective_of_card_eq_finrank_of_residue_comp_ne (O := L) (B := L ⊗[O] H)
    (fun i => evalAt (pts i)) hcard' hdist
  intro x y hxy
  exact hbij.1 (funext hxy)

theorem map_twist_eq_self_of_isGroupLikeElem [Nontrivial O] [Module.Finite O H] [Module.Free O H]
    {ι : Type} [Fintype ι] (pts : ι → (H →ₐ[O] L)) (hinj : Function.Injective pts)
    (hcard : Fintype.card ι = Module.finrank O H)
    (m : ℕ) (hm : ∀ x : L ⊗[O] H, IsGroupLikeElem L x → x ^ m = 1)
    (τ τ' : L →ₐ[O] L) (hττ' : ∀ z, τ (τ' z) = z)
    (c' : ℕ)
    (hτ'ζ : ∀ ζ : L, ζ ^ m = 1 → τ' ζ = ζ ^ c')
    (hτ'pts : ∀ f : WithConv (H →ₐ[O] L),
      WithConv.toConv (τ'.comp (WithConv.ofConv f)) = f ^ c')
    (x : L ⊗[O] H) (hx : IsGroupLikeElem L x) :
    Algebra.TensorProduct.map τ (AlgHom.id O H) x = x := by
  refine eval_injective pts hinj hcard _ _ fun i => ?_
  set ζ := evalAt (pts i) x with hζ
  have hζm : ζ ^ m = 1 := by
    rw [hζ, ← map_pow, hm x hx, map_one]
  have hp' : ∀ h, pts i h = τ ((τ'.comp (pts i)) h) := fun h => (hττ' _).symm
  rw [evalAt_map_twist τ (pts i) (τ'.comp (pts i)) hp' x]
  have hconv : τ'.comp (pts i) = WithConv.ofConv ((WithConv.toConv (pts i)) ^ c') := by
    have := hτ'pts (WithConv.toConv (pts i))
    rw [WithConv.ofConv_toConv] at this
    rw [← this, WithConv.ofConv_toConv]
  rw [hconv, evalAt_pow _ x hx, WithConv.ofConv_toConv, ← hζ, ← hτ'ζ ζ hζm, hττ']

end DualPairing
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing"

namespace DualPairing

variable {O : Type} [CommRing O] {H : Type} [CommRing H] [HopfAlgebra O H]
variable {L : Type} [Field L] [Algebra O L]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def db (b : Module.Basis ι O H) (k : ι) : CartierDual O H := CartierDual.ofDual O H (b.coord k)

omit [Fintype ι] [DecidableEq ι] in
theorem db_apply (b : Module.Basis ι O H) (k : ι) (x : H) : db b k x = b.repr x k := by
  show CartierDual.toDual O H (CartierDual.ofDual O H (b.coord k)) x = b.repr x k
  rw [CartierDual.toDual_ofDual, Module.Basis.coord_apply]

omit [Fintype ι] in
theorem db_apply_basis (b : Module.Basis ι O H) (k i : ι) : db b k (b i) = if i = k then 1 else 0 := by
  rw [db_apply, Module.Basis.repr_self, Finsupp.single_apply]

def pair (b : Module.Basis ι O H) (f : CartierDual O H →ₐ[O] L) (ψ : H →ₐ[O] L) : L := ∑ k, f (db b k) * ψ (b k)

theorem eq_sum_tmul_of_pairing (b : Module.Basis ι O H) (g : L ⊗[O] H) (f : CartierDual O H →ₐ[O] L)
    (hg : ∀ φ : CartierDual O H, TensorProduct.rid O L (LinearMap.lTensor L (CartierDual.toDual O H φ) g) = f φ) :
    g = ∑ k, f (db b k) ⊗ₜ[O] b k := by
  set B := Algebra.TensorProduct.basis L b with hB
  have hexp : g = ∑ k, (B.repr g k) ⊗ₜ[O] b k := by
    conv_lhs => rw [← B.sum_repr g]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hB, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hcoef : ∀ k, f (db b k) = B.repr g k := by
    intro k
    rw [← hg (db b k)]
    conv_lhs => rw [hexp]
    rw [map_sum, map_sum]
    simp_rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
    have hdb : ∀ i, CartierDual.toDual O H (db b k) (b i) = if i = k then 1 else 0 := fun i => by
      rw [CartierDual.toDual_apply, db_apply_basis]
    simp_rw [hdb, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq' Finset.univ k, if_pos (Finset.mem_univ k)]
  rw [hexp]
  exact Finset.sum_congr rfl fun k _ => by rw [hcoef k]

theorem pair_eq_evalAt (b : Module.Basis ι O H) (g : L ⊗[O] H) (f : CartierDual O H →ₐ[O] L)
    (hg : ∀ φ : CartierDual O H, TensorProduct.rid O L (LinearMap.lTensor L (CartierDual.toDual O H φ) g) = f φ)
    (ψ : H →ₐ[O] L) : pair b f ψ = evalAt ψ g := by
  rw [eq_sum_tmul_of_pairing b g f hg, map_sum]
  simp_rw [evalAt_tmul]
  rfl

section withEquiv

variable [Module.Finite O H] [Module.Free O H]
variable (O H L)

structure GLData where
  e : (CartierDual O H →ₐ[O] L) ≃ GroupLike L (L ⊗[O] H)
  pairing : ∀ (ψ : CartierDual O H →ₐ[O] L) (φ : CartierDual O H),
    TensorProduct.rid O L (LinearMap.lTensor L (CartierDual.toDual O H φ) (e ψ).val) = ψ φ
  one : ∀ ψ₀ : CartierDual O H →ₐ[O] L, (∀ φ, ψ₀ φ = algebraMap O L (φ 1)) → (e ψ₀).val = 1
  mul : ∀ ψ₁ ψ₂ ψ₃ : CartierDual O H →ₐ[O] L,
    WithConv.toConv ψ₃.toLinearMap = WithConv.toConv ψ₁.toLinearMap * WithConv.toConv ψ₂.toLinearMap →
    (e ψ₃).val = (e ψ₁).val * (e ψ₂).val
  nat : ∀ (τ : L →ₐ[O] L) (ψ : CartierDual O H →ₐ[O] L),
    (e (τ.comp ψ)).val = Algebra.TensorProduct.map τ (AlgHom.id O H) (e ψ).val

variable {O H L}

theorem nonempty_glData : Nonempty (GLData O H L) := by
  obtain ⟨e, he1, he2, he3, he4⟩ := CartierDual.exists_algHomEquiv_groupLike O H
  exact ⟨⟨e L, he1 L, he2 L, he3 L, fun τ ψ => he4 L L τ ψ⟩⟩

variable (gl : GLData O H L) (b : Module.Basis ι O H)
include gl

theorem pair_eq_evalAt_val (f : CartierDual O H →ₐ[O] L) (ψ : H →ₐ[O] L) : pair b f ψ = evalAt ψ (gl.e f).val :=
  pair_eq_evalAt b _ f (gl.pairing f) ψ

theorem pair_convMul_right (f : CartierDual O H →ₐ[O] L) (ψ ψ' : WithConv (H →ₐ[O] L)) :
    pair b f (WithConv.ofConv (ψ * ψ')) = pair b f (WithConv.ofConv ψ) * pair b f (WithConv.ofConv ψ') := by
  rw [pair_eq_evalAt_val gl, pair_eq_evalAt_val gl, pair_eq_evalAt_val gl]
  exact evalAt_convMul ψ ψ' _ (gl.e f).isGroupLikeElem_val

theorem pair_one_right (f : CartierDual O H →ₐ[O] L) : pair b f (WithConv.ofConv (1 : WithConv (H →ₐ[O] L))) = 1 := by
  rw [pair_eq_evalAt_val gl]
  exact evalAt_one _ (gl.e f).isGroupLikeElem_val

theorem pair_convMul_left (f f' : WithConv (CartierDual O H →ₐ[O] L)) (ψ : H →ₐ[O] L) :
    pair b (WithConv.ofConv (f * f')) ψ = pair b (WithConv.ofConv f) ψ * pair b (WithConv.ofConv f') ψ := by
  rw [pair_eq_evalAt_val gl, pair_eq_evalAt_val gl, pair_eq_evalAt_val gl, ← map_mul]
  congr 1
  exact gl.mul _ _ _ (AlgHom.toLinearMap_convMul f f')

theorem pair_one_left (ψ : H →ₐ[O] L) : pair b (WithConv.ofConv (1 : WithConv (CartierDual O H →ₐ[O] L))) ψ = 1 := by
  rw [pair_eq_evalAt_val gl, gl.one _ (fun φ => ?_), map_one]
  rw [AlgHom.convOne_apply]
  exact congrArg (algebraMap O L) (CartierDual.counit_apply φ)

theorem pair_pow_left (f : WithConv (CartierDual O H →ₐ[O] L)) (ψ : H →ₐ[O] L) (n : ℕ) :
    pair b (WithConv.ofConv (f ^ n)) ψ = pair b (WithConv.ofConv f) ψ ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pair_one_left gl]
  | succ n ih => rw [pow_succ, pow_succ, pair_convMul_left gl, ih]

theorem pair_pow_right (f : CartierDual O H →ₐ[O] L) (ψ : WithConv (H →ₐ[O] L)) (n : ℕ) :
    pair b f (WithConv.ofConv (ψ ^ n)) = pair b f (WithConv.ofConv ψ) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pair_one_right gl]
  | succ n ih => rw [pow_succ, pow_succ, pair_convMul_right gl, ih]

theorem eq_one_of_forall_pair_eq_one [Nontrivial O]
    {κ : Type} [Fintype κ] (pts : κ → (H →ₐ[O] L)) (hinj : Function.Injective pts) (hcard : Fintype.card κ = Module.finrank O H)
    (f : WithConv (CartierDual O H →ₐ[O] L)) (hf : ∀ i, pair b (WithConv.ofConv f) (pts i) = 1) : f = 1 := by
  have hval : (gl.e (WithConv.ofConv f)).val = (gl.e (WithConv.ofConv 1)).val := by
    refine eval_injective pts hinj hcard _ _ fun i => ?_
    rw [← pair_eq_evalAt_val gl b, ← pair_eq_evalAt_val gl b, hf i, pair_one_left gl]
  have := gl.e.injective (GroupLike.val_injective hval)
  exact congrArg WithConv.toConv this

omit [DecidableEq ι] [Module.Finite O H] [Module.Free O H] gl in

theorem pair_twist (τ : L →ₐ[O] L) (f : CartierDual O H →ₐ[O] L) (ψ ψ' : H →ₐ[O] L) (hψ : ∀ h, ψ h = τ (ψ' h)) :
    pair b (τ.comp f) ψ = τ (pair b f ψ') := by
  unfold pair
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [AlgHom.comp_apply, hψ, map_mul]

end withEquiv
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing"

end DualPairing
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing"

namespace DualChar

structure Car {I : Subgroup (𝔏 ≃ₐ[𝔎] 𝔏)} (Γ : Type) (ρ : ↥I →* Function.End Γ) where

  val : Γ → (𝔏)ˣ

namespace Car

variable {I : Subgroup (𝔏 ≃ₐ[𝔎] 𝔏)} {Γ : Type} {ρ : ↥I →* Function.End Γ}

theorem ext {F G : Car Γ ρ} (h : ∀ x, F.val x = G.val x) : F = G := by
  cases F; cases G; congr; exact funext h

def equivAdd : Car Γ ρ ≃ Additive (Γ → (𝔏)ˣ) where
  toFun F := Additive.ofMul F.val
  invFun G := ⟨Additive.toMul G⟩
  left_inv _ := rfl
  right_inv _ := rfl

scoped instance : AddCommGroup (Car Γ ρ) := (equivAdd (Γ := Γ) (ρ := ρ)).addCommGroup

theorem add_val (F G : Car Γ ρ) (x : Γ) : (F + G).val x = F.val x * G.val x := rfl

theorem zero_val (x : Γ) : (0 : Car Γ ρ).val x = 1 := rfl

theorem nsmul_val (n : ℕ) (F : Car Γ ρ) (x : Γ) : (n • F).val x = F.val x ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, zero_val]
  | succ n ih => rw [succ_nsmul, add_val, ih, pow_succ]

def galUnit (σ : 𝔏 ≃ₐ[𝔎] 𝔏) (u : (𝔏)ˣ) : (𝔏)ˣ :=
  ⟨σ u, σ ↑u⁻¹, by rw [← map_mul, Units.mul_inv, map_one], by rw [← map_mul, Units.inv_mul, map_one]⟩

theorem galUnit_val (σ : 𝔏 ≃ₐ[𝔎] 𝔏) (u : (𝔏)ˣ) :
    (galUnit σ u : 𝔏) = σ u := rfl

scoped instance : SMul ↥I (Car Γ ρ) :=
  ⟨fun σ F => ⟨fun x => galUnit (σ : 𝔏 ≃ₐ[𝔎] 𝔏) (F.val (ρ σ⁻¹ x))⟩⟩

theorem smul_val (σ : ↥I) (F : Car Γ ρ) (x : Γ) :
    ((σ • F).val x : 𝔏) = (σ : 𝔏 ≃ₐ[𝔎] 𝔏) (F.val (ρ σ⁻¹ x)) := rfl

scoped instance : DistribMulAction ↥I (Car Γ ρ) where
  one_smul F := by
    apply ext; intro x; apply Units.ext
    rw [smul_val, inv_one, map_one, OneMemClass.coe_one, AlgEquiv.one_apply]
    rfl
  mul_smul σ τ F := by
    apply ext; intro x; apply Units.ext
    rw [smul_val, smul_val, smul_val, mul_inv_rev, map_mul, Subgroup.coe_mul, AlgEquiv.mul_apply]
    rfl
  smul_zero σ := by
    apply ext; intro x; apply Units.ext
    rw [smul_val, zero_val, zero_val, Units.val_one, map_one]
  smul_add σ F G := by
    apply ext; intro x; apply Units.ext
    rw [smul_val, add_val, add_val, Units.val_mul, Units.val_mul, map_mul, smul_val, smul_val]

end Car
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar.Car"

end DualChar
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar.Car P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar"

namespace DualFlag

open DualPairing DualChar

theorem exists_convMul_eq_one_of_comm {R H L : Type} [CommRing R] [CommRing H] [HopfAlgebra R H]
    [CommRing L] [Algebra R L]
    (f : WithConv (H →ₐ[R] L)) : ∃ g : WithConv (H →ₐ[R] L), g * f = 1 := by
  let S : H →ₐ[R] H :=
    { toFun := fun h => HopfAlgebra.antipode R h
      map_one' := HopfAlgebra.antipode_one
      map_mul' := fun x y => by rw [HopfAlgebra.antipode_mul, mul_comm]
      map_zero' := map_zero _
      map_add' := fun x y => map_add _ x y
      commutes' := fun r => by
        rw [Algebra.algebraMap_eq_smul_one, map_smul, HopfAlgebra.antipode_one] }
  have hS : ∀ h, S h = HopfAlgebra.antipode R h := fun _ => rfl
  refine ⟨WithConv.toConv ((WithConv.ofConv f).comp S), ?_⟩
  apply WithConv.ext
  apply AlgHom.ext
  intro h
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply, WithConv.ofConv_toConv]
  have key : ∀ t : TensorProduct R H H,
      Algebra.TensorProduct.lift ((WithConv.ofConv f).comp S) (WithConv.ofConv f)
          (fun _ _ => Commute.all _ _) t
        = (WithConv.ofConv f) (LinearMap.mul' R H ((HopfAlgebra.antipode R).rTensor H t)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
        rw [Algebra.TensorProduct.lift_tmul, LinearMap.rTensor_tmul, LinearMap.mul'_apply, map_mul,
          AlgHom.comp_apply, hS]
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add, map_add]
  rw [key, HopfAlgebra.mul_antipode_rTensor_comul_apply, AlgHom.commutes]

def rhoM {I : Subgroup (𝔏 ≃ₐ[𝔎] 𝔏)} {J : Type} [AddCommGroup J] [DistribMulAction ↥I J] (M : AddSubgroup J)
    (hMstab : ∀ (σ : ↥I) (x : J), x ∈ M → σ • x ∈ M) :
    ↥I →* Function.End ↥M where
  toFun σ := fun x => ⟨σ • (x : J), hMstab σ x x.2⟩
  map_one' := by
    apply funext; intro x
    exact Subtype.ext (one_smul _ (x : J))
  map_mul' σ τ := by
    apply funext; intro x
    exact Subtype.ext (mul_smul σ τ (x : J))

theorem rhoM_apply {I : Subgroup (𝔏 ≃ₐ[𝔎] 𝔏)} {J : Type} [AddCommGroup J] [DistribMulAction ↥I J]
    (M : AddSubgroup J) (hMstab : ∀ (σ : ↥I) (x : J), x ∈ M → σ • x ∈ M)
    (σ : ↥I) (x : ↥M) : ((rhoM M hMstab σ x : ↥M) : J) = σ • (x : J) := rfl

section Context

variable {O : Type} [CommRing O] [Algebra O (𝔏)] {HO : Type} [CommRing HO] [HopfAlgebra O HO]
variable [Module.Finite O HO] [Module.Free O HO]
variable {I : Subgroup (𝔏 ≃ₐ[𝔎] 𝔏)} {J : Type} [AddCommGroup J] [DistribMulAction ↥I J]
variable {M : AddSubgroup J} (pts : WithConv (HO →ₐ[O] 𝔏) ≃ ↥M)
variable (hadd : ∀ f g, pts (f * g) = pts f + pts g)
variable {ι : Type} [Fintype ι] [DecidableEq ι] (gl : GLData O HO (𝔏)) (b : Module.Basis ι O HO)

omit [Module.Finite O HO] [Module.Free O HO] [DistribMulAction ↥I J] in
include hadd in
theorem pts_one : pts 1 = 0 := by
  have h := hadd 1 1
  rw [one_mul] at h
  have h' : pts 1 + pts 1 = pts 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h'

omit [Module.Finite O HO] [Module.Free O HO] [DistribMulAction ↥I J] in
include hadd in
theorem pts_pow (f : WithConv (HO →ₐ[O] 𝔏)) (k : ℕ) : pts (f ^ k) = k • pts f := by
  induction k with
  | zero => rw [pow_zero, zero_nsmul, pts_one pts hadd]
  | succ k ih => rw [pow_succ, hadd, ih, succ_nsmul]

omit [Module.Finite O HO] [Module.Free O HO] [DistribMulAction ↥I J] in
include hadd in
theorem pow_natCard_eq_one (f : WithConv (HO →ₐ[O] 𝔏)) : f ^ Nat.card ↥M = 1 := by
  apply pts.injective
  rw [pts_pow pts hadd, pts_one pts hadd, card_nsmul_eq_zero']

omit [DistribMulAction ↥I J] in
include hadd gl in
theorem pair_pow_natCard_eq_one (f : CartierDual O HO →ₐ[O] 𝔏) (ψ : WithConv (HO →ₐ[O] 𝔏)) :
    pair b f (WithConv.ofConv ψ) ^ Nat.card ↥M = 1 := by
  rw [← pair_pow_right gl, pow_natCard_eq_one pts hadd, pair_one_right gl]

omit [DistribMulAction ↥I J] in
include hadd gl in
theorem isUnit_pair [Finite ↥M] (f : CartierDual O HO →ₐ[O] 𝔏)
    (ψ : WithConv (HO →ₐ[O] 𝔏)) : IsUnit (pair b f (WithConv.ofConv ψ)) :=
  IsUnit.of_pow_eq_one (pair_pow_natCard_eq_one pts hadd gl b f ψ) (Nat.card_pos (α := ↥M)).ne'

variable [Finite ↥M] (hMstab : ∀ (σ : ↥I) (x : J), x ∈ M → σ • x ∈ M)

def chi (f : CartierDual O HO →ₐ[O] 𝔏) : Car ↥M (rhoM M hMstab) :=
  ⟨fun m => (isUnit_pair pts hadd gl b f (pts.symm m)).unit⟩

theorem chi_val (f : CartierDual O HO →ₐ[O] 𝔏) (m : ↥M) :
    ((chi pts hadd gl b hMstab f).val m : 𝔏) = pair b f (WithConv.ofConv (pts.symm m)) :=
  IsUnit.unit_spec _

theorem chi_val_pts (f : CartierDual O HO →ₐ[O] 𝔏) (ψ : WithConv (HO →ₐ[O] 𝔏)) :
    ((chi pts hadd gl b hMstab f).val (pts ψ) : 𝔏) = pair b f (WithConv.ofConv ψ) := by
  rw [chi_val, Equiv.symm_apply_apply]

theorem chi_one : chi pts hadd gl b hMstab (WithConv.ofConv 1) = 0 := by
  apply Car.ext; intro m; apply Units.ext
  rw [chi_val, Car.zero_val, Units.val_one, pair_one_left gl]

theorem chi_mul (f g : WithConv (CartierDual O HO →ₐ[O] 𝔏)) :
    chi pts hadd gl b hMstab (WithConv.ofConv (f * g)) =
      chi pts hadd gl b hMstab (WithConv.ofConv f) + chi pts hadd gl b hMstab (WithConv.ofConv g) := by
  apply Car.ext; intro m; apply Units.ext
  rw [chi_val, Car.add_val, Units.val_mul, chi_val, chi_val, pair_convMul_left gl]

variable [Coalgebra.IsCocomm O HO]

theorem chi_injective [Nontrivial O] (hcard : Nat.card ↥M = Module.finrank O HO) :
    Function.Injective (fun f : WithConv (CartierDual O HO →ₐ[O] 𝔏) =>
      chi pts hadd gl b hMstab (WithConv.ofConv f)) := by
  classical
  haveI : Fintype ↥M := Fintype.ofFinite ↥M
  have hsep : ∀ f : WithConv (CartierDual O HO →ₐ[O] 𝔏),
      chi pts hadd gl b hMstab (WithConv.ofConv f) = 0 → f = 1 := by
    intro f hf
    refine eq_one_of_forall_pair_eq_one gl b (κ := ↥M) (fun m => WithConv.ofConv (pts.symm m))
      (fun m m' h => pts.symm.injective (WithConv.ofConv_injective h)) ?_ f fun m => ?_
    · rw [Fintype.card_eq_nat_card, hcard]
    · have h := congrArg (fun F : Car ↥M (rhoM M hMstab) => (F.val m : 𝔏)) hf
      rwa [chi_val, Car.zero_val, Units.val_one] at h
  intro f g hfg
  simp only at hfg
  obtain ⟨g', hg'⟩ := exists_convMul_eq_one_of_comm g
  have h1 : chi pts hadd gl b hMstab (WithConv.ofConv (f * g')) = 0 := by
    rw [chi_mul, hfg, ← chi_mul, mul_comm, hg', chi_one]
  have h2 := hsep _ h1
  calc f = f * (g' * g) := by rw [hg', mul_one]
    _ = f * g' * g := by rw [mul_assoc]
    _ = g := by rw [h2, one_mul]

def M₂ : AddSubgroup (Car ↥M (rhoM M hMstab)) where
  carrier := Set.range fun f : WithConv (CartierDual O HO →ₐ[O] 𝔏) =>
    chi pts hadd gl b hMstab (WithConv.ofConv f)
  zero_mem' := ⟨1, chi_one pts hadd gl b hMstab⟩
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f * g, chi_mul pts hadd gl b hMstab f g⟩
  neg_mem' := by
    rintro _ ⟨f, rfl⟩
    obtain ⟨g, hg⟩ := exists_convMul_eq_one_of_comm f
    refine ⟨g, ?_⟩
    have h : chi pts hadd gl b hMstab (WithConv.ofConv g) + chi pts hadd gl b hMstab (WithConv.ofConv f) = 0 := by
      rw [← chi_mul, hg, chi_one]
    exact eq_neg_of_add_eq_zero_left h

theorem mem_M₂ (F : Car ↥M (rhoM M hMstab)) :
    F ∈ M₂ pts hadd gl b hMstab ↔ ∃ f : WithConv (CartierDual O HO →ₐ[O] 𝔏),
      chi pts hadd gl b hMstab (WithConv.ofConv f) = F := Iff.rfl

def pts₂ [Nontrivial O] (hcard : Nat.card ↥M = Module.finrank O HO) :
    WithConv (CartierDual O HO →ₐ[O] 𝔏) ≃ ↥(M₂ pts hadd gl b hMstab) :=
  Equiv.ofBijective (fun f => ⟨chi pts hadd gl b hMstab (WithConv.ofConv f), f, rfl⟩)
    ⟨fun f g h => chi_injective pts hadd gl b hMstab hcard (congrArg Subtype.val h),
     fun F => by obtain ⟨F, f, hf⟩ := F; exact ⟨f, Subtype.ext hf⟩⟩

theorem pts₂_val [Nontrivial O] (hcard : Nat.card ↥M = Module.finrank O HO)
    (f : WithConv (CartierDual O HO →ₐ[O] 𝔏)) :
    ((pts₂ pts hadd gl b hMstab hcard f : ↥(M₂ pts hadd gl b hMstab)) : Car ↥M (rhoM M hMstab)) =
      chi pts hadd gl b hMstab (WithConv.ofConv f) := rfl

theorem pts₂_add [Nontrivial O] (hcard : Nat.card ↥M = Module.finrank O HO)
    (f g : WithConv (CartierDual O HO →ₐ[O] 𝔏)) :
    pts₂ pts hadd gl b hMstab hcard (f * g) = pts₂ pts hadd gl b hMstab hcard f + pts₂ pts hadd gl b hMstab hcard g :=
  Subtype.ext (chi_mul pts hadd gl b hMstab f g)

def S₂ (D : AddSubgroup J) : AddSubgroup (Car ↥M (rhoM M hMstab)) where
  carrier := {F | F ∈ M₂ pts hadd gl b hMstab ∧ ∀ m : ↥M, (m : J) ∈ D → F.val m = 1}
  zero_mem' := ⟨AddSubgroup.zero_mem _, fun m _ => Car.zero_val m⟩
  add_mem' := by
    rintro F G ⟨hF, hF'⟩ ⟨hG, hG'⟩
    exact ⟨AddSubgroup.add_mem _ hF hG, fun m hm => by rw [Car.add_val, hF' m hm, hG' m hm, one_mul]⟩
  neg_mem' := by
    rintro F ⟨hF, hF'⟩
    refine ⟨AddSubgroup.neg_mem _ hF, fun m hm => ?_⟩
    have h : (-F + F).val m = 1 := by rw [neg_add_cancel, Car.zero_val]
    rwa [Car.add_val, hF' m hm, mul_one] at h

theorem mem_S₂ (D : AddSubgroup J) (F : Car ↥M (rhoM M hMstab)) :
    F ∈ S₂ pts hadd gl b hMstab D ↔ F ∈ M₂ pts hadd gl b hMstab ∧ ∀ m : ↥M, (m : J) ∈ D → F.val m = 1 := Iff.rfl

theorem S₂_le (D : AddSubgroup J) : S₂ pts hadd gl b hMstab D ≤ M₂ pts hadd gl b hMstab := fun _ h => h.1

end Context
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar.Car P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar"

section PartTwo

variable {O : Type} [CommRing O] [Algebra O (𝔏)] {HO : Type} [CommRing HO] [HopfAlgebra O HO]
variable [Module.Finite O HO] [Module.Free O HO]
variable {I : Subgroup (𝔏 ≃ₐ[𝔎] 𝔏)} {J : Type} [AddCommGroup J] [DistribMulAction ↥I J]
variable {M : AddSubgroup J} (pts : WithConv (HO →ₐ[O] 𝔏) ≃ ↥M)
variable (hadd : ∀ f g, pts (f * g) = pts f + pts g)
variable {ι : Type} [Fintype ι] [DecidableEq ι] (gl : GLData O HO (𝔏)) (b : Module.Basis ι O HO)
variable [Finite ↥M] (hMstab : ∀ (σ : ↥I) (x : J), x ∈ M → σ • x ∈ M)

omit [Module.Finite O HO] [Module.Free O HO] [DistribMulAction ↥I J]
  [Finite ↥M] in
include hadd in
theorem pts_symm_add (m m' : ↥M) : pts.symm (m + m') = pts.symm m * pts.symm m' := by
  apply pts.injective
  rw [hadd, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

variable [Coalgebra.IsCocomm O HO]

theorem val_add_of_mem {F : Car ↥M (rhoM M hMstab)} (hF : F ∈ M₂ pts hadd gl b hMstab) (m m' : ↥M) :
    F.val (m + m') = F.val m * F.val m' := by
  obtain ⟨f, rfl⟩ := hF
  apply Units.ext
  rw [Units.val_mul, chi_val, chi_val, chi_val, pts_symm_add pts hadd]
  exact pair_convMul_right gl b _ _ _

theorem val_zero_of_mem {F : Car ↥M (rhoM M hMstab)} (hF : F ∈ M₂ pts hadd gl b hMstab) : F.val 0 = 1 := by
  have h := val_add_of_mem pts hadd gl b hMstab hF 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem val_nsmul_of_mem {F : Car ↥M (rhoM M hMstab)} (hF : F ∈ M₂ pts hadd gl b hMstab) (n : ℕ) (m : ↥M) :
    F.val (n • m) = F.val m ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, val_zero_of_mem pts hadd gl b hMstab hF]
  | succ n ih => rw [succ_nsmul, val_add_of_mem pts hadd gl b hMstab hF, ih, pow_succ]

theorem nsmul_eq_zero_of_mem_M₂ (c : ℕ) (hMc : ∀ m : ↥M, (c • m : ↥M) = 0)
    {F : Car ↥M (rhoM M hMstab)} (hF : F ∈ M₂ pts hadd gl b hMstab) : c • F = 0 := by
  apply Car.ext
  intro m
  rw [Car.nsmul_val, ← val_nsmul_of_mem pts hadd gl b hMstab hF, hMc m, val_zero_of_mem pts hadd gl b hMstab hF,
    Car.zero_val]

theorem val_neg_of_mem {F : Car ↥M (rhoM M hMstab)} (hF : F ∈ M₂ pts hadd gl b hMstab) (m : ↥M) :
    F.val (-m) = (F.val m)⁻¹ := by
  have h := val_add_of_mem pts hadd gl b hMstab hF (-m) m
  rw [neg_add_cancel, val_zero_of_mem pts hadd gl b hMstab hF] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem val_zsmul_of_mem {F : Car ↥M (rhoM M hMstab)} (hF : F ∈ M₂ pts hadd gl b hMstab) (z : ℤ) (m : ↥M) :
    F.val (z • m) = F.val m ^ z := by
  cases z with
  | ofNat n => rw [Int.ofNat_eq_natCast, natCast_zsmul, zpow_natCast, val_nsmul_of_mem pts hadd gl b hMstab hF]
  | negSucc n =>
      rw [negSucc_zsmul, zpow_negSucc, val_neg_of_mem pts hadd gl b hMstab hF, val_nsmul_of_mem pts hadd gl b hMstab hF]

theorem exists_algHom_eq
    (hOfix : ∀ σ : 𝔏 ≃ₐ[𝔎] 𝔏, σ ∈ I ↔ ∀ x : O, σ (algebraMap O (𝔏) x) = algebraMap O (𝔏) x)
    (σ : ↥I) :
    ∃ τ : 𝔏 →ₐ[O] 𝔏, ∀ z, τ z = (σ : 𝔏 ≃ₐ[𝔎] 𝔏) z :=
  ⟨{ ((σ : 𝔏 ≃ₐ[𝔎] 𝔏) : 𝔏 →+* 𝔏) with
      commutes' := fun o => (hOfix σ).mp σ.2 o }, fun _ => rfl⟩

theorem pts₂_act [Nontrivial O] (hcard : Nat.card ↥M = Module.finrank O HO)
    (hOfix : ∀ σ : 𝔏 ≃ₐ[𝔎] 𝔏, σ ∈ I ↔ ∀ x : O, σ (algebraMap O (𝔏) x) = algebraMap O (𝔏) x)
    (hact : ∀ (σ : ↥I) (f g : WithConv (HO →ₐ[O] 𝔏)),
      (∀ x : HO, g x = (σ : 𝔏 ≃ₐ[𝔎] 𝔏) (f x)) → ((pts g : ↥M) : J) = σ • ((pts f : ↥M) : J))
    (σ : ↥I)
    (f g : WithConv (CartierDual O HO →ₐ[O] 𝔏)) (hfg : ∀ x : CartierDual O HO, g x = (σ : 𝔏 ≃ₐ[𝔎] 𝔏) (f x)) :
    ((pts₂ pts hadd gl b hMstab hcard g : ↥(M₂ pts hadd gl b hMstab)) : Car ↥M (rhoM M hMstab)) =
      σ • ((pts₂ pts hadd gl b hMstab hcard f : ↥(M₂ pts hadd gl b hMstab)) : Car ↥M (rhoM M hMstab)) := by
  rw [pts₂_val, pts₂_val]
  apply Car.ext; intro m; apply Units.ext
  rw [Car.smul_val, chi_val, chi_val]
  obtain ⟨τ, hτ⟩ := exists_algHom_eq (I := I) hOfix σ
  obtain ⟨τ', hτ'⟩ := exists_algHom_eq (I := I) hOfix σ⁻¹

  have hψ' : pts.symm (rhoM M hMstab σ⁻¹ m) =
      WithConv.toConv (τ'.comp (WithConv.ofConv (pts.symm m))) := by
    apply pts.symm_apply_eq.mpr
    apply Subtype.ext
    rw [rhoM_apply]
    have h := hact σ⁻¹ (pts.symm m)
      (WithConv.toConv (τ'.comp (WithConv.ofConv (pts.symm m)))) fun x => hτ' _
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  rw [hψ', WithConv.ofConv_toConv]
  have hg : WithConv.ofConv g = τ.comp (WithConv.ofConv f) := AlgHom.ext fun x => (hfg x).trans (hτ (f x)).symm
  rw [hg, pair_twist b τ (WithConv.ofConv f) (WithConv.ofConv (pts.symm m)) (τ'.comp (WithConv.ofConv (pts.symm m)))
    fun h => ?_, hτ]
  rw [AlgHom.comp_apply, hτ, hτ', Subgroup.coe_inv, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]

theorem smul_eq_nsmul_of_mem_S₂ (D : AddSubgroup J)
    (q : ℕ) (hqD : ∀ m : ↥M, ((q • m : ↥M) : J) ∈ D)
    (hdisp : ∀ (σ : ↥I) (m : ↥M), σ • (m : J) - m ∈ D)
    (σ : ↥I) (c : ℕ)
    (hc : ∀ ζ : 𝔏, ζ ^ q = 1 → (σ : 𝔏 ≃ₐ[𝔎] 𝔏) ζ = ζ ^ c)
    (F : Car ↥M (rhoM M hMstab)) (hF : F ∈ S₂ pts hadd gl b hMstab D) : σ • F = c • F := by
  obtain ⟨hFM, hFD⟩ := hF
  apply Car.ext; intro m; apply Units.ext
  rw [Car.smul_val, Car.nsmul_val, Units.val_pow_eq_pow_val]

  have hd : ((rhoM M hMstab σ⁻¹ m - m : ↥M) : J) ∈ D := by
    rw [AddSubgroupClass.coe_sub, rhoM_apply]
    exact hdisp σ⁻¹ m
  have h1 : F.val (rhoM M hMstab σ⁻¹ m) = F.val m := by
    have h := val_add_of_mem pts hadd gl b hMstab hFM m (rhoM M hMstab σ⁻¹ m - m)
    rw [add_sub_cancel, hFD _ hd, mul_one] at h
    exact h
  rw [h1]
  apply hc
  rw [← Units.val_pow_eq_pow_val, ← val_nsmul_of_mem pts hadd gl b hMstab hFM, hFD _ (hqD m), Units.val_one]

end PartTwo
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar.Car P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar"

section Count

variable {O : Type} [CommRing O] [Algebra O (𝔏)] {HO : Type} [CommRing HO] [HopfAlgebra O HO]
variable [Module.Finite O HO] [Module.Free O HO] [Coalgebra.IsCocomm O HO]
variable {I : Subgroup (𝔏 ≃ₐ[𝔎] 𝔏)} {J : Type} [AddCommGroup J] [DistribMulAction ↥I J]
variable {M : AddSubgroup J} (pts : WithConv (HO →ₐ[O] 𝔏) ≃ ↥M)
variable (hadd : ∀ f g, pts (f * g) = pts f + pts g)
variable {ι : Type} [Fintype ι] [DecidableEq ι] (gl : GLData O HO (𝔏)) (b : Module.Basis ι O HO)
variable [Finite ↥M] (hMstab : ∀ (σ : ↥I) (x : J), x ∈ M → σ • x ∈ M)

theorem natCard_M₂ [Nontrivial O] (hcard : Nat.card ↥M = Module.finrank O HO) :
    Nat.card ↥(M₂ pts hadd gl b hMstab) = Nat.card ↥M := by
  rw [← Nat.card_congr (pts₂ pts hadd gl b hMstab hcard),
    Nat.card_congr (⟨WithConv.ofConv, WithConv.toConv, fun _ => rfl, fun _ => rfl⟩ :
      WithConv (CartierDual O HO →ₐ[O] 𝔏) ≃ (CartierDual O HO →ₐ[O] 𝔏)),
    HopfAlgebra.natCard_algHom_eq_finrank_of_charZero (O) (CartierDual O HO) (𝔏),
    CartierDual.finrank_eq, hcard]

def toHom (F : ↥(M₂ pts hadd gl b hMstab)) : Multiplicative ↥M →* (𝔏)ˣ where
  toFun m := (F : Car ↥M (rhoM M hMstab)).val m.toAdd
  map_one' := val_zero_of_mem pts hadd gl b hMstab F.2
  map_mul' m m' := val_add_of_mem pts hadd gl b hMstab F.2 m.toAdd m'.toAdd

theorem toHom_injective : Function.Injective (toHom pts hadd gl b hMstab) := by
  intro F G h
  apply Subtype.ext
  apply Car.ext
  intro m
  exact DFunLike.congr_fun h (Multiplicative.ofAdd m)

theorem toHom_bijective [Nontrivial O] (hcard : Nat.card ↥M = Module.finrank O HO) :
    Function.Bijective (toHom pts hadd gl b hMstab) := by
  haveI : NeZero (Monoid.exponent (Multiplicative ↥M)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have hhom : Nat.card (Multiplicative ↥M →* (𝔏)ˣ) = Nat.card ↥M :=
    (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Multiplicative ↥M) (𝔏)).trans
      (Nat.card_congr ⟨Multiplicative.toAdd, Multiplicative.ofAdd, fun _ => rfl, fun _ => rfl⟩)
  haveI : Finite (Multiplicative ↥M →* (𝔏)ˣ) :=
    Nat.finite_of_card_ne_zero (by rw [hhom]; exact Nat.card_pos.ne')
  refine (toHom_injective pts hadd gl b hMstab).bijective_of_nat_card_le ?_
  rw [hhom, natCard_M₂ pts hadd gl b hMstab hcard]

theorem natCard_S₂_mul [Nontrivial O] (hcard : Nat.card ↥M = Module.finrank O HO) (S : AddSubgroup J) (hSM : S ≤ M) :
    Nat.card ↥(S₂ pts hadd gl b hMstab S) * Nat.card ↥S = Nat.card ↥M := by
  classical
  haveI : NeZero (Monoid.exponent (Multiplicative ↥M)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  let H : Subgroup (Multiplicative ↥M) := AddSubgroup.toSubgroup (S.addSubgroupOf M)
  have hH : Nat.card ↥H = Nat.card ↥S := by
    rw [← Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hSM).toEquiv]
    exact Nat.card_congr
      ⟨fun x => ⟨x.1.toAdd, (Multiplicative.mem_toSubgroup _ _).mp x.2⟩,
       fun y => ⟨Multiplicative.ofAdd y.1, (Multiplicative.mem_toSubgroup _ _).mpr y.2⟩,
       fun _ => rfl, fun _ => rfl⟩

  have hS₂ : Nat.card ↥(S₂ pts hadd gl b hMstab S) = Nat.card (MonoidHom.domRestrictHom H (𝔏)ˣ).ker := by
    refine Nat.card_eq_of_bijective
      (fun F => ⟨toHom pts hadd gl b hMstab ⟨F.1, F.2.1⟩, MonoidHom.mem_ker.mpr (MonoidHom.ext fun h => ?_)⟩) ⟨?_, ?_⟩
    · rw [MonoidHom.domRestrictHom_apply, MonoidHom.domRestrict_apply, MonoidHom.one_apply]
      exact F.2.2 h.1.toAdd (AddSubgroup.mem_addSubgroupOf.mp ((Multiplicative.mem_toSubgroup _ _).mp h.2))
    · intro F G h
      have h1 := toHom_injective pts hadd gl b hMstab (congrArg Subtype.val h)
      exact Subtype.ext (congrArg (fun x : ↥(M₂ pts hadd gl b hMstab) => x.1) h1)
    · rintro ⟨ψ, hψ⟩
      obtain ⟨F, hF⟩ := (toHom_bijective pts hadd gl b hMstab hcard).2 ψ
      refine ⟨⟨F.1, F.2, fun m hm => ?_⟩, Subtype.ext hF⟩
      have h1 := DFunLike.congr_fun (MonoidHom.mem_ker.mp hψ)
        (⟨Multiplicative.ofAdd m, (Multiplicative.mem_toSubgroup _ _).mpr (AddSubgroup.mem_addSubgroupOf.mpr hm)⟩ : ↥H)
      rw [MonoidHom.domRestrictHom_apply, MonoidHom.domRestrict_apply, MonoidHom.one_apply, ← hF] at h1
      exact h1
  have hker := CommGroup.card_domRestrictHom_ker (M := 𝔏) H
  have hlag := H.card_eq_card_quotient_mul_card_subgroup
  rw [hS₂, hker, ← hH, ← Nat.card_congr (⟨Multiplicative.toAdd, Multiplicative.ofAdd, fun _ => rfl, fun _ => rfl⟩ :
    Multiplicative ↥M ≃ ↥M)]
  rw [hlag]

theorem natCard_S₂ [Nontrivial O] (hcard : Nat.card ↥M = Module.finrank O HO) (q m : ℕ) (hq0 : q ≠ 0)
    (hcardM : Nat.card ↥M = q ^ (2 * m)) (S : AddSubgroup J) (hSM : S ≤ M) (hcardS : Nat.card ↥S = q ^ m) :
    Nat.card ↥(S₂ pts hadd gl b hMstab S) = q ^ m := by
  have h := natCard_S₂_mul pts hadd gl b hMstab hcard S hSM
  rw [hcardS, hcardM, two_mul, pow_add] at h
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.pos_of_ne_zero hq0) m) h

end Count
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar.Car P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar"

section Flag

theorem natCard_eq_pow_of_prime_nsmul_eq_zero (q : ℕ) [Fact q.Prime] (V : Type) [AddCommGroup V] [Finite V]
    (hV : ∀ x : V, q • x = 0) : ∃ s : ℕ, Nat.card V = q ^ s := by
  classical
  letI : Module (ZMod q) V := AddCommGroup.zmodModule hV
  haveI : Module.Finite (ZMod q) V := Module.Finite.of_finite
  letI : Fintype V := Fintype.ofFinite V
  refine ⟨Module.finrank (ZMod q) V, ?_⟩
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod q) (V := V), ZMod.card]

theorem exists_surjective_dualFlag
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (𝔏))
    (O : Type) [CommRing O] [IsDomain O] [Algebra O (𝔏)] [FaithfulSMul O (𝔏)]
    (hOA : ∀ x : O, algebraMap O (𝔏) x ∈ A)
    (hOdvr : IsDiscreteValuationRing O) (hOirr : Irreducible ((q : ℕ) : O))
    (hOfix : ∀ σ : 𝔏 ≃ₐ[𝔎] 𝔏,
      σ ∈ A.inertiaSubgroupIn 𝔎 ↔ ∀ x : O, σ (algebraMap O (𝔏) x) = algebraMap O (𝔏) x)
    (hOmax : ∀ y ∈ A, (∀ σ ∈ A.inertiaSubgroupIn 𝔎, σ y = y) → ∃ x : O, algebraMap O (𝔏) x = y)
    (HO : Type) [CommRing HO] [HopfAlgebra O HO]
    [Module.Finite O HO] [Module.Flat O HO] [Coalgebra.IsCocomm O HO] [Module.Free O HO]
    {J : Type} [AddCommGroup J]
    [DistribMulAction ↥(A.inertiaSubgroupIn 𝔎) J]
    (M : AddSubgroup J)
    (pts : WithConv (HO →ₐ[O] 𝔏) ≃ ↥M)
    (hadd : ∀ f g, pts (f * g) = pts f + pts g)
    (hact : ∀ (σ : ↥(A.inertiaSubgroupIn 𝔎)) (f g : WithConv (HO →ₐ[O] 𝔏)),
      (∀ x : HO, g x = (σ : 𝔏 ≃ₐ[𝔎] 𝔏) (f x)) → ((pts g : ↥M) : J) = σ • ((pts f : ↥M) : J))
    (hMstab : ∀ (σ : ↥(A.inertiaSubgroupIn 𝔎)) (x : J), x ∈ M → σ • x ∈ M)
    [Finite ↥M] (hMq : ∀ x : ↥M, q • x = 0)
    (S : AddSubgroup J) (hSM : S ≤ M)
    (hdisp : ∀ (σ : ↥(A.inertiaSubgroupIn 𝔎)) (m : ↥M), σ • (m : J) - m ∈ S)
    (n : (𝔏 ≃ₐ[𝔎] 𝔏) → ℕ)
    (hn : ∀ (σ : 𝔏 ≃ₐ[𝔎] 𝔏) (ζ : 𝔏),
      ζ ^ q = 1 → σ ζ = ζ ^ (n σ))
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (gl : GLData O HO (𝔏)) (b : Module.Basis ι O HO) :
    ∃ (a : ℕ), q ^ a * Nat.card ↥S = Nat.card ↥M ∧
      ∃ p : CartierDual O HO →ₐc[O] MonoidAlgebra O (Multiplicative (Fin a → ZMod q)),
        Function.Surjective p ∧
        ∀ f : CartierDual O HO →ₐ[O] 𝔏,
          (∃ g : MonoidAlgebra O (Multiplicative (Fin a → ZMod q)) →ₐ[O] 𝔏,
              g.comp (p : CartierDual O HO →ₐ[O] MonoidAlgebra O (Multiplicative (Fin a → ZMod q))) = f) ↔
            ∀ m : ↥M, (m : J) ∈ S → pair b f (WithConv.ofConv (pts.symm m)) = 1 := by
  classical
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  haveI : IsDiscreteValuationRing O := hOdvr
  haveI : Nontrivial O := inferInstance
  have hcard : Nat.card ↥M = Module.finrank O HO := by
    rw [← HopfAlgebra.natCard_algHom_eq_finrank_of_charZero O HO (𝔏), ← Nat.card_congr pts]
    exact Nat.card_congr (⟨WithConv.ofConv, WithConv.toConv, fun _ => rfl, fun _ => rfl⟩ :
      WithConv (HO →ₐ[O] 𝔏) ≃ (HO →ₐ[O] 𝔏))
  have hqM : ∀ x : ↥M, ((q • x : ↥M) : J) ∈ S := fun x => by
    rw [hMq x, ZeroMemClass.coe_zero]; exact S.zero_mem

  let D' : Submonoid (WithConv (CartierDual O HO →ₐ[O] 𝔏)) :=
    { carrier := {f | chi pts hadd gl b hMstab (WithConv.ofConv f) ∈ S₂ pts hadd gl b hMstab S}
      one_mem' := by
        show chi pts hadd gl b hMstab (WithConv.ofConv 1) ∈ S₂ pts hadd gl b hMstab S
        rw [chi_one]; exact AddSubgroup.zero_mem _
      mul_mem' := fun {f g} hf hg => by
        show chi pts hadd gl b hMstab (WithConv.ofConv (f * g)) ∈ S₂ pts hadd gl b hMstab S
        rw [chi_mul]; exact AddSubgroup.add_mem _ hf hg }
  have hD'mem : ∀ f, f ∈ D' ↔ chi pts hadd gl b hMstab (WithConv.ofConv f) ∈ S₂ pts hadd gl b hMstab S := fun _ => Iff.rfl

  have hchi_pow : ∀ (f : WithConv (CartierDual O HO →ₐ[O] 𝔏)) (k : ℕ),
      chi pts hadd gl b hMstab (WithConv.ofConv (f ^ k)) = k • chi pts hadd gl b hMstab (WithConv.ofConv f) := by
    intro f k
    induction k with
    | zero => rw [pow_zero, zero_nsmul, chi_one]
    | succ k ih => rw [pow_succ, chi_mul, ih, succ_nsmul]

  obtain ⟨s, hs⟩ := natCard_eq_pow_of_prime_nsmul_eq_zero q ↥M hMq
  haveI : Finite ↥S := Finite.of_injective (fun x : ↥S => (⟨x.1, hSM x.2⟩ : ↥M)) (fun x y h => Subtype.ext (congrArg (fun z : ↥M => (z : J)) h))
  have hSq : ∀ x : ↥S, q • x = 0 := fun x => by
    have := hMq ⟨x.1, hSM x.2⟩
    exact Subtype.ext (by simpa using congrArg (fun z : ↥M => (z : J)) this)
  obtain ⟨a', ha'⟩ := natCard_eq_pow_of_prime_nsmul_eq_zero q ↥S hSq
  have hmul := natCard_S₂_mul pts hadd gl b hMstab hcard S hSM
  have hle : a' ≤ s := by
    have hdvd : q ^ a' ∣ q ^ s := by rw [← ha', ← hs, ← hmul]; exact Dvd.intro_left _ rfl
    exact (Nat.pow_dvd_pow_iff_le_right (Fact.out : q.Prime).one_lt).mp hdvd
  have hcardS₂ : Nat.card ↥(S₂ pts hadd gl b hMstab S) = q ^ (s - a') := by
    have h2 : Nat.card ↥(S₂ pts hadd gl b hMstab S) * q ^ a' = q ^ (s - a') * q ^ a' := by
      rw [← pow_add, Nat.sub_add_cancel hle, ← ha', hmul, hs]
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.pos_of_ne_zero hq0) a') h2
  have hcardD' : Nat.card ↥D' = q ^ (s - a') := by
    rw [← hcardS₂]
    refine Nat.card_congr (Equiv.ofBijective
      (fun f : ↥D' => (⟨chi pts hadd gl b hMstab (WithConv.ofConv f.1), (hD'mem f.1).mp f.2⟩ : ↥(S₂ pts hadd gl b hMstab S))) ⟨?_, ?_⟩)
    · intro f g hfg
      have h1 : chi pts hadd gl b hMstab (WithConv.ofConv f.1) = chi pts hadd gl b hMstab (WithConv.ofConv g.1) := congrArg Subtype.val hfg
      exact Subtype.ext (chi_injective pts hadd gl b hMstab hcard h1)
    · rintro ⟨F, hF⟩
      obtain ⟨f, hf⟩ := (S₂_le pts hadd gl b hMstab S) hF
      refine ⟨⟨f, ?_⟩, Subtype.ext hf⟩
      show chi pts hadd gl b hMstab (WithConv.ofConv f) ∈ S₂ pts hadd gl b hMstab S
      have hf' : chi pts hadd gl b hMstab (WithConv.ofConv f) = F := hf
      rw [hf']; exact hF

  have hD' : ∀ σ ∈ A.inertiaSubgroupIn 𝔎, ∀ c : ℕ,
      (∀ ζ : 𝔏, ζ ^ q = 1 → σ ζ = ζ ^ c) →
      ∀ f ∈ D', ∀ g : WithConv (CartierDual O HO →ₐ[O] 𝔏),
        (∀ h : CartierDual O HO, g h = σ (f h)) → g = f ^ c := by
    intro σ hσ c hc f hf g hfg
    apply chi_injective pts hadd gl b hMstab hcard
    show chi pts hadd gl b hMstab (WithConv.ofConv g) = chi pts hadd gl b hMstab (WithConv.ofConv (f ^ c))
    have h1 := pts₂_act pts hadd gl b hMstab hcard hOfix hact ⟨σ, hσ⟩ f g hfg
    rw [pts₂_val, pts₂_val] at h1
    rw [h1, hchi_pow]
    exact smul_eq_nsmul_of_mem_S₂ pts hadd gl b hMstab S q hqM hdisp ⟨σ, hσ⟩ c hc _ hf

  obtain ⟨p, hp, hdict⟩ :=
    HopfAlgebra.exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid_of_isAlgClosed q hq2 A O hOA hOdvr hOirr hOfix hOmax
      (CartierDual O HO) D' (s - a') hcardD' hD'
  refine ⟨s - a', ?_, p, hp, fun f => (hdict f).trans ?_⟩
  · rw [← hcardS₂, hmul]
  · show WithConv.toConv f ∈ D' ↔ _
    rw [hD'mem, WithConv.ofConv_toConv, mem_S₂]
    constructor
    · rintro ⟨-, h⟩ m hm
      have h1 := congrArg (fun u : (𝔏)ˣ => (u : 𝔏)) (h m hm)
      rwa [chi_val, Units.val_one] at h1
    · intro h
      exact ⟨⟨WithConv.toConv f, rfl⟩,
        fun m hm => Units.ext (by rw [chi_val, Units.val_one]; exact h m hm)⟩

end Flag
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar.Car P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar"

end DualFlag
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar.Car P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar"

namespace BlockIdempotents

open DualPairing

theorem exists_convMul_eq_one_of_comm {R H L : Type} [CommRing R] [CommRing H] [HopfAlgebra R H]
    [CommRing L] [Algebra R L]
    (f : WithConv (H →ₐ[R] L)) : ∃ g : WithConv (H →ₐ[R] L), g * f = 1 := by
  let S : H →ₐ[R] H :=
    { toFun := fun h => HopfAlgebra.antipode R h
      map_one' := HopfAlgebra.antipode_one
      map_mul' := fun x y => by rw [HopfAlgebra.antipode_mul, mul_comm]
      map_zero' := map_zero _
      map_add' := fun x y => map_add _ x y
      commutes' := fun r => by
        rw [Algebra.algebraMap_eq_smul_one, map_smul, HopfAlgebra.antipode_one] }
  have hS : ∀ h, S h = HopfAlgebra.antipode R h := fun _ => rfl
  refine ⟨WithConv.toConv ((WithConv.ofConv f).comp S), ?_⟩
  apply WithConv.ext
  apply AlgHom.ext
  intro h
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply, WithConv.ofConv_toConv]
  have key : ∀ t : TensorProduct R H H,
      Algebra.TensorProduct.lift ((WithConv.ofConv f).comp S) (WithConv.ofConv f)
          (fun _ _ => Commute.all _ _) t
        = (WithConv.ofConv f) (LinearMap.mul' R H ((HopfAlgebra.antipode R).rTensor H t)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
        rw [Algebra.TensorProduct.lift_tmul, LinearMap.rTensor_tmul, LinearMap.mul'_apply, map_mul,
          AlgHom.comp_apply, hS]
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add, map_add]
  rw [key, HopfAlgebra.mul_antipode_rTensor_comul_apply, AlgHom.commutes]

section Construction

variable (t : ℕ) [NeZero t] {Γ : Type} [CommGroup Γ] [Fintype Γ] [DecidableEq Γ]

variable (Γ) in

def enum (hΓ : Fintype.card Γ = t) : Fin t ≃ Γ :=
  let e : Fin t ≃ Γ := (finCongr hΓ.symm).trans (Fintype.equivFin Γ).symm
  e.trans (Equiv.swap (e 0) 1)

theorem enum_zero (hΓ : Fintype.card Γ = t) : enum t Γ hΓ 0 = 1 := by
  show Equiv.swap _ 1 _ = 1
  exact Equiv.swap_apply_left _ _

variable (O : Type) [CommRing O] [Nontrivial O] [Algebra O (𝔏)] [FaithfulSMul O (𝔏)]

variable (Γ) in

def bG : Module.Basis Γ O
    (MonoidAlgebra O Γ) :=
  MonoidAlgebra.basis Γ O

omit [NeZero t] [CommGroup Γ] [Fintype Γ] [DecidableEq Γ] in
theorem bG_apply (x : Γ) : bG Γ O x = MonoidAlgebra.single x 1 :=
  MonoidAlgebra.basis_apply O x

variable (Γ) (𝔏) in

def BB : Module.Basis Γ (𝔏)
    (𝔏 ⊗[O] MonoidAlgebra O Γ) :=
  Algebra.TensorProduct.basis (𝔏) (bG Γ O)

omit [NeZero t] [CommGroup Γ] [Fintype Γ] [DecidableEq Γ] in
theorem BB_apply (x : Γ) :
    BB 𝔏 Γ O x = (1 : 𝔏) ⊗ₜ[O] bG Γ O x :=
  Algebra.TensorProduct.basis_apply _ _

omit [NeZero t] in
theorem BB_mul (x y : Γ) : BB 𝔏 Γ O x * BB 𝔏 Γ O y = BB 𝔏 Γ O (x * y) := by
  rw [BB_apply, BB_apply, BB_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, bG_apply, bG_apply,
    bG_apply, MonoidAlgebra.single_mul_single, one_mul]

omit [NeZero t] in
theorem BB_one : BB 𝔏 Γ O 1 = 1 := by
  rw [BB_apply, bG_apply, ← MonoidAlgebra.one_def, ← Algebra.TensorProduct.one_def]

omit [NeZero t] in

theorem db_bG_eq (e : CartierDual O (MonoidAlgebra O Γ)
      ≃ₐ[O] (Γ → O))
    (he : ∀ φ x, e φ x = φ (MonoidAlgebra.single x 1)) (x : Γ) :
    db (bG Γ O) x = e.symm (Pi.single x 1) := by
  apply e.injective
  rw [AlgEquiv.apply_symm_apply]
  funext y
  rw [he, ← bG_apply O, db_apply_basis, Pi.single_apply]

theorem algebraMap_injective_O : Function.Injective (algebraMap O (𝔏)) :=
  FaithfulSMul.algebraMap_injective O (𝔏)

section coordinates

variable {G' : Type} [DecidableEq G']

theorem single_one_mul_self (x : G') : (Pi.single x (1 : O) : G' → O) * Pi.single x 1 = Pi.single x 1 := by
  funext y
  simp only [Pi.mul_apply, Pi.single_apply]
  split_ifs <;> simp

theorem single_one_mul_single_one_of_ne {x y : G'} (hxy : x ≠ y) :
    (Pi.single x (1 : O) : G' → O) * Pi.single y 1 = 0 := by
  funext z
  simp only [Pi.mul_apply, Pi.single_apply, Pi.zero_apply]
  split_ifs with h1 h2
  · exact absurd (h1.symm.trans h2) hxy
  all_goals simp

variable [Fintype G']

theorem sum_single_one : (∑ x : G', (Pi.single x (1 : O) : G' → O)) = 1 :=
  Finset.univ_sum_single (1 : G' → O)

end coordinates
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar.Car P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar"

variable {O}
variable {HO : Type} [CommRing HO] [HopfAlgebra O HO] [Module.Finite O HO] [Module.Free O HO]
  [Coalgebra.IsCocomm O HO]
variable {Bq : Type} [CommRing Bq] [HopfAlgebra O Bq]
variable (π : CartierDual O HO →ₐc[O] Bq)
variable (θ : Bq ≃ₐc[O] MonoidAlgebra O Γ)
variable (bd : HO ≃ₐc[O] CartierDual O (CartierDual O HO))

def θπ : CartierDual O HO →ₐc[O] MonoidAlgebra O Γ := θ.toBialgHom.comp π

omit [NeZero t] in
theorem θπ_apply (d : CartierDual O HO) : θπ π θ d = θ (π d) := rfl

omit [NeZero t] in
theorem θπ_surjective (hπ : Function.Surjective π) : Function.Surjective (θπ π θ) := fun y =>
  let ⟨b, hb⟩ := θ.surjective y
  let ⟨d, hd⟩ := hπ b
  ⟨d, by rw [θπ_apply, hd]; exact hb⟩

def epsOf (x : Γ) : HO :=
  bd.symm (CartierDual.map (θπ π θ) (db (bG Γ O) x))

def epsFam (hΓ : Fintype.card Γ = t) : Fin t → HO := fun i => epsOf π θ bd (enum t Γ hΓ i)

theorem epsFam_apply (hΓ : Fintype.card Γ = t) (i : Fin t) :
    epsFam t π θ bd hΓ i = epsOf π θ bd (enum t Γ hΓ i) := rfl

def Phi (e : CartierDual O (MonoidAlgebra O Γ)
      ≃ₐ[O] (Γ → O)) :
    (Γ → O) →ₐ[O] HO :=
  ((bd.symm : CartierDual O (CartierDual O HO) ≃ₐ[O] HO) : CartierDual O (CartierDual O HO) →ₐ[O] HO).comp
    (((CartierDual.map (θπ π θ) : CartierDual O (MonoidAlgebra O Γ) →ₐ[O]
        CartierDual O (CartierDual O HO))).comp
      (e.symm : (Γ → O) →ₐ[O]
        CartierDual O (MonoidAlgebra O Γ)))

theorem epsOf_eq_Phi (e : CartierDual O (MonoidAlgebra O Γ)
      ≃ₐ[O] (Γ → O))
    (he : ∀ φ x, e φ x = φ (MonoidAlgebra.single x 1)) (x : Γ) :
    epsOf π θ bd x = Phi π θ bd e (Pi.single x 1) := by
  unfold epsOf Phi
  rw [db_bG_eq O e he x]
  rfl

theorem epsOf_ne_zero (hπ : Function.Surjective π) (x : Γ) :
    epsOf π θ bd x ≠ 0 := by
  intro h0
  have h1 : CartierDual.map (θπ π θ) (db (bG Γ O) x) = 0 := by
    apply bd.symm.injective
    rw [map_zero]
    exact h0
  have h2 : ∀ y, db (bG Γ O) x y = (0 : O) := by
    intro y
    obtain ⟨d, rfl⟩ := θπ_surjective π θ hπ y
    have h1d := DFunLike.congr_fun h1 d
    rw [CartierDual.map_apply] at h1d
    exact h1d
  have h3 := db_apply_basis (bG Γ O) x x
  rw [if_pos rfl, h2] at h3
  exact zero_ne_one h3

def Ψ (ψ : HO →ₐ[O] 𝔏) : CartierDual O (CartierDual O HO) →ₐ[O] 𝔏 :=
  ψ.comp (bd.symm.toBialgHom : CartierDual O (CartierDual O HO) →ₐ[O] HO)

theorem Ψ_convMul (ψ₁ ψ₂ : WithConv (HO →ₐ[O] 𝔏)) :
    WithConv.toConv (Ψ bd (ψ₁ * ψ₂).ofConv).toLinearMap
      = WithConv.toConv (Ψ bd ψ₁.ofConv).toLinearMap * WithConv.toConv (Ψ bd ψ₂.ofConv).toLinearMap := by
  unfold Ψ
  rw [AlgHom.convMul_comp_bialgHom_distrib ψ₁ ψ₂ bd.symm.toBialgHom]
  exact AlgHom.toLinearMap_convMul _ _

variable (e : CartierDual O (MonoidAlgebra O Γ)
  ≃ₐ[O] (Γ → O))
variable (he : ∀ φ x, e φ x = φ (MonoidAlgebra.single x 1))
variable (glD : GLData O (CartierDual O HO) (𝔏))

def T (ψ : HO →ₐ[O] 𝔏) : 𝔏 ⊗[O] CartierDual O HO :=
  (glD.e (Ψ bd ψ)).val

def X (ψ : HO →ₐ[O] 𝔏) :
    𝔏 ⊗[O] MonoidAlgebra O Γ :=
  Algebra.TensorProduct.map (AlgHom.id O (𝔏))
    (θπ π θ : CartierDual O HO →ₐ[O] MonoidAlgebra O Γ) (T bd glD ψ)

theorem rid_lTensor_X (ψ : HO →ₐ[O] 𝔏)
    (φ : CartierDual O (MonoidAlgebra O Γ)) :
    TensorProduct.rid O (𝔏)
        (LinearMap.lTensor (𝔏) (CartierDual.toDual O _ φ) (X π θ bd glD ψ))
      = Ψ bd ψ (CartierDual.map (θπ π θ) φ) := by
  rw [← glD.pairing (Ψ bd ψ) (CartierDual.map (θπ π θ) φ)]
  unfold X T
  have hmaps :
      (TensorProduct.rid O (𝔏)).toLinearMap
          ∘ₗ LinearMap.lTensor (𝔏) (CartierDual.toDual O _ φ)
          ∘ₗ (Algebra.TensorProduct.map (AlgHom.id O (𝔏))
              (θπ π θ : CartierDual O HO →ₐ[O] MonoidAlgebra O Γ)).toLinearMap
        = (TensorProduct.rid O (𝔏)).toLinearMap
          ∘ₗ LinearMap.lTensor (𝔏) (CartierDual.toDual O _ (CartierDual.map (θπ π θ) φ)) :=
    TensorProduct.ext' fun _ _ => rfl
  exact LinearMap.congr_fun hmaps (glD.e (Ψ bd ψ)).val

theorem X_eq_sum (ψ : HO →ₐ[O] 𝔏) :
    X π θ bd glD ψ = ∑ x, ψ (epsOf π θ bd x) ⊗ₜ[O] bG Γ O x := by
  rw [eq_sum_tmul_of_pairing (bG Γ O) (X π θ bd glD ψ)
    ((Ψ bd ψ).comp (CartierDual.map (θπ π θ) :
      CartierDual O (MonoidAlgebra O Γ) →ₐ[O] CartierDual O (CartierDual O HO)))
    (fun φ => rid_lTensor_X π θ bd glD ψ φ)]
  rfl

omit [NeZero t] in
theorem X_mul (ψ₁ ψ₂ : WithConv (HO →ₐ[O] 𝔏)) :
    X π θ bd glD (ψ₁ * ψ₂).ofConv = X π θ bd glD ψ₁.ofConv * X π θ bd glD ψ₂.ofConv := by
  unfold X T
  rw [glD.mul _ _ _ (Ψ_convMul bd ψ₁ ψ₂)]
  exact map_mul _ _ _

omit [NeZero t] in
theorem X_eq_map_θ (ψ : HO →ₐ[O] 𝔏) :
    X π θ bd glD ψ
      = Algebra.TensorProduct.map (AlgHom.id O (𝔏))
          ((θ : Bq ≃ₐ[O] MonoidAlgebra O Γ) :
            Bq →ₐ[O] MonoidAlgebra O Γ)
          (Algebra.TensorProduct.map (AlgHom.id O (𝔏)) (π : CartierDual O HO →ₐ[O] Bq)
            (T bd glD ψ)) := by
  unfold X
  have hmaps :
      (Algebra.TensorProduct.map (AlgHom.id O (𝔏))
          (θπ π θ : CartierDual O HO →ₐ[O] MonoidAlgebra O Γ)).toLinearMap
        = ((Algebra.TensorProduct.map (AlgHom.id O (𝔏))
              ((θ : Bq ≃ₐ[O] MonoidAlgebra O Γ) :
                Bq →ₐ[O] MonoidAlgebra O Γ)).comp
            (Algebra.TensorProduct.map (AlgHom.id O (𝔏))
              (π : CartierDual O HO →ₐ[O] Bq))).toLinearMap :=
    TensorProduct.ext' fun _ _ => rfl
  exact LinearMap.congr_fun hmaps (T bd glD ψ)

omit [NeZero t] [Fintype Γ] [DecidableEq Γ] in
theorem map_θ_eq_one_iff (Y : 𝔏 ⊗[O] Bq) :
    Algebra.TensorProduct.map (AlgHom.id O (𝔏))
        ((θ : Bq ≃ₐ[O] MonoidAlgebra O Γ) :
          Bq →ₐ[O] MonoidAlgebra O Γ) Y = 1 ↔ Y = 1 := by
  constructor
  · intro h
    have hback : ∀ Z : 𝔏 ⊗[O] Bq,
        Algebra.TensorProduct.map (AlgHom.id O (𝔏))
          (((θ : Bq ≃ₐ[O] MonoidAlgebra O Γ).symm :
            MonoidAlgebra O Γ →ₐ[O] Bq))
          (Algebra.TensorProduct.map (AlgHom.id O (𝔏))
            ((θ : Bq ≃ₐ[O] MonoidAlgebra O Γ) :
              Bq →ₐ[O] MonoidAlgebra O Γ) Z) = Z := by
      intro Z
      induction Z using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | tmul c b =>
        exact congrArg (fun z : Bq => c ⊗ₜ[O] z)
          ((θ : Bq ≃ₐ[O] MonoidAlgebra O Γ).symm_apply_apply b)
      | add s t hs ht => rw [map_add, map_add, hs, ht]
    rw [← hback Y, h, map_one]
  · rintro rfl
    exact map_one _

section withCoordinates

include he

theorem epsOf_mul_self (x : Γ) :
    epsOf π θ bd x * epsOf π θ bd x = epsOf π θ bd x := by
  rw [epsOf_eq_Phi π θ bd e he, ← map_mul, single_one_mul_self]

theorem isIdempotentElem_epsOf (x : Γ) : IsIdempotentElem (epsOf π θ bd x) :=
  epsOf_mul_self π θ bd e he x

theorem epsOf_mul_epsOf_of_ne {x y : Γ} (hxy : x ≠ y) :
    epsOf π θ bd x * epsOf π θ bd y = 0 := by
  rw [epsOf_eq_Phi π θ bd e he, epsOf_eq_Phi π θ bd e he, ← map_mul, single_one_mul_single_one_of_ne O hxy,
    map_zero]

theorem sum_epsOf : (∑ x, epsOf π θ bd x) = 1 := by
  simp_rw [epsOf_eq_Phi π θ bd e he]
  rw [← map_sum, sum_single_one, map_one]

theorem sum_epsFam (hΓ : Fintype.card Γ = t) : (∑ i, epsFam t π θ bd hΓ i) = 1 :=
  (Equiv.sum_comp (enum t Γ hΓ) (fun x => epsOf π θ bd x)).trans (sum_epsOf π θ bd e he)

theorem apply_epsOf_eq_zero_or_one (ψ : WithConv (HO →ₐ[O] 𝔏))
    (x : Γ) :
    ψ (epsOf π θ bd x) = 0 ∨ ψ (epsOf π θ bd x) = 1 :=
  IsIdempotentElem.iff_eq_zero_or_one.mp (by
    show ψ.ofConv (epsOf π θ bd x) * ψ.ofConv (epsOf π θ bd x) = ψ.ofConv (epsOf π θ bd x)
    rw [← map_mul, epsOf_mul_self π θ bd e he])

theorem existsUnique_apply_epsOf_eq_one (ψ : WithConv (HO →ₐ[O] 𝔏)) :
    ∃! x : Γ, ψ (epsOf π θ bd x) = 1 := by
  have hsum : (∑ x, ψ (epsOf π θ bd x)) = 1 := by
    show (∑ x, ψ.ofConv (epsOf π θ bd x)) = 1
    rw [← map_sum, sum_epsOf π θ bd e he, map_one]
  have hex : ∃ x, ψ (epsOf π θ bd x) = 1 := by
    by_contra hnone
    push Not at hnone
    have hzero : ∀ x, ψ (epsOf π θ bd x) = 0 := fun x =>
      (apply_epsOf_eq_zero_or_one π θ bd e he ψ x).resolve_right (hnone x)
    rw [Finset.sum_eq_zero (fun x _ => hzero x)] at hsum
    exact zero_ne_one hsum
  obtain ⟨x, hx⟩ := hex
  refine ⟨x, hx, fun y hy => ?_⟩
  by_contra hyx
  have hprod : ψ (epsOf π θ bd y) * ψ (epsOf π θ bd x) = 0 := by
    show ψ.ofConv (epsOf π θ bd y) * ψ.ofConv (epsOf π θ bd x) = 0
    rw [← map_mul, epsOf_mul_epsOf_of_ne π θ bd e he hyx, map_zero]
  rw [hy, hx, one_mul] at hprod
  exact one_ne_zero hprod

def label (ψ : WithConv (HO →ₐ[O] 𝔏)) : Γ :=
  Classical.choose (existsUnique_apply_epsOf_eq_one π θ bd e he ψ).exists

theorem apply_epsOf_label (ψ : WithConv (HO →ₐ[O] 𝔏)) :
    ψ (epsOf π θ bd (label π θ bd e he ψ)) = 1 :=
  Classical.choose_spec (existsUnique_apply_epsOf_eq_one π θ bd e he ψ).exists

theorem label_eq_iff (ψ : WithConv (HO →ₐ[O] 𝔏)) (x : Γ) :
    label π θ bd e he ψ = x ↔ ψ (epsOf π θ bd x) = 1 := by
  constructor
  · rintro rfl
    exact apply_epsOf_label π θ bd e he ψ
  · intro hx
    exact (existsUnique_apply_epsOf_eq_one π θ bd e he ψ).unique (apply_epsOf_label π θ bd e he ψ) hx

theorem apply_epsOf_eq_ite (ψ : WithConv (HO →ₐ[O] 𝔏)) (x : Γ) :
    ψ (epsOf π θ bd x) = if x = label π θ bd e he ψ then 1 else 0 := by
  split_ifs with hx
  · rw [hx]
    exact apply_epsOf_label π θ bd e he ψ
  · refine (apply_epsOf_eq_zero_or_one π θ bd e he ψ x).resolve_right fun h1 => hx ?_
    exact ((label_eq_iff π θ bd e he ψ x).mpr h1).symm

theorem exists_label_eq (hπ : Function.Surjective π)
    {κ : Type} [Fintype κ] (pf : κ → (HO →ₐ[O] 𝔏)) (hinj : Function.Injective pf)
    (hcard : Fintype.card κ = Module.finrank O HO) (x : Γ) :
    ∃ ψ : WithConv (HO →ₐ[O] 𝔏), label π θ bd e he ψ = x := by
  by_contra hnone
  push Not at hnone
  have hzero : ∀ ψ : HO →ₐ[O] 𝔏, ψ (epsOf π θ bd x) = 0 := by
    intro ψ
    have hne := hnone (WithConv.toConv ψ)
    rw [Ne, label_eq_iff] at hne
    exact (apply_epsOf_eq_zero_or_one π θ bd e he (WithConv.toConv ψ) x).resolve_right hne
  have htmul : (1 : 𝔏) ⊗ₜ[O] epsOf π θ bd x = (0 : 𝔏 ⊗[O] HO) := by
    refine eval_injective pf hinj hcard _ _ fun i => ?_
    rw [evalAt_tmul, hzero, mul_zero, map_zero]
  apply epsOf_ne_zero π θ bd hπ x
  apply Algebra.TensorProduct.includeRight_injective (R := O) (A := 𝔏) (B := HO)
    (algebraMap_injective_O O)
  rw [Algebra.TensorProduct.includeRight_apply, map_zero, htmul]

include glD

theorem X_eq_BB_label (ψ : WithConv (HO →ₐ[O] 𝔏)) :
    X π θ bd glD ψ.ofConv = BB 𝔏 Γ O (label π θ bd e he ψ) := by
  rw [X_eq_sum]
  have hval : ∀ x, ψ.ofConv (epsOf π θ bd x) = if x = label π θ bd e he ψ then 1 else 0 :=
    fun x => apply_epsOf_eq_ite π θ bd e he ψ x
  simp_rw [hval]
  rw [Finset.sum_eq_single (label π θ bd e he ψ)]
  · rw [if_pos rfl, BB_apply]
  · intro x _ hx
    rw [if_neg hx, TensorProduct.zero_tmul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem label_mul (ψ₁ ψ₂ : WithConv (HO →ₐ[O] 𝔏)) :
    label π θ bd e he (ψ₁ * ψ₂) = label π θ bd e he ψ₁ * label π θ bd e he ψ₂ := by
  apply (BB 𝔏 Γ O).injective
  rw [← X_eq_BB_label π θ bd e he glD, X_mul, X_eq_BB_label π θ bd e he glD, X_eq_BB_label π θ bd e he glD,
    BB_mul]

theorem label_one : label π θ bd e he (1 : WithConv (HO →ₐ[O] 𝔏)) = 1 := by
  have h := label_mul π θ bd e he glD 1 1
  rw [one_mul] at h
  exact mul_eq_left.mp h.symm

theorem counit_epsOf_one : Coalgebra.counit (R := O) (epsOf π θ bd 1) = (1 : O) := by
  apply algebraMap_injective_O (𝔏 := 𝔏)
  rw [map_one, ← AlgHom.convOne_apply (R := O) (A := 𝔏) (epsOf π θ bd 1)]
  exact (label_eq_iff π θ bd e he 1 1).mp (label_one π θ bd e he glD)

theorem counit_epsOf_of_ne {x : Γ} (hx : x ≠ 1) :
    Coalgebra.counit (R := O) (epsOf π θ bd x) = (0 : O) := by
  apply algebraMap_injective_O (𝔏 := 𝔏)
  rw [map_zero, ← AlgHom.convOne_apply (R := O) (A := 𝔏) (epsOf π θ bd x),
    apply_epsOf_eq_ite π θ bd e he, label_one π θ bd e he glD, if_neg hx]

theorem natCard_fiber_eq (hπ : Function.Surjective π)
    {κ : Type} [Fintype κ] (pf : κ → (HO →ₐ[O] 𝔏)) (hinj : Function.Injective pf)
    (hcard : Fintype.card κ = Module.finrank O HO) (x : Γ) :
    Nat.card {ψ : WithConv (HO →ₐ[O] 𝔏) // label π θ bd e he ψ = x}
      = Nat.card {ψ : WithConv (HO →ₐ[O] 𝔏) // label π θ bd e he ψ = 1} := by
  obtain ⟨ψ₀, hψ₀⟩ := exists_label_eq π θ bd e he hπ pf hinj hcard x
  obtain ⟨ψ₀', hψ₀'⟩ := exists_convMul_eq_one_of_comm ψ₀
  have hψ₀'' : ψ₀ * ψ₀' = 1 := by rw [mul_comm]; exact hψ₀'
  have hlab' : label π θ bd e he ψ₀' * x = 1 := by
    rw [← hψ₀, ← label_mul π θ bd e he glD, hψ₀', label_one π θ bd e he glD]
  refine Nat.card_congr
    { toFun := fun ψ => ⟨ψ₀' * ψ.1, by rw [label_mul π θ bd e he glD, ψ.2, hlab']⟩
      invFun := fun χ => ⟨ψ₀ * χ.1, by rw [label_mul π θ bd e he glD, χ.2, mul_one, hψ₀]⟩
      left_inv := fun ψ => Subtype.ext (by
        show ψ₀ * (ψ₀' * ψ.1) = ψ.1
        rw [← mul_assoc, hψ₀'', one_mul])
      right_inv := fun χ => Subtype.ext (by
        show ψ₀' * (ψ₀ * χ.1) = χ.1
        rw [← mul_assoc, hψ₀', one_mul]) }

theorem natCard_label_fiber [Finite (WithConv (HO →ₐ[O] 𝔏))] (hπ : Function.Surjective π)
    {κ : Type} [Fintype κ] (pf : κ → (HO →ₐ[O] 𝔏)) (hinj : Function.Injective pf)
    (hcard : Fintype.card κ = Module.finrank O HO)
    (hΓ : Fintype.card Γ = t)
    (d : ℕ) (hcardP : Nat.card (WithConv (HO →ₐ[O] 𝔏)) = t * d) (x : Γ) :
    Nat.card {ψ : WithConv (HO →ₐ[O] 𝔏) // label π θ bd e he ψ = x} = d := by
  have hfib : ∀ y, Nat.card {ψ : WithConv (HO →ₐ[O] 𝔏) // label π θ bd e he ψ = y}
      = Nat.card {ψ : WithConv (HO →ₐ[O] 𝔏) // label π θ bd e he ψ = 1} :=
    fun y => natCard_fiber_eq π θ bd e he glD hπ pf hinj hcard y
  have hG : Fintype.card Γ = t := hΓ
  have htotal : Nat.card (WithConv (HO →ₐ[O] 𝔏))
      = t * Nat.card {ψ : WithConv (HO →ₐ[O] 𝔏) // label π θ bd e he ψ = 1} := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (label π θ bd e he)), Nat.card_sigma]
    simp_rw [hfib]
    rw [Finset.sum_const, Finset.card_univ, hG, smul_eq_mul]
  rw [hfib x]
  have hq : t * Nat.card {ψ : WithConv (HO →ₐ[O] 𝔏) // label π θ bd e he ψ = 1}
      = t * d := by
    rw [← htotal, hcardP]
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne t)) hq

theorem natCard_apply_epsOf_eq_one [Finite (WithConv (HO →ₐ[O] 𝔏))] (hπ : Function.Surjective π)
    {κ : Type} [Fintype κ] (pf : κ → (HO →ₐ[O] 𝔏)) (hinj : Function.Injective pf)
    (hcard : Fintype.card κ = Module.finrank O HO)
    (hΓ : Fintype.card Γ = t)
    (d : ℕ) (hcardP : Nat.card (WithConv (HO →ₐ[O] 𝔏)) = t * d) (x : Γ) :
    Nat.card {ψ : WithConv (HO →ₐ[O] 𝔏) // ψ (epsOf π θ bd x) = 1} = d :=
  (Nat.card_congr (Equiv.subtypeEquivRight fun ψ => (label_eq_iff π θ bd e he ψ x).symm)).trans
    (natCard_label_fiber t π θ bd e he glD hπ pf hinj hcard hΓ d hcardP x)

theorem apply_epsOf_one_eq_one_iff (ψ : WithConv (HO →ₐ[O] 𝔏)) :
    ψ (epsOf π θ bd 1) = 1
      ↔ Algebra.TensorProduct.map (AlgHom.id O (𝔏)) (π : CartierDual O HO →ₐ[O] Bq)
          (glD.e (ψ.ofConv.comp (bd.symm.toBialgHom : CartierDual O (CartierDual O HO) →ₐ[O] HO))).val = 1 := by
  rw [← label_eq_iff π θ bd e he ψ 1, ← map_θ_eq_one_iff θ]
  change _ ↔ Algebra.TensorProduct.map _ _ (Algebra.TensorProduct.map _ _ (T bd glD ψ.ofConv)) = 1
  rw [← X_eq_map_θ, X_eq_BB_label π θ bd e he glD, ← BB_one O]
  exact (BB 𝔏 Γ O).injective.eq_iff.symm

end withCoordinates
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar.Car P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar"

end Construction
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar.Car P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar"

theorem exists_epsFamily_generic
    (t : ℕ) [NeZero t] (d : ℕ) (O : Type) [CommRing O] [Algebra O (𝔏)] [FaithfulSMul O (𝔏)] [Nontrivial O]
    (HO : Type) [CommRing HO] [HopfAlgebra O HO] [Module.Finite O HO] [Module.Free O HO] [Coalgebra.IsCocomm O HO]
    (Bq : Type) [CommRing Bq] [HopfAlgebra O Bq]
    (π : CartierDual O HO →ₐc[O] Bq) (hπ : Function.Surjective π)
    (Γ : Type) [CommGroup Γ] (hΓ : Nat.card Γ = t)
    (θ : Bq ≃ₐc[O] MonoidAlgebra O Γ)
    (bd : HO ≃ₐc[O] CartierDual O (CartierDual O HO))
    (glD : DualPairing.GLData O (CartierDual O HO) (𝔏))
    [Finite (WithConv (HO →ₐ[O] 𝔏))]
    (hcardP : Nat.card (WithConv (HO →ₐ[O] 𝔏)) = t * d) :
    ∃ ε : Fin t → HO,
      (∀ i, IsIdempotentElem (ε i)) ∧
      (∀ i j, i ≠ j → ε i * ε j = 0) ∧
      (∑ i, ε i) = 1 ∧
      Coalgebra.counit (ε 0) = (1 : O) ∧
      (∀ i, i ≠ 0 → Coalgebra.counit (ε i) = (0 : O)) ∧
      (∀ ψ : WithConv (HO →ₐ[O] 𝔏), ∃! i : Fin t, ψ (ε i) = 1) ∧
      (∀ i : Fin t, Nat.card {ψ : WithConv (HO →ₐ[O] 𝔏) // ψ (ε i) = 1} = d) ∧
      (∀ (i : Fin t) (ψ χ : WithConv (HO →ₐ[O] 𝔏)), ψ (ε i) = 1 → χ (ε 0) = 1 → (ψ * χ) (ε i) = 1) ∧
      (∀ ψ : WithConv (HO →ₐ[O] 𝔏),
        ψ (ε 0) = 1 ↔
          Algebra.TensorProduct.map (AlgHom.id O (𝔏)) (π : CartierDual O HO →ₐ[O] Bq)
            (glD.e (ψ.ofConv.comp (bd.symm.toBialgHom : CartierDual O (CartierDual O HO) →ₐ[O] HO))).val = 1) := by
  classical
  haveI : Finite Γ := Nat.finite_of_card_ne_zero (by rw [hΓ]; exact NeZero.ne t)
  letI : Fintype Γ := Fintype.ofFinite Γ
  have hΓ' : Fintype.card Γ = t := by rw [← Nat.card_eq_fintype_card, hΓ]
  obtain ⟨e, he, -, -⟩ := CartierDual.exists_algEquiv_monoidAlgebra_pi O Γ
  haveI : Finite (HO →ₐ[O] 𝔏) := Finite.of_equiv _ (WithConv.equiv (HO →ₐ[O] 𝔏))
  letI : Fintype (HO →ₐ[O] 𝔏) := Fintype.ofFinite _
  let pf : (HO →ₐ[O] 𝔏) → (HO →ₐ[O] 𝔏) := id
  have hinj : Function.Injective pf := Function.injective_id
  have hcard : Fintype.card (HO →ₐ[O] 𝔏) = Module.finrank O HO := by
    rw [Fintype.card_eq_nat_card]
    exact HopfAlgebra.natCard_algHom_eq_finrank_of_charZero O HO (𝔏)
  refine ⟨epsFam t π θ bd hΓ', fun i => isIdempotentElem_epsOf π θ bd e he _,
    fun i j hij => epsOf_mul_epsOf_of_ne π θ bd e he ((enum t Γ hΓ').injective.ne hij),
    sum_epsFam t π θ bd e he hΓ', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [epsFam_apply, enum_zero]
    exact counit_epsOf_one π θ bd e he glD
  · intro i hi
    rw [epsFam_apply]
    refine counit_epsOf_of_ne π θ bd e he glD fun h1 => hi ?_
    rw [← enum_zero t hΓ'] at h1
    exact (enum t Γ hΓ').injective h1
  · intro ψ
    obtain ⟨x, hx, huniq⟩ := existsUnique_apply_epsOf_eq_one π θ bd e he ψ
    refine ⟨(enum t Γ hΓ').symm x, ?_, fun i hi => ?_⟩
    · dsimp only
      rw [epsFam_apply, Equiv.apply_symm_apply]
      exact hx
    · rw [Equiv.eq_symm_apply]
      exact huniq _ hi
  · intro i
    exact natCard_apply_epsOf_eq_one t π θ bd e he glD hπ pf hinj hcard hΓ' d hcardP _
  · intro i ψ χ hψ hχ
    rw [epsFam_apply] at hψ ⊢
    rw [epsFam_apply, enum_zero] at hχ
    rw [← label_eq_iff π θ bd e he] at hψ hχ ⊢
    rw [label_mul π θ bd e he glD, hψ, hχ, mul_one]
  · intro ψ
    rw [epsFam_apply, enum_zero]
    exact apply_epsOf_one_eq_one_iff π θ bd e he glD ψ

end BlockIdempotents
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar.Car P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar"

section GlueLemmas
open DualPairing
variable {O : Type} [CommRing O] [Algebra O (𝔏)] {HO : Type} [CommRing HO] [HopfAlgebra O HO]
  [Module.Finite O HO] [Module.Free O HO] [Coalgebra.IsCocomm O HO]

theorem evalAt_map_point {Γ : Type} [CommGroup Γ]
    (p : CartierDual O HO →ₐc[O] MonoidAlgebra O (Γ))
    (g : MonoidAlgebra O (Γ) →ₐ[O] 𝔏)
    (z : 𝔏 ⊗[O] CartierDual O HO) :
    evalAt g (Algebra.TensorProduct.map (AlgHom.id O (𝔏))
        (p : CartierDual O HO →ₐ[O] MonoidAlgebra O (Γ)) z)
      = evalAt (g.comp (p : CartierDual O HO →ₐ[O] MonoidAlgebra O (Γ))) z := by
  induction z using TensorProduct.induction_on with
  | zero =>
    exact ((congrArg (evalAt g) (map_zero (Algebra.TensorProduct.map (AlgHom.id O (𝔏))
          (p : CartierDual O HO →ₐ[O] MonoidAlgebra O (Γ))))).trans
        (map_zero (evalAt g))).trans (map_zero (evalAt (g.comp
          (p : CartierDual O HO →ₐ[O] MonoidAlgebra O (Γ))))).symm
  | tmul a φ => rfl
  | add x y hx hy =>
    have hM := map_add (Algebra.TensorProduct.map (AlgHom.id O (𝔏))
      (p : CartierDual O HO →ₐ[O] MonoidAlgebra O (Γ))) x y
    have hL := map_add (evalAt g)
      (Algebra.TensorProduct.map (AlgHom.id O (𝔏))
        (p : CartierDual O HO →ₐ[O] MonoidAlgebra O (Γ)) x)
      (Algebra.TensorProduct.map (AlgHom.id O (𝔏))
        (p : CartierDual O HO →ₐ[O] MonoidAlgebra O (Γ)) y)
    have hR := map_add (evalAt (g.comp
      (p : CartierDual O HO →ₐ[O] MonoidAlgebra O (Γ)))) x y
    exact (congrArg (evalAt g) hM).trans (hL.trans ((congrArg₂ (· + ·) hx hy).trans hR.symm))

theorem pair_eq_evalAt_of_bidual {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι O HO)
    (bd : HO ≃ₐc[O] CartierDual O (CartierDual O HO))
    (hbd : ∀ (a : HO) (φ : CartierDual O HO), bd a φ = φ a)
    (glD : GLData O (CartierDual O HO) (𝔏))
    (f : CartierDual O HO →ₐ[O] 𝔏) (ψ : HO →ₐ[O] 𝔏) :
    pair b f ψ
      = evalAt f
          (glD.e (ψ.comp (bd.symm.toBialgHom : CartierDual O (CartierDual O HO) →ₐ[O] HO))).val := by
  generalize hΨ' : ψ.comp (bd.symm.toBialgHom : CartierDual O (CartierDual O HO) →ₐ[O] HO) = Ψ'
  refine Eq.trans ?_
    (pair_eq_evalAt (b.dualBasis.map (CartierDual.ofDual O HO)) (glD.e Ψ').val Ψ' (fun Λ => glD.pairing Ψ' Λ) f)
  unfold DualPairing.pair
  refine Finset.sum_congr rfl fun k _ => ?_
  have hbD : (b.dualBasis.map (CartierDual.ofDual O HO)) k = db b k := by
    rw [Module.Basis.map_apply, Module.Basis.coe_dualBasis]
    rfl
  have hdbD : db (b.dualBasis.map (CartierDual.ofDual O HO)) k = bd (b k) := by
    apply CartierDual.ext
    intro φ
    rw [db_apply, hbd]
    show b.dualBasis.repr ((CartierDual.ofDual O HO).symm φ) k = φ (b k)
    rw [Module.Basis.dualBasis_repr]
    rfl
  have hΨ : Ψ' (bd (b k)) = ψ (b k) := by
    rw [← hΨ']
    exact congrArg ψ (bd.symm_apply_apply (b k))
  rw [hdbD, hbD, hΨ, mul_comm]

end GlueLemmas
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar.Car P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar"

end Ws25.S3
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar.Car P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25 P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3"
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar.Car P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25"

namespace Ws25
namespace S3
namespace Intrinsic

open Ws25.S3 Ws25.S3.DualPairing Ws25.S3.DualFlag

variable {O : Type} [CommRing O] [Algebra O (𝔏)]
variable {B : Type} [CommRing B] [HopfAlgebra O B]

local notation "P" => WithConv (B →ₐ[O] 𝔏)

def post (τ : 𝔏 →ₐ[O] 𝔏) (f : P) : P := WithConv.toConv (τ.comp (WithConv.ofConv f))

theorem post_apply (τ : 𝔏 →ₐ[O] 𝔏) (f : P) (b : B) : post τ f b = τ (f b) := rfl

theorem post_mul (τ : 𝔏 →ₐ[O] 𝔏) (f g : P) : post τ (f * g) = post τ f * post τ g := by
  apply WithConv.ext; apply AlgHom.ext; intro b
  show τ ((f * g) b) = (post τ f * post τ g) b
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply]
  show τ (Algebra.TensorProduct.lift (WithConv.ofConv f) (WithConv.ofConv g) (fun _ _ => Commute.all _ _) (Coalgebra.comul b)) =
    Algebra.TensorProduct.lift (τ.comp (WithConv.ofConv f)) (τ.comp (WithConv.ofConv g)) (fun _ _ => Commute.all _ _) (Coalgebra.comul b)
  induction (Coalgebra.comul (R := O) b) using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, map_mul]; rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem post_one (τ : 𝔏 →ₐ[O] 𝔏) : post τ (1 : P) = 1 := by
  apply WithConv.ext; apply AlgHom.ext; intro b
  show τ ((1 : P) b) = (1 : P) b
  rw [AlgHom.convOne_apply, AlgHom.commutes]

theorem post_id (f : P) : post (AlgHom.id O (𝔏)) f = f := by
  apply WithConv.ext; apply AlgHom.ext; intro b; rfl

theorem post_comp (τ τ' : 𝔏 →ₐ[O] 𝔏) (f : P) : post (τ.comp τ') f = post τ (post τ' f) := by
  apply WithConv.ext; apply AlgHom.ext; intro b; rfl

end Ws25.S3.Intrinsic
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar.Car P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25 P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3"
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar.Car P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25 P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3"
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar.Car P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25 P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3"

namespace Ws25
namespace KummerO
namespace PointsDict

open WithConv

section Provider
variable (A : ValuationSubring (𝔏)) (O : Type) [CommRing O] [Algebra O ↥A]

@[reducible] noncomputable def algebraQbar : Algebra O (𝔏) :=
  ((algebraMap ↥A (𝔏)).comp (algebraMap O ↥A)).toAlgebra

theorem isScalarTower_qbar : letI := algebraQbar A O; IsScalarTower O ↥A (𝔏) :=
  letI := algebraQbar A O
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

end Provider
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar.Car P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25 P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3"

section Points

variable {A : ValuationSubring (𝔏)} {O : Type} [CommRing O] [Algebra O ↥A]
  [Algebra O (𝔏)] [IsScalarTower O ↥A (𝔏)]
variable (B : Type) [CommRing B] [Bialgebra O B]

omit [Bialgebra O B] in
theorem algebraMap_mem (x : O) : algebraMap O (𝔏) x ∈ A := by
  rw [IsScalarTower.algebraMap_apply O ↥A (𝔏)]
  exact (algebraMap O ↥A x).2

noncomputable abbrev jA : ↥A →ₐ[O] 𝔏 := IsScalarTower.toAlgHom O ↥A (𝔏)

omit [Bialgebra O B] in
theorem jA_apply (a : ↥A) : jA (A := A) (O := O) a = (a : 𝔏) := rfl

theorem apply_mem_of_moduleFinite {B : Type} [CommRing B] [Algebra O B] [Module.Finite O B]
    (f : B →ₐ[O] 𝔏) (h : B) : f h ∈ A := by
  classical
  have hOA : ∀ x : O, algebraMap O (𝔏) x ∈ A := algebraMap_mem (A := A) (O := O)
  have hint : IsIntegral O (f h) := (Algebra.IsIntegral.isIntegral (R := O) h).map f
  obtain ⟨p, hpm, hpev⟩ := hint
  rw [← A.valuation_le_one_iff]
  by_contra hgt
  rw [not_le] at hgt
  have hy0 : A.valuation (f h) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hgt)
  have hsum : ∑ i ∈ Finset.range (p.natDegree + 1),
      algebraMap O (𝔏) (p.coeff i) * f h ^ i = 0 := by
    rw [← Polynomial.eval₂_eq_sum_range]
    exact hpev
  rw [Finset.sum_range_succ, hpm.coeff_natDegree, map_one, one_mul] at hsum
  have hyd : f h ^ p.natDegree
      = -∑ i ∈ Finset.range p.natDegree,
          algebraMap O (𝔏) (p.coeff i) * f h ^ i :=
    eq_neg_of_add_eq_zero_right hsum
  have hlt : A.valuation (∑ i ∈ Finset.range p.natDegree,
      algebraMap O (𝔏) (p.coeff i) * f h ^ i)
        < A.valuation (f h) ^ p.natDegree := by
    apply Valuation.map_sum_lt _ (pow_ne_zero _ hy0)
    intro i hi
    have hi' : i < p.natDegree := Finset.mem_range.mp hi
    rw [Valuation.map_mul, Valuation.map_pow]
    calc A.valuation (algebraMap O (𝔏) (p.coeff i)) * A.valuation (f h) ^ i
        ≤ 1 * A.valuation (f h) ^ i := by
          apply mul_le_mul_left
          exact (A.valuation_le_one_iff _).mpr (hOA (p.coeff i))
      _ = A.valuation (f h) ^ i := one_mul _
      _ < A.valuation (f h) ^ p.natDegree := pow_lt_pow_right₀ hgt hi'
  have hcontra : A.valuation (f h ^ p.natDegree) < A.valuation (f h) ^ p.natDegree := by
    rw [hyd, Valuation.map_neg]
    exact hlt
  rw [Valuation.map_pow] at hcontra
  exact lt_irrefl _ hcontra

noncomputable def toQ (f : WithConv (B →ₐ[O] ↥A)) : WithConv (B →ₐ[O] 𝔏) :=
  toConv ((jA (A := A) (O := O)).comp (ofConv f))

theorem toQ_apply (f : WithConv (B →ₐ[O] ↥A)) (b : B) :
    ofConv (toQ B f) b = ((ofConv f b : ↥A) : 𝔏) := rfl

theorem toQ_injective : Function.Injective (toQ (A := A) (O := O) B) := by
  intro f g hfg
  apply WithConv.ext
  apply AlgHom.ext
  intro b
  apply Subtype.ext
  have := congrArg (fun φ : WithConv (B →ₐ[O] 𝔏) => ofConv φ b) hfg
  exact this

theorem toQ_mul (f g : WithConv (B →ₐ[O] ↥A)) : toQ B (f * g) = toQ B f * toQ B g := by
  apply WithConv.ext
  show (jA (A := A) (O := O)).comp (ofConv (f * g)) = _
  rw [AlgHom.comp_convMul_distrib]
  rfl

theorem toQ_one : toQ (A := A) (O := O) B 1 = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro b
  rw [toQ_apply]
  show (((1 : WithConv (B →ₐ[O] ↥A)) b : ↥A) : 𝔏) = (1 : WithConv (B →ₐ[O] 𝔏)) b
  rw [AlgHom.convOne_apply, AlgHom.convOne_apply, IsScalarTower.algebraMap_apply O ↥A (𝔏)]
  rfl

theorem toQ_pow (f : WithConv (B →ₐ[O] ↥A)) (n : ℕ) : toQ B (f ^ n) = toQ B f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, toQ_one]
  | succ n ih => rw [pow_succ, pow_succ, toQ_mul, ih]

noncomputable def ofQ [Module.Finite O B] (φ : WithConv (B →ₐ[O] 𝔏)) : WithConv (B →ₐ[O] ↥A) :=
  toConv
    { toFun := fun b => ⟨ofConv φ b, apply_mem_of_moduleFinite (ofConv φ) b⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y)
      commutes' := fun r => Subtype.ext (by
        show ofConv φ (algebraMap O B r) = ((algebraMap O ↥A r : ↥A) : 𝔏)
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply O ↥A (𝔏)]
        rfl) }

theorem ofQ_apply [Module.Finite O B] (φ : WithConv (B →ₐ[O] 𝔏)) (b : B) :
    ((ofConv (ofQ (A := A) B φ) b : ↥A) : 𝔏) = ofConv φ b := rfl

theorem toQ_ofQ [Module.Finite O B] (φ : WithConv (B →ₐ[O] 𝔏)) : toQ B (ofQ (A := A) B φ) = φ := by
  apply WithConv.ext; apply AlgHom.ext; intro b; rfl

theorem ofQ_toQ [Module.Finite O B] (f : WithConv (B →ₐ[O] ↥A)) : ofQ (A := A) B (toQ B f) = f := by
  apply WithConv.ext; apply AlgHom.ext; intro b; apply Subtype.ext; rfl

noncomputable def pointsEquiv [Module.Finite O B] : WithConv (B →ₐ[O] ↥A) ≃ WithConv (B →ₐ[O] 𝔏) :=
  { toFun := toQ B
    invFun := ofQ (A := A) B
    left_inv := ofQ_toQ B
    right_inv := toQ_ofQ B }

theorem pointsEquiv_apply [Module.Finite O B] (f : WithConv (B →ₐ[O] ↥A)) : pointsEquiv (A := A) B f = toQ B f := rfl

theorem apply_eq_one_iff (f : WithConv (B →ₐ[O] ↥A)) (e : B) : ofConv f e = 1 ↔ ofConv (toQ B f) e = 1 := by
  rw [toQ_apply]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact Subtype.ext h

theorem natCard_block_eq [Module.Finite O B] (e : B) :
    Nat.card {ψ : WithConv (B →ₐ[O] ↥A) // ofConv ψ e = 1} = Nat.card {φ : WithConv (B →ₐ[O] 𝔏) // ofConv φ e = 1} :=
  Nat.card_congr ((pointsEquiv (A := A) B).subtypeEquiv (fun f => apply_eq_one_iff B f e))

theorem forall_apply_eq_iff (σ : 𝔏 ≃ₐ[𝔎] 𝔏) (f g : WithConv (B →ₐ[O] ↥A)) :
    (∀ b : B, ((ofConv g b : ↥A) : 𝔏) = σ ((ofConv f b : ↥A) : 𝔏)) ↔
      ∀ b : B, ofConv (toQ B g) b = σ (ofConv (toQ B f) b) := Iff.rfl

end Points
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar.Car P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25 P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3"

end Ws25.KummerO.PointsDict
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar.Car P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25 P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3"
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar.Car P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25 P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3"
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar.Car P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25 P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3"

open Ws25.KummerO.PointsDict Ws25.S3 Ws25.S3.DualPairing Ws25.S3.DualFlag Ws25.S3.Intrinsic in
set_option maxHeartbeats 6400000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    {𝔎 : Type} [Field 𝔎] {𝔏 : Type} [Field 𝔏] [Algebra 𝔎 𝔏] [IsAlgClosed 𝔏] [CharZero 𝔏]
    (A : ValuationSubring 𝔏) (hA : A.LiesOverPrime q)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hirr : Irreducible (q : O))
    [Algebra O ↥A] (ι : O →+* ↥A) (hι : Function.Injective ι) (hιalg : ∀ x : O, algebraMap O ↥A x = ι x)
    (hιfix : ∀ σ : (𝔏 ≃ₐ[𝔎] 𝔏), σ ∈ A.inertiaSubgroupIn 𝔎 ↔ ∀ x : O, σ ((ι x : ↥A) : 𝔏) = ((ι x : ↥A) : 𝔏))
    (hιmax : ∀ a : ↥A, (∀ σ ∈ A.inertiaSubgroupIn 𝔎, σ (a : 𝔏) = (a : 𝔏)) → a ∈ Set.range ι)
    (B : Type) [CommRing B] [HopfAlgebra O B] [Module.Finite O B] [Module.Free O B] [Coalgebra.IsCocomm O B]
    (hBq : ∀ (T : Type) [CommRing T] [Algebra O T] (f : WithConv (B →ₐ[O] T)), f ^ q = 1)
    (n : (𝔏 ≃ₐ[𝔎] 𝔏) → ℕ)
    (hn : ∀ σ (ζ : 𝔏), ζ ^ q = 1 → σ ζ = ζ ^ n σ)
    (D : Submonoid (WithConv (B →ₐ[O] ↥A)))
    (hDcyc : ∀ σ ∈ A.inertiaSubgroupIn 𝔎, ∀ f ∈ D, ∀ g : WithConv (B →ₐ[O] ↥A),
      (∀ b : B, ((WithConv.ofConv g b : ↥A) : 𝔏) = σ ((WithConv.ofConv f b : ↥A) : 𝔏)) → g = f ^ n σ)
    (hquot : ∀ σ ∈ A.inertiaSubgroupIn 𝔎, ∀ f g : WithConv (B →ₐ[O] ↥A),
      (∀ b : B, ((WithConv.ofConv g b : ↥A) : 𝔏) = σ ((WithConv.ofConv f b : ↥A) : 𝔏)) → ∃ d ∈ D, g = f * d)
    (Λ : Type) [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ] (hΛ : Nat.card Λ = Nat.card ↥D) :
    ∃ (N : ℕ) (ε : Fin (N + 1) → B),
      (∀ i, IsIdempotentElem (ε i)) ∧
      (∀ i j, i ≠ j → ε i * ε j = 0) ∧
      (∑ i, ε i) = 1 ∧
      Coalgebra.counit (R := O) (ε 0) = 1 ∧
      (∀ i, i ≠ 0 → Coalgebra.counit (R := O) (ε i) = 0) ∧
      (∀ ψ : WithConv (B →ₐ[O] ↥A), ∃! i : Fin (N + 1), ψ (ε i) = 1) ∧
      (∀ ψ : WithConv (B →ₐ[O] ↥A), ψ ∈ D ↔ ψ (ε 0) = 1) ∧
      (∀ i : Fin (N + 1), ∃ ψ : WithConv (B →ₐ[O] ↥A), ψ (ε i) = 1) ∧
      (∀ (i : Fin (N + 1)) (ψ φ : WithConv (B →ₐ[O] ↥A)), ψ (ε i) = 1 → (φ (ε i) = 1 ↔ ∃ d ∈ D, φ = ψ * d)) ∧
      (∀ i : Fin (N + 1), Nat.card {ψ : WithConv (B →ₐ[O] ↥A) // ψ (ε i) = 1} = Fintype.card Λ) ∧
      (N + 1) * Nat.card ↥D = Nat.card (WithConv (B →ₐ[O] ↥A)) := by
  classical
  have hqp : q.Prime := Fact.out
  have hq0 : q ≠ 0 := hqp.ne_zero
  have hQpos : 0 < q := hqp.pos

  letI : Algebra O (𝔏) := algebraQbar A O
  haveI : IsScalarTower O ↥A (𝔏) := isScalarTower_qbar A O
  haveI : FaithfulSMul O (𝔏) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro x y hxy
    apply hι
    rw [← hιalg, ← hιalg]
    apply Subtype.ext
    rw [IsScalarTower.algebraMap_apply O ↥A (𝔏), IsScalarTower.algebraMap_apply O ↥A (𝔏)] at hxy
    exact hxy
  have halg : ∀ x : O, algebraMap O (𝔏) x = ((ι x : ↥A) : 𝔏) := by
    intro x
    rw [IsScalarTower.algebraMap_apply O ↥A (𝔏), hιalg]
    rfl
  have hOA : ∀ x : O, algebraMap O (𝔏) x ∈ A := fun x => algebraMap_mem (A := A) (O := O) x
  have hOfix : ∀ σ : (𝔏 ≃ₐ[𝔎] 𝔏), σ ∈ A.inertiaSubgroupIn 𝔎 ↔ ∀ x : O, σ (algebraMap O (𝔏) x) = algebraMap O (𝔏) x := by
    intro σ
    rw [hιfix σ]
    simp only [halg]
  have hOmax : ∀ y ∈ A, (∀ σ ∈ A.inertiaSubgroupIn 𝔎, σ y = y) → ∃ x : O, algebraMap O (𝔏) x = y := by
    intro y hy hfix
    obtain ⟨x, hx⟩ := hιmax ⟨y, hy⟩ (fun σ hσ => hfix σ hσ)
    exact ⟨x, by rw [halg, hx]⟩
  haveI : Nontrivial O := inferInstance

  have hptq : ∀ φ : WithConv (B →ₐ[O] 𝔏), φ ^ q = 1 := by
    intro φ
    rw [← toQ_ofQ (A := A) B φ, ← toQ_pow, hBq, toQ_one]
  have hunit : ∀ f : WithConv (B →ₐ[O] 𝔏), IsUnit f := fun f => IsUnit.of_pow_eq_one (hptq f) hq0
  letI instG : CommGroup (WithConv (B →ₐ[O] 𝔏)) := { groupOfIsUnit hunit with mul_comm := mul_comm }
  have hcardF : Nat.card (B →ₐ[O] 𝔏) = Module.finrank O B :=
    HopfAlgebra.natCard_algHom_eq_finrank_of_charZero O B (𝔏)
  haveI : Nontrivial B := ⟨⟨0, 1, fun h => zero_ne_one
    ((map_zero (Coalgebra.counit (R := O) (A := B))).symm.trans ((congrArg (Coalgebra.counit (R := O) (A := B)) h).trans Bialgebra.counit_one))⟩⟩
  haveI : Finite (B →ₐ[O] 𝔏) :=
    Nat.finite_of_card_ne_zero (by rw [hcardF]; exact ((Module.finrank_pos_iff_of_free (R := O) B).mpr inferInstance).ne')
  haveI : Finite (WithConv (B →ₐ[O] 𝔏)) := Finite.of_equiv _ (WithConv.equiv (B →ₐ[O] 𝔏)).symm
  haveI : Finite (WithConv (B →ₐ[O] ↥A)) := Finite.of_equiv _ (pointsEquiv (A := A) B).symm
  haveI : Finite ↥D := Subtype.finite

  let toQh : WithConv (B →ₐ[O] ↥A) →* WithConv (B →ₐ[O] 𝔏) :=
    { toFun := toQ (A := A) (O := O) B, map_one' := toQ_one B, map_mul' := toQ_mul B }
  have htoQh : ∀ f, toQh f = toQ (A := A) (O := O) B f := fun _ => rfl
  let D' : Submonoid (WithConv (B →ₐ[O] 𝔏)) := D.map toQh
  have hmemD' : ∀ f : WithConv (B →ₐ[O] ↥A), toQ (A := A) (O := O) B f ∈ D' ↔ f ∈ D := by
    intro f
    constructor
    · rintro ⟨g, hg, hgf⟩
      rw [htoQh] at hgf
      rwa [← toQ_injective B hgf]
    · intro hf
      exact ⟨f, hf, rfl⟩
  have hcardD' : Nat.card ↥D' = Nat.card ↥D := by
    refine (Nat.card_congr (Equiv.ofBijective (fun d : ↥D => (⟨toQh d.1, d.1, d.2, rfl⟩ : ↥D')) ⟨?_, ?_⟩)).symm
    · intro d₁ d₂ h
      exact Subtype.ext (toQ_injective (A := A) (O := O) B (congrArg Subtype.val h))
    · rintro ⟨_, f, hf, rfl⟩
      exact ⟨⟨f, hf⟩, rfl⟩
  have hD'inv : ∀ x ∈ D', x⁻¹ ∈ D' := by
    intro x hx
    have hx1 : x⁻¹ = x ^ (q - 1) := by
      apply mul_left_cancel (a := x)
      rw [mul_inv_cancel, ← pow_succ', Nat.sub_add_cancel hqp.one_le, hptq]
    rw [hx1]; exact pow_mem hx _

  let τ : ↥(A.inertiaSubgroupIn 𝔎) → (𝔏 →ₐ[O] 𝔏) := fun σ =>
    { ((σ : (𝔏 ≃ₐ[𝔎] 𝔏)) : 𝔏 →+* 𝔏) with commutes' := fun o => (hOfix σ).mp σ.2 o }
  have hτ : ∀ (σ : ↥(A.inertiaSubgroupIn 𝔎)) (z : 𝔏), τ σ z = (σ : (𝔏 ≃ₐ[𝔎] 𝔏)) z := fun _ _ => rfl
  have hτ1 : τ 1 = AlgHom.id O (𝔏) := AlgHom.ext fun z => rfl
  have hτmul : ∀ σ σ', τ (σ * σ') = (τ σ).comp (τ σ') := fun _ _ => AlgHom.ext fun z => rfl
  letI instAct : DistribMulAction ↥(A.inertiaSubgroupIn 𝔎) (Additive (WithConv (B →ₐ[O] 𝔏))) :=
    { smul := fun σ x => Additive.ofMul (post (τ σ) (Additive.toMul x))
      one_smul := fun x => by
        show Additive.ofMul (post (τ 1) (Additive.toMul x)) = x
        rw [hτ1, post_id]; rfl
      mul_smul := fun σ σ' x => by
        show Additive.ofMul (post (τ (σ * σ')) (Additive.toMul x)) = Additive.ofMul (post (τ σ) (Additive.toMul (Additive.ofMul (post (τ σ') (Additive.toMul x)))))
        rw [hτmul, post_comp]; rfl
      smul_zero := fun σ => by
        show Additive.ofMul (post (τ σ) (Additive.toMul 0)) = 0
        rw [toMul_zero, post_one]; rfl
      smul_add := fun σ x y => by
        show Additive.ofMul (post (τ σ) (Additive.toMul (x + y))) = Additive.ofMul (post (τ σ) (Additive.toMul x)) + Additive.ofMul (post (τ σ) (Additive.toMul y))
        rw [toMul_add, post_mul]; rfl }
  have smul_def : ∀ (σ : ↥(A.inertiaSubgroupIn 𝔎)) (x : Additive (WithConv (B →ₐ[O] 𝔏))),
      σ • x = Additive.ofMul (post (τ σ) (Additive.toMul x)) := fun _ _ => rfl
  let M : AddSubgroup (Additive (WithConv (B →ₐ[O] 𝔏))) := ⊤
  let pts : WithConv (B →ₐ[O] 𝔏) ≃ ↥M :=
    { toFun := fun f => ⟨Additive.ofMul f, trivial⟩
      invFun := fun x => Additive.toMul x.1
      left_inv := fun f => rfl
      right_inv := fun x => Subtype.ext rfl }
  have hpts : ∀ f, ((pts f : ↥M) : Additive (WithConv (B →ₐ[O] 𝔏))) = Additive.ofMul f := fun _ => rfl
  have hpts_symm : ∀ x : ↥M, pts.symm x = Additive.toMul x.1 := fun _ => rfl
  have hadd : ∀ f g, pts (f * g) = pts f + pts g := fun _ _ => rfl
  have hact : ∀ (σ : ↥(A.inertiaSubgroupIn 𝔎)) (f g : WithConv (B →ₐ[O] 𝔏)),
      (∀ x : B, g x = (σ : (𝔏 ≃ₐ[𝔎] 𝔏)) (f x)) →
        ((pts g : ↥M) : Additive (WithConv (B →ₐ[O] 𝔏))) = σ • ((pts f : ↥M) : Additive (WithConv (B →ₐ[O] 𝔏))) := by
    intro σ f g hfg
    rw [hpts, hpts, smul_def]
    congr 1
    apply WithConv.ext; apply AlgHom.ext; intro x
    exact hfg x
  have hMstab : ∀ (σ : ↥(A.inertiaSubgroupIn 𝔎)) (x : Additive (WithConv (B →ₐ[O] 𝔏))), x ∈ M → σ • x ∈ M :=
    fun _ _ _ => trivial
  haveI : Finite ↥M := Finite.of_equiv _ pts
  have hMq : ∀ x : ↥M, q • x = 0 := by
    intro x
    apply Subtype.ext
    show q • (x.1 : Additive (WithConv (B →ₐ[O] 𝔏))) = 0
    rw [← ofMul_toMul x.1, ← ofMul_pow, hptq]
    rfl
  let S : AddSubgroup (Additive (WithConv (B →ₐ[O] 𝔏))) :=
    { carrier := {x | Additive.toMul x ∈ D'}
      zero_mem' := D'.one_mem
      add_mem' := fun {x y} hx hy => D'.mul_mem hx hy
      neg_mem' := fun {x} hx => hD'inv _ hx }
  have hmemS : ∀ x, x ∈ S ↔ Additive.toMul x ∈ D' := fun _ => Iff.rfl
  have hSM : S ≤ M := fun _ _ => trivial
  have hdisp : ∀ (σ : ↥(A.inertiaSubgroupIn 𝔎)) (m : ↥M),
      σ • (m : Additive (WithConv (B →ₐ[O] 𝔏))) - m ∈ S := by
    intro σ m
    rw [hmemS, smul_def, toMul_sub, toMul_ofMul]
    set f : WithConv (B →ₐ[O] 𝔏) := Additive.toMul (m : Additive (WithConv (B →ₐ[O] 𝔏))) with hf
    let f₀ := ofQ (A := A) B f
    let g₀ := ofQ (A := A) B (post (τ σ) f)
    have hrel : ∀ b : B, ((WithConv.ofConv g₀ b : ↥A) : 𝔏) = (σ : (𝔏 ≃ₐ[𝔎] 𝔏)) ((WithConv.ofConv f₀ b : ↥A) : 𝔏) := by
      rw [forall_apply_eq_iff B (σ : (𝔏 ≃ₐ[𝔎] 𝔏)) f₀ g₀, toQ_ofQ, toQ_ofQ]
      intro b; rfl
    obtain ⟨d, hd, hgd⟩ := hquot σ σ.2 f₀ g₀ hrel
    have h1 : post (τ σ) f = f * toQ (A := A) (O := O) B d := by
      rw [← toQ_ofQ (A := A) B (post (τ σ) f), ← toQ_ofQ (A := A) B f]
      show toQ B g₀ = toQ B f₀ * toQ B d
      rw [← toQ_mul, ← hgd]
    rw [h1, mul_div_cancel_left]
    exact ⟨d, hd, rfl⟩

  obtain ⟨gl⟩ := (nonempty_glData : Nonempty (GLData O B (𝔏)))
  obtain ⟨glD⟩ := (nonempty_glData : Nonempty (GLData O (CartierDual O B) (𝔏)))
  obtain ⟨bd, hbd⟩ := CartierDual.exists_bialgEquiv_bidual O B
  let bas := Module.Free.chooseBasis O B

  obtain ⟨a, ha, p, hp, hdict⟩ :=
    exists_surjective_dualFlag q hq2 A O hOA inferInstance hirr hOfix hOmax B M pts hadd hact hMstab hMq S hSM hdisp n hn gl bas

  have hcardS : Nat.card ↥S = Nat.card ↥D := by
    rw [← hcardD']
    exact Nat.card_congr
      { toFun := fun x => ⟨Additive.toMul x.1, x.2⟩
        invFun := fun y => ⟨Additive.ofMul y.1, y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hcardM : Nat.card ↥M = Nat.card (WithConv (B →ₐ[O] 𝔏)) := (Nat.card_congr pts).symm
  obtain ⟨N, hN⟩ : ∃ N : ℕ, q ^ a = N + 1 := Nat.exists_eq_succ_of_ne_zero (pow_ne_zero a hq0)
  have hΓ : Nat.card (Multiplicative (Fin a → ZMod q)) = N + 1 := by
    rw [← hN, Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hcardP : Nat.card (WithConv (B →ₐ[O] 𝔏)) = (N + 1) * Nat.card ↥D := by
    rw [← hN, ← hcardS, ← hcardM, ha]
  obtain ⟨ε, h1, h2, h3, h4, h5, h6, h8, h9, hblock₀⟩ :=
    BlockIdempotents.exists_epsFamily_generic (N + 1) (Nat.card ↥D) O B (MonoidAlgebra O (Multiplicative (Fin a → ZMod q))) p hp
      (Multiplicative (Fin a → ZMod q)) hΓ (BialgEquiv.refl O _) bd glD hcardP

  have hsep : ∀ x y : 𝔏 ⊗[O] MonoidAlgebra O (Multiplicative (Fin a → ZMod q)),
      (∀ g : MonoidAlgebra O (Multiplicative (Fin a → ZMod q)) →ₐ[O] 𝔏, evalAt g x = evalAt g y) → x = y := by
    have hcardG : Nat.card (MonoidAlgebra O (Multiplicative (Fin a → ZMod q)) →ₐ[O] 𝔏)
        = Module.finrank O (MonoidAlgebra O (Multiplicative (Fin a → ZMod q))) :=
      HopfAlgebra.natCard_algHom_eq_finrank_of_charZero O _ (𝔏)
    haveI : Finite (MonoidAlgebra O (Multiplicative (Fin a → ZMod q)) →ₐ[O] 𝔏) := by
      apply Nat.finite_of_card_ne_zero
      rw [hcardG, Module.finrank_eq_card_basis (BlockIdempotents.bG (Multiplicative (Fin a → ZMod q)) O)]
      exact Fintype.card_ne_zero
    letI := Fintype.ofFinite (MonoidAlgebra O (Multiplicative (Fin a → ZMod q)) →ₐ[O] 𝔏)
    intro x y hxy
    exact eval_injective (fun g => g) (fun _ _ h => h) (by rw [← Nat.card_eq_fintype_card, hcardG]) x y hxy
  have hfwd : ∀ ψ : WithConv (B →ₐ[O] 𝔏), ψ ∈ D' → ψ (ε 0) = 1 := by
    intro ψ hψ
    rw [hblock₀ ψ]
    refine hsep _ _ fun g => ?_
    refine ((evalAt_map_point p g _).trans ?_).trans (map_one (evalAt g)).symm
    refine (pair_eq_evalAt_of_bidual bas bd hbd glD _ ψ.ofConv).symm.trans ?_
    have hS' : ((pts ψ : ↥M) : Additive (WithConv (B →ₐ[O] 𝔏))) ∈ S := by
      rw [hmemS, hpts, toMul_ofMul]; exact hψ
    have h := (hdict (g.comp (p : CartierDual O B →ₐ[O] MonoidAlgebra O (Multiplicative (Fin a → ZMod q))))).mp ⟨g, rfl⟩ (pts ψ) hS'
    rwa [Equiv.symm_apply_apply] at h
  have hblk : ∀ ψ : WithConv (B →ₐ[O] 𝔏), ψ ∈ D' ↔ ψ (ε 0) = 1 := by
    have hSet : {ψ : WithConv (B →ₐ[O] 𝔏) | ψ ∈ D'} = {ψ | ψ (ε 0) = 1} := by
      refine Set.eq_of_subset_of_ncard_le (fun ψ hψ => hfwd ψ hψ) ?_
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      have hc₂ : Nat.card ↥{ψ : WithConv (B →ₐ[O] 𝔏) | ψ (ε 0) = 1} = Nat.card ↥D := h8 0
      have hc₁ : Nat.card ↥{ψ : WithConv (B →ₐ[O] 𝔏) | ψ ∈ D'} = Nat.card ↥D := hcardD'
      exact (hc₂.trans hc₁.symm).le
    intro ψ
    constructor
    · exact hfwd ψ
    · intro h
      have : ψ ∈ {ψ : WithConv (B →ₐ[O] 𝔏) | ψ ∈ D'} := by rw [hSet]; exact h
      exact this

  have hone : ∀ (f : WithConv (B →ₐ[O] ↥A)) (x : B), f x = 1 ↔ (toQ (A := A) (O := O) B f) x = 1 :=
    fun f x => apply_eq_one_iff B f x
  refine ⟨N, ε, h1, h2, h3, h4, h5, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro ψ
    obtain ⟨i, hi, huniq⟩ := h6 (toQ (A := A) (O := O) B ψ)
    exact ⟨i, (hone ψ _).mpr hi, fun j hj => huniq j ((hone ψ _).mp hj)⟩
  ·
    intro ψ
    rw [hone, ← hblk, hmemD']
  ·
    intro i
    have hpos : 0 < Nat.card {ψ : WithConv (B →ₐ[O] 𝔏) // ψ (ε i) = 1} := by
      rw [h8 i]; exact Nat.card_pos
    obtain ⟨⟨φ, hφ⟩⟩ := (Nat.card_pos_iff.mp hpos).1
    exact ⟨ofQ (A := A) B φ, (hone _ _).mpr (by rw [toQ_ofQ]; exact hφ)⟩
  ·
    intro i ψ φ hψ
    have hψ' := (hone ψ _).mp hψ
    constructor
    · intro hφ
      have hφ' := (hone φ _).mp hφ

      set χ : WithConv (B →ₐ[O] 𝔏) := (toQ (A := A) (O := O) B ψ)⁻¹ * toQ (A := A) (O := O) B φ with hχ
      have hχ0 : χ (ε 0) = 1 := by

        obtain ⟨j, hj, -⟩ := h6 χ
        by_contra hne
        have hj0 : j ≠ 0 := fun h0 => hne (h0 ▸ hj)

        exact absurd hj (by

          have hsub : ∀ χ' : WithConv (B →ₐ[O] 𝔏), χ' (ε 0) = 1 → (toQ (A := A) (O := O) B ψ * χ') (ε i) = 1 :=
            fun χ' hχ' => h9 i _ χ' hψ' hχ'
          have hinj : Function.Injective (fun χ' : {χ' : WithConv (B →ₐ[O] 𝔏) // χ' (ε 0) = 1} =>
              (⟨toQ (A := A) (O := O) B ψ * χ'.1, hsub χ'.1 χ'.2⟩ : {φ' : WithConv (B →ₐ[O] 𝔏) // φ' (ε i) = 1})) :=
            fun x y h => Subtype.ext (mul_left_cancel (congrArg Subtype.val h))
          have hbij := (Function.Injective.bijective_of_nat_card_le hinj (by rw [h8 i, h8 0]))
          obtain ⟨⟨χ', hχ'⟩, hχ'φ⟩ := hbij.2 ⟨toQ (A := A) (O := O) B φ, hφ'⟩
          have : χ = χ' := by
            rw [hχ]
            have := congrArg Subtype.val hχ'φ
            simp only at this
            rw [← this, inv_mul_cancel_left]
          intro hjχ
          rw [this] at hne
          exact hne hχ')
      have hχD : χ ∈ D' := (hblk χ).mpr hχ0
      obtain ⟨d, hd, hdχ⟩ := hχD
      refine ⟨d, hd, ?_⟩
      apply toQ_injective (A := A) (O := O) B
      rw [toQ_mul, ← htoQh d, hdχ, hχ, mul_inv_cancel_left]
    · rintro ⟨d, hd, rfl⟩
      rw [hone, toQ_mul]
      exact h9 i _ _ hψ' ((hblk _).mp ((hmemD' d).mpr hd))
  ·
    intro i
    rw [← Nat.card_eq_fintype_card, hΛ, ← h8 i]
    exact natCard_block_eq (A := A) B (ε i)
  ·
    rw [Nat.card_congr (pointsEquiv (A := A) B), hcardP]

end
p2m_reactivate "P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualPairing P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar.Car P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3.DualChar P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25 P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed.Ws25.S3"

end S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed
end P2MW
export P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed (solution)
