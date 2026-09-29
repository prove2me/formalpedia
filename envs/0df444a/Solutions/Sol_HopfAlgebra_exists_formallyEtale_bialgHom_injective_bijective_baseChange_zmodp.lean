-- Prove2me | solution 1 for HopfAlgebra.exists_formallyEtale_bialgHom_injective_bijective_baseChange_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ba6b1454-3bd9-5211-8697-6153e2208bd0

import Mathlib
import Theorems.Thm_HopfAlgebra_exists_isReduced_bialgHom_injective_comp_eq_pow_zmodp
import Theorems.Thm_HopfAlgebra_exists_formallyEtale_bialgEquiv_baseChange_zmodp
import Theorems.Thm_Bialgebra_existsUnique_bialgHom_baseChange_eq_zmodp
import Theorems.Thm_HenselianLocalRing_existsUnique_isIdempotentElem_mk_eq_of_moduleFinite
import Theorems.Thm_IsAdicComplete_of_module_finite_free_span_natCast
import Theorems.Thm_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_ker_algebraMap_zmod_eq_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_formallyEtale_bialgHom_injective_bijective_baseChange_zmodp

set_option autoImplicit false

open scoped TensorProduct

universe u v w

namespace HopfAlgebra
p2m_export "HopfAlgebra" "sum_mul_antipode_eq_algebraMap_counit mk sum_antipode_mul_eq_algebraMap_counit mul_antipode_rTensor_comul mul_antipode_lTensor_comul exists_isReduced_bialgHom_injective_comp_eq_pow_zmodp exists_formallyEtale_bialgEquiv_baseChange_zmodp"
namespace EtLiftC12
p2m_open "HopfAlgebra"

private theorem exists_ringEquiv_quotient_tensor
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (S : Type w) [CommRing S] [Algebra 𝓞 S] :
    ∃ τ : (S ⧸ (Ideal.span {(p : 𝓞)}).map (algebraMap 𝓞 S)) ≃+* ZMod p ⊗[𝓞] S,
      ∀ s : S, τ (Ideal.Quotient.mk _ s) = (1 : ZMod p) ⊗ₜ[𝓞] s := by
  have hsurj : Function.Surjective (Algebra.ofId 𝓞 (ZMod p)) := ZMod.ringHom_surjective _
  have hker' : Ideal.span {(p : 𝓞)} = RingHom.ker (Algebra.ofId 𝓞 (ZMod p)) := hker.symm
  let ι : (𝓞 ⧸ Ideal.span {(p : 𝓞)}) ≃ₐ[𝓞] ZMod p :=
    (Ideal.quotientEquivAlgOfEq 𝓞 hker').trans (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  let e₁ := Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (Ideal.span {(p : 𝓞)})
  let e₂ := Algebra.TensorProduct.comm 𝓞 S (𝓞 ⧸ Ideal.span {(p : 𝓞)})
  let e₃ : (𝓞 ⧸ Ideal.span {(p : 𝓞)}) ⊗[𝓞] S ≃ₐ[𝓞] ZMod p ⊗[𝓞] S :=
    Algebra.TensorProduct.congr ι (AlgEquiv.refl : S ≃ₐ[𝓞] S)
  refine ⟨e₁.toRingEquiv.trans (e₂.toRingEquiv.trans e₃.toRingEquiv), fun s => ?_⟩
  simp only [RingEquiv.coe_trans, Function.comp_apply, AlgEquiv.coe_ringEquiv]
  rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  simp

private theorem existsUnique_isIdempotentElem_tmul_eq
    {𝓞 : Type u} [CommRing 𝓞] [HenselianLocalRing 𝓞] (p : ℕ) [Fact p.Prime]
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (hmax : IsLocalRing.maximalIdeal 𝓞 = Ideal.span {(p : 𝓞)})
    (S : Type w) [CommRing S] [Algebra 𝓞 S] [Module.Finite 𝓞 S]
    (x : ZMod p ⊗[𝓞] S) (hx : IsIdempotentElem x) :
    ∃! e : S, IsIdempotentElem e ∧ (1 : ZMod p) ⊗ₜ[𝓞] e = x := by
  obtain ⟨τ, hτ⟩ := exists_ringEquiv_quotient_tensor p hker S
  have hmap : (IsLocalRing.maximalIdeal 𝓞).map (algebraMap 𝓞 S) =
      (Ideal.span {(p : 𝓞)}).map (algebraMap 𝓞 S) := by rw [hmax]
  let κ : (S ⧸ (IsLocalRing.maximalIdeal 𝓞).map (algebraMap 𝓞 S)) ≃+*
      (S ⧸ (Ideal.span {(p : 𝓞)}).map (algebraMap 𝓞 S)) := Ideal.quotEquivOfEq hmap
  have hκ : ∀ s : S, κ (Ideal.Quotient.mk _ s) = Ideal.Quotient.mk _ s := fun s => rfl
  have key : ∀ s : S,
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝓞).map (algebraMap 𝓞 S)) s = κ.symm (τ.symm x) ↔
        (1 : ZMod p) ⊗ₜ[𝓞] s = x := by
    intro s
    rw [RingEquiv.eq_symm_apply, RingEquiv.eq_symm_apply, hκ, hτ]
  obtain ⟨e, ⟨he, hemk⟩, huniq⟩ :=
    HenselianLocalRing.existsUnique_isIdempotentElem_mk_eq_of_moduleFinite (R := 𝓞) (S := S)
      (κ.symm (τ.symm x)) ((hx.map τ.symm).map κ.symm)
  refine ⟨e, ⟨he, (key e).1 hemk⟩, fun e' he' => huniq e' ⟨he'.1, (key e').2 he'.2⟩⟩

private theorem mainU
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (L : Type v) [CommRing L] [HopfAlgebra 𝓞 L] [Coalgebra.IsCocomm 𝓞 L]
    [Module.Free 𝓞 L] [Module.Finite 𝓞 L] :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra 𝓞 H) (_ : Coalgebra.IsCocomm 𝓞 H)
      (_ : Module.Free 𝓞 H) (_ : Module.Finite 𝓞 H) (_ : Algebra.FormallyEtale 𝓞 H) (j : H →ₐc[𝓞] L),
      Function.Injective j ∧
      IsReduced (ZMod p ⊗[𝓞] H) ∧
      Function.Bijective ((Ideal.Quotient.mkₐ (ZMod p) (nilradical (ZMod p ⊗[𝓞] L))).comp
        (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (j : H →ₐ[𝓞] L))) ∧
      ∀ e : L, IsIdempotentElem e → e ∈ Set.range j := by
  classical
  have hpp : p.Prime := Fact.out

  obtain ⟨hdom, hdvr, -, hmax⟩ :=
    IsAdicComplete.exists_isDomain_isDiscreteValuationRing_of_ker_algebraMap_zmod_eq_span p hp hker
  haveI := hdom
  haveI := hdvr
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal 𝓞) 𝓞 := by rw [hmax]; infer_instance
  haveI : HenselianLocalRing 𝓞 :=
    { toIsLocalRing := inferInstance
      is_henselian := fun f hf a₀ h₁ h₂ =>
        (IsAdicComplete.henselianRing 𝓞 (IsLocalRing.maximalIdeal 𝓞)).is_henselian f hf a₀ h₁
          (h₂.map _) }

  obtain ⟨n, Hbar, _, _, _, _, _, πb, jb, hπb, hjb, hkerπ, hcomp⟩ :=
    HopfAlgebra.exists_isReduced_bialgHom_injective_comp_eq_pow_zmodp p (ZMod p ⊗[𝓞] L)
  obtain ⟨H, _, _, _, _, _, _, -, ⟨θ⟩⟩ :=
    HopfAlgebra.exists_formallyEtale_bialgEquiv_baseChange_zmodp p hp hker Hbar
  let θ' : ZMod p ⊗[𝓞] H →ₐc[ZMod p] Hbar := θ
  have hθ' : ∀ x, θ' x = θ x := fun _ => rfl
  have hθinj : Function.Injective θ' := EquivLike.injective θ
  have hθbij : Function.Bijective θ' := EquivLike.bijective θ
  obtain ⟨j, hj, -⟩ :=
    Bialgebra.existsUnique_bialgHom_baseChange_eq_zmodp p hp hker H L (jb.comp θ')
  have hjx : ∀ x : ZMod p ⊗[𝓞] H,
      Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (j : H →ₐ[𝓞] L) x = jb (θ' x) :=
    fun x => by rw [hj]; rfl
  have hj1 : ∀ h : H, (1 : ZMod p) ⊗ₜ[𝓞] (j h) = jb (θ' ((1 : ZMod p) ⊗ₜ[𝓞] h)) := fun h => by
    rw [← hjx, Algebra.TensorProduct.map_tmul]
    rfl

  obtain ⟨τH, hτH⟩ := exists_ringEquiv_quotient_tensor p hker H
  have hdiv : ∀ y : H, (1 : ZMod p) ⊗ₜ[𝓞] y = 0 → ∃ y' : H, y = (p : H) * y' := by
    intro y hy
    rw [← hτH, map_eq_zero_iff _ τH.injective, Ideal.Quotient.eq_zero_iff_mem, Ideal.map_span,
      Set.image_singleton, map_natCast, Ideal.mem_span_singleton'] at hy
    obtain ⟨a, ha⟩ := hy
    exact ⟨a, by rw [← ha, mul_comm]⟩

  have hreg : IsSMulRegular L ((p : 𝓞)) := Module.Flat.isSMulRegular_of_nonZeroDivisors hp
  have hstep : ∀ y : H, j y = 0 → ∃ y' : H, y = (p : H) * y' ∧ j y' = 0 := by
    intro y hy
    have h1 : (1 : ZMod p) ⊗ₜ[𝓞] y = 0 := by
      apply hθinj
      apply hjb
      rw [← hj1, hy, TensorProduct.tmul_zero, map_zero, map_zero]
    obtain ⟨y', rfl⟩ := hdiv y h1
    refine ⟨y', rfl, hreg ?_⟩
    have : ((p : 𝓞)) • j y' = j ((p : H) * y') := by
      rw [map_mul, map_natCast, Algebra.smul_def, map_natCast]
    show (p : 𝓞) • j y' = (p : 𝓞) • (0 : L)
    rw [this, hy, smul_zero]
  have hpow : ∀ (k : ℕ) (y : H), j y = 0 → ∃ y' : H, y = (p : H) ^ k * y' ∧ j y' = 0 := by
    intro k
    induction k with
    | zero => exact fun y hy => ⟨y, by rw [pow_zero, one_mul], hy⟩
    | succ k ih =>
      intro y hy
      obtain ⟨y₁, rfl, hy₁⟩ := ih y hy
      obtain ⟨y₂, rfl, hy₂⟩ := hstep y₁ hy₁
      exact ⟨y₂, by ring, hy₂⟩
  haveI : IsAdicComplete (Ideal.span {(p : H)}) H :=
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p H
  have hinj : Function.Injective j := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have hH : IsHausdorff (Ideal.span {(p : H)}) H := inferInstance
    refine hH.haus y fun k => ?_
    rw [SModEq.zero]
    obtain ⟨y', rfl, -⟩ := hpow k y hy
    rw [Ideal.span_singleton_pow, ← smul_eq_mul]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

  have hred : IsReduced (ZMod p ⊗[𝓞] H) := isReduced_of_injective θ' hθinj

  have hbij : Function.Bijective ((Ideal.Quotient.mkₐ (ZMod p) (nilradical (ZMod p ⊗[𝓞] L))).comp
      (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (j : H →ₐ[𝓞] L))) := by
    have hkerπ' : nilradical (ZMod p ⊗[𝓞] L) = RingHom.ker (πb : ZMod p ⊗[𝓞] L →ₐ[ZMod p] Hbar) :=
      hkerπ.symm
    let πq : ((ZMod p ⊗[𝓞] L) ⧸ nilradical (ZMod p ⊗[𝓞] L)) ≃ₐ[ZMod p] Hbar :=
      (Ideal.quotientEquivAlgOfEq (ZMod p) hkerπ').trans (Ideal.quotientKerAlgEquivOfSurjective hπb)
    have hπq : ∀ b, πq (Ideal.Quotient.mk _ b) = πb b := fun b => by
      simp [πq]

    let F : Hbar →ₐ[ZMod p] Hbar := (πb : ZMod p ⊗[𝓞] L →ₐ[ZMod p] Hbar).comp (jb : Hbar →ₐ[ZMod p] _)
    have hF : ∀ y, F y = y ^ p ^ n := by
      intro y
      obtain ⟨b, rfl⟩ := hπb y
      change πb (jb (πb b)) = _
      rw [hcomp, map_pow]
    have hFinj : Function.Injective F := by
      rw [injective_iff_map_eq_zero]
      intro y hy
      rw [hF] at hy
      exact IsReduced.eq_zero y ⟨_, hy⟩
    have hFbij : Function.Bijective F :=
      ⟨hFinj, (LinearMap.injective_iff_surjective (f := F.toLinearMap)).1 hFinj⟩
    have hfx : ∀ x, πq (((Ideal.Quotient.mkₐ (ZMod p) (nilradical (ZMod p ⊗[𝓞] L))).comp
        (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (j : H →ₐ[𝓞] L))) x) = F (θ' x) := by
      intro x
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hπq, hjx]
      rfl
    have heq : ⇑((Ideal.Quotient.mkₐ (ZMod p) (nilradical (ZMod p ⊗[𝓞] L))).comp
        (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (j : H →ₐ[𝓞] L))) =
        πq.symm ∘ F ∘ θ' := by
      funext x
      rw [Function.comp_apply, Function.comp_apply, ← hfx, AlgEquiv.symm_apply_apply]
    rw [heq]
    exact πq.symm.bijective.comp (hFbij.comp hθbij)

  have hidem : ∀ e : L, IsIdempotentElem e → e ∈ Set.range j := by
    intro e he
    have h1e : IsIdempotentElem ((1 : ZMod p) ⊗ₜ[𝓞] e) := by
      change (1 : ZMod p) ⊗ₜ[𝓞] e * (1 : ZMod p) ⊗ₜ[𝓞] e = (1 : ZMod p) ⊗ₜ[𝓞] e
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, he.eq]
    let x : ZMod p ⊗[𝓞] H := θ.symm (πb ((1 : ZMod p) ⊗ₜ[𝓞] e))
    have hθx : θ' x = πb ((1 : ZMod p) ⊗ₜ[𝓞] e) := by
      rw [hθ']
      exact θ.apply_symm_apply _
    have hx : IsIdempotentElem x := by
      have h2 : IsIdempotentElem (θ' x) := by rw [hθx]; exact h1e.map _
      change x * x = x
      apply hθinj
      rw [map_mul]
      exact h2.eq
    obtain ⟨f, ⟨hf, hfx⟩, -⟩ := existsUnique_isIdempotentElem_tmul_eq p hker hmax H x hx
    refine ⟨f, ?_⟩

    have hred_eq : (1 : ZMod p) ⊗ₜ[𝓞] (j f) = (1 : ZMod p) ⊗ₜ[𝓞] e := by
      rw [hj1, hfx, hθx, hcomp, Algebra.TensorProduct.tmul_pow, one_pow,
        ← Nat.succ_pred_eq_of_pos (pow_pos hpp.pos n), he.pow_succ_eq]
    obtain ⟨e₀, -, huniq⟩ := existsUnique_isIdempotentElem_tmul_eq p hker hmax L
      ((1 : ZMod p) ⊗ₜ[𝓞] e) h1e
    rw [huniq (j f) ⟨hf.map j, hred_eq⟩, huniq e ⟨he, rfl⟩]
  exact ⟨H, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, j,
    hinj, hred, hbij, hidem⟩

end HopfAlgebra.EtLiftC12

namespace HopfTransport

open scoped TensorProduct

universe u₁ u₂ u₃

variable (R : Type u₁) [CommRing R] {α : Type u₂} {β : Type u₃} (e : α ≃ β) [CommRing β]

private abbrev _root_.HopfTransport.commRing : CommRing α := e.commRing

p2m_export "HopfTransport" "commRing"
section Alg

variable [Algebra R β]

private abbrev _root_.HopfTransport.algebra : letI := commRing e; Algebra R α := by
  letI := commRing e
  exact e.algebra R

p2m_export "HopfTransport" "algebra"

private def _root_.HopfTransport.algEquiv : by
    letI := commRing e; letI := algebra R e
    exact α ≃ₐ[R] β := by
  letI := commRing e; letI := algebra R e
  exact e.algEquiv R

p2m_export "HopfTransport" "algEquiv"
private theorem algEquiv_apply (a : α) : by
    letI := commRing e; letI := algebra R e
    exact algEquiv R e a = e a := rfl

end Alg

variable [HopfAlgebra R β]

private noncomputable abbrev coalgebraStruct : by
    letI := commRing e; letI := algebra R e
    exact CoalgebraStruct R α := by
  letI := commRing e; letI := algebra R e
  exact
    { comul := (Algebra.TensorProduct.congr (algEquiv R e).symm (algEquiv R e).symm).toLinearMap ∘ₗ
        Coalgebra.comul (R := R) (A := β) ∘ₗ (algEquiv R e).toLinearMap
      counit := Coalgebra.counit (R := R) (A := β) ∘ₗ (algEquiv R e).toLinearMap }

private theorem comul_def (a : α) : by
    letI := commRing e; letI := algebra R e; letI := coalgebraStruct R e
    exact Coalgebra.comul (R := R) a =
      Algebra.TensorProduct.congr (algEquiv R e).symm (algEquiv R e).symm
        (Coalgebra.comul (R := R) (algEquiv R e a)) := rfl

private theorem counit_def (a : α) : by
    letI := commRing e; letI := algebra R e; letI := coalgebraStruct R e
    exact Coalgebra.counit (R := R) a = Coalgebra.counit (R := R) (algEquiv R e a) := rfl

private theorem map_congr_symm (t : β ⊗[R] β) : by
    letI := commRing e; letI := algebra R e
    exact Algebra.TensorProduct.map (algEquiv R e : α →ₐ[R] β) (algEquiv R e : α →ₐ[R] β)
      (Algebra.TensorProduct.congr (algEquiv R e).symm (algEquiv R e).symm t) = t := by
  letI := commRing e; letI := algebra R e
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [Algebra.TensorProduct.congr_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private noncomputable def coalgEquivSymm : by
    letI := commRing e; letI := algebra R e; letI := coalgebraStruct R e
    exact β ≃ₗc[R] α := by
  letI := commRing e; letI := algebra R e; letI := coalgebraStruct R e
  exact
    { (algEquiv R e).symm.toLinearEquiv with
      counit_comp := by
        apply LinearMap.ext
        intro b
        change Coalgebra.counit (R := R) (algEquiv R e ((algEquiv R e).symm b)) = Coalgebra.counit b
        rw [AlgEquiv.apply_symm_apply]
      map_comp_comul := by
        apply LinearMap.ext
        intro b
        change TensorProduct.map (algEquiv R e).symm.toLinearEquiv.toLinearMap
            (algEquiv R e).symm.toLinearEquiv.toLinearMap (Coalgebra.comul (R := R) b) =
          Algebra.TensorProduct.congr (algEquiv R e).symm (algEquiv R e).symm
            (Coalgebra.comul (R := R) (algEquiv R e ((algEquiv R e).symm b)))
        rw [AlgEquiv.apply_symm_apply]
        induction (Coalgebra.comul (R := R) b) using TensorProduct.induction_on with
        | zero => simp
        | tmul x y => simp [Algebra.TensorProduct.congr_apply]
        | add x y hx hy => rw [map_add, map_add, hx, hy] }

private noncomputable abbrev coalgebra : by
    letI := commRing e; letI := algebra R e
    exact Coalgebra R α := by
  letI := commRing e; letI := algebra R e; letI := coalgebraStruct R e
  exact (coalgEquivSymm R e).toCoalgebra

private noncomputable abbrev bialgebra : by
    letI := commRing e; letI := algebra R e
    exact Bialgebra R α := by
  letI := commRing e; letI := algebra R e; letI := coalgebra R e
  refine Bialgebra.mk' R α ?_ ?_ ?_ ?_
  · change Coalgebra.counit (R := R) (algEquiv R e 1) = 1
    rw [map_one, Bialgebra.counit_one]
  · intro a b
    change Coalgebra.counit (R := R) (algEquiv R e (a * b)) =
      Coalgebra.counit (R := R) (algEquiv R e a) * Coalgebra.counit (R := R) (algEquiv R e b)
    rw [map_mul, Bialgebra.counit_mul]
  · change Algebra.TensorProduct.congr (algEquiv R e).symm (algEquiv R e).symm
      (Coalgebra.comul (R := R) (algEquiv R e 1)) = 1
    rw [map_one, Bialgebra.comul_one, map_one]
  · intro a b
    change Algebra.TensorProduct.congr (algEquiv R e).symm (algEquiv R e).symm
        (Coalgebra.comul (R := R) (algEquiv R e (a * b))) =
      Algebra.TensorProduct.congr (algEquiv R e).symm (algEquiv R e).symm
          (Coalgebra.comul (R := R) (algEquiv R e a)) *
        Algebra.TensorProduct.congr (algEquiv R e).symm (algEquiv R e).symm
          (Coalgebra.comul (R := R) (algEquiv R e b))
    rw [map_mul, Bialgebra.comul_mul, map_mul]

private theorem antipode_rTensor (a : α) : by
    letI := commRing e; letI := algebra R e; letI := bialgebra R e
    exact LinearMap.mul' R α
      (((algEquiv R e).symm.toLinearMap ∘ₗ HopfAlgebra.antipode R (A := β) ∘ₗ
          (algEquiv R e).toLinearMap).rTensor α (Coalgebra.comul (R := R) a)) =
      algebraMap R α (Coalgebra.counit (R := R) a) := by
  letI := commRing e; letI := algebra R e; letI := bialgebra R e
  let ℛ := Coalgebra.Repr.arbitrary R (algEquiv R e a)
  rw [comul_def, counit_def, ← ℛ.eq, map_sum, map_sum, map_sum]
  simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul,
    LinearMap.mul'_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    AlgEquiv.coe_algHom, AlgEquiv.apply_symm_apply]
  simp only [← map_mul]
  rw [← map_sum, HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit ℛ, AlgEquiv.commutes]

private theorem antipode_lTensor (a : α) : by
    letI := commRing e; letI := algebra R e; letI := bialgebra R e
    exact LinearMap.mul' R α
      (((algEquiv R e).symm.toLinearMap ∘ₗ HopfAlgebra.antipode R (A := β) ∘ₗ
          (algEquiv R e).toLinearMap).lTensor α (Coalgebra.comul (R := R) a)) =
      algebraMap R α (Coalgebra.counit (R := R) a) := by
  letI := commRing e; letI := algebra R e; letI := bialgebra R e
  let ℛ := Coalgebra.Repr.arbitrary R (algEquiv R e a)
  rw [comul_def, counit_def, ← ℛ.eq, map_sum, map_sum, map_sum]
  simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul,
    LinearMap.mul'_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    AlgEquiv.coe_algHom, AlgEquiv.apply_symm_apply]
  simp only [← map_mul]
  rw [← map_sum, HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit ℛ, AlgEquiv.commutes]

private noncomputable abbrev hopfAlgebra : by
    letI := commRing e; letI := algebra R e
    exact HopfAlgebra R α := by
  letI := commRing e; letI := algebra R e; letI := bialgebra R e
  exact
    { antipode := (algEquiv R e).symm.toLinearMap ∘ₗ HopfAlgebra.antipode R (A := β) ∘ₗ
        (algEquiv R e).toLinearMap
      mul_antipode_rTensor_comul := by
        apply LinearMap.ext
        intro a
        exact antipode_rTensor R e a
      mul_antipode_lTensor_comul := by
        apply LinearMap.ext
        intro a
        exact antipode_lTensor R e a }

private noncomputable def bialgEquiv : by
    letI := commRing e; letI := algebra R e; letI := hopfAlgebra R e
    exact α ≃ₐc[R] β := by
  letI := commRing e; letI := algebra R e; letI := hopfAlgebra R e
  refine BialgEquiv.ofAlgEquiv (algEquiv R e) ?_ ?_
  · apply AlgHom.ext
    intro a
    rfl
  · apply AlgHom.ext
    intro a
    change Algebra.TensorProduct.map (algEquiv R e : α →ₐ[R] β) (algEquiv R e : α →ₐ[R] β)
        (Coalgebra.comul (R := R) a) = Coalgebra.comul (R := R) (algEquiv R e a)
    rw [comul_def]
    exact map_congr_symm R e _

private theorem bialgEquiv_apply (a : α) : by
    letI := commRing e; letI := algebra R e; letI := hopfAlgebra R e
    exact bialgEquiv R e a = e a := rfl

private theorem isCocomm [Coalgebra.IsCocomm R β] : by
    letI := commRing e; letI := algebra R e; letI := hopfAlgebra R e
    exact Coalgebra.IsCocomm R α := by
  letI := commRing e; letI := algebra R e; letI := hopfAlgebra R e
  refine ⟨?_⟩
  apply LinearMap.ext
  intro a
  change TensorProduct.comm R α α (Coalgebra.comul (R := R) a) = Coalgebra.comul (R := R) a
  rw [comul_def]
  have hnat : ∀ t : β ⊗[R] β, TensorProduct.comm R α α
      (Algebra.TensorProduct.congr (algEquiv R e).symm (algEquiv R e).symm t) =
      Algebra.TensorProduct.congr (algEquiv R e).symm (algEquiv R e).symm (TensorProduct.comm R β β t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [Algebra.TensorProduct.congr_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [hnat]
  congr 1
  exact LinearMap.congr_fun (Coalgebra.comm_comp_comul R β) (algEquiv R e a)

end HopfTransport

namespace HopfAlgebra
p2m_export "HopfAlgebra" "sum_mul_antipode_eq_algebraMap_counit mk sum_antipode_mul_eq_algebraMap_counit mul_antipode_rTensor_comul mul_antipode_lTensor_comul exists_isReduced_bialgHom_injective_comp_eq_pow_zmodp exists_formallyEtale_bialgEquiv_baseChange_zmodp"
namespace EtLiftC12
namespace Transport
p2m_open "HopfAlgebra"

private theorem exists_bialgEquiv_of_injective
    {R : Type u} [CommRing R]
    {H₀ : Type w} [CommRing H₀] [HopfAlgebra R H₀] [Coalgebra.IsCocomm R H₀]
    {L : Type v} [CommRing L] [HopfAlgebra R L]
    (j₀ : H₀ →ₐc[R] L) (hj₀ : Function.Injective j₀) :
    ∃ (H : Type v) (_ : CommRing H) (_ : HopfAlgebra R H) (_ : Coalgebra.IsCocomm R H)
      (ε : H₀ ≃ₐc[R] H) (j : H →ₐc[R] L),
      ∀ x : H₀, j (ε x) = j₀ x := by
  classical
  let e₀ : ↥(Set.range (j₀ : H₀ → L)) ≃ H₀ := (Equiv.ofInjective (j₀ : H₀ → L) hj₀).symm
  letI := HopfTransport.commRing e₀
  letI := HopfTransport.algebra R e₀
  letI := HopfTransport.hopfAlgebra R e₀
  refine ⟨↥(Set.range (j₀ : H₀ → L)), inferInstance, inferInstance, HopfTransport.isCocomm R e₀,
    (HopfTransport.bialgEquiv R e₀).symm, j₀.comp (HopfTransport.bialgEquiv R e₀ : _ →ₐc[R] H₀),
    fun x => ?_⟩
  rw [BialgHom.comp_apply]
  change j₀ (HopfTransport.bialgEquiv R e₀ ((HopfTransport.bialgEquiv R e₀).symm x)) = j₀ x
  rw [BialgEquiv.apply_symm_apply]

end HopfAlgebra.EtLiftC12.Transport

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (L : Type v) [CommRing L] [HopfAlgebra 𝓞 L] [Coalgebra.IsCocomm 𝓞 L]
    [Module.Free 𝓞 L] [Module.Finite 𝓞 L] :
    ∃ (H : Type v) (_ : CommRing H) (_ : HopfAlgebra 𝓞 H) (_ : Coalgebra.IsCocomm 𝓞 H)
      (_ : Module.Free 𝓞 H) (_ : Module.Finite 𝓞 H) (_ : Algebra.FormallyEtale 𝓞 H) (j : H →ₐc[𝓞] L),
      Function.Injective j ∧
      IsReduced (ZMod p ⊗[𝓞] H) ∧
      Function.Bijective ((Ideal.Quotient.mkₐ (ZMod p) (nilradical (ZMod p ⊗[𝓞] L))).comp
        (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (j : H →ₐ[𝓞] L))) ∧
      ∀ e : L, IsIdempotentElem e → e ∈ Set.range j := by
  classical
  obtain ⟨H₀, _, _, _, _, _, _, j₀, hinj₀, hred₀, hbij₀, hidem₀⟩ :=
    HopfAlgebra.EtLiftC12.mainU p hp hker L
  obtain ⟨H, _, _, _, ε, j, hjε⟩ :=
    HopfAlgebra.EtLiftC12.Transport.exists_bialgEquiv_of_injective (R := 𝓞) j₀ hinj₀
  let ε' : H₀ ≃ₐ[𝓞] H := ε
  have hε' : ∀ x, ε' x = ε x := fun _ => rfl
  haveI : Module.Free 𝓞 H := Module.Free.of_equiv ε'.toLinearEquiv
  haveI : Module.Finite 𝓞 H := Module.Finite.equiv ε'.toLinearEquiv
  haveI : Algebra.FormallyEtale 𝓞 H := Algebra.FormallyEtale.of_equiv ε'

  have hjcomp : (j : H →ₐ[𝓞] L) = (j₀ : H₀ →ₐ[𝓞] L).comp (ε'.symm : H →ₐ[𝓞] H₀) := by
    ext y
    change j y = j₀ (ε'.symm y)
    rw [← hjε, ← hε', AlgEquiv.apply_symm_apply]
  have hjy : ∀ y : H, j y = j₀ (ε'.symm y) := fun y => DFunLike.congr_fun hjcomp y
  refine ⟨H, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, j,
    ?_, ?_, ?_, ?_⟩
  ·
    intro y₁ y₂ h
    rw [hjy, hjy] at h
    exact ε'.symm.injective (hinj₀ h)
  ·
    let κ : ZMod p ⊗[𝓞] H ≃ₐ[ZMod p] ZMod p ⊗[𝓞] H₀ :=
      Algebra.TensorProduct.congr (AlgEquiv.refl : ZMod p ≃ₐ[ZMod p] ZMod p) ε'.symm
    exact isReduced_of_injective κ κ.injective
  ·
    have hmap : Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (j : H →ₐ[𝓞] L) =
        (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (j₀ : H₀ →ₐ[𝓞] L)).comp
          (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (ε'.symm : H →ₐ[𝓞] H₀)) := by
      rw [← Algebra.TensorProduct.map_comp, AlgHom.comp_id, ← hjcomp]
    have hbijε : Function.Bijective
        (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (ε'.symm : H →ₐ[𝓞] H₀)) := by
      have h := (Algebra.TensorProduct.congr (AlgEquiv.refl : ZMod p ≃ₐ[ZMod p] ZMod p) ε'.symm).bijective
      have hfun : ⇑(Algebra.TensorProduct.congr (AlgEquiv.refl : ZMod p ≃ₐ[ZMod p] ZMod p) ε'.symm) =
          ⇑(Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (ε'.symm : H →ₐ[𝓞] H₀)) := by
        funext x
        rw [Algebra.TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom]
      rwa [hfun] at h
    rw [hmap, ← AlgHom.comp_assoc, AlgHom.coe_comp]
    exact hbij₀.comp hbijε
  ·
    intro e he
    obtain ⟨x, hx⟩ := hidem₀ e he
    exact ⟨ε x, by rw [hjε, hx]⟩

end S_HopfAlgebra_exists_formallyEtale_bialgHom_injective_bijective_baseChange_zmodp
end P2MW
export P2MW.S_HopfAlgebra_exists_formallyEtale_bialgHom_injective_bijective_baseChange_zmodp (solution)
