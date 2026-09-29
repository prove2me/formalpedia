-- Prove2me | solution 1 for HopfAlgebra.map_hopfKer_eq_hopfKer_of_comul_mul_tmul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/bba6074a-9506-5b30-8752-1e515dcb762d

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Theorems.Thm_HopfAlgebra_toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique
import Theorems.Thm_HopfAlgebra_exists_algHom_comp_hopfKer_val_eq_of_surjective_of_isAlgClosed
import Theorems.Thm_Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_IsReduced_of_finrank_le_natCard_algHom
import Theorems.Thm_Algebra_Etale_of_isReduced_of_perfectField
import Theorems.Thm_Algebra_Etale_natCard_algHom_eq_finrank_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_comul_mul_tmul_eq

set_option autoImplicit false
open scoped TensorProduct
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk antipode_one antipode_mul mul_antipode_rTensor_comul_apply coaction coaction_apply hopfKer toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique exists_algHom_comp_hopfKer_val_eq_of_surjective_of_isAlgClosed natCard_algHom_eq_finrank_of_charZero"
namespace FC
p2m_open "HopfAlgebra"

theorem apply_eq_one_of_ker_eq
    (K : Type) [Field K] (A : Type) [CommRing A] [HopfAlgebra K A] (e : A)
    (Af : Type) [CommRing Af] [Algebra K Af] (πf : A →ₐ[K] Af)
    (hkerf : RingHom.ker πf = Ideal.span {1 - e}) :
    πf e = 1 := by
  have h : (1 - e) ∈ RingHom.ker πf := by
    rw [hkerf]; exact Ideal.mem_span_singleton_self _
  have h2 : πf (1 - e) = 0 := h
  rw [map_sub, map_one, sub_eq_zero] at h2
  exact h2.symm

theorem comp_apply_eq_one_of_ker_eq
    (K : Type) [Field K] (A : Type) [CommRing A] [HopfAlgebra K A] (e : A)
    (Af : Type) [CommRing Af] [Algebra K Af] (πf : A →ₐ[K] Af)
    (hkerf : RingHom.ker πf = Ideal.span {1 - e})
    (L : Type) [CommRing L] [Algebra K L] (ψ : Af →ₐ[K] L) :
    (ψ.comp πf) e = 1 := by
  rw [AlgHom.comp_apply]
  show ψ (πf e) = 1
  rw [apply_eq_one_of_ker_eq K A e Af πf hkerf, map_one]

theorem existsUnique_comp_eq_of_apply_eq_one
    (K : Type) [Field K] (A : Type) [CommRing A] [HopfAlgebra K A] (e : A)
    (Af : Type) [CommRing Af] [Algebra K Af] (πf : A →ₐ[K] Af) (hπf : Function.Surjective πf)
    (hkerf : RingHom.ker πf = Ideal.span {1 - e})
    (L : Type) [CommRing L] [Algebra K L] (μ : A →ₐ[K] L) (hμ : μ e = 1) :
    ∃! ψ : Af →ₐ[K] L, ψ.comp πf = μ := by
  have hle : ∀ a ∈ RingHom.ker (πf : A →+* Af), μ a = 0 := by
    intro a ha
    have ha' : a ∈ Ideal.span {1 - e} := by
      have : a ∈ RingHom.ker πf := ha
      rwa [hkerf] at this
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha'
    rw [map_mul, map_sub, map_one, hμ, sub_self, mul_zero]
  let e1 : (A ⧸ RingHom.ker (πf : A →+* Af)) ≃ₐ[K] Af :=
    Ideal.quotientKerAlgEquivOfSurjective hπf
  let ψ0 : (A ⧸ RingHom.ker (πf : A →+* Af)) →ₐ[K] L := Ideal.Quotient.liftₐ _ μ hle
  have hs : ∀ a : A, e1.symm (πf a) = Ideal.Quotient.mk _ a := by
    intro a
    rw [AlgEquiv.symm_apply_eq]
    show πf a = Ideal.quotientKerAlgEquivOfSurjective hπf (Ideal.Quotient.mk _ a)
    rw [Ideal.quotientKerAlgEquivOfSurjective_apply]
    exact (RingHom.kerLift_mk (πf : A →+* Af) a).symm
  refine ⟨ψ0.comp (e1.symm : Af →ₐ[K] _), ?_, ?_⟩
  · apply AlgHom.ext
    intro a
    show ψ0 (e1.symm (πf a)) = μ a
    rw [hs]
    rfl
  · intro ψ hψ
    apply AlgHom.ext
    intro b
    obtain ⟨a, rfl⟩ := hπf b
    have h1 : ψ (πf a) = μ a := by rw [← hψ]; rfl
    rw [h1]
    show μ a = ψ0 (e1.symm (πf a))
    rw [hs]
    rfl

theorem forall_comp_apply_eq_one_and_existsUnique_comp_eq
    (K : Type) [Field K] (A : Type) [CommRing A] [HopfAlgebra K A] (e : A)
    (Af : Type) [CommRing Af] [Algebra K Af] (πf : A →ₐ[K] Af) (hπf : Function.Surjective πf)
    (hkerf : RingHom.ker πf = Ideal.span {1 - e}) :
    (∀ ψ : Af →ₐ[K] AlgebraicClosure K, (ψ.comp πf) e = 1) ∧
    (∀ μ : A →ₐ[K] AlgebraicClosure K, μ e = 1 →
      ∃! ψ : Af →ₐ[K] AlgebraicClosure K, ψ.comp πf = μ) :=
  ⟨fun ψ => comp_apply_eq_one_of_ker_eq K A e Af πf hkerf (AlgebraicClosure K) ψ,
   fun μ hμ => existsUnique_comp_eq_of_apply_eq_one K A e Af πf hπf hkerf (AlgebraicClosure K) μ hμ⟩

theorem convMul_apply_eq_of_apply_eq_one
    (K : Type) [Field K] (A : Type) [CommRing A] [HopfAlgebra K A] (e : A)
    (hΔe : Coalgebra.comul (R := K) e * (e ⊗ₜ[K] (1 : A)) = e ⊗ₜ[K] e)
    (L : Type) [CommRing L] [Algebra K L] (ν w : WithConv (A →ₐ[K] L))
    (hν : WithConv.ofConv ν e = 1) :
    WithConv.ofConv (ν * w) e = WithConv.ofConv w e := by
  have key := congrArg (Algebra.TensorProduct.lift (WithConv.ofConv ν) (WithConv.ofConv w)
    (fun _ _ => Commute.all _ _)) hΔe
  rw [map_mul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, map_one, mul_one, hν,
    mul_one, one_mul] at key

  rw [← key]
  exact AlgHom.convMul_apply ν w e

theorem convOne_apply_eq_one
    (K : Type) [Field K] (A : Type) [CommRing A] [HopfAlgebra K A] (e : A)
    (hεe : Coalgebra.counit (R := K) e = 1)
    (L : Type) [CommRing L] [Algebra K L] :
    WithConv.ofConv (1 : WithConv (A →ₐ[K] L)) e = 1 := by
  rw [AlgHom.convOne_apply, hεe, map_one]

def Esub (K : Type) [Field K] (A : Type) [CommRing A] [HopfAlgebra K A] (e : A)
    (hΔe : Coalgebra.comul (R := K) e * (e ⊗ₜ[K] (1 : A)) = e ⊗ₜ[K] e)
    (hεe : Coalgebra.counit (R := K) e = 1)
    (L : Type) [CommRing L] [Algebra K L] : Submonoid (WithConv (A →ₐ[K] L)) where
  carrier := {ν | WithConv.ofConv ν e = 1}
  one_mem' := convOne_apply_eq_one K A e hεe L
  mul_mem' {ν w} hν hw := by
    show WithConv.ofConv (ν * w) e = 1
    rw [convMul_apply_eq_of_apply_eq_one K A e hΔe L ν w hν]
    exact hw

theorem mem_Esub_iff (K : Type) [Field K] (A : Type) [CommRing A] [HopfAlgebra K A] (e : A)
    (hΔe : Coalgebra.comul (R := K) e * (e ⊗ₜ[K] (1 : A)) = e ⊗ₜ[K] e)
    (hεe : Coalgebra.counit (R := K) e = 1)
    (L : Type) [CommRing L] [Algebra K L] (ν : WithConv (A →ₐ[K] L)) :
    ν ∈ Esub K A e hΔe hεe L ↔ WithConv.ofConv ν e = 1 := Iff.rfl

theorem mul_mem_Esub_iff (K : Type) [Field K] (A : Type) [CommRing A] [HopfAlgebra K A] (e : A)
    (hΔe : Coalgebra.comul (R := K) e * (e ⊗ₜ[K] (1 : A)) = e ⊗ₜ[K] e)
    (hεe : Coalgebra.counit (R := K) e = 1)
    (L : Type) [CommRing L] [Algebra K L] {ν w : WithConv (A →ₐ[K] L)}
    (hν : ν ∈ Esub K A e hΔe hεe L) :
    ν * w ∈ Esub K A e hΔe hεe L ↔ w ∈ Esub K A e hΔe hεe L := by
  rw [mem_Esub_iff, mem_Esub_iff, convMul_apply_eq_of_apply_eq_one K A e hΔe L ν w hν]

end HopfAlgebra.FC

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk antipode_one antipode_mul mul_antipode_rTensor_comul_apply coaction coaction_apply hopfKer toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique exists_algHom_comp_hopfKer_val_eq_of_surjective_of_isAlgClosed natCard_algHom_eq_finrank_of_charZero"
namespace FC
p2m_open "HopfAlgebra"

noncomputable def liftPtEquiv (K : Type*) [Field K] (L : Type*) [CommRing L] [Algebra K L]
    (B : Type*) [CommRing B] [Algebra K B] :
    (B →ₐ[K] L) ≃ (L ⊗[K] B →ₐ[L] L) where
  toFun g := Algebra.TensorProduct.lift (Algebra.ofId L L) g (fun _ _ => Commute.all _ _)
  invFun φ := (φ.restrictScalars K).comp Algebra.TensorProduct.includeRight
  left_inv g := by
    apply AlgHom.ext
    intro b
    show Algebra.TensorProduct.lift (Algebra.ofId L L) g (fun _ _ => Commute.all _ _) ((1 : L) ⊗ₜ[K] b) = g b
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  right_inv φ := by
    apply Algebra.TensorProduct.ext'
    intro l b
    rw [Algebra.TensorProduct.lift_tmul]
    show algebraMap L L l * φ ((1 : L) ⊗ₜ[K] b) = φ (l ⊗ₜ[K] b)
    rw [Algebra.algebraMap_self, RingHom.id_apply, ← smul_eq_mul, ← map_smul, TensorProduct.smul_tmul',
      smul_eq_mul, mul_one]

theorem natCard_algHom_eq_natCard_baseChange (K : Type*) [Field K] (L : Type*) [CommRing L] [Algebra K L]
    (B : Type*) [CommRing B] [Algebra K B] :
    Nat.card (B →ₐ[K] L) = Nat.card (L ⊗[K] B →ₐ[L] L) :=
  Nat.card_congr (liftPtEquiv K L B)

theorem finrank_subalgebra_eq_natCard_algHom
    (K : Type) [Field K] (Af : Type) [CommRing Af] [Algebra K Af] [Module.Finite K Af]
    (hpts : Nat.card (Af →ₐ[K] AlgebraicClosure K) = Module.finrank K Af)
    (S : Subalgebra K Af) :
    Module.finrank K ↥S = Nat.card (↥S →ₐ[K] AlgebraicClosure K) := by
  classical

  haveI : Module.Finite K ↥S := Module.Finite.of_injective S.val.toLinearMap Subtype.val_injective

  have hred : IsReduced (AlgebraicClosure K ⊗[K] Af) := by
    apply IsReduced.of_finrank_le_natCard_algHom (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] Af)
    rw [← natCard_algHom_eq_natCard_baseChange K (AlgebraicClosure K) Af, hpts, Module.finrank_baseChange]

  haveI : IsReduced (AlgebraicClosure K ⊗[K] ↥S) := by
    haveI := hred
    apply isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id (AlgebraicClosure K) (AlgebraicClosure K)) S.val)
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := AlgebraicClosure K) S.val.toLinearMap
      Subtype.val_injective
    intro x y hxy
    apply h
    have e1 : ∀ z, S.val.toLinearMap.lTensor (AlgebraicClosure K) z =
        Algebra.TensorProduct.map (AlgHom.id (AlgebraicClosure K) (AlgebraicClosure K)) S.val z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    rw [e1, e1]; exact hxy

  haveI : Algebra.Etale (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] ↥S) :=
    Algebra.Etale.of_isReduced_of_perfectField (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] ↥S)
  have hcount := Algebra.Etale.natCard_algHom_eq_finrank_of_isAlgClosed (AlgebraicClosure K)
    (AlgebraicClosure K ⊗[K] ↥S)
  rw [natCard_algHom_eq_natCard_baseChange K (AlgebraicClosure K) ↥S, hcount, Module.finrank_baseChange]

theorem finrank_eq_natCard_algHom
    (K : Type) [Field K] (Af : Type) [CommRing Af] [Algebra K Af] [Module.Finite K Af]
    (hpts : Nat.card (Af →ₐ[K] AlgebraicClosure K) = Module.finrank K Af) :
    Module.finrank K Af = Nat.card (Af →ₐ[K] AlgebraicClosure K) := hpts.symm

end HopfAlgebra.FC

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk antipode_one antipode_mul mul_antipode_rTensor_comul_apply coaction coaction_apply hopfKer toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique exists_algHom_comp_hopfKer_val_eq_of_surjective_of_isAlgClosed natCard_algHom_eq_finrank_of_charZero"
namespace FC
p2m_open "HopfAlgebra"

open scoped TensorProduct

theorem map_hopfKer_le_hopfKer
    {R : Type*} [CommRing R] {A Ā Af Āf : Type*} [CommRing A] [CommRing Ā] [CommRing Af] [CommRing Āf]
    [HopfAlgebra R A] [HopfAlgebra R Ā] [HopfAlgebra R Af] [HopfAlgebra R Āf]
    (π : A →ₐc[R] Ā) (πf : A →ₐc[R] Af) (πf' : Ā →ₐc[R] Āf) (πff : Af →ₐc[R] Āf)
    (hcomm : ∀ x : A, πff (πf x) = πf' (π x)) :
    (HopfAlgebra.hopfKer π).map (πf : A →ₐ[R] Af) ≤ HopfAlgebra.hopfKer πff := by
  rintro _ ⟨b, hb, rfl⟩
  have hb' : HopfAlgebra.coaction π b = b ⊗ₜ[R] 1 := hb
  show HopfAlgebra.coaction πff ((πf : A →ₐ[R] Af) b) = (πf : A →ₐ[R] Af) b ⊗ₜ[R] 1
  rw [HopfAlgebra.coaction_apply] at hb' ⊢

  have h1 := (LinearMap.congr_fun (CoalgHomClass.map_comp_comul (πf : A →ₐc[R] Af)) b).symm
  simp only [LinearMap.comp_apply] at h1

  change TensorProduct.map (AlgHom.id R Af).toLinearMap (πff : Af →ₐ[R] Āf).toLinearMap
      (Coalgebra.comul (R := R) ((πf : A →ₐ[R] Af) b)) = _
  change TensorProduct.map (AlgHom.id R A).toLinearMap (π : A →ₐ[R] Ā).toLinearMap (Coalgebra.comul (R := R) b)
      = b ⊗ₜ[R] 1 at hb'
  erw [h1]
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
  have h2 : TensorProduct.map ((AlgHom.id R Af).toLinearMap ∘ₗ ((πf : A →ₐc[R] Af) : A →ₗ[R] Af))
        ((πff : Af →ₐ[R] Āf).toLinearMap ∘ₗ ((πf : A →ₐc[R] Af) : A →ₗ[R] Af))
      = TensorProduct.map (πf : A →ₐ[R] Af).toLinearMap (πf' : Ā →ₐ[R] Āf).toLinearMap ∘ₗ
          TensorProduct.map (AlgHom.id R A).toLinearMap (π : A →ₐ[R] Ā).toLinearMap := by
    rw [← TensorProduct.map_comp]
    congr 1
    all_goals (apply LinearMap.ext; intro x; first | rfl | exact hcomm x)
  erw [h2]
  rw [LinearMap.comp_apply, hb', TensorProduct.map_tmul]
  change (πf b) ⊗ₜ[R] (πf' 1) = (πf : A →ₐ[R] Af) b ⊗ₜ[R] 1
  rw [map_one]
  rfl

end HopfAlgebra.FC

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk antipode_one antipode_mul mul_antipode_rTensor_comul_apply coaction coaction_apply hopfKer toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique exists_algHom_comp_hopfKer_val_eq_of_surjective_of_isAlgClosed natCard_algHom_eq_finrank_of_charZero"
namespace FC
p2m_open "HopfAlgebra"

section Coc
variable (K : Type) [CommSemiring K] (A Af : Type) [CommRing A] [CommRing Af] [Bialgebra K A] [Bialgebra K Af]

theorem isCocomm_of_surjective [Coalgebra.IsCocomm K A] (πf : A →ₐc[K] Af) (hπf : Function.Surjective πf) :
    Coalgebra.IsCocomm K Af := by
  refine ⟨?_⟩
  apply LinearMap.ext
  intro b
  obtain ⟨a, rfl⟩ := hπf b
  rw [LinearMap.comp_apply]
  change TensorProduct.comm K Af Af (Coalgebra.comul (πf a)) = Coalgebra.comul (πf a)
  rw [← CoalgHomClass.map_comp_comul_apply πf a]
  have hnat : ∀ z : A ⊗[K] A, TensorProduct.comm K Af Af (TensorProduct.map (πf : A →ₗ[K] Af) (πf : A →ₗ[K] Af) z)
      = TensorProduct.map (πf : A →ₗ[K] Af) (πf : A →ₗ[K] Af) (TensorProduct.comm K A A z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    | tmul x y => rw [TensorProduct.map_tmul, TensorProduct.comm_tmul, TensorProduct.comm_tmul, TensorProduct.map_tmul]
  rw [hnat, Coalgebra.comm_comul]

end Coc

section E0
variable (K : Type) [Field K]

namespace E0aux

theorem exists_comp_eq_of_apply_eq_one (Ā : Type) [CommRing Ā] [Algebra K Ā] (x : Ā)
    (Āf : Type) [CommRing Āf] [Algebra K Āf] (πf' : Ā →ₐ[K] Āf) (hπf' : Function.Surjective πf')
    (hkerf' : RingHom.ker πf' = Ideal.span {1 - x}) (L : Type) [CommRing L] [Algebra K L]
    (χ : Ā →ₐ[K] L) (hχ : χ x = 1) : ∃ ψ : Āf →ₐ[K] L, ψ.comp πf' = χ := by
  have hk : ∀ a, πf' a = 0 → χ a = 0 := by
    intro a ha
    have ha' : a ∈ Ideal.span {1 - x} := by rw [← hkerf']; exact ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha'
    rw [map_mul, map_sub, map_one, hχ, sub_self, mul_zero]
  refine ⟨(Ideal.Quotient.liftₐ (RingHom.ker πf') χ (fun a ha => hk a ha)).comp
    (Ideal.quotientKerAlgEquivOfSurjective hπf').symm.toAlgHom, ?_⟩
  apply AlgHom.ext
  intro a
  have hq : (Ideal.quotientKerAlgEquivOfSurjective hπf').symm (πf' a) = Ideal.Quotient.mk (RingHom.ker πf') a := by
    rw [AlgEquiv.symm_apply_eq, Ideal.quotientKerAlgEquivOfSurjective_mk]
  change (Ideal.Quotient.liftₐ (RingHom.ker πf') χ (fun a ha => hk a ha))
      ((Ideal.quotientKerAlgEquivOfSurjective hπf').symm (πf' a)) = χ a
  rw [hq]
  rfl

theorem apply_eq_one_of_ker_eq (Ā : Type) [CommRing Ā] [Algebra K Ā] (x : Ā)
    (Āf : Type) [CommRing Āf] [Algebra K Āf] (πf' : Ā →ₐ[K] Āf)
    (hkerf' : RingHom.ker πf' = Ideal.span {1 - x}) : πf' x = 1 := by
  have h : (1 - x) ∈ RingHom.ker πf' := by rw [hkerf']; exact Ideal.mem_span_singleton_self _
  rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h
  exact h.symm

noncomputable def subtypeEquivAlgHom (Ā : Type) [CommRing Ā] [Algebra K Ā] (x : Ā)
    (Āf : Type) [CommRing Āf] [Algebra K Āf] (πf' : Ā →ₐ[K] Āf) (hπf' : Function.Surjective πf')
    (hkerf' : RingHom.ker πf' = Ideal.span {1 - x}) (L : Type) [CommRing L] [Algebra K L] :
    {χ : Ā →ₐ[K] L // χ x = 1} ≃ (Āf →ₐ[K] L) where
  toFun χ := (exists_comp_eq_of_apply_eq_one K Ā x Āf πf' hπf' hkerf' L χ.1 χ.2).choose
  invFun ψ := ⟨ψ.comp πf', by rw [AlgHom.comp_apply, apply_eq_one_of_ker_eq K Ā x Āf πf' hkerf', map_one]⟩
  left_inv χ := Subtype.ext (exists_comp_eq_of_apply_eq_one K Ā x Āf πf' hπf' hkerf' L χ.1 χ.2).choose_spec
  right_inv ψ := by
    have h := (exists_comp_eq_of_apply_eq_one K Ā x Āf πf' hπf' hkerf' L (ψ.comp πf')
      (by rw [AlgHom.comp_apply, apply_eq_one_of_ker_eq K Ā x Āf πf' hkerf', map_one])).choose_spec
    apply AlgHom.ext
    intro b
    obtain ⟨a, rfl⟩ := hπf' b
    exact DFunLike.congr_fun h a

end E0aux

theorem natCard_subtype_algHom_apply_eq_one_ne_zero
    (K : Type) [Field K] [CharZero K]
    (Ā : Type) [CommRing Ā] [HopfAlgebra K Ā] [Module.Finite K Ā] (x : Ā) (hx : Coalgebra.counit (R := K) x = 1)
    (Āf : Type) [CommRing Āf] [HopfAlgebra K Āf] (πf' : Ā →ₐc[K] Āf) (hπf' : Function.Surjective πf')
    (hkerf' : RingHom.ker (πf' : Ā →ₐ[K] Āf) = Ideal.span {1 - x}) :
    Nat.card {χ : Ā →ₐ[K] AlgebraicClosure K // χ x = 1} ≠ 0 := by
  haveI : Module.Finite K Āf :=
    Module.Finite.of_surjective ((πf' : Ā →ₐ[K] Āf).toLinearMap) hπf'

  haveI : Nontrivial Āf := by
    refine ⟨⟨1, 0, fun h10 => ?_⟩⟩
    have hmem : (1 : Ā) ∈ RingHom.ker (πf' : Ā →ₐ[K] Āf) := by
      rw [RingHom.mem_ker, map_one]; exact h10
    rw [hkerf'] at hmem
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
    have := congrArg (Coalgebra.counit (R := K) (A := Ā)) hb
    rw [Bialgebra.counit_mul, map_sub, Bialgebra.counit_one, hx, sub_self, mul_zero] at this
    exact zero_ne_one this
  rw [Nat.card_congr (E0aux.subtypeEquivAlgHom K Ā x Āf (πf' : Ā →ₐ[K] Āf) hπf' hkerf' (AlgebraicClosure K)),
    HopfAlgebra.natCard_algHom_eq_finrank_of_charZero K Āf (AlgebraicClosure K)]
  exact Module.finrank_pos.ne'

end E0

end HopfAlgebra.FC

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk antipode_one antipode_mul mul_antipode_rTensor_comul_apply coaction coaction_apply hopfKer toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique exists_algHom_comp_hopfKer_val_eq_of_surjective_of_isAlgClosed natCard_algHom_eq_finrank_of_charZero"
namespace FC
p2m_open "HopfAlgebra"

theorem natCard_eq_mul_of_fibre {M X G : Type*} [Finite M] [Finite G]
    (res : M → X) (hsurj : Function.Surjective res) (act : M → G → M)
    (hfib : ∀ m m' : M, res m = res m' ↔ ∃ g : G, m' = act m g)
    (hfree : ∀ m : M, Function.Injective (act m)) :
    Nat.card M = Nat.card X * Nat.card G := by
  classical
  choose s hs using hsurj
  let φ : X × G → M := fun p => act (s p.1) p.2
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨x, g⟩ ⟨x', g'⟩ h
      simp only [φ] at h
      have hx : x = x' := by
        have h1 : res (s x) = res (act (s x) g) := (hfib _ _).mpr ⟨g, rfl⟩
        have h2 : res (s x') = res (act (s x') g') := (hfib _ _).mpr ⟨g', rfl⟩
        rw [hs, h] at h1; rw [hs] at h2; exact h1.trans h2.symm
      subst hx
      exact Prod.ext rfl (hfree _ h)
    · intro m
      obtain ⟨g, hg⟩ := (hfib (s (res m)) m).mp (hs (res m))
      exact ⟨(res m, g), hg.symm⟩
  rw [← Nat.card_eq_of_bijective φ hφ, Nat.card_prod]

theorem natCard_le_mul_of_fibre {M X G : Type*} [Finite M] [Finite X] [Finite G]
    (res : M → X)
    (ι : ∀ m : M, {m' : M // res m' = res m} → G) (hι : ∀ m, Function.Injective (ι m)) :
    Nat.card M ≤ Nat.card X * Nat.card G := by
  classical
  haveI := Fintype.ofFinite M; haveI := Fintype.ofFinite X; haveI := Fintype.ofFinite G
  have h1 : Nat.card M = ∑ x : X, Fintype.card {m : M // res m = x} := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv res).symm
  have h2 : ∀ x : X, Fintype.card {m : M // res m = x} ≤ Fintype.card G := by
    intro x
    by_cases hx : ∃ m, res m = x
    · obtain ⟨m, rfl⟩ := hx
      exact Fintype.card_le_of_injective (ι m) (hι m)
    · have : IsEmpty {m : M // res m = x} := ⟨fun m => hx ⟨m.1, m.2⟩⟩
      simp
  calc Nat.card M = ∑ x : X, Fintype.card {m : M // res m = x} := h1
    _ ≤ ∑ _x : X, Fintype.card G := Finset.sum_le_sum fun x _ => h2 x
    _ = Nat.card X * Nat.card G := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

noncomputable def antipodeAlgHom' (K : Type*) [CommRing K] (A : Type*) [CommRing A] [HopfAlgebra K A] :
    A →ₐ[K] A :=
  AlgHom.ofLinearMap (HopfAlgebraStruct.antipode (R := K))
    (HopfAlgebra.antipode_one (R := K) (A := A))
    (fun a b => by rw [HopfAlgebra.antipode_mul, mul_comm])

theorem antipodeAlgHom'_apply {K : Type*} [CommRing K] {A : Type*} [CommRing A] [HopfAlgebra K A]
    (a : A) : antipodeAlgHom' K A a = HopfAlgebraStruct.antipode (R := K) a := rfl

theorem exists_left_inv_point
    {K : Type*} [CommRing K] {A : Type*} [CommRing A] [HopfAlgebra K A]
    {L : Type*} [CommRing L] [Algebra K L] (ν : A →ₐ[K] L) :
    ∃ ν' : A →ₐ[K] L, WithConv.toConv ν' * WithConv.toConv ν = 1 := by
  refine ⟨ν.comp (antipodeAlgHom' K A), ?_⟩
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  change (WithConv.toConv (ν.comp (antipodeAlgHom' K A)) * WithConv.toConv ν).ofConv a =
    (1 : WithConv (A →ₐ[K] L)).ofConv a
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
  have key : (Algebra.TensorProduct.lift (ν.comp (antipodeAlgHom' K A)) ν
      (fun _ _ => Commute.all _ _)).toLinearMap =
      ν.toLinearMap ∘ₗ LinearMap.mul' K A ∘ₗ (HopfAlgebraStruct.antipode (R := K)).rTensor A := by
    apply TensorProduct.ext'
    intro x y
    simp [Algebra.TensorProduct.lift_tmul, LinearMap.rTensor_tmul, antipodeAlgHom'_apply]
  have h := LinearMap.congr_fun key (Coalgebra.comul (R := K) a)
  simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply] at h
  change Algebra.TensorProduct.lift (ν.comp (antipodeAlgHom' K A)) ν _ (Coalgebra.comul (R := K) a) = _
  rw [h, HopfAlgebra.mul_antipode_rTensor_comul_apply, AlgHom.commutes]

theorem mul_right_injective_point
    {K : Type*} [CommRing K] {A : Type*} [CommRing A] [HopfAlgebra K A]
    {L : Type*} [CommRing L] [Algebra K L] (ν : WithConv (A →ₐ[K] L)) :
    Function.Injective (fun μ : WithConv (A →ₐ[K] L) => ν * μ) := by
  intro μ₁ μ₂ h
  obtain ⟨ν', hl⟩ := exists_left_inv_point (K := K) ν.ofConv
  have hl' : WithConv.toConv ν' * ν = 1 := by simpa using hl
  simp only at h
  calc μ₁ = (WithConv.toConv ν' * ν) * μ₁ := by rw [hl', one_mul]
    _ = WithConv.toConv ν' * (ν * μ₁) := by rw [mul_assoc]
    _ = WithConv.toConv ν' * (ν * μ₂) := by rw [h]
    _ = (WithConv.toConv ν' * ν) * μ₂ := by rw [mul_assoc]
    _ = μ₂ := by rw [hl', one_mul]

theorem comp_injective_of_surjective {K : Type*} [CommSemiring K] {A B L : Type*} [Semiring A] [Semiring B]
    [Semiring L] [Algebra K A] [Algebra K B] [Algebra K L] (π : A →ₐ[K] B) (hπ : Function.Surjective π)
    {χ χ' : B →ₐ[K] L} (h : χ.comp π = χ'.comp π) : χ = χ' := by
  apply AlgHom.ext
  intro b
  obtain ⟨a, rfl⟩ := hπ b
  exact DFunLike.congr_fun h a

theorem natCard_algHom_ne_zero (K : Type) [Field K] [CharZero K] (A : Type) [CommRing A] [HopfAlgebra K A]
    [Module.Finite K A] : Nat.card (A →ₐ[K] AlgebraicClosure K) ≠ 0 := by
  haveI : Nontrivial A := (Bialgebra.counitAlgHom K A).toRingHom.domain_nontrivial
  rw [HopfAlgebra.natCard_algHom_eq_finrank_of_charZero K A (AlgebraicClosure K)]
  exact Module.finrank_pos.ne'

theorem finite_algHom (K : Type) [Field K] [CharZero K] (A : Type) [CommRing A] [HopfAlgebra K A]
    [Module.Finite K A] : Finite (A →ₐ[K] AlgebraicClosure K) :=
  Nat.finite_of_card_ne_zero (natCard_algHom_ne_zero K A)

theorem natCard_hopfKer_mul_natCard_eq
    (K : Type) [Field K] [CharZero K]
    (Af : Type) [CommRing Af] [HopfAlgebra K Af] [Module.Finite K Af] [Coalgebra.IsCocomm K Af]
    (Āf : Type) [CommRing Āf] [HopfAlgebra K Āf]
    (πff : Af →ₐc[K] Āf) (hπff : Function.Surjective πff) :
    Nat.card (↥(HopfAlgebra.hopfKer πff) →ₐ[K] AlgebraicClosure K) *
        Nat.card (Āf →ₐ[K] AlgebraicClosure K) =
      Nat.card (Af →ₐ[K] AlgebraicClosure K) := by
  classical
  haveI : Module.Finite K Āf := Module.Finite.of_surjective (πff : Af →ₐ[K] Āf).toLinearMap hπff
  haveI := finite_algHom K Af
  haveI := finite_algHom K Āf
  obtain ⟨-, -, hP2⟩ := HopfAlgebra.toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique πff hπff (AlgebraicClosure K)
  symm
  refine natCard_eq_mul_of_fibre
    (fun ψ : Af →ₐ[K] AlgebraicClosure K => ψ.comp (HopfAlgebra.hopfKer πff).val)
    (HopfAlgebra.exists_algHom_comp_hopfKer_val_eq_of_surjective_of_isAlgClosed πff hπff (AlgebraicClosure K))
    (fun ψ χ => WithConv.ofConv (WithConv.toConv ψ * WithConv.toConv (χ.comp (πff : Af →ₐ[K] Āf)))) ?_ ?_
  · intro ψ ψ'
    have hiff := hP2 (WithConv.toConv ψ) (WithConv.toConv ψ')
    rw [hiff]
    constructor
    · rintro ⟨χ, hχ, -⟩
      refine ⟨χ, ?_⟩
      show ψ' = WithConv.ofConv (WithConv.toConv ψ * WithConv.toConv (χ.comp (πff : Af →ₐ[K] Āf)))
      rw [← hχ]
    · rintro ⟨χ, hχ⟩
      refine ⟨χ, ?_, ?_⟩
      · rw [hχ]
      · intro χ' hχ'
        have hχ2 : WithConv.toConv ψ' = WithConv.toConv ψ * WithConv.toConv (χ.comp (πff : Af →ₐ[K] Āf)) := by
          rw [hχ]
        have hcancel := mul_right_injective_point (K := K) (WithConv.toConv ψ) (hχ'.symm.trans hχ2)
        exact comp_injective_of_surjective (πff : Af →ₐ[K] Āf) hπff (WithConv.toConv_injective hcancel)
  · intro ψ χ₁ χ₂ h
    have h' := congrArg WithConv.toConv h
    simp only [WithConv.toConv_ofConv] at h'
    have hcancel := mul_right_injective_point (K := K) (WithConv.toConv ψ) h'
    exact comp_injective_of_surjective (πff : Af →ₐ[K] Āf) hπff (WithConv.toConv_injective hcancel)

theorem natCard_subtype_ne_zero
    (K : Type) [Field K] [CharZero K]
    (A : Type) [CommRing A] [HopfAlgebra K A] [Module.Finite K A]
    (Ā : Type) [CommRing Ā] [HopfAlgebra K Ā] (π : A →ₐc[K] Ā) (hπ : Function.Surjective π) (e : A)
    (Āf : Type) [CommRing Āf] [HopfAlgebra K Āf] (πf' : Ā →ₐc[K] Āf) (hπf' : Function.Surjective πf')
    (hD1' : ∀ χ : Ā →ₐ[K] AlgebraicClosure K, χ (π e) = 1 →
      ∃! ψ : Āf →ₐ[K] AlgebraicClosure K, ψ.comp (πf' : Ā →ₐ[K] Āf) = χ)
    (hD1e' : ∀ ψ : Āf →ₐ[K] AlgebraicClosure K, (ψ.comp (πf' : Ā →ₐ[K] Āf)) (π e) = 1) :
    Nat.card {χ : Ā →ₐ[K] AlgebraicClosure K // χ (π e) = 1} ≠ 0 := by
  classical
  haveI : Module.Finite K Ā := Module.Finite.of_surjective (π : A →ₐ[K] Ā).toLinearMap hπ
  haveI : Module.Finite K Āf := Module.Finite.of_surjective (πf' : Ā →ₐ[K] Āf).toLinearMap hπf'
  haveI := finite_algHom K Ā

  have hbij : Nat.card {χ : Ā →ₐ[K] AlgebraicClosure K // χ (π e) = 1} =
      Nat.card (Āf →ₐ[K] AlgebraicClosure K) := by
    refine Nat.card_eq_of_bijective
      (fun χ => (hD1' χ.1 χ.2).choose) ⟨?_, ?_⟩
    · intro χ χ' h
      apply Subtype.ext
      have h1 := (hD1' χ.1 χ.2).choose_spec.1
      have h2 := (hD1' χ'.1 χ'.2).choose_spec.1
      rw [← h1, ← h2]
      exact congrArg (fun ψ : Āf →ₐ[K] AlgebraicClosure K => ψ.comp (πf' : Ā →ₐ[K] Āf)) h
    · intro ψ
      refine ⟨⟨ψ.comp (πf' : Ā →ₐ[K] Āf), hD1e' ψ⟩, ?_⟩
      exact ((hD1' _ (hD1e' ψ)).choose_spec.2 ψ rfl).symm
  rw [hbij]
  exact natCard_algHom_ne_zero K Āf

theorem natCard_le_natCard_map_hopfKer_mul
    (K : Type) [Field K] [CharZero K]
    (A : Type) [CommRing A] [HopfAlgebra K A] [Module.Finite K A] [Coalgebra.IsCocomm K A]
    (Ā : Type) [CommRing Ā] [HopfAlgebra K Ā] (π : A →ₐc[K] Ā) (hπ : Function.Surjective π)
    (e : A)
    (Af : Type) [CommRing Af] [HopfAlgebra K Af] (πf : A →ₐc[K] Af) (hπf : Function.Surjective πf)
    (Āf : Type) [CommRing Āf] [HopfAlgebra K Āf] (πf' : Ā →ₐc[K] Āf) (hπf' : Function.Surjective πf')
    (hD1e : ∀ ψ : Af →ₐ[K] AlgebraicClosure K, (ψ.comp (πf : A →ₐ[K] Af)) e = 1)
    (hD1' : ∀ χ : Ā →ₐ[K] AlgebraicClosure K, χ (π e) = 1 →
      ∃! ψ : Āf →ₐ[K] AlgebraicClosure K, ψ.comp (πf' : Ā →ₐ[K] Āf) = χ)
    (hD3 : ∀ ν w : WithConv (A →ₐ[K] AlgebraicClosure K), (WithConv.ofConv ν) e = 1 →
      ((WithConv.ofConv (ν * w)) e = 1 ↔ (WithConv.ofConv w) e = 1)) :
    Nat.card (Af →ₐ[K] AlgebraicClosure K) ≤
      Nat.card (↥((HopfAlgebra.hopfKer π).map (πf : A →ₐ[K] Af)) →ₐ[K] AlgebraicClosure K) *
        Nat.card (Āf →ₐ[K] AlgebraicClosure K) := by
  classical
  haveI : Module.Finite K Ā := Module.Finite.of_surjective (π : A →ₐ[K] Ā).toLinearMap hπ
  haveI : Module.Finite K Af := Module.Finite.of_surjective (πf : A →ₐ[K] Af).toLinearMap hπf
  haveI : Module.Finite K Āf := Module.Finite.of_surjective (πf' : Ā →ₐ[K] Āf).toLinearMap hπf'
  haveI : Module.Flat K A := inferInstance
  haveI := finite_algHom K Af
  haveI := finite_algHom K Āf
  set C : Subalgebra K Af := (HopfAlgebra.hopfKer π).map (πf : A →ₐ[K] Af) with hC

  let res : (Af →ₐ[K] AlgebraicClosure K) → (↥C →ₐ[K] AlgebraicClosure K) := fun ψ => ψ.comp C.val
  haveI : Finite (↥C →ₐ[K] AlgebraicClosure K) :=
    Finite.of_surjective res (fun φ => Subalgebra.exists_algHom_comp_val_eq_of_isAlgClosed C (AlgebraicClosure K) φ)
  obtain ⟨-, -, hP2⟩ := HopfAlgebra.toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique π hπ (AlgebraicClosure K)

  have hpull : ∀ ψ ψ' : Af →ₐ[K] AlgebraicClosure K, res ψ' = res ψ →
      (ψ.comp (πf : A →ₐ[K] Af)).comp (HopfAlgebra.hopfKer π).val =
        (ψ'.comp (πf : A →ₐ[K] Af)).comp (HopfAlgebra.hopfKer π).val := by
    intro ψ ψ' h
    apply AlgHom.ext
    intro b
    have hb : (πf : A →ₐ[K] Af) b ∈ C := Subalgebra.mem_map.mpr ⟨b, b.2, rfl⟩
    have := DFunLike.congr_fun h ⟨_, hb⟩
    exact this.symm

  have hχex : ∀ ψ ψ' : Af →ₐ[K] AlgebraicClosure K, res ψ' = res ψ →
      ∃! χ : Ā →ₐ[K] AlgebraicClosure K, WithConv.toConv (ψ'.comp (πf : A →ₐ[K] Af)) =
        WithConv.toConv (ψ.comp (πf : A →ₐ[K] Af)) * WithConv.toConv (χ.comp (π : A →ₐ[K] Ā)) := by
    intro ψ ψ' h
    have := (hP2 (WithConv.toConv (ψ.comp (πf : A →ₐ[K] Af))) (WithConv.toConv (ψ'.comp (πf : A →ₐ[K] Af)))).mp
    exact this (hpull ψ ψ' h)
  have hχe : ∀ ψ ψ' : Af →ₐ[K] AlgebraicClosure K, ∀ h : res ψ' = res ψ,
      (hχex ψ ψ' h).choose (π e) = 1 := by
    intro ψ ψ' h
    have hspec := (hχex ψ ψ' h).choose_spec.1
    have h3 := (hD3 (WithConv.toConv (ψ.comp (πf : A →ₐ[K] Af)))
      (WithConv.toConv (((hχex ψ ψ' h).choose).comp (π : A →ₐ[K] Ā))) (by simpa using hD1e ψ)).mp
    have := h3 (by rw [← hspec]; simpa using hD1e ψ')
    simpa using this
  refine natCard_le_mul_of_fibre res
    (fun ψ ψ' => (hD1' ((hχex ψ ψ'.1 ψ'.2).choose) (hχe ψ ψ'.1 ψ'.2)).choose) ?_
  intro ψ ψ'₁ ψ'₂ h12

  apply Subtype.ext
  have hl1 := (hD1' ((hχex ψ ψ'₁.1 ψ'₁.2).choose) (hχe ψ ψ'₁.1 ψ'₁.2)).choose_spec.1
  have hl2 := (hD1' ((hχex ψ ψ'₂.1 ψ'₂.2).choose) (hχe ψ ψ'₂.1 ψ'₂.2)).choose_spec.1
  have hχeq : (hχex ψ ψ'₁.1 ψ'₁.2).choose = (hχex ψ ψ'₂.1 ψ'₂.2).choose := by
    rw [← hl1, ← hl2]
    exact congrArg (fun φ : Āf →ₐ[K] AlgebraicClosure K => φ.comp (πf' : Ā →ₐ[K] Āf)) h12
  have hs1 := (hχex ψ ψ'₁.1 ψ'₁.2).choose_spec.1
  have hs2 := (hχex ψ ψ'₂.1 ψ'₂.2).choose_spec.1
  rw [hχeq] at hs1
  have hcomp : WithConv.toConv (ψ'₁.1.comp (πf : A →ₐ[K] Af)) = WithConv.toConv (ψ'₂.1.comp (πf : A →ₐ[K] Af)) :=
    hs1.trans hs2.symm
  exact comp_injective_of_surjective (πf : A →ₐ[K] Af) hπf (WithConv.toConv_injective hcomp)

end HopfAlgebra.FC

open HopfAlgebra.FC in
theorem solution
    (K : Type) [Field K] [CharZero K]
    (A : Type) [CommRing A] [HopfAlgebra K A] [Module.Finite K A] [Coalgebra.IsCocomm K A]
    (Ā : Type) [CommRing Ā] [HopfAlgebra K Ā] (π : A →ₐc[K] Ā) (hπ : Function.Surjective π)
    (e : A) (he : IsIdempotentElem e)
    (hΔe : Coalgebra.comul (R := K) e * (e ⊗ₜ[K] (1 : A)) = e ⊗ₜ[K] e)
    (hεe : Coalgebra.counit (R := K) e = 1)
    (f : A) (hf : IsIdempotentElem f) (hfK : f ∈ HopfAlgebra.hopfKer π) (hfe : f * e = e)
    (hmin : ∀ b ∈ HopfAlgebra.hopfKer π, b * e = 0 → b * f = 0)
    (Af : Type) [CommRing Af] [HopfAlgebra K Af] (πf : A →ₐc[K] Af) (hπf : Function.Surjective πf)
    (hkerf : RingHom.ker (πf : A →ₐ[K] Af) = Ideal.span {1 - e})
    (Āf : Type) [CommRing Āf] [HopfAlgebra K Āf] (πf' : Ā →ₐc[K] Āf) (hπf' : Function.Surjective πf')
    (hkerf' : RingHom.ker (πf' : Ā →ₐ[K] Āf) = Ideal.span {1 - π e})
    (πff : Af →ₐc[K] Āf) (hcomm : ∀ x : A, πff (πf x) = πf' (π x)) :
    (HopfAlgebra.hopfKer π).map (πf : A →ₐ[K] Af) = HopfAlgebra.hopfKer πff := by
  classical

  haveI : Module.Finite K Af := Module.Finite.of_surjective (πf : A →ₐ[K] Af).toLinearMap hπf
  haveI : Module.Finite K Ā := Module.Finite.of_surjective (π : A →ₐ[K] Ā).toLinearMap hπ
  haveI : Module.Finite K Āf := Module.Finite.of_surjective (πf' : Ā →ₐ[K] Āf).toLinearMap hπf'
  haveI : Coalgebra.IsCocomm K Af := isCocomm_of_surjective K A Af πf hπf
  have hπff : Function.Surjective πff := by
    intro y
    obtain ⟨z, rfl⟩ := hπf' y
    obtain ⟨x, rfl⟩ := hπ z
    exact ⟨πf x, hcomm x⟩

  set C := (HopfAlgebra.hopfKer π).map (πf : A →ₐ[K] Af) with hC
  set Bf := HopfAlgebra.hopfKer πff with hBf
  have hle : C ≤ Bf := map_hopfKer_le_hopfKer π πf πf' πff hcomm

  have hD1e := fun (ψ : Af →ₐ[K] AlgebraicClosure K) => comp_apply_eq_one_of_ker_eq K A e Af (πf : A →ₐ[K] Af) hkerf (AlgebraicClosure K) ψ
  have hD1' := fun (χ : Ā →ₐ[K] AlgebraicClosure K) (hχ : χ (π e) = 1) =>
    existsUnique_comp_eq_of_apply_eq_one K Ā (π e) Āf (πf' : Ā →ₐ[K] Āf) hπf' hkerf' (AlgebraicClosure K) χ hχ
  have hD3 : ∀ ν w : WithConv (A →ₐ[K] AlgebraicClosure K), (WithConv.ofConv ν) e = 1 →
      ((WithConv.ofConv (ν * w)) e = 1 ↔ (WithConv.ofConv w) e = 1) := fun ν w hν => by
    rw [convMul_apply_eq_of_apply_eq_one K A e hΔe (AlgebraicClosure K) ν w hν]

  have hE1 := natCard_hopfKer_mul_natCard_eq K Af Āf πff hπff
  have hE2 := natCard_le_natCard_map_hopfKer_mul K A Ā π hπ e Af πf hπf Āf πf' hπf' hD1e hD1' hD3
  have hm : Nat.card (Āf →ₐ[K] AlgebraicClosure K) ≠ 0 := natCard_algHom_ne_zero K Āf
  have hcardle : Nat.card (↥Bf →ₐ[K] AlgebraicClosure K) ≤ Nat.card (↥C →ₐ[K] AlgebraicClosure K) := by
    apply Nat.le_of_mul_le_mul_right _ (Nat.pos_of_ne_zero hm)
    rw [hE1]
    exact hE2

  have hpts : Nat.card (Af →ₐ[K] AlgebraicClosure K) = Module.finrank K Af :=
    HopfAlgebra.natCard_algHom_eq_finrank_of_charZero K Af (AlgebraicClosure K)
  have hge : Module.finrank K ↥Bf ≤ Module.finrank K ↥C := by
    rw [finrank_subalgebra_eq_natCard_algHom K Af hpts C, finrank_subalgebra_eq_natCard_algHom K Af hpts Bf]
    exact hcardle
  have hle' : Module.finrank K ↥C ≤ Module.finrank K ↥Bf := by
    rw [← Subalgebra.finrank_toSubmodule, ← Subalgebra.finrank_toSubmodule]
    exact Submodule.finrank_mono hle

  apply Subalgebra.toSubmodule_injective
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [Subalgebra.finrank_toSubmodule, Subalgebra.finrank_toSubmodule]
  exact le_antisymm hle' hge

end S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_comul_mul_tmul_eq
end P2MW
export P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_comul_mul_tmul_eq (solution)
