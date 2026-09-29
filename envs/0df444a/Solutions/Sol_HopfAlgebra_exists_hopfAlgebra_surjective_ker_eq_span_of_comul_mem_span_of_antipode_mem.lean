-- Prove2me | solution 1 for HopfAlgebra.exists_hopfAlgebra_surjective_ker_eq_span_of_comul_mem_span_of_antipode_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/6c3ce8f4-98f2-591f-943a-941555b42e75

import Mathlib
import Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_hopfAlgebra_surjective_ker_eq_span_of_comul_mem_span_of_antipode_mem

set_option autoImplicit false

open scoped TensorProduct

universe u v w

namespace TakQ
variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]

noncomputable def S : H →ₐ[k] H :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode k (A := H)) HopfAlgebra.antipode_one
    (fun a b => by rw [HopfAlgebra.antipode_mul, mul_comm])

theorem S_apply (a : H) : S (k := k) a = HopfAlgebra.antipode k a := rfl

section
variable {A : Type w} [CommRing A] [Algebra k A]

theorem comp_S_mul_self (x : H →ₐ[k] A) :
    WithConv.toConv (x.comp (S (k := k))) * WithConv.toConv x = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro c
  rw [AlgHom.convMul_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv, AlgHom.convOne_apply]
  have h : ∀ t : H ⊗[k] H, Algebra.TensorProduct.lift (x.comp S) x (fun _ _ => Commute.all _ _) t
      = x (LinearMap.mul' k H (LinearMap.rTensor H (HopfAlgebra.antipode k (A := H)) t)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Algebra.TensorProduct.lift_tmul, LinearMap.rTensor_tmul, S_apply]
    | add y z hy hz => rw [map_add, hy, hz, map_add, map_add, map_add]
  rw [h, HopfAlgebra.mul_antipode_rTensor_comul_apply, AlgHom.commutes]

theorem mul_comp_S_self (x : H →ₐ[k] A) :
    WithConv.toConv x * WithConv.toConv (x.comp (S (k := k))) = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro c
  rw [AlgHom.convMul_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv, AlgHom.convOne_apply]
  have h : ∀ t : H ⊗[k] H, Algebra.TensorProduct.lift x (x.comp S) (fun _ _ => Commute.all _ _) t
      = x (LinearMap.mul' k H (LinearMap.lTensor H (HopfAlgebra.antipode k (A := H)) t)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Algebra.TensorProduct.lift_tmul, LinearMap.lTensor_tmul, S_apply]
    | add y z hy hz => rw [map_add, hy, hz, map_add, map_add, map_add]
  rw [h, HopfAlgebra.mul_antipode_lTensor_comul_apply, AlgHom.commutes]
end

noncomputable def ee : H ⊗[k] H →ₗ[k] k :=
  (TensorProduct.lid k k).toLinearMap ∘ₗ
    TensorProduct.map (Coalgebra.counit (R := k) (A := H)) (Coalgebra.counit (R := k) (A := H))

theorem ee_tmul (a b : H) : ee (k := k) (a ⊗ₜ[k] b) = Coalgebra.counit (R := k) a * Coalgebra.counit (R := k) b := by
  simp [ee]

theorem ee_comul (a : H) : ee (k := k) (Coalgebra.comul (R := k) a) = Coalgebra.counit (R := k) a := by
  have h1 : TensorProduct.map (Coalgebra.counit (R := k) (A := H)) (Coalgebra.counit (R := k) (A := H))
      (Coalgebra.comul (R := k) a) = (1 : k) ⊗ₜ[k] Coalgebra.counit (R := k) a := by
    rw [← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul,
      LinearMap.lTensor_tmul]
  simp [ee, h1]

theorem map_eq_of_mem_span (K' : Subalgebra k H) {B : Type w} [CommRing B] [Algebra k B] (φ : H →ₐ[k] B)
    (hφ : ∀ x ∈ K', φ x = algebraMap k B (Coalgebra.counit (R := k) x))
    {t : H ⊗[k] H} (ht : t ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K', ∃ b ∈ K', t = a ⊗ₜ[k] b}) :
    Algebra.TensorProduct.map φ φ t = ee (k := k) t • (1 : B ⊗[k] B) := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      rw [Algebra.TensorProduct.map_tmul, hφ a ha, hφ b hb, ee_tmul, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
        smul_smul, mul_comm, Algebra.TensorProduct.one_def]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, map_add, add_smul]
  | smul c x _ hx => rw [map_smul, hx, map_smul, smul_eq_mul, mul_smul]

end TakQ

theorem solution
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (K' : Subalgebra k H)
    (hΔ' : ∀ x ∈ K', Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K', ∃ b ∈ K', t = a ⊗ₜ[k] b})
    (hS' : ∀ x ∈ K', HopfAlgebra.antipode k x ∈ K') :
    ∃ (Hb : Type v) (_ : CommRing Hb) (_ : HopfAlgebra k Hb) (π : H →ₐc[k] Hb),
      Function.Surjective π ∧
      RingHom.ker (π : H →+* Hb) = Ideal.span {x : H | x ∈ K' ∧ Coalgebra.counit (R := k) x = 0} ∧
      (∀ x : H, Coalgebra.counit (R := k) (π x) = Coalgebra.counit (R := k) x) ∧
      (∀ x : H, π (HopfAlgebra.antipode k x) = HopfAlgebra.antipode k (π x)) ∧
      ∀ (K : Subalgebra k H),
        (∀ x ∈ K, Coalgebra.comul (R := k) x ∈
          Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b}) →
        (∀ x ∈ K, HopfAlgebra.antipode k x ∈ K) →
        (∀ y ∈ K.map (π : H →ₐ[k] Hb), Coalgebra.comul (R := k) y ∈
          Submodule.span k {t : Hb ⊗[k] Hb |
            ∃ a ∈ K.map (π : H →ₐ[k] Hb), ∃ b ∈ K.map (π : H →ₐ[k] Hb), t = a ⊗ₜ[k] b}) ∧
        (∀ y ∈ K.map (π : H →ₐ[k] Hb), HopfAlgebra.antipode k y ∈ K.map (π : H →ₐ[k] Hb)) := by
  classical
  set J : Ideal H := Ideal.span {x : H | x ∈ K' ∧ Coalgebra.counit (R := k) x = 0} with hJ
  let mk : H →ₐ[k] H ⧸ J := Ideal.Quotient.mkₐ k J

  have hmk : ∀ x ∈ K', mk x = algebraMap k (H ⧸ J) (Coalgebra.counit (R := k) x) := by
    intro x hx
    have hmem : x - algebraMap k H (Coalgebra.counit (R := k) x) ∈ J :=
      Ideal.subset_span ⟨K'.sub_mem hx (K'.algebraMap_mem _), by simp [Bialgebra.counit_algebraMap]⟩
    have h0 : mk (x - algebraMap k H (Coalgebra.counit (R := k) x)) = 0 := by
      show Ideal.Quotient.mkₐ k J _ = 0
      rw [Ideal.Quotient.mkₐ_eq_mk]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [map_sub, sub_eq_zero, AlgHom.commutes] at h0
    exact h0

  have hcomul : ∀ a ∈ J, Algebra.TensorProduct.map mk mk (Coalgebra.comul (R := k) a) = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨hxK, hxε⟩ := hx
        rw [TakQ.map_eq_of_mem_span K' mk hmk (hΔ' x hxK), TakQ.ee_comul, hxε, zero_smul]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]
    | smul r x _ hx => rw [smul_eq_mul, Bialgebra.comul_mul, map_mul, hx, mul_zero]

  have hcounit : ∀ a ∈ J, Coalgebra.counit (R := k) a = 0 := by
    have hle : J ≤ RingHom.ker (Bialgebra.counitAlgHom k H) :=
      Ideal.span_le.mpr (fun x hx => by
        show x ∈ RingHom.ker (Bialgebra.counitAlgHom k H)
        rw [RingHom.mem_ker]; exact hx.2)
    intro a ha
    have := hle ha
    rwa [RingHom.mem_ker] at this

  have hanti : ∀ a ∈ J, HopfAlgebraStruct.antipode (R := k) a ∈ J := by
    have hmap : Ideal.map (TakQ.S (k := k) (H := H)) J ≤ J := by
      rw [Ideal.map_span]
      apply Ideal.span_mono
      rintro _ ⟨x, ⟨hxK, hxε⟩, rfl⟩
      exact ⟨hS' x hxK, by rw [TakQ.S_apply, HopfAlgebra.counit_antipode, hxε]⟩
    intro a ha
    exact hmap (Ideal.mem_map_of_mem (TakQ.S (k := k) (H := H)) ha)

  obtain ⟨Hb, _, _, π, hπ, hker, -, -, -⟩ :=
    HopfAlgebra.exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal J hcomul hcounit hanti

  have hε : ∀ x : H, Coalgebra.counit (R := k) (π x) = Coalgebra.counit (R := k) x :=
    fun x => CoalgHomClass.counit_comp_apply π x

  have hSπ : ∀ x : H, π (HopfAlgebra.antipode k x) = HopfAlgebra.antipode k (π x) := by
    let p : H →ₐ[k] Hb := (π : H →ₐ[k] Hb)
    have h1 : WithConv.toConv (p.comp (TakQ.S (k := k))) * WithConv.toConv p = 1 := TakQ.comp_S_mul_self p
    have h2 : WithConv.toConv p * WithConv.toConv ((TakQ.S (k := k)).comp p) = 1 := by

      have e := AlgHom.convMul_comp_bialgHom_distrib (WithConv.toConv (AlgHom.id k Hb))
        (WithConv.toConv (TakQ.S (k := k) (H := Hb))) π
      have hid : WithConv.toConv (AlgHom.id k Hb) * WithConv.toConv (TakQ.S (k := k) (H := Hb)) = 1 := by
        simpa [AlgHom.id_comp] using TakQ.mul_comp_S_self (k := k) (AlgHom.id k Hb)
      rw [hid] at e
      simp only [WithConv.ofConv_toConv, AlgHom.id_comp] at e

      have e1 : (WithConv.ofConv (1 : WithConv (Hb →ₐ[k] Hb))).comp (π : H →ₐ[k] Hb)
          = WithConv.ofConv (1 : WithConv (H →ₐ[k] Hb)) := by
        apply AlgHom.ext
        intro x
        rw [AlgHom.comp_apply, AlgHom.convOne_apply, AlgHom.convOne_apply]
        exact congrArg _ (hε x)
      rw [e1] at e
      exact (WithConv.ofConv_injective e).symm
    have h3 : WithConv.toConv (p.comp (TakQ.S (k := k))) = WithConv.toConv ((TakQ.S (k := k)).comp p) := by
      calc WithConv.toConv (p.comp (TakQ.S (k := k)))
          = WithConv.toConv (p.comp TakQ.S) * (WithConv.toConv p * WithConv.toConv (TakQ.S.comp p)) := by
            rw [h2, mul_one]
        _ = (WithConv.toConv (p.comp TakQ.S) * WithConv.toConv p) * WithConv.toConv (TakQ.S.comp p) := by
            rw [mul_assoc]
        _ = WithConv.toConv ((TakQ.S (k := k)).comp p) := by rw [h1, one_mul]
    intro x
    have := congrArg (fun f : WithConv (H →ₐ[k] Hb) => WithConv.ofConv f x) h3
    simp [TakQ.S_apply] at this
    exact this
  refine ⟨Hb, inferInstance, inferInstance, π, hπ, hker, hε, hSπ, ?_⟩

  intro K hΔ hS
  constructor
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subalgebra.mem_map.mp hy
    show Coalgebra.comul (R := k) (π x) ∈ _
    rw [← CoalgHomClass.map_comp_comul_apply π x]

    have aux : ∀ t : H ⊗[k] H, t ∈ Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b} →
        TensorProduct.map ((π : H →ₐ[k] Hb) : H →ₗ[k] Hb) ((π : H →ₐ[k] Hb) : H →ₗ[k] Hb) t ∈
          Submodule.span k {t : Hb ⊗[k] Hb |
            ∃ a ∈ K.map (π : H →ₐ[k] Hb), ∃ b ∈ K.map (π : H →ₐ[k] Hb), t = a ⊗ₜ[k] b} := by
      intro t ht
      induction ht using Submodule.span_induction with
      | mem t ht =>
          obtain ⟨a, ha, b, hb, rfl⟩ := ht
          rw [TensorProduct.map_tmul]
          exact Submodule.subset_span ⟨π a, Subalgebra.mem_map.mpr ⟨a, ha, rfl⟩, π b,
            Subalgebra.mem_map.mpr ⟨b, hb, rfl⟩, rfl⟩
      | zero => simp
      | add s t _ _ hs ht => rw [map_add]; exact Submodule.add_mem _ hs ht
      | smul c t _ ht => rw [map_smul]; exact Submodule.smul_mem _ c ht
    exact aux _ (hΔ x hx)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subalgebra.mem_map.mp hy
    show HopfAlgebra.antipode k (π x) ∈ _
    rw [← hSπ]
    exact Subalgebra.mem_map.mpr ⟨_, hS x hx, rfl⟩

end S_HopfAlgebra_exists_hopfAlgebra_surjective_ker_eq_span_of_comul_mem_span_of_antipode_mem
end P2MW
export P2MW.S_HopfAlgebra_exists_hopfAlgebra_surjective_ker_eq_span_of_comul_mem_span_of_antipode_mem (solution)
