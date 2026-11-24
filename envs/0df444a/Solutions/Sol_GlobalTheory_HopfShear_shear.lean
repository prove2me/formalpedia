-- Prove2me | solution 1 for GlobalTheory.HopfShear.shear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:55:11.695484+00:00
-- url     : https://prove2.me/submissions/c2b4e305-865a-4c88-b6ea-8ed8438f3e1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PointsGroup
import Theorems.Thm_GlobalTheory_HopfShear_pre_apply
import Theorems.Thm_GlobalTheory_HopfShear_conv_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct WithConv
open GlobalTheory GlobalTheory.HopfShear
variable {R A B X Y : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing X] [CommRing Y]
  [HopfAlgebra R A] [HopfAlgebra R B] [Algebra R X] [Algebra R Y]
attribute [local instance] pointsGroup
namespace GlobalTheory.HopfShear
theorem _root_.solution (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [HopfAlgebra R A]
    [HopfAlgebra R B] (f : B →ₐc[R] A) :
    Nonempty ((TensorProduct (AlgHom.range (f : B →ₐ[R] A)) A A) ≃ₗ[A]
      TensorProduct R A (A ⧸ Ideal.map (f : B →ₐ[R] A)
        (RingHom.ker (Bialgebra.counitAlgHom R B)))) := by
  set S := AlgHom.range (f : B →ₐ[R] A) with hS
  set I : Ideal A := Ideal.map (f : B →ₐ[R] A) (RingHom.ker (Bialgebra.counitAlgHom R B)) with hI
  let l : WithConv (A →ₐ[R] A ⊗[S] A) := toConv (IsScalarTower.toAlgHom R A (A ⊗[S] A))
  let r : WithConv (A →ₐ[R] A ⊗[S] A) :=
    toConv ((Algebra.TensorProduct.includeRight : A →ₐ[S] A ⊗[S] A).restrictScalars R)
  let l' : WithConv (A →ₐ[R] A ⊗[R] (A ⧸ I)) := toConv (IsScalarTower.toAlgHom R A _)
  let p : WithConv (A →ₐ[R] A ⊗[R] (A ⧸ I)) :=
    toConv ((Algebra.TensorProduct.includeRight : (A ⧸ I) →ₐ[R] A ⊗[R] (A ⧸ I)).comp
      (Ideal.Quotient.mkₐ R I))
  have hl : ∀ a, l.ofConv a = a ⊗ₜ 1 := fun a => rfl
  have hr : ∀ a, r.ofConv a = 1 ⊗ₜ a := fun a => rfl
  have hl' : ∀ a, l'.ofConv a = a ⊗ₜ 1 := fun a => rfl
  have hp : ∀ a, p.ofConv a = 1 ⊗ₜ Ideal.Quotient.mk I a := fun a => rfl
  have hlr : pre f l = pre f r := conv_ext fun b => by
    rw [pre_apply, pre_apply, hl, hr]
    have := TensorProduct.smul_tmul (R := S) (⟨f b, ⟨b, rfl⟩⟩ : S) (1 : A) (1 : A)
    simpa [Subalgebra.smul_def] using this
  have hpf : pre f p = 1 := conv_ext fun b => by
    rw [pre_apply, hp]
    have hb : b - algebraMap R B (Coalgebra.counit b) ∈
        RingHom.ker (Bialgebra.counitAlgHom R B) := by
      simp [RingHom.mem_ker]
    have h1 : Ideal.Quotient.mk I (f b) = algebraMap R _ (Coalgebra.counit b) := by
      have h2 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem (f : B →ₐ[R] A) hb)
      rw [map_sub, map_sub, sub_eq_zero, AlgHom.commutes] at h2
      exact h2
    rw [h1]
    exact (Algebra.TensorProduct.includeRight : (A ⧸ I) →ₐ[R] A ⊗[R] (A ⧸ I)).commutes _
  let g : A →ₐ[S] A ⊗[R] (A ⧸ I) :=
    { (l' * p).ofConv.toRingHom with
      commutes' := by
        rintro ⟨_, b, rfl⟩
        have h : pre f (l' * p) = pre f l' := by rw [map_mul, hpf, mul_one]
        have h2 : (l' * p).ofConv (f b) = f b ⊗ₜ 1 := congrArg (fun x => x.ofConv b) h
        exact h2 }
  let Φ : A ⊗[S] A →ₐ[A] A ⊗[R] (A ⧸ I) :=
    Algebra.TensorProduct.lift (Algebra.ofId A _) g fun _ _ => Commute.all _ _
  have hk : ∀ a ∈ I, (l⁻¹ * r).ofConv a = 0 := by
    have h : pre f (l⁻¹ * r) = 1 := by rw [map_mul, map_inv, hlr, inv_mul_cancel]
    have : I ≤ RingHom.ker (l⁻¹ * r).ofConv := by
      rw [hI, Ideal.map_le_iff_le_comap]
      intro b hb
      have h2 : (l⁻¹ * r).ofConv (f b) = algebraMap R _ (Coalgebra.counit b) :=
        congrArg (fun x => x.ofConv b) h
      have h3 : Coalgebra.counit (R := R) b = 0 := hb
      rw [h3, map_zero] at h2
      exact h2
    exact fun a ha => this ha
  let k : (A ⧸ I) →ₐ[R] A ⊗[S] A := Ideal.Quotient.liftₐ I (l⁻¹ * r).ofConv hk
  let Ψ : A ⊗[R] (A ⧸ I) →ₐ[A] A ⊗[S] A :=
    Algebra.TensorProduct.lift (Algebra.ofId A _) k fun _ _ => Commute.all _ _
  have hΦl : post (Φ.restrictScalars R) l = l' := conv_ext fun a => Φ.commutes a
  have hΦr : post (Φ.restrictScalars R) r = l' * p := conv_ext fun a => by
    change Φ (1 ⊗ₜ a) = g a
    simp [Φ, ← Algebra.TensorProduct.one_def]
  have hΨl : post (Ψ.restrictScalars R) l' = l := conv_ext fun a => Ψ.commutes a
  have hΨp : post (Ψ.restrictScalars R) p = l⁻¹ * r := conv_ext fun a => by
    change Ψ (1 ⊗ₜ Ideal.Quotient.mk I a) = k (Ideal.Quotient.mk I a)
    simp [Ψ, ← Algebra.TensorProduct.one_def]
  have h1 : ∀ a, Φ (Ψ (p.ofConv a)) = p.ofConv a := fun a => by
    have h : post (Φ.restrictScalars R) (post (Ψ.restrictScalars R) p) = p := by
      rw [hΨp, map_mul, map_inv, hΦl, hΦr, inv_mul_cancel_left]
    exact congrArg (fun x => x.ofConv a) h
  have h2 : ∀ a, Ψ (Φ (r.ofConv a)) = r.ofConv a := fun a => by
    have h : post (Ψ.restrictScalars R) (post (Φ.restrictScalars R) r) = r := by
      rw [hΦr, map_mul, hΨl, hΨp, mul_inv_cancel_left]
    exact congrArg (fun x => x.ofConv a) h
  refine ⟨(AlgEquiv.ofAlgHom Φ Ψ ?_ ?_).toLinearEquiv⟩
  · refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun c => ?_)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact h1 a
  · exact Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun a => h2 a)
end GlobalTheory.HopfShear
