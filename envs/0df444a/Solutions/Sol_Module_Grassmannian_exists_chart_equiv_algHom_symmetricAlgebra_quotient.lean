-- Prove2me | solution 1 for Module.Grassmannian.exists_chart_equiv_algHom_symmetricAlgebra_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/907832d3-20e5-5b24-a60d-73a4a923c3c0

import Mathlib
import Theorems.Thm_Module_Grassmannian_exists_chart_equiv_linearMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Grassmannian_exists_chart_equiv_algHom_symmetricAlgebra_quotient

open scoped TensorProduct
open TensorProduct

set_option autoImplicit false

namespace GrassChartS1aSym

variable (R : Type) [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M)
variable (A : Type) [CommRing A] [Algebra R A]

def rels : Set (SymmetricAlgebra R (Fin k → M)) :=
  {a | ∃ i j : Fin k, a = SymmetricAlgebra.ι R (Fin k → M) (Pi.single i (x j)) - if i = j then 1 else 0}

abbrev S : Type := SymmetricAlgebra R (Fin k → M) ⧸ Ideal.span (rels R x)

abbrev HomX : Type :=
  {ψ : M →ₗ[R] (Fin k → A) // ∀ j, ψ (x j) = Pi.single j 1}

variable {R A}

noncomputable def theta (ψ : M →ₗ[R] (Fin k → A)) : (Fin k → M) →ₗ[R] A :=
  LinearMap.lsum R (fun _ : Fin k => M) R fun i => (LinearMap.proj i).comp ψ

lemma theta_single (ψ : M →ₗ[R] (Fin k → A)) (i : Fin k) (m : M) :
    theta ψ (Pi.single i m) = ψ m i := by
  classical
  simp only [theta, LinearMap.lsum_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_comp,
    LinearMap.coe_proj, Function.comp_apply, Function.eval]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero, Pi.zero_apply])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]

lemma lift_theta_mem (ψ : HomX R x A) (a : SymmetricAlgebra R (Fin k → M))
    (ha : a ∈ Ideal.span (rels R x)) : SymmetricAlgebra.lift (theta ψ.1) a = 0 := by
  induction ha using Submodule.span_induction with
  | mem a h =>
    obtain ⟨i, j, rfl⟩ := h
    rw [map_sub, SymmetricAlgebra.lift_ι_apply, theta_single, ψ.2 j, Pi.single_apply]
    split_ifs <;> simp
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul r a _ ha => rw [smul_eq_mul, map_mul, ha, mul_zero]

noncomputable def toPt (ψ : HomX R x A) : S R x →ₐ[R] A :=
  Ideal.Quotient.liftₐ _ (SymmetricAlgebra.lift (theta ψ.1)) (lift_theta_mem x ψ)

lemma toPt_mk_ι (ψ : HomX R x A) (w : Fin k → M) :
    toPt x ψ (Ideal.Quotient.mk _ (SymmetricAlgebra.ι R _ w)) = theta ψ.1 w := by
  simp [toPt]

lemma toPt_mk_ι_single (ψ : HomX R x A) (i : Fin k) (m : M) :
    toPt x ψ (Ideal.Quotient.mk _ (SymmetricAlgebra.ι R _ (Pi.single i m))) = ψ.1 m i := by
  rw [toPt_mk_ι, theta_single]

noncomputable def ofPt (g : S R x →ₐ[R] A) : HomX R x A := by
  classical
  refine ⟨LinearMap.pi fun i =>
      (g.comp (Ideal.Quotient.mkₐ R _)).toLinearMap ∘ₗ SymmetricAlgebra.ι R (Fin k → M) ∘ₗ
        LinearMap.single R (fun _ : Fin k => M) i, fun j => ?_⟩
  funext i
  simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    AlgHom.coe_comp, Ideal.Quotient.mkₐ_eq_mk, LinearMap.coe_single]
  have hmem : SymmetricAlgebra.ι R (Fin k → M) (Pi.single i (x j)) - (if i = j then 1 else 0) ∈
      Ideal.span (rels R x) := Ideal.subset_span ⟨i, j, rfl⟩
  have h0 : g (Ideal.Quotient.mk _ (SymmetricAlgebra.ι R (Fin k → M) (Pi.single i (x j)) -
      (if i = j then 1 else 0))) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
  rw [map_sub, map_sub, sub_eq_zero] at h0
  rw [h0, Pi.single_apply]
  split_ifs <;> simp

lemma ofPt_apply (g : S R x →ₐ[R] A) (m : M) (i : Fin k) :
    (ofPt x g).1 m i = g (Ideal.Quotient.mk _ (SymmetricAlgebra.ι R _ (Pi.single i m))) := by
  classical
  simp [ofPt]

lemma ofPt_toPt (ψ : HomX R x A) : ofPt x (toPt x ψ) = ψ := by
  apply Subtype.ext
  apply LinearMap.ext
  intro m
  funext i
  rw [ofPt_apply, toPt_mk_ι_single]

lemma toPt_ofPt (g : S R x →ₐ[R] A) : toPt x (ofPt x g) = g := by
  classical
  refine Ideal.Quotient.algHom_ext R (SymmetricAlgebra.algHom_ext ?_)
  refine LinearMap.pi_ext fun i m => ?_
  change toPt x (ofPt x g) (Ideal.Quotient.mk _ (SymmetricAlgebra.ι R _ (Pi.single i m))) =
    g (Ideal.Quotient.mk _ (SymmetricAlgebra.ι R _ (Pi.single i m)))
  rw [toPt_mk_ι, theta_single, ofPt_apply]

noncomputable def homEquivPt : HomX R x A ≃ (S R x →ₐ[R] A) where
  toFun := toPt x
  invFun := ofPt x
  left_inv := ofPt_toPt x
  right_inv := toPt_ofPt x

variable {B : Type} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)

lemma homEquivPt_natural (ψ : HomX R x A) (ψ' : HomX R x B) (h : ∀ m i, ψ'.1 m i = φ (ψ.1 m i)) :
    homEquivPt x ψ' = φ.comp (homEquivPt x ψ) := by
  classical
  refine Ideal.Quotient.algHom_ext R (SymmetricAlgebra.algHom_ext ?_)
  refine LinearMap.pi_ext fun i m => ?_
  change toPt x ψ' (Ideal.Quotient.mk _ (SymmetricAlgebra.ι R _ (Pi.single i m))) =
    φ (toPt x ψ (Ideal.Quotient.mk _ (SymmetricAlgebra.ι R _ (Pi.single i m))))
  rw [toPt_mk_ι_single, toPt_mk_ι_single, h]

end GrassChartS1aSym

open GrassChartS1aSym in
theorem solution
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ) (x : Fin k → M) :
    ∃ (J : Ideal (SymmetricAlgebra R (Fin k → M)))
      (_ : J = Ideal.span {a | ∃ i j : Fin k,
        a = SymmetricAlgebra.ι R (Fin k → M) (Pi.single i (x j)) - if i = j then 1 else 0})
      (pt : ∀ (A : Type) [CommRing A] [Algebra R A],
        {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)} ≃
          (SymmetricAlgebra R (Fin k → M) ⧸ J →ₐ[R] A)),
      (∀ (A : Type) [CommRing A] [Algebra R A]
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)})
          (m : M),
          ∑ i, pt A N (Ideal.Quotient.mk J (SymmetricAlgebra.ι R (Fin k → M) (Pi.single i m))) •
              N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i) =
            N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] m)) ∧
      (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)}),
          ∃ h : Function.Bijective fun v : Fin k → B =>
              ∑ i, v i • (Module.Grassmannian.map φ N.1).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i),
            pt B ⟨Module.Grassmannian.map φ N.1, h⟩ = φ.comp (pt A N)) := by
  obtain ⟨pt₁, hcoord, -, hnat⟩ := Module.Grassmannian.exists_chart_equiv_linearMap R M k x
  refine ⟨Ideal.span (rels R x), rfl, fun A _ _ => (pt₁ A).trans (homEquivPt (R := R) (A := A) x), ?_, ?_⟩
  · intro A _ _ N m
    have h := hcoord A N m
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h
    congr 1
    exact toPt_mk_ι_single x (pt₁ A N) i m
  · intro A B _ _ _ _ φ N
    obtain ⟨h, hφ⟩ := hnat A B φ N
    exact ⟨h, homEquivPt_natural x φ (pt₁ A N) (pt₁ B ⟨_, h⟩) hφ⟩

end S_Module_Grassmannian_exists_chart_equiv_algHom_symmetricAlgebra_quotient
end P2MW
export P2MW.S_Module_Grassmannian_exists_chart_equiv_algHom_symmetricAlgebra_quotient (solution)
