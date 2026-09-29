-- Prove2me | solution 1 for Module.Projective.exists_baseChange_quotient_iso_of_squareZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/f7c12e25-1d4c-53e9-9ff1-f3393db5195b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Projective_exists_baseChange_quotient_iso_of_squareZero

universe u

set_option autoImplicit false
set_option maxHeartbeats 9600000

open TensorProduct Polynomial

theorem solution
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥)
    (P : Type u) [AddCommGroup P] [Module (R ⧸ I) P]
    [Module.Projective (R ⧸ I) P] [Module.Finite (R ⧸ I) P] :
    ∃ (P' : Type u) (_ : AddCommGroup P') (_ : Module R P'),
      Module.Projective R P' ∧ Module.Finite R P' ∧
      Nonempty (((R ⧸ I) ⊗[R] P') ≃ₗ[R ⧸ I] P) := by
  classical
  letI : Module R P := Module.compHom P (algebraMap R (R ⧸ I))
  have hPsmul : ∀ (r : R) (p : P), r • p = (Ideal.Quotient.mk I r) • p := fun r p => by
    show (algebraMap R (R⧸I) r) • p = _; rw [Ideal.Quotient.algebraMap_eq]
  letI : IsScalarTower R (R ⧸ I) P :=
    ⟨fun r c p => by
      rw [hPsmul, ← smul_assoc, smul_eq_mul, ← Ideal.Quotient.algebraMap_eq, ← Algebra.smul_def]⟩
  have hII : ∀ a ∈ I, ∀ b ∈ I, a * b = 0 := fun a ha b hb => by
    have h := Ideal.mul_mem_mul ha hb; rwa [← pow_two, hI, Ideal.mem_bot] at h
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (R ⧸ I) P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hfs : ∀ p, f (s p) = p := fun p => LinearMap.congr_fun hs p
  let e : Module.End (R⧸I) (Fin n → R⧸I) := s ∘ₗ f
  have he_idem : e * e = e := LinearMap.ext fun v => by
    show s (f (s (f v))) = s (f v); rw [hfs]
  have hesp : ∀ p, e (s p) = s p := fun p => by
    show s (f (s p)) = s p; rw [hfs]
  let q : (Fin n → R) →ₗ[R] (Fin n → R⧸I) :=
    LinearMap.pi fun i => (Algebra.linearMap R (R⧸I)).comp (LinearMap.proj i)
  have hq_apply : ∀ (v : Fin n → R) i, q v i = Ideal.Quotient.mk I (v i) := fun v i => by
    simp only [q, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Algebra.linearMap_apply, Ideal.Quotient.algebraMap_eq]
  have hq_surj : Function.Surjective q := fun w => by
    choose g hg using fun i => Ideal.Quotient.mk_surjective (w i)
    exact ⟨g, funext fun i => (hq_apply g i).trans (hg i)⟩
  have hq_ker : ∀ v, q v = 0 ↔ ∀ i, v i ∈ I := fun v => by
    simp only [funext_iff, hq_apply, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨e', he'⟩ :=
    Module.projective_lifting_property q ((e.restrictScalars R).comp q) hq_surj
  have he'_reduce : ∀ v, q (e' v) = e (q v) := fun v => LinearMap.congr_fun he' v
  let η : Module.End R (Fin n → R) := e' * e' - e'
  have hη_ker : ∀ v, q (η v) = 0 := fun v => by
    have : q (e' (e' v)) - q (e' v) = 0 := by
      rw [he'_reduce, he'_reduce, ← Module.End.mul_apply, he_idem, sub_self]
    simpa only [η, Module.End.mul_apply, LinearMap.sub_apply, map_sub] using this
  have hη_I : ∀ v i, η v i ∈ I := fun v i => (hq_ker _).mp (hη_ker v) i
  have hbasis : ∀ (w : Fin n → R), w = ∑ j, (w j) • Pi.single j (1 : R) := fun w => by
    ext k; simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  have hηη : η * η = 0 := LinearMap.ext fun v => funext fun i => by
    simp only [Module.End.mul_apply, LinearMap.zero_apply, Pi.zero_apply]
    conv_lhs => rw [hbasis (η v), map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_eq_zero fun j _ => hII (η v j) (hη_I v j) _ (hη_I _ i)
  let e'' : Module.End R (Fin n → R) := 3 • (e' * e') - 2 • (e' * e' * e')
  have he''_reduce : ∀ v, q (e'' v) = e (q v) := fun v => by
    have h1 : q (e' (e' v)) = e (q v) := by
      rw [he'_reduce, he'_reduce, ← Module.End.mul_apply, he_idem]
    have h2 : q (e' (e' (e' v))) = e (q v) := by
      rw [he'_reduce, he'_reduce, he'_reduce, ← Module.End.mul_apply,
        ← Module.End.mul_apply, he_idem, he_idem]
    simp only [e'', LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
      map_sub, map_nsmul, h1, h2]
    abel
  have he''_idem : e'' * e'' = e'' := by
    have hφe'' : aeval (R := R) e' (3 * X^2 - 2 * X^3 : R[X]) = e'' := by
      rw [map_sub, map_mul, map_mul, map_pow, map_pow, aeval_X, map_ofNat, map_ofNat,
        show (3 : Module.End R (Fin n → R)) = ((3:ℕ) : Module.End R (Fin n → R)) from by norm_cast,
        show (2 : Module.End R (Fin n → R)) = ((2:ℕ) : Module.End R (Fin n → R)) from by norm_cast,
        ← nsmul_eq_mul, ← nsmul_eq_mul, sq, pow_succ, sq]
    have hφη : aeval (R := R) e' (X^2 - X : R[X]) = η := by
      rw [map_sub, map_pow, aeval_X, sq]
    have hpoly : ((3*X^2 - 2*X^3 : R[X])^2 - (3*X^2 - 2*X^3))
        = (X^2 - X)^2 * (4*X^2 - 4*X - 3) := by ring
    have key := congrArg (aeval (R := R) e') hpoly
    rw [map_sub, map_pow, map_mul, map_pow, hφe'', hφη,
      show e''^2 = e''*e'' from sq e'',
      show η^2 = η*η from sq η, hηη, zero_mul, sub_eq_zero] at key
    exact key
  have he''_fix : ∀ v ∈ LinearMap.range e'', e'' v = v := fun v ⟨y, hy⟩ => by
    rw [← hy, ← Module.End.mul_apply, he''_idem]
  refine ⟨LinearMap.range e'', inferInstance, inferInstance, ?_, ?_, ?_⟩
  · refine Module.Projective.of_split (LinearMap.range e'').subtype e''.rangeRestrict ?_
    exact LinearMap.ext fun p' => Subtype.ext (he''_fix p'.val p'.property)
  · exact Module.Finite.range e''
  · set P' : Submodule R (Fin n → R) := LinearMap.range e''
    let α : P' →ₗ[R] P := (f.restrictScalars R) ∘ₗ q ∘ₗ P'.subtype
    have hα_app : ∀ p' : P', α p' = f (q p'.val) := fun _ => rfl
    have hα_surj : Function.Surjective α := fun p => by
      obtain ⟨v, hv⟩ := hq_surj (s p)
      exact ⟨⟨e'' v, LinearMap.mem_range_self _ _⟩, by
        rw [hα_app, he''_reduce, hv, hesp, hfs]⟩
    have hα_ker : LinearMap.ker α = I • (⊤ : Submodule R P') := by
      ext p'
      simp only [LinearMap.mem_ker, hα_app]
      constructor
      · intro hp'
        have hqr : q p'.val ∈ LinearMap.range e := by
          obtain ⟨y, hy⟩ := p'.property; exact ⟨q y, by rw [← hy, he''_reduce]⟩
        obtain ⟨w, hw⟩ := hqr
        have hfw : f w = 0 := by
          have : f (s (f w)) = 0 := by change f (e w) = 0; rw [hw]; exact hp'
          rwa [hfs] at this
        have hq0 : q p'.val = 0 := by rw [← hw]; show s (f w) = 0; rw [hfw, map_zero]
        have hcoord : ∀ i, p'.val i ∈ I := (hq_ker _).mp hq0
        rw [Submodule.mem_smul_top_iff]
        show (p' : Fin n → R) ∈ I • P'
        rw [← he''_fix p'.val p'.property, hbasis p'.val, map_sum]
        simp only [map_smul]
        exact Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem_smul (hcoord i) (LinearMap.mem_range_self _ _)
      · intro hp'
        refine Submodule.smul_induction_on hp' (fun a ha w _ => ?_)
          (fun x y hx hy => by
            show f (q ((x : Fin n → R) + (y : Fin n → R))) = 0
            rw [map_add, map_add, hx, hy, add_zero])
        show f (q (a • (↑w : Fin n → R))) = 0
        have hq0 : q (a • (↑w : Fin n → R)) = 0 := funext fun i => by
          simp only [hq_apply, Pi.smul_apply, smul_eq_mul, map_mul, Pi.zero_apply]
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul]
        rw [hq0, map_zero]
    let ψ₁ : (R ⧸ I) ⊗[R] P' ≃ₗ[R] P' ⧸ (I • (⊤:Submodule R P')) := quotTensorEquivQuotSMul P' I
    let ψ₂ : (P' ⧸ (I • (⊤:Submodule R P'))) ≃ₗ[R] P :=
      (Submodule.quotEquivOfEq _ _ hα_ker.symm).trans
        (LinearMap.quotKerEquivOfSurjective α hα_surj)
    let ψ : (R ⧸ I) ⊗[R] P' ≃ₗ[R] P := ψ₁.trans ψ₂
    refine ⟨⟨⟨⟨ψ, ψ.map_add⟩, ?_⟩, ψ.symm, ψ.left_inv, ψ.right_inv⟩⟩
    intro c z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    simp only [RingHom.id_apply]
    rw [← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul, ψ.map_smul,
      ← IsScalarTower.algebraMap_smul (R⧸I) r (ψ z)]

end S_Module_Projective_exists_baseChange_quotient_iso_of_squareZero
end P2MW
export P2MW.S_Module_Projective_exists_baseChange_quotient_iso_of_squareZero (solution)
