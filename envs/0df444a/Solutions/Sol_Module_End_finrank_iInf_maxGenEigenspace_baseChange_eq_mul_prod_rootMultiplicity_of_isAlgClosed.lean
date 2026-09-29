-- Prove2me | solution 1 for Module.End.finrank_iInf_maxGenEigenspace_baseChange_eq_mul_prod_rootMultiplicity_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/de441abb-660f-5c88-9b7e-8a3cae3248ef

import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_End_finrank_iInf_maxGenEigenspace_baseChange_eq_mul_prod_rootMultiplicity_of_isAlgClosed

set_option autoImplicit false

open Polynomial

namespace CESCount

open TensorProduct

section Tower

variable {K E Ω : Type} [Field K] [Field E] [Field Ω] [Algebra K E] [Algebra K Ω] [Algebra E Ω]
  [IsScalarTower K E Ω] {W : Type} [AddCommGroup W] [Module K W]

theorem cancelBaseChange_baseChange_baseChange_apply (T : Module.End K W) (x : Ω ⊗[E] (E ⊗[K] W)) :
    AlgebraTensorModule.cancelBaseChange K E Ω Ω W (((T.baseChange E).baseChange Ω) x) =
      (T.baseChange Ω) (AlgebraTensorModule.cancelBaseChange K E Ω Ω W x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul ω m =>
    induction m using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
      simp only [LinearMap.baseChange_tmul] at ha hb ⊢
      simp only [tmul_add, map_add, ha, hb]
    | tmul e w => simp [LinearMap.baseChange_tmul, AlgebraTensorModule.cancelBaseChange_tmul]

theorem finrank_iInf_ker_pow_baseChange_tower {Q : Type} [Fintype Q]
    (U : Q → Module.End K W) (μ : Q → E) (k : Q → ℕ) :
    Module.finrank Ω ↥(⨅ q, LinearMap.ker (((U q).baseChange Ω -
        algebraMap Ω (Module.End Ω (Ω ⊗[K] W)) (algebraMap E Ω (μ q))) ^ k q)) =
      Module.finrank E ↥(⨅ q, LinearMap.ker (((U q).baseChange E -
        algebraMap E (Module.End E (E ⊗[K] W)) (μ q)) ^ k q)) := by
  classical

  cases isEmpty_or_nonempty Q with
  | inl hQ =>
    rw [iInf_of_empty, iInf_of_empty, finrank_top, finrank_top, Module.finrank_baseChange,
      Module.finrank_baseChange]
  | inr hQ =>
  let g : Q → Module.End E (E ⊗[K] W) := fun q =>
    ((U q).baseChange E - algebraMap E (Module.End E (E ⊗[K] W)) (μ q)) ^ k q
  let S : Q → Module.End Ω (Ω ⊗[K] W) := fun q =>
    ((U q).baseChange Ω - algebraMap Ω (Module.End Ω (Ω ⊗[K] W)) (algebraMap E Ω (μ q))) ^ k q
  have hVE : (⨅ q, LinearMap.ker (((U q).baseChange E -
        algebraMap E (Module.End E (E ⊗[K] W)) (μ q)) ^ k q)) = LinearMap.ker (LinearMap.pi g) := by
    rw [LinearMap.ker_pi]
  have hVΩ : (⨅ q, LinearMap.ker (((U q).baseChange Ω -
        algebraMap Ω (Module.End Ω (Ω ⊗[K] W)) (algebraMap E Ω (μ q))) ^ k q)) =
      ⨅ q, LinearMap.ker (S q) := rfl

  let κ : Ω ⊗[E] (E ⊗[K] W) ≃ₗ[Ω] Ω ⊗[K] W := AlgebraTensorModule.cancelBaseChange K E Ω Ω W
  have hg1 : ∀ q, (g q).baseChange Ω =
      (((U q).baseChange E).baseChange Ω -
        algebraMap Ω (Module.End Ω (Ω ⊗[E] (E ⊗[K] W))) (algebraMap E Ω (μ q))) ^ k q := by
    intro q
    show Module.End.baseChangeHom E Ω (E ⊗[K] W) (g q) = _
    simp only [g, map_pow]
    rw [map_sub (Module.End.baseChangeHom E Ω (E ⊗[K] W)), AlgHom.commutes]
    congr 2
    · rw [IsScalarTower.algebraMap_apply E Ω (Module.End Ω (Ω ⊗[E] (E ⊗[K] W)))]
  let S' : Q → Module.End Ω (Ω ⊗[E] (E ⊗[K] W)) := fun q =>
    ((U q).baseChange E).baseChange Ω -
      algebraMap Ω (Module.End Ω (Ω ⊗[E] (E ⊗[K] W))) (algebraMap E Ω (μ q))
  let S₀ : Q → Module.End Ω (Ω ⊗[K] W) := fun q =>
    (U q).baseChange Ω - algebraMap Ω (Module.End Ω (Ω ⊗[K] W)) (algebraMap E Ω (μ q))
  have hsemi : ∀ q, Function.Semiconj κ (S' q) (S₀ q) := by
    intro q x
    show κ (S' q x) = S₀ q (κ x)
    simp only [κ, S', S₀, LinearMap.sub_apply, map_sub, Module.algebraMap_end_apply, map_smul,
      cancelBaseChange_baseChange_baseChange_apply]
  have hg : ∀ q (x : Ω ⊗[E] (E ⊗[K] W)), κ (((g q).baseChange Ω) x) = S q (κ x) := by
    intro q x
    rw [hg1]
    show κ ((S' q ^ k q) x) = (S₀ q ^ k q) (κ x)
    rw [Module.End.pow_apply, Module.End.pow_apply]
    exact (hsemi q).iterate_right (k q) x
  have hker : ∀ q, Submodule.map (κ : Ω ⊗[E] (E ⊗[K] W) →ₗ[Ω] Ω ⊗[K] W)
      (LinearMap.ker ((g q).baseChange Ω)) = LinearMap.ker (S q) := by
    intro q
    have : LinearMap.ker ((g q).baseChange Ω) =
        (LinearMap.ker (S q)).comap (κ : Ω ⊗[E] (E ⊗[K] W) →ₗ[Ω] Ω ⊗[K] W) := by
      ext x
      simp only [LinearMap.mem_ker, Submodule.mem_comap, LinearEquiv.coe_coe]
      rw [← hg, LinearEquiv.map_eq_zero_iff]
    rw [this, Submodule.map_comap_eq_of_surjective κ.surjective]

  rw [hVΩ, hVE]
  have hmap : (⨅ q, LinearMap.ker (S q)) =
      Submodule.map (κ : Ω ⊗[E] (E ⊗[K] W) →ₗ[Ω] Ω ⊗[K] W) (⨅ q, LinearMap.ker ((g q).baseChange Ω)) := by
    rw [Submodule.map_iInf _ κ.injective]
    exact iInf_congr fun q => (hker q).symm
  rw [hmap, LinearEquiv.finrank_map_eq]

  have hpi : (⨅ q, LinearMap.ker ((g q).baseChange Ω)) = LinearMap.ker ((LinearMap.pi g).baseChange Ω) := by
    have hcomp : LinearMap.pi (fun q => (g q).baseChange Ω) =
        (TensorProduct.piRight E Ω Ω (fun _ : Q => E ⊗[K] W)).toLinearMap ∘ₗ (LinearMap.pi g).baseChange Ω := by
      apply TensorProduct.AlgebraTensorModule.curry_injective
      ext ω x
      simp [LinearMap.baseChange_tmul]
    rw [← LinearMap.ker_pi, hcomp, LinearEquiv.ker_comp]
  rw [hpi]

  have e : Ω ⊗[E] ↥(LinearMap.ker (LinearMap.pi g)) ≃ₗ[Ω]
      ↥(LinearMap.ker ((LinearMap.pi g).baseChange Ω)) :=
    LinearMap.tensorKerEquiv Ω Ω (LinearMap.pi g)
  haveI : Module.Free E ↥(LinearMap.ker (LinearMap.pi g)) :=
    Module.Free.of_divisionRing E ↥(LinearMap.ker (LinearMap.pi g))
  rw [← LinearEquiv.finrank_eq e, Module.finrank_baseChange]

variable [FiniteDimensional K W]

theorem finrank_iInf_maxGenEigenspace_baseChange_tower {Q : Type} [Fintype Q]
    (U : Q → Module.End K W) (μ : Q → E) :
    Module.finrank Ω ↥(⨅ q, Module.End.maxGenEigenspace ((U q).baseChange Ω) (algebraMap E Ω (μ q))) =
      Module.finrank E ↥(⨅ q, Module.End.maxGenEigenspace ((U q).baseChange E) (μ q)) := by
  set n : ℕ := Module.finrank K W with hn
  have hmax : ∀ (L : Type) [Field L] [Algebra K L] (T : Module.End K W) (ν : L),
      Module.End.maxGenEigenspace (T.baseChange L) ν =
        LinearMap.ker ((T.baseChange L - algebraMap L (Module.End L (L ⊗[K] W)) ν) ^ n) := by
    intro L _ _ T ν
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.finrank_baseChange, ← hn,
      Module.End.genEigenspace_nat, Algebra.algebraMap_eq_smul_one]
  rw [iInf_congr (fun q => hmax Ω (U q) (algebraMap E Ω (μ q))),
    iInf_congr (fun q => hmax E (U q) (μ q))]
  exact finrank_iInf_ker_pow_baseChange_tower U μ (fun _ => n)

end Tower

end CESCount

namespace CESCount

section Transcendental

variable {K L : Type} [Field K] [Field L] [Algebra K L] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem maxGenEigenspace_baseChange_eq_bot_of_transcendental (T : Module.End K W) {ν : L}
    (hν : Transcendental K ν) : Module.End.maxGenEigenspace (T.baseChange L) ν = ⊥ := by
  by_contra h
  apply hν
  have h1 : Module.End.HasEigenvalue (T.baseChange L) ν :=
    (Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one
      (f := T.baseChange L) (μ := ν) (k := ⊤) ENat.top_pos).mp h
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, LinearMap.charpoly_baseChange] at h1
  exact ⟨T.charpoly, (LinearMap.charpoly_monic T).ne_zero, by
    rwa [Polynomial.aeval_def, ← Polynomial.eval_map]⟩

theorem rootMultiplicity_map_eq_zero_of_transcendental (p : K[X]) {ν : L} (hν : Transcendental K ν) :
    Polynomial.rootMultiplicity ν (p.map (algebraMap K L)) = 0 := by
  by_cases hp : p = 0
  · simp [hp]
  · apply Polynomial.rootMultiplicity_eq_zero
    intro hroot
    exact hν ⟨p, hp, by rwa [Polynomial.aeval_def, ← Polynomial.eval_map]⟩

end Transcendental

end CESCount

theorem solution
    {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {Q : Type} [Fintype Q] (U : Q → Module.End K W) (P : Q → Polynomial K) (c : ℕ)
    (Ω₁ : Type) [Field Ω₁] [Algebra K Ω₁] [IsAlgClosed Ω₁]
    (h₁ : ∀ μ : Q → Ω₁, Module.finrank Ω₁
        ↥(⨅ q, Module.End.maxGenEigenspace ((U q).baseChange Ω₁) (μ q)) =
      c * ∏ q, Polynomial.rootMultiplicity (μ q) ((P q).map (algebraMap K Ω₁)))
    (Ω₂ : Type) [Field Ω₂] [Algebra K Ω₂] (lam : Q → Ω₂) :
    Module.finrank Ω₂ ↥(⨅ q, Module.End.maxGenEigenspace ((U q).baseChange Ω₂) (lam q)) =
      c * ∏ q, Polynomial.rootMultiplicity (lam q) ((P q).map (algebraMap K Ω₂)) := by
  classical
  by_cases halg : ∀ q, IsAlgebraic K (lam q)
  · let E : IntermediateField K Ω₂ := IntermediateField.adjoin K (Set.range lam)
    haveI : FiniteDimensional K E := IntermediateField.finiteDimensional_adjoin (fun x hx => by
      obtain ⟨q, rfl⟩ := hx
      exact (halg q).isIntegral)
    let μ : Q → E := fun q => ⟨lam q, IntermediateField.subset_adjoin K _ (Set.mem_range_self q)⟩
    haveI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    let σ : E →ₐ[K] Ω₁ := IsAlgClosed.lift
    have h2 : Module.finrank Ω₂ ↥(⨅ q, Module.End.maxGenEigenspace ((U q).baseChange Ω₂) (lam q)) =
        Module.finrank E ↥(⨅ q, Module.End.maxGenEigenspace ((U q).baseChange E) (μ q)) :=
      CESCount.finrank_iInf_maxGenEigenspace_baseChange_tower (E := E) (Ω := Ω₂) U μ
    have h1' : Module.finrank Ω₁ ↥(⨅ q, Module.End.maxGenEigenspace ((U q).baseChange Ω₁) (σ (μ q))) =
        Module.finrank E ↥(⨅ q, Module.End.maxGenEigenspace ((U q).baseChange E) (μ q)) := by
      letI : Algebra E Ω₁ := (σ : E →+* Ω₁).toAlgebra
      haveI : IsScalarTower K E Ω₁ :=
        IsScalarTower.of_algebraMap_eq (fun k => (σ.commutes k).symm)
      exact CESCount.finrank_iInf_maxGenEigenspace_baseChange_tower (E := E) (Ω := Ω₁) U μ
    have hR2 : ∀ q, Polynomial.rootMultiplicity (lam q) ((P q).map (algebraMap K Ω₂)) =
        Polynomial.rootMultiplicity (μ q) ((P q).map (algebraMap K E)) := by
      intro q
      rw [Polynomial.eq_rootMultiplicity_map (p := (P q).map (algebraMap K E))
        (algebraMap E Ω₂).injective (μ q), Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
      rfl
    have hR1 : ∀ q, Polynomial.rootMultiplicity (σ (μ q)) ((P q).map (algebraMap K Ω₁)) =
        Polynomial.rootMultiplicity (μ q) ((P q).map (algebraMap K E)) := by
      intro q
      rw [Polynomial.eq_rootMultiplicity_map (p := (P q).map (algebraMap K E))
        (σ : E →+* Ω₁).injective (μ q), Polynomial.map_map]
      rw [AlgHom.comp_algebraMap]
      rfl
    calc Module.finrank Ω₂ ↥(⨅ q, Module.End.maxGenEigenspace ((U q).baseChange Ω₂) (lam q))
        = Module.finrank E ↥(⨅ q, Module.End.maxGenEigenspace ((U q).baseChange E) (μ q)) := h2
      _ = Module.finrank Ω₁ ↥(⨅ q, Module.End.maxGenEigenspace ((U q).baseChange Ω₁) (σ (μ q))) :=
          h1'.symm
      _ = c * ∏ q, Polynomial.rootMultiplicity (σ (μ q)) ((P q).map (algebraMap K Ω₁)) :=
          h₁ (fun q => σ (μ q))
      _ = c * ∏ q, Polynomial.rootMultiplicity (μ q) ((P q).map (algebraMap K E)) := by
          simp_rw [hR1]
      _ = c * ∏ q, Polynomial.rootMultiplicity (lam q) ((P q).map (algebraMap K Ω₂)) := by
          simp_rw [hR2]
  · simp only [not_forall] at halg
    obtain ⟨q₀, hq₀⟩ := halg
    have hL : (⨅ q, Module.End.maxGenEigenspace ((U q).baseChange Ω₂) (lam q)) = ⊥ :=
      eq_bot_iff.mpr (iInf_le_of_le q₀
        (by rw [CESCount.maxGenEigenspace_baseChange_eq_bot_of_transcendental (U q₀) hq₀]))
    have hR : ∏ q, Polynomial.rootMultiplicity (lam q) ((P q).map (algebraMap K Ω₂)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ q₀)
        (CESCount.rootMultiplicity_map_eq_zero_of_transcendental (P q₀) hq₀)
    rw [hL, finrank_bot, hR, mul_zero]

end S_Module_End_finrank_iInf_maxGenEigenspace_baseChange_eq_mul_prod_rootMultiplicity_of_isAlgClosed
end P2MW
export P2MW.S_Module_End_finrank_iInf_maxGenEigenspace_baseChange_eq_mul_prod_rootMultiplicity_of_isAlgClosed (solution)
