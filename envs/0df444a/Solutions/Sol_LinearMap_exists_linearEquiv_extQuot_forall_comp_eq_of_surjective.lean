-- Prove2me | solution 1 for LinearMap.exists_linearEquiv_extQuot_forall_comp_eq_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/d851253e-dbf8-5bd8-ab8f-aa4f6023fb5a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_exists_linearEquiv_extQuot_forall_comp_eq_of_surjective

set_option autoImplicit false

universe u v

namespace P2mWs3EP1

variable {B : Type u} [CommRing B] {M N : Type v} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]

abbrev Rel {F : Type u} [AddCommGroup F] [Module B F] (p : F →ₗ[B] M) : Submodule B (↥(LinearMap.ker p) →ₗ[B] N) :=
  LinearMap.range (LinearMap.lcomp B N (LinearMap.ker p).subtype)

def kerMap {F₁ F₂ : Type u} [AddCommGroup F₁] [Module B F₁] [AddCommGroup F₂] [Module B F₂]
    (p₁ : F₁ →ₗ[B] M) (p₂ : F₂ →ₗ[B] M) (g : F₁ →ₗ[B] F₂) (hg : p₂ ∘ₗ g = p₁) :
    ↥(LinearMap.ker p₁) →ₗ[B] ↥(LinearMap.ker p₂) :=
  g.restrict (p := LinearMap.ker p₁) (q := LinearMap.ker p₂) (fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, hg, hx])

theorem kerMap_coe {F₁ F₂ : Type u} [AddCommGroup F₁] [Module B F₁] [AddCommGroup F₂] [Module B F₂]
    (p₁ : F₁ →ₗ[B] M) (p₂ : F₂ →ₗ[B] M) (g : F₁ →ₗ[B] F₂) (hg : p₂ ∘ₗ g = p₁) (s : ↥(LinearMap.ker p₁)) :
    ((kerMap p₁ p₂ g hg s : ↥(LinearMap.ker p₂)) : F₂) = g s := rfl

def pull {F₁ F₂ : Type u} [AddCommGroup F₁] [Module B F₁] [AddCommGroup F₂] [Module B F₂]
    (p₁ : F₁ →ₗ[B] M) (p₂ : F₂ →ₗ[B] M) (g : F₁ →ₗ[B] F₂) (hg : p₂ ∘ₗ g = p₁) :
    ((↥(LinearMap.ker p₂) →ₗ[B] N) ⧸ Rel (N := N) p₂) →ₗ[B] ((↥(LinearMap.ker p₁) →ₗ[B] N) ⧸ Rel (N := N) p₁) :=
  Submodule.mapQ _ _ (LinearMap.lcomp B N (kerMap p₁ p₂ g hg)) (by
    rintro _ ⟨φ, rfl⟩
    rw [Submodule.mem_comap]
    refine ⟨φ ∘ₗ g, ?_⟩
    ext s
    rfl)

theorem pull_mk {F₁ F₂ : Type u} [AddCommGroup F₁] [Module B F₁] [AddCommGroup F₂] [Module B F₂]
    (p₁ : F₁ →ₗ[B] M) (p₂ : F₂ →ₗ[B] M) (g : F₁ →ₗ[B] F₂) (hg : p₂ ∘ₗ g = p₁) (δ : ↥(LinearMap.ker p₂) →ₗ[B] N) :
    pull (N := N) p₁ p₂ g hg (Submodule.Quotient.mk δ) = Submodule.Quotient.mk (δ ∘ₗ kerMap p₁ p₂ g hg) := rfl

theorem pull_eq_pull {F₁ F₂ : Type u} [AddCommGroup F₁] [Module B F₁] [AddCommGroup F₂] [Module B F₂]
    (p₁ : F₁ →ₗ[B] M) (p₂ : F₂ →ₗ[B] M) (g g' : F₁ →ₗ[B] F₂) (hg : p₂ ∘ₗ g = p₁) (hg' : p₂ ∘ₗ g' = p₁) :
    pull (N := N) p₁ p₂ g hg = pull (N := N) p₁ p₂ g' hg' := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H δ =>
    rw [pull_mk, pull_mk, Submodule.Quotient.eq]

    have hd : ∀ x : F₁, (g - g') x ∈ LinearMap.ker p₂ := fun x => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, map_sub, ← LinearMap.comp_apply, ← LinearMap.comp_apply, hg, hg', sub_self]
    refine ⟨δ ∘ₗ LinearMap.codRestrict (LinearMap.ker p₂) (g - g') hd, ?_⟩
    ext s
    show δ (LinearMap.codRestrict (LinearMap.ker p₂) (g - g') hd s) = δ (kerMap p₁ p₂ g hg s) - δ (kerMap p₁ p₂ g' hg' s)
    rw [← map_sub]
    congr 1

theorem pull_comp {F₁ F₂ F₃ : Type u} [AddCommGroup F₁] [Module B F₁] [AddCommGroup F₂] [Module B F₂]
    [AddCommGroup F₃] [Module B F₃]
    (p₁ : F₁ →ₗ[B] M) (p₂ : F₂ →ₗ[B] M) (p₃ : F₃ →ₗ[B] M) (g : F₁ →ₗ[B] F₂) (hg : p₂ ∘ₗ g = p₁)
    (h : F₂ →ₗ[B] F₃) (hh : p₃ ∘ₗ h = p₂) (x) :
    pull (N := N) p₁ p₂ g hg (pull (N := N) p₂ p₃ h hh x) =
      pull (N := N) p₁ p₃ (h ∘ₗ g) (by rw [← LinearMap.comp_assoc, hh, hg]) x := by
  induction x using Submodule.Quotient.induction_on with
  | H δ => rw [pull_mk, pull_mk, pull_mk]; rfl

theorem pull_id {F₁ : Type u} [AddCommGroup F₁] [Module B F₁] (p₁ : F₁ →ₗ[B] M) (x) :
    pull (N := N) p₁ p₁ LinearMap.id (LinearMap.comp_id p₁) x = x := by
  induction x using Submodule.Quotient.induction_on with
  | H δ => rw [pull_mk]; rfl

theorem exists_lift {r : ℕ} {F₂ : Type u} [AddCommGroup F₂] [Module B F₂]
    (p₁ : (Fin r → B) →ₗ[B] M) (p₂ : F₂ →ₗ[B] M) (hp₂ : Function.Surjective p₂) :
    ∃ g : (Fin r → B) →ₗ[B] F₂, p₂ ∘ₗ g = p₁ := by
  classical
  choose σ hσ using fun i : Fin r => hp₂ (p₁ (Pi.basisFun B (Fin r) i))
  refine ⟨(Pi.basisFun B (Fin r)).constr B σ, (Pi.basisFun B (Fin r)).ext fun i => ?_⟩
  rw [LinearMap.comp_apply, Module.Basis.constr_basis, hσ]

end P2mWs3EP1

open P2mWs3EP1 in
theorem solution
    {B : Type u} [CommRing B] {M N : Type v} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    {r₁ r₂ : ℕ} (p₁ : (Fin r₁ → B) →ₗ[B] M) (p₂ : (Fin r₂ → B) →ₗ[B] M)
    (hp₁ : Function.Surjective p₁) (hp₂ : Function.Surjective p₂) :
    ∃ Φ : ((↥(LinearMap.ker p₂) →ₗ[B] N) ⧸ LinearMap.range (LinearMap.lcomp B N (LinearMap.ker p₂).subtype)) ≃ₗ[B]
        ((↥(LinearMap.ker p₁) →ₗ[B] N) ⧸ LinearMap.range (LinearMap.lcomp B N (LinearMap.ker p₁).subtype)),
      ∀ (g : (Fin r₁ → B) →ₗ[B] (Fin r₂ → B)), p₂ ∘ₗ g = p₁ →
        ∀ (g' : ↥(LinearMap.ker p₁) →ₗ[B] ↥(LinearMap.ker p₂)),
          (∀ s : ↥(LinearMap.ker p₁), ((g' s : ↥(LinearMap.ker p₂)) : Fin r₂ → B) = g (s : Fin r₁ → B)) →
          ∀ δ : ↥(LinearMap.ker p₂) →ₗ[B] N,
            Φ (Submodule.Quotient.mk δ) = Submodule.Quotient.mk (δ ∘ₗ g') := by
  obtain ⟨g₀, hg₀⟩ := exists_lift p₁ p₂ hp₂
  obtain ⟨h₀, hh₀⟩ := exists_lift p₂ p₁ hp₁
  refine ⟨LinearEquiv.ofLinear (pull p₁ p₂ g₀ hg₀) (pull p₂ p₁ h₀ hh₀)
      (LinearMap.ext fun x => ?_) (LinearMap.ext fun x => ?_), ?_⟩
  · rw [LinearMap.comp_apply, pull_comp, pull_eq_pull (N := N) p₁ p₁ (h₀ ∘ₗ g₀) LinearMap.id _ (LinearMap.comp_id p₁),
      pull_id, LinearMap.id_apply]
  · rw [LinearMap.comp_apply, pull_comp, pull_eq_pull (N := N) p₂ p₂ (g₀ ∘ₗ h₀) LinearMap.id _ (LinearMap.comp_id p₂),
      pull_id, LinearMap.id_apply]
  · intro g hg g' hg' δ
    have hgg : g' = kerMap p₁ p₂ g hg := by
      apply LinearMap.ext; intro s; apply Subtype.ext; rw [hg' s, kerMap_coe]
    show pull (N := N) p₁ p₂ g₀ hg₀ (Submodule.Quotient.mk δ) = _
    rw [pull_eq_pull (N := N) p₁ p₂ g₀ g hg₀ hg, pull_mk, hgg]

end S_LinearMap_exists_linearEquiv_extQuot_forall_comp_eq_of_surjective
end P2MW
export P2MW.S_LinearMap_exists_linearEquiv_extQuot_forall_comp_eq_of_surjective (solution)
