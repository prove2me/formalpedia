-- Prove2me | solution 1 for GlobalTheory.MuTowerInj.ker_le_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:59:22.884649+00:00
-- url     : https://prove2.me/submissions/63aa4aa9-0834-4794-b581-1a8154b0345c

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MuCocycleCoboundaryLift
import Theorems.Thm_GlobalTheory_MuTowerInj_mapH2Add_mk
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_ReciprocityTheory_Gal_coboundaries2_le_cocycles2
import Theorems.Thm_ReciprocityTheory_Gal_mem_cocycles2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GlobalTheory GlobalTheory.MuTowerInj
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {R₁ R₂ R₃ M₁ M₂ M₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃]
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module R₁ M₁] [Module R₂ M₂] [Module R₃ M₃]
  [TopologicalSpace M₁] [TopologicalSpace M₂] [TopologicalSpace M₃]
  [DiscreteTopology M₁] [DiscreteTopology M₂] [DiscreteTopology M₃]
namespace GlobalTheory.MuTowerInj
theorem _root_.solution [ContinuousMul Γ] (ρ₁ : Representation R₁ Γ M₁)
    (ρ₂ : Representation R₂ Γ M₂) (ρ₃ : Representation R₃ Γ M₃) (h₂ : ContAction ρ₂)
    (u : M₁ →+ M₂) (hu : ∀ g m, u (ρ₁ g m) = ρ₂ g (u m))
    (p : M₂ →+ M₃) (hp : ∀ g m, p (ρ₂ g m) = ρ₃ g (p m))
    (hinj : Function.Injective u) (hsurj : Function.Surjective p)
    (hex : ∀ m, p m = 0 → ∃ k, u k = m) :
    (secondCohomologyMapOfEquivariantAdd ρ₂ ρ₃ p hp).ker ≤ (secondCohomologyMapOfEquivariantAdd ρ₁ ρ₂ u hu).range := by
  intro x hx
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [AddMonoidHom.mem_ker, mapH2Add_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hx
  obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem ρ₃ _).1 hx

  have hsc : Continuous (Function.surjInv hsurj ∘ c) :=
    (continuous_of_discreteTopology (f := Function.surjInv hsurj)).comp hc
  have hb : d1 ρ₂ (Function.surjInv hsurj ∘ c) ∈ Z2 ρ₂ :=
    coboundaries2_le_cocycles2 ρ₂ h₂ ((separated_dvr_second_cohomology_mem ρ₂ _).2 ⟨_, hsc, rfl⟩)
  have hf' : f.1 - d1 ρ₂ (Function.surjInv hsurj ∘ c) ∈ Z2 ρ₂ := (Z2 ρ₂).sub_mem f.2 hb

  have hker : ∀ q, p ((f.1 - d1 ρ₂ (Function.surjInv hsurj ∘ c)) q) = 0 := by
    rintro ⟨g, h⟩
    have e : ρ₃ g (c h) - c (g * h) + c g = p (f.1 (g, h)) := by
      have e0 := congrFun hcf (g, h)
      rw [d1_apply] at e0
      exact e0
    rw [Pi.sub_apply, d1_apply, map_sub, map_add, map_sub, hp]
    simp only [Function.comp_apply, Function.surjInv_eq hsurj]
    rw [e, sub_self]
  obtain ⟨k, hk⟩ : ∃ k : Γ × Γ → M₁, ∀ q, u (k q) = (f.1 - d1 ρ₂ (Function.surjInv hsurj ∘ c)) q :=
    ⟨fun q => Function.invFun u _, fun q => Function.invFun_eq (hex _ (hker q))⟩
  have hkc : Continuous k := by
    have hk' : k = Function.invFun u ∘ (f.1 - d1 ρ₂ (Function.surjInv hsurj ∘ c)) := by
      funext q
      rw [Function.comp_apply, ← hk q, Function.leftInverse_invFun hinj]
    rw [hk']
    exact (continuous_of_discreteTopology (f := Function.invFun u)).comp ((mem_cocycles2 ρ₂ _).1 hf').1
  have hkZ : k ∈ Z2 ρ₁ := by
    refine (mem_cocycles2 ρ₁ k).2 ⟨hkc, fun g h t => hinj ?_⟩
    rw [map_zero, map_sub, map_add, map_sub, hu, hk, hk, hk, hk]
    exact ((mem_cocycles2 ρ₂ _).1 hf').2 g h t
  refine AddMonoidHom.mem_range.2 ⟨Submodule.Quotient.mk ⟨k, hkZ⟩, ?_⟩
  rw [mapH2Add_mk, Submodule.Quotient.eq, Submodule.mem_comap]
  refine (separated_dvr_second_cohomology_mem ρ₂ _).2 ⟨-(Function.surjInv hsurj ∘ c), hsc.neg, ?_⟩
  funext q
  rw [map_neg, Pi.neg_apply]
  show _ = u (k q) - f.1 q
  rw [hk q, Pi.sub_apply]
  abel
end GlobalTheory.MuTowerInj
