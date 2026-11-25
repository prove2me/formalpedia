-- Prove2me | solution 1 for GlobalTheory.SublatCount.encard_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:02:58.707398+00:00
-- url     : https://prove2.me/submissions/a2e17516-cc57-4895-8514-ade13f1b191a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSublatticesQuotientProdDegreeOnePrimes
import Theorems.Thm_GlobalTheory_SublatCount_encard_eq_of_bijOn
import Theorems.Thm_GlobalTheory_SublatCount_smul_quot
import Theorems.Thm_GlobalTheory_SublatCount_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.SublatCount
variable {O N : Type} [CommRing O] [AddCommGroup N] [Module O N]
namespace GlobalTheory.SublatCount
theorem _root_.solution (I J : Ideal O) (h : IsCoprime I J) :
    (Ker (I * J) N).encard = (Ker I N).encard * (Ker J N).encard := by
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 h
  have key : ∀ {I J : Ideal O} {a b : O}, a ∈ I → b ∈ J → a + b = 1 →
      ∀ {L₁ L₂ L₁' L₂' : Submodule O N}, L₂ ∈ Ker J N → L₁' ∈ Ker I N →
      L₁ ⊓ L₂ = L₁' ⊓ L₂' → L₁ ≤ L₁' := by
    intro I J a b ha hb hab L₁ L₂ L₁' L₂' h2 h1' he x hx
    have h3 : b • x ∈ L₁ ⊓ L₂ := ⟨L₁.smul_mem b hx, smul_mem h2 hb x⟩
    rw [he] at h3
    have := L₁'.add_mem (smul_mem h1' ha x) h3.1
    rwa [← add_smul, hab, one_smul] at this
  rw [← Set.encard_prod]
  symm
  refine encard_eq_of_bijOn (f := fun p => p.1 ⊓ p.2) ⟨?_, ?_, ?_⟩
  · rintro ⟨_, _⟩ ⟨⟨f, hf, rfl⟩, ⟨g, hg, rfl⟩⟩
    refine ⟨(crt I J h).symm.toLinearMap ∘ₗ f.prod g, (crt I J h).symm.surjective.comp ?_, ?_⟩
    · rintro ⟨x, y⟩
      obtain ⟨u, rfl⟩ := hf x
      obtain ⟨v, rfl⟩ := hg y
      refine ⟨b • u + a • v, Prod.ext ?_ ?_⟩
      · change f (b • u + a • v) = f u
        rw [map_add, map_smul, map_smul, smul_quot ha, ← smul_quot ha (f u), ← add_smul,
          add_comm, hab, one_smul]
      · change g (b • u + a • v) = g v
        rw [map_add, map_smul, map_smul, smul_quot hb, ← smul_quot hb (g v), ← add_smul,
          add_comm, hab, one_smul]
    · rw [LinearEquiv.ker_comp, LinearMap.ker_prod]
  · rintro ⟨L₁, L₂⟩ ⟨h1, h2⟩ ⟨L₁', L₂'⟩ ⟨h1', h2'⟩ he
    have he : L₁ ⊓ L₂ = L₁' ⊓ L₂' := he
    have he' : L₂ ⊓ L₁ = L₂' ⊓ L₁' := by rw [inf_comm, he, inf_comm]
    have hba : b + a = 1 := by rw [add_comm, hab]
    exact Prod.ext (le_antisymm (key ha hb hab h2 h1' he) (key ha hb hab h2' h1 he.symm))
      (le_antisymm (key hb ha hba h1 h2' he') (key hb ha hba h1' h2 he'.symm))
  · rintro _ ⟨f, hf, rfl⟩
    let g := (crt I J h).toLinearMap ∘ₗ f
    have hg : Function.Surjective g := (crt I J h).surjective.comp hf
    refine ⟨(LinearMap.ker (LinearMap.fst O _ _ ∘ₗ g), LinearMap.ker (LinearMap.snd O _ _ ∘ₗ g)),
      ⟨⟨_, Prod.fst_surjective.comp hg, rfl⟩, ⟨_, Prod.snd_surjective.comp hg, rfl⟩⟩, ?_⟩
    change LinearMap.ker _ ⊓ LinearMap.ker _ = _
    rw [← LinearMap.ker_prod, ← LinearEquiv.ker_comp (crt I J h) f]
    rfl
end GlobalTheory.SublatCount
