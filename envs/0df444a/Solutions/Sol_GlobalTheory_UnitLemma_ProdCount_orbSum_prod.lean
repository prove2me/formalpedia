-- Prove2me | solution 1 for GlobalTheory.UnitLemma.ProdCount.orbSum_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:43:44.752471+00:00
-- url     : https://prove2.me/submissions/4780d3eb-ec4c-474d-90ec-06904587ee7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountProdOfIdempotentSeparable
import Theorems.Thm_GlobalTheory_UnitLemma_ProdCount_finsum_prod_mul
import Theorems.Thm_P2M_GlobalTheory_UnitLemma_ProdCount_relIndex_prod__970088dce797
import Theorems.Thm_GlobalTheory_UnitLemma_ProdCount_mulLat_prod
import Theorems.Thm_GlobalTheory_UnitLemma_ProdCount_mulLat_one
import Theorems.Thm_GlobalTheory_UnitLemma_ProdCount_stabLat_prod
import Theorems.Thm_GlobalTheory_UnitLemma_ProdCount_intUnits_prod
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_orbSum_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.ProdCount
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial
variable {O : Type} [CommRing O] {A₁ A₂ : Type} [CommRing A₁] [Algebra O A₁] [CommRing A₂] [Algebra O A₂]
namespace GlobalTheory.UnitLemma.ProdCount
theorem _root_.solution (G₁ : Subgroup A₁ˣ) (G₂ : Subgroup A₂ˣ) (G : Subgroup (A₁ × A₂)ˣ)
    (hG : ∀ t, t ∈ G ↔ (MulEquiv.prodUnits t).1 ∈ G₁ ∧ (MulEquiv.prodUnits t).2 ∈ G₂)
    (X₁ : Set (Submodule O A₁)) (X₂ : Set (Submodule O A₂)) (X : Set (Submodule O (A₁ × A₂)))
    (hX : ∀ L₁ L₂, Submodule.prod L₁ L₂ ∈ X ↔ L₁ ∈ X₁ ∧ L₂ ∈ X₂)
    (hsplit : ∀ L ∈ X, ∃ L₁ L₂, L = Submodule.prod L₁ L₂) :
    orbSum O G X (fun _ => 1) = orbSum O G₁ X₁ (fun _ => 1) * orbSum O G₂ X₂ (fun _ => 1) := by
  rw [orbSum_eq, orbSum_eq, orbSum_eq, ← finsum_prod_mul]
  let f : X₁ → X₂ → X := fun L₁ L₂ => ⟨L₁.1.prod L₂.1, (hX _ _).2 ⟨L₁.2, L₂.2⟩⟩
  have key : ∀ (t₁ : A₁ˣ) (t₂ : A₂ˣ), t₁ ∈ G₁ → t₂ ∈ G₂ → ∀ (L₁ M₁ : X₁) (L₂ M₂ : X₂),
      M₁.1 = mulLat O (t₁ : A₁) L₁.1 → M₂.1 = mulLat O (t₂ : A₂) L₂.1 →
      ∃ t ∈ G, (f M₁ M₂).1 = mulLat O ((t : (A₁ × A₂)ˣ) : A₁ × A₂) (f L₁ L₂).1 := by
    intro t₁ t₂ h₁ h₂ L₁ M₁ L₂ M₂ e₁ e₂
    refine ⟨MulEquiv.prodUnits.symm (t₁, t₂), by rw [hG]; simpa using ⟨h₁, h₂⟩, ?_⟩
    change M₁.1.prod M₂.1 = mulLat O ((t₁ : A₁), (t₂ : A₂)) (L₁.1.prod L₂.1)
    rw [mulLat_prod, e₁, e₂]
  let F : Orb O G₁ X₁ → Orb O G₂ X₂ → Orb O G X := Quot.map₂ f
    (by
      rintro L₁ L₂ M₂ ⟨t, ht, e⟩
      exact key 1 t G₁.one_mem ht L₁ L₁ L₂ M₂ (mulLat_one _).symm e)
    (by
      rintro L₁ M₁ L₂ ⟨t, ht, e⟩
      exact key t 1 ht G₂.one_mem L₁ M₁ L₂ L₂ e (mulLat_one _).symm)
  have hsurj : ∀ L : X, ∃ L₁ L₂, L = f L₁ L₂ := by
    rintro ⟨L, hL⟩
    obtain ⟨L₁, L₂, rfl⟩ := hsplit L hL
    exact ⟨⟨L₁, ((hX _ _).1 hL).1⟩, ⟨L₂, ((hX _ _).1 hL).2⟩, rfl⟩
  let p₁ : X → X₁ := fun L => ⟨L.1.map (LinearMap.fst O A₁ A₂), by
    obtain ⟨L₁, L₂, rfl⟩ := hsurj L
    simpa [f] using L₁.2⟩
  let p₂ : X → X₂ := fun L => ⟨L.1.map (LinearMap.snd O A₁ A₂), by
    obtain ⟨L₁, L₂, rfl⟩ := hsurj L
    simpa [f] using L₂.2⟩
  have hp₁ : ∀ L₁ L₂, p₁ (f L₁ L₂) = L₁ := fun L₁ L₂ => Subtype.ext (by simp [p₁, f])
  have hp₂ : ∀ L₁ L₂, p₂ (f L₁ L₂) = L₂ := fun L₁ L₂ => Subtype.ext (by simp [p₂, f])
  have key2 : ∀ L M : X, (∃ t ∈ G, M.1 = mulLat O ((t : (A₁ × A₂)ˣ) : A₁ × A₂) L.1) →
      (∃ t ∈ G₁, (p₁ M).1 = mulLat O ((t : A₁ˣ) : A₁) (p₁ L).1) ∧
      (∃ t ∈ G₂, (p₂ M).1 = mulLat O ((t : A₂ˣ) : A₂) (p₂ L).1) := by
    rintro L M ⟨t, ht, e⟩
    obtain ⟨L₁, L₂, rfl⟩ := hsurj L
    obtain ⟨M₁, M₂, rfl⟩ := hsurj M
    rw [hp₁, hp₁, hp₂, hp₂]
    change M₁.1.prod M₂.1 = mulLat O _ (L₁.1.prod L₂.1) at e
    rw [mulLat_prod] at e
    have e1 := congrArg (Submodule.map (LinearMap.fst O A₁ A₂)) e
    have e2 := congrArg (Submodule.map (LinearMap.snd O A₁ A₂)) e
    simp only [Submodule.prod_map_fst, Submodule.prod_map_snd] at e1 e2
    exact ⟨⟨_, ((hG t).1 ht).1, e1⟩, ⟨_, ((hG t).1 ht).2, e2⟩⟩
  let q : Orb O G₁ X₁ × Orb O G₂ X₂ ≃ Orb O G X :=
    { toFun := fun o => F o.1 o.2
      invFun := fun o => (Quot.map p₁ (fun L M h => (key2 L M h).1) o, Quot.map p₂ (fun L M h => (key2 L M h).2) o)
      left_inv := by
        rintro ⟨⟨L₁⟩, ⟨L₂⟩⟩
        change (Quot.mk _ (p₁ (f L₁ L₂)), Quot.mk _ (p₂ (f L₁ L₂))) = _
        rw [hp₁, hp₂]
        rfl
      right_inv := by
        rintro ⟨L⟩
        obtain ⟨L₁, L₂, rfl⟩ := hsurj L
        change Quot.mk _ (f (p₁ (f L₁ L₂)) (p₂ (f L₁ L₂))) = _
        rw [hp₁, hp₂] }
  rw [← finsum_comp_equiv q]
  refine finsum_congr ?_
  rintro ⟨⟨L₁⟩, ⟨L₂⟩⟩
  change (((stabLat O (L₁.1.prod L₂.1) ⊓ G).relIndex (intUnits O (A₁ × A₂) ⊓ G) : ℕ) : ℚ) =
    (((stabLat O L₁.1 ⊓ G₁).relIndex (intUnits O A₁ ⊓ G₁) : ℕ) : ℚ) *
    (((stabLat O L₂.1 ⊓ G₂).relIndex (intUnits O A₂ ⊓ G₂) : ℕ) : ℚ)
  have h1 : stabLat O (L₁.1.prod L₂.1) ⊓ G = ((stabLat O L₁.1 ⊓ G₁).prod (stabLat O L₂.1 ⊓ G₂)).comap
      (MulEquiv.prodUnits (M := A₁) (N := A₂)).toMonoidHom := by
    ext t
    simp only [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_prod, stabLat_prod, hG,
      MulEquiv.coe_toMonoidHom]
    tauto
  have h2 : intUnits O (A₁ × A₂) ⊓ G = ((intUnits O A₁ ⊓ G₁).prod (intUnits O A₂ ⊓ G₂)).comap
      (MulEquiv.prodUnits (M := A₁) (N := A₂)).toMonoidHom := by
    ext t
    simp only [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_prod, intUnits_prod, hG,
      MulEquiv.coe_toMonoidHom]
    tauto
  rw [h1, h2, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective
    (f := (MulEquiv.prodUnits (M := A₁) (N := A₂)).toMonoidHom) MulEquiv.prodUnits.surjective,
    relIndex_prod', Nat.cast_mul]
end GlobalTheory.UnitLemma.ProdCount
