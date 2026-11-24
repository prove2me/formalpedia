-- Prove2me | solution 1 for GlobalTheory.inv_cup_pairing_of_inv_cup_characters
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:01:29.525696+00:00
-- url     : https://prove2.me/submissions/b4808df6-5c31-414a-9a89-9cb4b563a446

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvCupPairingOfInvCupCharacters
import Theorems.Thm_GlobalTheory_exists_sum_mul_of_finite_torsion
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (l : ℕ) [Fact l.Prime] (μ : Representation (ZMod (l ^ 1)) Γ (ZMod (l ^ 1))), (∀ g m, μ g m = m) → ∀ (e : H2 μ →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)) (I : Γ → Prop) (u : ZMod (l ^ 1)) (γ φ : Γ), (∀ z y : Γ → ZMod (l ^ 1), Continuous z → Continuous y → (∀ g h, z (g * h) = z g + z h) → (∀ g h, y (g * h) = y g + y h) → (∀ g, I g → y g = 0) → ∀ w : Z2 μ, (∀ g h, w.1 (g, h) = z g * y h) → e (Submodule.Quotient.mk w) = u * (z γ * y φ)) → ∀ (M M' : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [AddCommGroup M'] [TopologicalSpace M'] [DiscreteTopology M'], (∀ m : M, l • m = 0) → ∀ (β : M →+ M' →+ ZMod (l ^ 1)) (x : Γ → M) (y : Γ → M'), Continuous x → Continuous y → (∀ g h, x (g * h) = x g + x h) → (∀ g h, y (g * h) = y g + y h) → (∀ g, I g → y g = 0) → ∀ w : Z2 μ, (∀ g h, w.1 (g, h) = β (x g) (y h)) → e (Submodule.Quotient.mk w) = u * β (x γ) (y φ) := by
  intro Γ _ _ _ _ l _ μ hμ e I u γ φ hchar M M' _ _ _ _ _ _ hl β x y hxc hyc hxa hya hyI w hw
  classical
  haveI hp : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact Fact.out⟩
  haveI : NeZero (l ^ 1) := ⟨hp.out.ne_zero⟩
  letI : Module (ZMod (l ^ 1)) M :=
    AddCommGroup.zmodModule (fun m => by rw [pow_one]; exact hl m)
  have hfin : (Set.range x).Finite := (isCompact_range hxc).finite_of_discrete
  obtain ⟨ι, s, c, d, hdec⟩ :=
    exists_sum_mul_of_finite_torsion (l ^ 1) M M' β (Set.range x) hfin
  have hmem : ∀ k, (fun q : Γ × Γ => c k (x q.1) * d k (y q.2)) ∈ Z2 μ := by
    intro k
    rw [mem_cocycles2]
    refine ⟨?_, ?_⟩
    · exact ((continuous_of_discreteTopology.comp hxc).comp continuous_fst).mul
        ((continuous_of_discreteTopology.comp hyc).comp continuous_snd)
    · intro g h k'
      simp only [hμ, hxa, hya, map_add]
      ring
  let W : ι → Z2 μ := fun k => ⟨_, hmem k⟩
  have hWsum : w = ∑ k ∈ s, W k := by
    apply Subtype.ext
    funext q
    rcases q with ⟨g, h⟩
    rw [Submodule.coe_sum, Finset.sum_apply, hw g h]
    exact hdec (x g) ⟨g, rfl⟩ (y h)
  have hW : ∀ k, e (Submodule.Quotient.mk (W k)) = u * (c k (x γ) * d k (y φ)) := fun k =>
    hchar (fun g => c k (x g)) (fun g => d k (y g))
      (continuous_of_discreteTopology.comp hxc) (continuous_of_discreteTopology.comp hyc)
      (fun g h => by simp only [hxa, map_add]) (fun g h => by simp only [hya, map_add])
      (fun g hg => by simp only [hyI g hg, map_zero]) (W k) (fun g h => rfl)
  have hq : (Submodule.Quotient.mk (∑ k ∈ s, W k) : H2 μ) =
      ∑ k ∈ s, (Submodule.Quotient.mk (W k) : H2 μ) :=
    map_sum (Submodule.mkQ _) W s
  rw [hWsum, hq, map_sum]
  simp only [hW]
  rw [← Finset.mul_sum, ← hdec (x γ) ⟨γ, rfl⟩ (y φ)]
end GlobalTheory
