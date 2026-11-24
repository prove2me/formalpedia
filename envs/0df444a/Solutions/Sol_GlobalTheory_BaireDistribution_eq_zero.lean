-- Prove2me | solution 1 for GlobalTheory.BaireDistribution.eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:31:29.644223+00:00
-- url     : https://prove2.me/submissions/a916551a-7854-4c0a-a918-5a825b8fcffc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatDistributionEqZeroBaire
import Theorems.Thm_GlobalTheory_BaireDistribution_glue
import Theorems.Thm_GlobalTheory_BaireDistribution_isClopen_of_invariant
import Theorems.Thm_GlobalTheory_BaireDistribution_doubleCoset_invariant
import Theorems.Thm_GlobalTheory_BaireDistribution_exists_nhds_invariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open GlobalTheory GlobalTheory.BaireDistribution
namespace GlobalTheory.BaireDistribution
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (ι : Type) [Countable ι] (K : ι → ℕ → Subgroup G), (∀ i m, IsOpen (K i m : Set G) ∧ IsCompact (K i m : Set G)) → (∀ i, ∀ U ∈ nhds (1 : G), ∃ m, (K i m : Set G) ⊆ U) → ∀ D : SB G →ₗ[ℂ] ℂ, (∀ x : G, ∃ i, ∀ (m : ℕ) (φ : SB G), φ.1 = Set.indicator {g : G | ∃ a ∈ K i m, ∃ b ∈ K i m, g = a * x * b} (fun _ => (1 : ℂ)) → D φ = 0) → D = 0 := by
  intro G _ _ _ _ _ ι _ K hK hb D hD
  let O : Set G := {x | ∃ W, IsOpen W ∧ x ∈ W ∧ ∀ φ : SB G, Function.support φ.1 ⊆ W → D φ = 0}
  have hO : IsOpen O := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨W, h1, h2, h3⟩
    exact ⟨W, fun y hy => ⟨W, h1, hy, h3⟩, h1, h2⟩
  have h1 : ∀ φ : SB G, Function.support φ.1 ⊆ O → D φ = 0 := by
    intro φ hφ
    refine glue D IsClopen (fun _ h => h) isClopen_empty (fun _ _ => IsClopen.union)
      (fun _ _ => IsClopen.inter) (fun _ _ => IsClopen.diff) φ fun x hx => ?_
    obtain ⟨W, w1, w2, w3⟩ := hφ hx
    obtain ⟨i, -⟩ := hD x
    obtain ⟨m, hm⟩ := hb i ((fun y => x * y) ⁻¹' W)
      ((w1.preimage (by fun_prop)).mem_nhds (by simpa using w2))
    refine ⟨(fun y => x⁻¹ * y) ⁻¹' K i m, IsClopen.preimage
      ⟨(K i m).isClosed_of_isOpen (hK i m).1, (hK i m).1⟩ (by fun_prop), by simp,
      fun C' _ hC' ψ hψ => w3 ψ fun y hy => ?_⟩
    rw [hψ, Set.support_indicator] at hy
    simpa using hm (hC' hy.1)
  suffices hall : ∀ x, x ∈ O from LinearMap.ext fun φ => h1 φ fun x _ => hall x
  by_contra hne
  push_neg at hne
  let Z : ι → Set G := fun i => {x | ∀ (m : ℕ) (φ : SB G), φ.1 =
    Set.indicator {g : G | ∃ a ∈ K i m, ∃ b ∈ K i m, g = a * x * b} (fun _ => (1 : ℂ)) → D φ = 0}
  haveI : LocallyCompactSpace (Oᶜ : Set G) := hO.isClosed_compl.locallyCompactSpace
  haveI : Nonempty (Oᶜ : Set G) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  obtain ⟨i, y, hy⟩ := nonempty_interior_of_iUnion_of_closed (X := (Oᶜ : Set G))
    (f := fun i => Subtype.val ⁻¹' closure (Z i))
    (fun i => isClosed_closure.preimage continuous_subtype_val)
    (Set.eq_univ_of_forall fun x => by
      obtain ⟨i, hi⟩ := hD x.1
      exact Set.mem_iUnion.2 ⟨i, subset_closure hi⟩)
  obtain ⟨t, t1, t2, t3⟩ := mem_interior.1 hy
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.1 t2
  refine y.2 ⟨W, hW, t3, fun φ hφ => ?_⟩
  obtain ⟨U, hU, hinv⟩ := exists_nhds_invariant φ
  obtain ⟨m, hm⟩ := hb i U hU
  refine glue D (fun C => ∀ a ∈ K i m, ∀ b ∈ K i m, ∀ g, a * g * b ∈ C ↔ g ∈ C)
    (fun C hC => isClopen_of_invariant (hK i m).1 hC) (by simp)
    (fun C C' h h' a ha b hb g => or_congr (h a ha b hb g) (h' a ha b hb g))
    (fun C C' h h' a ha b hb g => and_congr (h a ha b hb g) (h' a ha b hb g))
    (fun C C' h h' a ha b hb g => and_congr (h a ha b hb g) (not_congr (h' a ha b hb g))) φ
    fun x hx => ⟨_, doubleCoset_invariant (K i m) x,
      ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩, fun C hC hs ψ hψ => ?_⟩
  have hval : ∀ g ∈ C, φ.1 g = φ.1 x := fun g hg => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hs hg
    exact hinv a (hm ha) b (hm hb) x
  by_cases hCO : C ⊆ O
  · refine h1 ψ fun g hg => hCO ?_
    rw [hψ, Set.support_indicator] at hg
    exact hg.1
  obtain ⟨w, w1, w2⟩ := Set.not_subset.1 hCO
  have w3 : w ∈ closure (Z i) := t1 (show (⟨w, w2⟩ : (Oᶜ : Set G)) ∈ Subtype.val ⁻¹' W from
    hφ (show φ.1 w ≠ 0 by rw [hval w w1]; exact hx))
  obtain ⟨z, z1, z2⟩ := mem_closure_iff.1 w3 C (isClopen_of_invariant (hK i m).1 hC).2 w1
  have hCz : C = {g : G | ∃ a ∈ K i m, ∃ b ∈ K i m, g = a * z * b} := by
    ext g
    constructor
    · intro hg
      obtain ⟨a, ha, b, hb, rfl⟩ := hs hg
      obtain ⟨c, hc, d, hd, rfl⟩ := hs z1
      exact ⟨a * c⁻¹, mul_mem ha (inv_mem hc), d⁻¹ * b, mul_mem (inv_mem hd) hb, by group⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact (hC a ha b hb z).2 z1
  have hx' : φ.1 x ≠ 0 := hx
  have := z2 m ((φ.1 x)⁻¹ • ψ) (by
    rw [← hCz, Submodule.coe_smul, hψ]
    ext g
    by_cases hg : g ∈ C
    · simp [Set.indicator_of_mem hg, hval g hg, hx']
    · simp [Set.indicator_of_notMem hg])
  simpa [hx'] using this
end GlobalTheory.BaireDistribution
