-- Prove2me | solution 1 for GlobalTheory.Mass.OrbTransport.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:07:09.139219+00:00
-- url     : https://prove2.me/submissions/67e4a02a-1092-451e-9841-accb0b384041

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitWeightedStabilizerSumTransportEquivariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
namespace GlobalTheory.Mass.OrbTransport
open NumberField Matrix in
open scoped ENNReal Classical in
open MulAction in
private lemma exists_smul_eq_orbit_out {G α : Type} [Group G] [MulAction G α] (y : α) :
    ∃ g : G, g • y = (Quotient.mk (orbitRel G α) y).out := by
  obtain ⟨g, hg⟩ := Quotient.mk_out (s := orbitRel G α) y
  exact ⟨g, hg⟩
open NumberField Matrix in
open scoped ENNReal Classical in
open MulAction in
private lemma card_stabilizer_smul_eq' {G α : Type} [Group G] [MulAction G α] (g : G) (a : α) :
    ENat.card (stabilizer G (g • a)) = ENat.card (stabilizer G a) :=
  (ENat.card_congr (stabilizerEquivStabilizer (g := g) rfl).toEquiv).symm
end GlobalTheory.Mass.OrbTransport
end

set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.OrbTransport
open NumberField Matrix
open scoped ENNReal Classical
open MulAction
namespace GlobalTheory.Mass.OrbTransport
namespace _root_.GlobalTheory.Mass.OrbTransport
theorem _root_.solution : ∀ (G G' α β : Type) [Group G] [Group G'] [MulAction G α] [MulAction G' β] (φ : G ≃* G') (f : α → β) (X : Set α) (Y : Set β) (N : β → ℝ≥0∞), _root_.GlobalTheory.Mass.Stable G X → _root_.GlobalTheory.Mass.Stable G' Y → Set.BijOn f X Y → (∀ (g : G), ∀ x ∈ X, f (g • x) = φ g • f x) → (∀ (g : G') y, N (g • y) = N y) → _root_.GlobalTheory.Mass.orbSum G X (fun x => N (f x)) = _root_.GlobalTheory.Mass.orbSum G' Y N := by
  intro G G' α β _ _ _ _ φ f X Y N hX hY hf hequiv hN
  have hcard : ∀ x ∈ X, ENat.card (stabilizer G' (f x)) = ENat.card (stabilizer G x) := by
    intro x hx
    refine (ENat.card_congr (Equiv.subtypeEquiv φ.toEquiv fun g => ?_)).symm
    simp only [mem_stabilizer_iff, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
    rw [← hequiv g x hx]
    exact ⟨fun h => by rw [h], fun h => hf.injOn (hX g x hx) hx h⟩
  have hout : ∀ q : {q : orbitRel.Quotient G α // q.out ∈ X},
      (Quotient.mk (orbitRel G' β) (f q.1.out)).out ∈ Y := by
    intro q
    obtain ⟨g, hg⟩ := exists_smul_eq_orbit_out (G := G') (f q.1.out)
    rw [← hg]
    exact hY g _ (hf.mapsTo q.2)
  let F : {q : orbitRel.Quotient G α // q.out ∈ X} → {q : orbitRel.Quotient G' β // q.out ∈ Y} :=
    fun q => ⟨Quotient.mk _ (f q.1.out), hout q⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨q₁, h₁⟩ ⟨q₂, h₂⟩ h
      obtain ⟨g', hg'⟩ := Quotient.exact (congrArg Subtype.val h)
      apply Subtype.ext
      show q₁ = q₂
      rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
      apply Quotient.sound
      refine ⟨φ.symm g', ?_⟩
      apply hf.injOn (hX _ _ h₂) h₁
      rw [hequiv _ _ h₂, MulEquiv.apply_symm_apply]
      exact hg'
    · rintro ⟨q', hq'⟩
      obtain ⟨x, hx, hfx⟩ := hf.surjOn hq'
      obtain ⟨g, hg⟩ := exists_smul_eq_orbit_out (G := G) x
      have hmem : (Quotient.mk (orbitRel G α) x).out ∈ X := by rw [← hg]; exact hX g x hx
      refine ⟨⟨Quotient.mk _ x, hmem⟩, Subtype.ext ?_⟩
      show Quotient.mk _ (f (Quotient.mk (orbitRel G α) x).out) = q'
      rw [← Quotient.out_eq q', ← hg, hequiv g x hx, hfx]
      exact Quotient.sound ⟨φ g, rfl⟩
  unfold _root_.GlobalTheory.Mass.orbSum
  rw [← (Equiv.ofBijective F hF).tsum_eq]
  congr 1
  funext q
  obtain ⟨g', hg'⟩ := exists_smul_eq_orbit_out (G := G') (f q.1.out)
  show _ = (ENat.card (stabilizer G' (Quotient.mk (orbitRel G' β) (f q.1.out)).out) : ℝ≥0∞)⁻¹ *
    N (Quotient.mk (orbitRel G' β) (f q.1.out)).out
  rw [← hg', card_stabilizer_smul_eq', hN, hcard _ q.2]
end _root_.GlobalTheory.Mass.OrbTransport
end GlobalTheory.Mass.OrbTransport
