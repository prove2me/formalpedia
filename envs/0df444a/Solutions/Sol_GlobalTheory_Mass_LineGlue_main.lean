-- Prove2me | solution 1 for GlobalTheory.Mass.LineGlue.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:24.310719+00:00
-- url     : https://prove2.me/submissions/36a299c2-afde-4a5e-ad93-babbb427daa9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianLatticesGluedAlongLine
import Theorems.Thm_GlobalTheory_Mass_LineGlue_sup_span_congr
import Theorems.Thm_GlobalTheory_Mass_LineGlue_exists_gen
import Theorems.Thm_GlobalTheory_Mass_LineGlue_encard_between
import Theorems.Thm_GlobalTheory_Mass_LineGlue_nondeg_of_pd
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_main
import Theorems.Thm_GlobalTheory_Mass_Witt_mem_perp
import Theorems.Thm_GlobalTheory_Mass_Witt_witt_definite


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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.LineGlue
namespace GlobalTheory.Mass.LineGlue
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ (U : Submodule K V) (A : Submodule (𝓞 K) U) (B : Submodule (𝓞 K) (perp h U)) (T : 𝓞 K), T ≠ 0 → Module.finrank K (perp h U) = 1 → IsIntLat (hRes h U) A → IsIntLat (hRes h (perp h U)) B → {L : Submodule (𝓞 K) V | IsIntLat h L ∧ (∀ x ∈ dual h L, T • x ∈ L) ∧ latIn U L = A ∧ latIn (perp h U) L = B}.encard ≤ ((Ideal.absNorm (Ideal.span {T}) * discN (hRes h U) A : ℕ) : ℕ∞) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hpd U A B T hT h1 hA hB
  obtain ⟨hc, hsU, hpU, -⟩ := (Witt.witt_definite K V h hK hs hpd).2 U
  obtain ⟨-, hsW, hpW, -⟩ := (Witt.witt_definite K V h hK hs hpd).2 (perp h U)
  have hd0 : discN (hRes h U) A ≠ 0 :=
    (DiscOrder.main K U (hRes h U) hK hsU (nondeg_of_pd _ hpU) A hA).1
  have dl := dualLattice (𝓞 K) K (perp h U) (hRes h (perp h U)) hsW (nondeg_of_pd _ hpW)
    star_algebraMap_ringOfIntegers_mem_range
  have horth : ∀ (u : U) (w : perp h U), h (u : V) (w : V) = 0 :=
    fun u w => (Witt.mem_perp h U w).1 w.2 u u.2
  have hdec : ∀ v : V, ∃ (u : U) (w : perp h U), v = u + w := by
    intro v
    have hv : v ∈ U ⊔ perp h U := by rw [hc.sup_eq_top]; trivial
    obtain ⟨u, hu, w, hw, e⟩ := Submodule.mem_sup.1 hv
    exact ⟨⟨u, hu⟩, ⟨w, hw⟩, e.symm⟩

  have hg : ∀ C : Submodule (𝓞 K) (perp h U), ∃ y : perp h U, B ≤ C → C.FG →
      C = B ⊔ Submodule.span (𝓞 K) {y} := by
    intro C
    by_cases hh : B ≤ C ∧ C.FG
    · obtain ⟨y, hy⟩ := exists_gen h1 hB.1 hh.1 hh.2
      exact ⟨y, fun _ _ => hy⟩
    · exact ⟨0, fun a b => absurd ⟨a, b⟩ hh⟩
  choose g hg using hg
  set Ad : Submodule (𝓞 K) U := dual (hRes h U) A with hAd
  let M : Submodule (𝓞 K) V := A.map (U.subtype.restrictScalars (𝓞 K)) ⊔
    B.map ((perp h U).subtype.restrictScalars (𝓞 K))
  let Φ : Submodule (𝓞 K) (perp h U) × (Ad ⧸ A.comap Ad.subtype) → Submodule (𝓞 K) V := fun p =>
    M ⊔ Submodule.span (𝓞 K) {(((Quotient.out p.2 : Ad) : U) : V) +
      (g (dual (hRes h (perp h U)) p.1) : V)}
  let S : Set (Submodule (𝓞 K) (perp h U)) := {C | B ≤ C ∧ ∀ x ∈ C, T • x ∈ B}
  have hsub : {L : Submodule (𝓞 K) V | IsIntLat h L ∧ (∀ x ∈ dual h L, T • x ∈ L) ∧
      latIn U L = A ∧ latIn (perp h U) L = B} ⊆ Φ '' (S ×ˢ Set.univ) := by
    rintro L ⟨hL, hTL, hLA, hLB⟩
    have mA : ∀ u : U, u ∈ A ↔ (u : V) ∈ L := fun u => by rw [← hLA]; rfl
    have mB : ∀ w : perp h U, w ∈ B ↔ (w : V) ∈ L := fun w => by rw [← hLB]; rfl
    let π : V →ₗ[𝓞 K] perp h U :=
      (Submodule.projectionOnto (perp h U) U hc.symm).restrictScalars (𝓞 K)
    have hπ : ∀ (u : U) (w : perp h U), π ((u : V) + (w : V)) = w := by
      intro u w
      simp only [π, LinearMap.restrictScalars_apply, map_add]
      rw [Submodule.projectionOnto_apply_right, Submodule.projectionOnto_apply_left, zero_add]
    set B' := L.map π with hB'
    have mB' : ∀ w : perp h U, w ∈ B' ↔ ∃ u : U, (u : V) + (w : V) ∈ L := by
      intro w
      constructor
      · rintro ⟨v, hv, rfl⟩
        obtain ⟨u, w, rfl⟩ := hdec v
        exact ⟨u, by rw [hπ]; exact hv⟩
      · rintro ⟨u, hu⟩
        exact ⟨_, hu, hπ u w⟩
    have hBB' : B ≤ B' := fun w hw => (mB' w).2 ⟨0, by simpa using (mB w).1 hw⟩
    have hB'fg : B'.FG := hL.1.fg.map π
    have hB'l : Submodule.IsLattice K B' :=
      haveI := hB.1
      Submodule.IsLattice.of_le_of_isLattice_of_fg K hBB' hB'fg
    have mC : ∀ x : perp h U, x ∈ dual (hRes h (perp h U)) B' ↔ (x : V) ∈ dual h L := by
      intro x
      rw [dualBasic_mem_dual, dualBasic_mem_dual]
      constructor
      · intro H v hv
        obtain ⟨u, w, rfl⟩ := hdec v
        have := H w ((mB' w).2 ⟨u, hv⟩)
        rw [map_add, LinearMap.add_apply, horth, zero_add]
        exact this
      · intro H w hw
        obtain ⟨u, hu⟩ := (mB' w).1 hw
        have := H _ hu
        rw [map_add, LinearMap.add_apply, horth, zero_add] at this
        exact this
    have hgen := hg B' hBB' hB'fg
    obtain ⟨a, ha⟩ := (mB' (g B')).1
      (hgen.ge (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
    have haA : a ∈ Ad := by
      rw [hAd, dualBasic_mem_dual]
      intro u hu
      have := hL.2 _ ((mA u).1 hu) _ ha
      rw [map_add, horth, add_zero] at this
      exact this
    refine ⟨(dual (hRes h (perp h U)) B', Submodule.Quotient.mk ⟨a, haA⟩), ⟨⟨?_, ?_⟩, trivial⟩, ?_⟩
    · intro w hw
      rw [mC, dualBasic_mem_dual]
      exact fun v hv => hL.2 v hv _ ((mB w).1 hw)
    · intro x hx
      rw [mB]
      exact hTL _ ((mC x).1 hx)
    · have hML : M ≤ L := by
        refine sup_le ?_ ?_
        · rintro _ ⟨u, hu, rfl⟩; exact (mA u).1 hu
        · rintro _ ⟨u, hu, rfl⟩; exact (mB u).1 hu
      have e1 : L = M ⊔ Submodule.span (𝓞 K) {(a : V) + (g B' : V)} := by
        refine le_antisymm ?_ (sup_le hML ((Submodule.span_singleton_le_iff_mem _ _).2 ha))
        intro v hv
        obtain ⟨u, w, rfl⟩ := hdec v
        obtain ⟨b, hb, z, hz, rfl⟩ := Submodule.mem_sup.1 (hgen.le ((mB' w).2 ⟨u, hv⟩))
        obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hz
        have e : (u : V) + ((b + r • g B' : perp h U) : V) =
            (((u - r • a : U) : V) + (b : V)) + r • ((a : V) + (g B' : V)) := by
          simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul_of_tower, smul_add]
          abel
        have hu : u - r • a ∈ A := by
          rw [mA]
          have := sub_mem (sub_mem hv (L.smul_mem r ha)) ((mB b).1 hb)
          rw [e] at this
          simpa using this
        rw [e]
        exact add_mem (Submodule.mem_sup_left (add_mem (Submodule.mem_sup_left ⟨_, hu, rfl⟩)
          (Submodule.mem_sup_right ⟨_, hb, rfl⟩)))
          (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
      simp only [Φ]
      rw [(dl B' hB'l).2.1, e1]
      apply sup_span_congr
      have hq : Quotient.out (Submodule.Quotient.mk ⟨a, haA⟩ : Ad ⧸ A.comap Ad.subtype) - ⟨a, haA⟩ ∈
          A.comap Ad.subtype := by
        rw [← Submodule.Quotient.eq]
        exact Submodule.Quotient.mk_out _
      rw [add_sub_add_right_eq_sub]
      exact Submodule.mem_sup_left ⟨_, hq, rfl⟩
  have hcard : Nat.card (Ad ⧸ A.comap Ad.subtype) = discN (hRes h U) A := rfl
  have : Finite (Ad ⧸ A.comap Ad.subtype) := Nat.finite_of_card_ne_zero (by rwa [hcard])
  calc _ ≤ (Φ '' (S ×ˢ Set.univ)).encard := Set.encard_le_encard hsub
    _ ≤ (S ×ˢ (Set.univ : Set (Ad ⧸ A.comap Ad.subtype))).encard := Set.encard_image_le _ _
    _ = S.encard * (discN (hRes h U) A : ℕ) := by
      rw [Set.encard_prod, Set.encard_univ, ENat.card_eq_coe_natCard, hcard]
    _ ≤ _ := by
      rw [Nat.cast_mul]
      gcongr
      exact encard_between h1 hB.1 T hT
end GlobalTheory.Mass.LineGlue
