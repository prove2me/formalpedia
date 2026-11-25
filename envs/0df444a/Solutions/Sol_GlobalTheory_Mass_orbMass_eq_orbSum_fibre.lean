-- Prove2me | solution 1 for GlobalTheory.Mass.orbMass_eq_orbSum_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:07:56.451013+00:00
-- url     : https://prove2.me/submissions/cd4cae74-2e4e-4d76-985c-4fcc218c455c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitStabilizerMassEqWeightedSumFibres
import Theorems.Thm_GlobalTheory_Mass_OrbFib_key
import Theorems.Thm_GlobalTheory_Mass_OrbFib_mem_orbit_out
import Theorems.Thm_GlobalTheory_Mass_OrbFib_encard_orbits
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
namespace GlobalTheory.Mass.OrbFib
section
variable {G γ : Type} [Group G] [MulAction G γ]
end
variable {G α β : Type} [Group G] [MulAction G α] [MulAction G β]
end GlobalTheory.Mass.OrbFib
namespace GlobalTheory.Mass
open NumberField Matrix in
open scoped ENNReal Classical in
variable {G α β : Type} [Group G] [MulAction G α] [MulAction G β] in
private theorem tsum_inv_card_stabilizer_mul_encard_orbit_fibre (π : α → β)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x) (Y : Set β) (hY : _root_.GlobalTheory.Mass.Stable G Y)
    (hfin : ∀ y ∈ Y, Finite (MulAction.stabilizer G y)) (x : α) (hx : π x ∈ Y) :
    ∑' r : {r : MulAction.orbitRel.Quotient G β // Quotient.out r ∈ Y},
      ((ENat.card (MulAction.stabilizer G (Quotient.out r.1)) : ℕ∞) : ℝ≥0∞)⁻¹ *
        (((MulAction.orbit G x ∩ π ⁻¹' {Quotient.out r.1}).encard : ℕ∞) : ℝ≥0∞) =
      ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞)⁻¹ := by
  obtain ⟨k, hk⟩ := Quotient.mk_out (s := MulAction.orbitRel G β) (π x)
  have hr0 : Quotient.out (Quotient.mk (MulAction.orbitRel G β) (π x)) ∈ Y := by
    rw [← hk]
    exact hY k _ hx
  rw [tsum_eq_single ⟨_, hr0⟩]
  · dsimp only
    rw [← hk, _root_.GlobalTheory.Mass.OrbFib.key π hπ x k]
    have hyY : k • π x ∈ Y := hY k _ hx
    have hfy := hfin _ hyY
    have hyT : ((ENat.card (MulAction.stabilizer G (k • π x)) : ℕ∞) : ℝ≥0∞) ≠ ⊤ := by
      haveI := hfy
      rw [ENat.card_eq_coe_natCard]
      simp
    rw [_root_.GlobalTheory.Mass.OrbFib.key π hπ x k] at hyT
    have hc0 : ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞) ≠ 0 := by
      have : ENat.card (MulAction.stabilizer G x) ≠ 0 := by
        rw [Ne, ENat.card_eq_zero_iff_empty, not_isEmpty_iff]
        exact ⟨1⟩
      simpa using this
    have he0 : (((MulAction.orbit G x ∩ π ⁻¹' {k • π x}).encard : ℕ∞) : ℝ≥0∞) ≠ 0 := by
      have hmem : k • x ∈ MulAction.orbit G x ∩ π ⁻¹' {k • π x} :=
        ⟨⟨k, rfl⟩, by simp [hπ]⟩
      have : (MulAction.orbit G x ∩ π ⁻¹' {k • π x}).encard ≠ 0 :=
        Set.encard_ne_zero.2 ⟨_, hmem⟩
      simpa using this
    have heT : (((MulAction.orbit G x ∩ π ⁻¹' {k • π x}).encard : ℕ∞) : ℝ≥0∞) ≠ ⊤ := by
      intro h
      apply hyT
      rw [h, ENNReal.top_mul hc0]
    rw [ENNReal.mul_inv (Or.inl he0) (Or.inl heT), mul_right_comm,
      ENNReal.inv_mul_cancel he0 heT, one_mul]
  · intro r hr
    have hempty : MulAction.orbit G x ∩ π ⁻¹' {Quotient.out r.1} = ∅ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      rintro ⟨g, rfl⟩ hz
      apply hr
      apply Subtype.ext
      rw [hπ] at hz
      have hmem : π x ∈ MulAction.orbit G (Quotient.out r.1) :=
        ⟨g⁻¹, by rw [← hz]; exact inv_smul_smul g (π x)⟩
      exact ((_root_.GlobalTheory.Mass.OrbFib.mem_orbit_out r.1 (π x)).1 hmem).symm
    rw [hempty]
    simp
end GlobalTheory.Mass
end

set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass
open NumberField Matrix
open scoped ENNReal Classical
namespace GlobalTheory.Mass
namespace _root_.GlobalTheory.Mass
theorem _root_.solution : ∀ (G α β : Type) [Group G] [MulAction G α]
    [MulAction G β] (X : Set α) (Y : Set β) (π : α → β), (∀ (g : G) x, π (g • x) = g • π x) →
    _root_.GlobalTheory.Mass.Stable G X → _root_.GlobalTheory.Mass.Stable G Y → Set.MapsTo π X Y →
    (∀ y ∈ Y, Finite (MulAction.stabilizer G y)) →
    _root_.GlobalTheory.Mass.orbMass G X =
      _root_.GlobalTheory.Mass.orbSum G Y (fun y => (((X ∩ π ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞)) := by
  intro G α β _ _ _ X Y π hπ hX hY hmaps hfin
  unfold _root_.GlobalTheory.Mass.orbMass _root_.GlobalTheory.Mass.orbSum
  dsimp only
  have step : ∀ r : {r : MulAction.orbitRel.Quotient G β // Quotient.out r ∈ Y},
      ((ENat.card (MulAction.stabilizer G (Quotient.out r.1)) : ℕ∞) : ℝ≥0∞)⁻¹ *
        (((X ∩ π ⁻¹' {Quotient.out r.1}).encard : ℕ∞) : ℝ≥0∞) =
      ∑' q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
        ((ENat.card (MulAction.stabilizer G (Quotient.out r.1)) : ℕ∞) : ℝ≥0∞)⁻¹ *
          (((MulAction.orbit G (Quotient.out q.1) ∩ π ⁻¹' {Quotient.out r.1}).encard : ℕ∞) :
            ℝ≥0∞) := by
    intro r
    rw [_root_.GlobalTheory.Mass.OrbFib.encard_orbits X hX, ENNReal.tsum_mul_left]
  rw [tsum_congr step, ENNReal.tsum_comm]
  refine tsum_congr fun q => ?_
  rw [mul_one]
  exact (tsum_inv_card_stabilizer_mul_encard_orbit_fibre π hπ Y hY hfin _ (hmaps q.2)).symm
end _root_.GlobalTheory.Mass
end GlobalTheory.Mass
