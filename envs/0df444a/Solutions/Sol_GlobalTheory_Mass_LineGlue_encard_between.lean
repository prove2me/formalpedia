-- Prove2me | solution 1 for GlobalTheory.Mass.LineGlue.encard_between
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:49:27.155872+00:00
-- url     : https://prove2.me/submissions/e291be4a-2dd3-42a5-9d75-7e86b9596e4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianLatticesGluedAlongLine
import Theorems.Thm_GlobalTheory_Mass_LineGlue_sup_span_congr
import Theorems.Thm_GlobalTheory_Mass_LineGlue_exists_gen

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
variable {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
namespace GlobalTheory.Mass.LineGlue
theorem _root_.solution (h1 : Module.finrank K W = 1) {B : Submodule (𝓞 K) W}
    (hB : Submodule.IsLattice K B) (T : 𝓞 K) (hT : T ≠ 0) :
    {C : Submodule (𝓞 K) W | B ≤ C ∧ ∀ x ∈ C, T • x ∈ B}.encard ≤
      ((Ideal.absNorm (Ideal.span {T}) : ℕ) : ℕ∞) := by
  set D : Submodule (𝓞 K) W := B.comap (LinearMap.lsmul (𝓞 K) W T) with hD
  have hTK : algebraMap (𝓞 K) K T ≠ 0 := by simpa using hT
  have hinj : Function.Injective (LinearMap.lsmul (𝓞 K) W T) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have : algebraMap (𝓞 K) K T • x = 0 := by rw [algebraMap_smul]; exact hx
    exact (smul_eq_zero.1 this).resolve_left hTK
  have hDfg : D.FG :=
    Submodule.fg_of_fg_map_injective _ hinj (hB.fg.of_le (Submodule.map_comap_le _ _))
  obtain ⟨y, hy⟩ := exists_gen h1 hB (fun x hx => B.smul_mem T hx : B ≤ D) hDfg
  have hyD : T • y ∈ B := by
    have : y ∈ D := by
      rw [hy]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)
    exact this
  let Φ : (𝓞 K ⧸ Ideal.span {T}) → Submodule (𝓞 K) W := fun q =>
    B ⊔ Submodule.span (𝓞 K) {(Quotient.out q : 𝓞 K) • y}
  have hsub : {C : Submodule (𝓞 K) W | B ≤ C ∧ ∀ x ∈ C, T • x ∈ B} ⊆ Φ '' Set.univ := by
    rintro C ⟨hBC, hC⟩
    have hCD : C ≤ D := hC
    obtain ⟨c, hc⟩ := exists_gen h1 hB hBC (hDfg.of_le hCD)
    have hcD : c ∈ B ⊔ Submodule.span (𝓞 K) {y} := by
      rw [← hy]
      apply hCD
      rw [hc]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self c)
    obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.1 hcD
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hz
    refine ⟨Ideal.Quotient.mk _ r, trivial, ?_⟩
    rw [hc]
    apply sup_span_congr
    have : Quotient.out (Ideal.Quotient.mk (Ideal.span {T}) r) - r ∈ Ideal.span {T} := by
      rw [← Ideal.Quotient.eq]
      exact Ideal.Quotient.mk_out _
    obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.1 this
    have e : Quotient.out (Ideal.Quotient.mk (Ideal.span {T}) r) • y - (a + r • y) =
        k • (T • y) - a := by
      rw [smul_smul, hk, sub_smul]; abel
    rw [e]
    exact sub_mem (B.smul_mem k hyD) ha
  have hn : Ideal.absNorm (Ideal.span {T}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hT
  have hcard : Nat.card (𝓞 K ⧸ Ideal.span {T}) = Ideal.absNorm (Ideal.span {T}) := rfl
  have : Finite (𝓞 K ⧸ Ideal.span {T}) := Nat.finite_of_card_ne_zero (by rwa [hcard])
  calc _ ≤ (Φ '' Set.univ).encard := Set.encard_le_encard hsub
    _ ≤ (Set.univ : Set (𝓞 K ⧸ Ideal.span {T})).encard := Set.encard_image_le _ _
    _ = _ := by rw [Set.encard_univ, ENat.card_eq_coe_natCard, hcard]
end GlobalTheory.Mass.LineGlue
