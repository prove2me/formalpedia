-- Prove2me | solution 1 for GlobalTheory.SW.Nbr.nb_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:37:17.451578+00:00
-- url     : https://prove2.me/submissions/c3a0f32b-2401-4d44-8a8d-210a50faf1b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Theorems.Thm_GlobalTheory_SW_Nbr_max_of_norm
import Theorems.Thm_P2M_GlobalTheory_SW_Nbr_Int__symm_b5c59deb8a7e
import Theorems.Thm_GlobalTheory_SW_Nbr_smul_le_iff
import Theorems.Thm_GlobalTheory_SW_Nbr_finrank_eq
import Theorems.Thm_GlobalTheory_SW_Nbr_proj
import Theorems.Thm_GlobalTheory_SW_Nbr_relIndex_eq
import Theorems.Thm_GlobalTheory_SW_Nbr_index_iff
import Theorems.Thm_GlobalTheory_SW_Nbr_nbOf_spec
import Theorems.Thm_GlobalTheory_SW_Nbr_nbOf_mem
import Theorems.Thm_GlobalTheory_SW_Nbr_eq_nbOf
import Theorems.Thm_GlobalTheory_SW_Hyper_count


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Nbr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
namespace GlobalTheory.SW.Nbr
theorem _root_.solution {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ : Lt E n}
    (h : Λ ∈ Vset E n M) : (Nb M P Λ).Finite ∧ (Nb M P Λ).ncard * (q - 1) = q ^ n - 1 := by
  have := max_of_norm hP.1 hP.2.2.1
  have := proj h.1
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr h.1
  have hc : Nat.card (𝓞 E ⧸ P) = q := hP.2.2.1
  have : Finite (𝓞 E ⧸ P) := Nat.finite_of_card_ne_zero (hc ▸ hP.1.ne_zero)
  obtain ⟨h1, h2⟩ := Hyper.count (M := Λ) P
  rw [hc, finrank_eq h] at h2
  have hb : Set.BijOn (fun Λ' : Lt E n => Λ'.comap Λ.subtype) (Nb M P Λ)
      {N : Submodule (𝓞 E) Λ | ∃ f : Λ →ₗ[𝓞 E] 𝓞 E ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N} := by
    refine ⟨fun Λ' h' => (index_iff hP.1 hP.2.2.1 _).1
      ⟨fun c hc x => smul_le_iff.1 h'.2.1 c hc x x.2, h'.2.2.trans hP.2.2.1⟩,
      fun Λ' h' Λ'' h'' e => ?_, fun N hN => ?_⟩
    · have e' := congrArg (Submodule.map Λ.subtype) e
      simp only [Submodule.map_comap_subtype] at e'
      exact (eq_nbOf hP h h').trans (e' ▸ (eq_nbOf hP h h'').symm)
    · obtain ⟨h3, h4⟩ := (index_iff hP.1 hP.2.2.1 N).2 hN
      have h5 : (N.map Λ.subtype).comap Λ.subtype = N :=
        Submodule.comap_map_eq_of_injective Λ.injective_subtype N
      have h6 : P • Λ ≤ N.map Λ.subtype :=
        smul_le_iff.2 fun c hc x hx => ⟨_, h3 c hc ⟨x, hx⟩, rfl⟩
      have h7 : (N.map Λ.subtype).toAddSubgroup.relIndex Λ.toAddSubgroup = q := by
        rw [relIndex_eq, h5, h4]
      refine ⟨_, nbOf_mem hP h h6 (Λ.map_subtype_le N) h7, ?_⟩
      have h8 := (nbOf_spec hP h h6 (Λ.map_subtype_le N) h7).2
      refine Eq.trans ?_ h5
      ext x
      exact ⟨fun hx => h8.le ⟨x.2, hx⟩, fun hx => (h8.ge hx).2⟩
  exact ⟨hb.finite_iff_finite.2 h1, by rw [hb.ncard_eq, h2]⟩
end GlobalTheory.SW.Nbr
