-- Prove2me | solution 1 for GlobalTheory.RowLev.map_eq_span_of_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:15:36.981868+00:00
-- url     : https://prove2.me/submissions/a8687225-4a98-4687-a5a2-d7e57fc3fe94

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegralAdeleIdealOfIdealPrincipalAndInter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.RowLev
open Formalism.UG Formalism.UG.P Inhab
namespace GlobalTheory.RowLev
theorem _root_.solution {O S : Type} [CommRing O] [CommRing S] (ψ : O →+* S) (𝔞 : Ideal O) (hfg : 𝔞.FG)
    (m a : O) (hm : m ∈ 𝔞) (ha : Ideal.span {m} * 𝔞 ⊔ Ideal.span {a} = 𝔞) (μ : S)
    (hidem : (μ * ψ m) * (μ * ψ m) = μ * ψ m)
    (hjac : (1 - μ * ψ m) * ψ m ∈ Ideal.jacobson (⊥ : Ideal S)) :
    ∃ t : S, 𝔞.map ψ = Ideal.span {t} := by
  generalize he : μ * ψ m = e at hidem hjac
  have hb : Ideal.span {ψ m} * 𝔞.map ψ ⊔ Ideal.span {ψ a} = 𝔞.map ψ := by
    conv_rhs => rw [← ha]
    rw [Ideal.map_sup, Ideal.map_mul, Ideal.map_span, Ideal.map_span, Set.image_singleton,
      Set.image_singleton]
  have haa : a ∈ 𝔞 := by
    rw [← ha]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  have ha' : ψ a ∈ 𝔞.map ψ := Ideal.mem_map_of_mem ψ haa
  have he' : e ∈ 𝔞.map ψ := by
    rw [← he]
    exact Ideal.mul_mem_left _ μ (Ideal.mem_map_of_mem ψ hm)
  refine ⟨e + (1 - e) * ψ a, le_antisymm ?_ ?_⟩
  · have h1 : e ∈ Ideal.span {e + (1 - e) * ψ a} :=
      Ideal.mem_span_singleton'.2 ⟨e, by linear_combination (1 - ψ a) * hidem⟩
    have h2 : (1 - e) * ψ a ∈ Ideal.span {e + (1 - e) * ψ a} :=
      Ideal.mem_span_singleton'.2 ⟨1 - e, by linear_combination (ψ a - 1) * hidem⟩
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (hfg.map ψ)
      ((Ideal.span_singleton_le_iff_mem _).2 hjac) ?_
    intro x hx
    rw [← hb] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨w, hw, rfl⟩ := Ideal.mem_span_singleton_mul.1 hy
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    refine Submodule.mem_sup.2 ⟨e * (ψ m * w + s * ψ a) + s * ((1 - e) * ψ a), ?_,
      ((1 - e) * ψ m) • w, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hw, ?_⟩
    · exact add_mem (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_left _ _ h2)
    · rw [smul_eq_mul]
      ring
  · rw [Ideal.span_singleton_le_iff_mem]
    exact add_mem he' (Ideal.mul_mem_left _ _ ha')
end GlobalTheory.RowLev
