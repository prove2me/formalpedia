-- Prove2me | solution 1 for GlobalTheory.SplitLift.exists_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:56:07.571141+00:00
-- url     : https://prove2.me/submissions/58047034-6605-401e-a70e-3c16e978fa3a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUnitaryStabilizerLiftOfSplitIdempotent
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_RowLev_Red_map_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.SplitLift
open Formalism.UG
variable {A : Type} [CommRing A] {n : ℕ}
namespace GlobalTheory.SplitLift
theorem _root_.solution (S : Subring A) (Λ : Submodule S (Fin n → A)) {k : Type} [Field k]
    (r : S →+* k) (c : Λ →ₛₗ[r] (Fin n → k)) (ε : S) (hfg : Λ.FG)
    (hε : ε * ε = ε) (hrε : r ε = 1)
    (hr : Function.Surjective r) (hloc : ∀ z : S, r z ≠ 0 → ∃ t : S, z * t * ε = ε)
    (hc : Function.Surjective c)
    (hker : ∀ y : Λ, c y = 0 → (y : Fin n → A) ∈ RingHom.ker r • Λ) :
    ∃ μ : Fin n → Λ, (∀ a : Fin n → S, c (∑ i, a i • μ i) = fun i => r (a i)) ∧
      (∀ i, ε • μ i = μ i) ∧ ∀ y : Λ, ∃ a : Fin n → S, ε • y = ∑ i, a i • μ i := by
  choose g hg using hc
  let μ : Fin n → Λ := fun i => ε • g (Pi.single i 1)
  have h1 : ∀ a : Fin n → S, c (∑ i, a i • μ i) = fun i => r (a i) := by
    intro a
    rw [map_sum]
    ext j
    simp [μ, map_smulₛₗ, hg, hrε, Finset.sum_apply, Pi.single_apply]
  have h2 : ∀ i, ε • μ i = μ i := fun i => by simp only [μ, smul_smul, hε]
  refine ⟨μ, h1, h2, ?_⟩
  let N : Submodule S (Fin n → A) := Submodule.span S (Set.range fun i => (μ i : Fin n → A))
  have hle : Λ ≤ N ⊔ RingHom.ker r • Λ := by
    intro y hy
    choose f hf using hr
    let a : Fin n → S := fun i => f (c ⟨y, hy⟩ i)
    have h0 : c (⟨y, hy⟩ - ∑ i, a i • μ i) = 0 := by
      rw [map_sub, h1]; ext j; simp [a, hf]
    have h3 := hker _ h0
    have h4 : ((∑ i, a i • μ i : Λ) : Fin n → A) ∈ N := by
      rw [Submodule.coe_sum]
      exact Submodule.sum_mem _ fun i _ =>
        N.smul_mem (a i) (Submodule.subset_span ⟨i, rfl⟩)
    have : y = ((∑ i, a i • μ i : Λ) : Fin n → A) +
        ((⟨y, hy⟩ - ∑ i, a i • μ i : Λ) : Fin n → A) := by
      rw [Submodule.coe_sub]; simp
    rw [this]
    exact Submodule.add_mem_sup h4 h3
  obtain ⟨z, hz, hzle⟩ :=
    Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hfg le_rfl hle
  have hz1 : r z ≠ 0 := by
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hz
    rw [hz]; exact one_ne_zero
  obtain ⟨t, ht⟩ := hloc z hz1
  intro y
  have hy : z • (y : Fin n → A) ∈ N := hzle (Submodule.smul_mem_pointwise_smul _ _ _ y.2)
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 hy
  refine ⟨fun i => t * ε * b i, Subtype.ext ?_⟩
  have : ε • (y : Fin n → A) = (t * ε) • z • (y : Fin n → A) := by
    rw [smul_smul]; congr 1; linear_combination -ht
  rw [Submodule.coe_smul, this, ← hb, Finset.smul_sum, Submodule.coe_sum]
  simp only [Submodule.coe_smul, smul_smul]
end GlobalTheory.SplitLift
