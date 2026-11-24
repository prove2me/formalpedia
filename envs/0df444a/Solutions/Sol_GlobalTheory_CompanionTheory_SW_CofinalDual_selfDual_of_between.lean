-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CofinalDual.selfDual_of_between
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:06:54.227922+00:00
-- url     : https://prove2.me/submissions/d9a42255-86f5-4519-929f-e0e3d0dcebef

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AnnihilatorOfAnnihilatorLe
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CofinalDual_relIndex_ne_zero_of_isOpen
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CofinalDual_measure_eq_relIndex_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CofinalDual_relIndex_eq_of_pairing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CofinalDual
namespace GlobalTheory.CompanionTheory.SW.CofinalDual
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (χ : V → V → ℂ) (μ : Measure V), μ.IsAddHaarMeasure → (∀ x y, χ x y = χ y x) → (∀ x y, ‖χ x y‖ = 1) → (∀ x x' y, χ (x + x') y = χ x y * χ x' y) → ∀ L₁ L L₂ : AddSubgroup V, L₁ ≤ L → L ≤ L₂ → IsOpen (L₁ : Set V) → IsCompact (L₂ : Set V) → IsCompact (perp χ L₁) → IsOpen (perp χ L₂) → perp χ (perp χ L₁) ⊆ L₁ → perp χ (perp χ L₂) ⊆ L₂ → μ L₁ * μ (perp χ L₁) = 1 → μ L₂ * μ (perp χ L₂) = 1 → IsCompact (perp χ L) ∧ IsOpen (perp χ L) ∧ perp χ (perp χ L) ⊆ L ∧ μ L * μ (perp χ L) = 1 := by
  intro V _ _ _ _ _ χ μ hμ hs hn ha L₁ L L₂ h1 h2 oL₁ cL₂ cP₁ oP₂ dd₁ dd₂ _ m₂
  let Q : AddSubgroup V → AddSubgroup V := perpSub χ hs hn ha
  have hQ : ∀ (A : AddSubgroup V) (y : V), y ∈ Q A ↔ ∀ x ∈ A, χ x y = 1 := fun _ _ => Iff.rfl
  have hQc : ∀ A : AddSubgroup V, (Q A : Set V) = perp χ A := fun _ => rfl
  have anti : ∀ A B : AddSubgroup V, A ≤ B → Q B ≤ Q A :=
    fun A B h y hy x hx => hy x (h hx)
  have hself : ∀ A : AddSubgroup V, A ≤ Q (Q A) := fun A x hx y hy => by
    rw [hs]
    exact hy x hx
  have placeRankTwoOne : Q L₂ ≤ Q L₁ := anti _ _ (h1.trans h2)
  have P2 : Q L₂ ≤ Q L := anti _ _ h2
  have P1 : Q L ≤ Q L₁ := anti _ _ h1
  have LM : L ≤ Q (Q L) := hself L
  have ML : Q (Q L) ≤ L₂ := fun z hz => dd₂ (anti _ _ P2 hz)
  have n0 : L₁.relIndex L₂ ≠ 0 := relIndex_ne_zero_of_isOpen _ _ oL₁ cL₂
  have p0 : (Q L₂).relIndex (Q L₁) ≠ 0 := relIndex_ne_zero_of_isOpen _ _ oP₂ cP₁
  have ea := AddSubgroup.relIndex_mul_relIndex L₁ L L₂ h1 h2
  have ep := AddSubgroup.relIndex_mul_relIndex (Q L₂) (Q L) (Q L₁) P2 P1
  have ek := AddSubgroup.relIndex_mul_relIndex L (Q (Q L)) L₂ LM ML
  have a0 : L₁.relIndex L ≠ 0 := fun h => n0 (by rw [← ea, h, zero_mul])
  have a'0 : L.relIndex L₂ ≠ 0 := fun h => n0 (by rw [← ea, h, mul_zero])
  have q0 : (Q L₂).relIndex (Q L) ≠ 0 := fun h => p0 (by rw [← ep, h, zero_mul])
  have q'0 : (Q L).relIndex (Q L₁) ≠ 0 := fun h => p0 (by rw [← ep, h, mul_zero])
  have m0 : (Q (Q L)).relIndex L₂ ≠ 0 := fun h => a'0 (by rw [← ek, h, mul_zero])
  have kerL₁ : ∀ x, x ∈ L₁ ↔ ∀ y ∈ Q L₁, χ x y = 1 := fun x =>
    ⟨fun hx y hy => hy x hx, fun h => dd₁ fun y hy => by
      rw [hs]
      exact h y hy⟩
  have e1 : L₁.relIndex L = (Q L).relIndex (Q L₁) :=
    relIndex_eq_of_pairing χ hs hn ha L₁ L (Q L) (Q L₁) (fun x _ => kerL₁ x)
      (fun y _ => hQ L y) a0 q'0
  have e2 : (Q (Q L)).relIndex L₂ = (Q L₂).relIndex (Q L) :=
    relIndex_eq_of_pairing χ hs hn ha (Q (Q L)) L₂ (Q L₂) (Q L)
      (fun x _ => by
        rw [hQ]
        exact forall₂_congr fun y _ => by rw [hs])
      (fun y _ => hQ L₂ y) m0 q0
  have e3 : L₁.relIndex L₂ = (Q L₂).relIndex (Q L₁) :=
    relIndex_eq_of_pairing χ hs hn ha L₁ L₂ (Q L₂) (Q L₁) (fun x _ => kerL₁ x)
      (fun y _ => hQ L₂ y) n0 p0
  have e4 : L.relIndex L₂ = (Q L₂).relIndex (Q L) := by
    have : L₁.relIndex L * L.relIndex L₂ = L₁.relIndex L * (Q L₂).relIndex (Q L) := by
      rw [ea, e3, ← ep, e1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero a0) this
  have hk : L.relIndex (Q (Q L)) = 1 := by
    have : L.relIndex (Q (Q L)) * (Q (Q L)).relIndex L₂ = 1 * (Q (Q L)).relIndex L₂ := by
      rw [ek, one_mul, e2, e4]
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero m0) this
  have MLe : Q (Q L) ≤ L := AddSubgroup.relIndex_eq_one.1 hk
  have oP : IsOpen (Q L : Set V) := AddSubgroup.isOpen_mono P2 oP₂
  refine ⟨?_, oP, MLe, ?_⟩
  · exact cP₁.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ oP) P1
  · change μ L * μ (Q L) = 1
    change μ L₂ * μ (Q L₂) = 1 at m₂
    rw [measure_eq_relIndex_mul μ L₁ L h1 oL₁ a0, measure_eq_relIndex_mul μ (Q L₂) (Q L) P2 oP₂ q0,
      ← m₂, measure_eq_relIndex_mul μ L₁ L₂ (h1.trans h2) oL₁ n0, ← ea, e4]
    push_cast
    ring
end GlobalTheory.CompanionTheory.SW.CofinalDual
