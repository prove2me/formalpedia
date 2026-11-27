-- Prove2me | solution 1 for GlobalTheory.UnimodMass.fiber_card_mul_stabCard
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:39:09.89321+00:00
-- url     : https://prove2.me/submissions/84d8c2ad-03b1-4151-86cb-f50270ee58a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteDcOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DoubleCosetMassEqRelIndexMulMass
import Theorems.Thm_GlobalTheory_UnimodMass_dcOfCoset_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnimodMass
namespace GlobalTheory.UnimodMass
theorem _root_.solution {G : Type} [Group G] (Γ W K : Subgroup G) (hWK : W ≤ K) (t : G)
    (ht : Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) (k : K) :
    Nat.card {x : K ⧸ W.subgroupOf K // dcOfCoset Γ W K t x = dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K)} *
      stabCard Γ W (t * k) = stabCard Γ K t := by
  classical
  set A := {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}
  set B := {x : K ⧸ W.subgroupOf K // dcOfCoset Γ W K t x = dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K)}
  set T := {δ : Γ // (t * k)⁻¹ * (δ : G) * (t * k) ∈ W}
  have hT : stabCard Γ W (t * k) = Nat.card T := rfl
  have hA : stabCard Γ K t = Nat.card A := rfl
  let φ : A → K := fun γ => ⟨t⁻¹ * (γ.1 : G) * t, γ.2⟩
  have hα : ∀ γ : A, dcOfCoset Γ W K t ((φ γ * k : K) : K ⧸ W.subgroupOf K) =
      dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K) := by
    intro γ
    rw [dcOfCoset_mk, dcOfCoset_mk]
    apply Quotient.sound
    refine ⟨(γ.1 : G)⁻¹, Γ.inv_mem γ.1.2, 1, W.one_mem, ?_⟩
    simp [φ, mul_assoc]
  let α : A → B := fun γ => ⟨(φ γ * k : K), hα γ⟩
  have hsurj : Function.Surjective α := by
    rintro ⟨x, hx⟩
    induction x using QuotientGroup.induction_on with
    | H k' =>
      rw [dcOfCoset_mk, dcOfCoset_mk] at hx
      obtain ⟨γ, hγ, w, hw, e⟩ := Quotient.exact hx

      have hmem : t⁻¹ * γ⁻¹ * t ∈ K := by
        have : t⁻¹ * γ⁻¹ * t = (k' : G) * w * (k : G)⁻¹ := by
          have e' : (k : G) = t⁻¹ * γ * t * k' * w := by
            calc (k : G) = t⁻¹ * (t * k) := by group
              _ = _ := by rw [e]; group
          rw [e']; group
        rw [this]
        exact K.mul_mem (K.mul_mem k'.2 (hWK hw)) (K.inv_mem k.2)
      refine ⟨⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, hmem⟩, ?_⟩
      apply Subtype.ext
      show ((φ _ * k : K) : K ⧸ W.subgroupOf K) = (k' : K ⧸ W.subgroupOf K)
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have e' : (k : G) = t⁻¹ * γ * t * k' * w := by
        calc (k : G) = t⁻¹ * (t * k) := by group
          _ = _ := by rw [e]; group
      have : ((φ ⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, hmem⟩ * k)⁻¹ * k' : K) = (w⁻¹ : G) := by
        simp only [φ, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
        rw [e']; group
      rw [this]; exact W.inv_mem hw
  have hfib : ∀ γ₀ : A, Nonempty ({γ : A // α γ = α γ₀} ≃ T) := by
    intro γ₀
    have key : ∀ γ : A, α γ = α γ₀ ↔ (t * k)⁻¹ * ((γ₀.1 : G)⁻¹ * γ.1) * (t * k) ∈ W := by
      intro γ
      rw [Subtype.ext_iff]
      show ((φ γ * k : K) : K ⧸ W.subgroupOf K) = ((φ γ₀ * k : K) : K ⧸ W.subgroupOf K) ↔ _
      rw [eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have : (((φ γ₀ * k)⁻¹ * (φ γ * k) : K) : G) = (t * k)⁻¹ * ((γ₀.1 : G)⁻¹ * γ.1) * (t * k) := by
        simp only [φ, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]; group
      rw [this]
    refine ⟨{ toFun := fun γ => ⟨⟨(γ₀.1 : G)⁻¹ * γ.1.1, Γ.mul_mem (Γ.inv_mem γ₀.1.2) γ.1.1.2⟩, (key γ.1).1 γ.2⟩
              invFun := fun δ => ⟨⟨⟨(γ₀.1 : G) * δ.1, Γ.mul_mem γ₀.1.2 δ.1.2⟩, ?_⟩, ?_⟩
              left_inv := fun γ => by ext; simp
              right_inv := fun δ => by ext; simp }⟩
    · have h1 : t⁻¹ * ((γ₀.1 : G) * δ.1) * t =
          (t⁻¹ * γ₀.1 * t) * ((k : G) * ((t * k)⁻¹ * δ.1 * (t * k)) * (k : G)⁻¹) := by group
      rw [h1]
      exact K.mul_mem γ₀.2 (K.mul_mem (K.mul_mem k.2 (hWK δ.2)) (K.inv_mem k.2))
    · rw [key]
      simpa using δ.2
  have e : A ≃ B × T :=
    (Equiv.sigmaFiberEquiv α).symm.trans
      ((Equiv.sigmaCongrRight (fun b => by
          have hb := hsurj b
          exact Classical.choice (by
            obtain ⟨γ₀, hγ₀⟩ := hb
            subst hγ₀
            exact hfib γ₀))).trans (Equiv.sigmaEquivProd B T))
  rw [hT, hA, Nat.card_congr e, Nat.card_prod]
end GlobalTheory.UnimodMass
