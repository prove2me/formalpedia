-- Prove2me | solution 1 for GlobalTheory.GramCount.ncard_gram_mod_eq_card_ker_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:31:56.038312+00:00
-- url     : https://prove2.me/submissions/ec273fa5-d3fc-4d05-bd58-04beaf3613f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardPrimitiveTuplesGramModNilpotent
import Theorems.Thm_GlobalTheory_GramCount_Prim_map
import Theorems.Thm_GlobalTheory_GramCount_map_ip
import Theorems.Thm_GlobalTheory_GramCount_prim_of_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped Classical
namespace GlobalTheory.GramCount
private lemma ncard_preimage_surjective_eq {A B : Type} [CommRing A] [CommRing B]
    (φ : A →+* B) (hs : Function.Surjective φ) (m n : ℕ)
    (T : Set (Fin m → Fin n → B)) :
    Set.ncard {x : Fin m → Fin n → A | (fun a i => φ (x a i)) ∈ T} =
      Nat.card {u : A // φ u = 0} ^ (n * m) * Set.ncard T := by
  have hσ : ∀ b, φ (Function.surjInv hs b) = b := Function.surjInv_eq hs

  let E : (Fin m → Fin n → A) ≃ (Fin m → Fin n → B) × (Fin m → Fin n → {u : A // φ u = 0}) :=
    { toFun := fun x => (fun a i => φ (x a i),
        fun a i => ⟨x a i - Function.surjInv hs (φ (x a i)), by rw [map_sub, hσ, sub_self]⟩)
      invFun := fun q a i => Function.surjInv hs (q.1 a i) + (q.2 a i).1
      left_inv := fun x => by funext a i; simp
      right_inv := fun q => by
        obtain ⟨q1, q2⟩ := q
        refine Prod.ext ?_ ?_
        · funext a i; simp [hσ, (q2 a i).2]
        · funext a i; apply Subtype.ext; simp [hσ, (q2 a i).2] }
  have e2 : {x : Fin m → Fin n → A | (fun a i => φ (x a i)) ∈ T} ≃
      T × (Fin m → Fin n → {u : A // φ u = 0}) :=
    (E.subtypeEquiv (p := fun x : Fin m → Fin n → A => (fun a i => φ (x a i)) ∈ T)
      (q := fun q : (Fin m → Fin n → B) × (Fin m → Fin n → {u : A // φ u = 0}) => q.1 ∈ T)
      (fun x => Iff.rfl)).trans Equiv.prodSubtypeFstEquivSubtypeProd
  simp only [← Nat.card_coe_set_eq]
  rw [Nat.card_congr e2, Nat.card_prod, Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin]
  ring
end GlobalTheory.GramCount
end

set_option autoImplicit false
open scoped Classical
open GlobalTheory GlobalTheory.GramCount
namespace GlobalTheory.GramCount
theorem _root_.solution {A B : Type} [CommRing A] [Finite A] [CommRing B]
    (c : A →+* A) (c' : B →+* B) (hc : ∀ u, c (c u) = u) (p : A) (hp : IsNilpotent p)
    (φ : A →+* B) (hs : Function.Surjective φ) (hφ : ∀ u, φ (c u) = c' (φ u))
    (hk : ∀ u, φ u = 0 ↔ p ∣ u) (m n : ℕ) (G : Matrix (Fin m) (Fin m) A) :
    Set.ncard {x : Fin m → Fin n → A | Prim c x ∧ ∀ a b, p ∣ ip c (x b) (x a) - G a b} =
      Nat.card {u : A // p ∣ u} ^ (n * m) * Set.ncard (sols c' n (G.map φ)) := by
  have hk' : ∀ u, φ u = 0 → IsUnit (1 + u) := fun u hu => by
    obtain ⟨v, rfl⟩ := (hk u).1 hu
    exact (Commute.all p v).isNilpotent_mul_right hp |>.isUnit_one_add

  have hset : {x : Fin m → Fin n → A | Prim c x ∧ ∀ a b, p ∣ ip c (x b) (x a) - G a b} =
      {x | (fun a i => φ (x a i)) ∈ sols c' n (G.map φ)} := by
    ext x
    simp only [Set.mem_setOf_eq, sols]
    constructor
    · rintro ⟨hx, hG⟩
      refine ⟨Prim.map c c' φ hφ hx, fun a b => ?_⟩
      have h := (hk _).2 (hG a b)
      rw [map_sub, map_ip c c' φ hφ] at h
      simpa [Matrix.map_apply, sub_eq_zero] using h
    · rintro ⟨hx, hG⟩
      refine ⟨prim_of_map c hc c' φ hφ hs hk' hx, fun a b => (hk _).1 ?_⟩
      have h := hG a b
      simp only [Matrix.map_apply] at h
      rw [map_sub, map_ip c c' φ hφ, h, sub_self]
  rw [hset, ncard_preimage_surjective_eq φ hs m n, Nat.card_congr (Equiv.subtypeEquivRight hk)]
end GlobalTheory.GramCount
