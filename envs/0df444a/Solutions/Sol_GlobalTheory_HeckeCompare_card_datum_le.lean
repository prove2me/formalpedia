-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.card_datum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:45:49.302099+00:00
-- url     : https://prove2.me/submissions/47852d65-806d-4e95-ad58-796281b9dabe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj
import Theorems.Thm_GlobalTheory_HeckeCompare_ev_pow
import Theorems.Thm_GlobalTheory_HeckeCompare_triv_symm
import Theorems.Thm_GlobalTheory_HeckeCompare_triv_one
import Theorems.Thm_GlobalTheory_HeckeCompare_card_orth
import Theorems.Thm_GlobalTheory_HeckeCompare_datum_tors
import Theorems.Thm_GlobalTheory_HeckeCompare_ev_orth
import Theorems.Thm_GlobalTheory_HeckeTate_IsPart_exists_inv
import Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_ext
import Theorems.Thm_GlobalTheory_HeckeTate_exists_local_iso


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HeckeCompare
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [CommGroup Q] {ρ : 𝓞 E → Q →* Q} {e : ℕ → Q → Q → kˣ → Prop}
variable (I : TateIso D k Q (fun a x => ρ a x) e) (hu : Uniq e) (hρ : IsAct ρ) {P : Ideal (𝓞 E)} [hP : P.IsMaximal]
  (hco : P ⊔ P.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) {p : ℕ} (hp : 0 < p) (hpP : (p : 𝓞 E) ∈ P)
include I hu hρ hco
include hp hpP
variable {C₀ : Subgroup Q} (h₁ : ∀ a, ∀ x ∈ C₀, ρ a x ∈ C₀)
  (h₂ : ∀ x ∈ C₀, ∀ a ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E), ρ a x = 1)
include h₂
include h₁
omit h₁ hco
namespace GlobalTheory.HeckeCompare
theorem _root_.solution [IsAlgClosed k] [CharZero k] (hf : Finite {x : Q // x ^ p = 1}) :
    Nat.card C₀ ≤ Ideal.absNorm P ^ (D.p + D.q) := by
  have ht : ∀ c ∈ C₀, c ^ p = 1 := fun c hc => datum_tors hρ hpP h₂ hc
  have hc := card_orth I hu hp hf C₀ ht
  have := D.fin
  have := D.proj
  have := hP.isPrime
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact Nat.cast_ne_zero.2 hp.ne' (Ideal.mem_bot.1 hpP)
  have : Finite (𝓞 E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
  obtain ⟨φ, φ', s, hs, hφ, -⟩ := HeckeTate.exists_local_iso (R := 𝓞 E) (M := D.La) (M' := Fin (D.p + D.q) → 𝓞 E)
    (by rw [D.rank, Module.finrank_fin_fun]) P
  have fU : Finite {x : Q // x ^ p = 1 ∧ ∀ c ∈ C₀, e p x c 1} :=
    Finite.of_injective (β := {x : Q // x ^ p = 1}) (fun x => ⟨x.1, x.2.1⟩) fun a b h =>
      Subtype.ext (congrArg (fun z : {x : Q // x ^ p = 1} => z.1) h)
  let F : {x : Q // x ^ p = 1 ∧ ∀ c ∈ C₀, e p x c 1} × (Fin (D.p + D.q) → 𝓞 E ⧸ P) → {x : Q // x ^ p = 1} :=
    fun z => ⟨z.1.1 * I.ev p (φ' fun i => (z.2 i).out), by rw [mul_pow, z.1.2.1, ev_pow I hp, mul_one]⟩
  have hF : Function.Surjective F := by
    rintro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := (I.onto p hp _).1 hx
    obtain ⟨t, π, hπ, h⟩ := hP.exists_inv hs
    let y : Fin (D.p + D.q) → 𝓞 E := t • φ a
    let y' : Fin (D.p + D.q) → 𝓞 E := fun i => (Ideal.Quotient.mk P (y i)).out
    have hm : a - φ' y' ∈ P • (⊤ : Submodule (𝓞 E) D.La) := by
      have e₁ : a - φ' y' = π • a + φ' (y - y') := by
        rw [map_sub, map_smul, hφ, smul_smul, ← add_sub_assoc, ← add_smul, add_comm π, h, one_smul]
      rw [e₁]
      refine add_mem (Submodule.smul_mem_smul hπ trivial) ?_
      rw [pi_eq_sum_univ' (y - y'), map_sum]
      refine sum_mem fun i _ => ?_
      rw [map_smul]
      exact Submodule.smul_mem_smul (Ideal.Quotient.eq.1 (Quotient.out_eq _).symm) trivial
    refine ⟨(⟨I.ev p (a - φ' y'), ev_pow I hp _, ev_orth I hu hρ hp hpP h₂ hm⟩, fun i => Ideal.Quotient.mk P (y i)),
      Subtype.ext ?_⟩
    show I.ev p (a - φ' y') * I.ev p (φ' y') = _
    rw [← I.add, sub_add_cancel]
  have hle := Nat.card_le_card_of_surjective F hF
  rw [Nat.card_prod, Nat.card_fun, ← hc, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at hle
  have : Nonempty {x : Q // x ^ p = 1 ∧ ∀ c ∈ C₀, e p x c 1} := ⟨⟨1, one_pow _, fun c hc =>
    triv_symm I hu hp (ht c hc) (one_pow _) (triv_one I hu hp (ht c hc))⟩⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.le_of_mul_le_mul_left hle Nat.card_pos
end GlobalTheory.HeckeCompare
