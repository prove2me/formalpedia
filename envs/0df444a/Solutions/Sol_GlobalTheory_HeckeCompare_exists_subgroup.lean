-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.exists_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:26:06.633713+00:00
-- url     : https://prove2.me/submissions/447af7f3-b9cf-40d8-98cc-9ba496d73405

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj
import Theorems.Thm_GlobalTheory_HeckeCompare_card_eq_tors_mul
import Theorems.Thm_GlobalTheory_HeckeCompare_exists_split_one
import Theorems.Thm_GlobalTheory_HeckeCompare_IsAct_nat
import Theorems.Thm_GlobalTheory_HeckeCompare_IsAct_comm
import Theorems.Thm_GlobalTheory_HeckeCompare_IsAct_split
import Theorems.Thm_GlobalTheory_HeckeCompare_IsAct_pow_tors
import Theorems.Thm_GlobalTheory_HeckeCompare_IsAct_kill_mul_iff
import Theorems.Thm_GlobalTheory_HeckeCompare_triv_mul
import Theorems.Thm_GlobalTheory_HeckeCompare_triv_symm
import Theorems.Thm_GlobalTheory_HeckeCompare_triv_adj
import Theorems.Thm_GlobalTheory_HeckeCompare_triv_one
import Theorems.Thm_GlobalTheory_HeckeCompare_triv_down
import Theorems.Thm_GlobalTheory_HeckeCompare_exists_root
import Theorems.Thm_GlobalTheory_HeckeCompare_card_orth
import Theorems.Thm_GlobalTheory_HeckeCompare_conj_isMaximal
import Theorems.Thm_GlobalTheory_HeckeCompare_triv_of_primary
import Theorems.Thm_GlobalTheory_HeckeCompare_datum_tors
import Theorems.Thm_GlobalTheory_HeckeCompare_mem_kerSet_iff
import Theorems.Thm_GlobalTheory_HeckeCompare_ev_orth
import Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_ext


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
namespace GlobalTheory.HeckeCompare
theorem _root_.solution [IsAlgClosed k] [CharZero k] (hf : Finite {x : Q // x ^ p = 1}) :
    ∃ C : Subgroup Q, (C : Set Q) = kerSet ρ e p P (P.map (H.bar : 𝓞 E →+* 𝓞 E)) C₀ ∧
      (∀ x ∈ C, ∀ a, ρ a x ∈ C) ∧
      (∀ J : Ideal (𝓞 E), J * P = Ideal.span {(p : 𝓞 E)} → ∀ x, (∀ a ∈ J, ρ a x = 1) → x ∈ C) ∧
      (∀ x ∈ C, ∀ a ∈ Ideal.span {(p : 𝓞 E)} * P.map (H.bar : 𝓞 E →+* 𝓞 E), ρ a x = 1) ∧
      (∀ x ∈ C, ∀ y ∈ C, e (p * p) x y 1) ∧ Nat.card C = Nat.card {x : Q // x ^ p = 1} ∧
      Nat.card {x : Q // x ^ p = 1} = Nat.card {x : Q // x ∈ C ∧ x ^ p = 1} * Nat.card C₀ := by
  have ht : ∀ c ∈ C₀, c ^ p = 1 := fun c hc => datum_tors hρ hpP h₂ hc
  have hq := Nat.mul_pos hp hp
  have h1 : ∀ y : Q, y ^ p = 1 → e p 1 y 1 := fun y hy =>
    triv_symm I hu hp hy (one_pow _) (triv_one I hu hp hy)
  let U : Subgroup Q := Subgroup.ofDiv {x | x ^ p = 1 ∧ ∀ c ∈ C₀, e p x c 1} ⟨1, one_pow _, fun c hc => h1 c (ht c hc)⟩
    fun x hx y hy => by
      have ti : y⁻¹ ^ p = 1 := by rw [inv_pow, hy.1, inv_one]
      refine ⟨by rw [mul_pow, hx.1, ti, mul_one], fun c hc => triv_mul I hu hp hx.1 ti (ht c hc) (hx.2 c hc) ?_⟩
      have e₁ : y⁻¹ = ρ (-1) y := by
        have := hρ.2.2 (-1) 1 y
        have h0 := hρ.nat 0 y
        rw [Nat.cast_zero, pow_zero] at h0
        rw [neg_add_cancel, h0, hρ.1] at this
        exact inv_eq_of_mul_eq_one_left this.symm
      rw [e₁, triv_adj I hu hp hy.1 (ht c hc)]
      exact hy.2 _ (h₁ _ c hc)
  let W : Subgroup Q := Subgroup.ofDiv
    {x | (∃ n : ℕ, ∀ a ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) ^ n, ρ a x = 1) ∧ x ^ p ∈ C₀}
    ⟨1, ⟨0, fun a _ => map_one _⟩, by rw [one_pow]; exact C₀.one_mem⟩ (by
      rintro x ⟨⟨n, hn⟩, hx⟩ y ⟨⟨m, hm⟩, hy⟩
      refine ⟨⟨n + m, fun a ha => ?_⟩, by rw [mul_pow, inv_pow]; exact C₀.mul_mem hx (C₀.inv_mem hy)⟩
      rw [map_mul, map_inv, hn a (Ideal.pow_le_pow_right (Nat.le_add_right _ _) ha),
        hm a (Ideal.pow_le_pow_right (Nat.le_add_left _ _) ha), inv_one, mul_one])
  have mem : ∀ x, x ∈ U ⊔ W ↔ ∃ x' x₂ : Q, x = x' * x₂ ∧ (x' ^ p = 1 ∧ ∀ c ∈ C₀, e p x' c 1) ∧
      (∃ n : ℕ, ∀ a ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) ^ n, ρ a x₂ = 1) ∧ x₂ ^ p ∈ C₀ := fun x => by
    rw [Subgroup.mem_sup]
    exact ⟨fun ⟨a, ha, b, hb, h⟩ => ⟨a, b, h.symm, ha, hb⟩, fun ⟨a, b, h, ha, hb⟩ => ⟨a, ha, b, hb, h.symm⟩⟩
  have tors : ∀ x, (x ∈ U ⊔ W ∧ x ^ p = 1) ↔ (x ^ p = 1 ∧ ∀ c ∈ C₀, e p x c 1) := fun x => by
    refine ⟨fun ⟨hx, t⟩ => ⟨t, fun c hc => ?_⟩, fun h => ⟨Subgroup.mem_sup_left h, h.1⟩⟩
    obtain ⟨x', x₂, rfl, ⟨t', o⟩, ⟨r, k₂⟩, -⟩ := (mem x).1 hx
    rw [mul_pow, t', one_mul] at t
    exact triv_mul I hu hp t' t (ht c hc) (o c hc)
      (triv_of_primary I hu hρ hco hp t (ht c hc) k₂ (s := 1) (by rw [pow_one]; exact h₂ c hc))
  have img : (U ⊔ W).map (powMonoidHom p) = C₀ := by
    refine le_antisymm ?_ fun c hc => ?_
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨x', x₂, rfl, ⟨t', -⟩, -, k₂⟩ := (mem x).1 hx
      rwa [powMonoidHom_apply, mul_pow, t', one_mul]
    · have := conj_isMaximal H P
      obtain ⟨n, π, j, hπ, h, hj⟩ := exists_split_one (Nat.cast_ne_zero.2 hp.ne' : (p : 𝓞 E) ≠ 0)
        (P.map (H.bar : 𝓞 E →+* 𝓞 E))
      obtain ⟨y, rfl⟩ := exists_root I hp (ht c hc)
      have e₁ : ρ j y ^ p = y ^ p := by
        have := hρ.split h (y ^ p)
        rwa [h₂ _ hc π hπ, one_mul, map_pow] at this
      refine ⟨ρ j y, Subgroup.mem_sup_right ⟨⟨n + 1, fun a ha => ?_⟩, e₁ ▸ hc⟩, e₁⟩
      rw [← hρ.2.1]
      exact (hρ.kill_mul_iff p _ y).2 (h₂ _ hc) _ (hj a ha)
  have hc := card_orth I hu hp hf C₀ ht
  rw [← Nat.card_congr (Equiv.subtypeEquivRight tors)] at hc
  refine ⟨U ⊔ W, Set.ext fun x => (mem x).trans (mem_kerSet_iff I hu hρ hco hp hpP h₁ h₂ x).symm, fun x hx a => ?_,
    fun J hJ x hx => ?_, fun x hx => (hρ.kill_mul_iff p _ x).2 (h₂ _ (img ▸ ⟨x, hx, rfl⟩)), fun x hx y hy => ?_,
    by rw [card_eq_tors_mul _ p, img, hc], hc.symm⟩
  · obtain ⟨x', x₂, rfl, ⟨t, o⟩, ⟨r, k₂⟩, k₂'⟩ := (mem x).1 hx
    refine (mem _).2 ⟨ρ a x', ρ a x₂, map_mul _ _ _, ⟨hρ.pow_tors t a, fun c hc => ?_⟩,
      ⟨r, fun b hb => by rw [hρ.comm, k₂ b hb, map_one]⟩, by rw [← map_pow]; exact h₁ _ _ k₂'⟩
    rw [triv_adj I hu hp t (ht c hc)]
    exact o _ (h₁ _ c hc)
  · have hpJ : (p : 𝓞 E) ∈ J * P := hJ ▸ Ideal.mem_span_singleton_self _
    have t : x ^ p = 1 := (hρ.nat p x).symm.trans (hx _ (Ideal.mul_le_inf hpJ).1)
    obtain ⟨a, rfl⟩ := (I.onto p hp _).1 t
    refine Subgroup.mem_sup_left ⟨t, ev_orth I hu hρ hp hpP h₂ ?_⟩
    have key : ∀ z ∈ J * P, ∃ b ∈ P • (⊤ : Submodule (𝓞 E) D.La), z • a = p • b := fun z hz => by
      refine Submodule.mul_induction_on hz (fun j hj π hπ => ?_) ?_
      · obtain ⟨b, hb⟩ := (I.ker p hp (j • a)).1 ((I.lin p j a).trans (hx j hj))
        exact ⟨π • b, Submodule.smul_mem_smul hπ trivial, by rw [mul_comm, mul_smul, hb, smul_comm]⟩
      · rintro z z' ⟨b, hb, e₁⟩ ⟨b', hb', e₂⟩
        exact ⟨b + b', add_mem hb hb', by rw [add_smul, e₁, e₂, smul_add]⟩
    obtain ⟨b, hb, e₁⟩ := key _ hpJ
    rw [Nat.cast_smul_eq_nsmul] at e₁
    have : a = b := D.unimod.1 (LinearMap.ext fun y => mul_left_cancel₀ (Nat.cast_ne_zero.2 hp.ne' : (p : ℤ) ≠ 0) (by
      have := congrArg (fun z => D.EF z y) e₁
      simpa only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] using this))
    exact this ▸ hb
  · obtain ⟨x', x₂, rfl, ⟨t, o⟩, ⟨r, k₂⟩, k₂'⟩ := (mem x).1 hx
    obtain ⟨y', y₂, rfl, ⟨t', o'⟩, ⟨r', l₂⟩, l₂'⟩ := (mem y).1 hy
    have a₁ : x' ^ (p * p) = 1 := by rw [pow_mul, t, one_pow]
    have a₂ : x₂ ^ (p * p) = 1 := by rw [pow_mul, ht _ k₂']
    have b₁ : y' ^ (p * p) = 1 := by rw [pow_mul, t', one_pow]
    have b₂ : y₂ ^ (p * p) = 1 := by rw [pow_mul, ht _ l₂']
    have b₃ : (y' * y₂) ^ (p * p) = 1 := by rw [mul_pow, b₁, b₂, mul_one]
    refine triv_mul I hu hq a₁ a₂ b₃ (triv_symm I hu hq b₃ a₁ ((triv_down I hu hp b₃ t).2 ?_))
      (triv_symm I hu hq b₃ a₂ (triv_mul I hu hq b₁ b₂ a₂ (triv_symm I hu hq a₂ b₁ ((triv_down I hu hp a₂ t').2 ?_))
        (triv_of_primary I hu hρ hco hq b₂ a₂ l₂ k₂)))
    · rw [mul_pow, t', one_mul]
      exact triv_symm I hu hp t (ht _ l₂') (o _ l₂')
    · exact triv_symm I hu hp t' (ht _ k₂') (o' _ k₂')
end GlobalTheory.HeckeCompare
