-- Prove2me | solution 1 for GlobalTheory.BrauerZero.ind_one_sub_index_mem_D0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:03:51.00275+00:00
-- url     : https://prove2.me/submissions/a77d15ce-9133-47be-a91d-50f2dc91b977

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndApplyOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedOneSubIndexMemDegreeOneCharacterDiff
import Theorems.Thm_GlobalTheory_BrauerZero_ind_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI GlobalTheory.BrauerZero
open GlobalTheory GlobalTheory.BrauerZero
namespace GlobalTheory.BrauerZero
theorem _root_.solution {G : Type} [Group G] [Finite G] (K : Subgroup G)
    (hK : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ K) :
    ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ)) ∈ D0 G := by
  classical
  haveI := Fintype.ofFinite G
  haveI hN : K.Normal := ⟨fun n hn g => by
    have h1 := hK g n
    have : g * n * g⁻¹ = (g * n * g⁻¹ * n⁻¹) * n := by group
    rw [this]; exact K.mul_mem h1 hn⟩
  letI : CommGroup (G ⧸ K) :=
    { (inferInstance : Group (G ⧸ K)) with
      mul_comm := by
        intro x y
        induction x using QuotientGroup.induction_on with
        | H a =>
        induction y using QuotientGroup.induction_on with
        | H b =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
          have := hK b⁻¹ a⁻¹
          have e : (a * b)⁻¹ * (b * a) = b⁻¹ * a⁻¹ * b⁻¹⁻¹ * a⁻¹⁻¹ := by group
          rw [e]; exact this }
  haveI : Fintype (G ⧸ K) := Fintype.ofFinite _
  let Q := Additive (G ⧸ K)

  let F : AddChar Q ℂ → G → ℂ := fun ψ g => ψ (Additive.ofMul (QuotientGroup.mk g : G ⧸ K))
  have hFmul : ∀ ψ : AddChar Q ℂ, ∀ a b : G, F ψ (a * b) = F ψ a * F ψ b := by
    intro ψ a b
    simp only [F, QuotientGroup.mk_mul, ofMul_mul, AddChar.map_add_eq_mul]
  have hFone : ∀ ψ : AddChar Q ℂ, F ψ 1 = 1 := by
    intro ψ
    simp only [F, QuotientGroup.mk_one, ofMul_one, AddChar.map_zero_eq_one]

  have hgen : ∀ ψ : AddChar Q ℂ, (F ψ - fun _ => (1 : ℂ)) ∈ D0 G := by
    intro ψ
    let f : G →* ℂ := { toFun := F ψ, map_one' := hFone ψ, map_mul' := hFmul ψ }
    let χ : (⊤ : Subgroup G) →* ℂˣ := (MonoidHom.toHomUnits f).comp (⊤ : Subgroup G).subtype
    have hcl : ∀ g x : G, F ψ (x⁻¹ * g * x) = F ψ g := by
      intro g x
      rw [hFmul, hFmul, mul_comm (F ψ x⁻¹), mul_assoc, ← hFmul, inv_mul_cancel, hFone, mul_one]
    have h1 : ind (⊤ : Subgroup G) (fun h => (χ h : ℂ)) = F ψ := by
      exact (ind_top (F ψ) hcl : _)
    have h2 : ind (⊤ : Subgroup G) (fun _ => (1 : ℂ)) = fun _ => (1 : ℂ) :=
      ind_top (fun _ => (1 : ℂ)) (fun _ _ => rfl)
    apply AddSubgroup.subset_closure
    exact ⟨⊤, χ, by rw [h1, h2]⟩

  have hind : ∀ g : G, ind K (fun _ => (1 : ℂ)) g = if g ∈ K then (K.index : ℂ) else 0 := by
    intro g
    have hconj : ∀ x : G, (x⁻¹ * g * x ∈ K ↔ g ∈ K) := by
      intro x
      constructor
      · intro h
        have := hN.conj_mem _ h x
        have e : x * (x⁻¹ * g * x) * x⁻¹ = g := by group
        rwa [e] at this
      · intro h
        have := hN.conj_mem _ h x⁻¹
        have e : x⁻¹ * g * x⁻¹⁻¹ = x⁻¹ * g * x := by group
        rwa [e] at this
    simp only [ind, finsum_eq_sum_of_fintype, ext0]
    have hs : ∀ x : G, (if h : x⁻¹ * g * x ∈ K then (1 : ℂ) else 0) = if g ∈ K then 1 else 0 := by
      intro x
      by_cases hg : g ∈ K
      · rw [dif_pos ((hconj x).2 hg), if_pos hg]
      · rw [dif_neg (fun h => hg ((hconj x).1 h)), if_neg hg]
    rw [Finset.sum_congr rfl (fun x _ => hs x), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, ← K.card_mul_index]
    have : (Nat.card K : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := K)).ne'
    split_ifs
    · push_cast; field_simp
    · simp

  have hsum : ∀ g : G, (∑ ψ : AddChar Q ℂ, F ψ g) = if g ∈ K then (K.index : ℂ) else 0 := by
    intro g
    have := AddChar.sum_apply_eq_ite (α := Q) (Additive.ofMul (QuotientGroup.mk g : G ⧸ K))
    simp only [F]
    rw [this]
    have hc : (Fintype.card Q : ℂ) = (K.index : ℂ) := by
      rw [Subgroup.index, ← Nat.card_eq_fintype_card]; rfl
    have he : (Additive.ofMul (QuotientGroup.mk g : G ⧸ K) = 0) ↔ g ∈ K := by
      rw [ofMul_eq_zero, QuotientGroup.eq_one_iff]
    by_cases hg : g ∈ K
    · rw [if_pos (he.2 hg), if_pos hg, hc]
    · rw [if_neg (fun h => hg (he.1 h)), if_neg hg]
  have hcard : (Fintype.card (AddChar Q ℂ) : ℂ) = (K.index : ℂ) := by
    rw [AddChar.card_eq, Subgroup.index, ← Nat.card_eq_fintype_card]; rfl
  have heq : ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ))
      = ∑ ψ : AddChar Q ℂ, (F ψ - fun _ => (1 : ℂ)) := by
    funext g
    rw [Finset.sum_apply]
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    rw [hind g, hsum g, hcard]
  rw [heq]
  exact AddSubgroup.sum_mem _ (fun ψ _ => hgen ψ)
end GlobalTheory.BrauerZero
