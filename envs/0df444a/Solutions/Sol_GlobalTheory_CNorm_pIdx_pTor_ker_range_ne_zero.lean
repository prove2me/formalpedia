-- Prove2me | solution 1 for GlobalTheory.CNorm.pIdx_pTor_ker_range_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:06:58.118311+00:00
-- url     : https://prove2.me/submissions/564333f8-9115-4c90-a77f-65d89b24d20a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionFiniteKerRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
namespace GlobalTheory.CNorm
theorem _root_.solution :
    ∀ (p : ℕ) (A A' : Type) [CommGroup A] [CommGroup A'] (g : A →* A'),
      pIdx p (⊤ : Subgroup A) ≠ 0 → pTor p (⊤ : Subgroup A) ≠ 0 → pTor p g.range ≠ 0 →
      pIdx p g.ker ≠ 0 ∧ pTor p g.ker ≠ 0 ∧ pIdx p g.range ≠ 0 := by
  intro p A A' _ _ g h1 h2 h3
  unfold pIdx pTor pows at *
  refine ⟨?_, ?_, ?_⟩
  · set f : A →* A := powMonoidHom p with hf
    have hP : ((⊤ : Subgroup A).map f).relIndex g.ker ≠ 0 :=
      fun h0 => h1 (Subgroup.relIndex_eq_zero_of_le_right le_top h0)
    have hBD : g.ker ≤ g.ker.comap f := by
      intro x hx
      exact g.ker.pow_mem hx p
    have hD : g.ker.relIndex (g.ker.comap f) ≠ 0 := by
      rw [Subgroup.relIndex_ker]
      have : Nat.card ((g.ker.comap f).map g) = Nat.card {x : A' // x ∈ g.range ∧ x ^ p = 1} := by
        refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
        intro x
        constructor
        · rintro ⟨a, ha, rfl⟩
          refine ⟨⟨a, rfl⟩, ?_⟩
          have : g (a ^ p) = 1 := ha
          rwa [map_pow] at this
        · rintro ⟨⟨a, rfl⟩, ha⟩
          refine ⟨a, ?_, rfl⟩
          change g (a ^ p) = 1
          rwa [map_pow]
      rw [this]
      exact h3
    have hQ : (g.ker.map f).relIndex ((g.ker.comap f).map f) ≠ 0 := by
      intro h0
      have hd := Subgroup.relIndex_map_map f g.ker (g.ker.comap f)
      have hk : f.ker ≤ g.ker.comap f := by
        intro x hx
        have : f x = 1 := hx
        change f x ∈ g.ker
        rw [this]
        exact one_mem _
      rw [h0, sup_eq_left.2 hk] at hd
      have hdv : (g.ker ⊔ f.ker).relIndex (g.ker.comap f) ∣ g.ker.relIndex (g.ker.comap f) :=
        Subgroup.relIndex_dvd_of_le_left _ le_sup_left
      rw [← hd] at hdv
      exact hD (Nat.eq_zero_of_zero_dvd hdv)
    have he : (g.ker.comap f).map f = ((⊤ : Subgroup A).map f) ⊓ g.ker := by
      rw [Subgroup.map_comap_eq, ← MonoidHom.range_eq_map]
    refine Subgroup.relIndex_ne_zero_trans hQ ?_
    rw [he, Subgroup.inf_relIndex_right]
    exact hP
  · have hfin : Finite {x : A // x ∈ (⊤ : Subgroup A) ∧ x ^ p = 1} := Nat.finite_of_card_ne_zero h2
    have : Finite {x : A // x ∈ g.ker ∧ x ^ p = 1} :=
      Finite.of_injective
        (fun x => (⟨x.1, Subgroup.mem_top _, x.2.2⟩ : {x : A // x ∈ (⊤ : Subgroup A) ∧ x ^ p = 1}))
        (fun x y h => Subtype.ext (congrArg (fun z => z.1) h))
    have : Nonempty {x : A // x ∈ g.ker ∧ x ^ p = 1} := ⟨⟨1, one_mem _, one_pow p⟩⟩
    exact Nat.card_pos.ne'
  · have he : g.range.map (powMonoidHom p) = ((⊤ : Subgroup A).map (powMonoidHom p)).map g := by
      ext x
      constructor
      · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨a ^ p, ⟨a, Subgroup.mem_top _, rfl⟩, by simp⟩
      · rintro ⟨_, ⟨a, -, rfl⟩, rfl⟩
        exact ⟨g a, ⟨a, rfl⟩, by simp⟩
    rw [he]
    intro h0
    have hd := Subgroup.relIndex_map_map g ((⊤ : Subgroup A).map (powMonoidHom p)) ⊤
    rw [← MonoidHom.range_eq_map g, h0, top_sup_eq] at hd
    have hdv : ((⊤ : Subgroup A).map (powMonoidHom p) ⊔ g.ker).relIndex ⊤ ∣
        ((⊤ : Subgroup A).map (powMonoidHom p)).relIndex ⊤ :=
      Subgroup.relIndex_dvd_of_le_left _ le_sup_left
    rw [← hd] at hdv
    exact h1 (Nat.eq_zero_of_zero_dvd hdv)
end GlobalTheory.CNorm
