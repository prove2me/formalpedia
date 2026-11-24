-- Prove2me | solution 1 for GlobalTheory.SubmodulePowSimple.mem_span_equivValues
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:12:24.94225+00:00
-- url     : https://prove2.me/submissions/62c5af1d-d16b-4e40-a6d9-a176cb4e7bab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubmodulePowSimpleEqSumEquivValues
import Theorems.Thm_GlobalTheory_SubmodulePowSimple_snocZero_diag
import Theorems.Thm_GlobalTheory_SubmodulePowSimple_single_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule
open GlobalTheory GlobalTheory.SubmodulePowSimple
variable {P : Type} [AddCommGroup P] [Module ℂ P] {ι : Type}
namespace GlobalTheory.SubmodulePowSimple
theorem _root_.solution (a : ι → Module.End ℂ P)
    (hs : ∀ B : Submodule ℂ P, (∀ i, ∀ p ∈ B, a i p ∈ B) → B ≠ ⊥ → B = ⊤) :
    ∀ (m : ℕ) (N : Submodule ℂ (Fin m → P)), (∀ i, ∀ y ∈ N, (fun j => a i (y j)) ∈ N) →
    ∀ y ∈ N, y ∈ span ℂ (equivValues a m N) := by
  intro m
  induction m with
  | zero =>
    intro N _ y _
    rw [Subsingleton.elim y 0]; exact zero_mem _
  | succ m ih =>
    intro N hN y hy
    let B : Submodule ℂ P := N.comap (LinearMap.single ℂ (fun _ : Fin (m+1) => P) (Fin.last m))
    have hBmem : ∀ p, p ∈ B ↔ (Pi.single (Fin.last m) p : Fin (m+1) → P) ∈ N := fun p => by
      simp [B]
    have hBst : ∀ i, ∀ p ∈ B, a i p ∈ B := by
      intro i p hp
      rw [hBmem] at hp ⊢
      rw [single_diag]; exact hN i _ hp
    by_cases hB : B = ⊥
    · let I : (Fin (m+1) → P) →ₗ[ℂ] (Fin m → P) := LinearMap.funLeft ℂ P Fin.castSucc
      have hinj : ∀ x₁ ∈ N, ∀ x₂ ∈ N, I x₁ = I x₂ → x₁ = x₂ := by
        intro x₁ h₁ x₂ h₂ he
        have hd : x₁ - x₂ ∈ N := N.sub_mem h₁ h₂
        have hs' : x₁ - x₂ = Pi.single (Fin.last m) ((x₁ - x₂) (Fin.last m)) := by
          funext j; refine Fin.lastCases ?_ (fun j => ?_) j
          · simp
          · have h := congrFun he j
            change x₁ (Fin.castSucc j) = x₂ (Fin.castSucc j) at h
            rw [Pi.single_eq_of_ne (Fin.castSucc_lt_last j).ne]
            simp [h]
        have hB' : (x₁ - x₂) (Fin.last m) ∈ B := by
          rw [hBmem, ← hs']; exact hd
        rw [hB, Submodule.mem_bot] at hB'
        rw [hB', Pi.single_zero] at hs'
        exact sub_eq_zero.mp hs'
      let N0 := N.map I
      have hN0 : ∀ i, ∀ w ∈ N0, (fun j => a i (w j)) ∈ N0 := by
        intro i w hw
        obtain ⟨x, hx, rfl⟩ := hw
        exact ⟨_, hN i x hx, rfl⟩
      have lift : ∀ S : P →ₗ[ℂ] (Fin m → P), (∀ p, S p ∈ N0) →
          ∃ S' : P →ₗ[ℂ] (Fin (m+1) → P), (∀ p, S' p ∈ N) ∧ ∀ p, I (S' p) = S p := by
        intro S hS
        let J : N →ₗ[ℂ] (Fin m → P) := I ∘ₗ N.subtype
        have hJ : Function.Injective J := by
          intro u v huv; exact Subtype.ext (hinj u u.2 v v.2 huv)
        have hS' : ∀ p, S p ∈ LinearMap.range J := by
          intro p; obtain ⟨x, hx, hxe⟩ := hS p; exact ⟨⟨x, hx⟩, hxe⟩
        have key : ∀ v, J ((LinearEquiv.ofInjective J hJ).symm v) = v := fun v => by
          have h := congrArg Subtype.val ((LinearEquiv.ofInjective J hJ).apply_symm_apply v)
          rw [LinearEquiv.ofInjective_apply] at h
          exact h
        refine ⟨N.subtype ∘ₗ (LinearEquiv.ofInjective J hJ).symm.toLinearMap ∘ₗ
          S.codRestrict _ hS', fun p => Subtype.property _, fun p => ?_⟩
        exact key ⟨S p, hS' p⟩
      have h1 := ih N0 hN0 (I y) ⟨y, hy, rfl⟩
      obtain ⟨n, f, g, hfg⟩ := (Submodule.mem_span_set').mp h1
      have hg : ∀ k, ∃ S : P →ₗ[ℂ] (Fin m → P), (∀ i p, S (a i p) = fun j => a i (S p j)) ∧
          (∀ p, S p ∈ N0) ∧ ∃ q, (g k : Fin m → P) = S q := fun k => (g k).2
      choose S hSa hSN q hq using hg
      choose S' hS'N hS'I using fun k => lift (S k) (hSN k)
      have hS'a : ∀ k i p, S' k (a i p) = fun j => a i (S' k p j) := by
        intro k i p
        apply hinj _ (hS'N k _) _ (hN i _ (hS'N k p))
        rw [hS'I, hSa, ← hS'I k p]; rfl
      have hy_eq : y = ∑ k, f k • S' k (q k) := by
        apply hinj _ hy _ (sum_mem fun k _ => N.smul_mem _ (hS'N k _))
        rw [← hfg, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul, hS'I, hq]
      rw [hy_eq]
      exact sum_mem fun k _ => smul_mem _ _ (subset_span ⟨S' k, hS'a k, hS'N k, q k, rfl⟩)
    · have hBt := hs B hBst hB
      have hmem : ∀ p, (Pi.single (Fin.last m) p : Fin (m+1) → P) ∈ N := fun p => by
        rw [← hBmem, hBt]; exact Submodule.mem_top
      obtain ⟨y', hy'⟩ : ∃ y', y' = y - Pi.single (Fin.last m) (y (Fin.last m)) := ⟨_, rfl⟩
      have hy'N : y' ∈ N := hy' ▸ N.sub_mem hy (hmem _)
      have hy'last : y' (Fin.last m) = 0 := by simp [hy']
      let N' := N.comap (snocZero m)
      have hN' : ∀ i, ∀ z ∈ N', (fun j => a i (z j)) ∈ N' := by
        intro i z hz
        show snocZero m _ ∈ N
        rw [snocZero_diag]; exact hN i _ hz
      let z : Fin m → P := fun j => y' (Fin.castSucc j)
      have hz : snocZero m z = y' := by
        funext j; refine Fin.lastCases ?_ (fun j => ?_) j
        · simp [snocZero, hy'last]
        · simp [snocZero, z]
      have hzN' : z ∈ N' := show snocZero m z ∈ N from hz ▸ hy'N
      have h1 := ih N' hN' z hzN'
      have h2 : y' ∈ span ℂ (equivValues a (m+1) N) := by
        rw [← hz]
        have h := Submodule.mem_map_of_mem (f := snocZero m) h1
        rw [Submodule.map_span] at h
        refine Submodule.span_mono ?_ h
        rintro _ ⟨v, ⟨S, hSa, hSN, q, rfl⟩, rfl⟩
        refine ⟨snocZero m ∘ₗ S, ?_, fun p => hSN p, q, rfl⟩
        intro i p; simp only [LinearMap.comp_apply, hSa, snocZero_diag]
      have h3 : (Pi.single (Fin.last m) (y (Fin.last m)) : Fin (m+1) → P) ∈
          span ℂ (equivValues a (m+1) N) := by
        refine Submodule.subset_span
          ⟨LinearMap.single ℂ (fun _ : Fin (m+1) => P) (Fin.last m), ?_, ?_, y (Fin.last m), rfl⟩
        · intro i p; simp only [LinearMap.single_apply]; exact single_diag _ _
        · intro p; simpa using hmem p
      have : y = y' + Pi.single (Fin.last m) (y (Fin.last m)) := by simp [hy']
      rw [this]; exact add_mem h2 h3
end GlobalTheory.SubmodulePowSimple
