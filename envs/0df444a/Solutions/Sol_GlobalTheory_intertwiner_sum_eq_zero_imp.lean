-- Prove2me | solution 1 for GlobalTheory.intertwiner_sum_eq_zero_imp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T06:04:35.133206+00:00
-- url     : https://prove2.me/submissions/e228aec3-8db3-42f2-b251-63f16df75757

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InjectiveSumOfLinIndepIntertwiners

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Representation
namespace GlobalTheory
theorem _root_.solution {G : Type} [Group G] {N X : Type} [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X)
    (hirr : π.IsIrreducible)
    (hschur : ∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) :
    ∀ (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ), LinearIndependent ℂ φ →
      ∀ w : Fin m → N, ∑ j, φ j (w j) = 0 → w = 0 := by
  intro m
  induction m with
  | zero => intro φ _ w _; exact Subsingleton.elim _ _
  | succ m ih =>
    intro φ hφ
    let Φ : (Fin (m+1) → N) →ₗ[ℂ] X := ∑ j, (φ j).toLinearMap ∘ₗ LinearMap.proj j
    have hΦ : ∀ w, Φ w = ∑ j, φ j (w j) := by intro w; simp [Φ, LinearMap.sum_apply]
    let K := LinearMap.ker Φ
    have hK : ∀ w, w ∈ K ↔ ∑ j, φ j (w j) = 0 := by intro w; simp [K, hΦ]
    have hφ' : LinearIndependent ℂ (fun j : Fin m => φ j.castSucc) :=
      hφ.comp _ (Fin.castSucc_injective m)
    have claimA : ∀ w : Fin (m+1) → N, ∑ j, φ j (w j) = 0 → w (Fin.last m) = 0 → w = 0 := by
      intro w hw hl
      rw [Fin.sum_univ_castSucc, hl, map_zero, add_zero] at hw
      have := ih _ hφ' (fun j => w j.castSucc) hw
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hl
      · exact congrFun this j
    have hstable : ∀ (g : G) (w : Fin (m+1) → N), ∑ j, φ j (w j) = 0 →
        ∑ j, φ j (π g (w j)) = 0 := by
      intro g w hw
      simp_rw [IntertwiningMap.isIntertwining]
      rw [← map_sum, hw, map_zero]
    let P : Subrepresentation π :=
      { toSubmodule := K.map (LinearMap.proj (Fin.last m))
        apply_mem_toSubmodule := by
          rintro g _ ⟨w, hw, rfl⟩
          refine ⟨fun j => π g (w j), ?_, rfl⟩
          rw [SetLike.mem_coe, hK] at hw ⊢
          exact hstable g w hw }
    have hmemP : ∀ w : Fin (m+1) → N, ∑ j, φ j (w j) = 0 → w (Fin.last m) ∈ P := fun w hw =>
      show w (Fin.last m) ∈ K.map (LinearMap.proj (Fin.last m)) from ⟨w, (hK w).2 hw, rfl⟩
    rcases hirr.eq_bot_or_eq_top P with hP | hP
    · intro w hw
      apply claimA w hw
      have := hmemP w hw
      rw [hP] at this
      exact (Submodule.mem_bot ℂ).mp this
    · exfalso
      have hsurj : ∀ n : N, ∃ w : Fin (m+1) → N, ∑ j, φ j (w j) = 0 ∧ w (Fin.last m) = n := by
        intro n
        have : n ∈ P := by rw [hP]; exact Submodule.mem_top
        obtain ⟨w, hw, rfl⟩ := (show n ∈ K.map (LinearMap.proj (Fin.last m)) from this)
        exact ⟨w, (hK w).1 hw, rfl⟩
      have huniq : ∀ w w' : Fin (m+1) → N, ∑ j, φ j (w j) = 0 → ∑ j, φ j (w' j) = 0 →
          w (Fin.last m) = w' (Fin.last m) → w = w' := by
        intro w w' hw hw' hl
        have := claimA (w - w') (by simp [map_sub, Finset.sum_sub_distrib, hw, hw'])
          (by simp [hl])
        exact sub_eq_zero.mp this
      let p : K →ₗ[ℂ] N := LinearMap.proj (Fin.last m) ∘ₗ K.subtype
      have hp : Function.Bijective p := by
        constructor
        · intro a b hab
          exact Subtype.ext (huniq a.1 b.1 ((hK _).1 a.2) ((hK _).1 b.2) hab)
        · intro n
          obtain ⟨w, hw, hl⟩ := hsurj n
          exact ⟨⟨w, (hK w).2 hw⟩, hl⟩
      let e := LinearEquiv.ofBijective p hp
      let s : N →ₗ[ℂ] (Fin (m+1) → N) := K.subtype ∘ₗ e.symm.toLinearMap
      have hsK : ∀ n, ∑ j, φ j (s n j) = 0 := fun n => (hK _).1 (e.symm n).2
      have hsl : ∀ n, s n (Fin.last m) = n := fun n => e.apply_symm_apply n
      have hsg : ∀ (g : G) (n : N), s (π g n) = fun j => π g (s n j) := by
        intro g n
        apply huniq _ _ (hsK _) (hstable g _ (hsK n))
        simp only [hsl]
      have hc : ∀ j : Fin m, ∃ c : ℂ, ∀ n, s n j.castSucc = c • n := by
        intro j
        let f : π.IntertwiningMap π :=
          { toLinearMap := LinearMap.proj j.castSucc ∘ₗ s
            isIntertwining' := by
              intro g; ext n; simp [hsg] }
        obtain ⟨c, hc⟩ := hschur f
        refine ⟨c, fun n => ?_⟩
        have := congrArg (fun L => L n) hc
        simpa [f] using this
      choose c hc using hc
      have hrel : ∑ j : Fin m, c j • φ j.castSucc + φ (Fin.last m) = 0 := by
        ext n
        have := hsK n
        rw [Fin.sum_univ_castSucc] at this
        simp only [hc, hsl, map_smul] at this
        simpa [IntertwiningMap.sum_apply] using this
      have := (Fintype.linearIndependent_iff.mp hφ) (Fin.snoc c 1) (by
        rw [Fin.sum_univ_castSucc]; simpa using hrel)
      have h1 := this (Fin.last m)
      simp at h1
end GlobalTheory
