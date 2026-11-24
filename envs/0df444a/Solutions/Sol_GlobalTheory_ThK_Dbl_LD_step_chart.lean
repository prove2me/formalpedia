-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.step_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:57:09.326845+00:00
-- url     : https://prove2.me/submissions/d7a87cc7-b283-433e-ad41-f6c62d3185d4

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistC
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistD
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_nonarch_mat
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_lc_mat
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_Eqv_unip
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_bump_ratio
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_chE_levi
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_chE_unip
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_chR_chE
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_det_blk
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_exists_bump
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_kill_tens
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_mul_blk_zero
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_nonarch_pi
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_sb_chE
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_sb_chR
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_sb_comp
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_sb_right
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_sb_tens


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology GlobalTheory.WeilM Matrix
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k]
  [NonarchimedeanAddGroup k] [LocallyCompactSpace k] {c : k → ℂ} {ϖ : k}
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution (hc : ∀ a ≠ 0, c a ≠ 0) (h0 : ϖ ≠ 0) (h1 : ϖ ≠ 1) {n d : ℕ} (ih : Claim c n d)
    {l : (Matrix (Fin (n + 1)) (Fin (d + 1)) k → ℂ) →ₗ[ℂ] ℂ} (hl : Eqv c l)
    (hd : ∀ φ ∈ SB _, (∀ X, Deg X → φ X = 0) → l φ = 0) : ∀ φ ∈ SB _, (∀ X, X 0 0 = 0 → φ X = 0) → l φ = 0 := by
  have := nonarch_pi (Fin d) k
  have := nonarch_mat (k := k) n d
  have := lc_mat (k := k) n d
  intro φ hφ hz
  let L := l ∘ₗ LinearMap.funLeft ℂ ℂ (chE (k := k) (n := n) (d := d))
  have hL : ∀ F, L F = l fun X => F (chE X) := fun _ => rfl
  have e : φ = fun X => φ (chR (chE X)) := by
    ext X
    by_cases hX : X 0 0 = 0
    · rw [hz X hX, hz _ (by simpa [chR, chE] using hX)]
    · rw [chR_chE X hX]
  rw [e, ← hL fun y => φ (chR y)]
  refine kill_tens {z | z.1 0 ≠ 0} L (fun F hF hF0 ψ hψ => ?_) (sb_chR hφ hz)
    fun z h => hz _ (by simpa [chR] using h)
  let T : ∀ ψ : Matrix (Fin n) (Fin d) k → ℂ, ((Fin (n + 1) → k) × (Fin d → k) → ℂ) →ₗ[ℂ] ℂ := fun ψ =>
    { toFun := fun F => L fun z => F z.1 * ψ z.2
      map_add' := fun F F' => by rw [← map_add]; congr 1; ext z; simp [add_mul]
      map_smul' := fun a F => by rw [← map_smul]; congr 1; ext z; simp [mul_assoc] }
  refine kill_tens {x : Fin (n + 1) → k | x 0 ≠ 0} (T ψ) (fun f hf hf0 => ?_) hF fun z h => hF0 z h
  replace hf0 : ∀ x, x 0 = 0 → f x = 0 := fun x hx => hf0 x (not_not.2 hx)
  let m : ∀ ψ : Matrix (Fin n) (Fin d) k → ℂ, ((Fin d → k) → ℂ) →ₗ[ℂ] ℂ := fun ψ =>
    { toFun := fun g => T ψ fun z => f z.1 * g z.2
      map_add' := fun F F' => by rw [← map_add]; congr 1; ext z; simp [mul_add]
      map_smul' := fun a F => by rw [← map_smul]; congr 1; ext z; simp [mul_left_comm] }
  have hm : ∀ ψ g, m ψ g = l fun X => f (chE X).1.1 * g (chE X).1.2 * ψ (chE X).2 := fun _ _ => rfl
  have sb : ∀ ψ ∈ SB _, ∀ g ∈ SB (Fin d → k), (fun X => f (chE X).1.1 * g (chE X).1.2 * ψ (chE X).2) ∈ SB _ := fun ψ hψ g hg =>
    sb_chE (sb_tens (sb_tens hf hg) hψ) fun y hy => by simp [hf0 _ hy]
  have inv : ∀ ψ ∈ SB _, ∀ g ∈ SB _, ∀ a, m ψ (fun x => g (x + a)) = m ψ g := fun ψ hψ g hg a => by
    rw [hm, hm, ← hl.unip hc h0 h1 a _ (sb ψ hψ g hg)]
    congr 1; ext X
    by_cases hX : X 0 0 = 0
    · rw [hf0 _ (by simpa [chE] using hX), hf0 _ (by simpa [chE, mul_blk_zero] using hX)]; simp
    · rw [chE_unip X hX]
  obtain ⟨g₀, hg₀⟩ := exists_bump (Fin d → k)
  obtain ⟨_, -, hs⟩ := bump_ratio hg₀ hg₀
  refine (hs _ (inv ψ hψ)).2 ?_
  let l₁ : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun ψ => l fun X => f (chE X).1.1 * g₀ (chE X).1.2 * ψ (chE X).2
      map_add' := fun F F' => by rw [← map_add]; congr 1; ext z; simp [mul_add]
      map_smul' := fun a F => by rw [← map_smul]; congr 1; ext z; simp [mul_left_comm] }
  refine ih l₁ (fun h hh => ?_) (fun ψ hψ hψ0 => hd _ (sb ψ hψ _ hg₀.1) fun X hX => ?_) ψ hψ
  · have hg₁ : Bump fun u => g₀ (u ᵥ* h) :=
      ⟨sb_comp (· ᵥ* h) (· ᵥ* h⁻¹) (by fun_prop) (by fun_prop)
        (fun x => by simp [mul_nonsing_inv h hh.isUnit]) hg₀.1, fun _ => hg₀.2.1 _, by simpa using hg₀.2.2⟩
    obtain ⟨s, ps, hs⟩ := bump_ratio hg₀ hg₁
    obtain ⟨t, pt, ht⟩ := hl (blk 1 0 h) (by simpa [det_blk] using hh)
    refine ⟨t * s, mul_pos pt ps, fun ψ hψ => ?_⟩
    have a := ht _ (sb ψ hψ _ hg₀.1)
    simp only [chE_levi, det_blk, one_mul] at a
    have b := (hs _ (inv _ (sb_right hψ hh))).1
    refine b.trans ((congrArg ((s : ℂ) * ·) a).trans ?_)
    show _ * (_ * l₁ ψ) = _
    push_cast; ring
  · by_cases hX0 : X 0 0 = 0
    · rw [hf0 _ (by simpa [chE] using hX0)]; simp
    · rw [hψ0 _ (hX.chE hX0), mul_zero]
end GlobalTheory.ThK.Dbl.LD
