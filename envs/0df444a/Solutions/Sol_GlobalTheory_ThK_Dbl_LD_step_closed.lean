-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.step_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:28:45.270766+00:00
-- url     : https://prove2.me/submissions/7f31376e-00b4-48f6-b8d6-e2032f238c26

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistC
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistD
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_exists_bump
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_nonarch_pi
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
theorem _root_.solution {n d : ℕ} (ih : Claim c n d) {l : (Matrix (Fin (n + 1)) (Fin d) k → ℂ) →ₗ[ℂ] ℂ} (hl : Eqv c l)
    (hd : ∀ φ ∈ SB _, (∀ X, Deg X → φ X = 0) → l φ = 0) (hz : ∀ φ ∈ SB _, (∀ X, X 0 = 0 → φ X = 0) → l φ = 0) :
    ∀ φ ∈ SB _, l φ = 0 := by
  have := nonarch_pi (Fin d) k
  obtain ⟨g₀, hg₀⟩ := exists_bump (Fin d → k)
  let cn : (Fin d → k) → Matrix (Fin n) (Fin d) k → Matrix (Fin (n + 1)) (Fin d) k := fun y Y => Matrix.of (Fin.cons y Y)
  let tl : Matrix (Fin (n + 1)) (Fin d) k → Matrix (Fin n) (Fin d) k := fun X => X.submatrix Fin.succ id
  have ccn : Continuous fun z : (Fin d → k) × Matrix (Fin n) (Fin d) k => cn z.1 z.2 := by
    refine continuous_matrix fun i j => ?_
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [cn] <;> fun_prop
  have ctl : Continuous tl := by fun_prop
  have hcn : ∀ X, cn (X 0) (tl X) = X := fun X => by
    ext i j; refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  have sb : ∀ ψ ∈ SB _, (fun X => g₀ (X 0) * ψ (tl X)) ∈ SB (Matrix (Fin (n + 1)) (Fin d) k) := fun ψ hψ =>
    sb_comp (fun X => (X 0, tl X)) (fun z => cn z.1 z.2) (by fun_prop) ccn hcn (sb_tens hg₀.1 hψ)
  let l₂ : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun ψ => l fun X => g₀ (X 0) * ψ (tl X)
      map_add' := fun F F' => by rw [← map_add]; congr 1; ext z; simp [mul_add]
      map_smul' := fun a F => by rw [← map_smul]; congr 1; ext z; simp [mul_left_comm] }
  have eq : ∀ φ ∈ SB _, ∀ φ' ∈ SB _, (∀ X, X 0 = 0 → φ X = φ' X) → l φ = l φ' := fun φ hφ φ' hφ' h => by
    rw [← sub_eq_zero, ← map_sub]
    exact hz _ (sub_mem hφ hφ') fun X hX => sub_eq_zero.2 (h X hX)
  have z := ih l₂ (fun h hh => ?_) fun ψ hψ hψ0 => hd _ (sb ψ hψ) fun X hX => ?_
  · intro φ hφ
    have hr : (fun Y => φ (cn 0 Y)) ∈ SB _ :=
      sb_comp (cn 0) tl (ccn.comp (Continuous.prodMk_right 0)) ctl (fun Y => rfl) hφ
    refine (eq φ hφ _ (sb _ hr) fun X hX => ?_).trans (z _ hr)
    have := hcn X
    rw [hX] at this
    rw [this, hX, hg₀.2.2, one_mul]
  · obtain ⟨t, pt, ht⟩ := hl h hh
    refine ⟨t, pt, fun ψ hψ => (eq _ (sb _ (sb_right hψ hh)) _ (sb_right (sb ψ hψ) hh) fun X hX => ?_).trans (ht _ (sb ψ hψ))⟩
    have : (X * h) 0 = 0 := by ext j; simp [mul_apply, hX]
    rw [hX, this]; rfl
  · obtain ⟨v, hv, h⟩ := hX
    rw [hψ0 (tl X) ⟨v, hv, funext fun i => congrFun h i.succ⟩, mul_zero]
end GlobalTheory.ThK.Dbl.LD
