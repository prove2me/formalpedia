-- Prove2me | solution 1 for GroupIsoPoly.extension_iso_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T05:08:05.442748+00:00
-- url     : https://prove2.me/submissions/4131d014-3438-42f3-9d48-2697adb76186

import Mathlib
import Definitions.Def_GroupIsoPoly_Ext
import Definitions.Def_GroupIsoPoly_coboundary

set_option autoImplicit false
open GroupIsoPoly

theorem solution {p a : ℕ} [Fact p.Prime] {Q : Type*} [Group Q] [Finite Q]
    (θG θH : Representation (ZMod p) Q (Fin a → ZMod p)) (fG : NormCocycle θG) (fH : NormCocycle θH)
    (α : (Fin a → ZMod p) ≃ₗ[ZMod p] (Fin a → ZMod p)) (β : MulAut Q) :
    (∀ b : Q → (Fin a → ZMod p),
      (∃ F : Ext θG fG ≃* Ext θH fH, ∀ (u : Fin a → ZMod p) (q : Q),
          F (Ext.mk u q) = Ext.mk (α u + b q) (β q)) ↔
        ((∀ (q : Q) (v : Fin a → ZMod p), α (θG q v) = θH (β q) (α v)) ∧
          ∀ q r : Q, b q + θH (β q) (b r) - b (q * r) = α (fG.f q r) - fH.f (β q) (β r))) ∧
    ((∀ (q : Q) (v : Fin a → ZMod p), α (θG q v) = θH (β q) (α v)) →
      (∀ (j : ℕ) (f : (Fin j → Q) → (Fin a → ZMod p)),
          Tmap α β (j + 1) (coboundary θG j f) = coboundary θH j (Tmap α β j f)) ∧
        ((∃ b : Q → (Fin a → ZMod p),
            ∀ q r : Q, b q + θH (β q) (b r) - b (q * r) = α (fG.f q r) - fH.f (β q) (β r)) ↔
          ∃ c : (Fin 1 → Q) → (Fin a → ZMod p),
            coboundary θH 1 c =
              fun g => Tmap α β 2 (fun x => fG.f (x 0) (x 1)) g - fH.f (g 0) (g 1))) := by
  refine ⟨fun b => ⟨?_, ?_⟩, fun h5 => ⟨fun j f => ?_, ⟨?_, ?_⟩⟩⟩
  · rintro ⟨F, hF⟩
    have key : ∀ u v q r, α (u + θG q v + fG.f q r) + b (q * r) =
        α u + b q + θH (β q) (α v + b r) + fH.f (β q) (β r) := by
      intro u v q r
      have h := congrArg Ext.fst (map_mul F (Ext.mk u q) (Ext.mk v r))
      have e : (Ext.mk u q : Ext θG fG) * Ext.mk v r = Ext.mk (u + θG q v + fG.f q r) (q * r) := rfl
      rw [e, hF, hF, hF] at h
      simpa using h
    refine ⟨fun q v => ?_, fun q r => ?_⟩
    · have h1 := key 0 v q 1
      have h2 := key 0 0 q 1
      simp only [map_add, map_zero, zero_add, add_zero] at h1 h2
      linear_combination (norm := module) h1 - h2
    · have h2 := key 0 0 q r
      simp only [map_zero, zero_add, add_zero] at h2
      linear_combination (norm := module) -h2
  · rintro ⟨h5, h6⟩
    refine ⟨{ toFun := fun x => Ext.mk (α (Ext.fst x) + b (Ext.snd x)) (β (Ext.snd x))
              invFun := fun y => Ext.mk (α.symm (Ext.fst y - b (β.symm (Ext.snd y))))
                (β.symm (Ext.snd y))
              left_inv := ?_
              right_inv := ?_
              map_mul' := ?_ }, fun u q => rfl⟩
    · intro x
      rw [Ext.ext_iff']
      simp
    · intro y
      rw [Ext.ext_iff']
      simp
    · intro x y
      rw [Ext.ext_iff']
      refine ⟨?_, by simp⟩
      simp only [Ext.fst_mul, Ext.snd_mul, Ext.fst_mk, Ext.snd_mk, map_add, map_mul]
      have e1 := h5 (Ext.snd x) (Ext.fst y)
      have e2 := h6 (Ext.snd x) (Ext.snd y)
      linear_combination (norm := module) e1 - e2
  · funext g
    simp only [Tmap, coboundary, map_add, map_sum, map_smul]
    congr 1
    · have := h5 (β.symm (g 0)) (f fun i => β.symm (g i.succ))
      simpa using this
    · refine Finset.sum_congr rfl fun i _ => ?_
      congr 3
      funext k
      simp only [Fin.contractNth]
      split_ifs <;> simp [map_mul]
  · rintro ⟨b, hb⟩
    refine ⟨fun x => b (β.symm (x 0)), ?_⟩
    funext g
    have := hb (β.symm (g 0)) (β.symm (g 1))
    simp only [coboundary, Tmap, Fin.sum_univ_two]
    simp [Fin.contractNth, map_mul] at this ⊢
    linear_combination (norm := module) this
  · rintro ⟨c, hc⟩
    refine ⟨fun q => c (fun _ => β q), fun q r => ?_⟩
    have := congrFun hc ![β q, β r]
    simp only [coboundary, Tmap, Fin.sum_univ_two] at this
    simp [Fin.contractNth, map_mul] at this ⊢
    have c0 : Fin.contractNth (0 : Fin 2) (fun x1 x2 : Q => x1 * x2) ![β q, β r] = fun _ => β q * β r := by
      funext k; fin_cases k; simp [Fin.contractNth]
    have c1 : Fin.contractNth (1 : Fin 2) (fun x1 x2 : Q => x1 * x2) ![β q, β r] = fun _ => β q := by
      funext k; fin_cases k; simp [Fin.contractNth]
    rw [c0, c1] at this
    linear_combination (norm := module) this
