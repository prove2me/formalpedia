-- Prove2me | solution 1 for GlobalTheory.UnramifiedHensel.exists_relation_gradient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:10:28.28723+00:00
-- url     : https://prove2.me/submissions/f9649803-99a7-4f97-a843-60c75fcbd907

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRelationGradient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
open GlobalTheory.UnramifiedHensel
namespace GlobalTheory.UnramifiedHensel
theorem _root_.solution {R A k ι : Type} [CommRing R] [CommRing A] [Field k]
    [Fintype ι] [DecidableEq ι] (ev : MvPolynomial ι R →+* A) (hev : Function.Surjective ev)
    (red : A →+* k) (hred : ∀ c : k, ∃ w : R, red (ev (C w)) = c)
    (h : ∀ φ : A →+* DualNumber k, (∀ a, (φ a).fst = red a) → (∀ w, (φ (ev (C w))).snd = 0) →
      ∀ i, (φ (ev (X i))).snd = 0) (i : ι) :
    ∃ G : MvPolynomial ι R, ev G = 0 ∧
      ∀ j, red (ev (pderiv j G)) = if j = i then 1 else 0 := by
  let Γ : Submodule k (ι → k) :=
    { carrier := {γ | ∃ G : MvPolynomial ι R, ev G = 0 ∧ ∀ j, red (ev (pderiv j G)) = γ j}
      add_mem' := by
        rintro a b ⟨G, hG, ha⟩ ⟨H, hH, hb⟩
        exact ⟨G + H, by simp [hG, hH], fun j => by simp [ha, hb]⟩
      zero_mem' := ⟨0, by simp, fun j => by simp⟩
      smul_mem' := by
        rintro c a ⟨G, hG, ha⟩
        obtain ⟨w, hw⟩ := hred c
        refine ⟨C w * G, by simp [hG], fun j => ?_⟩
        rw [pderiv_C_mul]
        simp [ha, hw] }
  suffices hΓ : Γ = ⊤ by
    have : (fun j => if j = i then (1 : k) else 0) ∈ Γ := by rw [hΓ]; trivial
    exact this
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne)
    inferInstance
  let v : ι → k := fun j => f (Pi.single j 1)
  have hfv : ∀ γ : ι → k, f γ = ∑ j, γ j * v j := by
    intro γ
    conv_lhs => rw [pi_eq_sum_univ' γ]
    simp [v, map_sum]
  let ψ : MvPolynomial ι R →+* DualNumber k :=
    eval₂Hom ((TrivSqZeroExt.inlHom k k).comp (red.comp (ev.comp C)))
      (fun j => (TrivSqZeroExt.inl (red (ev (X j))) + TrivSqZeroExt.inr (v j) : DualNumber k))
  have hψ : ∀ F, (ψ F).fst = red (ev F) ∧
      (ψ F).snd = ∑ j, red (ev (pderiv j F)) * v j := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C a => simp [ψ]
    | add p q hp hq => simp [hp.1, hp.2, hq.1, hq.2, add_mul, Finset.sum_add_distrib]
    | mul_X p n hp =>
      have h1 : (ψ (X n)).fst = red (ev (X n)) := by simp [ψ]
      have h2 : (ψ (X n)).snd = v n := by simp [ψ]
      refine ⟨by simp [hp.1, h1], ?_⟩
      rw [map_mul, DualNumber.snd_mul, hp.1, hp.2, h1, h2]
      have : ∀ j, red (ev (pderiv j (p * X n))) * v j =
          red (ev (pderiv j p)) * v j * red (ev (X n)) +
            (if j = n then red (ev p) * v n else 0) := by
        intro j
        rw [pderiv_mul, pderiv_X]
        by_cases hj : j = n
        · subst hj; simp; ring
        · simp [hj, Pi.single_apply, Ne.symm hj]; ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_mul]
      simp [add_comm]
  have hker : RingHom.ker ev ≤ RingHom.ker ψ := by
    intro F hF
    rw [RingHom.mem_ker] at hF ⊢
    ext
    · simp [(hψ F).1, hF]
    · rw [(hψ F).2, ← hfv (fun j => red (ev (pderiv j F)))]
      have : f (fun j => red (ev (pderiv j F))) ∈ Γ.map f :=
        Submodule.mem_map_of_mem ⟨F, hF, fun _ => rfl⟩
      rw [hf] at this
      simpa using this
  let φ : A →+* DualNumber k := ev.liftOfSurjective hev ⟨ψ, hker⟩
  have hφ : ∀ F, φ (ev F) = ψ F := fun F => RingHom.liftOfSurjective_comp_apply _ _ _ F
  have hv := h φ (fun a => by obtain ⟨F, rfl⟩ := hev a; rw [hφ, (hψ F).1])
    (fun w => by rw [hφ, (hψ _).2]; simp)
  apply hf0
  ext j
  have := hv j
  rw [hφ] at this
  have h2 : (ψ (X j)).snd = v j := by simp [ψ]
  simpa [v, h2] using this
end GlobalTheory.UnramifiedHensel
