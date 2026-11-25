-- Prove2me | solution 1 for GlobalTheory.DI.frob_lift_etale_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:39:10.125224+00:00
-- url     : https://prove2.me/submissions/60a45e1a-9409-416f-9180-3547aa30d895

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingHomLiftOfFormallySmooth
import Theorems.Thm_GlobalTheory_DI_exists_ringHom_lift_of_formallySmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DI
namespace GlobalTheory.DI
theorem _root_.solution :
    ∀ (p : ℕ) [Fact p.Prime] {n : ℕ} {B : Type} [CommRing B]
      (φ : MvPolynomial (Fin n) (ZMod (p ^ 2)) →+* B), φ.Etale →
      ∃ F : B →+* B, (∀ z, ∃ w, F z = z ^ p + p * w) ∧
        ∀ l, F (φ (MvPolynomial.X l)) = φ (MvPolynomial.X l) ^ p := by
  intro p hpf n B _ φ hφ
  have hp : p.Prime := hpf.out
  set I : Ideal B := Ideal.span {(p : B)} with hIdef
  have hp2 : ((p : B)) ^ 2 = 0 := by
    have : ((p ^ 2 : ℕ) : MvPolynomial (Fin n) (ZMod (p ^ 2))) = 0 := by
      rw [← map_natCast (MvPolynomial.C (σ := Fin n)), ZMod.natCast_self, map_zero]
    calc ((p : B)) ^ 2 = φ ((p ^ 2 : ℕ) : MvPolynomial (Fin n) (ZMod (p ^ 2))) := by
          rw [map_natCast]; push_cast; rfl
      _ = 0 := by rw [this, map_zero]
  have hI : IsNilpotent I := by
    refine ⟨2, ?_⟩
    rw [hIdef, Ideal.span_singleton_pow, hp2, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.zero_eq_bot]
  have hsm : φ.FormallySmooth := by
    letI := φ.toAlgebra
    haveI : Algebra.Etale _ B := hφ
    show Algebra.FormallySmooth _ B
    infer_instance
  let ψ : MvPolynomial (Fin n) (ZMod (p ^ 2)) →+* B :=
    φ.comp (MvPolynomial.expand p).toRingHom
  have hg : (powModP p hp B).comp φ = (Ideal.Quotient.mk I).comp ψ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact congrArg (· r) (Subsingleton.elim ((((powModP p hp B).comp φ)).comp MvPolynomial.C)
        (((Ideal.Quotient.mk I).comp ψ).comp MvPolynomial.C))
    · intro i
      simp [ψ, powModP, I]
  obtain ⟨F, hF1, hF2⟩ := exists_ringHom_lift_of_formallySmooth φ hsm ψ I hI (powModP p hp B) hg
  refine ⟨F, fun z => ?_, fun l => ?_⟩
  · have h1 := hF1 z
    have : F z - z ^ p ∈ I := by
      rw [← Ideal.Quotient.eq]
      exact h1
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp this
    exact ⟨w, by rw [mul_comm]; linear_combination -hw⟩
  · rw [hF2]
    simp [ψ]
end GlobalTheory.DI
